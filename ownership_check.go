package main

// Liveness and Ownership Analysis.
//
// Tracks local variable usage across function statements to determine:
// 1. Last-use point of buffer/string/slice/map/struct typed variables.
// 2. Variable ownership states (Owned, Borrowed, Moved, Dropped).
// 3. Compile-time prevention of use-after-move and use-after-free bugs.

import (
	"fmt"
)

// VarState represents the ownership state of a local variable.
type VarState int

const (
	StateOwned VarState = iota
	StateBorrowed
	StateMoved
	StateDropped
)

func (s VarState) String() string {
	switch s {
	case StateOwned:
		return "owned"
	case StateBorrowed:
		return "borrowed"
	case StateMoved:
		return "moved"
	case StateDropped:
		return "dropped"
	default:
		return "unknown"
	}
}

// OwnershipDiagnostic holds compile-time ownership violation findings.
type OwnershipDiagnostic struct {
	Code    string // e.g. "OWN001", "OWN002"
	Message string
	VarName string
	Decl    string
}

// LivenessInfo records variable usage positions in statements.
type LivenessInfo struct {
	// Variables whose last use occurs at this statement (eligible for drop/reclaim).
	LastUses map[Stmt][]string
	// Variables whose ownership has been moved (e.g. via ch <- v).
	MovedVars map[string]bool
}

// AnalyzeOwnership performs forward dataflow analysis to track ownership and last-use
// points across every function in the Program AST.
func AnalyzeOwnership(prog *Program, c *Checker) ([]OwnershipDiagnostic, map[*FuncDecl]*LivenessInfo) {
	var diags []OwnershipDiagnostic
	funcLiveness := make(map[*FuncDecl]*LivenessInfo)

	for _, fn := range prog.Funcs {
		info, d := analyzeFuncOwnership(fn, c)
		diags = append(diags, d...)
		funcLiveness[fn] = info
	}

	return diags, funcLiveness
}

func analyzeFuncOwnership(fn *FuncDecl, c *Checker) (*LivenessInfo, []OwnershipDiagnostic) {
	info := &LivenessInfo{
		LastUses:  make(map[Stmt][]string),
		MovedVars: make(map[string]bool),
	}
	var diags []OwnershipDiagnostic

	// 1. Count occurrences of reads for each local variable:
	// Var -> statement list accessing it in order
	accessMap := make(map[string][]Stmt)
	escaped := make(map[string]bool)

	// Mark variables boxed by closures as escaping
	if fn.Boxed != nil {
		for v := range fn.Boxed {
			escaped[v] = true
		}
	}

	// Build global variable set to detect global assignments
	globalSet := make(map[string]bool)
	if c != nil {
		for _, g := range c.GlobalOrder() {
			globalSet[g] = true
		}
	}
	// Return variables escape so their assigned values are not dropped
	for _, r := range fn.Returns {
		globalSet[r] = true
		escaped[r] = true
	}

	var scanStmts func(stmts []Stmt, inLoop bool)
	scanStmts = func(stmts []Stmt, inLoop bool) {
		for _, stmt := range stmts {
			readVars := collectReadIdents(stmt)
			for v := range readVars {
				if isLocalVariable(fn, v) {
					accessMap[v] = append(accessMap[v], stmt)
					if inLoop {
						// Variables accessed inside loops cannot be dropped inside the loop
						// since subsequent iterations might still access them.
						escaped[v] = true
					}
				}
			}

			// Escape detection:
			// a) Assignment to global variable (e.g.: g_config = local_data)
			if as, ok := stmt.(*AssignStmt); ok {
				if globalSet[as.Name] {
					vReads := collectReadIdents(as)
					for rv := range vReads {
						escaped[rv] = true
					}
				}
			}
			// b) Return statement: values returned escape the function scope
			if ret, ok := stmt.(*ReturnStmt); ok {
				vReads := collectReadIdents(ret)
				for rv := range vReads {
					escaped[rv] = true
				}
			}
			// c) Function / method calls: arguments passed to external functions could be stored
			// in global state, closures, or escaping heap containers
			walkExprs(stmt, func(e Expr) {
				if call, ok := e.(*Call); ok {
					for _, arg := range call.Args {
						if id, ok := arg.(*Ident); ok {
							escaped[id.Name] = true
						}
					}
				} else if cv, ok := e.(*CallValue); ok {
					for _, arg := range cv.Args {
						if id, ok := arg.(*Ident); ok {
							escaped[id.Name] = true
						}
					}
				}
			})

			// Recurse into conditional and loop blocks
			switch s := stmt.(type) {
			case *IfStmt:
				scanStmts(s.Then, inLoop)
				scanStmts(s.Else, inLoop)
			case *WhileStmt:
				scanStmts(s.Body, true)
			case *RangeStmt:
				scanStmts(s.Body, true)
			case *ArenaStmt:
				scanStmts(s.Body, inLoop)
			}
		}
	}

	scanStmts(fn.Body, false)

	// 2. Record last-use points for each local variable (unless escaped)
	for v, stmts := range accessMap {
		if escaped[v] {
			continue
		}
		if len(stmts) > 0 {
			lastStmt := stmts[len(stmts)-1]
			info.LastUses[lastStmt] = append(info.LastUses[lastStmt], v)
		}
	}

	// 3. Verify move semantics (e.g. channel send: SendStmt)
	movedAt := make(map[string]int) // var -> statement index

	for idx, stmt := range fn.Body {
		switch s := stmt.(type) {
		case *SendStmt:
			if id, ok := s.Val.(*Ident); ok {
				if isLocalVariable(fn, id.Name) {
					if movedAt[id.Name] > 0 {
						diags = append(diags, OwnershipDiagnostic{
							Code:    "OWN002",
							Message: fmt.Sprintf("variable `%s` used after move", id.Name),
							VarName: id.Name,
							Decl:    fn.Name,
						})
					} else {
						movedAt[id.Name] = idx + 1
						info.MovedVars[id.Name] = true
					}
				}
			}
		default:
			// Check if statements after the move attempt to read the moved variable
			reads := collectReadIdents(stmt)
			for r := range reads {
				if mIdx := movedAt[r]; mIdx > 0 && idx >= mIdx {
					diags = append(diags, OwnershipDiagnostic{
						Code:    "OWN002",
						Message: fmt.Sprintf("variable `%s` used after move (moved at step %d)", r, mIdx),
						VarName: r,
						Decl:    fn.Name,
					})
				}
			}
		}
	}

	return info, diags
}

// isLocalVariable checks if an identifier is a parameter or a local variable of the function.
func isLocalVariable(fn *FuncDecl, name string) bool {
	for _, p := range fn.Params {
		if p == name {
			return true
		}
	}
	for _, r := range fn.Returns {
		if r == name {
			return true
		}
	}
	found := false
	var checkStmts func(stmts []Stmt)
	checkStmts = func(stmts []Stmt) {
		for _, stmt := range stmts {
			if found {
				return
			}
			switch s := stmt.(type) {
			case *AssignStmt:
				if s.Name == name {
					found = true
					return
				}
			case *IfStmt:
				checkStmts(s.Then)
				checkStmts(s.Else)
			case *WhileStmt:
				checkStmts(s.Body)
			case *RangeStmt:
				checkStmts(s.Body)
			case *ArenaStmt:
				checkStmts(s.Body)
			}
		}
	}
	checkStmts(fn.Body)
	return found
}

// collectReadIdents gathers all variable identifiers read within a given Statement.
func collectReadIdents(stmt Stmt) map[string]bool {
	reads := make(map[string]bool)
	switch s := stmt.(type) {
	case *ExprStmt:
		visitExpr(s.X, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *AssignStmt:
		visitExpr(s.Val, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *ReturnStmt:
		for _, x := range s.Vals {
			visitExpr(x, func(e Expr) {
				if id, ok := e.(*Ident); ok {
					reads[id.Name] = true
				}
			})
		}
	case *SendStmt:
		visitExpr(s.Ch, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
		visitExpr(s.Val, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *IfStmt:
		visitExpr(s.Cond, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *WhileStmt:
		visitExpr(s.Cond, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *RangeStmt:
		visitExpr(s.X, func(e Expr) {
			if id, ok := e.(*Ident); ok {
				reads[id.Name] = true
			}
		})
	case *GoStmt:
		if s.Call != nil {
			visitExpr(s.Call, func(e Expr) {
				if id, ok := e.(*Ident); ok {
					reads[id.Name] = true
				}
			})
		}
	case *ArenaStmt:
		for _, st := range s.Body {
			r := collectReadIdents(st)
			for k := range r {
				reads[k] = true
			}
		}
	}
	return reads
}

// walkExprs traverses all expressions within an AST statement.
func walkExprs(stmt Stmt, fn func(Expr)) {
	if stmt == nil {
		return
	}
	switch s := stmt.(type) {
	case *ExprStmt:
		visitExpr(s.X, fn)
	case *AssignStmt:
		visitExpr(s.Val, fn)
	case *ReturnStmt:
		for _, x := range s.Vals {
			visitExpr(x, fn)
		}
	case *SendStmt:
		visitExpr(s.Ch, fn)
		visitExpr(s.Val, fn)
	case *IfStmt:
		visitExpr(s.Cond, fn)
		for _, st := range s.Then {
			walkExprs(st, fn)
		}
		for _, st := range s.Else {
			walkExprs(st, fn)
		}
	case *WhileStmt:
		visitExpr(s.Cond, fn)
		for _, st := range s.Body {
			walkExprs(st, fn)
		}
	case *RangeStmt:
		visitExpr(s.X, fn)
		for _, st := range s.Body {
			walkExprs(st, fn)
		}
	case *GoStmt:
		if s.Call != nil {
			visitExpr(s.Call, fn)
		}
	case *ArenaStmt:
		for _, st := range s.Body {
			walkExprs(st, fn)
		}
	}
}

func visitExpr(e Expr, fn func(Expr)) {
	if e == nil {
		return
	}
	fn(e)
	switch x := e.(type) {
	case *Unary:
		visitExpr(x.X, fn)
	case *Binary:
		visitExpr(x.L, fn)
		visitExpr(x.R, fn)
	case *Call:
		for _, a := range x.Args {
			visitExpr(a, fn)
		}
	case *Index:
		visitExpr(x.X, fn)
		visitExpr(x.Idx, fn)
	case *SliceExpr:
		visitExpr(x.X, fn)
		visitExpr(x.Lo, fn)
		visitExpr(x.Hi, fn)
	case *StructLit:
		for _, v := range x.Vals {
			visitExpr(v, fn)
		}
	case *FieldAccess:
		visitExpr(x.X, fn)
	case *CallValue:
		visitExpr(x.Fn, fn)
		for _, a := range x.Args {
			visitExpr(a, fn)
		}
	case *Recv:
		visitExpr(x.Ch, fn)
	}
}
