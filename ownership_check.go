package main

// Liveness and Ownership Analysis.
//
// Melacak penggunaan variabel lokal dalam suatu fungsi untuk menentukan:
// 1. Titik penggunaan terakhir (Last-Use point) dari variabel bertipe buffer/string/slice/map/struct.
// 2. Status kepemilikan variabel (Owned, Borrowed, Moved, Dropped).
// 3. Mencegah use-after-move dan use-after-free pada tingkat compile-time.

import (
	"fmt"
)

// VarState merepresentasikan status kepemilikan suatu variabel lokal.
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

// OwnershipDiagnostic menyimpan temuan pelanggaran kepemilikan.
type OwnershipDiagnostic struct {
	Code    string // e.g. "OWN001", "OWN002"
	Message string
	VarName string
	Decl    string
}

// LivenessInfo mencatat lokasi penggunaan variabel dalam statement.
type LivenessInfo struct {
	// Variabel-variabel yang terakhir kali digunakan pada statement ini (siap di-drop/reclaim).
	LastUses map[Stmt][]string
	// Variabel yang dipindahkan kepemilikannya (misal via ch <- v).
	MovedVars map[string]bool
}

// AnalyzeOwnership melakukan forward dataflow analysis untuk melacak ownership dan last-use
// pada setiap fungsi dalam AST Program.
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

	// 1. Hitung kemunculan pembacaan setiap variabel lokal
	// Var -> daftar urutan statement yang mengaksesnya
	accessMap := make(map[string][]Stmt)

	var scanStmts func(stmts []Stmt)
	scanStmts = func(stmts []Stmt) {
		for _, stmt := range stmts {
			readVars := collectReadIdents(stmt)
			for v := range readVars {
				if isLocalVariable(fn, v) {
					accessMap[v] = append(accessMap[v], stmt)
				}
			}
			// Rekursif ke dalam blok if, while, for-range
			switch s := stmt.(type) {
			case *IfStmt:
				scanStmts(s.Then)
				scanStmts(s.Else)
			case *WhileStmt:
				scanStmts(s.Body)
			case *RangeStmt:
				scanStmts(s.Body)
			case *ArenaStmt:
				scanStmts(s.Body)
			}
		}
	}

	scanStmts(fn.Body)

	// 2. Catat titik last-use untuk setiap variabel
	for v, stmts := range accessMap {
		if len(stmts) > 0 {
			lastStmt := stmts[len(stmts)-1]
			info.LastUses[lastStmt] = append(info.LastUses[lastStmt], v)
		}
	}

	// 3. Verifikasi Move Semantics (misal: kirim ke channel: SendStmt)
	movedAt := make(map[string]int) // var -> index statement

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
			// Periksa apakah statement setelah titik move mencoba membaca variabel yang sudah moved
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

// isLocalVariable mengecek apakah sebuah identifier adalah parameter atau variabel lokal fungsi.
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

// collectReadIdents mengumpulkan semua variabel yang dibaca dalam suatu Statement.
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
	}
	return reads
}

// walkExprs melakukan traversal ekspresi dalam AST statement.
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
