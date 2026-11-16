package main

import (
	"fmt"
)

// OOMDiagnostic represents a potential compile-time memory leak or OOM risk.
type OOMDiagnostic struct {
	Code    string
	Message string
	Decl    string
	Line    int
}

// DetectLoopAllocations checks if there are unbounded heap allocations inside loops (for/while)
// that are not enclosed within an `arena { }` block, risking memory accumulation (OOM).
func DetectLoopAllocations(prog *Program, c *Checker) []OOMDiagnostic {
	var diags []OOMDiagnostic

	for _, fn := range prog.Funcs {
		checkBodyForLoopAllocations(fn, fn.Body, &diags)
	}

	return diags
}

func checkBodyForLoopAllocations(fn *FuncDecl, stmts []Stmt, diags *[]OOMDiagnostic) {
	for _, stmt := range stmts {
		switch s := stmt.(type) {
		case *WhileStmt:
			checkLoopStmts(fn, s.Body, diags)
		case *RangeStmt:
			checkLoopStmts(fn, s.Body, diags)
		case *IfStmt:
			checkBodyForLoopAllocations(fn, s.Then, diags)
			checkBodyForLoopAllocations(fn, s.Else, diags)
		case *ArenaStmt:
			continue
		}
	}
}

func checkLoopStmts(fn *FuncDecl, body []Stmt, diags *[]OOMDiagnostic) {
	for _, stmt := range body {
		switch s := stmt.(type) {
		case *ArenaStmt:
			// Enclosed within an arena block; lifetime is bounded per iteration.
			continue
		case *AssignStmt:
			if exprAllocatesHeap(s.Val) {
				*diags = append(*diags, OOMDiagnostic{
					Code:    "OOM001",
					Message: fmt.Sprintf("unbounded heap allocation inside loop for `%s`; wrap the loop body with `arena { ... }` or reuse an outer buffer to prevent OOM", s.Name),
					Decl:    fn.Name,
				})
			}
		case *MultiAssign:
			for _, rhs := range s.Rhs {
				if exprAllocatesHeap(rhs) {
					*diags = append(*diags, OOMDiagnostic{
						Code:    "OOM001",
						Message: "unbounded heap allocation inside loop; wrap the loop body with `arena { ... }` to prevent OOM",
						Decl:    fn.Name,
					})
					break
				}
			}
		case *ExprStmt:
			if exprAllocatesHeap(s.X) {
				*diags = append(*diags, OOMDiagnostic{
					Code:    "OOM001",
					Message: "unbounded heap allocation inside loop; wrap the loop body with `arena { ... }` to prevent OOM",
					Decl:    fn.Name,
				})
			}
		case *IfStmt:
			checkLoopStmts(fn, s.Then, diags)
			checkLoopStmts(fn, s.Else, diags)
		case *WhileStmt:
			checkLoopStmts(fn, s.Body, diags)
		case *RangeStmt:
			checkLoopStmts(fn, s.Body, diags)
		}
	}
}

func exprAllocatesHeap(e Expr) bool {
	if e == nil {
		return false
	}
	allocates := false
	visitExpr(e, func(x Expr) {
		switch ex := x.(type) {
		case *MakeSlice, *MakeMap, *MakeChan:
			allocates = true
		case *Call:
			if ex.Callee == "make" || ex.Callee == "append" {
				allocates = true
			}
		case *Binary:
			// String concatenation involves dynamic heap allocation
			if ex.Op == "+" {
				if isStringExpr(ex.L) || isStringExpr(ex.R) {
					allocates = true
				}
			}
		}
	})
	return allocates
}

func isStringExpr(e Expr) bool {
	if e == nil {
		return false
	}
	switch x := e.(type) {
	case *StringLit:
		return true
	case *Call:
		return x.Callee == "str" || x.Callee == "to_string" || x.Callee == "sprintf"
	default:
		return false
	}
}
