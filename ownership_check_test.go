package main

import (
	"testing"
)

func TestOwnershipCheck_LastUseDetection(t *testing.T) {
	src := `
func test_last_use() {
	x := "hello"
	println(x)
	y := "world"
	println(y)
}
func main() { test_last_use() }
`
	decls, err := splitFunctions(src)
	if err != nil {
		t.Fatalf("splitFunctions failed: %v", err)
	}
	prog, err := ParseProgram(decls)
	if err != nil {
		t.Fatalf("ParseProgram failed: %v", err)
	}
	ctx, err := Check(prog)
	if err != nil {
		t.Fatalf("Check failed: %v", err)
	}

	diags, liveness := AnalyzeOwnership(prog, ctx)
	if len(diags) > 0 {
		t.Fatalf("unexpected diagnostics: %v", diags)
	}

	// Cari fungsi test_last_use
	var targetFn *FuncDecl
	for _, fn := range prog.Funcs {
		if fn.Name == "test_last_use" {
			targetFn = fn
			break
		}
	}
	if targetFn == nil {
		t.Fatal("target function test_last_use not found")
	}

	info := liveness[targetFn]
	if info == nil {
		t.Fatal("no liveness info for test_last_use")
	}

	// Pastikan ada statement yang mencatat last-use untuk x dan y
	foundX := false
	foundY := false
	for _, vars := range info.LastUses {
		for _, v := range vars {
			if v == "x" {
				foundX = true
			}
			if v == "y" {
				foundY = true
			}
		}
	}

	if !foundX || !foundY {
		t.Fatalf("expected last-use for x and y, got foundX=%v, foundY=%v", foundX, foundY)
	}
}

func TestOwnershipCheck_UseAfterMove(t *testing.T) {
	src := `
func test_move() {
	ch := make(chan string)
	msg := "important"
	ch <- msg
	println(msg)
}
func main() { test_move() }
`
	decls, err := splitFunctions(src)
	if err != nil {
		t.Fatalf("splitFunctions failed: %v", err)
	}
	prog, err := ParseProgram(decls)
	if err != nil {
		t.Fatalf("ParseProgram failed: %v", err)
	}
	ctx, err := Check(prog)
	if err != nil {
		t.Fatalf("Check failed: %v", err)
	}

	diags, _ := AnalyzeOwnership(prog, ctx)
	if len(diags) == 0 {
		t.Fatal("expected OWN002 use-after-move error, but got none")
	}

	matched := false
	for _, d := range diags {
		if d.Code == "OWN002" && d.VarName == "msg" {
			matched = true
			break
		}
	}
	if !matched {
		t.Fatalf("expected OWN002 for msg, got %v", diags)
	}
}
