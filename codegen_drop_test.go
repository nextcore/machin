package main

import (
	"strings"
	"testing"
)

func TestCodegen_DropOnLastUse(t *testing.T) {
	src := `
func compute() {
	s := "temporary string"
	println(s)
	x := 42
	println(x)
}
func main() { compute() }
`
	decls, err := splitFunctions(src)
	if err != nil {
		t.Fatalf("splitFunctions failed: %v", err)
	}
	prog, err := ParseProgram(decls)
	if err != nil {
		t.Fatalf("ParseProgram failed: %v", err)
	}

	csrc, err := CompileToC(prog, false)
	if err != nil {
		t.Fatalf("CompileToC failed: %v", err)
	}

	// Pastikan mfl_release di-emit untuk variabel s tepat setelah statement println(s)
	if !strings.Contains(csrc, "mfl_release((void*)v_s") {
		t.Fatalf("expected mfl_release for v_s in emitted C, got:\n%s", csrc)
	}
}
