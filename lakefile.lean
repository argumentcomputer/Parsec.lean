import Lake
open Lake DSL

package parsec {
  srcDir := "src"
  precompileModules := true
}

@[defaultTarget]
lean_lib Parsec
