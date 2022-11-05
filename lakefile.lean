import Lake
open Lake DSL

package parsec {
  srcDir := "src"
  precompileModules := true
}

@[default_target]
lean_lib Parsec
