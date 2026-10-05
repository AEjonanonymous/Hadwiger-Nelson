import Lake
open Lake DSL

package «HadwigerNelson» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Hadwiger_Nelson_Final» where
  srcDir := "."
