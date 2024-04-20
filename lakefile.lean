import Lake
open Lake DSL

package shred where
  -- add package configuration options here

lean_lib PosNat where
  -- add library configuration options here

@[default_target]
lean_exe shred where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
