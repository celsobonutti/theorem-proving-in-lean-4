import Lake
open Lake DSL

package «theorem-proving» where
  -- add package configuration options here

lean_lib «TheoremProving» where
  -- add library configuration options here

@[default_target]
lean_exe «theorem-proving» where
  root := `Main
