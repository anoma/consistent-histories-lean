import Lake
open Lake DSL

package "ContForm" where
  version := v!"0.1.0"

@[default_target]
lean_lib «ContForm» where
  -- add library configuration options here
