import Lake
open Lake DSL

package "ConsistentHistories" where
  version := v!"0.1.0"

@[default_target]
lean_lib «ConsistentHistories» where
  -- add library configuration options here
