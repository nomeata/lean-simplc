import Lake
open Lake DSL

package «simplc» where
  -- add package configuration options here

require std from git "https://github.com/leanprover/std4" @ "bump/v4.6.0"

@[default_target]
lean_lib «Simplc» where
  precompileModules := true
  -- add library configuration options here
