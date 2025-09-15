import Lake
open Lake DSL

package turan3

require mathlib from
  git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib turan3

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"