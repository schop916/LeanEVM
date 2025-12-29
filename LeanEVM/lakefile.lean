import Lake
open Lake DSL

package «lean-evm» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "main"

@[default_target]
lean_lib «LeanEVM» where
  globs := #[.submodules `LeanEVM]

lean_lib «LearnEVM» where
  globs := #[.submodules `LearnEVM]

lean_lib «Lab» where
  globs := #[.submodules `Lab]

lean_lib «Translator» where
  globs := #[.submodules `Translator]

lean_lib «Generated» where
  globs := #[.submodules `Generated]
