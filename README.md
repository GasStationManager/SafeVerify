# SafeVerify

The purpose of this script is to check whether a file of submitted Lean code and/or proof matches the specifications.
This is safer than direct checking with the Lean compiler or REPL, because it guards against potential exploits, including manipulation of environment via metaprogramming,
using additional axioms, and exploitation of buggy tactics.
Currently it serves as the proof-checking backend of
- [Provably-Correct Vibe Coding](http://ProvablyCorrectVibeCoding.com), a web app for vibe coding in Lean,
- [Code with Proofs: the Arena](https://github.com/GasStationManager/CodeProofTheArena), a website for coding problems with proofs of correctness, and
- [TheoremMarketplace](https://github.com/wadimiusz/lean-contract-interact), smart contracts for theorem bounties.

The branch `minif2f-deepseek-check` contains a version backported to Lean 4.9.0. This can be used to check [DeepSeek Prover V2's solutions to MiniF2F](https://github.com/deepseek-ai/DeepSeek-Prover-V2/tree/main). Similarly, the branch `minif2f-kimina-check` contains a version with Lean 4.15.0 that can be used to check [Kimina-Prover-Preview's and Kimina-Prover's solutions to MiniF2F](https://github.com/MoonshotAI/Kimina-Prover-Preview). The branch `abc-trinity-check` contains a version with Lean 4.20.0 that can be used to check [Trinity's autoformalization of the de Bruijin bound on the ABC conjecture](https://github.com/morph-labs/lean-abc-true-almost-always/). The branch `seed-prover-check` contains a version with Lean 4.14.0, that can be used to check [Seed Prover's published solutions, including IMO 2025](https://github.com/ByteDance-Seed/Seed-Prover/tree/main/SeedProver).


This is part of a broader effort to create [safe and hallucination-free coding AIs](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html).

In more detail: the script takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
The first file (the target) may contain theorem / function signatures with `sorry` in their bodies;
the second file is expected to fill them.
Uses `Environment.replay` to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.

Most of the code is adapted from [lean4checker](https://github.com/leanprover/lean4checker/). With suggestions taken from users on [Lean Zulip](https://leanprover.zulipchat.com/).

# List of checks performed by the script

- For both input files, run the content of the files through `Environment.replay`.
  - This is the same check as what `lean4checker` performs, re-checking each declaration with the kernel. Emits an exception if a declaration is not accepted by the kernel (possibly due to environment manipulation).
  - This only replays the content of the file, not the imports. To also replay the imports, you'll need to modify the script to match what `lean4checker --fresh` does.
- The remaining checks are done on the replayed environments of both files. This ensures that the checks are not affected by any environment manipulations
- For each declaration from the target file, make sure a declaration of the same name, kind (def / theorem) and type is in the submission file.
- For definitions, also check that their bodies are the same. Execpt for cases where the target file's definition depends on `sorry`, in which case the submission file's definition body is allowed to be different.
  - This tries to capture both the case of complete definitions that are not meant to be changed, and definition stubs with sorrys that are meant to be filled.
  - What if there is a function `g` that is complete, but in its body calls a function `f` that contains a sorry? Then function `g` also depends on `sorry` and therefore its body (not type) can be modified. If you don't want `g` to be modified, one approach is to make `g` take a function (with f's type) as input. Or use a different mechansim to denote which defs / theorems are allowed to be modified. 
- Check the submission file's definitions and theorems to make sure they only depends on the three standard axioms: `propext`, `Quot.sound`, `Classical.choice`.
  - uses `CollectAxioms.collect`
  - You may modify the `AllowedAxioms` list in the script to tighten or widen the set of allowed axioms.
- For each definition in the target or submission file, if it is marked `partial` or `unsafe`, throw an exception.
  - This requirement is perhaps more specific to the use case of verifying [solutions to coding tasks with proofs of correctness](https://github.com/GasStationManager/CodeProofTheArena). There the use of partial/unsafe functions could allow infinite loops that satisfy the type requirement.

Things that SafeVerify does not check, that you may want to check via other means:

- Use of keywords like `implemented_by`, `extern`, `uncomputable`: these are difficult to catch at the level of olean files which SafeVerify works in, but depending on use case you may choose to scan for and ban them at the source level. see e.g. [judge.py in CodeProofTheArena](https://github.com/GasStationManager/CodeProofTheArena/blob/main/app/services/judge.py).

# Usage

First step is to compile lean files into `.olean` files. E.g.
```
lake env lean -o submission.olean submission.lean
```
Then pass the olean files to the tool:
```
lake env lean --run Main.lean target.olean submission.olean
```

# Building an executable

```
lake build
```
will build the executable at `.lake/build/bin/safe_verify`.
