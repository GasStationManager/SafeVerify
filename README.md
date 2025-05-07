# SafeVerify

The purpose of this script is to check whether a file of submitted Lean code and/or proof matches the specifications.
This is safer than direct checking with the Lean compiler or REPL, because it guards against potential exploits, including manipulation of environment via metaprogramming,
using additional axioms, and exploitation of buggy tactics.
Currently it serves as the proof-checking backend of
- [Code with Proofs: the Arena](https://github.com/GasStationManager/CodeProofTheArena), a website for coding problems with proofs of correctness, and
- [TheoremMarketplace](https://github.com/wadimiusz/lean-contract-interact), smart contracts for theorem bounties.

The branch `minif2f-deepseek-check` contains a version backported to Lean 4.9.0. This can be used to check [DeepSeek Prover V2's solutions to MiniF2F](https://github.com/deepseek-ai/DeepSeek-Prover-V2/tree/main). 

This is part of a broader effort to create [safe and hallucination-free coding AIs](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html).

In more detail: it takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
The first file (the target) may contain theorem / function signatures with `sorry` in their bodies;
the second file is expected to fill them.
Uses Environment.replay to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.

Most of the code is adapted from [lean4checker](https://github.com/leanprover/lean4checker/). With suggestions taken from users on [Lean Zulip](https://leanprover.zulipchat.com/).


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
