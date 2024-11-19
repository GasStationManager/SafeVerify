# SafeVerify (Work In Progress)

The purpose of this script is to check user's submitted Lean code and/or proof matches the specifications. Will be used by  [Code with Proofs: the Arena](https://github.com/GasStationManager/CodeProofTheArena)
and [lean-contract-interact](https://github.com/wadimiusz/lean-contract-interact) projects as proof-checking backend. 

Takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
First file (the target) may contain theorem / function signature with sorry in their bodies;
the second file is expected to fill them.
Uses Environment.replay to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.

# Usage

First step is to compile lean files into `.olean` files. E.g.
```
lake env lean -o submission.olean submission.lean
```
Then pass the olean files to the tool:
```
lake env lean --run Main.lean target.olean submission.olean
```
