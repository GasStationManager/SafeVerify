# SafeVerify (Work In Progress)

Takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
First file (the target) may contain theorem / function signature with sorry in their bodies;
the second file is expected to fill them.
Uses Environment.replay to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.

# Usage

First step is to compile lean file into `.olean` files. E.g.
```
lake env lean -o submission.olean submission.lean
```
Then pass the olean files to the tool:
```
lake env lean --run Main.lean target.olean submission.olean
```
