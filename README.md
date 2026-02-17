# SafeVerify

The purpose of this script is to check whether a file of submitted Lean code and/or proof matches the specifications.
This is safer than direct checking with the Lean compiler or REPL, because it guards against potential exploits, including manipulation of environment via metaprogramming,
using additional axioms, and exploitation of buggy tactics.
Currently it serves as the proof-checking backend of
- [Provably-Correct Vibe Coding](http://ProvablyCorrectVibeCoding.com), a web app for vibe coding in Lean,
- [Code with Proofs: the Arena](https://github.com/GasStationManager/CodeProofTheArena), a website for coding problems with proofs of correctness, and
- [TheoremMarketplace](https://github.com/wadimiusz/lean-contract-interact), smart contracts for theorem bounties.

The branch `minif2f-deepseek-check` contains a version backported to Lean 4.9.0. This can be used to check [DeepSeek Prover V2's solutions to MiniF2F](https://github.com/deepseek-ai/DeepSeek-Prover-V2/tree/main). Similarly, the branch `minif2f-kimina-check` contains a version with Lean 4.15.0 that can be used to check [Kimina-Prover-Preview's and Kimina-Prover's solutions to MiniF2F](https://github.com/MoonshotAI/Kimina-Prover-Preview). The branch `abc-trinity-check` contains a version with Lean 4.20.0 that can be used to check [Trinity's autoformalization of the de Bruijin bound on the ABC conjecture](https://github.com/morph-labs/lean-abc-true-almost-always/). The branch `seed-prover-check` contains a version with Lean 4.14.0, that can be used to check [Seed Prover's published solutions, including IMO 2025](https://github.com/ByteDance-Seed/Seed-Prover/tree/main/SeedProver). SafeVerify has been used by [PutnamBench's official leaderboard](https://trishullab.github.io/PutnamBench/leaderboard.html) to verify some of the submitted solutions. 


This is part of a broader effort to create [safe and hallucination-free coding AIs](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html).

In more detail: the script takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
The first file (the target) may contain theorem / function signatures with `sorry` in their bodies;
the second file is expected to fill them.
Uses `Environment.replay` to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.

Most of the code is adapted from [lean4checker](https://github.com/leanprover/lean4checker/). With suggestions taken from users on [Lean Zulip](https://leanprover.zulipchat.com/).

## List of checks performed by the script

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

- Use of keywords like `implemented_by`, `extern`, `noncomputable`: these are difficult to catch at the level of olean files which SafeVerify works in, but depending on use case you may choose to scan for and ban them at the source level. see e.g. [judge.py in CodeProofTheArena](https://github.com/GasStationManager/CodeProofTheArena/blob/main/app/services/judge.py).
- Potential attacks that exploit code execution during compilation to modify the filesystem. You may want to do compilation in a sandbox to produce the olean files, then pass the olean files to SafeVerify.

## Usage

First step is to compile lean files into `.olean` files. E.g.
```
lake env lean -o submission.olean submission.lean
```
Then pass the olean files to the tool:
```
lake env lean --run Main.lean target.olean submission.olean
```

## Building an executable

```
lake build
```
will build the script as an executable at `.lake/build/bin/safe_verify`. You can then run the executable by
```
lake exe safe_verify target.olean submission.olean
```

## Command-Line Flags

SafeVerify accepts the following command-line flags:

- `--disallow-partial`: Disallow partial definitions. When enabled, any partial constant will cause SafeVerify to throw an error. This is useful for preventing infinite loops that could satisfy type requirements.
- `-v, --verbose`: Enable verbose error messages. When enabled, SafeVerify will print detailed type information for mismatches, including expected vs. actual types, level parameters, and values.
- `-s, --save <filepath>`: Save the verification output to a JSON file at the specified path. The JSON contains detailed information about each declaration checked.

**Example usage:**
```bash
# Run with verbose output
lake exe safe_verify --verbose target.olean submission.olean

# Run with partial definitions disallowed
lake exe safe_verify --disallow-partial target.olean submission.olean

# Run and save output to JSON
lake exe safe_verify --save output.json target.olean submission.olean

# Combine multiple flags
lake exe safe_verify -v --disallow-partial -s output.json target.olean submission.olean
```

## Output Format

When SafeVerify runs, it produces the following output:

### Standard Output

1. **Header information:**
   ```
   Currently running on Lean v<version>
   Running SafeVerify on target file: <target.olean> and submission file: <submission.olean>.
   ```

2. **Replay progress:**
   ```
   ------------------
   Replaying <target.olean>
   Finished setting up the environment.
   Finished replay. Found <N> declarations.
   ------------------
   Replaying <submission.olean>
   Finished setting up the environment.
   Finished replay. Found <N> declarations.
   ------------------
   ```

3. **Verification results:**
   - If all checks pass: `Finished.`
   - If checks fail: Error messages are printed to stderr (see below)

### Error Output

When SafeVerify detects problems, it prints error messages to stderr. Each error follows this format:

```
Found a problem in <submission.olean> with declaration <name>: <failure-description>
```

When the `--verbose` flag is enabled, additional details are provided depending on the failure type:
- **Theorem type mismatch:** Shows expected vs. actual types and level parameters
- **Definition mismatch:** Shows type, level parameter, safety, and value differences
- **Opaque mismatch:** Shows type, level parameter, safety (isUnsafe), and value differences
- **Disallowed axioms:** Lists which axioms were used that are not allowed

### JSON Output

When using the `--save` flag, SafeVerify outputs a JSON file containing an array of verification outcomes. Each outcome has the following structure:

```json
{
  "targetInfo": {
    "constInfo": {"kind": "theorem"},
    "axioms": ["propext", "Classical.choice"]
  },
  "solutionInfo": {
    "constInfo": {"kind": "theorem"},
    "axioms": ["propext", "Classical.choice"]
  },
  "failureMode": null
}
```

- `targetInfo`: Information about the declaration in the target file
- `solutionInfo`: Information about the corresponding declaration in the submission file (or `null` if not found)
- `failureMode`: The type of failure that occurred (or `null` if the check passed)

## Possible Verification Outcomes

When comparing declarations between the target and submission files, SafeVerify produces one of the following outcomes:

### Success
- **No failure mode:** The declaration in the submission file matches the target declaration in all required ways (same name, kind, type, and value where applicable).

### Failure Modes

1. **`declaration not found in submission`**
   - The target file contains a declaration that does not exist in the submission file.

2. **`kind mismatch (expected <kind1>, got <kind2>)`**
   - The declaration exists but has the wrong kind. For example, the target expects a `theorem` but the submission provides a `def`.
   - Possible kinds: `axiom`, `def`, `theorem`, `opaque`, `quot`, `inductive`, `constructor`, `recursor`

3. **`theorem type mismatch`**
   - The declaration is a theorem but its type differs from the target theorem's type.
   - With `--verbose`: Shows expected and actual types, including level parameters if they differ.

4. **`definition type or value mismatch`**
   - The declaration is a definition but either:
     - Its type differs from the target, or
     - Its value (body) differs from the target (only checked when the target doesn't depend on `sorry`)
   - With `--verbose`: Shows type mismatches, level parameter mismatches, safety mismatches, and indicates if values differ.

5. **`opaque type or value mismatch`**
   - The declaration is opaque but either:
     - Its type differs from the target, or
     - Its value differs from the target, or
     - Its safety properties differ
   - With `--verbose`: Shows type mismatches, level parameter mismatches, safety (isUnsafe) mismatches, and indicates if values differ.

6. **`uses disallowed axioms`**
   - The declaration uses axioms beyond the three standard allowed axioms: `propext`, `Quot.sound`, and `Classical.choice`.
   - With `--verbose`: Lists the specific disallowed axioms that were used.

### Exit Codes

- `0`: All checks passed successfully
- Non-zero: Verification failed (an error was thrown)

## What if the proof contains `native_decide`?

Currently, proofs containing `native_decide` will not pass SafeVerify, partially due to the additional dependence on the axoim `ofReduceBool`, but also the fact that a proof term is not produced, and therefore cannot be sent to the kernel. You may consider using [ReplaceNativeDecide](https://github.com/GasStationManager/ReplaceNativeDecide) to replace the uses of `native_decide` with explicit proofs, then pass the updated proof to SafeVerify so that the rest of the proof can be checked.
