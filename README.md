# Lean corpus across 152 Erdős problems

A public corpus of **914 Lean files across 152 distinct Erdős problems**, with **937 verification receipts** and a completed file-to-receipt audit. The audit separates what compiled cleanly from what merely looked complete in text.

Current status:

- **211** files compiled with a clean axiom footprint;
- **266** are textually free of `sorry` but have no clean-footprint verdict recorded;
- **267** failed to compile;
- **23** contain `sorry` in the source;
- **147** have no joined verification receipt.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Why the distinction matters

The often-quoted **891 sorry-free** count is only a textual property. It does not tell you whether Lean accepted the file or which axioms the resulting theorem depends on.

`JOIN.json` matches verification receipts to Lean files by receipt id and confirms each match by requiring the declared theorem name to appear in the file. That process joins **767 files through 814 receipts**, with zero unconfirmed joins.

| status | files |
|---|---:|
| compiled with a **clean** axiom footprint | **211** |
| no `sorry` / `sorryAx`, but no clean-footprint verdict recorded | 266 |
| failed to compile | **267** |
| contains `sorry` in its text | 23 |
| no joined receipt | 147 |
| **total** | **914** |

A file can contain no literal `sorry` and still fail elaboration; in some cases Lean then introduces `sorryAx`. That is why the compile/axiom audit is the meaningful status layer.

## Receipt accounting

| | |
|---|---:|
| Lean files | 914 |
| textually sorry-free | 891 |
| distinct Erdős problems | 152 |
| receipts | 937 |
| receipts marked `KERNEL_CHECKED` | 421 across 119 problems |
| receipts reporting a clean axiom footprint | 218 across 46 problems |

The original verification records were keyed by receipt id rather than filename. Reconstructing that mapping increased the usable join from 14 files to 767 and exposed the compile-status distribution above.

The **267 failed files remain in the corpus** because their failures are useful data about formalization attempts: recursion limits, elaboration errors, type mismatches, or finite decisions evaluating the opposite way from the proposed statement.

`MANIFEST.json` records each file's SHA-256, Erdős problem id, presence of `sorry`, and joined receipt when one exists.

## Mathematical role

This is a raw formalization corpus: small obligations, lemmas, finite checks, and unsuccessful formalization attempts produced while working on open Erdős problems. It is useful for provenance, formalization research, and extracting statements for later review.

For more curated layers, see:

- `jaredwilder/erdos-theorems` — 79 declarations with clean axiom-footprint accounting;
- `jaredwilder/erdos152` — 160 statement formalizations with a semantic audit;
- `jaredwilder/lean-semantic-blades` — 33 semantic checks for source fidelity.

The 914-file corpus has not itself been through that semantic comparison, so source fidelity is a separate question from successful Lean compilation.

## License

Apache-2.0.