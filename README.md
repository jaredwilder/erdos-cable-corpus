# erdos-cable-corpus

**A 914-file Lean corpus across 152 distinct Erdős problems, shipped with 937 receipts and a
completed file-to-receipt audit.** The joined corpus resolves to **211 clean-footprint compiled
files, 266 textually sorry-free files without a clean-footprint verdict, 267 compile failures, 23
files containing `sorry`, and 147 files with no joined receipt.**

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Corpus status

The often-quoted **891 sorry-free** count is a textual property only. The kernel-side status comes
from `JOIN.json`, which matches receipt ids to Lean files and confirms each join by requiring the
receipt's declared theorem name to appear in the matched file.

That join covers **767 files through 814 receipts**, with zero unconfirmed joins.

| verdict | files |
|---|---:|
| compiled with a **clean** axiom footprint | **211** |
| no `sorry` and no `sorryAx`, but no clean-footprint verdict recorded | 266 |
| **failed to compile** | **267** |
| contains `sorry` in its text | 23 |
| no receipt could be joined | 147 |
| **total** | **914** |

The distinction matters because Lean may introduce `sorryAx` when elaboration fails. A file can be
textually free of `sorry` and still never have been accepted by the kernel.

## Receipt accounting

| | |
|---|---:|
| Lean files | 914 |
| textually sorry-free | 891 |
| distinct Erdős problems | 152 |
| receipts | 937 |
| receipts marked `KERNEL_CHECKED` | 421 across 119 problems |
| receipts reporting a clean axiom footprint | 218 across 46 problems |

The original pipeline keyed receipts by receipt id rather than filename. Matching on that id lifted
the usable join from 14 files to 767 and exposed the true compile-status distribution above.

The 267 failed files are preserved because they are informative. Their receipts record ordinary
elaboration failures such as maximum recursion depth, or a `decide` result going the opposite way.
That failure data is part of the corpus, not a judgment on the 211 files that did compile cleanly.

`MANIFEST.json` records, per file, its SHA-256, whether it contains `sorry`, its Erdős problem id,
and its joined receipt when one exists.

## Mathematical role

This repository is the **raw formalization upstream**: small obligations, lemmas, finite checks,
and failed formalization attempts emitted while attacking open Erdős problems. It is useful as a
large provenance corpus and as a source of formal objects for later semantic review.

For curated audited mathematics, see:

- `jaredwilder/erdos-theorems` — 79 declarations with clean axiom-footprint accounting;
- `jaredwilder/erdos152` — 160 statement formalizations with a full semantic defect audit;
- `jaredwilder/lean-semantic-blades` — the 33-blade semantic gate.

The cable corpus itself has **not** been passed through the semantic blade gate, so semantic fidelity
must be checked separately from kernel acceptance.

## License

Apache-2.0.
