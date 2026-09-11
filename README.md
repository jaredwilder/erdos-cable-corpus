# erdos-cable-corpus

The raw output of a machine formalization pipeline aimed at open Erdos problems: **914 Lean files
across 152 distinct problems**, shipped with all 937 kernel receipts.

891 of the 914 contain no `sorry` in their text. **That is a statement about the text, not about the
kernel.** Joining the receipts to the files (see `JOIN.json`, and the section below) shows **211
files with a clean axiom footprint and 267 that failed to compile** despite being textually
sorry-free. Read the table before quoting any number from this repository.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Read this before reading anything else

**891 sorry-free files does not mean 891 meaningful theorems, and it does not mean any Erdos
problem is closed.** These are small obligations, lemmas and finite checks emitted by a driver and
pushed through a Lean cable. A file being sorry-free means the kernel accepted what was written in
it. Whether what was written is interesting, or faithful to the problem it is filed under, is a
separate question that this release does not answer.

**This corpus has NOT been through the semantic blade gate.** Only the separate 160-file corpus at
github.com/jaredwilder/erdos152 was audited that way, and zero of those reached CERTIFIED. There is
no reason to expect this corpus to be cleaner. Treat every file as unaudited.

## Honest accounting of the receipts

| | |
|---|---|
| Lean files | 914 |
| sorry-free | 891 |
| distinct Erdos problems | 152 |
| receipts | 937 |
| receipts marked KERNEL_CHECKED | 421, across 119 problems |
| receipts with a clean axiom footprint | 218, across 46 problems |

**That gap is now closed, and closing it changed the headline. See `JOIN.json`.**

The receipts never keyed on filename. They key on a receipt **id**, and the Lean files carry that
id after a prefix (`LO14.cable.json` describes `msl_LO14.lean`). Matching on the id instead lifts
the join from **14 files to 767**, over **814 receipts**, and every one of those joins is confirmed
by requiring the receipt's own declared theorem name to appear in the file it was joined to. Zero
joins were accepted unconfirmed.

### What the per-file footprints turned out to say

| verdict | files |
|---|---|
| compiled with a **clean** axiom footprint | **211** |
| no `sorry` and no `sorryAx`, but the receipt records no clean footprint either way | 266 |
| **failed to compile** | **267** |
| contains `sorry` in its text | 23 |
| no receipt could be joined | 147 |
| | **914** |

### The 267 are the number that matters, and they correct this file

Those files contain **no `sorry` anywhere in their text**, and their receipts nonetheless record
`sorryAx` in the axiom footprint, `"status": "UNVERIFIED"` and `"exitCode": 1`. The reason is that
**Lean supplies `sorryAx` itself when elaboration fails.** The recorded errors are ordinary ones:
`maximum recursion depth has been reached`, and in one case ``Tactic `decide` proved that the
proposition`` went the other way.

So a file can be textually sorry-free and never have been accepted by the kernel at all.

**This means the count at the top of this README, 891 sorry-free, measures the text and not the
kernel, and it overstates what was verified.** The kernel-side reading of the same corpus is the
table above: 211 files with a clean footprint, 267 that failed to compile, and 147 that cannot be
spoken about either way because no receipt joins to them.

The original sentence here said the footprints were "not established" and called fixing the join an
open task. The task is done; the answer was worse than the guess. Publishing it is the point.

`MANIFEST.json` records, per file, its sha256, whether it contains `sorry`, its Erdos problem id,
and its receipt when one could be joined.

## Where the audited work is

- github.com/jaredwilder/erdos-theorems - 79 declarations, every one with a verified clean axiom
  footprint. That is the vetted set.
- github.com/jaredwilder/erdos152 - 160 statement formalizations with a full defect audit.
- github.com/jaredwilder/lean-semantic-blades - the auditor.

This repository is the unfiltered upstream of that work, published because withholding the raw pile
while showing only the polished subset is how corpora become untrustworthy.

## License

Apache-2.0.
