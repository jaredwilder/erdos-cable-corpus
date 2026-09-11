# erdos-cable-corpus

The raw output of a machine formalization pipeline aimed at open Erdos problems: **914 Lean files
across 152 distinct problems, 891 of them sorry-free**, shipped with all 937 kernel receipts.

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

**The known gap:** only **14 of 914** Lean files could be joined to their receipt by filename. The
receipts use ids of their own and the naming does not line up. So the per-file axiom footprints in
this release are **not established**, and the 218 and 46 above are receipt-side aggregates that
cannot currently be attributed to specific files. Fixing that join is an open task and I would
rather publish the gap than paper over it.

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
