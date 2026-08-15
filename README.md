# A Formal Theory of Phonological Equivalence

Verification artifact for the doctoral dissertation *A Formal Theory of
Phonological Equivalence* (Alexandre Menezes Barroso, State University of
Campinas, Institute of Language Studies). The repository contains the data,
machine-checked proofs, and audit records that validate the dissertation's
registered mathematical results in three independent engines: Python 3,
Wolfram Mathematica, and Lean 4.

The dissertation is written to be auditable by hand: every theorem is proved
in the text and its appendices, and Appendix M gives an independent
reconstruction protocol that requires no software. This repository provides
the complementary machine route over the same registered content. Each
registered result is stated once as a typed formal specification, proved by a
replayable proof record, checked independently by at least two engines, and
bound to the dissertation's bilingual statement files by SHA-256 hash. The
artifact certifies the registered formal statements; it does not, and does not
claim to, establish literature priority, the fairness of source
transcriptions, or empirical ontology.

## What is certified

- **68 registered results** and **218 registered proof goals**, all
  discharged. Every proof goal has exactly one accepted proof record under
  `formal/proofs/`, replayed by the Python proof kernel and independently
  validated in Wolfram; 173 goals are additionally replayed as exact
  mathematics in Wolfram, and the remaining 45 universal goals are closed by
  the Lean kernel and referenced from Wolfram as pinned declaration checks.
- **Lean closure of the full registry.** The Lean package
  (`lean/PhonologicalCalculus`, 114 modules) covers all 68 results and all
  218 proof goals (`lean/reports/*.tsv`, every row `lean_closed`), under an
  axiom whitelist of `Classical.choice`, `Quot.sound`, and `propext`, with
  `sorry`, `admit`, `native_decide`, `unsafe`, and new axioms forbidden by an
  enforced token check, and an independent kernel re-check (`leanchecker
  --fresh`) recorded in `lean/logs/`.
- **Adversarial non-vacuity.** 90 mutated specifications
  (`formal/mutants/`) — one deliberate mathematical error each, including
  strict/non-strict inequality flips, wrong KKT multiplier signs, and wrong
  phase boundaries — are all rejected by both engines
  (`formal/reports/mutation_report.tsv`, kill rate 100%, zero survivors).
- **Cross-engine agreement** on all 68 result statuses and 218 proof goals
  (286 agreement records), plus a 15-anchor exact-value comparison between
  the Python and Wolfram engines (Kazakh profile, Kyrgyz grid winner,
  Goldrick–Daland distances, Walker boundary, ledger counts, and others).
- **A closed trusted foundation.** Everything assumed without in-tree proof
  is enumerated in `formal/foundation/` — 22 items: one axiom (exact real
  arithmetic), one software-semantic assumption, 12 imported standard
  theorems with citations, and 8 derived lemmas that carry their own proof
  records. Each item lists its downstream results and the exact withdrawal
  effect if it were removed. Assumptions are recorded as sufficient;
  necessity is explicitly not claimed.

## How the artifact binds to the dissertation

The dissertation states its results as numbered theorems in prose; the
artifact assigns each a stable registry identifier. The binding is by
content hash, not by convention: each specification in `formal/specs/`
embeds the SHA-256 of the canonical English and Portuguese statement texts,
and each statement-correspondence check in `formal/statement_checks/` pins
the dissertation's per-result LaTeX statement files by path and whole-file
SHA-256 (recorded results: `formal/reports/statement_correspondence.tsv`,
28 sub-checks per result, all PASS). The identifier groups map onto the
dissertation as follows.

| Group | Results | Content | Dissertation location |
| --- | --- | --- | --- |
| CALC | CALC-F1, CALC-R01–R15 | Qualified finite decision theorem and its fifteen boundary regressions | Ch. 2, App. B–C |
| FIN | FIN-A1–A7 | Finite representation, recovery, and information theorems | Ch. 3, App. D |
| MAX | MAX-G1–G9 | Exact finite Maximum Entropy results, including the Basic Syllable decomposition 121 = 105 + 16 | Ch. 4, App. E |
| CHG | CHG-B1–B16 | Directional continuous Harmonic Grammar: exact finite persistence, phases, limits | Ch. 6, App. F |
| CTX | CTX-C1–C2 | Contextual two-trigger interaction theorems | Ch. 6, App. G |
| FLUX | FLUX-D1–D5 | Constitutive response and identification theorems | Ch. 6, App. G |
| SUP | SUP-E1–E4 | Support, continuation, and endpoint theorems | Ch. 6, App. G |
| SEL | SEL-F1–F2 | Selected-output geometry, including the Goldrick–Daland selected-output reversal | Ch. 7, App. H |
| APP | APP-MCC-GRID, APP-MCC-LENGTH, APP-MCC-COMP, APP-BASIC | Exact applications to McCollum's continuous HG and the Basic Syllable system (e.g. the grid-versus-continuum winner 41/42) | Ch. 7 §§7.3–7.4, 7.7; App. H–I |
| DATA | DATA-PT-R1, DATA-EN-R1, DATA-ZH-R1 | Exact replays of the Portuguese, English, and Mandarin decision ledgers | Ch. 8, App. J |

Four additional source-facing application records
(`formal/application_specs/`, `formal/application_proofs/`) bind the Walker,
Pater et al., and Cabrera completions (Ch. 7 §7.8) and the Goldrick–Daland
application (Ch. 7 §7.6) to named Lean declarations in
`lean/PhonologicalCalculus/Application/SourceFacing.lean`, with the source
PDF hash, page anchors, and an explicit verification boundary separating
what Lean proves from what remains a transcription or interpretive claim.

## Repository layout

| Path | Contents |
| --- | --- |
| `data/canonical/` | Exact fixtures per result group (applications, continuous HG, MaxEnt, finite calculus) and the three empirical decision ledgers: Portuguese 72 cells, English 300 aggregate rows plus 14,135 speaker-scenario rows, Mandarin 639 rows with per-row source-TextGrid SHA-256 provenance |
| `data/schemas/` | One JSON Schema per canonical data file (36, matched 1:1 by title) |
| `data/wolfram_exports/` | Lossless exact-rational exports of the ledgers as embedded in the Wolfram engine, with a SHA-256 manifest (`manifest.tsv`) and the authoritative 68-entry result catalog (`wolfram_catalog.json`) |
| `formal/specs/` | 68 canonical result specifications: typed statements, assumptions, scope, explicit non-claims, withdrawal conditions, proof goals |
| `formal/proofs/` | 218 proof records (one per goal), foundation-lemma proofs, and the exact MaxEnt witness and semantic-closure objects |
| `formal/statement_checks/` | 68 bilingual statement-correspondence records |
| `formal/foundation/` | The 22-item trusted-foundation registry |
| `formal/mutants/` | 90 adversarial mutated specifications |
| `formal/source_transcriptions/` | Exact typed transcriptions of the printed fragments of the six published analyses, pinned to their PDFs by SHA-256 and page anchor |
| `formal/kernel/python/` | The Python proof-checking kernel: standard library only, exact integer and rational arithmetic, floating point rejected |
| `formal/kernel/wolfram/` | The Wolfram proof CLI, machine-closure and adversarial validators, and the neutral proof exporter |
| `formal/reports/` | The audit ledger of the certifying run: formal closure, proof inventory, statement correspondence, assumption reports, dependency closure, mutation report, source-conflict resolutions, kernel test report |
| `formal/traces/wolfram/` | Independent Wolfram-engine outputs: neutral AST export of all 218 proof goals, machine closure, adversarial results |
| `lean/` | The pinned Lean 4 package, verification scripts, coverage reports, and the captured logs of a complete passing run |
| `python/` | The build and validation library for the full artifact, and its 129-test suite |
| `wolfram/` | `SecondOrderPhonologyVerification.wl`, the self-contained executable catalog of all 68 results |

## Auditing the dissertation with this repository

The audits below are ordered by how little tooling they require. Paths are
relative to the repository root.

**1. No tooling: read the records.** `formal/reports/formal_closure.json`
and `release_attestation.json` state the certified counts and their scope
limits. `formal/reports/proof_inventory.tsv` registers every proof record
with its file hash and replay status. `lean/logs/` holds the build, axiom
audit, forbidden-token, and independent kernel-check logs of the passing
Lean run, and `lean/reports/` maps every result and proof goal to named Lean
declarations.

**2. Hash and count checks (any shell).** Recompute SHA-256 over the files
listed in `data/wolfram_exports/manifest.tsv` and compare. Re-derive the
ledger summary claims by counting rows: for example, the Mandarin ledger's
622 matches, 13 counterexamples, and 4 principled refusals from
`data/canonical/demonstrations/mandarin_rows.tsv`, or the 300 English
aggregate rows all reporting 14 positive medians. Validate any canonical
data file against its schema in `data/schemas/`.

**3. Python kernel replay (Python 3.10+, no dependencies).** With
`formal/kernel/python` on `PYTHONPATH`, `second_order_proof_kernel.CheckProofFile`
re-verifies a proof record against its specification from first principles:
statement hashes are recomputed, the proof method is re-executed with exact
arithmetic, and any float, unknown rule, or tampered hash is rejected. The
foundation registry replays completely (22/22), and 193 of the 218 proof
records replay from this tree alone; the remaining 25 (the three
corpus-ledger replays and the 22 MaxEnt semantic-closure records) also
require registry and source-ledger files that live in the dissertation
source repository and are not part of this snapshot.

**4. Wolfram replay (wolframscript).**
`wolframscript -script wolfram/SecondOrderPhonologyVerification.wl --run-all
--mode machine-strict --output <dir>` re-runs the executable catalog;
`--export-data` regenerates the ledger exports for byte comparison against
the shipped copies. `wolframscript -script
formal/kernel/wolfram/SecondOrderProofCLI.wl --adversarial` re-runs the
90-mutant kill suite. Exit codes are deterministic and documented in each
CLI's help text.

**5. Lean rebuild (elan/Lake, network required for Mathlib).** The package
pins `leanprover/lean4:v4.32.2` and Mathlib revision `905b95818eb3` via
`lean/lean-toolchain` and `lean/lake-manifest.json`. `lake build` from
`lean/` re-elaborates all 114 modules; `lake env leanchecker --fresh
PhonologicalCalculus.All` repeats the independent kernel check;
`sh lean/scripts/check_forbidden_tokens.sh` re-verifies the token policy.
The full `lean/scripts/verify.sh` orchestrator additionally regenerates
coverage from registry files kept in the dissertation source repository.

## Provenance and non-redistribution

The six published analyses that source-facing results depend on are pinned
in `formal/source_transcriptions/` by PDF SHA-256 and page anchor; the PDFs
themselves are deliberately not redistributed. The three speech corpora
behind the empirical ledgers (CORAA NURC-SP, VCTK, AISHELL-3) are likewise
not redistributed; the ledgers carry per-row provenance (including per-row
source-TextGrid SHA-256 for Mandarin), and the dissertation records the
corpus licenses and their limits. Source-facing results are conditional on
the registered transcriptions: `formal/reports/source_conflicts.tsv`
documents 21 material transcription discrepancies and their resolutions.

## Recorded toolchain

The shipped reports record one complete certifying run: Python 3.12.3,
Wolfram 15.0.1, Lean 4.32.2 (Lake 5.0.0, elan 4.2.3) with Mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`, on macOS arm64. Reproduction of
engine runs requires those toolchains; the record-level audits in steps 1–3
above require only a shell and Python.

## Snapshot limitations

This repository is a flattened extract of the dissertation's full
deliverables tree, and some recorded paths refer to that original layout.
Not shipped here: the `registry/` tables, the bilingual per-result LaTeX
statement files (`proofs/en|pt_BR/results/*.tex`) whose hashes the
statement checks record, the corpus source ledgers named by the three
data-replay proofs, and the orchestration scripts of the full build
pipeline. Consequently the statement-correspondence file hashes and the 25
proof records noted above can be re-verified only against the dissertation
source repository, and the Python build library under `python/` documents
the full artifact rather than running from this tree. One known
inconsistency is, as of now, preserved to be fixed later: `data/canonical/wolfram_exports/`
contains an earlier snapshot of `wolfram_catalog.json`; the authoritative,
manifest-pinned copy is `data/wolfram_exports/wolfram_catalog.json`.

The reason for not shipping the whole deliverables package is simply storage space and convenience, as mostly of the other files relate to the internal development history, version registry, and so on. They are not needed for the full audit. In a next release, before my PhD defense, I will re-organize this repo so it is more self-contained, instead of having older hashes, directory mismatches, internal machine paths, and so on. Still, as I said, from the existing files in this repo, a reader can absolutely reconstruct and validate/audit my whole research without a problem, it is simply messy right now. In this next release, I also intend to provide here an English language version of my final dissertation that will serve as this repo's official documentation.
