# A Formal Theory of Phonological Equivalence

[![DOI](https://zenodo.org/badge/1334718126.svg)](https://doi.org/10.5281/zenodo.21941367)

This repository contains the public code and data accompanying my doctoral dissertation, that can be found [here](https://phd.alexandrebarroso.com). It collects the exact calculations, formal
proofs, worked examples, and reduced empirical tables used in the dissertation. The formal aspects of this research were developed between 2024 and 2026. See also [PhonoScript Project](https://github.com/alexandre-barroso/phonoscript_project).

## Contents

- `data/` contains the distributed research data:
  - `corpora.tar.xz` is the compressed folder containing the text transcriptions (.txt files) and TextGrids (.TextGrid files) of the data utilized (40 hours of (diverse) British English, 40 hours of Northern/Southern Mandarin, and 160 hours of Paulista Brazilian Portuguese). Raw speech corpora and audio are not redistributed here, due to licensing and storage reasons;
  - `applications/` gives the Basic Syllable, McCollum, Goldrick-Daland,
    Walker, Pater, and Cabrera examples;
  - `continuous_hg/` gives exact profiles, support boundaries, continuation
    comparisons, and identifiability examples;
  - `demonstrations/` gives the Portuguese, English, and Mandarin decision
    tables;
  - `finite_calculus/` gives a complete typed-contract example; and
  - `maxent/` gives exact finite-MaxEnt examples and counterexamples.
- `python/` contains standard-library exact-arithmetic implementations of the
  finite, MaxEnt, continuous-HG, contextual, flux, application, and
  support-selection calculations.
- `wolfram/` contains symbolic MaxEnt calculations in the Wolfram Language.
- `lean/` contains the Lean proofs for the finite calculus, representation
  results, MaxEnt, continuous HG, selection, support, and applications.

## Python

Python 3.10 or later is sufficient; the package has no third-party
dependencies. For example:

```sh
PYTHONPATH=python python3 - <<'PY'
from fractions import Fraction
from phonological_equivalence import QuadraticProfile

print(QuadraticProfile(Fraction(5), Fraction(1), 6))
PY
```

The result is the exact quadratic continuous-HG profile
`[1, 3/5, 3/10, 1/10, 0, 0, 0]`.

## Wolfram Language

With Wolfram Language installed, the two MaxEnt calculation groups can be
evaluated directly:

```sh
wolframscript -code 'Get["wolfram/MaxEntG1G5.wl"]; Print[MaxEntG1G5Calculations`MaxEntG1G5Results[]]'
wolframscript -code 'Get["wolfram/MaxEntG6G9.wl"]; Print[MaxEntG6G9Calculations`MaxEntG6G9Results[]]'
```

## Lean

The Lean sources form one library. From the `lean/` directory, run:

```sh
lake build
```

The toolchain and Mathlib dependency are declared in that directory.

## Data conventions

The tab-separated files have a header row and preserve exact rational values
as strings such as `41/42`; decimal columns are included only for reading and
plotting. The empirical tables are reduced or derived data used by the
dissertation's declared readers.

The dissertation remains the source for theorem statements, proofs in prose,
linguistic interpretation, empirical premises, and scope limitations. These
files supply the corresponding public calculations and data annotations.
