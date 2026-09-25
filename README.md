# Steps Unbounded Results

Canonical technical archive for results published through [Steps Unbounded](https://stepsunbounded.com).

This repository is the **record**: full statements, supporting material, verification code, and reproducibility notes belong here. The website presents results in a readable form and links back to this archive.

```text
research / working material
        │ deliberate promotion
        ▼
steps-unbounded-results   canonical technical archive
        │ deliberate presentation
        ▼
stepsunbounded.com        public website
```

Material should be promoted here deliberately when it is ready to preserve. If the website and this repository ever disagree about the technical content of a result, this repository should be treated as the canonical record.

## Result identifiers

Each result receives a permanent identifier such as `R001`, `R002`, and so on. Identifiers should never be reused.

## Status convention

Suggested statuses:

- **Conjecture** — no complete proof is claimed.
- **Informally proven** — a complete argument is presented, but no machine-checked proof is claimed.
- **Computationally verified** — the stated computational checks are reproducible from material in this repository.
- **Lean verified** — a linked Lean formalization is built by this repository's CI and included in the axiom audit.

Use only the statuses that actually apply to a result, and state any limitations explicitly.

## Structure

```text
results/
  R001.md              # canonical record for a result
  R002.md
verify/
  R001/                 # verification or reproduction code/data for R001
  R002/
notes/
  ...                   # supporting research notes worth preserving
templates/
  result.md             # starting point for a new result record
lean/
  lean-toolchain        # pinned Lean version
  lakefile.lean         # pinned mathlib dependency and library definition
  StepsUnboundedResults.lean
  StepsUnboundedResults/
    Foundation.lean
    R001.lean           # one module per formalized result, when applicable
  AxiomAudit.lean       # explicit audit of headline theorems
.github/workflows/
  lean.yml              # reproducible Lean CI
```

Website pages may be shorter or more editorial. They should link to the corresponding permanent result record here.

## Lean formalizations

The Lean environment is pinned to Lean 4.32.0 and mathlib v4.32.0. To reproduce a build locally:

```bash
cd lean
lake exe cache get
lake build StepsUnboundedResults
lake env lean AxiomAudit.lean
```

CI performs the same build whenever `lean/` or the Lean workflow changes. It also rejects formalized source files containing `sorry`, `admit`, or an explicit `axiom` declaration.

When a result becomes formally verified, add a module such as `lean/StepsUnboundedResults/R001.lean`, import it from `StepsUnboundedResults.lean`, and add `#print axioms` entries for its headline theorems to `AxiomAudit.lean`. A result should only be labelled **Lean verified** while that CI run is green.

## Result record contract

A result record should normally include:

1. Permanent identifier and title
2. Status
3. Statement or claim
4. Context and definitions
5. Proof, derivation, experiment, or evidence
6. Verification / reproduction instructions where applicable
7. Limitations and open questions
8. Links to associated files and the website presentation

## Repository policy

- Do not commit secrets, private keys, access tokens, or Cloudflare credentials.
- Keep reproducibility material beside the result it supports.
- Prefer stable filenames and permanent result identifiers over descriptive names that may change.
- Do not silently replace a published claim. Preserve enough history to understand meaningful revisions.

## Website

<https://stepsunbounded.com>
