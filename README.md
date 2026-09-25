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
- **Formally verified** — a linked machine-checked formalization is included and its verification process is documented.

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
```

Website pages may be shorter or more editorial. They should link to the corresponding permanent result record here.

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
