# One Edge, Unbounded Instability

[![Software archive DOI](https://zenodo.org/badge/1320866980.svg)](https://doi.org/10.5281/zenodo.21764640)
[![Paper DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21764586.svg)](https://doi.org/10.5281/zenodo.21764586)

This repository accompanies the preprint:

> Anton Künzi, *One Edge, Unbounded Instability: Hilbert Decomposition Signed
> Measures in Multiparameter Persistence*, preprint, version 1.0
> (30 July 2026).

It contains a Lean 4 proof that, for every parameter dimension `n ≥ 3` and
integer `m ≥ 1`, there is a finite graph `Sₘ` with two monotone
filtrations that differ only in the grade of one edge and satisfy

```text
‖fₘ - gₘ‖₁ = 1
‖μ_H₀(fₘ) - μ_H₀(gₘ)‖_{KR,1} = 2m.
```

These identities disprove the proposed constant-`n` bound and every finite
replacement depending only on dimension, for each fixed `n ≥ 3`.  The first
explicit violation is the four-vertex diamond at `n = 3`, `m = 2`, where
`4 > 3`.  The [LaTeX source](paper/main.tex) and
[compiled paper](paper/one-edge-unbounded-instability.pdf) are included.

## Verify the Lean proof

From the repository root:

```bash
lake exe cache get
lake env lean OneEdgeInstability/P1.lean
lake env lean OneEdgeInstability/P3.lean
lake build
lake env leanchecker OneEdgeInstability
rg -n '\b(sorry|admit|axiom|unsafe)\b' --glob '*.lean'
git diff --check
```

The first command downloads the pinned Mathlib build cache.  The repository
pins Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.  Verification does not require `lake update`.

If `lake` is not found, install Lean's official `elan` toolchain manager:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

Then rerun the commands above. See the
[official Lean installation guide](https://lean-lang.org/install/manual/) for
other platforms.

For a live demonstration, open the repository in VS Code with the official
**Lean 4** extension, then open `OneEdgeInstability/P1.lean` and jump to one
of the public theorems below.  The Infoview shows the checked statement and
reports an error if a change breaks the proof.  **Terminal → Run Build
Task** runs the project build configured in `.vscode/tasks.json`.

## Main checked declarations

Names in the table are relative to the root namespace
`OneEdgeInstability`; for example, the first fully qualified name is
`OneEdgeInstability.P1.theorem1_H0_counterexample_family`.

| Mathematical statement | Lean declaration |
| --- | --- |
| Complete `H₀` family | `P1.theorem1_H0_counterexample_family` |
| Proposed constant-`n` P1 inequality is false | `P1.proposed_constant_n_P1_inequality_false` |
| No finite dimension-only P2 constant | `P1.no_finite_dimension_only_P2_constant` |
| Explicit diamond counterexample `4 > 3` | `P1.n3_m2_explicit_counterexample` |
| Unit-cube rescaling | `P1.unit_cube_H0_counterexample_family` |
| Arbitrarily small inputs with fixed output | `P1.arbitrarily_close_unit_cube_counterexamples` |
| Same-family `H₁` and Euler cancellation | `P1.same_family_H1_and_Euler_cancellation` |
| Presentation-distance P3 family | `P3.p3_H0_presentation_counterexample_family` |
| No finite dimension-only P3 constant | `P3.no_finite_dimension_only_P3_constant` |

`OneEdgeInstability/P1.lean` imports only `Mathlib`.  It defines the graph,
filtrations, sublevel connected components, and ordinary cellular homology.
It also constructs finite atomic signed measures, realizes them as Mathlib
signed measures with their Jordan parts, and defines `KR₁` as an infimum
over Mathlib product measures with prescribed measurable-set marginals and
`lintegral` cost.  Python output is not used in the proof.

`OneEdgeInstability/P3.lean` separately defines finite labeled
presentations and the finite-path presentation metric. It proves
`d_I¹(Mₘ,Nₘ) ≤ 1` from the common incidence matrix and the one moved column;
this proof is separate from P1.

## Repository map

- `paper/`: preprint source, compiled PDF, and paper license.
- `OneEdgeInstability/P1.lean`: complete P1/P2 family and the rescaling and
  `H₁`/Euler extensions.
- `OneEdgeInstability/P3.lean`: presentation-distance P3 bridge.
- `scripts/verify_h0_scipy.py`: independent finite `H₀` computation for
  `m = 1, …, 15`; secondary evidence only.

Run the independent `H₀` computation with:

```bash
uv sync
uv run python scripts/verify_h0_scipy.py
```

## Licensing and citation

Lean and Python source code are licensed under Apache-2.0; see
[LICENSE](LICENSE). The paper is licensed under CC BY 4.0; see
[paper/LICENSE.md](paper/LICENSE.md). Machine-readable citation metadata is
in [CITATION.cff](CITATION.cff). The release repository is
[`ZeterMordio/one-edge-instability`](https://github.com/ZeterMordio/one-edge-instability).
The version 1.0 preprint is archived at
[doi:10.5281/zenodo.21764586](https://doi.org/10.5281/zenodo.21764586).
The corresponding `v1.0.0` software release is archived at
[doi:10.5281/zenodo.21764641](https://doi.org/10.5281/zenodo.21764641)
and records Git commit `9cf9f40bf975a2ba637e24715c2a3f99082df5ce`.
