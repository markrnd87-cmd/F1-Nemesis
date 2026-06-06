import Lake
open Lake DSL

/-!
The 𝔽₁ Square with an Intersection Theory — a research program toward
`Spec ℤ ×_{𝔽₁} Spec ℤ` and the Hodge-index positivity that is the Riemann Hypothesis.

This package extends the UOR-Foundation Lean library (the `uor` package). It is pinned to a
concrete release tag (v0.5.2 — the latest UOR-Framework release that ships the `lean4/` library)
for reproducibility; the exact resolved revision is frozen in `lake-manifest.json`.
-/

package f1square where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require uor from git
  "https://github.com/UOR-Foundation/UOR-Framework" @ "v0.5.2"

@[default_target]
lean_lib F1Square where
  -- Root module: `F1Square.lean` at the repository root (default srcDir ".").
  -- Keeps the seed's `UOR.Bridge.F1Square` namespace, extending the `UOR` library.
