/-
F1 square — v0.21.0 stage G, bricks **G2b.0 / G2b.1 (the tower carries a form; infinite
definiteness — the make-or-break)**: the gauge tower with a compatible inner product, and the
recorded obstruction when the direct limit's signature has a negative entry.

ROADMAP §8 (Stages 2b.0 / 2b.1) and §9/§10. Gate B needs an INFINITE positive-definite limit: the
atlas base is finite rank (E₈, brick G2a), the primitive span is infinite. This brick:

- **G2b.0 — the tower carries a metric** (falsifier: "the tower is only an addressing/modulus
  structure with no metric"). A `GaugeTower` is a family of Gram kernels, each a genuine `WeilPSD`
  inner product (not merely a modulus), with the E₈ seed at the base. `e8Tower` inhabits it —
  every level the E₈ `WeilPSD` metric — so the tower DOES carry a form to take the limit of.

- **G2b.1 — infinite definiteness, the make-or-break** (falsifier: "the limit form is indefinite —
  a negative entry in the metric"). The direct limit closes Gate B iff its single kernel is
  `WeilPSD`. The OBSTRUCTION is recorded as a theorem (`limit_indefinite_of_neg_signature`): any
  strictly negative diagonal entry of the limit metric — a negative SIGNATURE entry — makes it not
  `WeilPSD`, so Gate B FAILS. The hypothesized atlas signature `Σ = {10,2,7,−1}` is exhibited as a
  diagonal metric (`sigmaMetric`) and proven indefinite (`sigmaMetric_not_psd`): its `−1` entry
  kills definiteness.

HONEST SCOPE (§10). Whether the GENUINE atlas direct limit realizes `Σ = {10,2,7,−1}` (or any
negative-entry signature) is UNSOURCED in F1 — the atlas signature is not in this repository. So
this brick does NOT decide Gate B: it builds the tower-with-metric and records, as a theorem, the
exact obstruction that a negative signature entry would be (the §9 "Localized" terminal mode for the
make-or-break). It asserts neither that the limit is definite (which would close the crux) nor that
it is indefinite. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.E8Seed

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

-- ===========================================================================
-- The indefiniteness obstruction: a negative diagonal entry kills PSD.
-- ===========================================================================

/-- **A strictly negative diagonal entry kills positive-semidefiniteness.** Contrapositive of
    `WeilPSD_diag` (PSD ⟹ nonnegative diagonal): if `−B(n,n) > 0`, then `B` is not `WeilPSD`. -/
theorem not_WeilPSD_of_neg_diag {B : Nat → Nat → Real} (n : Nat) (h : Pos (Rneg (B n n))) :
    ¬ WeilPSD B := by
  intro hpsd
  have hd : Rnonneg (B n n) := WeilPSD_diag hpsd n
  have hnn : Rnonneg (Rneg (Rneg (B n n))) := Rnonneg_congr (Req_symm (Rneg_neg (B n n))) hd
  exact not_Pos_of_Rnonneg_neg hnn h

-- ===========================================================================
-- G2b.0 — the gauge tower carries a compatible inner product.
-- ===========================================================================

/-- **A GAUGE TOWER carrying a compatible inner product**: a family of Gram kernels, each a genuine
    `WeilPSD` metric (not just a modulus / addressing structure), with the E₈ seed at the base. -/
structure GaugeTower where
  /-- the Gram metric at each tower level -/
  level : Nat → (Nat → Nat → Real)
  /-- every level is a genuine positive-semidefinite inner product -/
  psd : ∀ k, WeilPSD (level k)
  /-- the base level is the E₈ seed -/
  base : ∀ i j, Req (level 0 i j) (e8Gram i j)

/-- **The tower carries a form** (G2b.0, falsifier refuted): the constant E₈ tower is a gauge
    tower — every level is the E₈ `WeilPSD` metric — so the tower is a metric structure to take the
    limit of, not merely an addressing/modulus one. -/
def e8Tower : GaugeTower where
  level := fun _ => e8Gram
  psd := fun _ => e8_weilPSD
  base := fun _ _ => Req_refl _

-- ===========================================================================
-- G2b.1 — infinite definiteness (the make-or-break) and its obstruction.
-- ===========================================================================

/-- **THE LIMIT-DEFINITENESS QUESTION** (G2b.1, make-or-break): the direct limit of the tower is a
    single kernel `B` that the levels approach; Gate B closes iff `WeilPSD B`. -/
def LimitPSD (B : Nat → Nat → Real) : Prop := WeilPSD B

/-- **THE MAKE-OR-BREAK OBSTRUCTION, recorded as a theorem** (§9 Localized, §10): if the direct
    limit metric has ANY strictly negative diagonal entry — a negative SIGNATURE entry — then the
    limit form is indefinite (not `WeilPSD`), so Gate B FAILS. Positive-definiteness cannot survive
    a negative entry in the signature. -/
theorem limit_indefinite_of_neg_signature (B : Nat → Nat → Real) (n : Nat)
    (h : Pos (Rneg (B n n))) : ¬ LimitPSD B :=
  not_WeilPSD_of_neg_diag n h

/-- The hypothesized atlas signature `Σ = {10, 2, 7, −1}` (the §10 risk) as a diagonal metric. -/
def sigmaDiag : Nat → Real
  | 0 => ofQ ⟨10, 1⟩ (by decide)
  | 1 => ofQ ⟨2, 1⟩ (by decide)
  | 2 => ofQ ⟨7, 1⟩ (by decide)
  | 3 => Rneg one
  | _ => zero

/-- The hypothesized signature as a diagonal kernel. -/
def sigmaMetric (i j : Nat) : Real := if i = j then sigmaDiag i else zero

/-- **The hypothesized signature `Σ = {10,2,7,−1}` is INDEFINITE**: its `−1` entry makes the
    diagonal metric not `WeilPSD`. So IF the atlas direct limit realizes this `Σ`, Gate B fails —
    the make-or-break localizes. (Whether the genuine atlas limit has this signature is UNSOURCED
    in F1; this records the obstruction, not a verdict on RH.) -/
theorem sigmaMetric_not_psd : ¬ WeilPSD sigmaMetric :=
  not_WeilPSD_of_neg_diag 3 (Pos_congr (Req_symm (Rneg_neg one)) Pos_one)

end UOR.Bridge.F1Square.Square
