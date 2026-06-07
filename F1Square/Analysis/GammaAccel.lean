/-
F1 square — the **Euler–Mascheroni constant γ via the convergence-accelerated harmonic route**, whose
approximants have small denominators so that `Pos λ₁` is kernel-certifiable.

Standard definition, realized in *telescoped* form (so no log-additivity lemma is needed):

  γ = Σ_{i≥1} cᵢ,   cᵢ = 1/i − log((i+1)/i) = 1/i − 2·artanh(1/(2i+1)),   0 ≤ cᵢ ≤ 1/(i(i+1)).

Each consecutive-ratio log has a *small* artanh argument `1/(2i+1)` (fast geometric convergence),
unlike `log(n+1)` directly (argument `→ 1`). The series is built as a single rational diagonal (à la
`Rpi`, `gammaSeq`), reusing the artanh partial sum `artSum` (Log.lean); its termwise bracket
`0 ≤ cᵢ ≤ 1/(i(i+1))` rests on the two analytic facts `t ≤ artanh t ≤ t/(1−t²)`, mechanized here as
rational bounds on `artSum`.

This file builds the analytic foundation (the `artSum` bounds). The diagonal, its regularity, the
γ-lower bracket, and `Pos λ₁` follow. Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Log
import F1Square.Analysis.Euler

namespace UOR.Bridge.F1Square.Analysis

/-! ### Rational lower bound: `artSum t N ≥ t` (the first series term, for `t ≥ 0`) -/

/-- Each artanh term is non-negative for a non-negative base. -/
theorem artTerm_num_nonneg {t : Q} (ht0 : 0 ≤ t.num) (n : Nat) : 0 ≤ (artTerm t n).num := by
  show 0 ≤ (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩).num
  simp only [mul]
  have := qpow_nonneg ht0 (2 * n + 1)
  omega

/-- The artanh partial sums are monotone (one step), for a non-negative base. -/
theorem artSum_step {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (artSum t N) (artSum t (N + 1)) := by
  show Qle (artSum t N) (add (artSum t N) (artTerm t (N + 1)))
  exact Qle_self_add (artTerm_num_nonneg ht0 (N + 1))

/-- The artanh partial sums are monotone, for a non-negative base. -/
theorem artSum_mono {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) {a b : Nat} (hab : a ≤ b) :
    Qle (artSum t a) (artSum t b) := by
  induction hab with
  | refl => exact Qle_refl _
  | step _ ih => exact Qle_trans (artSum_den_pos htd _) ih (artSum_step ht0 htd _)

/-- The first partial sum is the base: `artSum t 0 ≈ t`. -/
theorem artSum_zero_eq (t : Q) : Qeq (artSum t 0) t := by
  show Qeq (mul (qpow t (2 * 0 + 1)) ⟨1, 2 * 0 + 1⟩) t
  have hq : qpow t 1 = mul t (qpow t 0) := qpow_succ t 0
  show Qeq (mul (qpow t 1) ⟨1, 1⟩) t
  rw [hq]
  simp only [Qeq, mul, qpow]; push_cast; ring_uor

/-- **`artSum t N ≥ t`** for a non-negative base — the artanh lower bound at the rational level. -/
theorem artSum_ge_arg {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle t (artSum t N) :=
  Qle_trans (artSum_den_pos htd 0) (Qeq_le (Qeq_symm (artSum_zero_eq t)))
    (artSum_mono ht0 htd (Nat.zero_le N))

/-! ### Rational geometric upper bound: `artSum t N · (1−t²) ≤ t` -/

/-- Each artanh term is `≤` the geometric term (since `1/(2n+1) ≤ 1`). -/
theorem artTerm_le_geoTerm {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (n : Nat) :
    Qle (artTerm t n) (geoTerm t n) := by
  show Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (qpow t (2 * n + 1))
  have h1 : Qle (⟨1, 2 * n + 1⟩ : Q) ⟨1, 1⟩ := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((2 * n + 1 : Nat) : Int); push_cast; omega
  have h2 : Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) :=
    Qmul_le_mul_left (qpow_nonneg ht0 _) h1
  have h3 : Qeq (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) (qpow t (2 * n + 1)) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  exact Qle_trans (Qmul_den_pos (qpow_den_pos htd _) Nat.one_pos) h2 (Qeq_le h3)

/-- The artanh partial sum is `≤` the geometric partial sum. -/
theorem artSum_le_geoSum {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) :
    ∀ N, Qle (artSum t N) (geoSum t N)
  | 0 => artTerm_le_geoTerm ht0 htd 0
  | (N + 1) => by
      show Qle (add (artSum t N) (artTerm t (N + 1))) (add (geoSum t N) (geoTerm t (N + 1)))
      exact Qadd_le_add (artSum_le_geoSum ht0 htd N) (artTerm_le_geoTerm ht0 htd (N + 1))

/-- Cleared geometric closed bound: `geoSum t N · (1−t²) ≤ t` (drop the non-negative `t^{2N+3}`). -/
theorem geoSum_cleared_le {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have hU := geoU_eq htd N
  exact Qle_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos htd N)
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) (qpow_den_pos htd _))
    (Qle_self_add (qpow_nonneg ht0 _)) (Qeq_le hU)

/-- **The cleared artanh geometric upper bound**: `artSum t N · (1−t²) ≤ t`. -/
theorem artSum_le_geo {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den)
    (hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul t t)).num) (N : Nat) :
    Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have h1 : Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t)))
      (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) :=
    Qmul_le_mul_right hWnn (artSum_le_geoSum ht0 htd N)
  exact Qle_trans (Qmul_den_pos (geoSum_den_pos htd N)
    (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) h1 (geoSum_cleared_le ht0 htd N)

end UOR.Bridge.F1Square.Analysis
