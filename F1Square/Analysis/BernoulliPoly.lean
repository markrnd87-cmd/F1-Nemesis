/-
F1 square — the **Bernoulli polynomials** `Bₙ(x) = Σ_{k=0}^{n} C(n,k)·B_k·x^{n−k}` as exact rationals
(the v0.16.0 prerequisite for the *periodic* Bernoulli functions `P_{2K}({x})` that carry the
Euler–Maclaurin remainder `R_K(s,N)`). Built on the Bernoulli numbers `bernoulli` and `Binomial.choose`.

`Bₙ(0) = Bₙ` (only the `k = n` term survives, `x⁰ = 1`), and `B₁(x) = x − ½`, `B₂(x) = x² − x + 1/6`,
… — all exact, by reduction.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Bernoulli
import F1Square.Analysis.ExpGen

namespace UOR.Bridge.F1Square.Analysis

/-- **The `n`-th Bernoulli polynomial** `Bₙ(x) = Σ_{k=0}^{n} C(n,k)·B_k·x^{n−k}` (exact rational eval). -/
def bernPoly (n : Nat) (x : Q) : Q :=
  Fsum (fun k => mul (mul (⟨(choose n k : Int), 1⟩ : Q) (bernoulli k)) (qpow x (n - k))) n

/-- `Bₙ(x)` has positive denominator (for `x.den > 0`), so it is a genuine rational. -/
theorem bernPoly_den_pos (n : Nat) {x : Q} (hx : 0 < x.den) : 0 < (bernPoly n x).den :=
  Fsum_den_pos (fun k => Qmul_den_pos (Qmul_den_pos Nat.one_pos (bernoulli_den_pos k))
    (qpow_den_pos hx _)) n

-- The defining values (exact, by reduction).

/-- `B₀(x) = 1`. -/
theorem bernPoly_zero (x : Q) : Qeq (bernPoly 0 x) ⟨1, 1⟩ := by
  show Qeq (mul (mul (⟨1, 1⟩ : Q) (bernoulli 0)) (qpow x 0)) ⟨1, 1⟩
  simp only [bernoulli, bernTable, qpow, Qeq, mul]; decide

/-- `B₁(0) = B₁ = −1/2`. -/
theorem bernPoly_one_at_zero : Qeq (bernPoly 1 ⟨0, 1⟩) ⟨-1, 2⟩ := by decide

/-- `B₂(0) = B₂ = 1/6`. -/
theorem bernPoly_two_at_zero : Qeq (bernPoly 2 ⟨0, 1⟩) ⟨1, 6⟩ := by decide

/-- `B₁(1) = 1/2` (`= x − ½` at `x = 1`). -/
theorem bernPoly_one_at_one : Qeq (bernPoly 1 ⟨1, 1⟩) ⟨1, 2⟩ := by decide

/-- `B₂(1) = 1/6 = B₂` (the `Bₙ(1) = Bₙ` symmetry for `n ≠ 1`). -/
theorem bernPoly_two_at_one : Qeq (bernPoly 2 ⟨1, 1⟩) ⟨1, 6⟩ := by decide

end UOR.Bridge.F1Square.Analysis
