/-
F1 square — **binomial coefficients and the factorial identity from scratch** (Lean core here has no
`Nat.choose` / `Nat.factorial` / `Nat.add_pow`). This is the foundational first piece of the v0.15.0
keystone: the exponential/trigonometric functional equation via the Cauchy product needs the binomial
identity `Σ_{i+j=k} (xⁱ/i!)(yʲ/j!) = (x+y)ᵏ/k!`, whose heart is `C(k,i)·i!·(k−i)! = k!`.

This module builds `choose` (Pascal's recurrence) and that factorial identity (the ℤ ring algebra is
discharged by `ring_uor`, the project's from-scratch `ring`). Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Exp

namespace UOR.Bridge.F1Square.Analysis

/-- Binomial coefficients via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

/-- `C(n,k) = 0` when `k > n`. -/
theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (_ + 1), 0, h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rw [choose_succ_succ, choose_eq_zero_of_lt (by omega : n < k),
        choose_eq_zero_of_lt (by omega : n < k + 1)]

/-- `C(n,n) = 1`. -/
theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | (n + 1) => by
      rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

-- ===========================================================================
-- A finite inclusive sum `Σ_{i=0}^{k} f i` over ℚ, with the algebra lemmas the binomial
-- theorem's Pascal step needs (distribution, additivity, index shift).
-- ===========================================================================

/-- Finite inclusive sum `Σ_{i=0}^{k} f i`. -/
def Fsum (f : Nat → Q) : Nat → Q
  | 0 => f 0
  | (k + 1) => add (Fsum f k) (f (k + 1))

theorem Fsum_den_pos {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) : ∀ k, 0 < (Fsum f k).den
  | 0 => hf 0
  | (k + 1) => add_den_pos (Fsum_den_pos hf k) (hf (k + 1))

/-- Pointwise-equal summands give equal sums. -/
theorem Fsum_congr {f g : Nat → Q} (h : ∀ i, Qeq (f i) (g i)) : ∀ k, Qeq (Fsum f k) (Fsum g k)
  | 0 => h 0
  | (k + 1) => Qadd_congr (Fsum_congr h k) (h (k + 1))

/-- Reassociation `(a+b)+(c+d) ≈ (a+c)+(b+d)`. -/
theorem Qadd_rearrange (a b c d : Q) : Qeq (add (add a b) (add c d)) (add (add a c) (add b d)) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- Distribution `c·(a+b) ≈ c·a + c·b`. -/
theorem Qmul_add_left (c a b : Q) : Qeq (mul c (add a b)) (add (mul c a) (mul c b)) := by
  simp only [Qeq, mul, add]; push_cast; ring_uor

/-- Sums add termwise. -/
theorem Fsum_add {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ i, 0 < (g i).den) :
    ∀ k, Qeq (Fsum (fun i => add (f i) (g i)) k) (add (Fsum f k) (Fsum g k))
  | 0 => Qeq_refl _
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (add_den_pos (Fsum_den_pos hf k) (Fsum_den_pos hg k))
          (add_den_pos (hf (k + 1)) (hg (k + 1))))
        (Qadd_congr (Fsum_add hf hg k) (Qeq_refl (add (f (k + 1)) (g (k + 1)))))
        (Qadd_rearrange (Fsum f k) (Fsum g k) (f (k + 1)) (g (k + 1)))

/-- A constant factor pulls out of a sum. -/
theorem Fsum_mul_left {c : Q} {f : Nat → Q} (hcd : 0 < c.den) (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum (fun i => mul c (f i)) k) (mul c (Fsum f k))
  | 0 => Qeq_refl _
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (Qmul_den_pos hcd (Fsum_den_pos hf k)) (Qmul_den_pos hcd (hf (k + 1))))
        (Qadd_congr (Fsum_mul_left hcd hf k) (Qeq_refl (mul c (f (k + 1)))))
        (Qeq_symm (Qmul_add_left c (Fsum f k) (f (k + 1))))

/-- Index shift: `Σ_{i=0}^{k} f(i+1) ≈ (Σ_{i=0}^{k+1} f i) − f 0`. -/
theorem Fsum_shift {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum (fun i => f (i + 1)) k) (Qsub (Fsum f (k + 1)) (f 0))
  | 0 => by
      show Qeq (f 1) (Qsub (add (f 0) (f 1)) (f 0))
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (Qsub_den_pos (Fsum_den_pos hf (k + 1)) (hf 0)) (hf (k + 1 + 1)))
        (Qadd_congr (Fsum_shift hf k) (Qeq_refl (f (k + 1 + 1))))
        (by
          show Qeq (add (Qsub (Fsum f (k + 1)) (f 0)) (f (k + 1 + 1)))
            (Qsub (add (Fsum f (k + 1)) (f (k + 1 + 1))) (f 0))
          simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor)

/-- **The factorial identity** `C(n,k)·k!·(n−k)! = n!` for `k ≤ n` — the divisibility heart of the
    binomial theorem. -/
theorem choose_mul_fct_mul_fct : ∀ {n k : Nat}, k ≤ n →
    choose n k * fct k * fct (n - k) = fct n
  | _, 0, _ => by simp [fct]
  | 0, (_ + 1), h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with hkn | hkn
      · -- k = n : the corner term
        subst hkn
        rw [Nat.sub_self, choose_self]; simp [fct]
      · -- k < n : Pascal step (ℤ ring algebra via ring_uor)
        have ih1 := choose_mul_fct_mul_fct (Nat.le_of_lt hkn)
        have ih2 := choose_mul_fct_mul_fct hkn
        have hsub : n + 1 - (k + 1) = n - k := by omega
        -- cast the facts to ℤ, keeping each Nat subterm as an opaque atom
        have ih1Z : (↑(choose n k) : Int) * ↑(fct k) * ↑(fct (n - k)) = ↑(fct n) := by
          exact_mod_cast ih1
        have ih2Z : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - (k + 1))) = ↑(fct n) := by
          exact_mod_cast ih2
        have hFk1 : (↑(fct (k + 1)) : Int) = ↑(k + 1) * ↑(fct k) := by exact_mod_cast fct_succ k
        have hFnk_nat : fct (n - k) = (n - k) * fct (n - (k + 1)) := by
          rw [show n - k = (n - (k + 1)) + 1 from by omega, fct_succ]
        have hFnk : (↑(fct (n - k)) : Int) = ↑(n - k) * ↑(fct (n - (k + 1))) := by
          exact_mod_cast hFnk_nat
        have hFn1 : (↑(fct (n + 1)) : Int) = ↑(n + 1) * ↑(fct n) := by exact_mod_cast fct_succ n
        have hk1 : (↑(k + 1) : Int) + ↑(n - k) = ↑(n + 1) := by
          exact_mod_cast (show (k + 1) + (n - k) = n + 1 from by omega)
        have hterm1 : (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k)) = ↑(k + 1) * ↑(fct n) := by
          rw [hFk1, ← ih1Z]; ring_uor
        have hterm2 : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(n - k) * ↑(fct n) := by
          rw [hFnk, ← ih2Z]; ring_uor
        have keyZ : ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(fct (n + 1)) :=
          calc ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
              = (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
                + ↑(choose n (k + 1)) * ↑(fct (k + 1)) * ↑(fct (n - k)) := by ring_uor
            _ = ↑(k + 1) * ↑(fct n) + ↑(n - k) * ↑(fct n) := by rw [hterm1, hterm2]
            _ = (↑(k + 1) + ↑(n - k)) * ↑(fct n) := by ring_uor
            _ = ↑(n + 1) * ↑(fct n) := by rw [hk1]
            _ = ↑(fct (n + 1)) := by rw [← hFn1]
        rw [hsub, choose_succ_succ]
        exact_mod_cast keyZ

end UOR.Bridge.F1Square.Analysis
