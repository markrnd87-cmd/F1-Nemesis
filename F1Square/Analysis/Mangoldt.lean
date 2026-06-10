/-
F1 square — the **von Mangoldt function** `Λ` and the **prime side** of the Weil explicit formula,
as genuine constructive reals (the v0.15.3 arithmetic ingredient).

The explicit formula pairs the zeros of `ζ` against the primes through the **prime side**

    Σ_p Σ_{k≥1} log p · h(k·log p)  =  Σ_{n≥2} Λ(n) · h(log n),

where `Λ` is the **von Mangoldt function** `Λ(n) = log p` if `n = pᵏ` is a prime power (`p` prime,
`k ≥ 1`), and `Λ(n) = 0` otherwise. The right-hand reindex uses `k·log p = log(pᵏ) = log n` for
`n = pᵏ` — so the prime side is exactly the `Λ`-weighted sum of `h(log n)`. For a **compactly
supported** test function `h` the sum is **finite** (only finitely many `n` carry support), hence a
genuine constructive real with no convergence hypothesis.

`Λ` is built with no primality predicate beyond the **smallest factor** `spf n` (least `d ≥ 2`
dividing `n`): `n` is a prime power iff stripping the factor `spf n` reaches `1`, and then
`Λ(n) = log (spf n)`. Everything is computable, so the defining values (`Λ(1) = 0`, `Λ(2) = log 2`,
`Λ(4) = log 2`, `Λ(6) = 0`, …) hold by reduction.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Smallest factor and the prime-power test (pure `Nat`, computable, choice-free).
-- ===========================================================================

/-- `spfFrom n d fuel` — the least `d' ≥ d` dividing `n`, searched with `fuel` steps; on exhaustion
    it returns `n`. -/
def spfFrom (n d fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else spfFrom n (d + 1) fuel

/-- The **smallest factor** of `n` (least divisor `≥ 2`; `spf n = n` for `n` prime, and the search is
    given `n` units of fuel, enough to reach `d = n` since `n ∣ n`). -/
def spf (n : Nat) : Nat := spfFrom n 2 n

/-- The search never returns below `1` (it returns either a divisor `≥ d` or `n`). -/
theorem spfFrom_ge_one (n : Nat) (hn : 1 ≤ n) : ∀ (fuel d : Nat), 1 ≤ d → 1 ≤ spfFrom n d fuel := by
  intro fuel
  induction fuel with
  | zero => intro d _; exact hn
  | succ f ih =>
    intro d hd
    simp only [spfFrom]
    split
    · exact hd
    · exact ih (d + 1) (by omega)

/-- `1 ≤ spf n` for `n ≥ 1` — so `log (spf n)` is well-formed. -/
theorem one_le_spf (n : Nat) (hn : 1 ≤ n) : 1 ≤ spf n :=
  spfFrom_ge_one n hn n 2 (by omega)

/-- `isPow n p fuel` — is `n` a power `pᵏ` (`k ≥ 0`, so `n = 1` counts)? Strips factors of `p`. -/
def isPow (n p fuel : Nat) : Bool :=
  match fuel with
  | 0 => decide (n = 1)
  | fuel + 1 =>
    if n = 1 then true
    else if n % p = 0 then isPow (n / p) p fuel else false

/-- The **prime-power test**: `n ≥ 2` and `n` is a pure power of its smallest factor. -/
def isPrimePow (n : Nat) : Bool := decide (2 ≤ n) && isPow n (spf n) n

/-- `isPrimePow n = true` forces `2 ≤ n` (the first conjunct). -/
theorem two_le_of_isPrimePow {n : Nat} (h : isPrimePow n = true) : 2 ≤ n := by
  unfold isPrimePow at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

-- ===========================================================================
-- The von Mangoldt function as a constructive real.
-- ===========================================================================

/-- The **von Mangoldt function** `Λ(n)`: `log (spf n)` when `n` is a prime power, else `0`.
    For `n = pᵏ` (`p` prime, `k ≥ 1`) this is `log p`; for `n ∈ {0, 1}` and composite `n` it is `0`. -/
def vonMangoldt (n : Nat) : Real :=
  if h : isPrimePow n = true then
    logN (spf n) (one_le_spf n (by have := two_le_of_isPrimePow h; omega))
  else zero

/-- `Λ(1) = 0` (`1` is not a prime power). -/
theorem vonMangoldt_one : Req (vonMangoldt 1) zero := Req_refl _

/-- `Λ(2) = log 2`. -/
theorem vonMangoldt_two : Req (vonMangoldt 2) (logN 2 (by omega)) := Req_refl _

/-- `Λ(3) = log 3`. -/
theorem vonMangoldt_three : Req (vonMangoldt 3) (logN 3 (by omega)) := Req_refl _

/-- `Λ(4) = log 2` (`4 = 2²`, a prime power; its value is `log 2`, not `log 4`). -/
theorem vonMangoldt_four : Req (vonMangoldt 4) (logN 2 (by omega)) := Req_refl _

/-- `Λ(6) = 0` (`6 = 2·3` is not a prime power). -/
theorem vonMangoldt_six : Req (vonMangoldt 6) zero := Req_refl _

/-- `Λ(8) = log 2` (`8 = 2³`). -/
theorem vonMangoldt_eight : Req (vonMangoldt 8) (logN 2 (by omega)) := Req_refl _

/-- `Λ(9) = log 3` (`9 = 3²`). -/
theorem vonMangoldt_nine : Req (vonMangoldt 9) (logN 3 (by omega)) := Req_refl _

/-- `Λ(n) ≥ 0` everywhere: it is either `0` or `log (spf n)` with `spf n ≥ 1`. -/
theorem vonMangoldt_nonneg (n : Nat) : Rnonneg (vonMangoldt n) := by
  unfold vonMangoldt
  split
  · exact Rnonneg_logN _ _
  · exact Rnonneg_zero

-- ===========================================================================
-- The prime side of the explicit formula: Σ_{n≥2} Λ(n) · h(log n), a finite sum.
-- ===========================================================================

/-- The `n`-th prime-side term `Λ(n) · h(log n)` (zero for `n < 2`, where `Λ` vanishes and `log n` is
    not formed). -/
def primeTerm (h : Real → Real) (n : Nat) : Real :=
  if hn : 2 ≤ n then Rmul (vonMangoldt n) (h (logN n (by omega))) else zero

/-- The **prime side** up to `N`: `Σ_{n=1}^N Λ(n) · h(log n) = Σ_{n=2}^N Λ(n) · h(log n)`. A genuine
    constructive real (a finite sum); for compactly supported `h` it is the full prime side. -/
def primeSide (h : Real → Real) : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (primeSide h n) (primeTerm h (n + 1))

/-- **Finiteness for compact support.** If every term beyond `N₀` vanishes, the prime side is
    constant past `N₀` — so a compactly supported `h` gives a single genuine real, independent of the
    cutoff. (Stated on the terms; `primeTerm_zero_of_h` derives it from `h` vanishing.) -/
theorem primeSide_stable (h : Real → Real) (N₀ : Nat)
    (hsupp : ∀ n, N₀ < n → Req (primeTerm h n) zero) :
    ∀ d, Req (primeSide h (N₀ + d)) (primeSide h N₀) := by
  intro d
  induction d with
  | zero => exact Req_refl _
  | succ k ih =>
    show Req (Radd (primeSide h (N₀ + k)) (primeTerm h (N₀ + k + 1))) (primeSide h N₀)
    refine Req_trans (Radd_congr ih (hsupp (N₀ + k + 1) (by omega))) ?_
    exact Radd_zero _

/-- If `h(log n) ≈ 0` then the `n`-th prime-side term vanishes (so `h`-support ⇒ term-support). -/
theorem primeTerm_zero_of_h (h : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hh : Req (h (logN n (by omega))) zero) : Req (primeTerm h n) zero := by
  unfold primeTerm
  rw [dif_pos hn]
  exact Req_trans (Rmul_congr (Req_refl _) hh) (Rmul_zero _)

end UOR.Bridge.F1Square.Analysis
