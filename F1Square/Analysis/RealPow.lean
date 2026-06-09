/-
F1 square — **real powers** `nᶜ = exp(c·log n)` (the v0.15.2 commit 1: the natural-exponent core).

The v0.15.1 ζ-convergence gate `exp(log n) = n` (`Rexp_log_nat_Rlog`) makes `log n` a genuine
constructive real with `exp(log n) ≈ n`. This file lifts that to **powers**: for a natural exponent
`k`, `exp(k·log n) ≈ nᵏ`. The mechanism is the exponential homomorphism `RexpReal_add`
(`exp(x+y) ≈ exp x · exp y`) iterated `k` times — i.e. `exp(k·x) ≈ (exp x)ᵏ` — composed with the gate.

`k·x` is the iterated real sum `Rnsmul k x = x + x + ⋯ + x` (`k` copies), so the homomorphism is a
clean induction: `exp((k+1)·x) = exp(x + k·x) ≈ exp x · exp(k·x) ≈ exp x · (exp x)ᵏ = (exp x)^{k+1}`.

This is the analytic content behind the `ζ` tail bound `|n^{-s}| = n^{-Re s}` for `Re s > 1`: the
real exponent of `n` is `exp(Re s · log n)`, and grounding it against the integer powers `nᵏ` (here)
and the exp monotonicity (next commit) is what makes `Σ n^{-s}` summable.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.ExpLog
import F1Square.Analysis.Pow

namespace UOR.Bridge.F1Square.Analysis

/-- **The natural scalar multiple** `k·x` of a real, as the iterated sum `x + x + ⋯ + x` (`k` copies).
    `0·x = 0` and `(k+1)·x = x + k·x`. This is the additive analogue of `Rpow` (iterated `Rmul`); it
    is what feeds the exponential homomorphism to produce `exp(k·x) = (exp x)ᵏ`. -/
def Rnsmul : Nat → Real → Real
  | 0, _ => zero
  | (k + 1), x => Radd x (Rnsmul k x)

theorem Rnsmul_zero (x : Real) : Rnsmul 0 x = zero := rfl

theorem Rnsmul_succ (k : Nat) (x : Real) : Rnsmul (k + 1) x = Radd x (Rnsmul k x) := rfl

/-- **The natural-power exponential homomorphism**: `exp(k·x) ≈ (exp x)ᵏ`. The diagonal lift of
    `exp((k+1)·x) = exp(x + k·x) ≈ exp x · exp(k·x)` (`RexpReal_add`), folded `k` times against
    `Rpow` (`(exp x)^{k+1} = exp x · (exp x)ᵏ`). The base `k = 0` is `exp 0 ≈ 1` (`RexpReal_zero`). -/
theorem RexpReal_nsmul (x : Real) : ∀ k, Req (RexpReal (Rnsmul k x)) (Rpow (RexpReal x) k)
  | 0 => RexpReal_zero
  | (k + 1) =>
      Req_trans (RexpReal_add x (Rnsmul k x))
        (Rmul_congr (Req_refl (RexpReal x)) (RexpReal_nsmul x k))

/-- **Real powers, abstract form**: if `exp L ≈ N` then `exp(k·L) ≈ Nᵏ`. With `L = log n` and
    `N = n` (the v0.15.1 gate `Rexp_log_nat_Rlog`), this is `exp(k·log n) ≈ nᵏ`. Decoupled from the
    `Rlog` plumbing so that any logarithm witness `exp L ≈ N` produces its powers — the established
    abstract-reconciliation pattern (cf. `Rexp_two_artanh_via`). -/
theorem RexpReal_nsmul_eq {L N : Real} (h : Req (RexpReal L) N) (k : Nat) :
    Req (RexpReal (Rnsmul k L)) (Rpow N k) :=
  Req_trans (RexpReal_nsmul L k) (Rpow_congr h k)

end UOR.Bridge.F1Square.Analysis
