/-
F1 square — the **first Li/Keiper coefficient** `λ₁` as a constructive real value.

By the Bombieri–Lagarias formula, the first Li coefficient is the *closed-form constant*

  λ₁ = 1 + γ/2 − ½·log(4π)

(no zeros, no higher Stieltjes constants enter). With `Rgamma0` (Euler.lean) and `Rlog4pi` (Pi.lean)
both genuine constructive reals, `λ₁` is therefore a **genuine constructive real value**, assembled by
the ring operations on ℝ (`Radd`, `Rmul` by the constant `½`, `Rneg`, `ofQ`). The numerical value is
`λ₁ ≈ 0.0231` — positive, consistent with the Riemann hypothesis (Li's criterion: RH ⇔ λₙ > 0 ∀ n).

**Honest boundary on `Pos λ₁`.** That `λ₁ > 0` is a true numerical fact, but a *kernel-checkable*
certificate of it from this construction is **computationally out of reach**: the certificate needs γ
to ≈0.046 absolute accuracy, and γ's defining alternating ζ-series converges only like `1/N` (needs
~20 terms), while each term is an exact-rational ζ-approximant whose denominator carries the running
`lcm` — already `gammaSeq 2` has a ~7000-digit denominator, and at the required depth the figure is
astronomically larger. A feasible positivity certificate would need a convergence-accelerated /
denominator-controlled representation of γ (e.g. `γ = lim (Hₙ − log(n+1))` with a sharp ζ-tail bound),
which is a separate substantial construction. Per the project's bright line we therefore realize the
**value** of `λ₁` here and do **not** assert `Pos λ₁` — the positivity stays an explicit, honestly
labeled statement, never faked. (The crux `liPositivityHolds` remains `none`; RH stays open.)

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Euler

namespace UOR.Bridge.F1Square.Analysis

/-- **The first Li coefficient** `λ₁ = 1 + γ/2 − ½·log(4π)`, as a constructive real value
    (Bombieri–Lagarias). Scaling by the constant `½ ≤ 1` is reindex-free, so the assembly is clean. -/
def Rlambda1 : Real :=
  Radd (Radd (ofQ ⟨1, 1⟩ (by decide)) (Rmul (ofQ ⟨1, 2⟩ (by decide)) Rgamma0))
    (Rneg (Rmul (ofQ ⟨1, 2⟩ (by decide)) Rlog4pi))

end UOR.Bridge.F1Square.Analysis
