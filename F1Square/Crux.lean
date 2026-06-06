/-
F1 square — the CRUX, stated as faithfully as this substrate allows.

This module states the open crux precisely and ties it to the proved Template (P1). Discipline
(the program stance): the honesty layer is a VERIFIER, not a prohibition. We do not forbid a
proof of the crux; we forbid fooling ourselves — and the sharpest safeguard here is the
faithfulness caution made explicit below.

  • `HodgeIndex P` is the §1.5 property: the form is `> 0` on the ample class and
    negative-definite on the primitive complement `H^⊥`.
  • `template_hodgeIndex` PROVES `HodgeIndex` for the product-of-curves Template — genuine, and
    [CLASSICAL] on a real surface over a field. So the PROPERTY is real and provable.
  • The CRUX is `HodgeIndex` for the arithmetic square `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` (companion
    §1.5 / T5). It is OPEN, and here is the faithful reason it is not just a corollary of the
    Template:

    FAITHFULNESS CAUTION. The crux is `HodgeIndex` on the SPECIFIC object `𝕊`, which is not
    constructed in this substrate (§1.1, OPEN). Do NOT define the crux as a loose existential
    `∃ P, HodgeIndex P` — that is witnessed by the Template and is classically TRUE, hence is
    NOT RH. The difficulty is the construction of `𝕊`, not the property (companion §0.3: "the
    mechanism is not the gap; the surface to run it on is"). Moreover a faithful statement of RH
    via the zeta zeros needs ℂ and ζ, which this pure substrate does not have; the equivalence
    between the geometric `HodgeIndex` on `𝕊` and the analytic RH is itself [CLASSICAL].
    Therefore `CruxFor` below is parameterized by the (unconstructed) realization `P = 𝕊`; we
    neither construct it, nor assert `HodgeIndex 𝕊`, nor axiomatize it. If such a `𝕊` is one day
    built here and `HodgeIndex 𝕊` proved (axiom-clean, audited), that is a result — not a defect.
-/

import F1Square.Template

namespace UOR.Bridge.F1Square.Crux

open UOR.Bridge.F1Square.Template

/-- A polarized intersection lattice: a class type with a symmetric integer pairing, a
    distinguished ample class `H`, and a 2-parameter family `f x y = x·f₁ + y·f₂` spanning the
    primitive complement `H^⊥`. -/
structure Polarized where
  /-- the class type -/
  C : Type
  /-- the intersection pairing -/
  p : C → C → Int
  /-- the ample (polarization) class -/
  H : C
  /-- the primitive-complement family `x·f₁ + y·f₂` -/
  f : Int → Int → C

/-- The Hodge-index property (companion §1.5): `H² > 0`, and the form is negative-definite on
    the primitive complement `H^⊥` (`≤ 0` everywhere, with `0` only at the origin). -/
def HodgeIndex (P : Polarized) : Prop :=
  0 < P.p P.H P.H
  ∧ (∀ x y : Int, P.p (P.f x y) (P.f x y) ≤ 0)
  ∧ (∀ x y : Int, P.p (P.f x y) (P.f x y) = 0 → x = 0 ∧ y = 0)

/-- The product-of-curves Template (P1) as a polarized lattice. -/
def templatePolarized : Polarized where
  C := Cls
  p := pair
  H := (1, 1, 0)
  f := fun x y => (x, -x, y)

/-- The Template SATISFIES the Hodge-index property — a real theorem, assembled from P1. It is
    [CLASSICAL] on a genuine product surface; it is NOT the arithmetic square. -/
theorem template_hodgeIndex : HodgeIndex templatePolarized := by
  refine ⟨H_sq_pos, fun x y => ?_, fun x y => ?_⟩
  · exact Hperp_neg_semidef x y
  · exact Hperp_definite x y

/-- THE CRUX, parameterized by a realization. `CruxFor P` is `HodgeIndex P`; the Riemann
    Hypothesis (geometric face) is `CruxFor 𝕊` for the unconstructed arithmetic square `𝕊`.
    OPEN: no `𝕊` is constructed and `HodgeIndex 𝕊` is neither proved nor axiomatized here.
    `template_hodgeIndex` shows the property is genuine; the crux is the SAME property on a
    DIFFERENT, unbuilt object — that specificity is the open content. -/
def CruxFor (P : Polarized) : Prop := HodgeIndex P

end UOR.Bridge.F1Square.Crux
