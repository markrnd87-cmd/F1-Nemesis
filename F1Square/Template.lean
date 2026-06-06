/-
F1 square — the product-of-curves intersection-form TEMPLATE (a UOR-style realization).

Companion §2.2 / §0.3 / §1.4. Canonical form: the Néron–Severi lattice of a product of
(elliptic) curves, basis `{E₁, E₂, E₃}` with `E₁·E₂ = 1`, `E₁² = E₂² = 0`, `E₃² = −2`
(sourced: Bryan et al., arXiv 1905.07085). Invariants proved here — pure Lean 4, no Mathlib,
no `sorry`:
  • the pairing is symmetric;
  • the sourced intersection numbers (`E₁·E₂ = 1`, `E₃² = −2`);
  • the ample class `H = E₁ + E₂` has `H² = 2 > 0` (the projectivity/Kähler precondition, §1.4);
  • `H^⊥ = span{E₁−E₂, E₃}`, on which the form is `diag(−2, −2)`: negative-semidefinite AND
    nondegenerate (`pair v v = 0 ↔ v = 0`) — i.e. NEGATIVE-DEFINITE.
Together these are the Hodge type `(1, 2)` decomposition (one positive line `H`, a
negative-definite primitive plane `H^⊥`).

Scope (honest): this is the TEMPLATE the concrete 𝔽₁ square must match (§2.2 caveat); it is
[CLASSICAL] on a genuine product surface over a field, NOT a construction of the square. The
intersection numbers are the sourced ones, derived/checked — never hand-tuned (the program's
"declarative discipline").
-/

namespace UOR.Bridge.F1Square.Template

/-- A divisor class as coordinates in the basis `{E₁, E₂, E₃}`. -/
abbrev Cls : Type := Int × Int × Int

/-- The sourced intersection pairing on `NS(E × E)`:
    `⟨u, v⟩ = u₁v₂ + u₂v₁ − 2·u₃v₃` (Gram `[[0,1,0],[1,0,0],[0,0,−2]]`). -/
def pair (u v : Cls) : Int := u.1 * v.2.1 + u.2.1 * v.1 - 2 * (u.2.2 * v.2.2)

/-- Pure-core helper: every square is non-negative in `ℤ`. -/
theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have hh : 0 ≤ (-a) * (-a) := Int.mul_nonneg h' h'
    simpa using hh

/-- The pairing is symmetric. -/
theorem pair_symm (u v : Cls) : pair u v = pair v u := by
  unfold pair
  rw [Int.mul_comm u.1 v.2.1, Int.mul_comm u.2.1 v.1, Int.mul_comm u.2.2 v.2.2]
  omega

/-- Sourced: `E₁ · E₂ = 1`. -/
theorem E1_dot_E2 : pair (1, 0, 0) (0, 1, 0) = 1 := by decide

/-- Sourced: `E₃² = −2`. -/
theorem E3_sq : pair (0, 0, 1) (0, 0, 1) = -2 := by decide

/-- The ample class `H = E₁ + E₂` has `H² = 2`. -/
theorem H_sq : pair (1, 1, 0) (1, 1, 0) = 2 := by decide

/-- `H² > 0`: the projectivity/Kähler precondition (§1.4) holds on the template. -/
theorem H_sq_pos : 0 < pair (1, 1, 0) (1, 1, 0) := by decide

-- The primitive complement `H^⊥` is spanned by `f₁ = E₁ − E₂ = (1,-1,0)` and `f₂ = E₃ = (0,0,1)`.

/-- `f₁ = E₁ − E₂ ⟂ H`. -/
theorem f1_perp : pair (1, 1, 0) (1, -1, 0) = 0 := by decide

/-- `f₂ = E₃ ⟂ H`. -/
theorem f2_perp : pair (1, 1, 0) (0, 0, 1) = 0 := by decide

/-- The `H^⊥` Gram is `diag(−2,−2)` — entry `(1,1)`. -/
theorem Hperp_gram_11 : pair (1, -1, 0) (1, -1, 0) = -2 := by decide
/-- The `H^⊥` Gram is `diag(−2,−2)` — entry `(1,2)`. -/
theorem Hperp_gram_12 : pair (1, -1, 0) (0, 0, 1) = 0 := by decide
/-- The `H^⊥` Gram is `diag(−2,−2)` — entry `(2,2)`. -/
theorem Hperp_gram_22 : pair (0, 0, 1) (0, 0, 1) = -2 := by decide

/-- A general `H^⊥` vector `x·f₁ + y·f₂ = (x, −x, y)` has self-intersection
    `−2x² − 2y²` (derived, not assumed). -/
theorem Hperp_value (x y : Int) :
    pair (x, -x, y) (x, -x, y) = -2 * (x * x) - 2 * (y * y) := by
  simp only [pair, Int.mul_neg, Int.neg_mul]
  omega

/-- The form is negative-SEMIdefinite on `H^⊥`. -/
theorem Hperp_neg_semidef (x y : Int) : pair (x, -x, y) (x, -x, y) ≤ 0 := by
  rw [Hperp_value]
  have hx : 0 ≤ x * x := sq_nonneg x
  have hy : 0 ≤ y * y := sq_nonneg y
  omega

/-- Helper: in `ℤ`, `a² = 0 → a = 0` (via `natAbs`, pure core). -/
theorem int_sq_eq_zero {a : Int} (h : a * a = 0) : a = 0 := by
  have h1 : (a * a).natAbs = 0 := by simp [h]
  rw [Int.natAbs_mul] at h1
  have h2 : a.natAbs = 0 := by
    rcases Nat.mul_eq_zero.mp h1 with h' | h' <;> exact h'
  exact Int.natAbs_eq_zero.mp h2

/-- Nondegeneracy on `H^⊥`: the only null vector is `0`. With `Hperp_neg_semidef`
    this is NEGATIVE-DEFINITENESS of the form on the primitive complement — the §1.4
    Hodge-index content on the template. -/
theorem Hperp_definite (x y : Int) :
    pair (x, -x, y) (x, -x, y) = 0 → x = 0 ∧ y = 0 := by
  rw [Hperp_value]
  intro h
  have hx : 0 ≤ x * x := sq_nonneg x
  have hy : 0 ≤ y * y := sq_nonneg y
  have hx0 : x * x = 0 := by omega
  have hy0 : y * y = 0 := by omega
  exact ⟨int_sq_eq_zero hx0, int_sq_eq_zero hy0⟩

end UOR.Bridge.F1Square.Template
