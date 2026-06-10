/-
F1 square — the **cos/sin angle-addition formulas** `cos(a+b) = cos a cos b − sin a sin b` and
`sin(a+b) = sin a cos b + cos a sin b` (the v0.16.0 prerequisite for the complex exponential law
`Cexp(a+b) = Cexp a · Cexp b`, hence for the tight Lipschitz bounds `|cos a − cos b| ≤ |a−b|` that
control the η-series variation `Σ|n⁻ˢ − (n+1)⁻ˢ| < ∞` — the integration-free route to `ζ` on the
critical strip).

This module builds the **formal (finite, exact) heart**: the *antidiagonal binomial identity*

    (a+b)^{2m}/(2m)!  =  Σ_{2i ≤ 2m} a^{2i}·b^{2m−2i}/((2i)!·(2m−2i)!)        [the `cos·cos` diagonal]
                       + Σ_{2i+1 ≤ 2m} a^{2i+1}·b^{2m−2i−1}/((2i+1)!·(2m−2i−1)!)  [the `sin·sin` diagonal]

which is exactly `cos(a+b)`'s degree-`2m` term reorganized into the product diagonals. It is a pure
binomial fact: each coefficient `C(2m,p)/(2m)! = 1/(p!·(2m−p)!)` (`choose_mul_fct_mul_fct`), and the
even/odd split of `p` is `Fsum_parity_split`. The convergence/reconciliation (lifting to `RaltReal`)
builds on top, mirroring `CosSinAdd` / `ExpRealAdd`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.CosSinAdd
import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Analysis

/-- **The two-variable pair term** `aᵖ·b^{2m−p}/(p!·(2m−p)!)` — the coefficient-`p` summand of the
    degree-`2m` antidiagonal (a `cos·cos` term when `p` even, a `sin·sin` term when `p` odd). -/
def pairTerm (a b : Q) (m p : Nat) : Q :=
  mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩

theorem pairTerm_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m p : Nat) :
    0 < (pairTerm a b m p).den :=
  Qmul_den_pos (Qmul_den_pos (qpow_den_pos had p) (qpow_den_pos hbd _))
    (Nat.mul_pos (fct_pos _) (fct_pos _))

/-- **Per-term scaling**: the binomial term `C(2m,p)·aᵖ·b^{2m−p}` divided by `(2m)!` equals the pair
    term `aᵖ·b^{2m−p}/(p!·(2m−p)!)` (the binomial-coefficient identity `C(2m,p)/(2m)! = 1/(p!(2m−p)!)`). -/
theorem binTerm_scaled_eq {a b : Q} (m : Nat) {p : Nat} (hp : p ≤ 2 * m) :
    Qeq (mul (⟨1, fct (2 * m)⟩ : Q) (binTerm a b (2 * m) p)) (pairTerm a b m p) := by
  -- `binTerm a b (2m) p = ⟨C(2m,p),1⟩ · (aᵖ · b^{2m−p})`; scale by `1/(2m)!`. The whole thing reduces to
  -- the coefficient identity `⟨C(2m,p), (2m)!⟩ ≈ ⟨1, p!·(2m−p)!⟩` (`choose_mul_fct_mul_fct`).
  have hkeyZ : (choose (2 * m) p : Int) * (fct p : Int) * (fct (2 * m - p) : Int)
      = (fct (2 * m) : Int) := by exact_mod_cast choose_mul_fct_mul_fct hp
  show Qeq (mul (⟨1, fct (2 * m)⟩ : Q)
      (mul (⟨(choose (2 * m) p : Int), 1⟩ : Q) (mul (qpow a p) (qpow b (2 * m - p)))))
    (mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩)
  simp only [Qeq, mul]
  push_cast
  generalize (qpow a p).num = an
  generalize (qpow b (2 * m - p)).num = bn
  generalize ((qpow a p).den : Int) = ad
  generalize ((qpow b (2 * m - p)).den : Int) = bd
  generalize ((choose (2 * m) p : Nat) : Int) = cc at hkeyZ ⊢
  generalize ((fct p : Nat) : Int) = fp at hkeyZ ⊢
  generalize ((fct (2 * m - p) : Nat) : Int) = fq at hkeyZ ⊢
  generalize ((fct (2 * m) : Nat) : Int) = ff at hkeyZ ⊢
  rw [← hkeyZ]; ring_uor

/-- **The antidiagonal binomial identity** (the formal heart of the addition formula): for `m = m'+1`,

    `(a+b)^{2m}/(2m)!  =  Σ_{j=0}^{m'+1} a^{2j}·b^{2m−2j}/((2j)!·(2m−2j)!)`     [`cos·cos` diagonal]
                        ` + Σ_{j=0}^{m'} a^{2j+1}·b^{2m−2j−1}/((2j+1)!·(2m−2j−1)!)` [`sin·sin` diagonal].

    Pure binomial: expand `(a+b)^{2m}` (`binomial`), divide each term by `(2m)!`
    (`binTerm_scaled_eq`, the coefficient identity), then split the index by parity
    (`Fsum_parity_split`). The `sin·sin` diagonal has the even `p`-terms removed and `+1` shifted. -/
theorem addPow_div_antidiag {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
  have hbtd : ∀ i, 0 < (binTerm a b (2 * (m' + 1)) i).den := binTerm_den_pos had hbd _
  have hptd : ∀ i, 0 < (pairTerm a b (m' + 1) i).den := pairTerm_den_pos had hbd _
  have hc2m : 0 < (⟨1, fct (2 * (m' + 1))⟩ : Q).den := fct_pos _
  -- `(a+b)^{2m}·(1/(2m)!) ≈ (1/(2m)!)·Σ binTerm`.
  have h1 : Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1)))) :=
    Qeq_trans (Qmul_den_pos (Fsum_den_pos hbtd _) hc2m)
      (Qmul_congr (binomial had hbd _) (Qeq_refl _)) (Qmul_swap _ _)
  -- distribute the scaling into the sum, then rewrite each term to `pairTerm`.
  have h2 : Qeq (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1))))
      (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1))) :=
    Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hc2m (hbtd i)) _)
      (Qeq_symm (Fsum_mul_left hc2m hbtd _))
      (Fsum_congr_le (fun i hi => binTerm_scaled_eq (m' + 1) (by omega : i ≤ 2 * (m' + 1))))
  -- parity-split the index `0 ≤ p ≤ 2m = 2m'+2`.
  have h3 : Qeq (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1)))
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
    have hsplit := Fsum_parity_split (pairTerm a b (m' + 1)) hptd m'
    rwa [show 2 * m' + 2 = 2 * (m' + 1) from by omega] at hsplit
  exact Qeq_trans (Qmul_den_pos hc2m (Fsum_den_pos hbtd _)) h1
    (Qeq_trans (Fsum_den_pos hptd _) h2 h3)

-- ===========================================================================
-- The **signed diagonal relation** `altTerm(a+b,0,m) = cos·cos-diagonal − sin·sin-diagonal`,
-- connecting the (sign-free) antidiagonal sums to the actual product diagonals of `cos`/`sin`.
-- ===========================================================================

/-- `(a²)ʲ ≈ a^{2j}`. -/
theorem qpow_sq_eq {a : Q} (had : 0 < a.den) (j : Nat) :
    Qeq (qpow (mul a a) j) (qpow a (2 * j)) := by
  rw [show 2 * j = j + j from by omega]
  exact Qeq_trans (Qmul_den_pos (qpow_den_pos had j) (qpow_den_pos had j))
    (qpow_mul_dist a a had had j) (Qeq_symm (qpow_add a had j j))

/-- **Signed power split**: `(−a²)ʲ ≈ (−1)ʲ·a^{2j}`. -/
theorem qpow_negsq {a : Q} (had : 0 < a.den) (j : Nat) :
    Qeq (qpow (neg (mul a a)) j) (mul (qpow (⟨-1, 1⟩ : Q) j) (qpow a (2 * j))) := by
  have hneg : Qeq (neg (mul a a)) (mul (⟨-1, 1⟩ : Q) (mul a a)) := by
    simp only [Qeq, neg, mul]; push_cast; ring_uor
  have hN : 0 < (neg (mul a a)).den := Nat.mul_pos had had
  have hM : 0 < (mul (⟨-1, 1⟩ : Q) (mul a a)).den := Qmul_den_pos (by decide) (Qmul_den_pos had had)
  refine Qeq_trans (qpow_den_pos hM j) (qpow_Qeq hneg j) ?_
  refine Qeq_trans (Qmul_den_pos (qpow_den_pos (by decide) j) (qpow_den_pos (Qmul_den_pos had had) j))
    (qpow_mul_dist (⟨-1, 1⟩ : Q) (mul a a) (by decide) (Qmul_den_pos had had) j) ?_
  exact Qmul_congr (Qeq_refl _) (qpow_sq_eq had j)

/-- **Paired signed powers**: `(−a²)ʲ·(−b²)^{m−j} ≈ (−1)ᵐ·a^{2j}·b^{2(m−j)}` (for `j ≤ m`). -/
theorem negsq_pair {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (qpow (neg (mul a a)) j) (qpow (neg (mul b b)) (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))) := by
  have hSa : 0 < (qpow (⟨-1, 1⟩ : Q) j).den := qpow_den_pos (by decide) j
  have hSb : 0 < (qpow (⟨-1, 1⟩ : Q) (m - j)).den := qpow_den_pos (by decide) (m - j)
  have hA : 0 < (qpow a (2 * j)).den := qpow_den_pos had (2 * j)
  have hB : 0 < (qpow b (2 * (m - j))).den := qpow_den_pos hbd (2 * (m - j))
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSa hA) (Qmul_den_pos hSb hB))
    (Qmul_congr (qpow_negsq had j) (qpow_negsq hbd (m - j))) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSa hSb) (Qmul_den_pos hA hB))
    (Qmul4_rearrange _ _ _ _) ?_
  refine Qmul_congr ?_ (Qeq_refl _)
  have hm : j + (m - j) = m := by omega
  have h := Qeq_symm (qpow_add (⟨-1, 1⟩ : Q) (by decide) j (m - j))
  rwa [hm] at h

/-- `(1/d₁)·(1/d₂) ≈ 1/(d₁·d₂)`. -/
private theorem mul_inv_dens (d1 d2 : Nat) : Qeq (mul (⟨1, d1⟩ : Q) ⟨1, d2⟩) ⟨1, d1 * d2⟩ := by
  show (1 * 1 : Int) * ((d1 * d2 : Nat) : Int) = (1 : Int) * ((d1 * d2 : Nat) : Int)
  generalize ((d1 * d2 : Nat) : Int) = X; ring_uor

/-- **The paired alternating-term identity** (any offset `off`): the product of the `off`-shifted
    `j`-th and `(m−j)`-th alternating terms equals `(−1)ᵐ·a^{2j}·b^{2(m−j)}/((2j+off)!·(2(m−j)+off)!)`.
    (`off = 0` gives the `cos·cos` diagonal; `off = 1` the body of the `sin·sin` diagonal.) -/
theorem altPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m)
    (off : Nat) :
    Qeq (mul (altTerm a off j) (altTerm b off (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m)
          (mul (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))
            ⟨1, fct (2 * j + off) * fct (2 * (m - j) + off)⟩)) := by
  have hP1 : 0 < (qpow (neg (mul a a)) j).den := qpow_den_pos (Nat.mul_pos had had) j
  have hP2 : 0 < (qpow (neg (mul b b)) (m - j)).den := qpow_den_pos (Nat.mul_pos hbd hbd) (m - j)
  have hF1 : 0 < (⟨1, fct (2 * j + off)⟩ : Q).den := fct_pos _
  have hF2 : 0 < (⟨1, fct (2 * (m - j) + off)⟩ : Q).den := fct_pos _
  have hSm : 0 < (qpow (⟨-1, 1⟩ : Q) m).den := qpow_den_pos (by decide) m
  have hA : 0 < (qpow a (2 * j)).den := qpow_den_pos had (2 * j)
  have hB : 0 < (qpow b (2 * (m - j))).den := qpow_den_pos hbd (2 * (m - j))
  simp only [altTerm]
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hP1 hP2) (Qmul_den_pos hF1 hF2))
    (Qmul4_rearrange _ _ _ _) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSm (Qmul_den_pos hA hB))
      (Nat.mul_pos (fct_pos _) (fct_pos _) :
        0 < (⟨1, fct (2 * j + off) * fct (2 * (m - j) + off)⟩ : Q).den))
    (Qmul_congr (negsq_pair had hbd hjm) (mul_inv_dens _ _)) ?_
  exact Qeq_symm (Qmul_assoc3 _ _ _)

/-- **The `cos·cos` diagonal term** `cosTermⱼ·cosT_{m−j} ≈ (−1)ᵐ·pairTerm(2j)` (`j ≤ m`). -/
theorem cosPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (altTerm a 0 j) (altTerm b 0 (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (pairTerm a b m (2 * j))) := by
  have he : 2 * m - 2 * j = 2 * (m - j) := by omega
  have h := altPair_eq had hbd hjm 0
  simp only [Nat.add_zero] at h
  simp only [pairTerm, he]
  exact h

/-- The `i`-th term of `sin a = a·Σ (−a²)ⁱ/(2i+1)!`. -/
def sinTerm (a : Q) (i : Nat) : Q := mul a (altTerm a 1 i)

theorem sinTerm_den_pos {a : Q} (had : 0 < a.den) (i : Nat) : 0 < (sinTerm a i).den :=
  Qmul_den_pos had (altTerm_den_pos had 1 i)

/-- **The `sin·sin` diagonal term** `sinTermⱼ·sinT_{m'−j} ≈ (−1)^{m'}·pairTerm(2j+1)` (`j ≤ m'`). -/
theorem sinPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m' : Nat} (hjm : j ≤ m') :
    Qeq (mul (sinTerm a j) (sinTerm b (m' - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m') (pairTerm a b (m' + 1) (2 * j + 1))) := by
  have hr : 2 * (m' + 1) - (2 * j + 1) = 2 * (m' - j) + 1 := by omega
  have hAB : 0 < (mul (altTerm a 1 j) (altTerm b 1 (m' - j))).den :=
    Qmul_den_pos (altTerm_den_pos had 1 j) (altTerm_den_pos hbd 1 (m' - j))
  -- pull out the `a·b` factor, reduce the inner alternating product via `altPair_eq`.
  have hstep : Qeq (mul (sinTerm a j) (sinTerm b (m' - j)))
      (mul (mul a b) (mul (qpow (⟨-1, 1⟩ : Q) m')
        (mul (mul (qpow a (2 * j)) (qpow b (2 * (m' - j))))
          ⟨1, fct (2 * j + 1) * fct (2 * (m' - j) + 1)⟩))) := by
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos had hbd) hAB)
      (Qmul4_rearrange a (altTerm a 1 j) b (altTerm b 1 (m' - j))) ?_
    exact Qmul_congr (Qeq_refl _) (altPair_eq had hbd hjm 1)
  refine Qeq_trans ?_ hstep ?_
  · exact Qmul_den_pos (Qmul_den_pos had hbd) (Qmul_den_pos (qpow_den_pos (by decide) m')
      (Qmul_den_pos (Qmul_den_pos (qpow_den_pos had _) (qpow_den_pos hbd _))
        (Nat.mul_pos (fct_pos _) (fct_pos _))))
  -- the remaining AC rearrangement: `(a·b)·(Sm'·(A·B)·G) = Sm'·((a·A)·(b·B))·G`, with `a·A^{2j}=A^{2j+1}`.
  simp only [pairTerm, hr, qpow_succ]
  simp only [Qeq, mul]
  generalize a.num = an; generalize (a.den : Int) = ad
  generalize b.num = bn; generalize (b.den : Int) = bd
  generalize (qpow a (2 * j)).num = aA; generalize ((qpow a (2 * j)).den : Int) = aD
  generalize (qpow b (2 * (m' - j))).num = bB; generalize ((qpow b (2 * (m' - j))).den : Int) = bD
  generalize (qpow (⟨-1, 1⟩ : Q) m').num = sn; generalize ((qpow (⟨-1, 1⟩ : Q) m').den : Int) = sd
  push_cast
  generalize ((fct (2 * j + 1) : Nat) : Int) = f1
  generalize ((fct (2 * (m' - j) + 1) : Nat) : Int) = f2
  ring_uor

-- ===========================================================================
-- The diagonal convolutions and the **diagonal addition identity**.
-- ===========================================================================

/-- The degree-`m` `cos·cos` diagonal `Σ_{j≤m} cosTermⱼ·cosT_{m−j}`. -/
def cosConv (a b : Q) (m : Nat) : Q := Fsum (fun j => mul (altTerm a 0 j) (altTerm b 0 (m - j))) m

/-- The degree-`m'` `sin·sin` diagonal `Σ_{j≤m'} sinTermⱼ·sinT_{m'−j}`. -/
def sinConv (a b : Q) (m' : Nat) : Q := Fsum (fun j => mul (sinTerm a j) (sinTerm b (m' - j))) m'

theorem cosConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    0 < (cosConv a b m).den :=
  Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 j) (altTerm_den_pos hbd 0 (m - j))) m

theorem sinConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    0 < (sinConv a b m').den :=
  Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had j) (sinTerm_den_pos hbd (m' - j))) m'

/-- The `cos·cos` diagonal factors as `(−1)ᵐ · Σ_j pairTerm(2j)`. -/
theorem cosConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    Qeq (cosConv a b m)
        (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTerm a b m (2 * j)) m)) := by
  simp only [cosConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m)
      (pairTerm_den_pos had hbd m _)) m)
    (Fsum_congr_le (fun j hj => cosPair_eq had hbd (by omega : j ≤ m))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m) (fun j => pairTerm_den_pos had hbd m _) m

/-- The `sin·sin` diagonal factors as `(−1)^{m'} · Σ_j pairTerm(2j+1)`. -/
theorem sinConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (sinConv a b m')
        (mul (qpow (⟨-1, 1⟩ : Q) m') (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
  simp only [sinConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m')
      (pairTerm_den_pos had hbd (m' + 1) _)) m')
    (Fsum_congr_le (fun j hj => sinPair_eq had hbd (by omega : j ≤ m'))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m') (fun j => pairTerm_den_pos had hbd (m' + 1) _) m'

/-- `(−1)·x ≈ −x`. -/
private theorem neg_one_mul_eq (x : Q) : Qeq (mul (⟨-1, 1⟩ : Q) x) (neg x) := by
  simp only [Qeq, mul, neg]; push_cast; ring_uor

/-- **The diagonal addition identity** (`m = m'+1`): the degree-`m` term of `cos(a+b)` equals the
    `cos·cos` diagonal minus the `sin·sin` diagonal — i.e. the per-degree `cos(a+b) = cos·cos − sin·sin`.
    From the antidiagonal binomial identity (`addPow_div_antidiag`) by extracting the sign `(−1)ᵐ`
    (`qpow_negsq`) and matching the even/odd sums to the `cos·cos`/`sin·sin` diagonals
    (`cosConv_eq`/`sinConv_eq`); the `(−1)^{m'+1}` on the odd sum supplies the subtraction. -/
theorem altTerm_add_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (altTerm (add a b) 0 (m' + 1))
        (Qsub (cosConv a b (m' + 1)) (sinConv a b m')) := by
  have habd : 0 < (add a b).den := add_den_pos had hbd
  have hEd : 0 < (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1)).den :=
    Fsum_den_pos (fun j => pairTerm_den_pos had hbd _ _) _
  have hOd : 0 < (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m').den :=
    Fsum_den_pos (fun j => pairTerm_den_pos had hbd _ _) _
  have hS1d : 0 < (qpow (⟨-1, 1⟩ : Q) (m' + 1)).den := qpow_den_pos (by decide) _
  -- step 1: `altTerm(a+b,0,m) ≈ S1 · ((a+b)^{2m}/(2m)!) ≈ S1 · (E + O)`.
  have hsign : Qeq (altTerm (add a b) 0 (m' + 1))
      (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
        (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)) := by
    show Qeq (mul (qpow (neg (mul (add a b) (add a b))) (m' + 1)) ⟨1, fct (2 * (m' + 1) + 0)⟩)
      (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
        (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩))
    simp only [Nat.add_zero]
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hS1d (qpow_den_pos habd _)) (fct_pos _))
      (Qmul_congr (qpow_negsq habd (m' + 1)) (Qeq_refl _)) ?_
    exact Qeq_symm (Qmul_assoc3 _ _ _)
  have hanti : Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) :=
    addPow_div_antidiag had hbd m'
  have hstep1 : Qeq (altTerm (add a b) 0 (m' + 1))
      (add (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1)) (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1)))
           (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1)) (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m'))) :=
    Qeq_trans (Qmul_den_pos hS1d (Qmul_den_pos (qpow_den_pos habd _) (fct_pos _))) hsign
      (Qeq_trans (Qmul_den_pos hS1d (add_den_pos hEd hOd)) (Qmul_congr (Qeq_refl _) hanti)
        (Qmul_add_left _ _ _))
  -- step 2: `S1·E ≈ cosConv`, and `S1·O ≈ −sinConv`.
  have hcos : Qeq (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
      (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))) (cosConv a b (m' + 1)) :=
    Qeq_symm (cosConv_eq had hbd (m' + 1))
  have hsin : Qeq (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
      (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) (neg (sinConv a b m')) := by
    -- `S1 = (−1)·(−1)^{m'}`, so `S1·O = (−1)·((−1)^{m'}·O) ≈ (−1)·sinConv ≈ −sinConv`.
    rw [show qpow (⟨-1, 1⟩ : Q) (m' + 1) = mul (⟨-1, 1⟩ : Q) (qpow (⟨-1, 1⟩ : Q) m') from qpow_succ _ m']
    refine Qeq_trans (Qmul_den_pos (by decide) (Qmul_den_pos (qpow_den_pos (by decide) m') hOd))
      (Qeq_symm (Qmul_assoc3 _ _ _)) ?_
    refine Qeq_trans (Qmul_den_pos (by decide) (sinConv_den_pos had hbd m'))
      (Qmul_congr (Qeq_refl _) (Qeq_symm (sinConv_eq had hbd m'))) ?_
    exact neg_one_mul_eq _
  -- combine: `add (S1·E) (S1·O) ≈ add cosConv (−sinConv) = Qsub cosConv sinConv`.
  refine Qeq_trans (add_den_pos (Qmul_den_pos hS1d hEd) (Qmul_den_pos hS1d hOd)) hstep1 ?_
  exact Qadd_congr hcos hsin

end UOR.Bridge.F1Square.Analysis
