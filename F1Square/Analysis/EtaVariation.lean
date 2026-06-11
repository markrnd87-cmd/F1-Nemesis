/-
F1 square — the **`n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ = n⁻ˢ · e^{−s·δ_n}` (`δ_n = log(n+1) − log n`),
the engine of the η-series **variation bound** `Σ |n⁻ˢ − (n+1)⁻ˢ| < ∞` (`Re s > 0`) — the integration-free
route to `ζ` on the critical strip. The recurrence is the direct consequence of the complex exponential
law `Cexp_add`: `n⁻ˢ = e^{−s·log n}` (`cpowNeg`), and `log(n+1) = log n + δ_n`, so
`e^{−s·log(n+1)} = e^{−s·log n}·e^{−s·δ_n}`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.ComplexExpAdd
import F1Square.Analysis.ComplexZeta

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Complex-algebra helpers (componentwise `Ceq = ⟨Req, Req⟩` lifts of the real laws).
-- ===========================================================================

/-- `Rsub (Rneg x) (Rneg y) ≈ Rneg (Rsub x y)` (both `≈ y − x`). -/
theorem Rsub_RnegRneg (x y : Real) : Req (Rsub (Rneg x) (Rneg y)) (Rneg (Rsub x y)) :=
  Req_symm (Rneg_Radd x (Rneg y))

/-- ℂ addition respects `≈`. -/
theorem Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') := ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- ℂ negation respects `≈`. -/
theorem Cneg_congr {z z' : Complex} (h : Ceq z z') : Ceq (Cneg z) (Cneg z') :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- ℂ multiplication respects `≈`. -/
theorem Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

/-- ℂ subtraction respects `≈`. -/
theorem Csub_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Csub z w) (Csub z' w') := Cadd_congr hz (Cneg_congr hw)

/-- `z·(−w) ≈ −(z·w)` on ℂ. -/
theorem Cmul_neg_right (z w : Complex) : Ceq (Cmul z (Cneg w)) (Cneg (Cmul z w)) :=
  ⟨Req_trans (Rsub_congr (Rmul_neg_right z.re w.re) (Rmul_neg_right z.im w.im))
      (Rsub_RnegRneg (Rmul z.re w.re) (Rmul z.im w.im)),
   Req_trans (Radd_congr (Rmul_neg_right z.re w.im) (Rmul_neg_right z.im w.re))
      (Req_symm (Rneg_Radd (Rmul z.re w.im) (Rmul z.im w.re)))⟩

/-- **The consecutive-log gap** `δ_n = log(n+1) − log n` (for `n ≥ 2`), as a constructive real. -/
def deltaLogNat (n : Nat) (hn : 2 ≤ n) : Real :=
  Rsub (RlogNat (n + 1) (by omega)) (RlogNat n hn)

/-- **The `n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ ≈ n⁻ˢ · e^{−s·δ_n}` (for `n ≥ 2`). Both sides are
    `Cexp` of an argument; `log(n+1) = log n + δ_n` (`Radd_Rsub_self`) lifts through `Rmul_distrib` to the
    complex argument additivity, and `Cexp_add`/`Cexp_congr` close it. -/
theorem cpowNeg_succ (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (cpowNeg s (n + 1))
      (Cmul (cpowNeg s n)
        (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)) := by
  have h1 : 2 ≤ n + 1 := by omega
  unfold cpowNeg
  rw [dif_pos h1, dif_pos hn]
  -- both `ncpow` are `Cexp` of the argument `−s·log`; reduce to `Cexp_add` via argument additivity
  refine Ceq_trans (Cexp_congr (z := ⟨Rmul (Rneg s.re) (RlogNat (n + 1) h1), Rmul (Rneg s.im) (RlogNat (n + 1) h1)⟩)
      (w := Cadd ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
        ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩) ?_)
    (Cexp_add ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
      ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)
  -- argument additivity: `−s·log(n+1) ≈ −s·log n + (−s)·δ_n`, componentwise
  have hlog : Req (RlogNat (n + 1) h1) (Radd (RlogNat n hn) (deltaLogNat n hn)) :=
    Req_symm (Radd_Rsub_self (RlogNat n hn) (RlogNat (n + 1) h1))
  exact ⟨Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.re) (RlogNat n hn) (deltaLogNat n hn)),
    Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.im) (RlogNat n hn) (deltaLogNat n hn))⟩

/-- **The `n⁻ˢ` consecutive difference** `n⁻ˢ − (n+1)⁻ˢ ≈ n⁻ˢ·(1 − e^{−s·δ_n})` (for `n ≥ 2`) — the form
    on which the variation modulus `|n⁻ˢ − (n+1)⁻ˢ| ≤ |n⁻ˢ|·|1 − e^{−s·δ_n}|` is read off. Factor `n⁻ˢ`
    out of `n⁻ˢ − n⁻ˢ·e^{−s·δ_n}` (`cpowNeg_succ`) via `Cmul_distrib`/`Cmul_one`/`Cmul_neg_right`. -/
theorem cpowNeg_diff (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (Csub (cpowNeg s n) (cpowNeg s (n + 1)))
      (Cmul (cpowNeg s n)
        (Csub Cone (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))) :=
  Ceq_trans (Cadd_congr (Ceq_refl _) (Cneg_congr (cpowNeg_succ s n hn)))
    (Ceq_trans (Cadd_congr (Ceq_symm (Cmul_one (cpowNeg s n)))
        (Ceq_symm (Cmul_neg_right (cpowNeg s n)
          (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))))
      (Ceq_symm (Cmul_distrib (cpowNeg s n) Cone
        (Cneg (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)))))

/-- **`e^{−d} ≤ 1` for `d ≥ 0`** (the exponential of a non-positive argument is at most `1`). From
    `e^{−d}·e^d = 1` and `e^d ≥ 1`: `e^{−d} = e^{−d}·1 ≤ e^{−d}·e^d = 1`. -/
theorem RexpReal_neg_le_one (d : Real) (hd : Rnonneg d) : Rle (RexpReal (Rneg d)) one := by
  have hprod : Req (Rmul (RexpReal (Rneg d)) (RexpReal d)) one :=
    Req_trans (Req_symm (RexpReal_add (Rneg d) d))
      (Req_trans (RexpReal_congr (Req_trans (Radd_comm (Rneg d) d) (Radd_neg d))) RexpReal_zero)
  exact Rle_trans (Rle_of_Req (Req_symm (Rmul_one (RexpReal (Rneg d)))))
    (Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg (Rneg d)) (RexpReal_ge_one hd))
      (Rle_of_Req hprod))

-- ===========================================================================
-- The `n⁻ˢ` per-term component bounds `−n⁻ᴿᵉˢ ≤ Re/Im(n⁻ˢ) ≤ n⁻ᴿᵉˢ` (no real-abs; two-sided `Rle`,
-- mirroring `ComplexZeta`'s `czetaTerm_re_le`/`ge`). `cpowNeg s n = e^{−s·log n}` for `n ≥ 2`. -/
-- ===========================================================================

/-- `Re(n⁻ˢ) ≤ e^{−Re s·log n}` (`= n⁻ᴿᵉˢ`). -/
theorem cpowNeg_re_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).re) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_le _

/-- `−e^{−Re s·log n} ≤ Re(n⁻ˢ)`. -/
theorem cpowNeg_re_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).re) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_ge _

/-- `Im(n⁻ˢ) ≤ e^{−Re s·log n}`. -/
theorem cpowNeg_im_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).im) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_le _

/-- `−e^{−Re s·log n} ≤ Im(n⁻ˢ)`. -/
theorem cpowNeg_im_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).im) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_ge _


-- ===========================================================================
-- The tight exponential lower bound  1 + 4t ≤ e^t  (t ∈ [−1/2,0]), i.e. 1 − e^{−d} ≤ 4d.
-- The analytic crux of the η variation bound: lifts the Q-level quadratic remainder
-- `expSum_quad` (|expSum q N − (1+q)| ≤ |q|²·expSumM ≤ 3q²) through the diagonal, using the
-- algebra (1+q)−3q² ≥ 1+4q (q∈[−1,0]) to get a LINEAR bound (no real-side product to reconcile).
-- ===========================================================================

-- GOAL 1 (Q-level): for |q| ≤ 1 and q ≤ 1/(N+1) (the wiggle/upper bound) and N ≥ 1,
--   1 + 4q ≤ expSum q N + 3/(N+1).
-- Proof idea (by_cases on sign of q):
--   q ≥ 0:  expSum q N ≥ 1+q (expSum_ge_one_add, index N-1+1=N); 1+4q = (1+q)+3q ≤ expSum+3q ≤ expSum+3/(N+1)
--           since 3q ≤ 3/(N+1) (q ≤ 1/(N+1)).
--   q < 0:  expSum_quad gives |expSum q N − (1+q)| ≤ |q|²·expSumM 1 N ≤ 3q² (expSumM 1 N ≤ 3).
--           So expSum q N ≥ (1+q) − 3q². For q ∈ [−1,0): (1+q)−3q² ≥ 1+4q  (⟺ q(q+1) ≤ 0). Hence
--           1+4q ≤ expSum q N ≤ expSum q N + 3/(N+1).
-- expSumM 1 N ≤ ⟨3,1⟩ :  Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
theorem expSum_ge_one_add_four {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨1, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨3, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 3/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    -- 3q ≤ 3/(N+1)
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨3, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    -- assemble
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨3, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  1+4q ≤ (1+q) - 3q² ≤ expSum  ≤ expSum + 3/(N+1)
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q) := hq1
    -- quadratic remainder:  expSum q N ≥ (1+q) - |q|²·expSumM 1 N
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    -- |q|² ≤ |q|·1 = |q| = -q  (since q<0);  expSumM ≤ 3
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    -- expSum q N ≥ (1+q) − R   where R = |q|²·expSumM
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      -- (1+q) ≤ expSum + R
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      -- commute to  (1+q) ≤ R + expSum
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    -- 1+4q ≤ (1+q) − 3q²    (⟺ q(q+1) ≤ 0, here via |q|²≤|q|=−q)
    -- step: |q|·|q| ≤ |q|·1
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    -- now 1+4q ≤ (1+q) − |q|²·expSumM
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      -- R := |q|²·expSumM ;  show R ≤ (-q)·3 = -3q.
      -- step a:  R ≤ |q|²·3
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      -- step b:  |q|²·3 ≤ |q|·3
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      -- |q|·3 = (-q)·3   (|q| = -q since q<0)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      -- subtraction antitone:  (1+q) − (-3q) ≤ (1+q) − R ,  and (1+q) − (-3q) = 1+4q.
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · -- 1+4q = (1+q) − (-q)·3
        exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · -- (1+q) − (-q)·3 ≤ (1+q) − R  via R ≤ (-q)·3
        simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    -- chain: 1+4q ≤ (1+q)−R ≤ expSum ≤ expSum + 3/(N+1)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd)
      (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)))
      hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 3; decide))

-- Helper: the loose form of GOAL 1 with the Bishop upper bound `q ≤ 2/(N+1)` (slack `6/(N+1)`).
-- This is the form actually available at the diagonal (the real `t ≤ 0` only gives `2/(N+1)`).
private theorem expSum_ge_four_loose {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨2, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨6, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 6/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨6, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨6, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  identical to GOAL 1, slack 3 ≤ 6
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd) hRden) hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 6; decide))

-- GOAL 2 (real lift): for t ≤ 0 and t ≥ −1/2,  1 + 4t ≤ e^t.
-- Mirror RexpReal_ge_one_add_nonneg (RealPow:899-942). Diagonal j, R := RexpReal_R t j (≥ 4(j+1)).
-- LHS.seq(2j+1) = add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq A)) with A = Ridx (ofQ⟨4,1⟩) t (2*(2j+1)+1) (deep, ≥ R-scale).
-- Sample q := t.seq R.  From ht0 (t≤0): q ≤ 1/(R+1).  From htlo (t≥−1/2): q ≥ −1 (R large).  ⟹ |q|≤1.
-- Use expSum_ge_one_add_four at q,R; reconcile t.seq A ↔ t.seq R (and t.seq(2j+1)) by xreg_n_le × 4.
theorem RexpReal_ge_one_add_four {t : Real} (ht0 : Rle t zero)
    (htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) t) :
    Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) t)) (RexpReal t) := by
  intro j
  show Qle (add (⟨1, 1⟩ : Q)
      (mul (⟨4, 1⟩ : Q) (t.seq (Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)))))
    (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨2, j + 1⟩)
  -- xBound t ≥ 2 (since (t.seq 0).den ≥ 1)
  have hxB : 2 ≤ xBound t := by unfold xBound; have := t.den_pos 0; omega
  -- RexpReal_K t ≥ 2
  have hK2 : 2 ≤ RexpReal_K t := by
    unfold RexpReal_K
    have hp : 0 < npow (xBound t) (2 * xBound t + 1) := npow_pos (by omega) _
    omega
  -- R ≥ 8*(j+1) + 4
  have hRlb : 8 * (j + 1) + 4 ≤ RexpReal_R t j := by
    unfold RexpReal_R
    have hmul : 4 * (j + 1) * 2 ≤ 4 * (j + 1) * RexpReal_K t := Nat.mul_le_mul_left _ hK2
    omega
  -- RmulK ≥ 2  (xBound t ≥ 2)
  have hKmul : 2 ≤ RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t := by unfold RmulK; omega
  -- A ≥ 8*(j+1) - 1
  have hAlb : 8 * (j + 1) ≤ Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) + 1 := by
    rw [Ridx_succ (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)]
    have hmul : 2 * 2 * (2 * j + 1 + 1)
        ≤ 2 * RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t * (2 * j + 1 + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKmul)
    omega
  -- abstract the two heavy indices
  generalize hRdef : RexpReal_R t j = R at hRlb ⊢
  generalize hAdef : Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) = A at hAlb ⊢
  have hqd : 0 < (t.seq R).den := t.den_pos _
  -- the floor n₀ = 8(j+1) - 1, so n₀ + 1 = 8(j+1)
  have hn0A : 8 * (j + 1) - 1 ≤ A := by omega
  have hn0R : 8 * (j + 1) - 1 ≤ R := by omega
  have hn0succ : (8 * (j + 1) - 1) + 1 = 8 * (j + 1) := by omega
  -- q-bounds:  upper  q ≤ 2/(R+1)
  have hqhi : Qle (t.seq R) (⟨2, R + 1⟩ : Q) := by
    have h := ht0 R
    -- zero.seq R = ⟨0,1⟩ ;  add ⟨0,1⟩ ⟨2,R+1⟩ ≈ ⟨2,R+1⟩
    refine Qle_trans (add_den_pos (zero.den_pos R) (Nat.succ_pos R)) h (Qeq_le ?_)
    simp only [zero, ofQ, Qeq, add]; push_cast; ring_uor
  -- q-bounds: lower  -1/2 - 2/(R+1) ≤ q  ⟹  |q| ≤ 1
  have hq1 : Qle (Qabs (t.seq R)) (⟨1, 1⟩ : Q) := by
    have hlo := htlo R
    -- (Rneg (ofQ ⟨1,2⟩)).seq R = ⟨-1,2⟩
    have hlo' : Qle (⟨-1, 2⟩ : Q) (add (t.seq R) (⟨2, R + 1⟩ : Q)) := by
      refine Qle_trans (b := (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))).seq R)
        (Real.den_pos _ R) (Qeq_le ?_) hlo
      simp only [Rneg, ofQ, neg, Qeq]
    -- so q.num ≥ -(q.den)  (i.e. q ≥ -1) using R ≥ 3
    by_cases hsgn : 0 ≤ (t.seq R).num
    · -- q ≥ 0:  |q| = q ≤ 2/(R+1) ≤ 1
      have habsq : Qeq (Qabs (t.seq R)) (t.seq R) := by
        have hna : ((t.seq R).num.natAbs : Int) = (t.seq R).num := by omega
        simp only [Qeq, Qabs]; push_cast; rw [hna]
      have hle2 : Qle (Qabs (t.seq R)) (⟨2, R + 1⟩ : Q) :=
        Qle_trans hqd (Qeq_le habsq) hqhi
      exact Qle_trans (Nat.succ_pos R) hle2 (by simp only [Qle]; push_cast; omega)
    · -- q < 0:  |q| = -q ≤ 1/2 + 2/(R+1) ≤ 1  (R ≥ 3)
      have hneg : (t.seq R).num < 0 := Int.not_le.mp hsgn
      have hRbig : (3 : Int) ≤ ((R : Nat) : Int) := by
        have : 3 ≤ R := by omega
        exact_mod_cast this
      have hdpos : (1 : Int) ≤ ((t.seq R).den : Int) := by have := hqd; omega
      have hP : (0 : Int) < ((R : Nat) : Int) + 1 := by omega
      -- unfold hlo':  -(d·(R+1)) ≤ (n·(R+1) + 2·d)·2
      simp only [Qle, add] at hlo'
      push_cast at hlo'
      -- abbreviate the two products
      have hkey : -(t.seq R).num ≤ ((t.seq R).den : Int) := by
        -- write d, n, P
        -- hstar :  -(d*P) ≤ 2*n*P + 4*d
        have hstar : -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
            ≤ 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by
          have h := hlo'
          have e : (-1 : Int) * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
              = -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          have e2 : ((t.seq R).num * (((R : Nat) : Int) + 1) + 2 * ((t.seq R).den : Int)) * 2
              = 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by ring_uor
          rw [e, e2] at h; exact h
        -- h4d :  4*d ≤ d*P   (since P ≥ 4)
        have h4d : 4 * ((t.seq R).den : Int) ≤ ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := by
          have := Int.mul_le_mul_of_nonneg_left (a := (4 : Int)) (b := ((R : Nat) : Int) + 1)
            (c := ((t.seq R).den : Int)) (by omega) (by omega)
          have e : ((t.seq R).den : Int) * 4 = 4 * ((t.seq R).den : Int) := by ring_uor
          have e2 : ((t.seq R).den : Int) * (((R : Nat) : Int) + 1)
              = ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := rfl
          omega
        -- combine:  -(2n)*P ≤ (2d)*P
        have hcomb : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
            ≤ (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1) := by
          have e1 : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
              = -(2 * ((t.seq R).num * (((R : Nat) : Int) + 1))) := by ring_uor
          have e2 : (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1)
              = 2 * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          rw [e1, e2]; omega
        have hcanc : -(2 * (t.seq R).num) ≤ 2 * ((t.seq R).den : Int) :=
          Int.le_of_mul_le_mul_right hcomb hP
        omega
      simp only [Qle, Qabs]
      push_cast
      have hna : ((t.seq R).num.natAbs : Int) = -(t.seq R).num := by omega
      rw [hna]; omega
  -- the loose lower bound at q = t.seq R, N = R
  have hlb : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R)))
      (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) :=
    expSum_ge_four_loose hqd R (by omega) hq1 hqhi
  -- reconcile t.seq A with t.seq R at floor n0 (×4)
  have hAR : Qle (Qabs (Qsub (t.seq A) (t.seq R))) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q) :=
    xreg_n_le t hn0A hn0R
  -- 4·|t.seq A − t.seq R| ≤ 8/(n0+1) = 1/(j+1)
  have hrec : Qle (mul (⟨4, 1⟩ : Q) (t.seq A))
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)) := by
    -- |4·(A) − 4·(R)| = 4·|A−R| ≤ 8/(n0+1)
    have hmuldiff : Qle (Qabs (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R))))
        (⟨1, j + 1⟩ : Q) := by
      have he : Qeq (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R)))
          (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))) := by
        simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
      have h2 : Qle (Qabs (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))))
          (⟨1, j + 1⟩ : Q) := by
        rw [Qabs_mul]
        -- |4|·|A−R| ≤ ⟨4,1⟩·⟨2,n0+1⟩ = ⟨8,n0+1⟩ ≤ ⟨1,j+1⟩
        have h4 : Qeq (Qabs (⟨4, 1⟩ : Q)) (⟨4, 1⟩ : Q) := by simp only [Qeq, Qabs]; push_cast
        have hstep : Qle (mul (Qabs (⟨4, 1⟩ : Q)) (Qabs (Qsub (t.seq A) (t.seq R))))
            (mul (⟨4, 1⟩ : Q) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q)) :=
          Qmul_le_mul (Qabs_den_pos (by decide)) (by decide)
            (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))
            (by decide) (Qabs_num_nonneg _) (Qeq_le h4) hAR
        refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos _)) hstep ?_
        exact Qeq_le (by rw [hn0succ]; simp only [Qeq, mul]; push_cast; ring_uor)
      exact Qle_trans (Qabs_den_pos (Qmul_den_pos (by decide)
        (Qsub_den_pos (t.den_pos _) (t.den_pos _)))) (Qeq_le (Qabs_Qeq he)) h2
    exact Qle_add_of_Qabs_sub (Qmul_den_pos (by decide) (t.den_pos _))
      (Qmul_den_pos (by decide) (t.den_pos _)) (Nat.succ_pos _) hmuldiff
  -- assemble:  LHS ≤ add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq R)) + 1/(j+1)
  --               ≤ expSum + 6/(R+1) + 1/(j+1)  ≤ expSum + 2/(j+1)
  have hLHS : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R))) (⟨1, j + 1⟩ : Q)) := by
    refine Qle_trans (b := add (⟨1, 1⟩ : Q)
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)))
      (add_den_pos (by decide) (add_den_pos (Qmul_den_pos (by decide) (t.den_pos _))
        (Nat.succ_pos _))) (Qadd_le_add (Qle_refl _) hrec) ?_
    exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)
  -- chain hLHS with hlb (add 1/(j+1) on both)
  have hchain : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) (⟨1, j + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (add_den_pos (by decide) (Qmul_den_pos (by decide) (t.den_pos _)))
      (Nat.succ_pos _)) hLHS (Qadd_le_add hlb (Qle_refl _))
  -- final slack:  6/(R+1) + 1/(j+1) ≤ 2/(j+1)
  refine Qle_trans (add_den_pos (add_den_pos (expSum_den_pos hqd R) (Nat.succ_pos _))
    (Nat.succ_pos _)) hchain ?_
  -- (expSum + 6/(R+1)) + 1/(j+1) = expSum + (6/(R+1) + 1/(j+1)) ≤ expSum + 2/(j+1)
  refine Qle_trans (b := add (expSum (t.seq R) R)
    (add (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q)))
    (add_den_pos (expSum_den_pos hqd R) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)) ?_
  refine Qadd_le_add (Qle_refl _) ?_
  -- 6/(R+1) + 1/(j+1) ≤ 2/(j+1)   (R ≥ 8(j+1)+4 ⟹ 6/(R+1) ≤ 1/(j+1))
  have h6 : Qle (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q) := by
    have hRi : (8 : Int) * ((j : Int) + 1) + 4 ≤ (R : Int) := by exact_mod_cast hRlb
    simp only [Qle]; push_cast; omega
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add h6 (Qle_refl _)) ?_
  exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)

-- real-algebra rearrangements (copied from GammaOne, which is not in this import chain)
private theorem Rsub_le_of_le_add' {x y z : Real} (h : Rle x (Radd z y)) : Rle (Rsub x y) z :=
  Rle_trans (Rsub_le_sub h (Rle_refl y))
    (Rle_of_Req (Req_trans (Radd_assoc z y (Rneg y))
      (Req_trans (Radd_congr (Req_refl z) (Radd_neg y)) (Radd_zero z))))

private theorem Rle_add_of_Rsub_le' {x y z : Real} (h : Rle (Rsub x y) z) : Rle x (Radd y z) := by
  have heq : Req (Radd (Rsub x y) y) x :=
    Req_trans (Radd_assoc x (Rneg y) y)
      (Req_trans (Radd_congr (Req_refl x) (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y)))
        (Radd_zero x))
  exact Rle_trans (Rle_of_Req (Req_symm heq))
    (Rle_trans (Radd_le_add h (Rle_refl y)) (Rle_of_Req (Radd_comm z y)))

-- GOAL 3 (corollary, the applied form): 1 − e^{−d} ≤ 4d  for 0 ≤ d ≤ 1/2.
theorem RexpReal_one_sub_neg_le {d : Real} (hd0 : Rnonneg d)
    (hd1 : Rle d (ofQ (⟨1, 2⟩ : Q) (by decide))) :
    Rle (Rsub one (RexpReal (Rneg d))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) := by
  -- apply GOAL 2 at t := Rneg d
  have ht0 : Rle (Rneg d) zero :=
    Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hd0)) (Rle_of_Req Rneg_zero)
  have htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) (Rneg d) := Rle_Rneg hd1
  have hG2 : Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (RexpReal (Rneg d)) := RexpReal_ge_one_add_four ht0 htlo
  -- rewrite LHS:  1 + 4·(−d) ≈ 1 − 4·d
  have hEq : Req (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) :=
    Radd_congr (Req_refl _) (Rmul_neg_right (ofQ (⟨4, 1⟩ : Q) (by decide)) d)
  have hG2' : Rle (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) (RexpReal (Rneg d)) :=
    Rle_trans (Rle_of_Req (Req_symm hEq)) hG2
  -- rearrange:  1 − 4d ≤ e^{−d}  ⟹  1 ≤ 4d + e^{−d}  ⟹  1 − e^{−d} ≤ 4d
  have h1 : Rle one (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) (RexpReal (Rneg d))) :=
    Rle_add_of_Rsub_le' hG2'
  exact Rsub_le_of_le_add' h1


-- ===========================================================================
-- Tight cos/sin bounds for the η variation: 1 − cos x ≤ 3x² and RsinAux x ∈ [1−3x², 1+3x²]
-- (for x ∈ [−1,1]). Lifts the alternating-series quadratic remainder altSum_quad (|altSum q off N −
-- ⟨1,fct off⟩| ≤ 3|q|²) through the RaltReal diagonal, with a Bishop-overshoot clamp reconciled by
-- the established Lipschitz machinery (altSum_Lip_le/qsq_diff_le/LipS_le_U, as in RaltReal_diag_le).
-- ===========================================================================

-- altTerm q off n = (−q²)^n / (2n+off)!   [CosSin.lean:43]
-- altSum  q off 0 = altTerm q off 0 = ⟨1, fct off⟩ ;  altSum q off (n+1) = altSum q off n + altTerm q off (n+1)
-- For off ∈ {0,1}:  fct off = 1, so altSum q off 0 = ⟨1,1⟩.
-- (RaltReal x off).seq j = altSum (x.seq (RaltReal_R x j)) off (RaltReal_R x j)   [diagonal]
-- RaltReal_diag_le : j ≤ k → |RaltReal_seq x off j − RaltReal_seq x off k| ≤ ⟨1, j+1⟩   (Qbound j)
-- Rcos x = RaltReal x 0 ;  RsinAux x = RaltReal x 1 ;  Rsin x = Rmul x (RsinAux x)

-- GOAL 1 (Q-level, the keystone — mirror expSum_quad @ ExpLog.lean:597):
-- the deviation of altSum from its first term ⟨1,fct off⟩ is O(q²):  |altSum q off N − ⟨1,fct off⟩| ≤ 3·|q|².
-- Proof idea: altSum q off N − altSum q off 0 = Σ_{k=1}^N altTerm q off k ;  triangle-ineq + each
-- |altTerm q off k| = (q²)^k/(2k+off)! = q²·(q²)^{k-1}/(2k+off)! ≤ q²·1/(2k+off)! (|q|≤1), and Σ 1/(2k+off)! ≤ 3.
-- |neg(q²)| = |q|·|q| as a Q-equality.
private theorem altq2_abs {q : Q} : Qabs (neg (mul q q)) = mul (Qabs q) (Qabs q) := by
  rw [Qabs_neg, Qabs_mul]

-- |q|² ≤ ⟨1,1⟩ from |q| ≤ ⟨1,1⟩.
private theorem altq2_le_one {q : Q} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) :
    Qle (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q) := by
  have h := Qmul_le_mul (a := Qabs q) (b := ⟨1, 1⟩) (c := Qabs q) (d := ⟨1, 1⟩)
    (Qabs_den_pos hqd) (by decide) (Qabs_den_pos hqd) (Qabs_num_nonneg q) (Qabs_num_nonneg q) hq1 hq1
  refine Qle_trans (Qmul_den_pos (by decide) (by decide)) h (Qeq_le ?_)
  simp only [Qeq, mul]; push_cast

-- **Per-term quadratic bound** for the alternating series (k ≥ 1):
-- |altTerm q off k| ≤ |q|²·(1/k!).
private theorem altTerm_quad {q : Q} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q))
    {off n : Nat} (hn : 1 ≤ n) :
    Qle (Qabs (altTerm q off n)) (mul (mul (Qabs q) (Qabs q)) (⟨1, fct n⟩ : Q)) := by
  have hq2d : 0 < (mul (Qabs q) (Qabs q)).den := Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)
  have hq2n : 0 ≤ (mul (Qabs q) (Qabs q)).num :=
    Int.mul_nonneg (Qabs_num_nonneg q) (Qabs_num_nonneg q)
  have hq2one : Qle (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q) := altq2_le_one hqd hq1
  -- |altTerm| = qpow |neg q²| n · ⟨1,fct(2n+off)⟩
  have habs : Qabs (altTerm q off n)
      = mul (Qabs (qpow (neg (mul q q)) n)) ⟨1, fct (2 * n + off)⟩ := by
    unfold altTerm; rw [Qabs_mul]; rfl
  rw [habs]
  -- Qabs (qpow b n) = qpow (Qabs b) n = qpow (mul |q| |q|) n
  have hbabs : Qeq (Qabs (qpow (neg (mul q q)) n)) (qpow (mul (Qabs q) (Qabs q)) n) := by
    rw [← altq2_abs]; exact qpow_abs (neg (mul q q)) n
  -- qpow q2 n ≤ q2  (n ≥ 1):  qpow q2 n = q2 · qpow q2 (n-1) ≤ q2·1
  have hsplit : Qeq (qpow (mul (Qabs q) (Qabs q)) n)
      (mul (mul (Qabs q) (Qabs q)) (qpow (mul (Qabs q) (Qabs q)) (n - 1))) := by
    have hid : 1 + (n - 1) = n := by omega
    have h := qpow_add (mul (Qabs q) (Qabs q)) hq2d 1 (n - 1)
    rw [hid] at h
    refine Qeq_trans (Qmul_den_pos (qpow_den_pos hq2d 1) (qpow_den_pos hq2d (n - 1))) h ?_
    refine Qmul_congr ?_ (Qeq_refl _)
    show Qeq (qpow (mul (Qabs q) (Qabs q)) 1) (mul (Qabs q) (Qabs q))
    show Qeq (mul (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q)) (mul (Qabs q) (Qabs q))
    simp only [Qeq, mul]; push_cast; ring_uor
  have hle1 : Qle (qpow (mul (Qabs q) (Qabs q)) (n - 1)) (⟨1, 1⟩ : Q) :=
    qpow_le_one hq2n hq2d hq2one (n - 1)
  have hpow : Qle (qpow (mul (Qabs q) (Qabs q)) n) (mul (Qabs q) (Qabs q)) := by
    refine Qle_trans (Qmul_den_pos hq2d (qpow_den_pos hq2d (n - 1))) (Qeq_le hsplit) ?_
    refine Qle_trans (Qmul_den_pos hq2d (by decide)) (Qmul_le_mul_left hq2n hle1) (Qeq_le ?_)
    show Qeq (mul (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q)) (mul (Qabs q) (Qabs q))
    simp only [Qeq, mul]; push_cast; ring_uor
  -- |altTerm| ≤ q2·⟨1,fct(2n+off)⟩ ≤ q2·⟨1,fct n⟩
  have hstep1 : Qle (mul (Qabs (qpow (neg (mul q q)) n)) ⟨1, fct (2 * n + off)⟩)
      (mul (mul (Qabs q) (Qabs q)) ⟨1, fct (2 * n + off)⟩) := by
    refine Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) ?_
    exact Qle_trans (qpow_den_pos hq2d n) (Qeq_le hbabs) hpow
  have hstep2 : Qle (mul (mul (Qabs q) (Qabs q)) ⟨1, fct (2 * n + off)⟩)
      (mul (mul (Qabs q) (Qabs q)) ⟨1, fct n⟩) := by
    refine Qmul_le_mul_left hq2n ?_
    show (1 : Int) * ((fct n : Nat) : Int) ≤ 1 * ((fct (2 * n + off) : Nat) : Int)
    have := fct_mono (show n ≤ 2 * n + off by omega); push_cast; omega
  exact Qle_trans (Qmul_den_pos hq2d (fct_pos _)) hstep1 hstep2

-- **Quadratic remainder with M-series RHS** (mirror expSum_quad): for |q|≤1,
-- |altSum q off (N+1) − ⟨1,fct off⟩| ≤ |q|²·(expSumM 1 (N+1) − ⟨1,1⟩).
-- Note: altSum q off 0 = ⟨1,fct off⟩, so the k=0 term is excluded; we subtract the ⟨1,1⟩ = 1/0!.
private theorem altSum_quad_M {q : Q} {off : Nat} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q))
    (N : Nat) : Qle (Qabs (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)))
      (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 N) (⟨1, 1⟩ : Q))) := by
  induction N with
  | zero =>
      -- altSum q off 0 = ⟨1,fct off⟩, so |difference| = 0; RHS = |q|²·0 = 0
      have hidx : 2 * 0 + off = off := by omega
      -- |Qsub (altSum q off 0) ⟨1,fct off⟩| ≈ 0
      have habs0 : Qeq (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (Qabs (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct (2 * 0 + off)⟩) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩
        rw [hidx]
        have : (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct off⟩) (⟨1, fct off⟩ : Q)).num = 0 := by
          simp only [Qsub, add, neg, mul]; push_cast; ring_uor
        simp only [Qeq, Qabs]; rw [this]; simp
      have hz : Qeq (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 0) (⟨1, 1⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (mul (mul (Qabs q) (Qabs q)) (Qsub (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q))) ⟨0, 1⟩
        simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor
      have habsd : 0 < (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))).den :=
        Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off 0) (fct_pos off))
      refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) (Qeq_le habs0) ?_
      exact Qeq_le (Qeq_symm hz)
  | succ N ih =>
      -- altSum q off (N+1) = altSum q off N + altTerm q off (N+1)
      show Qle (Qabs (Qsub (add (altSum q off N) (altTerm q off (N + 1))) (⟨1, fct off⟩ : Q)))
        (mul (mul (Qabs q) (Qabs q))
          (Qsub (add (expSumM 1 N) ⟨(npow 1 (N + 1) : Int), fct (N + 1)⟩) (⟨1, 1⟩ : Q)))
      have hrw : Qeq (Qsub (add (altSum q off N) (altTerm q off (N + 1))) (⟨1, fct off⟩ : Q))
          (add (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)) (altTerm q off (N + 1))) := by
        simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
      refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (altSum_den_pos hqd off N)
          (fct_pos off)) (altTerm_den_pos hqd off (N + 1))))
        (Qeq_symm (Qabs_Qeq hrw)) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off N) (fct_pos off)))
          (Qabs_den_pos (altTerm_den_pos hqd off (N + 1))))
        (Qabs_add_le _ _) ?_
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
          (Qsub_den_pos (expSumM_den_pos 1 N) (by decide)))
          (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (fct_pos _)))
        (Qadd_le_add ih (altTerm_quad hqd hq1 (by omega : 1 ≤ N + 1))) (Qeq_le ?_)
      rw [npow_one]
      simp only [Qeq, mul, add, Qsub, neg]; push_cast; ring_uor

theorem altSum_quad {q : Q} {off : Nat} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (N : Nat) :
    Qle (Qabs (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)))
      (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) := by
  cases N with
  | zero =>
      -- |difference| is 0 ≤ |q|²·3
      have hidx : 2 * 0 + off = off := by omega
      have habs0 : Qeq (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (Qabs (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct (2 * 0 + off)⟩) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩
        rw [hidx]
        have : (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct off⟩) (⟨1, fct off⟩ : Q)).num = 0 := by
          simp only [Qsub, add, neg, mul]; push_cast; ring_uor
        simp only [Qeq, Qabs]; rw [this]; simp
      refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) (Qeq_le habs0) ?_
      exact Qsq_mul_nonneg q (⟨3, 1⟩ : Q) (by decide)
  | succ M =>
      -- use the M-series bound, then expSumM 1 (M+1) − 1 ≤ 3
      have hM := altSum_quad_M (off := off) hqd hq1 (M + 1)
      have hnn : 0 ≤ (mul (Qabs q) (Qabs q)).num :=
        Int.mul_nonneg (Qabs_num_nonneg q) (Qabs_num_nonneg q)
      -- expSumM 1 (M+1) ≤ ⟨3,1⟩ , so expSumM 1 (M+1) − ⟨1,1⟩ ≤ ⟨3,1⟩
      have hEbound : Qle (expSumM 1 (M + 1)) (⟨3, 1⟩ : Q) :=
        Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 (M + 1)) (by decide)
      have hsuble : Qle (Qsub (expSumM 1 (M + 1)) (⟨1, 1⟩ : Q)) (⟨3, 1⟩ : Q) :=
        Qle_trans (expSumM_den_pos 1 (M + 1))
          (Qsub_le_self (by show (0 : Int) ≤ 1; decide)) hEbound
      have hstep : Qle (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 (M + 1)) (⟨1, 1⟩ : Q)))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) := Qmul_le_mul_left hnn hsuble
      exact Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
        (Qsub_den_pos (expSumM_den_pos 1 (M + 1)) (by decide))) hM hstep

-- GOAL 2 (real lift, two-sided — mirror RexpReal_ge_one_add_four @ EtaVariation.lean):
-- for x ∈ [−1,1],  |RaltReal x off − 1| ≤ 3·x²  (both sides). Here off ∈ {0,1} so the first term is 1.
-- The diagonal sample q = x.seq R can overshoot [−1,1] by ≤ 2/(R+1), so altSum_quad is applied not
-- to q but to its CLAMP q' ∈ [−1,1] (|q'|≤1), and the gap |altSum q − altSum q'| is killed by the
-- Lipschitz machinery (altSum_Lip_le + qsq_diff_le + LipS_le_U), exactly as in RaltReal_diag_le.
-- The RHS product diagonal x.seq A is then reconciled with q' by product-Lipschitz.

-- npow B (2B+1) ≥ B² (B ≥ 1), used to floor RaltReal_K below.
private theorem npow_ge_sq {B : Nat} (hB : 0 < B) : B * B ≤ npow B (2 * B + 1) := by
  have h1 : B ≤ npow B (2 * B) := by
    have := npow_mono (i := B) hB (a := 1) (b := 2 * B) (by omega)
    rwa [(by rfl : npow B 1 = B * npow B 0), (by rfl : npow B 0 = 1), Nat.mul_one] at this
  calc B * B ≤ B * npow B (2 * B) := Nat.mul_le_mul_left B h1
    _ = npow B (2 * B + 1) := (npow_succ B (2 * B)).symm

-- The **central scalar estimate** at diagonal index j: the alternating diagonal approximant is within
-- 3·(x.seq A)² + 2/(j+1) of 1, for ANY deep index A (A ≥ 24(j+1)). Both lifts follow.
set_option maxHeartbeats 4000000 in
private theorem RaltReal_central {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) (j : Nat) {A : Nat}
    (hAlb : 36 * (j + 1) ≤ A + 1) :
    Qle (Qabs (Qsub (RaltReal_seq x off j) (⟨1, 1⟩ : Q)))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q)) := by
  -- abbreviations and index lower bounds
  have hM2 : 2 ≤ xBound x := by unfold xBound; have := x.den_pos 0; omega
  have hB : 0 < xBound x * xBound x := Nat.mul_pos (by omega) (by omega)
  have hB4 : 4 ≤ xBound x * xBound x := Nat.mul_le_mul hM2 hM2
  -- K_alt ≥ 8·xBound·Cx  and  K_alt ≥ B² (≥ 16)
  have hKmid : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
      ≤ RaltReal_K x := by unfold RaltReal_K; omega
  have hKsq : (xBound x * xBound x) * (xBound x * xBound x) ≤ RaltReal_K x := by
    have h := npow_ge_sq hB; unfold RaltReal_K; omega
  -- R lower bounds : R ≥ 24(j+1)
  have hR_K : 4 * (j + 1) * RaltReal_K x ≤ RaltReal_R x j := by unfold RaltReal_R; omega
  have hR_big : 36 * (j + 1) ≤ RaltReal_R x j := by
    have ha : 4 * (j + 1) * ((xBound x * xBound x) * (xBound x * xBound x))
        ≤ 4 * (j + 1) * RaltReal_K x := Nat.mul_le_mul_left _ hKsq
    have hBB : 16 ≤ (xBound x * xBound x) * (xBound x * xBound x) := Nat.mul_le_mul hB4 hB4
    have hb : 4 * (j + 1) * 16 ≤ 4 * (j + 1) * ((xBound x * xBound x) * (xBound x * xBound x)) :=
      Nat.mul_le_mul_left _ hBB
    omega
  -- expand the diagonal and abstract R
  show Qle (Qabs (Qsub (altSum (x.seq (RaltReal_R x j)) off (RaltReal_R x j)) (⟨1, 1⟩ : Q)))
    (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
  generalize hRdef : RaltReal_R x j = R at hR_big hR_K ⊢
  have hqd : 0 < (x.seq R).den := x.den_pos R
  have had : 0 < (x.seq A).den := x.den_pos A
  -- the clamp:  q' ∈ [−1,1] with |x.seq R − q'| ≤ 2/(R+1)
  have hqU : Qle (x.seq R) (add (⟨1, 1⟩ : Q) (⟨2, R + 1⟩ : Q)) := hx1 R
  have hqL : Qle (neg (⟨1, 1⟩ : Q)) (add (x.seq R) (⟨2, R + 1⟩ : Q)) := hx2 R
  obtain ⟨q', hq'd, hq'1, hq'dist⟩ :
      ∃ q', 0 < q'.den ∧ Qle (Qabs q') (⟨1, 1⟩ : Q) ∧
        Qle (Qabs (Qsub (x.seq R) q')) (⟨2, R + 1⟩ : Q) := by
    by_cases h1 : Qle (x.seq R) (⟨1, 1⟩ : Q)
    · by_cases h2 : Qle (neg (⟨1, 1⟩ : Q)) (x.seq R)
      · -- |q| ≤ 1, q' = q
        refine ⟨x.seq R, hqd, ?_, ?_⟩
        · simp only [Qle, Qabs, neg] at h1 h2 ⊢
          push_cast at h1 h2 ⊢
          rcases Int.natAbs_eq (x.seq R).num with he | he
          · rw [he]; push_cast; omega
          · rw [he]; push_cast; omega
        · have h0 : (Qsub (x.seq R) (x.seq R)).num = 0 := Qsub_self_num _
          simp only [Qle, Qabs, h0]
          simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
          have : (0 : Int) ≤ 2 * (((Qsub (x.seq R) (x.seq R)).den : Nat) : Int) := by
            have := Qsub_den_pos hqd hqd; omega
          omega
      · -- q < −1, clamp to −1
        refine ⟨neg (⟨1, 1⟩ : Q), by decide, by decide, ?_⟩
        -- |q − (−1)| = |q+1| = |(−1) − q| with (−1) − q ≥ 0, and (−1) − q ≤ 2/(R+1) from hqL
        rw [Qabs_Qsub_comm]
        have hnn : 0 ≤ (Qsub (neg (⟨1, 1⟩ : Q)) (x.seq R)).num := by
          simp only [Qle, neg] at h2; simp only [Qsub, add, neg]; push_cast at h2 ⊢; omega
        refine Qabs_le_of_nonneg hnn ?_
        exact Qsub_le_of_le_add hqd (Nat.succ_pos _) hqL
    · -- q > 1, clamp to 1
      refine ⟨(⟨1, 1⟩ : Q), by decide, by decide, ?_⟩
      have hnn : 0 ≤ (Qsub (x.seq R) (⟨1, 1⟩ : Q)).num := by
        simp only [Qle] at h1; simp only [Qsub, add, neg]; push_cast at h1 ⊢; omega
      refine Qabs_le_of_nonneg hnn ?_
      exact Qsub_le_of_le_add (by decide) (Nat.succ_pos _) hqU
  -- bounds  |q| ≤ ⟨xBound,1⟩ and |q'| ≤ ⟨xBound,1⟩  (for altSum_Lip_le with M = xBound)
  have hqM : Qle (Qabs (x.seq R)) (⟨xBound x, 1⟩ : Q) := canon_bound x R
  have hq'M : Qle (Qabs q') (⟨xBound x, 1⟩ : Q) :=
    Qle_trans (by decide) hq'1 (by simp only [Qle]; push_cast; have := hM2; omega)
  -- ============ clamp gap:  |altSum q off R − altSum q' off R| ≤ ⟨1, 2(j+1)⟩ ============
  have hgap : Qle (Qabs (Qsub (altSum (x.seq R) off R) (altSum q' off R))) (⟨1, 2 * (j + 1)⟩ : Q) := by
    have hLS := altSum_Lip_le (M := xBound x) hqd hq'd hqM hq'M off R
    have hCle : Qle (LipS (xBound x * xBound x) R)
        (⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat : Int), 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos _ _) (LipS_le_U (xBound x * xBound x) R)
        (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
    have hbridge := qsq_diff_le (M := xBound x) hqd hq'd hqM hq'M
    have hnqbridge : Qle (Qabs (Qsub (neg (mul (x.seq R) (x.seq R))) (neg (mul q' q'))))
        (mul (⟨(2 * xBound x : Nat), 1⟩ : Q) (⟨2, R + 1⟩ : Q)) :=
      Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos hqd hq'd)))
        hbridge (Qmul_le_mul_left (Int.ofNat_nonneg _) hq'dist)
    refine Qle_trans (Qmul_den_pos (LipS_den_pos _ _)
        (Qabs_den_pos (Qsub_den_pos (Nat.mul_pos hqd hqd) (Nat.mul_pos hq'd hq'd)))) hLS ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos
        (Nat.mul_pos hqd hqd) (Nat.mul_pos hq'd hq'd))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hCle) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos _)))
      (Qmul_le_mul_left (Int.ofNat_nonneg _) hnqbridge) ?_
    show ((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat : Int)
        * (((2 * xBound x : Nat) : Int) * 2) * (2 * (j + 1) : Nat)
        ≤ 1 * (((1 : Nat) * (1 * (R + 1)) : Nat) : Int)
    have harith : (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
        * (2 * xBound x * 2) * (2 * (j + 1)) ≤ 1 * (1 * (1 * (R + 1))) := by
      have he : (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
          * (2 * xBound x * 2) * (2 * (j + 1))
          = 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
            * (j + 1) := by
        have hI : (((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
              * (2 * xBound x * 2) * (2 * (j + 1)) : Nat) : Int)
            = ((8 * xBound x
              * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
                * (j + 1) : Nat) : Int) := by push_cast; ring_uor
        exact_mod_cast hI
      have hfin : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
          * (j + 1) ≤ R + 1 := by
        have h1 : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
            * (j + 1) ≤ RaltReal_K x * (j + 1) := Nat.mul_le_mul_right _ hKmid
        have h2 : RaltReal_K x * (j + 1) ≤ 4 * (j + 1) * RaltReal_K x := by
          have e : 4 * (j + 1) * RaltReal_K x = 4 * (RaltReal_K x * (j + 1)) := by
            rw [Nat.mul_assoc, Nat.mul_comm (j + 1) (RaltReal_K x)]
          rw [e]; exact Nat.le_mul_of_pos_left (RaltReal_K x * (j + 1)) (by decide)
        exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_trans hR_K (Nat.le_succ R))
      rw [he]; omega
    exact_mod_cast harith
  -- ============ altSum_quad at the CLAMP:  |altSum q' off R − 1| ≤ 3·q'² ============
  have hquad : Qle (Qabs (Qsub (altSum q' off R) (⟨1, 1⟩ : Q)))
      (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q)) := by
    have h := altSum_quad (off := off) hq'd hq'1 R; rwa [hoff] at h
  -- ============ product reconciliation ============
  -- |x.seq R − x.seq A| ≤ 2/(36(j+1)) = ⟨1,18(j+1)⟩
  have hn0R : 36 * (j + 1) - 1 ≤ R := by omega
  have hn0A : 36 * (j + 1) - 1 ≤ A := by omega
  have hn0s : (36 * (j + 1) - 1) + 1 = 36 * (j + 1) := by omega
  have hqa : Qle (Qabs (Qsub (x.seq R) (x.seq A))) (⟨1, 18 * (j + 1)⟩ : Q) := by
    have h := xreg_n_le x hn0R hn0A; rw [hn0s] at h
    have hstep : Qle (⟨2, 36 * (j + 1)⟩ : Q) (⟨1, 18 * (j + 1)⟩ : Q) := by
      simp only [Qle]; push_cast; omega
    exact Qle_trans (by show 0 < 36 * (j + 1); omega) h hstep
  -- |q' − x.seq R| ≤ 2/(R+1) ≤ ⟨1,18(j+1)⟩  (since R+1 ≥ 36(j+1))
  have hq'R : Qle (Qabs (Qsub q' (x.seq R))) (⟨1, 18 * (j + 1)⟩ : Q) := by
    rw [Qabs_Qsub_comm]
    refine Qle_trans (Nat.succ_pos _) hq'dist ?_
    have hRi : (36 : Int) * ((j : Int) + 1) ≤ ((R : Nat) : Int) := by exact_mod_cast hR_big
    simp only [Qle]; push_cast
    have : (2 : Int) * (18 * ((j : Int) + 1)) ≤ 1 * (((R : Nat) : Int) + 1) := by omega
    exact this
  -- |q' − x.seq A| ≤ ⟨1,18(j+1)⟩ + ⟨1,18(j+1)⟩ = ⟨1,9(j+1)⟩
  have hq'a : Qle (Qabs (Qsub q' (x.seq A))) (⟨1, 9 * (j + 1)⟩ : Q) := by
    have htri := Qabs_sub_triangle (a := q') (b := x.seq R) (c := x.seq A) hq'd hqd had
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hq'd hqd))
        (Qabs_den_pos (Qsub_den_pos hqd had))) htri ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add hq'R hqa) ?_
    exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)
  -- |x.seq A| ≤ |q'| + |q' − a| ≤ ⟨1,1⟩ + ⟨1,9(j+1)⟩ ≤ ⟨2,1⟩  (no canon_bound; uses tight q' bound)
  have ham : Qle (Qabs (x.seq A)) (⟨2, 1⟩ : Q) := by
    have haq' : Qle (Qabs (Qsub (x.seq A) q')) (⟨1, 9 * (j + 1)⟩ : Q) := by
      rw [Qabs_Qsub_comm]; exact hq'a
    refine Qle_trans (add_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos (Qsub_den_pos had hq'd)))
      (Qabs_le_add hq'd had) ?_
    refine Qle_trans (add_den_pos Nat.one_pos (Nat.succ_pos _)) (Qadd_le_add hq'1 haq') ?_
    simp only [Qle, add]; push_cast; omega
  -- product-Lipschitz : |q'·q' − a·a| ≤ ⟨3,1⟩·|q' − a|
  have hprodL : Qle (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
      (mul (⟨3, 1⟩ : Q) (Qabs (Qsub q' (x.seq A)))) := by
    have hfac : Qeq (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))
        (mul (Qsub q' (x.seq A)) (add q' (x.seq A))) := by
      simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
    have heq1 : Qeq (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
        (mul (Qabs (Qsub q' (x.seq A))) (Qabs (add q' (x.seq A)))) := by
      have h := Qabs_Qeq hfac; rw [Qabs_mul] at h; exact h
    have hsum : Qle (Qabs (add q' (x.seq A))) (⟨3, 1⟩ : Q) := by
      have ha1 : Qle (Qabs (add q' (x.seq A))) (add (Qabs q') (Qabs (x.seq A))) := Qabs_add_le q' _
      have ha2 : Qle (add (Qabs q') (Qabs (x.seq A))) (add (⟨1, 1⟩ : Q) (⟨2, 1⟩ : Q)) :=
        Qadd_le_add hq'1 ham
      have ha3 : Qle (add (⟨1, 1⟩ : Q) (⟨2, 1⟩ : Q)) (⟨3, 1⟩ : Q) := by decide
      exact Qle_trans (add_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos had)) ha1
        (Qle_trans (add_den_pos (by decide) (by decide)) ha2 ha3)
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hq'd had))
        (Qabs_den_pos (add_den_pos hq'd had)))
      (Qeq_le heq1) ?_
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hq'd had)) (by decide))
      (Qmul_le_mul_left (Qabs_num_nonneg _) hsum) (Qeq_le (mul_comm _ _))
  -- 3·|q'²−a²| ≤ 3·(3·⟨1,9(j+1)⟩) = ⟨1,j+1⟩
  have hprod3 : Qle (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))))
      (⟨1, j + 1⟩ : Q) := by
    have h1 : Qle (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
        (mul (⟨3, 1⟩ : Q) (⟨1, 9 * (j + 1)⟩ : Q)) :=
      Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos hq'd had)))
        hprodL (Qmul_le_mul_left (by decide) hq'a)
    have h2 : Qle (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))))
        (mul (⟨3, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (⟨1, 9 * (j + 1)⟩ : Q))) :=
      Qmul_le_mul_left (by decide) h1
    refine Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (by decide) (Nat.succ_pos _)))
      h2 (Qeq_le ?_)
    simp only [Qeq, mul]; push_cast; ring_uor
  -- ============ ASSEMBLE ============
  have htri := Qabs_sub_triangle (a := altSum (x.seq R) off R) (b := altSum q' off R)
    (c := (⟨1, 1⟩ : Q)) (altSum_den_pos hqd off R) (altSum_den_pos hq'd off R) (by decide)
  have hstep1 : Qle (Qabs (Qsub (altSum (x.seq R) off R) (⟨1, 1⟩ : Q)))
      (add (⟨1, 2 * (j + 1)⟩ : Q) (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q))) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off R)
        (altSum_den_pos hq'd off R)))
        (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hq'd off R) (by decide)))) htri
      (Qle_trans (add_den_pos (Nat.succ_pos _)
        (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos hq'd)) (by decide)))
        (Qadd_le_add hgap hquad) (Qle_refl _))
  -- mul (mul |q'| |q'|) ⟨3,1⟩ ≈ mul ⟨3,1⟩ (mul q' q')   (|q'|²=q'²)
  have hsqval : Qeq (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q)) (mul (⟨3, 1⟩ : Q) (mul q' q')) := by
    have hge : Qeq (mul (Qabs q') (Qabs q')) (mul q' q') := by
      have hnum : (q'.num.natAbs : Int) * (q'.num.natAbs : Int) = q'.num * q'.num := by
        have := Int.natAbs_mul_self (a := q'.num); push_cast at this; omega
      simp only [Qeq, mul, Qabs]; push_cast; rw [hnum]
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hq'd hq'd) (by decide))
      (Qmul_congr hge (Qeq_refl _)) ?_
    simp only [Qeq, mul]; push_cast; ring_uor
  -- 3·q'·q' ≤ 3·a·a + ⟨1,j+1⟩  (signed, from hprod3 via value-eq rearrangement)
  have h3le : Qle (mul (⟨3, 1⟩ : Q) (mul q' q'))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨1, j + 1⟩ : Q)) := by
    have hdiff : Qle (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q')) (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
        (⟨1, j + 1⟩ : Q) := by
      have hle : Qle (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q'))
            (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
          (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))) := by
        have he : Qeq (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q'))
              (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
            (mul (⟨3, 1⟩ : Q) (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))) := by
          simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
        refine Qle_trans (Qmul_den_pos (by decide) (Qsub_den_pos (Qmul_den_pos hq'd hq'd)
          (Qmul_den_pos had had))) (Qeq_le he) ?_
        exact Qmul_le_mul_left (by decide) (Qle_self_Qabs _)
      exact Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hq'd hq'd)
        (Qmul_den_pos had had)))) hle hprod3
    -- 3q'² = 3a² + (3q'² − 3a²) ≤ 3a² + ⟨1,j+1⟩
    have hval : Qeq (mul (⟨3, 1⟩ : Q) (mul q' q'))
        (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))
          (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q')) (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))) := by
      simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
    refine Qle_trans (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos had had))
        (Qsub_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos hq'd hq'd))
          (Qmul_den_pos (by decide) (Qmul_den_pos had had)))) (Qeq_le hval) ?_
    exact Qadd_le_add (Qle_refl _) hdiff
  have hRHSbound : Qle (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨1, j + 1⟩ : Q)) :=
    Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos hq'd hq'd))
      (Qeq_le hsqval) h3le
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hq'd)
    (Qabs_den_pos hq'd)) (by decide))) hstep1 ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (add_den_pos (Qmul_den_pos (by decide)
    (Qmul_den_pos had had)) (Nat.succ_pos _))) (Qadd_le_add (Qle_refl _) hRHSbound) ?_
  -- ⟨1,2(j+1)⟩ + (3a² + ⟨1,j+1⟩) = 3a² + (⟨1,2(j+1)⟩+⟨1,j+1⟩) ≤ 3a² + ⟨2,j+1⟩
  refine Qle_trans (b := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))
      (add (⟨1, 2 * (j + 1)⟩ : Q) (⟨1, j + 1⟩ : Q)))
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos had had))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor)) ?_
  refine Qadd_le_add (Qle_refl _) ?_
  -- 1/(2(j+1)) + 1/(j+1) = 3/(2(j+1)) ≤ 2/(j+1)
  simp only [Qle, add]; push_cast
  -- goal reduces to  3·(j+1)² ≤ 4·(j+1)²  with the product as an atom
  have key : (1 * ((j : Int) + 1) + 1 * (2 * ((j : Int) + 1))) * ((j : Int) + 1)
      = 3 * (((j : Int) + 1) * ((j : Int) + 1)) := by ring_uor
  have key2 : 2 * (2 * ((j : Int) + 1) * ((j : Int) + 1))
      = 4 * (((j : Int) + 1) * ((j : Int) + 1)) := by ring_uor
  rw [key, key2]
  have hsq : (0 : Int) ≤ ((j : Int) + 1) * ((j : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
  omega

-- the deep product index A = Ridx x x (Ridx (ofQ⟨3,1⟩) (Rmul x x) (2j+1)) satisfies A+1 ≥ 36(j+1).
private theorem prodIdx_lb (x : Real) (j : Nat) :
    36 * (j + 1) ≤ Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) + 1 := by
  have hM2 : 2 ≤ xBound x := by unfold xBound; have := x.den_pos 0; omega
  have hKxx : 2 ≤ RmulK x x := by unfold RmulK; omega
  have hKo : 5 ≤ RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) := by
    have hxo : xBound (ofQ (⟨3, 1⟩ : Q) (by decide)) = 5 := rfl
    have := Nat.le_max_left (xBound (ofQ (⟨3, 1⟩ : Q) (by decide))) (xBound (Rmul x x))
    unfold RmulK; omega
  rw [Ridx_succ x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))]
  rw [Ridx_succ (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)]
  -- A+1 = 2·K(x,x)·(2·K'·(2j+2)) ≥ 2·2·(2·5·(2(j+1))) = 80(j+1)
  have h1 : 2 * 5 * (2 * j + 1 + 1) ≤ 2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKo)
  have h2 : 2 * 2 * (2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1))
      ≤ 2 * RmulK x x * (2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1)) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKxx)
  -- 2·2·(2·5·(2j+2)) = 80(j+1)
  omega

theorem RaltReal_upper_le {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (RaltReal x off) (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) := by
  intro j
  have hA := prodIdx_lb x j
  -- (RaltReal x off).seq j = RaltReal_seq x off j ;  RHS.seq j = add ⟨1,1⟩ (mul ⟨3,1⟩ (a·a))
  show Qle (RaltReal_seq x off j)
    (add (add (⟨1, 1⟩ : Q)
      (mul (⟨3, 1⟩ : Q) (mul (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))
        (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))))) (⟨2, j + 1⟩ : Q))
  generalize hAdef : Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) = A
    at hA ⊢
  have hcent := RaltReal_central hoff hx1 hx2 j hA
  -- from |RaltReal_seq − 1| ≤ 3a² + ⟨2,j+1⟩  get  RaltReal_seq ≤ 1 + (3a² + ⟨2,j+1⟩)
  have h := Qle_add_of_Qabs_sub
    (a := RaltReal_seq x off j) (b := (⟨1, 1⟩ : Q))
    (c := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
    (altSum_den_pos (x.den_pos _) off _) (by decide)
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos _) (x.den_pos _)))
      (Nat.succ_pos _)) hcent
  refine Qle_trans (add_den_pos (by decide)
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos _) (x.den_pos _)))
      (Nat.succ_pos _))) h (Qeq_le ?_)
  simp only [Qeq, add, mul]; push_cast; ring_uor

theorem RaltReal_lower_ge {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (RaltReal x off) := by
  intro j
  have hA := prodIdx_lb x j
  -- LHS.seq j = Qsub ⟨1,1⟩ (mul ⟨3,1⟩ (a·a)) ;  RHS.seq j = RaltReal_seq x off j
  show Qle (add (⟨1, 1⟩ : Q)
      (neg (mul (⟨3, 1⟩ : Q) (mul (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))
        (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))))))
    (add (RaltReal_seq x off j) (⟨2, j + 1⟩ : Q))
  generalize hAdef : Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) = A
    at hA ⊢
  have hcent := RaltReal_central hoff hx1 hx2 j hA
  have hRd : 0 < (RaltReal_seq x off j).den := (RaltReal x off).den_pos j
  -- from |RaltReal_seq − 1| ≤ 3a² + ⟨2,j+1⟩  get  1 − 3a² ≤ RaltReal_seq + ⟨2,j+1⟩
  -- i.e.  1 ≤ RaltReal_seq + (3a² + ⟨2,j+1⟩)  via the OTHER side of the abs.
  have hsub : Qle (Qabs (Qsub (⟨1, 1⟩ : Q) (RaltReal_seq x off j)))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q)) := by
    rw [Qabs_Qsub_comm]; exact hcent
  have h := Qle_add_of_Qabs_sub
    (a := (⟨1, 1⟩ : Q)) (b := RaltReal_seq x off j)
    (c := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
    (by decide) hRd
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))
      (Nat.succ_pos _)) hsub
  -- h : 1 ≤ RaltReal_seq + (3a² + ⟨2,j+1⟩).  Add (neg 3a²) to both, cancel.
  have hstep := Qadd_le_add h (Qle_refl (neg (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))))
  -- hstep : add ⟨1,1⟩ (neg 3a²) ≤ add (add RaltReal (add 3a² ⟨2,j+1⟩)) (neg 3a²)
  --        and the RHS cancels to add RaltReal ⟨2,j+1⟩.
  exact Qle_congr_right (add_den_pos (add_den_pos hRd
      (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))
        (Nat.succ_pos _)))
      (neg_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))))
    (by simp only [Qeq, add, mul, neg]; push_cast; ring_uor) hstep

-- GOAL 3 (corollaries):
-- cos:  1 − cos x ≤ 3x²   (for x ∈ [−1,1])
theorem Rcos_one_sub_le_sq {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rcos x)) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x)) := by
  -- from  1 − 3x² ≤ cos x   get   1 ≤ 3x² + cos x   get   1 − cos x ≤ 3x²
  have hG : Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (Rcos x) :=
    RaltReal_lower_ge (by decide : fct 0 = 1) hx1 hx2
  exact Rsub_le_of_le_add' (Rle_add_of_Rsub_le' hG)

-- sin amplitude:  RsinAux x ≤ 1 + 3x²   and   1 − 3x² ≤ RsinAux x   (for x ∈ [−1,1])
theorem RsinAux_upper_le {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (RsinAux x) (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) := by
  unfold RsinAux
  exact RaltReal_upper_le (by decide) hx1 hx2

theorem RsinAux_lower_ge {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (RsinAux x) := by
  unfold RsinAux
  exact RaltReal_lower_ge (by decide) hx1 hx2

end UOR.Bridge.F1Square.Analysis
