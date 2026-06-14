/-
F1 square — v0.20.0 stage F: **the certified bracket `γ₂ ≥ −0.02`** via DISCRETE Euler–Maclaurin
(NO constructive integration), tying off `Pos λ₃`.

`γ₂ = g2Seq(N) + tail`, and the trapezoidal anchor `½f(N)` (`f(x)=ln²x/x`) captures the leading tail
`½ln²N/N`, leaving the summable trapezoidal residual `s_p = O(ln²p/p³)`. So
`γ₂ ≥ g2Seq(N) − ½ln²N/N − ε`, certifiable at `N = 200` with the rational squared/cubed-log evaluators.

THIS FILE — part (A): the squared-log lower-bound evaluator `lnSqSumLo` (a rational lower bound for
`Σ_{k≤N}(ln k)²/k`, the `GammaOne.lnSumBound` analogue, lower side, via `logLowBound` squared and
round-down) and the cubed/squared-log upper bounds (`logCube`/`logN²` via `logBound`). Parts (B)/(C)
(the `½ln²N/N` bound and the trapezoidal residual) and the final assembly follow.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaTwo

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

-- ===========================================================================
-- (A) `lnSqSumLo` — a rational LOWER bound for `lnSqSum N = Σ_{k=1}^N (ln k)²/k`.
-- ===========================================================================

/-- The accumulated rational lower bound for `Σ_{k=1}^N (ln k)²/k`, at fixed denominator `D`: each new
    term `(log(n+1))²/(n+1) ≥ (logLowBound n)²·(1/(n+1))`, then round DOWN. -/
def lnSqSumLo (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (n + 1) =>
      qRoundDown (add (lnSqSumLo T D n)
        (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩)) D

theorem lnSqSumLo_den_pos (T D : Nat) (hD : 0 < D) : ∀ N, 0 < (lnSqSumLo T D N).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`ofQ(lnSqSumLo T D N) ≤ lnSqSum N`** — the partial sum `Σ (log k)²/k` bounded BELOW term-by-term
    via `logN_ge_logLowBound` (squared monotonically, both sides nonneg), accumulated at denominator
    `D` (round down), artanh depth `T ≤ 21`. -/
theorem lnSqSumLo_le (T D : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    ∀ N, Rle (ofQ (lnSqSumLo T D N) (lnSqSumLo_den_pos T D hD N)) (lnSqSum N) := by
  intro N
  induction N with
  | zero =>
    have h0 : Req (ofQ (lnSqSumLo T D 0) (lnSqSumLo_den_pos T D hD 0)) zero :=
      Req_of_seq_Qeq (fun n => by show Qeq (⟨0, D⟩ : Q) ⟨0, 1⟩; simp only [Qeq]; push_cast; ring_uor)
    exact Rle_of_Req h0
  | succ n ih =>
    have hLLd := logLowBound_den_pos T D hD n
    have hLLnn : Rnonneg (ofQ (logLowBound T D n) hLLd) :=
      Rnonneg_ofQ hLLd (logLowBound_num_nonneg T D n)
    have hlow := logN_ge_logLowBound T D hD hT n
    have hlognn : Rnonneg (logN (n + 1) (Nat.succ_pos n)) := Rnonneg_logN _ _
    -- per-term lower bound `(LL)²·(1/(n+1)) ≤ (log(n+1))²·(1/(n+1)) = lnSqOver (n+1)`
    have hsq : Rle (Rmul (ofQ (logLowBound T D n) hLLd) (ofQ (logLowBound T D n) hLLd))
        (Rmul (logN (n + 1) (Nat.succ_pos n)) (logN (n + 1) (Nat.succ_pos n))) :=
      Rle_trans (Rmul_le_Rmul_right hLLnn hlow) (Rmul_le_Rmul_left hlognn hlow)
    have hmuld : 0 < (mul (mul (logLowBound T D n) (logLowBound T D n)) (⟨1, n + 1⟩ : Q)).den :=
      Qmul_den_pos (Qmul_den_pos hLLd hLLd) (Nat.succ_pos n)
    have hsqd : 0 < (mul (logLowBound T D n) (logLowBound T D n)).den := Qmul_den_pos hLLd hLLd
    have hterm : Rle (ofQ (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩) hmuld)
        (lnSqOver (n + 1) (Nat.succ_pos n)) := by
      -- ofQ(LL²·(1/(n+1))) ≈ (ofQ LL·ofQ LL)·ofQ(1/(n+1)) ≤ (log²)·(1/(n+1)) = lnSqOver
      refine Rle_trans (Rle_of_Req ?_)
        (Rmul_le_Rmul_right (Rnonneg_ofQ (Nat.succ_pos n) (by show (0 : Int) ≤ 1; decide)) hsq)
      refine Req_trans (Req_symm (Rmul_ofQ_ofQ hsqd (Nat.succ_pos n))) ?_
      exact Rmul_congr (Req_symm (Rmul_ofQ_ofQ hLLd hLLd)) (Req_refl _)
    -- accumulate: ofQ(round-down(prev + term)) ≤ prev + term ≤ lnSqSum n + lnSqOver(n+1)
    refine Rle_trans (Rle_ofQ_ofQ (lnSqSumLo_den_pos T D hD (n + 1))
      (add_den_pos (lnSqSumLo_den_pos T D hD n) hmuld)
      (qRoundDown_le (add (lnSqSumLo T D n)
        (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩))
        (add_den_pos (lnSqSumLo_den_pos T D hD n) hmuld) D)) ?_
    refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ (lnSqSumLo_den_pos T D hD n) hmuld)) ?_
    exact Radd_le_add ih hterm

-- ===========================================================================
-- (B) Cubed/squared-log UPPER bounds (`logBound`).
-- ===========================================================================

/-- `Rnonneg (ofQ (logBound T D M))` — the upper log bound is `≥ log(M+1) ≥ 0`. -/
theorem logBound_ofQ_nonneg (T D M : Nat) (hD : 0 < D) :
    Rnonneg (ofQ (logBound T D M) (logBound_den_pos T D hD M)) :=
  Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_logN (M + 1) (Nat.succ_pos M)))
    (logN_le_logBound T D hD M))

/-- `log(M+1)² ≤ logBound²` (squared monotonicity, both sides nonneg). -/
theorem logNsq_le (T D M : Nat) (hD : 0 < D) :
    Rle (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
        (Rmul (ofQ (logBound T D M) (logBound_den_pos T D hD M))
              (ofQ (logBound T D M) (logBound_den_pos T D hD M))) :=
  Rle_trans (Rmul_le_Rmul_right (Rnonneg_logN _ _) (logN_le_logBound T D hD M))
    (Rmul_le_Rmul_left (logBound_ofQ_nonneg T D M hD) (logN_le_logBound T D hD M))

/-- **Cubed-log upper bound** `(ln(M+1))³ ≤ logBound³` (`logCube`). -/
theorem logCube_le (T D M : Nat) (hD : 0 < D) :
    Rle (logCube (M + 1) (Nat.succ_pos M))
        (ofQ (mul (mul (logBound T D M) (logBound T D M)) (logBound T D M))
          (Qmul_den_pos (Qmul_den_pos (logBound_den_pos T D hD M) (logBound_den_pos T D hD M))
            (logBound_den_pos T D hD M))) := by
  have LBd := logBound_den_pos T D hD M
  have hLBsqnn : Rnonneg (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd)) :=
    Rnonneg_Rmul (logBound_ofQ_nonneg T D M hD) (logBound_ofQ_nonneg T D M hD)
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_logN _ _) (logNsq_le T D M hD)) ?_
  refine Rle_trans (Rmul_le_Rmul_left hLBsqnn (logN_le_logBound T D hD M)) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LBd LBd) (Req_refl _))
    (Rmul_ofQ_ofQ (Qmul_den_pos LBd LBd) LBd))

/-- **Half-squared-over-`N` upper bound** `½·(ln(M+1))²/(M+1) ≤ ½·logBound²/(M+1)` — the trapezoidal
    anchor `½f(M+1)`, `f(x) = ln²x/x`, bounded above. -/
theorem halfSqOver_le (T D M : Nat) (hD : 0 < D) :
    Rle (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
          (Rmul (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
            (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M))))
        (ofQ (mul (⟨1, 2⟩ : Q) (mul (mul (logBound T D M) (logBound T D M)) ⟨1, M + 1⟩))
          (Qmul_den_pos (by decide) (Qmul_den_pos
            (Qmul_den_pos (logBound_den_pos T D hD M) (logBound_den_pos T D hD M)) (Nat.succ_pos M)))) := by
  have LBd := logBound_den_pos T D hD M
  have hovnn : Rnonneg (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)) :=
    Rnonneg_ofQ (Nat.succ_pos M) (by show (0 : Int) ≤ 1; decide)
  have hinner : Rle (Rmul (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)))
      (Rmul (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M))) :=
    Rmul_le_Rmul_right hovnn (logNsq_le T D M hD)
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 1; decide)) hinner) ?_
  -- ½·((LB·LB)·(1/(M+1)))  ≈  ofQ(½·((logBound·logBound)·(1/(M+1))))
  have hinnerEq : Req (Rmul (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)))
      (ofQ (mul (mul (logBound T D M) (logBound T D M)) ⟨1, M + 1⟩)
        (Qmul_den_pos (Qmul_den_pos LBd LBd) (Nat.succ_pos M))) :=
    Req_trans (Rmul_congr (Rmul_ofQ_ofQ LBd LBd) (Req_refl _))
      (Rmul_ofQ_ofQ (Qmul_den_pos LBd LBd) (Nat.succ_pos M))
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) hinnerEq)
    (Rmul_ofQ_ofQ (by decide) (Qmul_den_pos (Qmul_den_pos LBd LBd) (Nat.succ_pos M))))

end UOR.Bridge.F1Square.Analysis
