-- F1 square intersection theory — UOR Foundation individual constants.
--
-- Formalization of `Spec ℤ ×_𝔽₁ Spec ℤ` and its intersection theory, in the UOR ontology
-- idiom. Companion to the development in `f1_square_intersection_theory.md`.
-- PRECISION (v0.17.0): what is constructed canonically is the MONOID-LEVEL tensor
-- `F ⊗_𝔽₁ F` (Deitmar 𝔽₁-algebras = commutative monoids; coproduct with universal
-- property proved, `Square/Tensor.lean`), whose tropicalization carries the §2.3 pencil.
-- The SEMIRING-level tensor `F ⊗_𝔹 F` over the Boolean semiring (the concrete description
-- Sagnier, arXiv 1703.10521, reports open) is the finer object; its concrete
-- intersection-theoretic description remains open and is NOT claimed here.
--
-- EPISTEMIC CONVENTION (matching this library, e.g. Bridge.Homology.boundarySquaredZero):
--   `universallyValid := some true`  ⇒ asserted established (verified / classical theorem)
--   `universallyValid := none`       ⇒ NOT asserted proven in this encoding (open / conditional)
-- The open crux (Hodge index = RH) is encoded with `none`, never `some true`. Results we
-- verified in the runtime (template signature, ample class, parallel-pencil structure) carry
-- their established status; the crux does not. No field asserts an unproven claim as true.

import UOR.Structures
import UOR.Individuals.Op
import UOR.Individuals.Schema
import UOR.Individuals.Convergence
import UOR.Individuals.Division
import UOR.Individuals.Homology

-- The genuine Lean proof layer (real theorems, no Mathlib, no `sorry`): proves the
-- [VERIFIED] / [CLASSICAL] boundary facts of the program. The crux (= RH) is never proved there.
import F1Square.Mechanism
import F1Square.Template
import F1Square.CharOne
import F1Square.Bridge
import F1Square.BridgeFF
import F1Square.CycleCounts
import F1Square.Crux
import F1Square.Square.Monoid
import F1Square.Square.Tensor
import F1Square.Square.Divisors
import F1Square.Square.Pencil
import F1Square.Square.Lattice
import F1Square.Square.Polarized
import F1Square.Square.Spectral
import F1Square.Tropical.Closure
import F1Square.Tropical.Signature
import F1Square.Tropical.Spectrum
import F1Square.Tropical.Siblings
import F1Square.Analysis.Rat
import F1Square.Analysis.RingNF
import F1Square.Analysis.RingTac
import F1Square.Analysis.QOrder
import F1Square.Analysis.Real
import F1Square.Analysis.Complex
import F1Square.Analysis.Complete
import F1Square.Analysis.Exp
import F1Square.Analysis.ExpGen
import F1Square.Analysis.ExactBounded
import F1Square.Analysis.Zeta
import F1Square.Analysis.ROrder
import F1Square.Analysis.Pow
import F1Square.Analysis.Inv
import F1Square.Analysis.RealDiv
import F1Square.Analysis.ExpReal
import F1Square.Analysis.ExpRealAdd
import F1Square.Analysis.CosSin
import F1Square.Analysis.Log
import F1Square.Analysis.Arctan
import F1Square.Analysis.Pi
import F1Square.Analysis.Euler
import F1Square.Analysis.GammaAccel
import F1Square.Analysis.GammaUpper
import F1Square.Analysis.LambdaOne
import F1Square.Analysis.Binomial
import F1Square.Analysis.Bernoulli
import F1Square.Analysis.BernoulliPoly
import F1Square.Analysis.ExpAdd
import F1Square.Analysis.CosSinAdd
import F1Square.Analysis.CosSinAddFormula
import F1Square.Analysis.CosSinBound
import F1Square.Analysis.ComplexExp
import F1Square.Analysis.ComplexExpAdd
import F1Square.Analysis.ComplexMod
import F1Square.Analysis.ComplexPow
import F1Square.Analysis.ExpLog
import F1Square.Analysis.RealPow
import F1Square.Analysis.ComplexZeta
import F1Square.Analysis.Mangoldt
import F1Square.Li
import F1Square.Analysis.LiOne
import F1Square.Analysis.ZetaTwo
import F1Square.Analysis.GammaOne
import F1Square.Analysis.LambdaTwo
import F1Square.Analysis.LiTwo
import F1Square.Analysis.ComplexInv
import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.EtaFunction
import F1Square.Analysis.EtaVariation
import F1Square.Analysis.CriticalZeta
import F1Square.Analysis.Gamma

open UOR.Primitives

namespace UOR.Bridge.F1Square

-- ===========================================================================
-- §0/§9. The base and the curve (boundary conditions — established/classical).
-- The square's 1-dimensional factor is the Connes–Consani arithmetic-site curve,
-- whose convergence-tower foundation (R→C→H→O) is already in the library
-- (UOR.Kernel.Convergence). The base semiring is characteristic-1 (idempotent).
-- These are carried as references, not re-asserted here.
-- ===========================================================================

-- §2.2 / T3. The intersection-pairing TEMPLATE (product-of-curves form).
-- Established as a CLASSICAL theorem (Hodge index for a projective surface) and
-- verified in the runtime on the sourced form {E₁,E₂,E₃}, E₃²=−2, signature (1,ρ−1).
-- Status: established as a TEMPLATE the concrete square must match (universally valid
-- as a statement about product surfaces over a field).
def intersectionTemplate : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .topological]
  verifiedAtLevel := #[]
  universallyValid := some (true)   -- Hodge index IS a theorem for product surfaces over a field
  validityKind := some (.universal)
  validKMin := none
  validKMax := none
}

-- §1.4. The AMPLE class (projectivity/Kähler precondition).
-- Resolved on the template (runtime-verified, gated): H = E₁+E₂ has H²=2>0, positive
-- cone has two components, form negative-definite on H^⊥. NON-automatic per the tropical
-- literature, hence a genuine result — but established ON THE TEMPLATE, not on the concrete
-- square. Status: established on the template (geometric/algebraic).
def ampleClassOnTemplate : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .geometric]
  verifiedAtLevel := #[]
  universallyValid := some (true)   -- verified: a class of positive self-intersection exists on the template
  validityKind := some (.universal)
  validKMin := none
  validKMax := none
}

-- §2.3. The concrete square F ⊗_𝔽₁ F: the parallel-pencil structural finding.
-- v0.17.0: DERIVED ON CANONICAL 𝕊, no longer a candidate-model observation. On the
-- constructed square (Square/Tensor.lean, universal property proved) the Frobenius
-- correspondences Γ_n = {(m, n·m)} are the flow translates of the diagonal
-- (Square.graph_translate_diag), have NO transverse fixed points
-- (Square.diag_inter_graph_empty), are pairwise disjoint (Square.graph_disjoint), run at
-- log-slope 1 — direction (1,1), stable count Δ·Γ_n = |det((1,1),(1,1))| = 0
-- (Square.pencil_parallel, Square.pencil_det_zero) — and sit at the constant separation
-- log n (Square.pencil_separation), which at a prime is the explicit-formula weight
-- Λ(p) = log p (Square.pencil_separation_vonMangoldt) and at pᵏ is k·log p
-- (Square.pencil_separation_pow). The arithmetic content provably relocates to the shift
-- lengths. Status: established on canonical 𝕊 (theorems, axiom-clean).
def parallelPencilStructure : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.topological, .geometric]
  verifiedAtLevel := #[]
  universallyValid := some (true)    -- derived on canonical 𝕊 (v0.17.0), no longer candidate-only
  validityKind := some (.universal)
  validKMin := none
  validKMax := none
}

-- §2.3 / §1.5. The shift-length positivity, and its identification with RH.
-- The Weil-type Gram on the pencil, W_ij = Σ_zeros cos(γ·(log p_i − log p_j)), is PSD — but
-- a control shows this PSD-ness holds for ANY real spectral parameters γ, so the positivity
-- is EQUIVALENT to the γ being real (zeros on the critical line) = RH. Hence the shift-length
-- positivity is RH, reached from the tropical direction — NOT a route around it.
-- Status: the positivity is RH. OPEN. Encoded with `none` (the crux), never `some true`.
def shiftLengthPositivity : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.analytical, .topological]
  verifiedAtLevel := #[]
  universallyValid := none           -- this positivity IS RH — OPEN, not asserted
  validityKind := none
  validKMin := none
  validKMax := none
}

-- §1.5 / T5. THE CRUX: the Hodge index theorem for 𝕊 (signature (1, ρ−1) on the concrete
-- square), whose negative-definiteness on the primitive complement forces the zeros onto
-- Re(s)=1/2. This is the Riemann Hypothesis. It is established locally/semilocally (Weil
-- positivity at the archimedean place, Connes–Consani) but NOT globally.
-- Status: OPEN — this is RH. universallyValid := none, validityKind := none. Never asserted.
-- (Mirrors the library's own convention: Bridge.Homology.indexBridge carries none.)
def hodgeIndexCrux : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .topological, .analytical]
  verifiedAtLevel := #[]
  universallyValid := none           -- = RH. OPEN. The crux is never asserted true.
  validityKind := none
  validKMin := none
  validKMax := none
}

-- ===========================================================================
-- The convergence-tower link: the square's curve factor sits at the F₁/tropical
-- base below the division-algebra tower. The tower TERMINATES at O (dim 8); the
-- next Cayley–Dickson step (sedenions, dim 16) is where division fails — the
-- "no normed division algebra of dim 16" boundary (Op.DA_4). Our sedenion
-- zero-divisor generator (XOR-class, e_8 exempt) characterizes exactly that
-- residual. These library objects are referenced, not re-asserted:
--   UOR.Kernel.Convergence.L3_Self        (O, dim 8 — top of the tower)
--   UOR.Kernel.Division.cayleyDickson_H_to_O  (the last division-preserving doubling)
--   UOR.Kernel.Op.DA_4                    (Adams/Hurwitz: no dim-16 division algebra)
-- ===========================================================================

-- A roll-up record of the construction's status, for the unproven-manifest layer.
-- Every field reflects the HONEST verified status; the crux fields are `none`.
structure F1SquareStatus where
  surfaceConstructed        : Option Bool   -- §1.1 / T1: canonical 𝕊 at the monoid-scheme level (v0.17.0)
  classGroupFinitelyGen     : Option Bool   -- §1.2 / T2: true on canonical 𝕊 (Square.cls_generated)
  intersectionTemplateValid : Option Bool   -- §2.2 / T3: true — derived intrinsically on 𝕊
  ampleClassExists          : Option Bool   -- §1.4: true on canonical 𝕊 (Square.sq_ample_pos)
  parallelPencilFinding     : Option Bool   -- §2.3: derived on canonical 𝕊 (v0.17.0)
  hodgeIndexHolds           : Option Bool   -- §1.5 / T5: NONE — this is RH (geometric face)
  liPositivityHolds         : Option Bool   -- Li's criterion: NONE — this is RH (analytic face)
  deriving Repr

def f1SquareStatus : F1SquareStatus := {
  surfaceConstructed        := some true      -- canonical 𝕊 = F ⊗_𝔽₁ F at the monoid-scheme level:
                                              -- the coproduct with its universal property PROVED
                                              -- (Square.copair_unique), strictly 2-dimensional
                                              -- (Square.gen2_injective), projections recover the curve.
                                              -- HONEST SCOPE: the T1/T2/T3 layers; the H¹-bearing
                                              -- spectral enrichment (T4/T5) is NOT constructed.
  classGroupFinitelyGen     := some true      -- on canonical 𝕊: free of rank 3 on the derived basis
                                              -- {V,H,E₃}; all distinguished classes inside
                                              -- (Square.cls_generated, Square.clsDiag_in_lattice)
  intersectionTemplateValid := some true      -- the sourced template EMERGES from point counts on 𝕊
                                              -- (Square.sqPair_eq_template; e3_sq_forced) — T3's
                                              -- intrinsic realization, no longer only the analogy
  ampleClassExists          := some true      -- on canonical 𝕊: H = [V]+[H], H² = 2 > 0, H^⊥
                                              -- negative-definite (Square.sq_ample_pos, sq_hperp_*)
  parallelPencilFinding     := some true      -- derived on canonical 𝕊 (Square/Pencil.lean): no
                                              -- transverse fixed points; separation log n = Λ-weights
  hodgeIndexHolds           := none           -- = RH (geometric face), OPEN, never asserted. NOTE:
                                              -- the COARSE-LATTICE Hodge index on 𝕊 is proven
                                              -- (Square.square_hodgeIndex) but PENCIL-BLIND
                                              -- (Square.square_hodge_pencil_blind: Δ·Γ_n = 0,
                                              -- [Γ_n] = [Δ] ∀n — no spectral input), hence NOT the
                                              -- crux; the crux is the H¹-bearing pairing's positivity.
  liPositivityHolds         := none           -- = RH (analytic face: λₙ > 0 ∀n, Li 1997), OPEN, never asserted
}

-- ===========================================================================
-- Proof-layer backing (P1–P6). The established (`some true`) fields above are discharged by
-- GENUINE Lean theorems in the proof layer (`F1Square/*.lean`), each audited axiom-clean
-- (no `sorry` / `native_decide` / stray axiom) by `scripts/honesty_audit.sh`:
--   intersectionTemplateValid ← Template.{E1_dot_E2, E3_sq, pair_symm}                 (P1, §2.2)
--   ampleClassExists          ← Template.{H_sq_pos, Hperp_neg_semidef, Hperp_definite} (P1, §1.4)
--   the Hodge/Hasse flip      ← Mechanism.{hodgeType_iff, hasse_q4/q9/q25_*}           (P1, §0.3/§9.1)
--   tropical positivity (R13) ← Mechanism.{tropMult_nonneg, bezout_line_line/conic}    (P2)
--   characteristic 1 (R1,R12) ← CharOne.{tAdd_idem, cycle_reversal_invariant}          (P2)
--   trace counts (R6)         ← CycleCounts.{N1 … N8}  (exact `Bᵐ`)                    (P3b)
--   mechanism + §2.3 control  ← Bridge.{hodge_implies_spectral_bound, control_psd}     (P3)
-- v0.2.0 (finite tropical stack + first analysis brick):
--   tropical Kleene/κ/spectrum ← Tropical.{R2_kleene_idempotent, R3_kappa_perm_invariant,
--                                R4_cycle_spectrum, R9_same_kappa, R10_diff_spectrum, R11_kappa_fiber}
--   sibling carriers (R14–R16) ← Tropical.{R14_kappaBool_perm_invariant, R15_faceted_address,
--                                R16_boolean_facet_degenerate}
--   tropical Hodge signatures ← Tropical.Signature.{parallel_pencil, fan_degenerate, fan_kernel,
--                                bh_two_positive_dirs}
--   exact ℚ analysis brick    ← Analysis.{reduce_6_8, reduce_idem, same_address_iff_eq}
-- v0.3.0 (the analysis substrate: a ℤ ring normalizer + constructive ℝ):
--   ℤ ring normalizer (the    ← Analysis.RingNF.{norm_sound, nf_eq, sq_add, mul_diff, sq_add3} —
--     no-`ring` ceiling lifted)  a reflective canonical polynomial form; soundness ⇒ general identities
--   general ℚ field laws       ← Analysis.{add_comm, mul_comm, mul_assoc, add_assoc, mul_add, add_neg}
--                                (now for ALL rationals, via the normalizer — not just v0.2.0 numerals)
--   constructive ℝ (Bishop)    ← Analysis.{const_regular, Req_refl, Req_symm, ofQ_respects, Pos_half}
-- v0.4.0 (a from-scratch `ring` tactic; ℚ ordered field; ℝ as an ordered additive group):
--   ring_uor (the no-Mathlib    ← Analysis.RingNF.{ring_uor_sq, ring_uor_cube, ring_uor_telescope} —
--     `ring`, built on nf_eq)     a reflective decision procedure: reify → nf_eq → decide
--   ℚ ordered field            ← Analysis.{Qle_trans, Qadd_le_add, Qabs_add_le, Qabs_sub_add4, Qeq_le}
--   ℝ arithmetic (regular)     ← Analysis.{Rneg, Radd} (negation + Bishop addition, regularity proved)
-- v0.5.0 (ℝ's Bishop equality is an equivalence; ℝ multiplication; ℂ = ℝ×ℝ with all four operations):
--   ℚ Archimedean + ≈-trans    ← Analysis.{Qarch, Qabs_sub_triangle, Req_trans} (the limiting argument)
--   ℚ multiplication/order     ← Analysis.{Qabs_mul, Qmul_le_mul, Qabs_mul_diff} (consumed by Rmul)
--   ℝ field arithmetic         ← Analysis.{Radd_comm, Radd_neg, Rmul, Rmul_comm} (add/neg/mul, regular)
--   ≈-congruence (well-defined)← Analysis.{Rneg_congr, Radd_congr, Rsub_congr} (operations respect ≈)
--   ℂ = ℝ×ℝ (comm. mult.)      ← Analysis.{Ceq_trans, Cadd_comm, Cadd_neg, Cmul, Cmul_comm}
-- v0.6.0 (ℝ and ℂ are commutative rings up to ≈; ℝ multiplication well-defined on the setoid):
--   Archimedean engine         ← Analysis.{Qarch_gen, Req_of_lin_bound} (linear bound C/(n+1) ⟹ ≈)
--   product-gap engine         ← Analysis.{Rmul_gap, Rgap_le, Rcross_le, canon_bound_mul}
--   ℝ multiplication well-def.  ← Analysis.Rmul_congr (the v0.5.0-deferred congruence, now proved)
--   ℝ commutative ring         ← Analysis.{Rmul_assoc, Rmul_distrib, Rmul_one, Radd_assoc, Rmul_zero}
--   ℂ commutative ring         ← Analysis.{Cadd_assoc, Cmul_one, Cmul_distrib, Cmul_assoc}
-- v0.7.0 (Cauchy completeness of ℝ — every regular sequence of reals converges):
--   limit construction         ← Analysis.{RReg, Rlim, RlimSeq_regular} (Bishop diagonal, reindex 4n+3)
--   convergence with rate      ← Analysis.Rlim_tendsTo (X k → lim X within 1/(k+1))
--   uniqueness of limits       ← Analysis.RTendsTo_unique (Archimedean + linear-bound criterion)
-- v0.8.0 (the first transcendental: Euler's number e via the exponential series):
--   factorial + partial sums   ← Analysis.{fct, eSum} (Σ 1/i!, from scratch — core has no factorial)
--   rigorous error bound       ← Analysis.ediff_bound (telescoping: U(n)=S(n)+2/(n+1)! decreasing)
--   e as a constructive real   ← Analysis.{e, eSeq_regular, e_pos} (the series value; positive)
-- v0.9.0 (the general exponential exp(q) on the rational interval [0,1]):
--   rational powers from scratch ← Analysis.{qpow, qpow_le_one} (qⁱ; for q∈[0,1] every qⁱ ≤ 1)
--   termwise domination bridge   ← Analysis.{expTerm_le, expdiff_dom} (qⁱ/i! ≤ 1/i!, gap dominated)
--   rigorous error bound (reused) ← Analysis.expdiff_bound (same 2/(a+1)! tail as e, by domination)
--   exp(q) as a constructive real ← Analysis.{Rexp, expSeq_regular}; anchors Rexp_zero (exp 0 ≈ 1),
--                                   Rexp_one_pos (exp 1 > 0), Rexp_one_eq_e (exp 1 ≈ e — ties to v0.8.0)
-- v0.10.0 (the λₙ / RH PROOF BOUNDARY — locked faithfully before ζ is built):
--   Bishop ℝ ≥ 0 / > 0         ← Li.{Rnonneg, Rnonneg_zero, Rnonneg_one, Pos_one}
--   Li-positivity property     ← Li.{LiPositive (strict, ζ-specific Li 1997), LiNonneg (BL 1999 form)};
--                                template_liPositive proves it for the constant-1 sequence (genuine)
--   the finite-check guard     ← Li.liPositive_iff_all_upTo (LiPositive = ∀N, LiPositiveUpTo; no
--                                finite N / `decide` reaches the universal — the first ~10⁵ λₙ are
--                                numerically positive yet that is NOT a proof)
--   ζ-layer substrate (interfaces, never asserted for the genuine λ) ← Li.{LiDecomposition (BL),
--                                ExplicitFormulaTrace (Weil 1952/Connes 1999), LiAgreesWith};
--                                LiDecomposition is now realized NON-TRIVIALLY (v0.15.3) ←
--                                Analysis.li_decomposition_realized, n=1 slice the real split
--   the explicit-formula prime side (v0.15.3) ← Analysis.{vonMangoldt (Λ; Λ(4)=log 2, Λ(6)=0),
--                                primeSide (Σ Λ(n)·h(log n), finite for compact support;
--                                primeSide_stable), and the Bombieri–Lagarias n=1 decomposition
--                                Rlambda1_decomposition (λ₁ = γ + (1 − γ/2 − ½log 4π))}
--   ζ(s) as a constructive object ← Analysis.{Czeta (Σ n⁻ˢ, complex s, Re s>1; Bishop Rlim of the dyadic
--                                partial sums), Czeta_re/im_tendsTo (convergence with rate 2/(k+1)); and the
--                                integer-s exact-bounded ζ (zeta, zeta_pos, zetadiff_bound)}; λₙ typed as
--                                Nat → ExactBoundedReal (Analysis.ExactBounded). HONEST SCOPE: ζ here
--                                is the convergent half-plane Re(s)>1 (no zeros, not the critical strip);
--                                the genuine λₙ values need analytic continuation + log (deferred).
-- v0.11.0 (the order ≤ on ℝ — the foundation for the transcendentals):
--   Bishop order ≤            ← Analysis.{Rle (xₙ ≤ yₙ + 2/(n+1)), Rle_refl, Rle_of_Req, Rle_antisymm,
--                               Rle_trans (Archimedean), Rle_zero_of_Rnonneg}; Rnonneg canonicalized here
--   ℚ signed-bound helpers    ← Analysis.{Qle_self_Qabs, Qabs_le_of_both, Qle_add_of_Qabs_sub,
--                               Qsub_le_of_le_add}
-- v0.12.0 (ℝ as a constructive field with powers, and `exp` on all of ℝ):
--   real field/powers          ← Analysis.{Rpow (iterated Rmul), Rpow_one, Rpow_congr; Rinv (1/x via
--                               a positivity witness, full Bishop regularity), Rdiv}
--   exp on ℝ (diagonal)        ← Analysis.{RexpReal = ⟨S_{x_{Rj}}(Rj)⟩ₙ, RexpReal_regular}, built from the
--                               rational bounds expSum_trunc_bound (geometric tail), expSum_Lip_le +
--                               LipS_le_U (Lipschitz), fct_ge_geom (factorial growth) — all axiom-clean
-- v0.13.0 (the transcendentals on ℝ: cos, sin, and log on positive reals (positivity-as-data)):
--   cos / sin on ℝ             ← Analysis.{Rcos = RaltReal x 0, Rsin = Rmul x (RaltReal x 1)}, the
--                               alternating series with base −q² dominated by exp(M²) (altSum_trunc_bound,
--                               altSum_Lip_le, fct_mono)
--   log on positive reals      ← Analysis.{RlogPos x k hk = 2·artanh((x−1)/(x+1)), positivity-AS-DATA — the
--                               SAME idiom as the reciprocal Rinv: from a witness x_k > 1/(k+1), the modulus
--                               1/M ≤ x ≤ M is DERIVED (M = |x₀| + 2 + 1/L, L = δ/2 the witness floor via
--                               Rinv_lb), not demanded of the caller. The engine Rlog x M takes the modulus
--                               explicitly (Rlog_two_ok exhibits it on x ≡ 2)}, built on the
--                               complete artanh diagonal Rartanh (artanh on every [−ρ,ρ], ρ<1), via the
--                               geometric tail (artSum_trunc), artanh Lipschitz (artSum_Lip_le), the general
--                               Bernoulli reindex (qpow_geom_bound), and the t-map q↦(q−1)/(q+1) with its
--                               cleared difference identity (tmap_diff_cleared), Lipschitz (tmap_lipschitz),
--                               and range bound (tmap_abs_le) — all axiom-clean, no `sorry`
-- v0.14.0 (the analytic constants of the Li/Keiper bridge, culminating in a positivity certificate
--          for the first Li coefficient λ₁ — EVIDENCE for RH's analytic face, never the crux):
--   π                          ← Analysis.Rpi (Machin 16·arctan(1/5) − 4·arctan(1/239), one diagonal),
--                               with Rpi_lower (π ≥ 6/5) and the tight Rpi_seq_ub_tight (π ≤ 3.142,
--                               via the alternating arctan truncation arctanSum_deep_le/ge at ρ=t)
--   log 2, log π               ← Analysis.{Rlog2c, Rlogπc} = 2·artanh((x−1)/(x+1)), clean rational /
--                               π-argument logs, with kernel-certified upper bounds Rlog2c_le
--                               (log 2 ≤ 0.6931) and Rlogπc_le (log π ≤ 1.1453) via artSum_le_value +
--                               artSum_base_mono (varying π-argument dominated by 15/29 = tmap(22/7))
--   γ (Euler–Mascheroni)       ← Analysis.Rgamma_h, the convergence-accelerated harmonic-telescoped
--                               γ = Σ(1/i − 2·artanh(1/(2i+1))), with the kernel-certified lower
--                               bracket Rgamma_h_lower (γ ≥ 0.54) — feasible where the ζ-series γ is not
--   λ₁ (first Li coefficient)  ← Analysis.Rlambda1 = ½·(2 + γ − log 4π) (Bombieri–Lagarias), with
--                               **Analysis.Rlambda1_pos : Pos Rlambda1** — λ₁ ≈ 0.0231 > 0, certified
--                               from γ ≥ 0.54, log 2 ≤ 0.6931, log π ≤ 1.1453 through the ℝ-order
--                               bridges (Radd_le_add, Rneg_le, Rhalf_ge). This realizes the n = 1 slice
--                               of Li's criterion as EVIDENCE; it does NOT assert λₙ > 0 for all n.
-- v0.17.0 (stage C — the canonical arithmetic square 𝕊 and its derived intersection lattice):
--   canonical 𝕊 = F ⊗_𝔽₁ F     ← Square.{copair_inl, copair_inr, copair_unique, sq_factor,
--     (universal property)        square_base_cocone, f1_initial, f1_initial_unique} — the
--                                coproduct of comm. monoids over the initial 𝔽₁; canonical
--                                BY the universal property, not by choice of model
--   strict 2-dimensionality    ← Square.{gen2_injective, inl_ne_inr, codiag_not_injective,
--     (§3.1 collapse avoided)     gen2_codiag_collapse, proj1_inl, proj2_inr, proj_faithful}
--   divisors & point counts    ← Square.{vFiber_inter_hFiber, vFiber_disjoint, hFiber_disjoint,
--                                diag_inter_vFiber, diag_inter_hFiber, graph_inter_vFiber,
--                                graph_inter_hFiber, graph_disjoint, diag_inter_graph_empty,
--                                graph_translate_diag, vFiber_translate, graph_one_diag}
--   the parallel pencil        ← Square.{pencil_shift (log y = log x + log n on Γ_n),
--     (§2.3 on canonical 𝕊)      pencil_parallel (slope 1 ⇒ direction (1,1)), pencil_det_zero
--                                (stable Δ·Γ_n = 0), pencil_separation (constant log n),
--                                pencil_separation_vonMangoldt (= Λ(p) at primes),
--                                pencil_separation_pow (k·log p), logN_mul_general,
--                                logN_pow_general}
--   the derived lattice (T3)   ← Square.{pair_*_derived (each number = a point count on 𝕊),
--                                e3_sq_forced (E₃² = −2 by bilinearity), sqPair_eq_template
--                                (the sourced §2.2 template EMERGES), sqPair_symm,
--                                sq_boundary_checks, sq_adjunction_checks, sq_signature_diag
--                                (the five-gate discipline), cls_generated (T2 f.g. on 𝕊)}
--   polarized 𝕊 (the lift)     ← Square.{squarePolarized (the Crux.Polarized instance is now
--                                𝕊's own lattice), sq_ample_pos (§1.4 on 𝕊), sq_hperp_neg_semidef,
--                                sq_hperp_definite, square_hodgeIndex} — and the boundary:
--                                Square.square_hodge_pencil_blind ([Γ_n]=[Δ], Δ·Γ_n=0 ∀n: the
--                                coarse-lattice Hodge index carries NO spectral input, so it is
--                                NOT the crux; same discipline as Bridge.control_psd)
-- The crux is NOT backed and stays `none` (BOTH faces, same RH) — λ₁ > 0 is the n=1 case, not RH:
--   hodgeIndexHolds (= RH, geometric) ← OPEN. Crux.template_hodgeIndex proves the property on the
--                               product-of-curves TEMPLATE; Square.square_hodgeIndex (v0.17.0)
--                               proves it on 𝕊's COARSE NUMERICAL LATTICE — which is provably
--                               pencil-blind (Square.square_hodge_pencil_blind), so NEITHER is the
--                               crux: the crux is the same property for the H¹-bearing pairing
--                               that carries the zeros (T4/T5), equivalently λₙ ≥ 0 ∀n.
--   liPositivityHolds (= RH, analytic) ← Li.LiCrux λ for the unconstructed genuine Li sequence λ —
--                               OPEN. Li.template_liPositive proves the property only for a constant
--                               sequence, never for λ; LiPositive λ ⟺ RH is [CLASSICAL] (Li 1997).
-- No arbitrary ceiling: if a genuine, audited, faithful proof of the crux ever lands, these fields
-- flip `none → some true` because that is then the truth (program stance, never a defect).
-- ===========================================================================

/-- Elaboration-checked witness that the manifest's established fields rest on real theorems
    (not just annotations): a sample of the proof layer, referenced from the manifest itself. -/
example :
    Template.pair (1, 1, 0) (1, 1, 0) = 2
    ∧ Mechanism.hodgeType 25 10
    ∧ (0 ≤ Bridge.controlForm 3 5 7 11 2 4)
    ∧ CycleCounts.trace (CycleCounts.powM CycleCounts.B 8) = 34
    ∧ Crux.HodgeIndex Crux.templatePolarized :=
  ⟨Template.H_sq, Mechanism.hasse_q25_a10, Bridge.control_psd 3 5 7 11 2 4,
   CycleCounts.N8, Crux.template_hodgeIndex⟩

/-- Elaboration-checked witness binding the v0.2.0 finite tropical stack and the ℚ brick to the
    manifest: Kleene idempotence (R2), κ⊥spectrum (R9/R10), the parallel pencil (§2.3), and the
    canonical ℚ form. -/
example :
    Tropical.mulN 4 (Tropical.starN 4 Tropical.W) (Tropical.starN 4 Tropical.W)
        = Tropical.starN 4 Tropical.W
    ∧ Tropical.kappa 2 Tropical.WA = Tropical.kappa 2 Tropical.WB
    ∧ Tropical.spectrum Tropical.WA Tropical.cyc2 ≠ Tropical.spectrum Tropical.WB Tropical.cyc2
    ∧ Tropical.Signature.det2 1 1 1 1 = 0
    ∧ Analysis.reduce ⟨6, 8⟩ = ⟨3, 4⟩ :=
  ⟨Tropical.R2_kleene_idempotent, Tropical.R9_same_kappa, Tropical.R10_diff_spectrum,
   Tropical.Signature.parallel_pencil, Analysis.reduce_6_8⟩

/-- Elaboration-checked witness binding the v0.3.0 analysis substrate to the manifest: the ℤ ring
    normalizer proves a *general* binomial identity (`(a+b)² = a²+2ab+b²`, here at a sample point),
    the general ℚ commutativity law holds, and the constructive real `½` is positive. -/
example :
    ((3 : Int) + 5) * (3 + 5) = 3 * 3 + 2 * (3 * 5) + 5 * 5
    ∧ Analysis.Qeq (Analysis.mul ⟨2, 3⟩ ⟨4, 5⟩) (Analysis.mul ⟨4, 5⟩ ⟨2, 3⟩)
    ∧ Analysis.Pos Analysis.half :=
  ⟨Analysis.RingNF.sq_add 3 5, Analysis.mul_comm ⟨2, 3⟩ ⟨4, 5⟩, Analysis.Pos_half⟩

/-- Elaboration-checked witness binding the v0.4.0 layer: the from-scratch `ring_uor` proves a general
    integer identity, ℚ addition is monotone (ordered field), and ℝ negation is a pointwise
    involution (ℝ arithmetic). -/
example :
    ((2 : Int) + 3) * (2 + 3) = 2 * 2 + 2 * (2 * 3) + 3 * 3
    ∧ (∀ a b c d : Analysis.Q, Analysis.Qle a b → Analysis.Qle c d →
        Analysis.Qle (Analysis.add a c) (Analysis.add b d))
    ∧ ((Analysis.Rneg (Analysis.Rneg Analysis.half)).seq 0).num = (Analysis.half.seq 0).num :=
  ⟨Analysis.RingNF.ring_uor_sq 2 3, fun _ _ _ _ hab hcd => Analysis.Qadd_le_add hab hcd,
   Analysis.Rneg_Rneg_seq Analysis.half 0⟩

/-- Elaboration-checked witness binding the v0.5.0 layer: Bishop equality on ℝ is transitive (an
    equivalence), ℝ multiplication is commutative up to `≈`, and ℂ multiplication is commutative
    up to `≈` (via the operation-congruences). -/
example :
    (∀ x y z : Analysis.Real, Analysis.Req x y → Analysis.Req y z → Analysis.Req x z)
    ∧ (∀ x y : Analysis.Real, Analysis.Req (Analysis.Rmul x y) (Analysis.Rmul y x))
    ∧ (∀ z w : Analysis.Complex, Analysis.Ceq (Analysis.Cmul z w) (Analysis.Cmul w z)) :=
  ⟨fun _ _ _ => Analysis.Req_trans, Analysis.Rmul_comm, Analysis.Cmul_comm⟩

/-- Elaboration-checked witness binding the v0.6.0 layer: ℝ multiplication is well-defined on the
    `≈`-setoid (the v0.5.0-deferred congruence), ℝ multiplication is associative up to `≈`, and ℂ
    multiplication is both associative and distributive up to `≈` — so ℂ is a commutative ring. -/
example :
    (∀ x x' y y' : Analysis.Real, Analysis.Req x x' → Analysis.Req y y' →
        Analysis.Req (Analysis.Rmul x y) (Analysis.Rmul x' y'))
    ∧ (∀ x y z : Analysis.Real,
        Analysis.Req (Analysis.Rmul (Analysis.Rmul x y) z) (Analysis.Rmul x (Analysis.Rmul y z)))
    ∧ (∀ z w v : Analysis.Complex,
        Analysis.Ceq (Analysis.Cmul (Analysis.Cmul z w) v) (Analysis.Cmul z (Analysis.Cmul w v)))
    ∧ (∀ z w v : Analysis.Complex,
        Analysis.Ceq (Analysis.Cmul z (Analysis.Cadd w v))
                     (Analysis.Cadd (Analysis.Cmul z w) (Analysis.Cmul z v))) :=
  ⟨fun _ _ _ _ => Analysis.Rmul_congr, Analysis.Rmul_assoc, Analysis.Cmul_assoc, Analysis.Cmul_distrib⟩

/-- Elaboration-checked witness binding the v0.7.0 layer: ℝ is Cauchy complete — every regular
    sequence of reals converges to its diagonal limit (with an explicit rate), and limits are unique
    up to `≈`. -/
example :
    (∀ (X : Nat → Analysis.Real) (h : Analysis.RReg X), Analysis.RTendsTo X (Analysis.Rlim X h))
    ∧ (∀ (X : Nat → Analysis.Real) (L L' : Analysis.Real),
        Analysis.RTendsTo X L → Analysis.RTendsTo X L' → Analysis.Req L L') :=
  ⟨Analysis.Rlim_tendsTo, fun _ _ _ => Analysis.RTendsTo_unique⟩

/-- Elaboration-checked witness binding the v0.8.0 layer: Euler's number `e` is a genuine constructive
    real (positive), and the exponential series carries a rigorous rational error bound on its partial
    sums (`S(b) − S(a) ≤ 2/(a+1)!` for `a ≤ b`) — the convergent-series-with-error-bound pattern. -/
example :
    Analysis.Pos Analysis.e
    ∧ (∀ a b : Nat, a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.eSum b) (Analysis.eSum a)) ⟨2, Analysis.fct (a + 1)⟩) :=
  ⟨Analysis.e_pos, fun _ _ h => Analysis.ediff_bound h⟩

/-- Elaboration-checked witness binding the v0.9.0 layer: the general exponential `exp(q)` on the
    rational interval `[0,1]` is a genuine constructive real — it agrees with `1` at `q = 0`
    (`exp 0 ≈ 1`), is positive at `q = 1` (`exp 1 > 0`), and its partial sums carry the *same*
    rigorous rational error bound as `e` via termwise domination (`qⁱ/i! ≤ 1/i!` for `q ∈ [0,1]`). -/
example :
    Analysis.Req (Analysis.Rexp ⟨0, 1⟩ (by decide) (by decide) (by decide)) Analysis.one
    ∧ Analysis.Req (Analysis.Rexp ⟨1, 1⟩ (by decide) (by decide) (by decide)) Analysis.e
    ∧ Analysis.Pos (Analysis.Rexp ⟨1, 1⟩ (by decide) (by decide) (by decide))
    ∧ (∀ (q : Analysis.Q) (hq0 : 0 ≤ q.num) (hqd : 0 < q.den) (hq1 : Analysis.Qle q ⟨1, 1⟩)
        (a b : Nat), a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.expSum q b) (Analysis.expSum q a))
          ⟨2, Analysis.fct (a + 1)⟩) :=
  ⟨Analysis.Rexp_zero, Analysis.Rexp_one_eq_e, Analysis.Rexp_one_pos,
   fun _ hq0 hqd hq1 _ _ h => Analysis.expdiff_bound hq0 hqd hq1 h⟩

/-- Elaboration-checked witness binding the v0.10.0 layer — the λₙ / RH proof boundary, locked
    faithfully. The Li-positivity PROPERTY is genuine (the constant-`1` sequence satisfies it), it is
    *exactly* the conjunction of all finite truncations (so no finite check is a proof), and the
    Bombieri–Lagarias decomposition is a genuine interface — while the CRUX, `LiCrux` for the
    unconstructed genuine Li sequence of ζ, is never asserted (`liPositivityHolds = none`, = RH). -/
example :
    Li.LiPositive (fun _ => Analysis.one)
    ∧ (∀ lam : Nat → Analysis.ExactBoundedReal, Li.LiPositive lam ↔ ∀ N, Li.LiPositiveUpTo lam N)
    ∧ (∀ lam : Nat → Analysis.ExactBoundedReal, Li.LiDecomposition lam lam (fun _ => Analysis.zero))
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Li.template_liPositive, Li.liPositive_iff_all_upTo, Li.liDecomposition_genuine, rfl⟩

/-- Elaboration-checked witness that ζ ships as a genuine **exact-bounded object**: for every integer
    `s ≥ 2`, `ζ(s) = Σ 1/iˢ` is a constructive real that is positive (`zeta_pos`) and whose partial
    sums carry the rigorous rational error bound `S(b) − S(a) ≤ 1/(a+1)` (`zetadiff_bound`) — its
    precision certificate. (This is ζ in the convergent regime `Re(s) > 1`, where it has no zeros; the
    analytic continuation to the critical strip — where RH lives — is not built.) -/
example :
    (∀ (s : Nat) (hs : 2 ≤ s), Analysis.Pos (Analysis.zeta s hs))
    ∧ (∀ (s : Nat) (_hs : 2 ≤ s) (a b : Nat), a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.zetaSum s b) (Analysis.zetaSum s a)) ⟨1, a + 1⟩)
    ∧ (∀ (x : Analysis.ExactBoundedReal) (n : Nat),
        Analysis.Qeq (Analysis.Qsub (Analysis.upperB x n) (Analysis.lowerB x n)) ⟨2, n + 1⟩) :=
  ⟨Analysis.zeta_pos, fun s hs _ _ h => Analysis.zetadiff_bound s hs h, Analysis.enclosure_width⟩

/-- Elaboration-checked witness binding the v0.11.0 layer: the order `≤` on ℝ is a genuine order —
    reflexive, antisymmetric up to `≈` (`x ≤ y` and `y ≤ x` give `x ≈ y`), transitive (the genuine
    Archimedean limiting step), and refined by `≈`; and Bishop non-negativity `x ≥ 0` entails `0 ≤ x`.
    This is the foundation the transcendentals (`exp`, `cos`/`sin`, `log`) build on. -/
example :
    (∀ x : Analysis.Real, Analysis.Rle x x)
    ∧ (∀ x y : Analysis.Real, Analysis.Rle x y → Analysis.Rle y x → Analysis.Req x y)
    ∧ (∀ x y z : Analysis.Real, Analysis.Rle x y → Analysis.Rle y z → Analysis.Rle x z)
    ∧ (∀ x : Analysis.Real, Analysis.Rnonneg x → Analysis.Rle Analysis.zero x) :=
  ⟨Analysis.Rle_refl, fun _ _ => Analysis.Rle_antisymm, fun _ _ _ => Analysis.Rle_trans,
   fun _ => Analysis.Rle_zero_of_Rnonneg⟩

/-- Elaboration-checked witness binding the v0.12.0 layer: real powers satisfy `x¹ ≈ x`, and the
    everywhere-defined `exp` on ℝ is a genuinely constructed real — its diagonal sequence is
    Bishop-regular, with the explicit rigorous gap bound `|expₓ(j) − expₓ(k)| ≤ 1/(j+1)` for `j ≤ k`
    (truncation + Lipschitz, both axiom-clean). -/
example :
    (∀ x : Analysis.Real, Analysis.Req (Analysis.Rpow x 1) x)
    ∧ (∀ x : Analysis.Real, Analysis.IsRegular (Analysis.RexpReal_seq x))
    ∧ (∀ x : Analysis.Real, ∀ j k : Nat, j ≤ k →
        Analysis.Qle (Analysis.Qabs (Analysis.Qsub (Analysis.RexpReal_seq x j)
          (Analysis.RexpReal_seq x k))) (Analysis.Qbound j)) :=
  ⟨Analysis.Rpow_one, Analysis.RexpReal_regular, fun _ _ _ h => Analysis.RexpReal_diag_le _ h⟩

/-- Elaboration-checked witness binding the v0.13.0 transcendentals: `cos` and `sin` (the alternating
    diagonal `RaltReal x off`) are genuinely constructed reals — their diagonal sequences are
    Bishop-regular; and `log` on positive reals is genuine **positivity-as-data**: from a witness
    `x_k > 1/(k+1)`, `RlogPos x k` derives the modulus `1/M ≤ x ≤ M` and yields a constructed real
    (third clause: `log 2` via this path, on the concrete positive real `2`). All axiom-clean, no
    `sorry`; the t-map range bound keeps the artanh argument inside `[−ρ,ρ]`, `ρ<1`. -/
example :
    (∀ x : Analysis.Real, ∀ off : Nat, Analysis.IsRegular (Analysis.RaltReal_seq x off))
    ∧ (∀ x : Analysis.Real, (∀ n, 0 < (x.seq n).num) → Analysis.IsRegular (Analysis.Rlog_seq x))
    ∧ Analysis.IsRegular (Analysis.RlogPos Analysis.twoReal 0 (by decide)).seq :=
  ⟨Analysis.RaltReal_regular, Analysis.Rlog_regular,
   (Analysis.RlogPos Analysis.twoReal 0 (by decide)).reg⟩

/-- Elaboration-checked witness binding the v0.14.0 analytic constants: the first Li/Keiper
    coefficient `λ₁ = ½·(2 + γ − log 4π)` is a **positivity-certified** constructive real —
    `Pos Rlambda1` holds (`λ₁ ≈ 0.0231 > 0`), built from the accelerated Euler–Mascheroni constant
    `γ ≥ 0.54` and the clean logs `log 2 ≤ 0.6931`, `log π ≤ 1.1453`, all choice-free and `sorry`-free.
    This is the `n = 1` slice of Li's criterion as **evidence**; it is NOT the crux — `λₙ > 0 ∀ n`
    (= RH) stays open and `liPositivityHolds = none` (witnessed just above). -/
example : Analysis.Pos Analysis.Rlambda1 ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Analysis.Rlambda1_pos, rfl⟩

/-- Elaboration-checked witness binding the v0.15.0 complex analytic engine (exponential core): the
    real exponential is a genuine **homomorphism** — `exp(x+y) ≈ exp x · exp y` for all constructive
    reals (`RexpReal_add`) — and the complex `nˢ` carries the **modulus identity** `|nˢ|² = (exp(Re s·log n))²`
    (`ncpow_normSq`, the analytic payoff of `cos²+sin² ≈ 1`). Both choice-free and `sorry`-free. This is
    the exponential core of stage A; ζ for complex `s` is gated on `exp∘log = id` (the v0.15.x series) and
    the crux stays open — `liPositivityHolds = none`. -/
example :
    (∀ x y : Analysis.Real, Analysis.Req (Analysis.RexpReal (Analysis.Radd x y))
        (Analysis.Rmul (Analysis.RexpReal x) (Analysis.RexpReal y)))
      ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Analysis.RexpReal_add, rfl⟩

/-- Elaboration-checked witness binding the v0.15.1 ζ-convergence gate `exp∘log = id`: the power-series
    composition identity **`exp(2·artanh τ) = (1+τ)/(1−τ)`** (`Rexp_two_artanh_ofQ`, the roadmap's
    research-grade base identity) and its corollary **`exp(log n) = n` for the *literal* `Rlog` term**
    (`Rexp_log_nat_Rlog`: `RexpReal (Rlog (ofQ n) …) ≈ n`). Built from scratch by composing the exp factorial
    series with the artanh geometric series (the corner bound `exp_corner_le`, the rational identity
    `exp_artanh_rat_cleared`, and the diagonal reconciliation `Rexp_two_artanh_via`); the radius-general
    construction makes it match the actual `Rlog` (whose artanh radius `ρ_M` is smaller) by definitional
    equality. Choice-free and `sorry`-free. This unlocks `|n⁻ˢ| = n⁻ᴿᵉˢ` for the ζ-complex tail (v0.15.2);
    the crux stays open — `liPositivityHolds = none`.

    Two bindings: the general theorem `Rexp_log_nat_Rlog` (for every `n ≥ 1`, with the obviously-satisfiable
    `Rlog` modulus side-conditions), and a concrete, fully-closed instance `exp(log 2) = 2` whose
    side-conditions are `decide`-checked — so the result is demonstrably non-vacuous. -/
example :
    (∀ (n : Nat), 1 ≤ n →
      ∀ (hMge : Analysis.Qle (⟨1, 1⟩ : Analysis.Q) ⟨(n : Int), 1⟩)
        (hxpos : ∀ k, 0 < ((Analysis.ofQ (⟨(n : Int), 1⟩ : Analysis.Q) Nat.one_pos).seq k).num)
        (hhi : ∀ k, Analysis.Qle ((Analysis.ofQ (⟨(n : Int), 1⟩ : Analysis.Q) Nat.one_pos).seq k) ⟨(n : Int), 1⟩)
        (hlo : ∀ k, Analysis.Qle (⟨1, 1⟩ : Analysis.Q)
          (Analysis.mul ((Analysis.ofQ (⟨(n : Int), 1⟩ : Analysis.Q) Nat.one_pos).seq k) ⟨(n : Int), 1⟩)),
        Analysis.Req (Analysis.RexpReal (Analysis.Rlog (Analysis.ofQ (⟨(n : Int), 1⟩ : Analysis.Q) Nat.one_pos)
            ⟨(n : Int), 1⟩ Nat.one_pos hMge hxpos hhi hlo))
          (Analysis.ofQ (⟨(n : Int), 1⟩ : Analysis.Q) Nat.one_pos))
      ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨fun n hn hMge hxpos hhi hlo => Analysis.Rexp_log_nat_Rlog n hn hMge hxpos hhi hlo, rfl⟩

/-- A concrete, fully-closed instance of the ζ-convergence gate for the literal `Rlog`: `exp(log 2) = 2`.
    The `Rlog` modulus side-conditions are supplied by `Rlog_two_ok` (each `decide`-checked) — the gate is
    non-vacuous on the constructive `log 2`. -/
example :
    Analysis.Req (Analysis.RexpReal (Analysis.Rlog (Analysis.ofQ (⟨(2 : Int), 1⟩ : Analysis.Q) Nat.one_pos)
        ⟨(2 : Int), 1⟩ Nat.one_pos Analysis.Rlog_two_ok.2.1 Analysis.Rlog_two_ok.2.2.1
        Analysis.Rlog_two_ok.2.2.2.1 Analysis.Rlog_two_ok.2.2.2.2))
      (Analysis.ofQ (⟨(2 : Int), 1⟩ : Analysis.Q) Nat.one_pos) :=
  Analysis.Rexp_log_nat_Rlog 2 (by decide) Analysis.Rlog_two_ok.2.1 Analysis.Rlog_two_ok.2.2.1
    Analysis.Rlog_two_ok.2.2.2.1 Analysis.Rlog_two_ok.2.2.2.2

set_option linter.unusedVariables false in
/-- Elaboration-checked witness binding the v0.15.2 keystone: **the Riemann zeta function `ζ(s) = Σ_{n≥1} n⁻ˢ`
    for *complex* `s` with `Re s > 1`** is a genuine constructive complex number (`Czeta`), and its partial
    sums converge to it with an explicit rate. For any `s` with `Re s ≥ 0` and a rational witness `τ > 0` of
    `Re s > 1` (`τ ≤ (Re s − 1)·log 2`, so the dyadic ratio `2^{1−Re s} < 1`), both the real and imaginary
    reindexed partial sums `Σ_{n<2^{M(k)}} Re/Im(n⁻ˢ)` converge to `Re/Im ζ(s)` with the canonical Bishop
    rate `2/(k+1)` (`Czeta_re_tendsTo`, `Czeta_im_tendsTo`) — the rigorous complex geometric tail. This is ζ
    in its *full* convergent half-plane `Re s > 1` (not merely integer `s ≥ 2`); the analytic continuation to
    the critical strip — where RH lives — is not built, and the crux stays open (`liPositivityHolds = none`).
    (The `Re s > 1` witness hypotheses are proof-scaffolding — semantically required for convergence but not
    syntactically present in the conclusion — so the unused-binder linter is disabled for these examples.) -/
example :
    (∀ (s : Analysis.Complex) (hσ : Analysis.Rnonneg s.re) (τ : Analysis.Q)
        (hτn : 0 < τ.num) (hτd : 0 < τ.den)
        (hθ : Analysis.Rle (Analysis.ofQ τ hτd)
          (Analysis.Rmul (Analysis.Rsub s.re Analysis.one) (Analysis.logN 2 (by omega)))),
        Analysis.RTendsTo (fun j => Analysis.czetaReSum s (2 ^ Analysis.czetaMidx τ j))
            (Analysis.Czeta s hσ hτn hτd hθ).re
          ∧ Analysis.RTendsTo (fun j => Analysis.czetaImSum s (2 ^ Analysis.czetaMidx τ j))
            (Analysis.Czeta s hσ hτn hτd hθ).im)
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨fun s hσ τ hτn hτd hθ =>
    ⟨Analysis.Czeta_re_tendsTo s hσ hτn hτd hθ, Analysis.Czeta_im_tendsTo s hσ hτn hτd hθ⟩, rfl⟩

/-- A concrete, fully-closed instance proving the v0.15.2 keystone is **non-vacuous**: at `s = 2` (real),
    `ζ(2) = Σ 1/n²` is built as `Czeta` and its real partial sums converge to `Re ζ(2)` with rate `2/(k+1)`.
    The `Re s > 1` witness is `τ = 1/2 ≤ (2−1)·log 2 = log 2` (`czeta_two_theta`, all `decide`/`omega`-checked);
    the imaginary part vanishes (`Im s = 0`). So the universally-quantified convergence above has a witness. -/
example :
    Analysis.RTendsTo
        (fun j => Analysis.czetaReSum ⟨Analysis.ofQ (⟨2, 1⟩ : Analysis.Q) (by decide), Analysis.zero⟩
          (2 ^ Analysis.czetaMidx (⟨1, 2⟩ : Analysis.Q) j))
        (Analysis.Czeta ⟨Analysis.ofQ (⟨2, 1⟩ : Analysis.Q) (by decide), Analysis.zero⟩
          (Analysis.Rnonneg_ofQ (by decide) (by decide)) (by decide) (by decide)
          Analysis.czeta_two_theta).re
      ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Analysis.Czeta_re_tendsTo ⟨Analysis.ofQ (⟨2, 1⟩ : Analysis.Q) (by decide), Analysis.zero⟩
      (Analysis.Rnonneg_ofQ (by decide) (by decide)) (by decide) (by decide) Analysis.czeta_two_theta, rfl⟩

set_option linter.unusedVariables false in
/-- Elaboration-checked witness that ζ(s) converges as a **genuine series** — not merely along the dyadic
    subsequence. For any complex `s` with `Re s > 1` (witness `τ`), the *full* real and imaginary partial-sum
    sequences are uniformly Cauchy: for *every* `N, N' ≥ 2^{M(j)}`, `|S(N) − S(N')| ≤ 2/(j+1)`
    (`czetaRe/Im_cauchy_full`). So every partial sum `Σ_{n=1}^N n⁻ˢ` past the dyadic anchor agrees within
    `2/(j+1)` — `Σ_{n≥1} n⁻ˢ` converges in the strong (full-sequence) sense, with the crux still open. -/
example :
    (∀ (s : Analysis.Complex) (hσ : Analysis.Rnonneg s.re) (τ : Analysis.Q)
        (hτn : 0 < τ.num) (hτd : 0 < τ.den)
        (_hθ : Analysis.Rle (Analysis.ofQ τ hτd)
          (Analysis.Rmul (Analysis.Rsub s.re Analysis.one) (Analysis.logN 2 (by omega))))
        (j N N' : Nat), 2 ^ Analysis.czetaMidx τ j ≤ N → 2 ^ Analysis.czetaMidx τ j ≤ N' →
        Analysis.Rle (Analysis.Rsub (Analysis.czetaReSum s N) (Analysis.czetaReSum s N'))
            (Analysis.ofQ ⟨2, j + 1⟩ (Nat.succ_pos j))
          ∧ Analysis.Rle (Analysis.Rsub (Analysis.czetaImSum s N) (Analysis.czetaImSum s N'))
            (Analysis.ofQ ⟨2, j + 1⟩ (Nat.succ_pos j)))
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨fun s hσ τ hτn hτd hθ j N N' hN hN' =>
    ⟨Analysis.czetaRe_cauchy_full s hσ hτn hτd hθ j N N' hN hN',
     Analysis.czetaIm_cauchy_full s hσ hτn hτd hθ j N N' hN hN'⟩, rfl⟩

set_option linter.unusedVariables false in
/-- Elaboration-checked witness that ζ(s) is **canonical** — independent of the convergence witness `τ`.
    For any complex `s` with `Re s > 1` and any *two* rational witnesses `τ₁, τ₂`, `Czeta` yields `≈`-equal
    real and imaginary parts (`Czeta_re/im_canonical`): both are the limit of the same full partial-sum
    sequence, so the limit is unique. Hence `ζ(s)` is a well-defined function of `s` alone on `Re s > 1`
    (not an artifact of the dyadic anchoring), with the crux still open. -/
example :
    (∀ (s : Analysis.Complex) (hσ : Analysis.Rnonneg s.re) (τ₁ τ₂ : Analysis.Q)
        (hτn₁ : 0 < τ₁.num) (hτd₁ : 0 < τ₁.den)
        (hθ₁ : Analysis.Rle (Analysis.ofQ τ₁ hτd₁)
          (Analysis.Rmul (Analysis.Rsub s.re Analysis.one) (Analysis.logN 2 (by omega))))
        (hτn₂ : 0 < τ₂.num) (hτd₂ : 0 < τ₂.den)
        (hθ₂ : Analysis.Rle (Analysis.ofQ τ₂ hτd₂)
          (Analysis.Rmul (Analysis.Rsub s.re Analysis.one) (Analysis.logN 2 (by omega)))),
        Analysis.Req (Analysis.Czeta s hσ hτn₁ hτd₁ hθ₁).re (Analysis.Czeta s hσ hτn₂ hτd₂ hθ₂).re
          ∧ Analysis.Req (Analysis.Czeta s hσ hτn₁ hτd₁ hθ₁).im (Analysis.Czeta s hσ hτn₂ hτd₂ hθ₂).im)
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨fun s hσ τ₁ τ₂ hτn₁ hτd₁ hθ₁ hτn₂ hτd₂ hθ₂ =>
    ⟨Analysis.Czeta_re_canonical s hσ hτn₁ hτd₁ hθ₁ hτn₂ hτd₂ hθ₂,
     Analysis.Czeta_im_canonical s hσ hτn₁ hτd₁ hθ₁ hτn₂ hτd₂ hθ₂⟩, rfl⟩

/-- Elaboration-checked witness binding the v0.15.3 layer — the **von Mangoldt `Λ` / prime side** and
    the **Bombieri–Lagarias `n = 1` decomposition**. `Λ(4) = log 2` and `Λ(6) = 0` exhibit a genuine
    arithmetic object (prime power vs. composite); the decomposition `λ₁ = λ₁^{arith} + λ₁^{∞}`
    (`γ` plus the archimedean `1 − γ/2 − ½·log 4π`) is a real theorem on constructive reals; and the
    `Li.LiDecomposition` interface is now realized **non-trivially** (`li_decomposition_realized`) — its
    `n = 1` slice is the genuine two-place split, not the trivial `λ = λ + 0`. This is the explicit
    formula's arithmetic ingredient and its `λ₁` bridge; it bears nothing on positivity — the crux
    `liPositivityHolds` stays `none`, RH open. -/
example :
    Analysis.Req (Analysis.vonMangoldt 4) (Analysis.logN 2 (by omega))
    ∧ Analysis.Req (Analysis.vonMangoldt 6) Analysis.zero
    ∧ Analysis.Req Analysis.Rlambda1
        (Analysis.Radd Analysis.Rlambda1_arith Analysis.Rlambda1_arch)
    ∧ Li.LiDecomposition Analysis.liLamSeq Analysis.liArithSeq Analysis.liArchSeq
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Analysis.vonMangoldt_four, Analysis.vonMangoldt_six, Analysis.Rlambda1_decomposition,
   Analysis.li_decomposition_realized, rfl⟩

/-- Elaboration-checked witness binding the **v0.16.0 stage-B layer** — critical-strip `ζ`, the
    archimedean `Γ′/Γ` place, and `Pos λ₂`. Built and compiled in this build (so their existence is
    machine-checked): `Analysis.Ceta` — `η(s)` on the whole strip `Re s > 0` as a constructive `ℂ`
    (the integration-free Dirichlet-eta route); `Analysis.CzetaStrip` with
    `Analysis.CzetaStrip_functional : (1 − 2^{1−s})·ζ ≈ η` and the non-vanishing
    `Analysis.etaDenom_Pos_normSq` — `ζ(s)` on the critical strip `0 < Re s < 1`; `Analysis.Digamma` —
    the archimedean `Γ′/Γ = ψ` EXACTLY (the convergent series `−γ + Σ[1/(n+1) − 1/(n+z)]`); and
    `Analysis.SpougeGamma` — Spouge's `Γ`-approximant (error bound cited, not formalized). The single
    theorem-level fact bound here is **`Pos λ₂`** (`Analysis.Rlambda2_pos`, `λ₂ ≈ 0.0043 > 0`), the
    higher-Stieltjes capstone — EVIDENCE for Li's criterion at `n = 2`, not the crux. RH stays open:
    `liPositivityHolds = none`. -/
example :
    Analysis.Pos Analysis.Rlambda2
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Analysis.Rlambda2_pos, rfl⟩

/-- Elaboration-checked witness binding the **v0.17.0 stage-C layer** — the canonical arithmetic
    square. In order: (1) the UNIVERSAL PROPERTY of `𝕊 = F ⊗_𝔽₁ F` (uniqueness of the universal
    map — the canonicality); (2) strict 2-dimensionality (the rank-2 monomial family is free);
    (3) the §2.3 finding on canonical `𝕊` (no transverse fixed points of the scaling Frobenius);
    (4) the derived lattice reproduces the sourced template intrinsically (`E₃² = −2`, forced by
    bilinearity from point counts); (5) the Hodge index of the derived lattice holds —
    AND (6) that lattice is pencil-blind (`Δ·Γ_n = 0` for all `n`), which is exactly why (5) is
    NOT the crux: `hodgeIndexHolds` and `liPositivityHolds` stay `none`, RH OPEN. -/
example :
    (∀ (T : Square.CMon) (f g : Square.MHom Square.Curve T) (h : Square.MHom Square.Sq T),
        (∀ a, h.map (Square.inl.map a) = f.map a) →
        (∀ b, h.map (Square.inr.map b) = g.map b) →
        ∀ z, h.map z = (Square.copair T f g).map z)
    ∧ (∀ a b c d : Nat, Square.gen2 a b = Square.gen2 c d → a = c ∧ b = d)
    ∧ (∀ n : Nat, 2 ≤ n → ∀ z : Square.SqPt, ¬(Square.diag z ∧ Square.graph n z))
    ∧ Square.sqPair Square.clsE3 Square.clsE3 = -2
    ∧ (∀ u v : Square.SqCls, Square.sqPair u v = Template.pair u v)
    ∧ Crux.HodgeIndex Square.squarePolarized
    ∧ (∀ n : Nat, Square.sqPair Square.clsDiag (Square.clsGraph n) = 0)
    ∧ f1SquareStatus.hodgeIndexHolds = none
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Square.copair_unique, Square.gen2_injective, Square.diag_inter_graph_empty,
   (Square.e3_sq_forced).2, Square.sqPair_eq_template, Square.square_hodgeIndex,
   fun _ => rfl, rfl, rfl⟩

/-- Elaboration-checked witness that the v0.17.0 pencil carries the ARITHMETIC content as
    constructive-real shift lengths: at every prime `p`, every point of the Frobenius graph `Γ_p`
    sits at log-separation exactly `Λ(p) = log p` from the diagonal — the explicit-formula prime
    weight (`Analysis/Mangoldt.lean`), reached geometrically on canonical `𝕊`. The pencil's
    POSITIVITY is RH and stays open. -/
example :
    (∀ (p : Nat) (hp2 : 2 ≤ p), (∀ d, d ∣ p → d = 1 ∨ d = p) →
      ∀ (z : Square.SqPt) (_ : Square.graph p z),
        Analysis.Req
          (Analysis.Rsub (Analysis.logN z.2.val z.2.property)
            (Analysis.logN z.1.val z.1.property))
          (Analysis.vonMangoldt p))
    ∧ f1SquareStatus.hodgeIndexHolds = none :=
  ⟨fun p hp2 hp z hz => Square.pencil_separation_vonMangoldt p hp2 hp z hz, rfl⟩

/-- Elaboration-checked witness binding the v0.17.0 **peer-review hardening**: (1) the coproduct
    property of `𝕊` packaged as one proposition (`sq_isCoproduct`) with uniqueness up to canonical
    isomorphism (`coproduct_unique_upto_iso`) — "the" tensor is well-defined; and (2) the von Mangoldt
    function is correct on ALL prime powers (`Λ(pᵏ) = log p`, via the from-scratch Euclid's lemma
    `prime_dvd_mul`), so the pencil's Λ-tie covers the full support of `Λ`. The crux stays `none`. -/
example :
    Square.IsCoproduct Square.Sq Square.inl Square.inr
    ∧ (∀ (p : Nat) (hp2 : 2 ≤ p), (∀ d, d ∣ p → d = 1 ∨ d = p) →
        ∀ {k : Nat}, 1 ≤ k →
          Analysis.Req (Analysis.vonMangoldt (p ^ k)) (Analysis.logN p (by omega)))
    ∧ f1SquareStatus.hodgeIndexHolds = none :=
  ⟨Square.sq_isCoproduct,
   fun p hp2 hp {k} hk => Analysis.vonMangoldt_prime_pow hp2 hp hk, rfl⟩

end UOR.Bridge.F1Square
