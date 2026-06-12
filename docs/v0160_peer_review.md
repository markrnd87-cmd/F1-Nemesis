# v0.16.0 — Peer-review notes (stage B)

This document records the adversarial self-review of the v0.16.0 release (critical-strip ζ, the
archimedean Γ′/Γ place, and `Pos λ₂`) and the resulting hardening. It is intended to give a reviewer
the attack surface and the honest scope up front.

## Review method

Three independent adversarial reviewers were run, one per new artifact, each mandated to find vacuity,
unsatisfiable hypotheses, mis-statements, soundness errors, and over-claims:

1. `Analysis/CriticalZeta.lean` — the η→ζ quotient.
2. `Analysis/Gamma.lean` — `RrpowPos`, the digamma `ψ`, and the Spouge `Γ` approximant.
3. The `Ceta` construction in `Analysis/EtaVariation.lean`.

The construction was found **sound and non-circular** throughout (every bound, projection, telescoping,
and `RReg`/`Rlim` step verified; no off-by-one — the `n = 1` η term is correctly retained). The findings
were about *formal completeness* and *honesty of claims*, not logic bugs. All are now closed except one
explicitly-deferred convenience lemma (below).

## Findings closed

### Non-vacuity — the headline gap
The headline objects were unwitnessed: nothing instantiated `Ceta`/`CzetaStrip`/`Digamma`/`SpougeGamma`
at a concrete point, so a reviewer could not see that the hypothesis bundles are jointly satisfiable.
For `Ceta`/`CzetaStrip` there was a deeper issue: the convergence witness `τ` was `Prop`-`∃`-wrapped
(via `EtaVSum_block_geo_le`), so a *closed, choice-free* value could not be extracted (a defect shared
with the already-shipped `Czeta`). Closed by:

- **`τ` exposed as data** — `etaTau` (+ the data-track `etaU_le_ratio_data`/`etaB_le_geo_data`/
  `EtaVSum_block_geo_data`) derives the geometric-decay witness from an explicit `Re s`-positivity
  witness `(kσ, hkσ)`, with **no `∃`/choice**.
- **`CetaW`** — η(s) as a concretely-constructible `ℂ`; **`CetaW_half_wellTyped`** exhibits a concrete
  `η(½)` value (choice-free).
- **`CzetaStripW`** — ζ(s) = `CetaW / (1 − 2^{1−s})`, concretely constructible; **`CzetaStrip_half_nonvacuous`**
  proves the inverse witness exists at `s = ½` (derived from `Re s = ½ ≤ ¾ < 1` via `etaDenom_Pos_normSq`),
  so the critical-strip ζ is non-vacuous on the critical line.
- **`Digamma_one_eq_neg_gamma`** — `ψ(1) = −γ`, proved outright (a concrete instantiation of `Digamma`
  *and* a validation of the `−γ` convention).
- **`spougeGammaWitness`** — a concrete `SpougeGamma` value (`a = 4, N = 2`).

### A real vacuity bug (Spouge)
`SpougeGamma`'s per-coefficient hypothesis was `∀ k, 1 ≤ k → a − k > 1` — **unbounded**, hence
unsatisfiable for any finite `a`, so `SpougeGamma` was *un-instantiable as typed*. Fixed by adding the
missing `k ≤ N` bound (matching the documented `N = ⌈a⌉−1`), threaded through the bracket recursion.

### `Ceta` tied to the η series + well-definedness (czeta-parity)
- **`CetaW_re/im_tendsTo`**, **`CetaW_re/im_full_tendsTo`** — the partial sums converge to `CetaW`.
- **`CetaW_czEtaSum_re/im_tendsTo`** — ties `CetaW` to the *genuine* alternating partial sums `czEtaSum`
  (de-orphaning `czEtaSum_two_eq_paired`); this is the precise sense in which `CetaW = η(s)`.
- **`CetaW_re/im_canonical`** — `CetaW` is independent of the positivity witness (well-defined).

### Uniqueness of the ζ quotient
- **`etaDenom_cancel`** — with the denominator non-vanishing, any two solutions of `(1−2^{1−s})·z ≈ w`
  are `≈`-equal; so `CzetaStripW` is *the* value pinned by the functional relation, not merely *a* solution.

### Cleanups / honesty
- Deleted the gratuitous `RnatQ` (duplicated `RofNat`, which is already in scope; its justifying comment
  was false).
- Strengthened the `RrpowPos` positivity API: **`Pos_RrpowPos_of_nonneg_log`** (`x^y > 0` from
  `Rnonneg y` and `Rnonneg (RlogPos x)`).
- Softened over-claims: `CzetaStrip_functional` is the *algebraic* relation (no analyticity is
  formalized); the file no longer claims to *characterize* the zero-locus of `1 − 2^{1−s}` (it proves the
  `Re s < 1` non-vanishing it needs); `Ceta`/`CetaW` are described as the Bishop limit of the reindexed
  paired partial sums, with the `czEtaSum` tie cited; the Spouge docstring says "approximates" (not `≈`)
  and loudly states the `N = ⌈a⌉−1` caller obligation and that the error bound is cited, not formalized.
- Corrected a comment that claimed `ring_uor` discharged proofs that are in fact hand-rolled `Req_trans`
  chains (forced, because `Radd`/`Rsub` reindex their operands).

### Positivity API completed to the base-≥1 form
`log x ≥ 0` for `x ≥ 1` is now a genuine theorem — **`Rnonneg_RlogPos`** — proved *without* the general
real `exp∘log = id` (which the codebase has only for `nat`), via the **artanh-sign route**: the rational
negative-argument artanh lower bound **`artSum_ge_neg_two_arg`** (`|t| ≤ ½ ⟹ artSum t N ≥ −2|t|`, from
the oddness `artSum_neg` + the geometric cap `artSum_le_two_arg`), lifted by **`Rnonneg_Rartanh_of_nonneg`**
(the key insight: `Rnonneg t` forces each negative per-index argument to be order `1/(Rⱼ+1) ≤ ½`, so the
small-argument bound always applies — no radius slack needed), composed through `tmap` and the `Rlog`/
`RlogPos` def-bridge. Hence the strongest positivity lemma **`Pos_RrpowPos_of_base_ge_one`**
(`x^y > 0` from `Rnonneg y` and `x ≥ 1`) now holds outright. Nothing in v0.16.0 is deferred.

## Standing scope (unchanged)

The crux `liPositivityHolds`/`hodgeIndexHolds` stay `none`; `Pos λ₂` is **evidence** for Li's criterion
at `n = 2`, not the crux. `λₙ > 0 ∀ n` (= RH), the off-critical-line zeros, and analyticity remain
out of scope. **RH stays open.** Every theorem is choice-free (`{propext, Quot.sound}`), audited in
`scripts/audit_axioms.lean`; the build is green.
