/-
F1 square — v0.21.0 stage G, brick **G3 (assembly and adjudication)**: the missing-object
embedding route, located; the crux fields stay `none`.

ROADMAP §8 (Stage 3) and §9. The embedding route is built end to end across bricks S, G0b, G0a,
G0, G1, G2a, G2b. This brick reads the gate and records the terminal state. Per §9 the program
terminates in one of two faithful states — Closed or Localized — and ships whichever it reaches.

THE VERDICT: LOCALIZED (§9). The route is complete and the two gates are located, but the crux did
NOT close, for the reasons the program itself predicts:

- **Gate A IS RH** (`stageG_frontier_located.1`): a diagonal match for the genuine square proves
  `LiNonneg (genuineLamSeq)` — the difficulty did not leave Gate A (§4.1), so it is not provable
  here; the §6 relocation shows the obvious zero-built candidate is circular.
- **Gate B is free at finite rank** (`.2`) but its INFINITE limit is obstructed by any negative
  signature entry (`.4`), and the atlas signature `Σ` is unsourced in F1 (§10) — so the make-or-break
  is not decided in the closing direction.
- The full-form bridge (`.3`) is the exact route a closure would travel (`−B` PSD ⟹ Hodge nonneg),
  but its hypothesis is RH-equivalent and not asserted.

So positivity is not output, the crux fields stay `none`, and RH stays open — exactly the bright
line. `stageG_frontier_located` packages this as one adjudication theorem, the v0.21.0 analog of
`genuine_crux_frontier_located`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.GaugeTower
import F1Square.Square.GateA
import F1Square.Square.FrobForm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

/-- **STAGE G ADJUDICATION** — the missing-object embedding route, located (the §9 "Localized"
    terminal state). One theorem packaging the five load-bearing facts:

    1. **Gate A is RH** — a diagonal match for the genuine square proves `LiNonneg (genuineLamSeq)`;
    2. **Gate B is free** at every finite rank — the atlas pairing is a manifest sum of squares;
    3. **the full-form bridge** — negative-semidefiniteness of the whole form `−B` gives Hodge
       nonnegativity (the route a closure would travel; its hypothesis is RH-equivalent);
    4. **the make-or-break obstruction** — any negative signature entry kills the infinite limit's
       positive-semidefiniteness (Gate B fails there);
    5. **the §6 relocation** — a zero-built candidate's match is exactly RH, not a free win.

    The difficulty is conserved (§4.1): it lives in Gate A (RH) and in the infinite limit's
    signature (unsourced). Nothing here asserts positivity; the crux fields stay `none`. -/
theorem stageG_frontier_located :
    (∀ (E : StieltjesEta) (ι : AtlasRule) (D : Nat),
        GateA E ι D → LiNonneg (genuineLamSeq E.eta))
    ∧ (∀ (ι : AtlasRule) (D : Nat), WeilPSD (atlasPair ι D))
    ∧ (∀ (S : SpectralSquare) (F : FullForm S), WeilPSD F.neg → SpectralHodgeNeg S)
    ∧ (∀ (B : Nat → Nat → Real) (n : Nat), Pos (Rneg (B n n)) → ¬ LimitPSD B)
    ∧ (∀ isZero : Complex → Prop,
        (∀ z, isZero z → Req (csubOneNormSq z) (cnormSq z)) ↔ AllZerosOnLine isZero) :=
  ⟨gateA_is_liNonneg, atlasPair_psd, fun _ F h => FullForm.negPSD_to_hodgeNeg F h,
   limit_indefinite_of_neg_signature, cayley_relocation⟩

end UOR.Bridge.F1Square.Square
