/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.VariableTimeAmplification

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 3 — the amplification-product bound

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Lemma 3 is printed on p.7, proof p.7–9.

Source statement (as printed, `p_stop,>i` the stopping mass strictly after
stage `i`, `p_succ` the success probability of the whole run):

  `∏_{j=i}^{m} √(r_j/r_j′) ≤ 3·(1 + √(p_stop,>i / p_succ))`.   (Lemma 3)

The printed product starts at the reference stage `i` itself.  The source's
Algorithm 2 does **not** bound the stage-`i` gain `√(r_i/r_i′)`: the overlap
chain whose recursion the proof uses runs from `i+1` to `m`.  The honest
Lean statement therefore splits Lemma 3 into its proof-controlled core

  `∏_{j=i+1}^{m} √(r_j/r_j′) ≤ 3·(1 + √(p_stop,>i / p_succ))`,

and the exact factorization of the printed product into that core times the
stage-`i` gain.  Together these two facts are precisely what the source's
argument establishes and what its statement consumes; the extra factor is
exposed rather than silently dropped.

Frozen reuse:
`QuantumAlgorithm.Papers.VarTimeAmpAmp10.MainTheorem.clause68_endpoint`
(core, from the `VtOverlapChain` telescoping) and
`...MainTheorem.lemma3_product_bound_with_stage_gain` (the factorization).
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

/-- Fixed arXiv:1010.4458v2, Lemma 3, proof-controlled core (printed p.7).

The stage gains strictly after the reference stage `i` obey the source's
`3·(1 + √(p_stop,>i / p_succ))`.  This is the product the source's overlap
recursion actually controls. -/
theorem source_lemma3_core {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
        (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1)
      ≤ lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc :=
  clause68_endpoint oc hm h1 h2

/-- Fixed arXiv:1010.4458v2, Lemma 3, printed product (printed p.7).

The printed product `∏_{j=i}^{m} √(r_j/r_j′)` equals the stage-`i` gain
`√(r_i/r_i′)` times the proof-controlled product over `j > i`.  This is the
exact content of the source's factorization and shows where the extra gain
factor of the printed lemma comes from. -/
theorem source_lemma3_factorization {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
        (fun j => (oc.chain.stage j).baseWeight) i (m + 1)
      = gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
        gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1) :=
  lemma3_product_bound_with_stage_gain oc hm h1 h2

/-- Fixed arXiv:1010.4458v2, Lemma 3, printed product bounded with the stage-`i`
gain exposed.

Combining the factorization with the core bound gives

  `∏_{j=i}^{m} √(r_j/r_j′) ≤ √(r_i/r_i′)·3·(1 + √(p_stop,>i / p_succ))`,

i.e. the printed Lemma 3 conclusion up to the stage-`i` gain that the source's
Algorithm 2 leaves unbounded. -/
theorem source_lemma3_printed_bound {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
        (fun j => (oc.chain.stage j).baseWeight) i (m + 1)
      ≤ gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
        lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := by
  rw [source_lemma3_factorization oc hm h1 h2]
  refine mul_le_mul_of_nonneg_left (source_lemma3_core oc hm h1 h2) ?_
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
