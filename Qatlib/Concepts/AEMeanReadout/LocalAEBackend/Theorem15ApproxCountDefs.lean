/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Basic Approx Count record and stopping definitions

This module defines the finite record model of Basic Approx Count from [BrassardEtAl2002]. The
loop uses geometrically increasing amplitude estimation grids, stops at the first nonzero
observed estimate or at a finite cap, and chooses a final grid from the stopping index and
requested relative precision.

The record weights form a product of loop-label probabilities. Final success is represented by
separate masses for output zero and for integer outputs within the relative-error target.

## Main definitions

* `basicApproxCountStop`: the first nonzero observation index, counted from one, or the loop
  cap.
* `basicApproxCountFinalM`: the rounded final grid size.
* `basicApproxCountPrefixWeight`: the product weight of a complete loop record.
* `basicApproxCountFinalGood`: the conditional final relative-error success mass.

## References

* [Brassard et al., Theorem 15][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The finite loop cap obtained by taking the natural ceiling of `log₂ (2 * √N)`. -/
noncomputable def basicApproxCountLoopCap (N : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (2*Real.sqrt (N : ℝ)))

/-- The uniform-preparation amplitude estimation label law at loop grid size `2 * 2^l.val`. -/
noncomputable def basicApproxCountLoopLaw {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (l : Fin (basicApproxCountLoopCap N)) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin (2*2^l.val)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (2*2^l.val) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0,hN⟩ : Fin N) S
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) (by
      have h0 : 0 < 2^l.val := by positivity
      omega)

/-- The real count estimate `N` times the amplitude readout in loop record `ω` at index `l`. -/
noncomputable def basicApproxCountObserved (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (l : Fin (basicApproxCountLoopCap N)) : ℝ :=
  (N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (2*2^l.val) (ω l)

/-- One plus the first loop index with a nonzero observed count, or the loop cap if every
observation is zero. -/
noncomputable def basicApproxCountStop (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℕ :=
  match Fin.find? (fun l : Fin (basicApproxCountLoopCap N) =>
      decide (basicApproxCountObserved N ω l ≠ 0)) with
  | some l => l.val+1
  | none => basicApproxCountLoopCap N

/-- The natural ceiling of `20 * π² * 2^s / ε`, used as the final Basic Approx Count grid size. -/
noncomputable def basicApproxCountFinalM (ε : ℝ) (s : ℕ) : ℕ :=
  Nat.ceil (20*Real.pi^2/ε*(2^s : ℝ))

/-- The uniform-preparation amplitude estimation law at the final grid chosen from record `ω`,
assuming that grid has size at least two. -/
noncomputable def basicApproxCountFinalLaw {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (basicApproxCountFinalM ε (basicApproxCountStop N ω))
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0,hN⟩ : Fin N) S
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hω

/-- The integer rounding of the final amplitude estimate multiplied by `N`. -/
noncomputable def basicApproxCountOutput (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate
    (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y+1/2⌋

/-- The product probability of all loop labels in the finite record `ω`. -/
noncomputable def basicApproxCountPrefixWeight {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℝ :=
  ∏ l : Fin (basicApproxCountLoopCap N),
    (basicApproxCountLoopLaw hN S l).prob (ω l)

/-- The final-record probability of integer output zero, conditional on the loop record `ω`. -/
noncomputable def basicApproxCountFinalZero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      basicApproxCountOutput N ε ω y = 0),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

/-- The final-record probability of integer output within `ε * S.card` of the marked count,
conditional on the loop record `ω`. -/
noncomputable def basicApproxCountFinalGood {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      |((basicApproxCountOutput N ε ω y : ℝ))-(S.card : ℝ)| ≤ ε*(S.card : ℝ)),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
