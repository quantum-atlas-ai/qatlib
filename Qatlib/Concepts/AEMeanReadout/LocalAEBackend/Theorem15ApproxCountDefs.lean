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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

noncomputable def basicApproxCountLoopCap (N : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (2*Real.sqrt (N : ℝ)))

noncomputable def basicApproxCountLoopLaw {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (l : Fin (basicApproxCountLoopCap N)) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin (2*2^l.val)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (2*2^l.val) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0,hN⟩ : Fin N) S
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) (by
      have h0 : 0 < 2^l.val := by positivity
      omega)

noncomputable def basicApproxCountObserved (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (l : Fin (basicApproxCountLoopCap N)) : ℝ :=
  (N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (2*2^l.val) (ω l)

noncomputable def basicApproxCountStop (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℕ :=
  match Fin.find? (fun l : Fin (basicApproxCountLoopCap N) =>
      decide (basicApproxCountObserved N ω l ≠ 0)) with
  | some l => l.val+1
  | none => basicApproxCountLoopCap N

noncomputable def basicApproxCountFinalM (ε : ℝ) (s : ℕ) : ℕ :=
  Nat.ceil (20*Real.pi^2/ε*(2^s : ℝ))

noncomputable def basicApproxCountFinalLaw {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (basicApproxCountFinalM ε (basicApproxCountStop N ω))
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0,hN⟩ : Fin N) S
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hω

noncomputable def basicApproxCountOutput (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate
    (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y+1/2⌋

noncomputable def basicApproxCountPrefixWeight {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℝ :=
  ∏ l : Fin (basicApproxCountLoopCap N),
    (basicApproxCountLoopLaw hN S l).prob (ω l)

noncomputable def basicApproxCountFinalZero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      basicApproxCountOutput N ε ω y = 0),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

noncomputable def basicApproxCountFinalGood {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      |((basicApproxCountOutput N ε ω y : ℝ))-(S.card : ℝ)| ≤ ε*(S.card : ℝ)),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
