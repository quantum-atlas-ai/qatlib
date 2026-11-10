/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManifoldInv07.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.ManifoldInv07.MainResults.AutomatonRecognition

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ManifoldInv07.MainResults.Defs

def acceptanceProbability {I : Type*} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (p0 : I) : ℝ :=
  BornProb (ApplyGate U (Ket p0)) p0

def jonesDistribution (Jpoly : ℂ) : ℝ := ‖Jpoly‖ ^ 2

theorem jones_automaton_recognizes_exactly {I : Type*} [Fintype I] [DecidableEq I]
    (p0 : I) (U : Matrix I I ℂ) (Jpoly : ℂ)
    (hKaul : Inner (Ket p0) (ApplyGate U (Ket p0)) = Jpoly) :
    |jonesDistribution Jpoly - acceptanceProbability U p0| = 0 := by
  have hval : (ApplyGate U (Ket p0)) p0 = Jpoly := by
    rw [← hKaul, inner_ket_left]
  unfold jonesDistribution acceptanceProbability BornProb
  rw [hval, sub_self, abs_zero]

theorem jones_automaton_threshold_zero {I : Type*} [Fintype I] [DecidableEq I]
    (p0 : I) (U : Matrix I I ℂ) (Jpoly : ℂ)
    (hKaul : Inner (Ket p0) (ApplyGate U (Ket p0)) = Jpoly) :
    |jonesDistribution Jpoly - acceptanceProbability U p0| ≤ (0 : ℝ) := by
  rw [jones_automaton_recognizes_exactly p0 U Jpoly hKaul]

theorem colored_automaton_recognizes_exactly {Color I : Type*}
    [Fintype Color] [Fintype I] [DecidableEq I]
    (p0 : I) (U : Color → Matrix I I ℂ) (Jpoly : Color → ℂ)
    (hKaul : ∀ c, Inner (Ket p0) (ApplyGate (U c) (Ket p0)) = Jpoly c) :
    ∀ c, |jonesDistribution (Jpoly c) - acceptanceProbability (U c) p0| = 0 :=
  fun c => jones_automaton_recognizes_exactly p0 (U c) (Jpoly c) (hKaul c)

end Qatlib.Papers.ManifoldInv07.MainResults.AutomatonRecognition
