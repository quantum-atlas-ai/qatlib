/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.OracleTransport
import Qatlib.Papers.QCounting98.MainResults.CountingWindow

/-!
# Standard Boolean-oracle amplitude-estimation program

This module defines `standardPaddedAEWord`, a Boolean-workspace implementation of the padded
amplitude-estimation circuit, together with its basis input `standardInput`. It proves exact
resource counts, unitarity, and agreement of the measured phase-label distribution with `aeLaw`,
providing a circuit realization of the counting analysis in [BrassardHoyerTapp1998Counting].

For the Fourier preparation on a domain of size `N`, `standard_theorem5` gives the strict
approximate-counting window with probability at least `8 / π²` and exactly `P` Boolean-oracle
queries.

## Main statements

* `standardPaddedAE_resources`: exact query and fixed-gate counts.
* `standardPaddedAE_unitary`: unitarity for a unitary state preparation.
* `standardPaddedAE_label`: the circuit readout agrees with `aeLaw`.
* `standard_theorem5`: the approximate-counting probability bound for the standard program.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath.BornBridge (relabelState)
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The standard Boolean-workspace circuit obtained by compiling the padded amplitude-estimation
circuit for preparation `A` and basis index `j`. -/
def standardPaddedAEWord (M : ℕ) (A : Matrix I I ℂ) (j : I) : Circuit ((I × Bool) × Fin M) :=
  standardAEWord M (aePaddedAECircuit M A j)

/-- The standard amplitude-estimation input with data index `j`, answer bit `false`, and phase
label zero, expressed using the workspace label order. -/
def standardInput (M : ℕ) (hM : 2 ≤ M) (j : I) : QState ((I × Bool) × Fin M) :=
  relabelState (aeStandardLabels I M)
    (TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (Ket j)))

section
omit [Fintype I]

/-- The standard input is the basis ket with data index `j`, answer bit `false`, and phase label
zero. -/
theorem standardInput_basis (M : ℕ) (hM : 2 ≤ M) (j : I) :
    standardInput M hM j = Ket ((j,false),(⟨0,by omega⟩ : Fin M)) := by
  ext ⟨⟨i,b⟩,z⟩
  simp only [standardInput,relabelState,aeStandardLabels,Function.comp_apply,TensorState,
    Qatlib.Foundations.PureStateMath.Ket,
    Prod.mk.injEq]
  by_cases hi : i = j <;> by_cases hb : b = false <;>
    by_cases hz : z = (⟨0,by omega⟩ : Fin M) <;> simp_all

end

/-- For phase precision at least two, the standard input state is normalized. -/
theorem standardInput_normalized (M : ℕ) (hM : 2 ≤ M) (j : I) :
    Normalized (standardInput M hM j) := by
  rw [standardInput_basis]
  exact normalized_ket _

section
omit [DecidableEq I]

/-- Relabeling the phase-first event with phase label `z` gives the workspace event whose final
coordinate is `z`. -/
theorem standard_label_event (M : ℕ) (z : Fin M) :
    (Finset.univ.filter (fun p : Fin M × (Bool × I) => p.1 = z)).map
        (aeStandardLabels I M).toEmbedding =
      Finset.univ.filter (fun p : (I × Bool) × Fin M => p.2 = z) := by
  ext q
  simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hq
    exact ⟨(aeStandardLabels I M).symm q,hq,(aeStandardLabels I M).apply_symm_apply q⟩

end

/-- For `M > 0`, the standard padded circuit uses exactly `M` queries and `5 * (M - 1) + 3 + 2 *
M` fixed gates. -/
theorem standardPaddedAE_resources (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (standardPaddedAEWord M A j) = M ∧
      GateCount (standardPaddedAEWord M A j) = 5*(M-1)+3+2*M := by
  have h := padded_query_exact_M M hM A j
  constructor
  · rw [standardPaddedAEWord,standardAE_queries,h.1]
  · rw [standardPaddedAEWord,standardAE_gates,h.1,h.2]

/-- For unitary `A` and phase precision at least two, the standard padded amplitude-estimation
circuit is unitary. -/
theorem standardPaddedAE_unitary (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : IsUnitaryCircuit (standardPaddedAEWord M A j) := by
  apply standardAE_unitary
  have h := (prepared_ae_expanded_access_and_output M hM A j ∅ hA).2.2.1
  simpa only [aePaddedAECircuit,isUnitaryCircuit_append,isUnitaryCircuit_query,
    isUnitaryCircuit_nil,and_true] using! h

/-- For unitary `A` and phase precision at least two, executing the standard padded circuit with
the Boolean workspace oracle on `standardInput` yields a normalized state. -/
theorem standardPaddedAE_normalized (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → Bool) :
    Normalized (Run (workspaceBitOracle f) (standardPaddedAEWord M A j) (standardInput M hM j)) :=
  (standardPaddedAE_unitary M hM A j hA).normalized_run (workspaceBitOracle_unitary f)
    (standardInput_normalized M hM j)

/-- For unitary `A` and phase precision at least two, the probability of phase label `z` in the
standard execution equals the corresponding value of `aeLaw` for `sourceMarked f`. -/
theorem standardPaddedAE_label (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → Bool) (z : Fin M) :
    MeasureProb (Run (workspaceBitOracle f) (standardPaddedAEWord M A j) (standardInput M hM j))
        (Finset.univ.filter (fun p => p.2 = z)) =
      (aeLaw M A j (sourceMarked f) hA hM).prob z := by
  have h := standardAE_readout M f (aePaddedAECircuit M A j)
    (TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (Ket j)))
    (Finset.univ.filter (fun p => p.1 = z))
  rw [standard_label_event] at h
  change _ = (aeLaw M A j (sourceMarked f) hA hM).prob z
  exact h.trans (aePaddedLaw_prob M A j (sourceMarked f) hA hM z)

/-- For `N > 0`, marked count `t = (levelSet F).card ≤ N / 2`, and `P ≥ 4`, the standard circuit
uses exactly `P` queries and has count-estimation error strictly below `2π * sqrt (t * N) /
P + π² * N / P²` with probability at least `8 / π²`. This realizes [Brassard et al., Theorem
5][BrassardHoyerTapp1998Counting] with the Boolean workspace oracle. -/
theorem standard_theorem5 (N P : ℕ) (F : Fin N → Bool) (hN : 0 < N)
    (ht : (levelSet F).card ≤ N/2) (hP : 4 ≤ P) :
    QueryCount (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩) = P ∧
      8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N : ℝ)*aeEstimate P z-((levelSet F).card : ℝ)| <
          2*Real.pi/(P : ℝ)*Real.sqrt (((levelSet F).card : ℝ)*(N : ℝ)) +
            Real.pi^2/(P : ℝ)^2*(N : ℝ)),
        MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩)
          (standardInput P (by omega) ⟨0,hN⟩)) (Finset.univ.filter (fun p => p.2 = z)) := by
  refine ⟨(standardPaddedAE_resources P (by omega) (QFTMatrix N) ⟨0,hN⟩).1,?_⟩
  simp_rw [standardPaddedAE_label P (by omega) (QFTMatrix N) ⟨0,hN⟩ (qftMatrix_unitary hN)]
  exact source_theorem5_approximate_counting N P F hN ht hP

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
