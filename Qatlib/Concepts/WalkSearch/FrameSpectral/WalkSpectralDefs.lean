/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilationDefs
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormStat

/-!
# Frame norm and detector endpoint specifications

This module defines the graph access, empty marked set, and frame norm propositions used by the
spectral endpoint theorems. `SzegedyTheorem5Unified` combines the interior correspondence with
the normalized intersection case.

The detector definitions describe marker and flag shear permutations and the common slice
operators required by `RowPreservingAccess`. `WalkSpectral3Clause39FullEndpoint` collects their
involutivity, branch action, cancellation, and repeated walk parity requirements. These results
concern the quantum walk framework of [Szegedy2004].

## Main statements

* `SzegedyTheorem5Unified`: The interior and normalized intersection norm requirements.
* `RowPreservingAccess`: Common forward and backward row slice operators.
* `WalkSpectral3Clause39FullEndpoint`: The combined spectral and detector branch specification.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.WalkSearch.Detection

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander

/-- The conjunction of graph setup and reachable dynamics for transition matrices, the countable
exact gate cover obstruction, and finite graph bit access. -/
def Clause1Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I),
    IsTransitionMatrix P →
      GraphSetupAccount P S ∧
      WalkPreservesReachableSpan P ∧
      ReachableTwoPlaneLaw P) ∧
  noCountableExactGateCover ∧
  (∀ (n d : ℕ) (hdn : d ≤ n) (adj : Fin n → Fin n → Bool) (M : Fin n → Bool),
    HasGraphBitAccess n d hdn adj M)

/-- The conjunction of the two empty marked set search impossibility statements and zero success
probability for the corresponding Szegedy walk search. -/
def Clause2Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (Sc Uc Cc bound : ℝ),
    ¬ HasRealElementFind P ∅ Sc Uc Cc bound) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P : I → I → ℝ) (Sc Uc Cc bound : ℝ),
    ¬ HasWalkFind P ∅ Sc Uc Cc bound) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P : I → I → ℝ) (Mq k t : ℕ),
    walkFindSuccessProb (SzegedyWalk P) (detectionInitial P)
      (edgeMarkedSet (∅ : Finset I)) Mq k t = 0)

/-- The requirement that a common image of two isometric frames is fixed by their bipartite walk
and has self inner product one when the first source is normalized [Szegedy, Theorem
5][Szegedy2004]. -/
def SzegedyTheorem5IntersectionNorm : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
    ∀ (a : QState I) (b : QState J),
      Normalized a → A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a ∧
      Qatlib.Foundations.PureStateMath.Inner (A *ᵥ a) (A *ᵥ a) = ((1 : ℝ) : ℂ)

/-- The conjunction of the interior norm correspondence and the normalized intersection
fixed-state statement [Szegedy, Theorem 5][Szegedy2004]. -/
def SzegedyTheorem5Unified : Prop :=
  SzegedyTheorem5InteriorNorm ∧ SzegedyTheorem5IntersectionNorm

/-- The conjunction of the unified frame norm statement and vanishing of the tau map at the +1
source endpoint. -/
def Clause3Spec : Prop :=
  SzegedyTheorem5Unified ∧
  BipartiteTauEndpointVanishes

/-- The permutation toggling the detector flag when the first vertex is marked, while preserving
the outer control and vertex registers. -/
noncomputable def printedMarkerOnUncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (v : DetectionSpace I) : DetectionSpace I :=
  if decide (v.2.2.1 ∈ S) then (v.1, !v.2.1, v.2.2) else v

/-- The permutation fixing the false control branch and toggling the flag on the true branch
exactly when the two vertices have different marked membership. -/
noncomputable def printedFlagShear {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (v : DetectionSpace I) : DetectionSpace I :=
  if v.1 = false then v
  else if decide (v.2.2.1 ∈ S) != decide (v.2.2.2 ∈ S) then (v.1, !v.2.1, v.2.2)
  else v

/-- Applying the printed flag shear twice returns the original detector index. -/
theorem printedFlagShear_involutive {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) : Function.Involutive (printedFlagShear S) := by
  intro v
  rcases v with ⟨b, c, xy⟩
  obtain ⟨x, y⟩ := xy
  by_cases hb : b = false
  · simp [printedFlagShear, hb]
  · by_cases h : decide (x ∈ S) != decide (y ∈ S)
    · simp [printedFlagShear, hb, h]
    · simp [printedFlagShear, hb, h]

/-- Applying the printed marker permutation twice returns the original detector index. -/
theorem printedMarkerOnUncontrolled_involutive {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) : Function.Involutive (printedMarkerOnUncontrolled S) := by
  intro v
  rcases v with ⟨b, c, xy⟩
  obtain ⟨x, y⟩ := xy
  by_cases h : decide (x ∈ S)
  · simp [printedMarkerOnUncontrolled, h]
  · simp [printedMarkerOnUncontrolled, h]

/-- The condition that `U` and its adjoint act on every row slice through common matrices `V`
and `W`, respectively, with `V * W = 1`. -/
def RowPreservingAccess {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) : Prop :=
  ∃ V W : Matrix I I ℂ,
    (∀ (f : I × I → ℂ) (x y : I), (U *ᵥ f) (x, y) = (V *ᵥ (fun e ↦ f (x, e))) y) ∧
    (∀ (f : I × I → ℂ) (x y : I), (Uᴴ *ᵥ f) (x, y) = (W *ᵥ (fun e ↦ f (x, e))) y) ∧
    V * W = 1

/-- The conjunction of the unified norm and tau endpoint statements with printed and corrected
detector branch laws, unitary row access cancellation, and row preserving flag shear and
parity formulas. -/
def WalkSpectral3Clause39FullEndpoint : Prop :=
  SzegedyTheorem5Unified ∧
  BipartiteTauEndpointVanishes ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
      (v : QState (DetectionSpace I)),
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIReflectionWord j) *ᵥ v) (false, c, xy)
        = (detectionMarkGate S *ᵥ v) (false, c, xy)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
      (v : QState (DetectionSpace I)),
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ v) (false, c, xy)
        = v (false, c, xy)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (S : Finset I),
    Function.Involutive (printedFlagShear S)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
      (v : QState (DetectionSpace I)),
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (detectionReflectionWord j) *ᵥ v) (false, c, xy)
        = v (false, c, xy)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I) (K : ℕ)
      (v : QState (DetectionSpace I)),
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (List.replicate K (plusIWalkWord j)).flatten *ᵥ v) (false, c, xy)
        = v (false, c, xy)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ),
    (detectionInstruction U S .rowForward) * (detectionInstruction U S .rowBackward) = 1) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I),
    RowPreservingAccess U →
    ∀ (v : QState (DetectionSpace I)) (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ v) (true, c, xy)
        = v (printedFlagShear S (true, c, xy))) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I),
    RowPreservingAccess U →
    ∀ (K : ℕ) (v : QState (DetectionSpace I)),
      (detectionEvaluate U S (List.replicate K (plusIWalkWord j)).flatten *ᵥ v)
        = if K % 2 = 0 then v
          else (detectionEvaluate U S (plusIWalkWord j) *ᵥ v))

end Qatlib.Concepts.WalkSearch.FrameSpectral
