/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector

/-!
# Bipartite spectral correspondence consumers

This module applies the bipartite source correspondence to prepared frame access and corrected
marked walks. `bipartite_prepared_labeled_spectrum_consumer` combines a labeled eigenframe with
exact access-program semantics and resource counts, while
`corrected_marked_walk_bipartite_bridge` identifies the marked construction with a bipartite
reflection walk.

The resulting `corrected_marked_busy_labeled_spectrum` describes the spectrum on the combined
frame range through endpoint sources and signed interior τ images, in the spectral framework of
[Szegedy2004].

## Main statements

* `bipartite_prepared_labeled_spectrum_consumer`: labeled spectrum and compiled walk powers.
* `corrected_marked_busy_labeled_spectrum`: labeled eigenframe for the corrected marked walk.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.TwoLevelLower

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Spectral
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For two isometric frames and unitary preparations, construct an orthonormal eigenframe on
their combined range with endpoint and signed interior source labels. The compiled access
program realizes each walk power on this frame with zero queries, `4 * k` preparation steps,
and `2 * k` other steps [Szegedy2004]. -/
theorem bipartite_prepared_labeled_spectrum_consumer {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ)
    (hF : IsIsometry F) (hG : IsIsometry G) (hU : U∈unitaryGroup H ℂ)
    (hV : V∈unitaryGroup H ℂ) :
    ∃ (m : ℕ) (X : Matrix H (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry X ∧
      X*Xᴴ=bipartiteTilde (U*F) (V*G)*matrixPseudoinverse (bipartiteTilde (U*F) (V*G)) ∧
      bipartiteWalk (U*F) (V*G)*X=X*diagonal z ∧
      m=(bipartiteTilde (U*F) (V*G)).rank ∧
      (∀ i : Fin m,
        (z i=1 ∧ ∃ u : QState (I⊕J), u≠0 ∧
          bipartiteDiscriminant (U*F) (V*G)*ᵥu=u ∧
          (fun h=>X h i)=bipartiteTilde (U*F) (V*G)*ᵥu) ∨
        (z i=-1 ∧ ∃ u : QState (I⊕J), u≠0 ∧
          bipartiteDiscriminant (U*F) (V*G)*ᵥu=0 ∧
          (fun h=>X h i)=bipartiteTilde (U*F) (V*G)*ᵥu) ∨
        (∃ lam : ℝ, 0<lam ∧ lam<1 ∧ ∃ (s : Bool) (u : QState (I⊕J)),
          u≠0 ∧ bipartiteDiscriminant (U*F) (V*G)*ᵥu=(lam:ℂ)•u ∧
          z i=bipartitePhase lam s ∧
          (fun h=>X h i)=bipartiteTauLinear (U*F) (V*G) lam s u)) ∧
      ∀ k : ℕ,
        IsUnitaryCircuit (compileBipartiteAccess F G U V (bipartiteAccessProgram k)) ∧
        QueryCount (compileBipartiteAccess F G U V (bipartiteAccessProgram k))=0 ∧
        GateCount (compileBipartiteAccess F G U V (bipartiteAccessProgram k))=4*k+2*k ∧
        (bipartiteAccessProgram k).countP BipartiteAccessStep.isPrepare=4*k ∧
        (bipartiteAccessProgram k).countP (fun s=>!s.isPrepare)=2*k ∧
        ∀ v : QState (Fin m),
          Run 1 (compileBipartiteAccess F G U V (bipartiteAccessProgram k)) (X*ᵥv)=
            X*ᵥ((diagonal z)^k*ᵥv) := by
  have hUF : IsIsometry (U*F) := by
    change (U*F)ᴴ*(U*F)=1
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U,
      show Uᴴ*U=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hU.1,Matrix.one_mul]
    exact hF
  have hVG : IsIsometry (V*G) := by
    change (V*G)ᴴ*(V*G)=1
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Vᴴ V,
      show Vᴴ*V=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hV.1,Matrix.one_mul]
    exact hG
  obtain ⟨m,X,z,hX,hXX,hWX,hm,hlabels⟩ :=
    bipartite_labeled_busy_spectral_frame H I J (U*F) (V*G) hUF hVG
  refine ⟨m,X,z,hX,hXX,hWX,hm,hlabels,?_⟩
  exact bipartite_actual_spectral_access_program F G U V X z hF hG hU hV hWX

/-- The reflection associated with a swapped frame is the conjugate of the original frame
reflection by the swap gate. -/
private theorem tau_swap_reflection_conj {I U : Type} [Fintype I] [DecidableEq I]
    [Fintype U] [DecidableEq U] (F : Matrix (I×I) U ℂ) :
    ReflectionAbout (((SwapGate : Matrix (I×I) (I×I) ℂ)*F)*
        (((SwapGate : Matrix (I×I) (I×I) ℂ)*F))ᴴ) =
      SwapGate*ReflectionAbout (F*Fᴴ)*SwapGate := by
  rw [Matrix.conjTranspose_mul, swapGate_hermitian]
  simp only [ReflectionAbout, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, swapGate_mul_self]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- For a symmetric transition matrix, identify the corrected marked walk with the bipartite
walk of the unmarked row frame and its swap, and identify the discriminant with the
off-diagonal unmarked principal blocks. -/
theorem corrected_marked_walk_bipartite_bridge :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I),
    IsTransitionMatrix P → (∀ i j, P i j = P j i) →
    correctedMarkedWalk P S =
      bipartiteWalk (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S) ∧
    bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S) =
      Matrix.fromBlocks 0 (unmarkedPrincipal P S) (unmarkedPrincipal P S) 0 := by
  intro I _ _ P S hP hsym
  constructor
  · rw [correctedMarkedWalk, bipartiteWalk]
    congr 1
    exact (tau_swap_reflection_conj (unmarkedRowFrame P S)).symm
  · have hgram := unmarkedRowFrame_swap_gram P S hP hsym
    have htop : (unmarkedRowFrame P S)ᴴ * ((SwapGate : Matrix (I×I) (I×I) ℂ) * unmarkedRowFrame P S) =
        unmarkedPrincipal P S := by rw [← Matrix.mul_assoc,hgram]
    have hbottom : ((SwapGate : Matrix (I×I) (I×I) ℂ) * unmarkedRowFrame P S)ᴴ * unmarkedRowFrame P S =
        unmarkedPrincipal P S := by
      rw [Matrix.conjTranspose_mul,swapGate_hermitian,Matrix.mul_assoc,htop]
    unfold bipartiteDiscriminant
    change Matrix.fromBlocks 0
      ((unmarkedRowFrame P S)ᴴ * ((SwapGate : Matrix (I×I) (I×I) ℂ) * unmarkedRowFrame P S))
      (((SwapGate : Matrix (I×I) (I×I) ℂ) * unmarkedRowFrame P S)ᴴ * unmarkedRowFrame P S) 0 = _
    rw [htop,hbottom]

/-- For a symmetric transition matrix, construct an orthonormal eigenframe of the corrected
marked walk on the combined frame range, with dimension equal to its rank and explicit
endpoint and signed interior source labels [Szegedy2004]. -/
theorem corrected_marked_busy_labeled_spectrum :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I),
    IsTransitionMatrix P → (∀ i j, P i j = P j i) →
    ∃ (m : ℕ) (V : Matrix (I×I) (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry V ∧
      V*Vᴴ = bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*
        matrixPseudoinverse
          (bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)) ∧
      correctedMarkedWalk P S*V = V*Matrix.diagonal z ∧
      m = Matrix.rank
          (bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)) ∧
      ∀ i : Fin m,
        (z i = 1 ∧ ∃ u : QState (Unmarked I S⊕Unmarked I S), u ≠ 0 ∧
          bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*ᵥu = u ∧
          (fun h => V h i) =
            bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*ᵥu) ∨
        (z i = -1 ∧ ∃ u : QState (Unmarked I S⊕Unmarked I S), u ≠ 0 ∧
          bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*ᵥu = 0 ∧
          (fun h => V h i) =
            bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*ᵥu) ∨
        (∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ ∃ (s : Bool) (u : QState (Unmarked I S⊕Unmarked I S)),
          u ≠ 0 ∧
          bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)*ᵥu =
            (lam:ℂ)•u ∧
          z i = bipartitePhase lam s ∧
          (fun h => V h i) =
            bipartiteTauLinear (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S) lam s u) := by
  intro I _ _ P S hP hsym
  let F := unmarkedRowFrame P S
  have hF : IsIsometry F := unmarkedRowFrame_isIsometry P S hP
  have hSF : IsIsometry ((SwapGate : Matrix (I×I) (I×I) ℂ)*F) := by
    change ((SwapGate : Matrix (I×I) (I×I) ℂ)*F)ᴴ * (SwapGate*F)=1
    calc
      _ = Fᴴ * ((SwapGate : Matrix (I×I) (I×I) ℂ)*SwapGate) * F := by
        rw [Matrix.conjTranspose_mul,swapGate_hermitian]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [swapGate_mul_self,Matrix.mul_one]; exact hF
  obtain ⟨m,V,z,hV,hVV,hWV,hm,hlabels⟩ := bipartite_labeled_busy_spectral_frame
    (I×I) (Unmarked I S) (Unmarked I S) F (SwapGate*F) hF hSF
  refine ⟨m,V,z,hV,hVV,?_,hm,hlabels⟩
  rw [(corrected_marked_walk_bipartite_bridge I P S hP hsym).1]
  exact hWV

end Qatlib.Concepts.WalkSearch.Spectral
