/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedyCorrectedFoldedSpectrumStat

/-!
# Corrected marked walk folded spectrum

This module proves `SzegedyCorrectedFoldedSpectrum` for symmetric transition matrices. The
explicit equivalence `corrected_block_split` combines the positive and negative unmarked
principal eigenspaces by component sums and differences.

This source splitting yields the interior phase multiplicities and the two endpoint
multiplicities of the corrected walk on the combined frame range, in the spectral setting of
[Szegedy2004].

## Main statements

* `corrected_block_split`: explicit linear equivalence for folded source eigenspaces.
* `szegedyCorrectedFoldedSpectrum`: the complete folded-spectrum contract.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
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

set_option maxHeartbeats 2000000 in

/-- For a symmetric transition matrix, the product of the unmarked principal eigenspaces at
`lam` and `-lam` is linearly equivalent to the bipartite discriminant eigenspace at `lam`,
via the component sum and difference. -/
private theorem corrected_block_split (I : Type) [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P)
    (hsym : ∀ i j, P i j = P j i) (lam : ℝ) :
    ∃ e : (↥(LinearMap.ker
            ((unmarkedPrincipal P S-(lam:ℂ)•
              (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin')) ×
          ↥(LinearMap.ker
            ((unmarkedPrincipal P S+(lam:ℂ)•
              (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))) ≃ₗ[ℂ]
        ↥(LinearMap.ker
          ((bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)-
            (lam:ℂ)•
              (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin')),
      ∀ u, (e u).1 = Sum.elim (u.1.1+u.2.1) (u.1.1-u.2.1) := by
  classical
  set X := unmarkedPrincipal P S with hXdef
  set B := bipartiteDiscriminant (unmarkedRowFrame P S)
    ((SwapGate : Matrix (I×I) (I×I) ℂ)*unmarkedRowFrame P S) with hBdef
  obtain ⟨_, hdisc⟩ := corrected_marked_walk_bipartite_bridge I P S hP hsym
  have hdisc' : B = Matrix.fromBlocks (0 : Matrix (Unmarked I S) (Unmarked I S) ℂ) X X 0 :=
    hdisc
  have hblock : ∀ v : QState (Unmarked I S⊕Unmarked I S),
      B*ᵥv = Sum.elim (X*ᵥ(v ∘ Sum.inr)) (X*ᵥ(v ∘ Sum.inl)) := by
    intro v
    rw [hdisc', Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add, add_zero]
  have hmemf : ∀ u : QState (Unmarked I S), ∀ w : QState (Unmarked I S),
      X*ᵥu = (lam:ℂ)•u → X*ᵥw = -((lam:ℂ)•w) →
      (B-(lam:ℂ)•(1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ))*ᵥ
        (Sum.elim (u+w) (u-w)) = 0 := by
    intro u w hu hw
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero,
      hblock, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.mulVec_sub, Matrix.mulVec_add, hu, hw]
    have hsmul : (lam:ℂ) • (Sum.elim (u+w) (u-w)) =
        Sum.elim ((lam:ℂ)•(u+w)) ((lam:ℂ)•(u-w)) := by
      ext (b | b) <;> simp <;> ring
    rw [hsmul]
    congr 1
    · module
    · module
  have hsplit : ∀ x : QState (Unmarked I S⊕Unmarked I S),
      (B-(lam:ℂ)•(1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ))*ᵥx = 0 →
      X*ᵥ(x ∘ Sum.inl) = (lam:ℂ)•(x ∘ Sum.inr) ∧ X*ᵥ(x ∘ Sum.inr) = (lam:ℂ)•(x ∘ Sum.inl) := by
    intro x hx
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, hblock] at hx
    have hcomp := fun b => congrFun hx b
    constructor
    · funext i
      have hh := hcomp (Sum.inr i)
      simpa using! hh
    · funext j
      have hh := hcomp (Sum.inl j)
      simpa using! hh
  have hmemg₁ : ∀ x : QState (Unmarked I S⊕Unmarked I S),
      (B-(lam:ℂ)•(1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ))*ᵥx = 0 →
      X*ᵥ((1/2:ℂ)•(x ∘ Sum.inl+x ∘ Sum.inr)) =
        (lam:ℂ)•((1/2:ℂ)•(x ∘ Sum.inl+x ∘ Sum.inr)) := by
    intro x hx
    obtain ⟨h₁, h₂⟩ := hsplit x hx
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, h₂, h₁]
    module
  have hmemg₂ : ∀ x : QState (Unmarked I S⊕Unmarked I S),
      (B-(lam:ℂ)•(1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ))*ᵥx = 0 →
      X*ᵥ((1/2:ℂ)•(x ∘ Sum.inl-x ∘ Sum.inr)) =
        -((lam:ℂ)•((1/2:ℂ)•(x ∘ Sum.inl-x ∘ Sum.inr))) := by
    intro x hx
    obtain ⟨h₁, h₂⟩ := hsplit x hx
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, h₂, h₁]
    module
  have hf : ∀ uv : (↥(LinearMap.ker
          ((X-(lam:ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))) ×
        ↥(LinearMap.ker
          ((X+(lam:ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin')),
      Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1) ∈
      LinearMap.ker ((B-(lam:ℂ)•
        (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin') := by
    intro uv
    have hu : X*ᵥuv.1.1 = (lam:ℂ)•uv.1.1 := by
      have hh := uv.1.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec] at hh
      exact sub_eq_zero.mp hh
    have hw : X*ᵥuv.2.1 = -((lam:ℂ)•uv.2.1) := by
      have hh := uv.2.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec] at hh
      exact eq_neg_of_add_eq_zero_left hh
    exact LinearMap.mem_ker.mpr (hmemf uv.1.1 uv.2.1 hu hw)
  have hkerx : ∀ x : LinearMap.ker
        ((B-(lam:ℂ)•
          (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin'),
      (B-(lam:ℂ)•
        (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ))*ᵥx.1 = 0 := by
    intro x
    have htt := LinearMap.mem_ker.mp x.2
    rwa [Matrix.toLin'_apply] at htt
  have hg₁ : ∀ x : LinearMap.ker
        ((B-(lam:ℂ)•
          (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin'),
      ((1/2:ℂ)•(x.1 ∘ Sum.inl+x.1 ∘ Sum.inr)) ∈
      LinearMap.ker ((X-(lam:ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin') := by
    intro x
    refine LinearMap.mem_ker.mpr ?_
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hmemg₁ x.1 (hkerx x), sub_self]
  have hg₂ : ∀ x : LinearMap.ker
        ((B-(lam:ℂ)•
          (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin'),
      ((1/2:ℂ)•(x.1 ∘ Sum.inl-x.1 ∘ Sum.inr)) ∈
      LinearMap.ker ((X+(lam:ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin') := by
    intro x
    refine LinearMap.mem_ker.mpr ?_
    rw [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hmemg₂ x.1 (hkerx x)]
    module
  refine ⟨{
    toFun := fun uv => ⟨Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1), hf uv⟩
    map_add' := by
      intro uv wv
      apply Subtype.ext
      simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
      ext (i | j) <;> simp <;> ring
    map_smul' := by
      intro t uv
      apply Subtype.ext
      show Sum.elim (t•uv.1.1+t•uv.2.1) (t•uv.1.1-t•uv.2.1) =
        t • Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1)
      ext (b | b) <;> simp <;> ring
    invFun := fun x => (⟨(1/2:ℂ)•(x.1 ∘ Sum.inl+x.1 ∘ Sum.inr), hg₁ x⟩,
      ⟨(1/2:ℂ)•(x.1 ∘ Sum.inl-x.1 ∘ Sum.inr), hg₂ x⟩)
    left_inv := by
      intro uv
      apply Prod.ext <;> apply Subtype.ext
      · show (1/2:ℂ)•((Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1)) ∘ Sum.inl+
          (Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1)) ∘ Sum.inr) = uv.1.1
        rw [Sum.elim_comp_inl, Sum.elim_comp_inr]
        have h2 : uv.1.1+uv.2.1+(uv.1.1-uv.2.1) = (2:ℂ)•uv.1.1 := by module
        rw [h2, smul_smul]
        norm_num
      · show (1/2:ℂ)•((Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1)) ∘ Sum.inl-
          (Sum.elim (uv.1.1+uv.2.1) (uv.1.1-uv.2.1)) ∘ Sum.inr) = uv.2.1
        rw [Sum.elim_comp_inl, Sum.elim_comp_inr]
        have h2 : uv.1.1+uv.2.1-(uv.1.1-uv.2.1) = (2:ℂ)•uv.2.1 := by module
        rw [h2, smul_smul]
        norm_num
    right_inv := by
      intro x
      apply Subtype.ext
      show Sum.elim ((1/2:ℂ)•(x.1 ∘ Sum.inl+x.1 ∘ Sum.inr)+(1/2:ℂ)•(x.1 ∘ Sum.inl-x.1 ∘ Sum.inr))
          ((1/2:ℂ)•(x.1 ∘ Sum.inl+x.1 ∘ Sum.inr)-(1/2:ℂ)•(x.1 ∘ Sum.inl-x.1 ∘ Sum.inr)) = x.1
      funext b
      cases b with
      | inl i =>
        simp only [Sum.elim_inl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Function.comp_apply]
        ring
      | inr j =>
        simp only [Sum.elim_inr, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Function.comp_apply]
        ring}, fun uv => rfl⟩

set_option maxHeartbeats 2000000 in

/-- Establish the corrected marked walk's folded spectrum, including source-space equivalences
and interior and endpoint multiplicities [Szegedy2004]. -/
theorem szegedyCorrectedFoldedSpectrum : SzegedyCorrectedFoldedSpectrum := by
  intro I _ _ P S hP hsym
  have hF : IsIsometry (unmarkedRowFrame P S) := unmarkedRowFrame_isIsometry P S hP
  have hG : IsIsometry ((SwapGate : Matrix (I×I) (I×I) ℂ)*unmarkedRowFrame P S) := by
    change ((SwapGate : Matrix (I×I) (I×I) ℂ)*unmarkedRowFrame P S)ᴴ*
      (SwapGate*unmarkedRowFrame P S)=1
    calc
      _ = (unmarkedRowFrame P S)ᴴ*((SwapGate : Matrix (I×I) (I×I) ℂ)*SwapGate)*
          (unmarkedRowFrame P S) := by
        rw [Matrix.conjTranspose_mul, swapGate_hermitian]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [swapGate_mul_self, Matrix.mul_one]; exact hF
  obtain ⟨hwalk, hdisc⟩ := corrected_marked_walk_bipartite_bridge I P S hP hsym
  have hone : (unmarkedPrincipal P S-((1:ℝ):ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) =
      (unmarkedPrincipal P S-(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) := by simp
  have hone' : (bipartiteDiscriminant (unmarkedRowFrame P S)
        (SwapGate*unmarkedRowFrame P S)-((1:ℝ):ℂ)•
        (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)) =
      (bipartiteDiscriminant (unmarkedRowFrame P S)
        (SwapGate*unmarkedRowFrame P S)-(1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)) := by simp
  have hone2 : (unmarkedPrincipal P S+((1:ℝ):ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) =
      (unmarkedPrincipal P S+(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact corrected_block_split I P S hP hsym
  · intro lam hl hu s
    obtain ⟨es, _⟩ := (bipartite_tau_eigenspace_pair_equivalence (I×I)
      (Unmarked I S) (Unmarked I S) (unmarkedRowFrame P S)
      (SwapGate*unmarkedRowFrame P S) lam hF hG hl hu).2.1 s
    obtain ⟨e, _⟩ := corrected_block_split I P S hP hsym lam
    rw [hwalk]
    exact es.finrank_eq.symm.trans (e.finrank_eq.symm.trans Module.finrank_prod)
  · obtain ⟨⟨ep, _⟩, _⟩ := bipartite_endpoint_eigenspace_transport (I×I) (Unmarked I S)
      (Unmarked I S) (unmarkedRowFrame P S)
      (SwapGate*unmarkedRowFrame P S) hF hG
    obtain ⟨e, _⟩ := corrected_block_split I P S hP hsym 1
    have hf1 := e.finrank_eq
    rw [hone, hone', hone2] at hf1
    rw [hwalk]
    exact ep.finrank_eq.symm.trans (hf1.symm.trans Module.finrank_prod)
  · obtain ⟨_, ⟨e0, _⟩⟩ := bipartite_endpoint_eigenspace_transport (I×I) (Unmarked I S)
      (Unmarked I S) (unmarkedRowFrame P S)
      (SwapGate*unmarkedRowFrame P S) hF hG
    obtain ⟨e, _⟩ := corrected_block_split I P S hP hsym 0
    have hf0 := e.finrank_eq
    have hz1 : (unmarkedPrincipal P S-((0:ℝ):ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) =
        (unmarkedPrincipal P S) := by simp
    have hz2 : (unmarkedPrincipal P S+((0:ℝ):ℂ)•(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)) =
        (unmarkedPrincipal P S) := by simp
    have hz3 : (bipartiteDiscriminant (unmarkedRowFrame P S)
        (SwapGate*unmarkedRowFrame P S)-((0:ℝ):ℂ)•
        (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)) =
      (bipartiteDiscriminant (unmarkedRowFrame P S)
        (SwapGate*unmarkedRowFrame P S)) := by simp
    rw [hz1, hz2, hz3, Module.finrank_prod] at hf0
    rw [hwalk]
    exact (e0.finrank_eq.symm.trans hf0.symm).trans (by ring)

end Qatlib.Concepts.WalkSearch.Spectral
