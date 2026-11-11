/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence

/-!
# Bipartite spectral symmetry and endpoint multiplicities

For two finite complex isometric frames, this module relates the discriminant eigenspaces at λ
and −λ by changing the sign of the second source component. It identifies the kernel of the
combined frame with the −1 source eigenspace and computes the source and walk endpoint
multiplicities.

The interior correspondence is extended to negative source eigenvalues through
`bipartite_tau_negative_interior_pair_equivalence`; `bipartite_full_space_endpoint_multiplicity`
includes the orthogonal complement of the combined frame range. The quantum walk spectral
framework is developed in [Szegedy2004].

## Main statements

* `bipartite_discriminant_spectrum_symmetry`: An explicit linear equivalence between opposite
  discriminant eigenspaces.
* `bipartite_frame_kernel_and_endpoint_source_dimensions`: Kernel identification and dimensions
  of the two endpoint source spaces.
* `bipartite_full_space_endpoint_multiplicity`: Dimensions of the full walk eigenspaces at ±1.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.TauEmbedding

namespace Qatlib.Concepts.WalkSearch.FrameSpectral
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The source transformation `(a, b) ↦ (a, −b)` on the direct sum of the two frame index
spaces. -/
private def sourceFlip {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (v : QState (I⊕J)) : QState (I⊕J) :=
  Sum.elim (fun i => v (.inl i)) (fun j => -(v (.inr j)))

/-- The source sign flip maps the zero state to zero. -/
private theorem sourceFlip_zero {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] : sourceFlip (0 : QState (I⊕J)) = 0 := by
  ext (i | j) <;> simp [sourceFlip]

/-- The source sign flip preserves addition of states. -/
private theorem sourceFlip_add {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (u v : QState (I⊕J)) :
    sourceFlip (u+v) = sourceFlip u+sourceFlip v := by
  ext (i | j)
  · simp [sourceFlip]
  · simp [sourceFlip]; ring

/-- The source sign flip commutes with complex scalar multiplication. -/
private theorem sourceFlip_smul {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : ℂ) (v : QState (I⊕J)) :
    sourceFlip (c•v) = c•sourceFlip v := by
  ext (i | j) <;> simp [sourceFlip]

/-- The source sign flip commutes with negation. -/
private theorem sourceFlip_neg {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (v : QState (I⊕J)) :
    sourceFlip (-v) = -(sourceFlip v) := by
  ext (i | j) <;> simp [sourceFlip]

/-- Applying the source sign flip twice returns the original state. -/
private theorem sourceFlip_sourceFlip {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (v : QState (I⊕J)) :
    sourceFlip (sourceFlip v) = v := by
  ext (i | j) <;> simp [sourceFlip]

/-- Matrix multiplication sends the pointwise negative of a vector to the negative of its image. -/
private theorem mulVec_neg_right {K L : Type} [Fintype L] [DecidableEq L] [Fintype K]
    [DecidableEq K] (M : Matrix K L ℂ) (w : QState L) :
    M *ᵥ (fun j => -(w j)) = -(M *ᵥ w) := by
  rw [show (fun j : L => -(w j)) = (-w : QState L) from rfl]
  exact Matrix.mulVec_neg w M

/-- The bipartite discriminant anticommutes with the source sign flip. -/
private theorem disc_sourceFlip {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (v : QState (I⊕J)) :
    bipartiteDiscriminant A B*ᵥsourceFlip v =
      sourceFlip (-(bipartiteDiscriminant A B*ᵥv)) := by
  have hd1 : bipartiteDiscriminant A B*ᵥsourceFlip v =
      Sum.elim (-((Aᴴ*B)*ᵥ(fun j => v (.inr j)))) ((Bᴴ*A)*ᵥ(fun i => v (.inl i))) := by
    rw [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
    simp only [sourceFlip, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec,
      zero_add, add_zero]
    rw [mulVec_neg_right]
  have hd2 : bipartiteDiscriminant A B*ᵥv =
      Sum.elim ((Aᴴ*B)*ᵥ(fun j => v (.inr j))) ((Bᴴ*A)*ᵥ(fun i => v (.inl i))) := by
    rw [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, zero_add, add_zero]
    rfl
  rw [hd1, hd2, sourceFlip_neg]
  ext (i | j) <;> simp [sourceFlip]

/-- For two isometric frames, the source sign flip gives a complex linear equivalence between
the discriminant eigenspaces at λ and −λ, which therefore have equal dimensions
[Szegedy2004]. -/
theorem bipartite_discriminant_spectrum_symmetry :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    IsIsometry A → IsIsometry B →
    (∃ e : ↥(LinearMap.ker
          ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) ≃ₗ[ℂ]
        ↥(LinearMap.ker
          ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')),
      ∀ u, (e u).1 = Sum.elim (fun i => u.1 (.inl i)) (fun j => -(u.1 (.inr j)))) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) =
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) := by
  intro H I J _ _ _ _ _ _ A B lam hA hB
  have step (c : ℂ) (v : QState (I⊕J)) :
      (bipartiteDiscriminant A B+c•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥsourceFlip v =
        sourceFlip (-((bipartiteDiscriminant A B-c•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥv)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, disc_sourceFlip,
      ← sourceFlip_smul, ← sourceFlip_add, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    congr 1
    module
  have key (c : ℂ) (v : QState (I⊕J)) :
      (bipartiteDiscriminant A B-c•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥv = 0 ↔
      (bipartiteDiscriminant A B+c•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥsourceFlip v = 0 := by
    constructor
    · intro hv
      rw [step, hv, neg_zero, sourceFlip_zero]
    · intro hv
      rw [step] at hv
      have h := congrArg sourceFlip hv
      rw [sourceFlip_sourceFlip, sourceFlip_zero] at h
      exact neg_eq_zero.mp h
  have hshape : ∀ (c : ℂ), (bipartiteDiscriminant A B-(-c)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) =
      bipartiteDiscriminant A B+c•(1 : Matrix (I⊕J) (I⊕J) ℂ) := by
    intro c
    rw [neg_smul, sub_neg_eq_add]
  have hshape' : ∀ (c : ℂ), (bipartiteDiscriminant A B+(-c)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) =
      bipartiteDiscriminant A B-c•(1 : Matrix (I⊕J) (I⊕J) ℂ) := by
    intro c
    rw [neg_smul, ← sub_eq_add_neg]
  have hmem : ∀ u : ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')),
      sourceFlip u.1 ∈ LinearMap.ker
        ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin') := by
    intro u
    have hv : (bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥu.1 = 0 := by
      rw [← Matrix.toLin'_apply]
      exact u.2
    exact LinearMap.mem_ker.mpr ((key (lam:ℂ) u.1).mp hv)
  have hmem' : ∀ w : ↥(LinearMap.ker
        ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')),
      sourceFlip w.1 ∈ LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin') := by
    intro w
    have hv : (bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥw.1 = 0 := by
      rw [← Matrix.toLin'_apply]
      exact w.2
    have hv' : (bipartiteDiscriminant A B-(-(lam:ℂ))•(1 : Matrix (I⊕J) (I⊕J) ℂ))*ᵥw.1 = 0 := by
      rw [hshape (lam:ℂ)]
      exact hv
    exact LinearMap.mem_ker.mpr (by
      rw [Matrix.toLin'_apply, ← hshape' (lam:ℂ)]
      exact (key (-(lam:ℂ)) w.1).mp hv')
  let f : ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) →ₗ[ℂ]
      ↥(LinearMap.ker
        ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) := {
    toFun := fun u => ⟨sourceFlip u.1, hmem u⟩
    map_add' := by intro u v; apply Subtype.ext; simp [sourceFlip_add]
    map_smul' := by intro c u; apply Subtype.ext; simp [sourceFlip_smul] }
  have hinj : Function.Injective f := by
    intro u v huv
    have hh : f (u-v) = 0 := by rw [map_sub, huv, sub_self]
    have hz : sourceFlip (u-v).1 = 0 := congrArg Subtype.val hh
    have h := congrArg sourceFlip hz
    rw [sourceFlip_sourceFlip, sourceFlip_zero] at h
    exact sub_eq_zero.mp (Subtype.ext h)
  have hsurj : Function.Surjective f := by
    intro w
    exact ⟨⟨sourceFlip w.1, hmem' w⟩,
      by apply Subtype.ext; exact sourceFlip_sourceFlip w.1⟩
  refine ⟨⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun u => rfl⟩, ?_⟩
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq

/-- For isometric frames, the combined frame kernel is exactly the discriminant eigenspace at
−1, and both endpoint source eigenspaces have dimension equal to the total source dimension
minus the combined frame rank [Szegedy2004]. -/
theorem bipartite_frame_kernel_and_endpoint_source_dimensions :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    (∀ v : QState (I⊕J), bipartiteTilde A B*ᵥv = 0 ↔ bipartiteDiscriminant A B*ᵥv = -v) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) =
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B+(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) =
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B) := by
  intro H I J _ _ _ _ _ _ A B hA hB
  have hgram := (bipartite_discriminant_tilde_bridge H I J A B hA hB).2.1
  have hiff : ∀ v : QState (I⊕J),
      bipartiteTilde A B*ᵥv = 0 ↔ bipartiteDiscriminant A B*ᵥv = -v := by
    intro v
    constructor
    · intro hv
      have hh : (1+bipartiteDiscriminant A B)*ᵥv = 0 := by
        rw [← hgram, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
      rw [Matrix.add_mulVec, Matrix.one_mulVec] at hh
      exact eq_neg_of_add_eq_zero_right hh
    · intro hd
      have hh : Qatlib.Foundations.PureStateMath.Inner (bipartiteTilde A B*ᵥv) (bipartiteTilde A B*ᵥv) = 0 := by
        rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hgram,
          Matrix.add_mulVec, Matrix.one_mulVec, hd, add_neg_cancel]
        simp [Qatlib.Foundations.PureStateMath.Inner]
      exact dotProduct_star_self_eq_zero.mp hh
  have hker : LinearMap.ker
      ((bipartiteDiscriminant A B+(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin') =
      LinearMap.ker (bipartiteTilde A B).toLin' := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.add_mulVec, Matrix.one_mulVec]
    constructor
    · intro hv
      exact (hiff v).2 (eq_neg_of_add_eq_zero_left hv)
    · intro hv
      rw [(hiff v).1 hv, neg_add_cancel]
  have hdimplus : Module.finrank ℂ ↥(LinearMap.ker
      ((bipartiteDiscriminant A B+(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) =
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B) := by
    have hdimT := LinearMap.finrank_range_add_finrank_ker (bipartiteTilde A B).toLin'
    change Matrix.rank (bipartiteTilde A B)+
      Module.finrank ℂ ↥(LinearMap.ker (bipartiteTilde A B).toLin') =
      Module.finrank ℂ (QState (I⊕J)) at hdimT
    simp only [Module.finrank_pi, Fintype.card_sum] at hdimT
    rw [hker]
    omega
  refine ⟨hiff, ?_, hdimplus⟩
  have hone : (bipartiteDiscriminant A B-((1:ℝ):ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) =
      (bipartiteDiscriminant A B-(1 : Matrix (I⊕J) (I⊕J) ℂ)) := by simp
  have hone' : (bipartiteDiscriminant A B+((1:ℝ):ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) =
      (bipartiteDiscriminant A B+(1 : Matrix (I⊕J) (I⊕J) ℂ)) := by simp
  have hG1 := (bipartite_discriminant_spectrum_symmetry H I J A B 1 hA hB).2
  rw [hone, hone'] at hG1
  exact hG1.trans hdimplus

/-- For `0 < lam < 1`, each associated walk eigenspace within the combined frame range has the
same dimension as either discriminant eigenspace at `lam` or `-lam` [Szegedy2004]. -/
theorem bipartite_busy_phase_fold_multiplicity :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    IsIsometry A → IsIsometry B → 0 < lam → lam < 1 → ∀ s : Bool,
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl hu s
  obtain ⟨e, _⟩ := (bipartite_tau_eigenspace_pair_equivalence H I J A B lam hA hB hl hu).2.1 s
  exact ⟨e.finrank_eq.symm,
    e.finrank_eq.symm.trans (bipartite_discriminant_spectrum_symmetry H I J A B lam hA hB).2⟩

/-- Negating the source eigenvalue exchanges the two Boolean branches of `bipartitePhase`. -/
private theorem phase_neg (lam : ℝ) (s : Bool) :
    bipartitePhase (-lam) s = bipartitePhase lam (!s) := by
  have hsq : (-lam)^2 = lam^2 := by ring
  simp only [bipartitePhase, hsq]
  cases s <;> simp

/-- Simultaneously negating the source eigenvalue, exchanging the phase branch, and flipping the
second source component leaves the tau image unchanged. -/
private theorem tau_linear_sourceFlip {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ) (s : Bool) (v : QState (I⊕J)) :
    bipartiteTauLinear A B (-lam) (!s) (sourceFlip v) = bipartiteTauLinear A B lam s v := by
  have hc : (-(( -lam : ℝ):ℂ)+(if (!s) then Complex.I else -Complex.I)*
      ((Real.sqrt (1-(-lam)^2)):ℂ)) =
      -((-(lam:ℂ)+(if s then Complex.I else -Complex.I)*((Real.sqrt (1-lam^2)):ℂ))) := by
    have hsq : (-lam)^2 = lam^2 := by ring
    rw [hsq]
    cases s <;> simp <;> ring
  have hn : (B : Matrix H J ℂ)*ᵥ (fun j => -(v (Sum.inr j))) =
      -(B*ᵥ(fun j => v (Sum.inr j))) := mulVec_neg_right B (fun j => v (Sum.inr j))
  change A*ᵥ(fun i => (sourceFlip v) (.inl i))+
      (-((-lam:ℝ):ℂ)+(if (!s) then Complex.I else -Complex.I)*((Real.sqrt (1-(-lam)^2)):ℂ))•
        (B*ᵥ(fun j => (sourceFlip v) (.inr j))) =
    A*ᵥ(fun i => v (.inl i))+
      (-(lam:ℂ)+(if s then Complex.I else -Complex.I)*((Real.sqrt (1-lam^2)):ℂ))•
        (B*ᵥ(fun j => v (.inr j)))
  simp only [sourceFlip, Sum.elim_inl, Sum.elim_inr]
  rw [hn, smul_neg, hc]
  module

/-- The complex linear equivalence between kernels induced by equality of their defining
matrices. -/
private def kerCast {n : Type} [Fintype n] [DecidableEq n]
    {M M' : Matrix n n ℂ} (hM : M = M') :
    LinearMap.ker M.toLin' ≃ₗ[ℂ] LinearMap.ker M'.toLin' where
  toFun x := ⟨x.1, hM ▸ x.2⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    rfl
  invFun x := ⟨x.1, hM.symm ▸ x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- Transporting a kernel element along matrix equality preserves its underlying vector. -/
private theorem kerCast_val {n : Type} [Fintype n] [DecidableEq n]
    {M M' : Matrix n n ℂ} (hM : M = M') (x : LinearMap.ker M.toLin') :
    (kerCast hM x).1 = x.1 := rfl

/-- For `-1 < lam < 0`, the two walk phases are distinct and the tau maps identify the source
eigenspace with each corresponding walk eigenspace in the combined frame range. The sum of
these two walk spaces has twice the source dimension [Szegedy2004]. -/
theorem bipartite_tau_negative_interior_pair_equivalence :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    IsIsometry A → IsIsometry B → -1 < lam → lam < 0 →
    bipartitePhase lam true ≠ bipartitePhase lam false ∧
    (∀ s : Bool,
      ∃ e : ↥(LinearMap.ker
            ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) ≃ₗ[ℂ]
          ↥(LinearMap.ker
              ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
            LinearMap.range (bipartiteTilde A B).toLin'),
        ∀ u, (e u).1 = bipartiteTauLinear A B lam s u.1) ∧
    Module.finrank ℂ ↥((LinearMap.ker
          ((bipartiteWalk A B-bipartitePhase lam true•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') ⊔
      (LinearMap.ker
          ((bipartiteWalk A B-bipartitePhase lam false•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin')) =
      2*Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl hu
  have hμl : 0 < -lam := by linarith
  have hμu : -lam < 1 := by linarith
  obtain ⟨hdist, heq, hdim⟩ :=
    bipartite_tau_eigenspace_pair_equivalence H I J A B (-lam) hA hB hμl hμu
  obtain ⟨e₁, he₁⟩ := (bipartite_discriminant_spectrum_symmetry H I J A B lam hA hB).1
  have hM : (bipartiteDiscriminant A B+(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) =
      (bipartiteDiscriminant A B-((-lam:ℝ):ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)) := by
    rw [Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  have hE : ∀ s : Bool,
      (LinearMap.ker ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') =
      (LinearMap.ker ((bipartiteWalk A B-bipartitePhase (-lam) (!s)•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') := by
    intro s
    rw [phase_neg, Bool.not_not]
  refine ⟨?_, ?_, ?_⟩
  · intro he
    refine hdist ?_
    rw [phase_neg lam true, phase_neg lam false]
    simp only [Bool.not_true, Bool.not_false]
    exact he.symm
  · intro s
    rw [hE s]
    obtain ⟨e', he'⟩ := heq (!s)
    refine ⟨e₁.trans ((kerCast hM).trans e'), fun u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      he' (kerCast hM (e₁ u)), kerCast_val]
    have hflip : (e₁ u).1 = sourceFlip u.1 := he₁ u
    rw [hflip, tau_linear_sourceFlip]
  · rw [hE true, hE false, Bool.not_true, Bool.not_false, sup_comm, hdim,
      (bipartite_discriminant_spectrum_symmetry H I J A B (-lam) hA hB).2]
    rw [Complex.ofReal_neg, neg_smul, sub_eq_add_neg]

/-- A vector lies in the kernel of the adjoint combined frame exactly when both frame adjoints
annihilate it. -/
private theorem tilde_conj_kernel {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (w : QState H) :
    (bipartiteTilde A B)ᴴ*ᵥw = 0 ↔ Aᴴ*ᵥw = 0 ∧ Bᴴ*ᵥw = 0 := by
  rw [bipartiteTilde, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mulVec]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun j => congrFun h (Sum.inr j)⟩
  · rintro ⟨ha, hb⟩
    ext (i | j)
    · exact congrFun ha i
    · exact congrFun hb j

/-- For isometric frames, the full walk eigenspace at +1 has the sum of the source kernel and
idle dimensions, while the −1 multiplicity is the total source dimension minus twice the
overlap rank [Szegedy2004]. -/
theorem bipartite_full_space_endpoint_multiplicity :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin')) =
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B)+
        (Fintype.card H-Matrix.rank (bipartiteTilde A B)) ∧
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B+(1 : Matrix H H ℂ)).toLin')) =
      Fintype.card I+Fintype.card J-2*Matrix.rank (Aᴴ*B) := by
  intro H I J _ _ _ _ _ _ A B hA hB
  have hmulti := bipartite_busy_idle_multiplicity H I J A B hA hB
  refine ⟨?_, ?_⟩
  · have hidle : LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin') ≤
        LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') := by
      intro w hw
      have h0 : (bipartiteTilde A B)ᴴ*ᵥw = 0 := by
        have htt := LinearMap.mem_ker.mp hw
        rwa [Matrix.toLin'_apply] at htt
      have hab := (tilde_conj_kernel A B w).mp h0
      have hfix : bipartiteWalk A B*ᵥw = w :=
        (two_isometry_idle_sector_fixed I J H A B w hA hB hab.1 hab.2).2.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        hfix, sub_self]
    have hsplit : LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') =
        (LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin') ⊔
        LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin') := by
      apply le_antisymm
      · intro w hw
        have hw' := hw
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
          Matrix.one_mulVec] at hw'
        have hwm : bipartiteWalk A B*ᵥw = w := sub_eq_zero.mp hw'
        have hpq := (bipartite_endpoint_projectors A B hA hB w).1.mp hwm
        have hPp : IsOrthogonalProjector (A*Aᴴ) := rangeProjector_isOrthogonalProjector hA
        have hQq : IsOrthogonalProjector (B*Bᴴ) := rangeProjector_isOrthogonalProjector hB
        have hPP : (A*Aᴴ)*ᵥ((A*Aᴴ)*ᵥw) = (A*Aᴴ)*ᵥw := by
          rw [Matrix.mulVec_mulVec, hPp.1]
        have hQQ : (B*Bᴴ)*ᵥ((B*Bᴴ)*ᵥw) = (B*Bᴴ)*ᵥw := by
          rw [Matrix.mulVec_mulVec, hQq.1]
        have hPBp : (B*Bᴴ)*ᵥ((A*Aᴴ)*ᵥw) = (A*Aᴴ)*ᵥw := by
          rw [hpq, hQQ]
        have hAp : Aᴴ*ᵥ((A*Aᴴ)*ᵥw) = Aᴴ*ᵥw := by
          rw [Matrix.mulVec_mulVec,
            show Aᴴ*(A*Aᴴ)=Aᴴ from by
              rw [← Matrix.mul_assoc, show Aᴴ*A=1 from hA, Matrix.one_mul]]
        have hBp : Bᴴ*ᵥ((A*Aᴴ)*ᵥw) = Bᴴ*ᵥw := by
          rw [hpq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
            show Bᴴ*B=1 from hB, Matrix.one_mul]
        have hpfix : bipartiteWalk A B*ᵥ((A*Aᴴ)*ᵥw) = (A*Aᴴ)*ᵥw := by
          rw [bipartiteWalk, ← Matrix.mulVec_mulVec, reflectionAbout_mulVec (A*Aᴴ), hPP]
          have hh : (2:ℂ)•((A*Aᴴ)*ᵥw)-((A*Aᴴ)*ᵥw) = (A*Aᴴ)*ᵥw := by module
          rw [hh, reflectionAbout_mulVec, hPBp]
          module
        have hprange : (A*Aᴴ)*ᵥw ∈ LinearMap.range (bipartiteTilde A B).toLin' := by
          refine ⟨Sum.elim (Aᴴ*ᵥw) 0, ?_⟩
          change bipartiteTilde A B*ᵥ(Sum.elim (Aᴴ*ᵥw) 0) = (A*Aᴴ)*ᵥw
          rw [bipartiteTilde, Matrix.fromCols_mulVec_sumElim]
          simp [Matrix.mulVec_mulVec]
        have hdk : (bipartiteTilde A B)ᴴ*ᵥ(w-(A*Aᴴ)*ᵥw) = 0 := by
          rw [(tilde_conj_kernel A B _).2 ⟨by
            rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
              show Aᴴ*(A*Aᴴ)=Aᴴ from by
                rw [← Matrix.mul_assoc, show Aᴴ*A=1 from hA, Matrix.one_mul],
              sub_self],
            by rw [Matrix.mulVec_sub, hBp, sub_self]⟩]
        have hdmem : w-(A*Aᴴ)*ᵥw ∈ LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin') := by
          rw [LinearMap.mem_ker, Matrix.toLin'_apply]
          exact hdk
        have hpmem : (A*Aᴴ)*ᵥw ∈ LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') ⊓
            LinearMap.range (bipartiteTilde A B).toLin' := by
          refine Submodule.mem_inf.mpr ⟨?_, hprange⟩
          rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
            hpfix, sub_self]
        exact Submodule.mem_sup.mpr ⟨(A*Aᴴ)*ᵥw, hpmem, w-(A*Aᴴ)*ᵥw, hdmem, by module⟩
      · exact sup_le inf_le_left hidle
    have hdisj' : Disjoint
        (LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin')
        (LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin')) := by
      apply disjoint_iff.mpr
      apply le_antisymm ?_ bot_le
      intro x hx
      change x = 0
      obtain ⟨u, hu⟩ := hx.1.2
      rw [Matrix.toLin'_apply] at hu
      have hx0 : (bipartiteTilde A B)ᴴ*ᵥx = 0 := by
        have htt := LinearMap.mem_ker.mp hx.2
        rwa [Matrix.toLin'_apply] at htt
      have hz : Qatlib.Foundations.PureStateMath.Inner x x = 0 := by
        rw [← hu, inner_mulVec_left_rect, hu, hx0]
        simp [Qatlib.Foundations.PureStateMath.Inner]
      exact dotProduct_star_self_eq_zero.mp hz
    rw [hsplit]
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin')
      (LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin'))
    rw [hdisj'.eq_bot, finrank_bot, add_zero] at hfin
    rw [hfin, hmulti.1]
    omega
  · have hsub : LinearMap.ker ((bipartiteWalk A B+(1 : Matrix H H ℂ)).toLin') ≤
        LinearMap.range (bipartiteTilde A B).toLin' := by
      intro w hw
      have hw' := hw
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.add_mulVec,
        Matrix.one_mulVec] at hw'
      have hwm : bipartiteWalk A B*ᵥw = -w := eq_neg_of_add_eq_zero_left hw'
      have hs := (bipartite_endpoint_projectors A B hA hB w).2.mp hwm
      refine ⟨Sum.elim (Aᴴ*ᵥw) (Bᴴ*ᵥw), ?_⟩
      change bipartiteTilde A B*ᵥ(Sum.elim (Aᴴ*ᵥw) (Bᴴ*ᵥw)) = w
      rw [bipartiteTilde, Matrix.fromCols_mulVec_sumElim]
      simpa only [Matrix.mulVec_mulVec] using! hs
    have hEq : LinearMap.ker ((bipartiteWalk A B+(1 : Matrix H H ℂ)).toLin') =
        (LinearMap.ker ((bipartiteWalk A B+(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin') := by
      ext w
      constructor
      · intro hw
        exact ⟨hw, hsub hw⟩
      · exact fun h => h.1
    rw [hEq, hmulti.2.1]

end Qatlib.Concepts.WalkSearch.FrameSpectral
