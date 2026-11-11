/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Projective energy readout with degenerate sectors

A finite label map and a unitary basis change define the sector operators `energyProjector`,
allowing several basis vectors to share a label. These operators form an orthogonal resolution
of the identity and define `energyInstrument`, with branches given by compression to the
corresponding sectors. This is the projective measurement construction described in [Kraus1983].

`energyDilation` implements coherent label readout with an ancillary register. The module proves
repeatability, preservation of operators commuting with all sector projectors, preservation of
the expectation of `energyHamiltonian`, and the branch formula in the presence of a reference
system.

## Main statements

* `energy_projector_actual_orthogonal_resolution`: Hermitian, idempotent, mutually orthogonal
  sector projectors summing to the identity.
* `energy_readout_dilation_unitary_and_branch_amplitudes`: a unitary dilation with the required
  projected amplitudes.
* `energy_nondemolition_and_repeatable_outcome`: preservation of commuting inputs and vanishing
  successive distinct branches.
* `energy_readout_preserves_energy_expectation`: the forgotten measurement preserves the
  Hamiltonian trace pairing.

## References

* [Kraus, 1983][Kraus1983]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped Classical BigOperators Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The conjugate transpose of a unitary finite-dimensional operator is unitary. -/
theorem energyConjTranspose_unitary {D : ℕ} {V : Operator D}
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    V.conjTranspose ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  have h := (Matrix.mem_unitaryGroup_iff').mp hV
  rw [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact h

/-- The diagonal selector for a label fiber conjugated by `V`, giving its sector projector when
`V` is unitary. -/
noncomputable def energyProjector {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) : Operator D :=
  V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose

/-- For unitary `V`, the label-sector operators have the stated conjugated diagonal form and are
Hermitian idempotents. Distinct sectors are orthogonal, and their sum is the identity. -/
theorem energy_projector_actual_orthogonal_resolution (D M : ℕ) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∀ a, energyProjector label V a = V * Matrix.diagonal (fun i => if label i=a then (1:ℂ) else 0) * Vᴴ) ∧
      (∀ a, (energyProjector label V a)ᴴ = energyProjector label V a ∧ energyProjector label V a * energyProjector label V a = energyProjector label V a) ∧
      (∀ a b, a≠b → energyProjector label V a * energyProjector label V b = 0) ∧
      ∑ a, energyProjector label V a = 1 := by
  have hVtV : V.conjTranspose * V = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hVVt : V * V.conjTranspose = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hDherm : ∀ a : Fin M,
      (Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)).conjTranspose
        = Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) := by
    intro a
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  have hDD : ∀ a b : Fin M,
      Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)
          * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0)
        = Matrix.diagonal (fun i => if label i = a then (if label i = b then (1:ℂ) else 0) else 0) := by
    intro a b
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.mul_diagonal, Matrix.diagonal_apply]
      split_ifs
      all_goals simp
    · simp only [Matrix.mul_diagonal, Matrix.diagonal_apply, if_neg h, zero_mul]
  have hDa : ∀ a : Fin M,
      Matrix.diagonal (fun i => if label i = a then (if label i = a then (1:ℂ) else 0) else 0)
        = Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) := by
    intro a
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      by_cases h1 : label i = a <;> simp
    · simp only [if_neg h]
  have hDab : ∀ a b : Fin M, a ≠ b →
      Matrix.diagonal (fun i => if label i = a then (if label i = b then (1:ℂ) else 0) else 0)
        = (0 : Operator D) := by
    intro a b hab
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      by_cases h1 : label i = a
      · rw [if_pos h1, if_neg (fun h2 => hab (h1.symm.trans h2)), if_pos rfl, Matrix.zero_apply]
      · rw [if_neg h1, if_pos rfl, Matrix.zero_apply]
    · rw [if_neg h, Matrix.zero_apply]
  have hmid : ∀ a b : Fin M, energyProjector label V a * energyProjector label V b
      = V * (Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)
        * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0)) * V.conjTranspose := by
    intro a b
    show (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose)
        * (V * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0) * V.conjTranspose) = _
    calc (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose)
          * (V * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0) * V.conjTranspose)
        = (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0))
            * (V.conjTranspose * V
              * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0)) * V.conjTranspose := by
          noncomm_ring
      _ = (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0))
            * (1 * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0)) * V.conjTranspose := by
          rw [hVtV]
      _ = V * (Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)
            * Matrix.diagonal (fun i => if label i = b then (1:ℂ) else 0)) * V.conjTranspose := by
          noncomm_ring
  have hsumD : (∑ a : Fin M, Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0))
      = (1 : Operator D) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [Finset.sum_ite_eq]
      simp
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun a _ => by rw [if_neg h]
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro a
    refine ⟨?_, ?_⟩
    · show (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose)ᴴ = _
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hDherm a, ← Matrix.mul_assoc]
      rfl
    · rw [hmid a a, hDD a a, hDa a]
      rfl
  · intro a b hab
    rw [hmid a b, hDD a b, hDab a b hab, Matrix.mul_zero, Matrix.zero_mul]
  · calc ∑ a, energyProjector label V a
        = ∑ a, V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose :=
          Finset.sum_congr rfl fun a _ => rfl
      _ = V * (∑ a, Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)) * V.conjTranspose := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = V * 1 * V.conjTranspose := by rw [hsumD]
      _ = 1 := by rw [Matrix.mul_one, hVVt]

/-- Adding and then subtracting the same element in `Fin M` returns the original element. -/
theorem fin_add_sub_cancel {M : ℕ} (a b : Fin M) : (a + b) - b = a := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  simp only [Fin.val_add, Fin.val_sub]
  rcases Nat.lt_or_ge (a.val + b.val) M with h | h
  · have hmod : (a.val + b.val) % M = a.val + b.val := Nat.mod_eq_of_lt h
    have hsum : M - b.val + (a.val + b.val) = M + a.val := by omega
    rw [hmod, hsum, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  · have hmod : (a.val + b.val) % M = a.val + b.val - M := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt (by omega)
    have hsum : M - b.val + (a.val + b.val - M) = a.val := by omega
    rw [hmod, hsum, Nat.mod_eq_of_lt ha]

/-- Subtracting and then adding the same element in `Fin M` returns the original element. -/
theorem fin_sub_add_cancel {M : ℕ} (a b : Fin M) : (a - b) + b = a := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  simp only [Fin.val_add, Fin.val_sub]
  rcases Nat.lt_or_ge (M - b.val + a.val) M with h | h
  · have hmod : (M - b.val + a.val) % M = M - b.val + a.val := Nat.mod_eq_of_lt h
    rw [hmod]
    have hsum : M - b.val + a.val + b.val = M + a.val := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  · have hmod : (M - b.val + a.val) % M = M - b.val + a.val - M := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have hsum : M - b.val + a.val - M + b.val = a.val := by omega
    rw [hsum, Nat.mod_eq_of_lt ha]

/-- The reversible map that adds the system basis label to the ancillary label register and
leaves the system index fixed. -/
def energyLabelEquiv {D M : ℕ} (label : Fin D → Fin M) :
    (Fin M × Fin D) ≃ (Fin M × Fin D) where
  toFun p := ⟨p.1 + label p.2, p.2⟩
  invFun q := ⟨q.1 - label q.2, q.2⟩
  left_inv := by
    rintro ⟨a, i⟩
    simp only [Prod.mk.injEq]
    exact ⟨fin_add_sub_cancel a (label i), trivial⟩
  right_inv := by
    rintro ⟨b, i⟩
    simp only [Prod.mk.injEq]
    exact ⟨fin_sub_add_cancel b (label i), trivial⟩

/-- The permutation matrix implementing `energyLabelEquiv` on the joint label and system
register. -/
noncomputable def energyLabelPerm {D M : ℕ} (label : Fin D → Fin M) :
    Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ :=
  Matrix.of fun q p => if energyLabelEquiv label p = q then (1:ℂ) else 0

/-- The label permutation acts on state amplitudes by composition with the inverse of
`energyLabelEquiv`. -/
theorem energyLabelPerm_mulVec {D M : ℕ} (label : Fin D → Fin M)
    (v : QState (Fin M × Fin D)) (q : Fin M × Fin D) :
    (energyLabelPerm label *ᵥ v) q = v ((energyLabelEquiv label).symm q) := by
  simp only [Matrix.mulVec, dotProduct, energyLabelPerm, Matrix.of_apply]
  rw [Finset.sum_eq_single ((energyLabelEquiv label).symm q)]
  · rw [if_pos (Equiv.apply_symm_apply _ _), one_mul]
  · intro z _ hz
    have hne : ¬(energyLabelEquiv label) z = q := by
      intro h
      exact hz ((Equiv.symm_apply_apply _ z).symm.trans
        (congrArg (energyLabelEquiv label).symm h))
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The matrix implementing reversible addition of the system label is unitary. -/
theorem energyLabelPerm_unitary {D M : ℕ} (label : Fin D → Fin M) :
    energyLabelPerm label ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (energyLabelEquiv label x)]
  · simp only [Matrix.conjTranspose_apply, energyLabelPerm, Matrix.of_apply, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [if_neg (fun h => hxy (((energyLabelEquiv label).injective h).symm)), if_neg hxy]
      simp
  · intro z _ hz
    simp only [Matrix.conjTranspose_apply, energyLabelPerm, Matrix.of_apply]
    rw [if_neg (Ne.symm hz), star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The label-addition matrix conjugated by the system basis change, implementing coherent
sector readout when `V` is unitary. -/
noncomputable def energyDilation {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ :=
  TensorGate (1 : Operator M) V * energyLabelPerm label
    * TensorGate (1 : Operator M) V.conjTranspose

/-- The product of two unitary matrices on a finite index type is unitary. -/
theorem unitaryGroup_mul {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup ι ℂ) :
    A * B ∈ Matrix.unitaryGroup ι ℂ := by
  have hA' : A * A.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hA
  have hB' : B * B.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hB
  have h1 : (A * B) * (B.conjTranspose * A.conjTranspose)
      = A * (B * B.conjTranspose) * A.conjTranspose := by noncomm_ring
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, h1,
    hB', Matrix.mul_one, hA']

/-- The coherent energy-readout dilation is unitary whenever its system basis change is unitary. -/
theorem energyDilation_unitary {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    energyDilation label V ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ := by
  have h1u : (1 : Operator M) ∈ Matrix.unitaryGroup (Fin M) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]; simp
  show TensorGate (1 : Operator M) V * energyLabelPerm label
      * TensorGate (1 : Operator M) V.conjTranspose ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ
  exact unitaryGroup_mul
    (unitaryGroup_mul
      (tensorGate_unitary h1u hV)
      (energyLabelPerm_unitary label))
    (tensorGate_unitary h1u (energyConjTranspose_unitary hV))

/-- For a nonempty label register and unitary `V`, the energy dilation is unitary. Starting the
label register at zero, its amplitude at `(a, i)` equals component `i` of the input
projected onto sector `a`. -/
theorem energy_readout_dilation_unitary_and_branch_amplitudes (D M : ℕ) (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D) (ψ : QState (Fin D))
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    energyDilation label V ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ ∧
      ∀ a i, (energyDilation label V *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ) (a,i) =
        (energyProjector label V a *ᵥ ψ) i := by
  refine ⟨energyDilation_unitary label V hV, ?_⟩
  intro a i

  have h3 : ∀ v : QState (Fin M × Fin D),
      ((TensorGate (1 : Operator M) V) *ᵥ v) (a, i) = ∑ k : Fin D, V i k * v (a, k) := by
    intro v
    have e1 : ((TensorGate (1 : Operator M) V) *ᵥ v) (a, i)
        = ∑ q : Fin M × Fin D, ((1 : Operator M) a q.1 * V i q.2) * v q := rfl
    have e2 : (∑ q : Fin M × Fin D, ((1 : Operator M) a q.1 * V i q.2) * v q)
        = ∑ q : Fin M × Fin D, if a = q.1 then V i q.2 * v q else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Matrix.one_apply]
      by_cases h : a = q.1 <;> simp [h]
    have e3 : (∑ q : Fin M × Fin D, if a = q.1 then V i q.2 * v q else 0)
        = ∑ k : Fin D, V i k * v (a, k) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a]
      · exact Finset.sum_congr rfl fun k _ => by rw [if_pos rfl]
      · intro m _ hm
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg (Ne.symm hm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [e1, e2, e3]

  have h1 : ((TensorGate (1 : Operator M) V.conjTranspose) *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ)
      = TensorState (Ket (⟨0,hM⟩:Fin M)) (V.conjTranspose *ᵥ ψ) := by
    have hgate := applyGate_tensorGate (1 : Operator M) V.conjTranspose
      (Ket (⟨0,hM⟩:Fin M)) ψ
    rw [applyGate_one] at hgate
    exact hgate

  have h2 : ∀ k : Fin D, (energyLabelPerm label *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M))
        (V.conjTranspose *ᵥ ψ)) (a, k)
      = (if label k = a then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k := by
    intro k
    rw [energyLabelPerm_mulVec]
    have hsplit : (energyLabelEquiv label).symm (a, k) = ⟨a - label k, k⟩ := rfl
    rw [hsplit]
    have hzeroadd : (⟨0,hM⟩:Fin M) + label k = label k := by
      apply Fin.ext
      simp only [Fin.val_add]
      rw [Nat.zero_add, Nat.mod_eq_of_lt (label k).isLt]
    by_cases h : label k = a
    · subst h
      show (if label k - label k = (⟨0,hM⟩:Fin M) then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k
        = (if label k = label k then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k
      have hself : label k - label k = (⟨0,hM⟩:Fin M) := by
        apply Fin.ext
        have hb := (label k).isLt
        simp only [Fin.val_sub]
        rw [show M - (label k).val + (label k).val = M from by omega, Nat.mod_self]
      rw [hself]
      simp
    · have hne : a - label k ≠ (⟨0,hM⟩:Fin M) := by
        intro heq
        apply h
        have hca := fin_sub_add_cancel a (label k)
        rw [heq, hzeroadd] at hca
        exact hca
      show (if a - label k = (⟨0,hM⟩:Fin M) then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k
        = (if label k = a then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k
      rw [if_neg hne, if_neg h]

  have hvec : energyDilation label V *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ
      = (TensorGate (1 : Operator M) V) *ᵥ (energyLabelPerm label *ᵥ
          ((TensorGate (1 : Operator M) V.conjTranspose) *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ)) := by
    rw [energyDilation, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc (energyDilation label V *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ) (a, i)
      = ∑ k : Fin D, V i k * ((energyLabelPerm label *ᵥ
            ((TensorGate (1 : Operator M) V.conjTranspose) *ᵥ TensorState (Ket (⟨0,hM⟩:Fin M)) ψ)) (a, k)) := by
        rw [hvec, h3]
    _ = ∑ k : Fin D, V i k * ((if label k = a then (1:ℂ) else 0) * (V.conjTranspose *ᵥ ψ) k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [h1, h2 k]
    _ = (energyProjector label V a *ᵥ ψ) i := by
        have hL : (∑ k : Fin D, V i k * ((if label k = a then (1:ℂ) else 0)
              * (∑ m : Fin D, V.conjTranspose k m * ψ m)))
            = ∑ m : Fin D, ∑ k : Fin D, V i k * (if label k = a then (1:ℂ) else 0)
                * (V.conjTranspose k m * ψ m) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
        have hR : (energyProjector label V a *ᵥ ψ) i
            = ∑ m : Fin D, ∑ k : Fin D, V i k * (if label k = a then (1:ℂ) else 0)
                * (V.conjTranspose k m * ψ m) := by
          have inner : ∀ k : Fin D, (∑ x : Fin D, V i x
                * Matrix.diagonal (fun l => if label l = a then (1:ℂ) else 0) x k)
                = V i k * (if label k = a then (1:ℂ) else 0) := by
            intro k
            rw [Finset.sum_eq_single k]
            · rw [Matrix.diagonal_apply, if_pos rfl]
            · intro x _ hx
              rw [Matrix.diagonal_apply, if_neg hx, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ _) h
          have entry : ∀ m : Fin D,
              ((V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)) * V.conjTranspose) i m
                = ∑ k : Fin D, V i k * (if label k = a then (1:ℂ) else 0) * V.conjTranspose k m := by
            intro m
            simp only [Matrix.mul_apply]
            rw [Finset.sum_congr rfl fun k _ => by rw [inner k]]
          show (∑ m : Fin D, ((V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0))
              * V.conjTranspose) i m * ψ m) = _
          rw [Finset.sum_congr rfl fun m _ => by rw [entry m]]
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
        rw [hR]
        simp only [Matrix.mulVec, dotProduct]
        rw [hL]

/-- The instrument whose Kraus operator for each outcome is the corresponding energy-sector
projector. -/
noncomputable def energyInstrument {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument (Fin M) D D :=
  Instrument.ofKraus (energyProjector label V)
    (by
      have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
      rw [Finset.sum_congr rfl fun a _ => by
        rw [(hG1.2.1 a).1, (hG1.2.1 a).2]]
      exact hG1.2.2.2)

/-- An energy-instrument branch compresses the input operator by its sector projector on both
sides. Its outcome weight is the real part of the trace pairing with that projector. -/
theorem energy_actual_instrument_projector_map (D M : ℕ) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : Fin M) (X : Operator D) :
    (energyInstrument label V hV).branch a X = energyProjector label V a * X * energyProjector label V a ∧
      instrumentProb (energyInstrument label V hV) X a =
        (Matrix.trace (energyProjector label V a * X)).re := by
  have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
  refine ⟨?_, ?_⟩
  · simp only [energyInstrument, Instrument.ofKraus_branch, (hG1.2.1 a).1]
  · simp only [instrumentProb, energyInstrument, Instrument.ofKraus_branch, (hG1.2.1 a).1]
    have hcycle : Matrix.trace (energyProjector label V a * X * energyProjector label V a)
        = Matrix.trace (energyProjector label V a * X) := by
      rw [Matrix.trace_mul_cycle, (hG1.2.1 a).2]
    rw [hcycle]

/-- Forgetting the energy-readout outcome preserves any operator commuting with all sector
projectors. Applying a different outcome branch after a given branch gives the zero
operator. -/
theorem energy_nondemolition_and_repeatable_outcome (D M : ℕ) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (X : Operator D) :
    ((∀ a, energyProjector label V a * X = X * energyProjector label V a) →
      (energyInstrument label V hV).forget.map X = X) ∧
      ∀ a b, a≠b → (energyInstrument label V hV).branch b ((energyInstrument label V hV).branch a X) = 0 := by
  have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
  refine ⟨?_, ?_⟩
  · intro hcomm
    rw [Instrument.forget_apply]
    have hstep : ∀ a : Fin M, energyProjector label V a * X * energyProjector label V a
        = X * energyProjector label V a := by
      intro a
      rw [hcomm a, Matrix.mul_assoc, (hG1.2.1 a).2]
    calc ∑ a, (energyInstrument label V hV).branch a X
        = ∑ a, X * energyProjector label V a :=
          Finset.sum_congr rfl fun a _ => by
            rw [(energy_actual_instrument_projector_map D M label V hV a X).1, hstep a]
      _ = X * ∑ a, energyProjector label V a := by rw [Finset.mul_sum]
      _ = X * 1 := by rw [hG1.2.2.2]
      _ = X := Matrix.mul_one X
  · intro a b hab
    rw [(energy_actual_instrument_projector_map D M label V hV b
          ((energyInstrument label V hV).branch a X)).1,
        (energy_actual_instrument_projector_map D M label V hV a X).1]
    show energyProjector label V b * (energyProjector label V a * X * energyProjector label V a)
        * energyProjector label V b = 0
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG1.2.2.1 b a (Ne.symm hab)]
    simp

/-- The operator obtained by assigning a real energy to each label and conjugating the resulting
diagonal matrix by `V`. -/
noncomputable def energyHamiltonian {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (E : Fin M → ℝ) : Operator D :=
  V * Matrix.diagonal (fun i => (E (label i):ℂ)) * V.conjTranspose

/-- For unitary `V`, the energy Hamiltonian has the stated conjugated diagonal form. Forgetting
the energy-readout outcome preserves its trace pairing with every input operator. -/
theorem energy_readout_preserves_energy_expectation (D M : ℕ) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (E : Fin M → ℝ) (X : Operator D) :
    energyHamiltonian label V E = V * Matrix.diagonal (fun i => (E (label i):ℂ)) * Vᴴ ∧
      Matrix.trace (energyHamiltonian label V E * (energyInstrument label V hV).forget.map X) =
        Matrix.trace (energyHamiltonian label V E * X) := by
  have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
  have hVtV : V.conjTranspose * V = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨rfl, ?_⟩
  have hcommH : ∀ a : Fin M, energyHamiltonian label V E * energyProjector label V a
      = energyProjector label V a * energyHamiltonian label V E := by
    intro a
    have hmid : ∀ W₁ W₂ : Operator D,
        (V * W₁ * V.conjTranspose) * (V * W₂ * V.conjTranspose)
          = V * (W₁ * W₂) * V.conjTranspose := by
      intro W₁ W₂
      calc (V * W₁ * V.conjTranspose) * (V * W₂ * V.conjTranspose)
          = (V * W₁) * (V.conjTranspose * V) * (W₂ * V.conjTranspose) := by noncomm_ring
        _ = (V * W₁) * 1 * (W₂ * V.conjTranspose) := by rw [hVtV]
        _ = V * (W₁ * W₂) * V.conjTranspose := by noncomm_ring
    have hdiag : Matrix.diagonal (fun i => (E (label i):ℂ))
        * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)
      = Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0)
        * Matrix.diagonal (fun i => (E (label i):ℂ)) := by
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_apply]
      by_cases h : i = j <;> simp only [h, if_true, if_false] <;> ring
    show (V * Matrix.diagonal (fun i => (E (label i):ℂ)) * V.conjTranspose)
        * (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose)
        = (V * Matrix.diagonal (fun i => if label i = a then (1:ℂ) else 0) * V.conjTranspose)
        * (V * Matrix.diagonal (fun i => (E (label i):ℂ)) * V.conjTranspose)
    rw [hmid, hmid, hdiag]
  calc Matrix.trace (energyHamiltonian label V E * (energyInstrument label V hV).forget.map X)
      = ∑ a : Fin M, Matrix.trace (energyHamiltonian label V E
          * (energyProjector label V a * X * energyProjector label V a)) := by
        rw [Instrument.forget_apply, Matrix.mul_sum, Matrix.trace_sum]
        exact Finset.sum_congr rfl fun a _ => by
          rw [(energy_actual_instrument_projector_map D M label V hV a X).1]
    _ = ∑ a : Fin M, Matrix.trace (energyHamiltonian label V E * energyProjector label V a * X) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have e1 : energyHamiltonian label V E * (energyProjector label V a * X
              * energyProjector label V a)
            = energyHamiltonian label V E * energyProjector label V a * X
              * energyProjector label V a := by noncomm_ring
        have e2 : energyProjector label V a * (energyHamiltonian label V E
              * energyProjector label V a * X)
            = energyHamiltonian label V E * energyProjector label V a * X := by
          have hcp : energyProjector label V a * energyHamiltonian label V E
              = energyHamiltonian label V E * energyProjector label V a := (hcommH a).symm
          calc energyProjector label V a * (energyHamiltonian label V E
                  * energyProjector label V a * X)
              = (energyProjector label V a * energyHamiltonian label V E
                  * energyProjector label V a) * X := by noncomm_ring
            _ = (energyHamiltonian label V E * energyProjector label V a
                  * energyProjector label V a) * X := by rw [hcp]
            _ = energyHamiltonian label V E * energyProjector label V a * X := by
                rw [Matrix.mul_assoc (energyHamiltonian label V E)
                  (energyProjector label V a) (energyProjector label V a), (hG1.2.1 a).2]
        rw [e1, Matrix.trace_mul_comm, e2]
    _ = Matrix.trace (energyHamiltonian label V E * X) := by
        rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hG1.2.2.2, Matrix.mul_one]

/-- An energy branch acting on the system and leaving a finite reference unchanged compresses
the joint operator by the sector projector tensored with the reference identity. -/
theorem energy_readout_reference_branches (D M r : ℕ) (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : Fin M)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft ((energyInstrument label V hV).branch a) X =
      TensorGate (energyProjector label V a) (1:Operator r) * X *
        TensorGate (energyProjector label V a) (1:Operator r) := by
  have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
  have hPentry : ∀ i j : Fin D,
      star (energyProjector label V a j i) = energyProjector label V a i j := by
    intro i j
    have h : (energyProjector label V a).conjTranspose i j = energyProjector label V a i j :=
      congrFun (congrFun (hG1.2.1 a).1 i) j
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hbranch : (energyInstrument label V hV).branch a
      = conjBranch (energyProjector label V a) := by
    apply LinearMap.ext
    intro Z
    rw [(energy_actual_instrument_projector_map D M label V hV a Z).1, conjBranch_apply,
      (hG1.2.1 a).1]

  have hswapfac :
      ((TensorGate (1 : Operator r) (energyProjector label V a)).submatrix Prod.swap Prod.swap)
      = TensorGate (energyProjector label V a) (1:Operator r) := by
    ext ⟨i, a'⟩ ⟨j, b'⟩
    simp only [Matrix.submatrix_apply, TensorGate, Matrix.kronecker_apply, Prod.swap_prod_mk]
    ring
  have hswapfacd :
      (((TensorGate (1 : Operator r) (energyProjector label V a)).conjTranspose).submatrix
        Prod.swap Prod.swap)
      = (TensorGate (energyProjector label V a) (1:Operator r)).conjTranspose := by
    ext ⟨i, a'⟩ ⟨j, b'⟩
    simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply, TensorGate,
      Matrix.kronecker_apply, Matrix.conjTranspose_apply, Prod.swap_prod_mk,
      star_mul, hPentry]
    ring
  have hbswap : Function.Bijective (Prod.swap : Fin D × Fin r → Fin r × Fin D) :=
    Equiv.bijective (Equiv.prodComm _ _)
  rw [hbranch]

  have hmain : tensorLeft (conjBranch (energyProjector label V a)) X
      = ((MatrixMap.conj ((1 : Operator r) ⊗ₖ energyProjector label V a)
          (X.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap) := by
    have e1 : tensorLeft (conjBranch (energyProjector label V a)) X
        = ((ChannelAmplification (conjBranch (energyProjector label V a)) r
            (X.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap) := by
      ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
      rfl
    rw [e1, channelAmplification_conjBranch (energyProjector label V a) r
      (X.submatrix Prod.swap Prod.swap)]
  rw [hmain]
  show ((TensorGate (1 : Operator r) (energyProjector label V a)
    * X.submatrix Prod.swap Prod.swap
    * (TensorGate (1 : Operator r) (energyProjector label V a)).conjTranspose).submatrix
    Prod.swap Prod.swap) = _
  rw [Matrix.submatrix_mul _ _ _ _ _ hbswap, Matrix.submatrix_mul _ _ _ _ _ hbswap]
  have hXX : (X.submatrix Prod.swap Prod.swap).submatrix Prod.swap Prod.swap = X := by
    ext i j
    simp only [Matrix.submatrix_apply]
    simp
  rw [hswapfac, hswapfacd, hXX, tensorGate_conjTranspose, (hG1.2.1 a).1,
    Matrix.conjTranspose_one]

end Qatlib.Concepts.MbqcFlow.FlowDecision
