/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementGeneralLoccDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability

open Qatlib
open scoped BigOperators ComplexOrder

variable {D E n : ℕ}

theorem outerProduct_applyGate_matrix {I : Type*} [Fintype I]
    (W : Matrix I I ℂ) (ψ : QState I) :
    outerProduct (ApplyGate W ψ) = W * outerProduct ψ * W.conjTranspose := by
  ext i j
  have starNorm : ∀ z : ℂ, (starRingEnd ℂ) z = star z := fun _ => rfl
  simp only [outerProduct_apply, ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, map_mul]
  simp only [starNorm]
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_mul_ite_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℂ) :
    (∑ b, (if a = b then 1 else 0) * f b) = f a := by
  have h : ∀ b, (if a = b then 1 else 0) * f b = if a = b then f b else 0 := by
    intro b
    by_cases hb : a = b <;> simp [hb]
  calc (∑ b, (if a = b then 1 else 0) * f b)
      = ∑ b, (if a = b then f b else 0) := Finset.sum_congr rfl fun b _ => h b
    _ = f a := by
      rw [Finset.sum_ite_eq]
      simp

theorem applyGate_tensorLeft_apply (A : Operator D) (ψ : QState (Fin D × Fin E))
    (a : Fin D) (b : Fin E) :
    ApplyGate (TensorGate A (1 : Operator E)) ψ (a, b) = ∑ u, A a u * ψ (u, b) := by
  classical
  simp only [ApplyGate, Matrix.mulVec, dotProduct, tensorGate_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  calc (∑ x_2, (A a x_1 * (if b = x_2 then 1 else 0)) * ψ (x_1, x_2))
      = A a x_1 * ∑ x_2, (if b = x_2 then 1 else 0) * ψ (x_1, x_2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x_2 _ => by ring
    _ = A a x_1 * ψ (x_1, b) := by rw [sum_mul_ite_one]

theorem sum_swap_outer {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → ℂ) :
    (∑ a, ∑ u, ∑ v, f a u v) = ∑ u, ∑ a, ∑ v, f a u v := by
  rw [@Finset.sum_comm κ ℂ ι]

theorem sum_swap_inner {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → ℂ) :
    (∑ u, ∑ a, ∑ v, f a u v) = ∑ u, ∑ v, ∑ a, f a u v := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [@Finset.sum_comm μ ℂ ι]

theorem secondMarginal_krausBranch (ψ : QState (Fin D × Fin E)) (A : Operator D)
    (b c : Fin E) :
    secondMarginalState (ApplyGate (TensorGate A (1 : Operator E)) ψ) b c
      = ∑ u, ∑ k, (starRingEnd ℂ) ((A.conjTranspose * A) u k) * ψ (u, b)
          * (starRingEnd ℂ) (ψ (k, c)) := by
  classical
  have hk : ∀ u k, (starRingEnd ℂ) ((A.conjTranspose * A) u k)
      = ∑ a, A a u * (starRingEnd ℂ) (A a k) := by
    intro u k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h' : (starRingEnd ℂ) (star (A a u) * A a k)
        = A a u * (starRingEnd ℂ) (A a k) := by
      have h := map_mul (starRingEnd ℂ) (star (A a u)) (A a k)
      rw [h]
      simp [RCLike.star_def]
    rw [h']
  have hL : secondMarginalState (ApplyGate (TensorGate A (1 : Operator E)) ψ) b c
      = ∑ a, ∑ u, ∑ v, A a u * ψ (u, b)
          * ((starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c))) := by
    simp only [secondMarginalState, secondMarginal, outerProduct_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [applyGate_tensorLeft_apply, applyGate_tensorLeft_apply, map_sum]
    conv_lhs =>
      rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    have h' : (starRingEnd ℂ) (A a v * ψ (v, c))
        = (starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c)) :=
      map_mul (starRingEnd ℂ) (A a v) (ψ (v, c))
    rw [h']
  calc secondMarginalState (ApplyGate (TensorGate A (1 : Operator E)) ψ) b c
      = ∑ a, ∑ u, ∑ v, A a u * ψ (u, b)
          * ((starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c))) := hL
    _ = ∑ u, ∑ v, ∑ a, A a u * ψ (u, b)
          * ((starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c))) := by
        rw [sum_swap_outer, sum_swap_inner]
    _ = ∑ u, ∑ k, (starRingEnd ℂ) ((A.conjTranspose * A) u k) * ψ (u, b)
          * (starRingEnd ℂ) (ψ (k, c)) := by
        have hpoint : ∀ u v,
            (∑ a, A a u * ψ (u, b) * ((starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c))))
              = (∑ a, A a u * (starRingEnd ℂ) (A a v)) * ψ (u, b)
                  * (starRingEnd ℂ) (ψ (v, c)) := by
          intro u v
          calc (∑ a, A a u * ψ (u, b)
              * ((starRingEnd ℂ) (A a v) * (starRingEnd ℂ) (ψ (v, c))))
              = ∑ a, (A a u * (starRingEnd ℂ) (A a v))
                  * (ψ (u, b) * (starRingEnd ℂ) (ψ (v, c))) := by
                refine Finset.sum_congr rfl fun a _ => by ring
            _ = (∑ a, A a u * (starRingEnd ℂ) (A a v))
                  * (ψ (u, b) * (starRingEnd ℂ) (ψ (v, c))) := by
                rw [← Finset.sum_mul]
            _ = (∑ a, A a u * (starRingEnd ℂ) (A a v)) * ψ (u, b)
                  * (starRingEnd ℂ) (ψ (v, c)) := by ring
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hk]
        exact hpoint u v

theorem krausComplete_pointwise (K : KrausInstrument D n) (u k : Fin D) :
    (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k))
      = (starRingEnd ℂ) (if u = k then 1 else 0) := by
  classical
  calc (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k))
      = (starRingEnd ℂ) (∑ i, ((K.op i).conjTranspose * (K.op i)) u k) := by
        rw [map_sum]
    _ = (starRingEnd ℂ) ((∑ i, (K.op i).conjTranspose * (K.op i)) u k) := by
        rw [Matrix.sum_apply]
    _ = (starRingEnd ℂ) (if u = k then 1 else 0) := by
        rw [K.hcomplete, Matrix.one_apply]

theorem secondMarginal_krausAverageState (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (b c : Fin E) :
    secondMarginal (krausAverageState ψ K) b c = secondMarginalState ψ b c := by
  classical
  have hsplit : secondMarginal (krausAverageState ψ K) b c
      = ∑ i, secondMarginalState (krausBranch ψ K i) b c := by
    simp only [krausAverageState, secondMarginalState, secondMarginal, Matrix.sum_apply,
      outerProduct_apply]
    rw [@Finset.sum_comm (Fin D) ℂ (Fin n)]
  rw [hsplit]
  have hbranch : ∀ (i : Fin n),
      secondMarginalState (krausBranch ψ K i) b c
        = ∑ u, ∑ k, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
            * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) :=
    fun i => secondMarginal_krausBranch ψ (K.op i) b c
  calc (∑ i, secondMarginalState (krausBranch ψ K i) b c)
      = ∑ i, ∑ u, ∑ k, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
          * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hbranch i
    _ = ∑ u, ∑ i, ∑ k, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
          * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by
        rw [@Finset.sum_comm (Fin D) ℂ (Fin n)]
    _ = ∑ u, ∑ k, ∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
          * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [@Finset.sum_comm (Fin D) ℂ (Fin n)]
    _ = ∑ u, ∑ k, (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k))
          * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        calc (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
            * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)))
            = ∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k)
                * (ψ (u, b) * (starRingEnd ℂ) (ψ (k, c))) := by
              refine Finset.sum_congr rfl fun i _ => by ring
          _ = (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k))
              * (ψ (u, b) * (starRingEnd ℂ) (ψ (k, c))) := by
              rw [← Finset.sum_mul]
          _ = (∑ i, (starRingEnd ℂ) (((K.op i).conjTranspose * (K.op i)) u k))
              * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by ring
    _ = ∑ u, ∑ k, (starRingEnd ℂ) (if u = k then 1 else 0)
          * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [krausComplete_pointwise]
    _ = ∑ u, ψ (u, b) * (starRingEnd ℂ) (ψ (u, c)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have hconv : (∑ k, (starRingEnd ℂ) (if u = k then 1 else 0)
            * ψ (u, b) * (starRingEnd ℂ) (ψ (k, c)))
          = ∑ k, (if u = k then 1 else 0)
              * (ψ (u, b) * (starRingEnd ℂ) (ψ (k, c))) := by
          exact Finset.sum_congr rfl fun k _ => by
            by_cases h : u = k
            · subst h
              simp
            · simp [h]
        rw [hconv, sum_mul_ite_one]
    _ = secondMarginalState ψ b c := by
        simp only [secondMarginalState, secondMarginal, outerProduct_apply]

theorem krausBranchReduced_eq (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n)
    (i : Fin n) :
    krausBranchReduced ψ K i
      = (K.op i) * PartialTrace (outerProduct ψ) * (K.op i).conjTranspose := by
  simp only [krausBranchReduced, krausBranch]
  exact partialTrace_outerProduct_apply_tensorLeft (D := D) (E := E) (K.op i) ψ

theorem krausBranchMass_eq_trace (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n)
    (i : Fin n) :
    krausBranchMass ψ K i = (Matrix.trace (krausBranchReduced ψ K i)).re := by
  have h1 : Matrix.trace (krausBranchReduced ψ K i)
      = Matrix.trace (outerProduct (krausBranch ψ K i)) := by
    simp only [krausBranchReduced]
    exact trace_partialTrace _
  have h2 : Matrix.trace (outerProduct (krausBranch ψ K i))
      = ((∑ j, ‖krausBranch ψ K i j‖ ^ 2 : ℝ) : ℂ) := trace_outerProduct _
  rw [krausBranchMass, h1, h2]
  simp only [Complex.ofReal_re]

theorem krausBranchMass_nonneg (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n)
    (i : Fin n) : 0 ≤ krausBranchMass ψ K i := by
  unfold krausBranchMass
  exact Finset.sum_nonneg fun j _ => by positivity

theorem krausBranchMass_eq_zero_iff (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n)
    (i : Fin n) :
    krausBranchMass ψ K i = 0 ↔ ∀ j, krausBranch ψ K i j = 0 := by
  unfold krausBranchMass
  constructor
  · intro h j
    have hz : ‖krausBranch ψ K i j‖ ^ 2 = 0 := by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun x => ‖krausBranch ψ K i x‖ ^ 2)
        (fun x _ => by positivity)).mp h j (Finset.mem_univ j)
      exact h1
    exact norm_eq_zero.mp (by simpa using hz)
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun x => ‖krausBranch ψ K i x‖ ^ 2)
      (fun x _ => by positivity)).mpr
    intro j _
    simp [h j]

theorem krausAverage_firstMarginal (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n) :
    PartialTrace (krausAverageState ψ K)
      = ∑ i, (K.op i) * PartialTrace (outerProduct ψ) * (K.op i).conjTranspose := by
  simp only [krausAverageState]
  rw [partialTrace_sum]
  exact Finset.sum_congr rfl fun i _ => krausBranchReduced_eq ψ K i

theorem krausBranchMass_sum_eq_one (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n)
    (hψ : Normalized ψ) :
    (∑ i, krausBranchMass ψ K i) = 1 := by
  have hmass : ∀ i, krausBranchMass ψ K i
      = (Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ) * (K.op i).conjTranspose)).re := by
    intro i
    rw [krausBranchMass_eq_trace, krausBranchReduced_eq]
  have hcyc : ∀ i,
      Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ) * (K.op i).conjTranspose)
        = Matrix.trace ((K.op i).conjTranspose * (K.op i) * PartialTrace (outerProduct ψ)) := by
    intro i
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have hsum : (∑ i, Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ)
        * (K.op i).conjTranspose))
      = Matrix.trace (PartialTrace (outerProduct ψ)) := by
    calc (∑ i, Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ)
          * (K.op i).conjTranspose))
        = ∑ i, Matrix.trace ((K.op i).conjTranspose * (K.op i)
            * PartialTrace (outerProduct ψ)) := by
          exact Finset.sum_congr rfl fun i _ => hcyc i
      _ = Matrix.trace ((∑ i, (K.op i).conjTranspose * (K.op i))
            * PartialTrace (outerProduct ψ)) := by
        rw [← Matrix.trace_sum, ← Finset.sum_mul]
      _ = Matrix.trace (1 * PartialTrace (outerProduct ψ)) := by rw [K.hcomplete]
      _ = Matrix.trace (PartialTrace (outerProduct ψ)) := by rw [Matrix.one_mul]
  calc (∑ i, krausBranchMass ψ K i)
      = ∑ i, (Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ)
          * (K.op i).conjTranspose)).re := by
        exact Finset.sum_congr rfl fun i _ => hmass i
    _ = (∑ i, Matrix.trace ((K.op i) * PartialTrace (outerProduct ψ)
          * (K.op i).conjTranspose)).re := by
        rw [← Complex.re_sum]
    _ = (Matrix.trace (PartialTrace (outerProduct ψ))).re := by rw [hsum]
    _ = 1 := by
        rw [trace_partialTrace, trace_outerProduct]
        have h2 : (∑ i, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
        rw [h2]
        norm_num

theorem secondMarginalState_trace (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Matrix.trace (secondMarginalState ψ) = 1 := by
  have h1 : Matrix.trace (secondMarginalState ψ) = Matrix.trace (outerProduct ψ) := by
    simp only [secondMarginalState, Matrix.trace, Matrix.diag_apply, secondMarginal]
    rw [Finset.sum_comm]
    rw [Fintype.sum_prod_type]
  rw [h1, trace_outerProduct]
  have h2 : (∑ i, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
  rw [h2]
  norm_num

theorem feedbackUnitary_mem (ψ : QState (Fin D × Fin E)) :
    (feedbackUnitary ψ).val ∈ Matrix.unitaryGroup (Fin E) ℂ := by
  exact (feedbackUnitary ψ).2

theorem feedbackState_firstMarginal (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    PartialTrace (outerProduct (feedbackState ψ)) = PartialTrace (outerProduct ψ) := by
  exact partialTrace_outerProduct_apply_tensorRight ψ (feedbackUnitary ψ).val
    (feedbackUnitary_mem ψ)

theorem negativity_nonneg {D E : ℕ} (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hρ : ρ.IsHermitian) : 0 ≤ negativity ρ hρ := by
  unfold negativity
  exact Finset.sum_nonneg fun j _ => by positivity

theorem negativity_of_isSeparableState {D E : ℕ}
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : ρ.IsHermitian)
    (hsep : Qatlib.Concepts.FiniteLocc.LOCCProgram.IsSeparableState ρ) :
    negativity ρ hρ = 0 := by
  have hPT : (Qatlib.Concepts.FiniteLocc.LOCCProgram.PartialTranspose ρ).PosSemidef :=
    Qatlib.Concepts.FiniteLocc.LOCCProgram.partialTranspose_posSemidef_of_isSeparableState ρ hsep
  have hnonneg : ∀ j, 0 ≤ (partialTransposeEigenvalues ρ hρ) j := by
    intro j
    exact ((Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
      (partialTranspose_hermitian hρ)).mp hPT) j
  unfold negativity
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)]
  intro j _
  have h1 : -(partialTransposeEigenvalues ρ hρ j) ≤ 0 := by
    linarith [hnonneg j]
  have h2 : max (-(partialTransposeEigenvalues ρ hρ j)) 0 ≤ 0 := by
    rw [max_eq_right h1]
  have h3 : 0 ≤ max (-(partialTransposeEigenvalues ρ hρ j)) 0 := le_max_right _ _
  exact le_antisymm h2 h3

theorem negativity_of_productState {D E : ℕ} (a : QState (Fin D)) (b : QState (Fin E))
    (ha : Normalized a) (hb : Normalized b)
    (hρ : (outerProduct (TensorState a b)).IsHermitian) :
    negativity (outerProduct (TensorState a b)) hρ = 0 := by
  have hsep : Qatlib.Concepts.FiniteLocc.LOCCProgram.IsSeparableState (outerProduct (TensorState a b)) :=
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.isSeparableState_outerProduct_iff_isProductState (TensorState a b)
      (normalized_tensorState ha hb)).mpr ⟨a, b, rfl⟩
  exact negativity_of_isSeparableState _ hρ hsep

def SchurConcavityShannonGeneral {D : ℕ} (a b : Fin D → ℝ) : Prop :=
  Qatlib.Concepts.FiniteLocc.LOCCProgram.Majorizes a b →
  (∀ j, 0 ≤ a j) → (∀ j, 0 ≤ b j) →
  (∑ j, Real.negMulLog (b j)) ≥ (∑ j, Real.negMulLog (a j))

def GeneralInstrumentAverageEntropyBound (D E n : ℕ) : Prop :=
  ∀ (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n) (hψ : Normalized ψ),
    (∀ i : Fin n, krausBranchMass ψ K i > 0) →
    (∑ i : Fin n, krausBranchMass ψ K i *
      (∑ j, Real.negMulLog (krausBranchSpectrum ψ K i j / krausBranchMass ψ K i)))
      ≤ Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs.schmidtEntropy ψ hψ

def MajorizationTTransformDecomposition (D : ℕ) (a b : Fin D → ℝ) : Prop :=
  ∃ (l : List (Fin D × Fin D × ℝ)),
    (∀ p ∈ l, 0 ≤ p.2.2 ∧ p.2.2 ≤ 1) ∧
    b = List.foldl (fun s (k, l', θ) => Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs.tTransformSpectrum s θ k l') a l

def DeterministicConversionCriterion (D E : ℕ) : Prop :=
  ∀ (ψ φ : QState (Fin D × Fin E)) (hψ : Normalized ψ) (hφ : Normalized φ),
    Qatlib.Concepts.FiniteLocc.LOCCProgram.Majorizes (Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs.schmidtSpectrum ψ hψ)
      (Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs.schmidtSpectrum φ hφ) →
      ∃ (protocol : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E),
        Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccComplete protocol ∧
          Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccChannel protocol (outerProduct ψ) = outerProduct φ

end Qatlib.Concepts.Entanglement.Separability
