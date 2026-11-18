/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QPrograms.MeasureProg
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

@[expose] public section

/-!
# Independent product execution of measurement programs

The single-instrument interface does not assert independence of repeated sampling. This module provides the
bridge for the case that is actually available in a straight-line setting: two measurement
programs run in parallel on disjoint tensor factors of a product input state. The joint branch
execution is the Kronecker product of the two history branch maps (`MatrixMap.kron`), and the
missing double-sided tensor action law `kronPairLemma` shows that it factorizes into the matrix
tensor product of the two unnormalized post states. Together with the public
`trace_tensorGate` this yields `pairWeightEq`: the joint history weight is the product of the
two program weights. The distribution layer packages the Born history weights of one program as
a public `FinDist`, the operator-level counterpart of `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.independentPair`.

Independence here belongs to disjoint system copies only: within a single program one adaptive
trajectory still chains its instruments through unnormalized outputs (`progProbPair`) and is
not i.i.d. Loops, termination, and expected time remain out of scope.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QPrograms.MeasureProg

namespace Qatlib.Concepts.QPrograms.ProdDist

variable {O : Type} [Fintype O] {D : ℕ}
variable {O₁ O₂ : Type} [Fintype O₁] [Fintype O₂] {D₁ D₂ E₁ E₂ : ℕ}

/-- The double-sided tensor action law for the Kronecker product of operator maps: applying
`MatrixMap.kron T₁ T₂` to a matrix tensor product applies `T₁` and `T₂` to their factors. The
public library proves the one-sided reference-system case (`kron_id_apply`); this two-sided
form is proved entrywise from the public `kron_def` expansion. -/
theorem kronPairLemma (T₁ : Operator D₁ →ₗ[ℂ] Operator E₁)
    (T₂ : Operator D₂ →ₗ[ℂ] Operator E₂) (A : Operator D₁) (B : Operator D₂) :
    MatrixMap.kron T₁ T₂ (TensorGate A B) = TensorGate (T₁ A) (T₂ B) := by
  ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
  rw [MatrixMap.kron_def]
  simp only [tensorGate_apply]
  have hT₁ : T₁ A b₁ b₂
      = ∑ p : Fin D₁ × Fin D₁, T₁ (Matrix.single p.1 p.2 1) b₁ b₂ * A p.1 p.2 := by
    have hc : ∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, A a₁ a₂ * T₁ (Matrix.single a₁ a₂ 1) b₁ b₂
          = T₁ A b₁ b₂ :=
      congrArg (fun S : MatrixMap (Fin D₁) (Fin E₁) ℂ => S A b₁ b₂) (MatrixMap.choi_map_inv T₁)
    rw [← hc]
    rw [← Fintype.sum_prod_type' fun a₁ a₂ => A a₁ a₂ * T₁ (Matrix.single a₁ a₂ 1) b₁ b₂]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hT₂ : T₂ B d₁ d₂
      = ∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2 := by
    have hc : ∑ c₁ : Fin D₂, ∑ c₂ : Fin D₂, B c₁ c₂ * T₂ (Matrix.single c₁ c₂ 1) d₁ d₂
          = T₂ B d₁ d₂ :=
      congrArg (fun S : MatrixMap (Fin D₂) (Fin E₂) ℂ => S B d₁ d₂) (MatrixMap.choi_map_inv T₂)
    rw [← hc]
    rw [← Fintype.sum_prod_type' fun c₁ c₂ => B c₁ c₂ * T₂ (Matrix.single c₁ c₂ 1) d₁ d₂]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have m1 : (∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, ∑ c₁ : Fin D₂, ∑ c₂ : Fin D₂,
        T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * T₂ (Matrix.single c₁ c₂ 1) d₁ d₂
          * (A a₁ a₂ * B c₁ c₂))
      = ∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, ∑ q : Fin D₂ × Fin D₂,
        (T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
          * (T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) := by
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
    calc (∑ c₁ : Fin D₂, ∑ c₂ : Fin D₂,
          T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * T₂ (Matrix.single c₁ c₂ 1) d₁ d₂
            * (A a₁ a₂ * B c₁ c₂))
        = ∑ q : Fin D₂ × Fin D₂,
          T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * T₂ (Matrix.single q.1 q.2 1) d₁ d₂
            * (A a₁ a₂ * B q.1 q.2) :=
          (Fintype.sum_prod_type' fun c₁ c₂ =>
            T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * T₂ (Matrix.single c₁ c₂ 1) d₁ d₂
              * (A a₁ a₂ * B c₁ c₂)).symm
      _ = ∑ q : Fin D₂ × Fin D₂,
          (T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
            * (T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) :=
          Finset.sum_congr rfl fun q _ => by ring
  have m2 : (∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, ∑ q : Fin D₂ × Fin D₂,
        (T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
          * (T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2))
      = (∑ p : Fin D₁ × Fin D₁, T₁ (Matrix.single p.1 p.2 1) b₁ b₂ * A p.1 p.2)
        * (∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) := by
    calc (∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, ∑ q : Fin D₂ × Fin D₂,
          (T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
            * (T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2))
        = ∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁,
          (T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
            * (∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) :=
          Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ =>
            (Finset.mul_sum _ _ _).symm
      _ = ∑ a₁ : Fin D₁,
          (∑ a₂ : Fin D₁, T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
            * (∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) :=
          Finset.sum_congr rfl fun a₁ _ => (Finset.sum_mul _ _ _).symm
      _ = (∑ a₁ : Fin D₁, ∑ a₂ : Fin D₁, T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂)
          * (∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) :=
          (Finset.sum_mul _ _ _).symm
      _ = (∑ p : Fin D₁ × Fin D₁, T₁ (Matrix.single p.1 p.2 1) b₁ b₂ * A p.1 p.2)
          * (∑ q : Fin D₂ × Fin D₂, T₂ (Matrix.single q.1 q.2 1) d₁ d₂ * B q.1 q.2) := by
          rw [← Fintype.sum_prod_type' fun a₁ a₂ =>
            T₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * A a₁ a₂]
  rw [m1, m2, hT₁, hT₂]

/-- The joint unnormalized post-measurement state of two measurement programs run in parallel
on disjoint tensor factors of a product input state: the Kronecker product of their history
branch maps applied to the product input. -/
noncomputable def pairPost (policy₁ : List O₁ → Instrument O₁ D₁ D₁)
    (policy₂ : List O₂ → Instrument O₂ D₂ D₂)
    (ρ₁ : Operator D₁) (ρ₂ : Operator D₂) (os₁ : List O₁) (os₂ : List O₂) :
    Matrix (Fin D₁ × Fin D₂) (Fin D₁ × Fin D₂) ℂ :=
  MatrixMap.kron (progBranch policy₁ os₁) (progBranch policy₂ os₂) (TensorGate ρ₁ ρ₂)

/-- The parallel execution factorizes: the joint post state of the two programs is the matrix
tensor product of their individual unnormalized post states. -/
theorem pairPostEq (policy₁ : List O₁ → Instrument O₁ D₁ D₁)
    (policy₂ : List O₂ → Instrument O₂ D₂ D₂)
    (ρ₁ : Operator D₁) (ρ₂ : Operator D₂) (os₁ : List O₁) (os₂ : List O₂) :
    pairPost policy₁ policy₂ ρ₁ ρ₂ os₁ os₂
      = TensorGate (progPost policy₁ ρ₁ os₁) (progPost policy₂ ρ₂ os₂) :=
  kronPairLemma (progBranch policy₁ os₁) (progBranch policy₂ os₂) ρ₁ ρ₂

/-- The joint history weight of two programs run in parallel on disjoint systems: the real
trace of the joint unnormalized post state. -/
noncomputable def pairWeight (policy₁ : List O₁ → Instrument O₁ D₁ D₁)
    (policy₂ : List O₂ → Instrument O₂ D₂ D₂)
    (ρ₁ : Operator D₁) (ρ₂ : Operator D₂) (os₁ : List O₁) (os₂ : List O₂) : ℝ :=
  (Matrix.trace (pairPost policy₁ policy₂ ρ₁ ρ₂ os₁ os₂)).re

/-- The independence bridge of disjoint copies: the joint weight of two program histories on a
product input is the product of the individual program weights, on positive semidefinite
inputs. -/
theorem pairWeightEq (policy₁ : List O₁ → Instrument O₁ D₁ D₁)
    (policy₂ : List O₂ → Instrument O₂ D₂ D₂)
    {ρ₁ : Operator D₁} (hρ₁ : ρ₁.PosSemidef) {ρ₂ : Operator D₂} (hρ₂ : ρ₂.PosSemidef)
    (os₁ : List O₁) (os₂ : List O₂) :
    pairWeight policy₁ policy₂ ρ₁ ρ₂ os₁ os₂
      = progProb policy₁ ρ₁ os₁ * progProb policy₂ ρ₂ os₂ := by
  rw [pairWeight, pairPostEq, trace_tensorGate, progTraceEq policy₁ hρ₁ os₁,
    progTraceEq policy₂ hρ₂ os₂]
  simp

/-- The Born history weights of all length-`n` trajectories of a program on a density input,
packaged as a public finite probability distribution. -/
noncomputable def histDist (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (n : ℕ) : FinDist (Fin n → O) where
  prob xs := histProb policy ρ n xs
  nonneg xs := progProbNonneg policy hρ.1 (List.ofFn xs)
  sum_one := sumHistProbOne policy n hρ

/-- The mass that the history distribution puts on one trajectory is its program history
weight. -/
theorem histDistProb (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (n : ℕ) (xs : Fin n → O) :
    (histDist policy hρ n).prob xs = histProb policy ρ n xs :=
  rfl

end Qatlib.Concepts.QPrograms.ProdDist
