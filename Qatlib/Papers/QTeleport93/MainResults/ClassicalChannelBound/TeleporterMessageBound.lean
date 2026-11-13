/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.ChannelIdentity

/-!
# A general one way teleporter message bound

`choiVector` is the unnormalized maximally entangled vector used to test recovery with a
reference. The auxiliary identities compute its norm, projector expectation, and expectations
against operators tensored with an identity.

`exact_one_way_teleporter_messages` combines these identities with complete positivity,
conditional quantum channels, and a common raw branch sum to prove that exact recovery of an `n`
dimensional system needs at least `n * n` messages. This formalizes a general message counting
consequence of the teleportation communication requirement in [BennettEtAl1993Teleportation].

## Main statements

* `choi_raw_family_sum` computes the sum of raw branches on the entangled test operator.
* `choiVector_tensor_expectation` turns a tensor expectation into a trace.
* `exact_one_way_teleporter_messages` proves the classical alphabet lower bound.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- The unnormalized maximally entangled vector with coefficient one on matching basis indices
and zero elsewhere. -/
noncomputable def choiVector (n : ℕ) : QState (Fin n × Fin n) :=
  fun p => if p.1 = p.2 then 1 else 0

/-- The squared norm of the unnormalized maximally entangled vector in dimension `n` is `n`. -/
theorem choiVector_inner (n : ℕ) :
    star (choiVector n) ⬝ᵥ choiVector n = (n : ℂ) := by
  classical
  simp [dotProduct, choiVector, Fintype.sum_prod_type]

/-- The expectation of the outer product of `choiVector n` in that same vector is `n * n`. -/
theorem choiVector_projector_expectation (n : ℕ) :
    star (choiVector n) ⬝ᵥ (outerProduct (choiVector n) *ᵥ choiVector n) =
      (n : ℂ) * n := by
  rw [outerProduct_mulVec, dotProduct_smul]
  change (star (choiVector n) ⬝ᵥ choiVector n) *
    (star (choiVector n) ⬝ᵥ choiVector n) = _
  rw [choiVector_inner]

/-- If the raw maps sum to the input trace times `σ`, their reference extensions on the Choi
outer product sum to `σ` tensored with the identity. -/
theorem choi_raw_family_sum {M : Type} [Fintype M] {n d : ℕ}
    (T : M → Operator n →ₗ[ℂ] Operator d) (σ : Operator d)
    (hns : ∀ A, ∑ m, T m A = Matrix.trace A • σ) :
    (∑ m, tensorLeft (T m) (outerProduct (choiVector n))) =
      TensorGate σ (1 : Operator n) := by
  classical
  ext ⟨i,r⟩ ⟨j,s⟩
  have he := congrArg (fun A : Operator d => A i j)
    (hns (fun a b => outerProduct (choiVector n) (a,r) (b,s)))
  have ht : Matrix.trace (fun a b => outerProduct (choiVector n) (a,r) (b,s)) =
      if r = s then 1 else 0 := by
    simp [Matrix.trace, outerProduct_apply, choiVector, mul_ite, eq_comm]
  simpa [Matrix.sum_apply, tensorLeft, ht, tensorGate_apply, Matrix.one_apply, mul_comm] using! he

/-- Applying a complex linear map to the first factor of `σ` tensored with an identity gives its
image of `σ` tensored with that identity. -/
theorem tensorLeft_tensor_identity {d n r : ℕ}
    (S : Operator d →ₗ[ℂ] Operator n) (σ : Operator d) :
    tensorLeft S (TensorGate σ (1 : Operator r)) =
      TensorGate (S σ) (1 : Operator r) := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hab : a = b
  · subst b
    simp [tensorLeft, tensorGate_apply]
  · simp only [tensorLeft, tensorGate_apply, Matrix.one_apply_ne hab, mul_zero]
    change S 0 i j = 0
    simp

/-- The expectation of `A` tensored with the identity in the unnormalized maximally entangled
vector equals the trace of `A`. -/
theorem choiVector_tensor_expectation {n : ℕ} (A : Operator n) :
    star (choiVector n) ⬝ᵥ
      (TensorGate A (1 : Operator n) *ᵥ choiVector n) = Matrix.trace A := by
  classical
  simp [dotProduct, Matrix.mulVec, choiVector, Fintype.sum_prod_type,
    tensorGate_apply, Matrix.one_apply, Matrix.trace, mul_ite, ite_mul]

/-- Completely positive raw branches with a common trace one replacement sum and conditional
quantum channels giving exact recovery require at least `n * n` messages
[BennettEtAl1993Teleportation]. -/
theorem exact_one_way_teleporter_messages
    {M : Type} [Fintype M] {n d : ℕ}
    (T : M → Operator n →ₗ[ℂ] Operator d)
    (hT : ∀ m, CompletelyPositive (T m))
    (S : M → QuantumChannel d n) (σ : Operator d)
    (htrace : Matrix.trace σ = 1)
    (hns : ∀ A, ∑ m, T m A = Matrix.trace A • σ)
    (hexact : ∀ ρ, IsDensityOperator ρ → ∑ m, (S m).map (T m ρ) = ρ) :
    n * n ≤ Fintype.card M := by
  classical
  let G : Operator n →ₗ[ℂ] Operator n := ∑ m, (S m).map.comp (T m)
  have hfix : ∀ A, ∑ m, (S m).map (T m A) = A := by
    intro A
    simpa [G] using! density_identity_on_all_operators G (by simpa [G] using! hexact) A
  let B := outerProduct (choiVector n)
  let q : M → M → ℝ := fun s m =>
    (star (choiVector n) ⬝ᵥ
      (tensorLeft (S s).map (tensorLeft (T m) B) *ᵥ choiVector n)).re
  have hq : ∀ s m, 0 ≤ q s m := by
    intro s m
    exact (tensorLeft_posSemidef (S s).completelyPositive
      (tensorLeft_posSemidef (hT m) (outerProduct_posSemidef _))).re_dotProduct_nonneg _
  have hsum : ∀ s, ∑ m, q s m = 1 := by
    intro s
    have he : (∑ m, tensorLeft (S s).map (tensorLeft (T m) B)) =
        TensorGate ((S s).map σ) (1 : Operator n) := by
      calc
        _ = tensorLeft (S s).map (∑ m, tensorLeft (T m) B) := by
          ext ⟨i,r⟩ ⟨j,t⟩
          simp only [Matrix.sum_apply, tensorLeft]
          have hb : (fun a b => ∑ m, T m (fun c e => B (c,r) (e,t)) a b) =
              ∑ m, T m (fun c e => B (c,r) (e,t)) := by
            ext a b
            simp only [Matrix.sum_apply]
          rw [hb, map_sum, Matrix.sum_apply]
        _ = _ := by
          rw [choi_raw_family_sum T σ hns, tensorLeft_tensor_identity]
    have hv := congrArg
      (fun A => (star (choiVector n) ⬝ᵥ (A *ᵥ choiVector n)).re) he

    rw [choiVector_tensor_expectation, (S s).tracePreserving σ, htrace] at hv
    simpa [q, Matrix.sum_mulVec, dotProduct_sum] using! hv
  have hdiag : ∑ m, q m m = ((n : ℝ) * n) := by
    have he : (∑ m, tensorLeft (S m).map (tensorLeft (T m) B)) = B := by
      ext ⟨i,r⟩ ⟨j,s⟩
      simpa [Matrix.sum_apply, tensorLeft] using! congrArg (fun A : Operator n => A i j)
        (hfix (fun a b => B (a,r) (b,s)))
    have hv := congrArg
      (fun A => (star (choiVector n) ⬝ᵥ (A *ᵥ choiVector n)).re) he
    simpa [q, B, Matrix.sum_mulVec, dotProduct_sum,
      choiVector_projector_expectation] using! hv
  have hle : ∀ m, q m m ≤ 1 := by
    intro m
    rw [← hsum m]
    exact Finset.single_le_sum (fun j _ => hq m j) (Finset.mem_univ m)
  have hbound := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hle m)
  rw [hdiag] at hbound
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hbound
  exact_mod_cast hbound

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
