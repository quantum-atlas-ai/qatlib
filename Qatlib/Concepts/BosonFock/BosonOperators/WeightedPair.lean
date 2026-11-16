/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # The adjoint of a genuine finite weighted coefficient pairing

Demand: LinearOptics10 Theorem 17. The factorial-weighted Fock pairing is
nondegenerate. An explicit finite weighted conjugate transpose constructs
its unique adjoint for every actual complex-linear map.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open ComplexConjugate
namespace Qatlib.Concepts.BosonFock.BosonOperators.WeightedPair
variable {I : Type*} [Fintype I]

/-- The actual finite weighted conjugate-linear/linear coefficient pairing. -/
def pair (w : I → ℝ) (a b : I → ℂ) : ℂ := ∑ i, conj (a i) * b i * (w i : ℂ)

/-- A concrete matrix entry of an actual linear operator, evaluated on a coordinate basis. -/
def entry (L : (I → ℂ) →ₗ[ℂ] (I → ℂ)) (i j : I) : ℂ := L (Pi.single j 1) i

/-- Every actual linear operator is determined by these finite basis entries. -/
theorem expand (L : (I → ℂ) →ₗ[ℂ] (I → ℂ)) (b : I → ℂ) (i : I) :
    L b i = ∑ j, b j * entry L i j := by
  have hb : b = ∑ j, b j • Pi.single j (1 : ℂ) := by ext j; simp [Pi.single_apply]
  calc
    _ = L (∑ j, b j • Pi.single j (1 : ℂ)) i := congrArg (fun x => L x i) hb
    _ = _ := by simp [entry]

/-- The actual weighted conjugate transpose as a complex-linear map. -/
def adjoint (w : I → ℝ) (L : (I → ℂ) →ₗ[ℂ] (I → ℂ)) : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
  LinearMap.pi (fun j => ∑ i, (conj (entry L i j) * (w i : ℂ) / (w j : ℂ)) •
    (LinearMap.proj i : (I → ℂ) →ₗ[ℂ] ℂ))

/-- The explicit weighted transpose satisfies the actual adjoint pairing identity. -/
theorem pairing (w : I → ℝ) (hw : ∀ i, w i ≠ 0)
    (L : (I → ℂ) →ₗ[ℂ] (I → ℂ)) (a b : I → ℂ) :
    pair w a (L b) = pair w (adjoint w L a) b := by
  have hwc (j : I) : (w j : ℂ) ≠ 0 := by exact_mod_cast hw j
  have hexpand : L b = fun i => ∑ j, b j * entry L i j := funext (expand L b)
  unfold pair
  rw [hexpand]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [adjoint, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, map_sum, map_mul, map_div₀, Complex.conj_conj,
    Complex.conj_ofReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hwc j]

/-- Testing against actual coordinate vectors separates every coefficient vector. -/
theorem nondegenerate (w : I → ℝ) (hw : ∀ i, w i ≠ 0) (a b : I → ℂ)
    (heq : ∀ q, pair w a q = pair w b q) : a = b := by
  funext j
  have hj := heq (Pi.single j 1)
  simp [pair, Pi.single_apply, hw j] at hj
  simpa using congrArg conj hj

/-- Every actual finite complex-linear operator has a unique adjoint for this pairing. -/
theorem existsUnique (w : I → ℝ) (hw : ∀ i, w i ≠ 0)
    (L : (I → ℂ) →ₗ[ℂ] (I → ℂ)) :
    ∃! D : (I → ℂ) →ₗ[ℂ] (I → ℂ), ∀ a b, pair w a (L b) = pair w (D a) b := by
  refine ⟨adjoint w L, pairing w hw L, ?_⟩
  intro D hD
  apply LinearMap.ext
  intro a
  exact nondegenerate w hw _ _ (fun b => (hD a b).symm.trans (pairing w hw L a b))

end Qatlib.Concepts.BosonFock.BosonOperators.WeightedPair
