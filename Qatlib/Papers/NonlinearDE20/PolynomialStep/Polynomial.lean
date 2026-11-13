/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.ActualEulerVariance

/-!
# Polynomial fields from tensor-power compression

The equivalence `targetEnvironmentEquiv` separates one target from `m` environment copies.
Compressing an interaction matrix against `tensorPower m x` defines `polynomialMatrix` and the
forced field `polynomialField`. The module expands its entries and proves the exact reduced
variance identity for `polynomialJointEuler` in the framework of [LloydEtAl2020].

## Main statements

* `polynomialMatrix_entries`: Each compressed entry is a double sum of interaction entries
  weighted by `m` conjugate and `m` unconjugated system amplitudes.
* `environmentPower_normalized`: The tensor power of a vector with squared norm one also has
  squared norm one.
* `polynomialEuler_variance`: For normalized input, the reduced joint polynomial Euler output
  differs from its pure system target by `dt * star dt` times the reduced interaction variance.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix
open Qatlib.Papers.NonlinearDE20.AffineLift.Model

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

/-- The equivalence separating the first coordinate of an `m + 1`-copy label from its remaining
`m` coordinates. -/
def targetEnvironmentEquiv (I : Type) (m : ℕ) : (Fin (m+1)→I)≃I×(Fin m→I) where
  toFun u:=(u 0,fun j=>u j.succ)
  invFun p:=Fin.cons p.1 p.2
  left_inv u:=by funext k;refine Fin.cases rfl (fun _=>rfl) k
  right_inv p:=by rcases p with ⟨a,r⟩;rfl

/-- Under the target-environment equivalence, inflating `x` by its `m`th tensor power equals its
`m + 1`st tensor power [LloydEtAl2020]. -/
theorem product_input_arity {I : Type} (m : ℕ) (x : I→ℂ) (u : Fin (m+1)→I) :
    inflate (tensorPower m x) x (targetEnvironmentEquiv I m u)=tensorPower (m+1) x u := by
  simp only [inflate,tensorPower,targetEnvironmentEquiv,Equiv.coe_fn_mk]
  rw [Fin.prod_univ_succ]

/-- The target-environment basis has cardinality equal to the system dimension raised to `m +
1`. -/
theorem interaction_dimension (I : Type) [Fintype I] (m : ℕ) :
    Fintype.card (I×(Fin m→I))=(Fintype.card I)^(m+1) := by
  simp [Fintype.card_pi,pow_succ,mul_comm]

/-- The interaction matrix compressed against the `m`th tensor power of the system vector. -/
def polynomialMatrix {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (x : I→ℂ) : Matrix I I ℂ :=
  compression B (tensorPower m x)

/-- Each compressed entry is a double sum of interaction entries weighted by `m` conjugate and
`m` unconjugated system amplitudes [LloydEtAl2020]. -/
theorem polynomialMatrix_entries {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (x : I→ℂ) (i j : I) :
    polynomialMatrix m B x i j=∑ a : Fin m→I,∑ b : Fin m→I,
      (∏ k : Fin m,star (x (a k)))*B (i,a) (j,b)*(∏ k : Fin m,x (b k)) := by
  rw [polynomialMatrix,compression_entries]
  simp only [tensorPower,star_prod]

/-- The tensor power of a vector with squared norm one also has squared norm one. -/
theorem environmentPower_normalized {I : Type} [Fintype I] (m : ℕ) (x : I→ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (∑ a : Fin m→I,Complex.normSq (tensorPower m x a))=1 := by
  change bornMass (tensorPower m x)=1
  rw [tensorPower_bornMass]
  change (∑ i : I,Complex.normSq (x i))^m=1
  rw [hx,one_pow]

/-- The vector field given by the linear term, the compressed polynomial interaction applied to
`x`, and the forcing vector. -/
def polynomialField {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) : I→ℂ :=
  A*ᵥ x+polynomialMatrix m B x*ᵥ x+b

/-- The joint Euler vector combining the inflated affine update with the interaction applied to
the product input. -/
def polynomialJointEuler {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ) : I×(Fin m→I)→ℂ :=
  inflate (tensorPower m x) (x+dt •(A*ᵥ x+b))+dt •(B*ᵥ inflate (tensorPower m x) x)

/-- For normalized input, the reduced joint polynomial Euler output differs from its pure system
target by `dt * star dt` times the reduced interaction variance. -/
theorem polynomialEuler_variance {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (outer (polynomialJointEuler m A B b x dt)).traceRight-outer (x+dt •polynomialField m A B b x)=
      (dt*star dt) •reducedVariance (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x) := by
  have h := productEuler_variance (tensorPower m x) (environmentPower_normalized m x hx)
    (x+dt •(A*ᵥ x+b)) (B*ᵥ inflate (tensorPower m x) x) (-dt)
  have hc : capture (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x)=polynomialMatrix m B x*ᵥ x :=
    (compression_action B (tensorPower m x) x).symm
  have he : x+dt •(A*ᵥ x+b)+dt •capture (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x)=
      x+dt •polynomialField m A B b x := by
    rw [hc]
    unfold polynomialField
    module
  simpa only [neg_smul,sub_neg_eq_add,star_neg,neg_mul_neg,he,polynomialJointEuler] using h

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
