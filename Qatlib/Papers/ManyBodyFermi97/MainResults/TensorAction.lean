/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.SignedOrbit
import Mathlib.Data.Fintype.Perm

/-!
# Common one-body actions preserve antisymmetry

`commonApply` applies the same matrix to every particle coordinate, and
`commonApply_preserves_antisym` proves that this action preserves antisymmetric states. The
module also gives an explicit two-particle example in which applying a bit flip to only one
coordinate fails to preserve antisymmetry.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `commonApply_perm`: Applying the same one-particle matrix to all coordinates commutes with
  particle permutations.
* `commonApply_preserves_antisym`: Applying the same one-particle matrix to every coordinate
  preserves antisymmetry.
* `single_x_not_antisym`: Applying the bit-flip matrix only to the first particle of the raw
  signed identity-label state produces a state that is not antisymmetric.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.TensorAction
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

/-- Reindexes a particle configuration by the permutation `τ`. -/
def permCfg {n m : ℕ} (x : Fin n → Fin m) (τ : Equiv.Perm (Fin n)) : Fin n → Fin m :=
  fun i => x (τ i)

/-- Acts on state amplitudes by precomposition with particle reindexing. -/
def permState {n m : ℕ} (τ : Equiv.Perm (Fin n)) (ψ : QState (Fin n → Fin m)) :
    QState (Fin n → Fin m) := fun x => ψ (permCfg x τ)

/-- A state is antisymmetric when every particle reindexing multiplies its amplitudes by the
permutation sign. -/
def IsAntisym {n m : ℕ} (ψ : QState (Fin n → Fin m)) : Prop :=
  ∀ (τ : Equiv.Perm (Fin n)) (x : Fin n → Fin m),
    ψ (permCfg x τ) = SignedOrbit.parity τ * ψ x

/-- Antisymmetry is equivalent to every particle permutation acting on the state by its sign
scalar. -/
theorem isAntisym_iff {n m : ℕ} (ψ : QState (Fin n → Fin m)) :
    IsAntisym ψ ↔ ∀ τ : Equiv.Perm (Fin n),
      permState τ ψ = (SignedOrbit.parity τ) • ψ := by
  constructor
  · intro h τ
    funext x
    exact h τ x
  · intro h τ x
    exact congrFun (h τ) x

/-- The equivalence on configurations induced by particle reindexing, with inverse given by the
inverse permutation. -/
def shiftCfg {n m : ℕ} (τ : Equiv.Perm (Fin n)) :
    (Fin n → Fin m) ≃ (Fin n → Fin m) where
  toFun b := fun i => b (τ i)
  invFun b := fun i => b (τ.symm i)
  left_inv b := by funext i; simp
  right_inv b := by funext i; simp

/-- Permuting the indices of a finite product of complex numbers leaves the product unchanged. -/
theorem prod_comp_perm {n : ℕ} (τ : Equiv.Perm (Fin n)) (g : Fin n → ℂ) :
    (∏ i, g (τ i)) = ∏ i, g i :=
  Fintype.prod_equiv τ (fun i => g (τ i)) g (fun _ => rfl)

/-- Applies the tensor power of the same one-particle matrix to all particle coordinates. -/
def commonApply {n m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (ψ : QState (Fin n → Fin m)) : QState (Fin n → Fin m) :=
  fun x => ∑ b : Fin n → Fin m, (∏ i : Fin n, U (x i) (b i)) * ψ b

/-- Applies the one-particle matrix `U` to coordinate `k`, leaving the other coordinates fixed. -/
def singleApply {n m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (k : Fin n)
    (ψ : QState (Fin n → Fin m)) : QState (Fin n → Fin m) :=
  fun x => ∑ y : Fin m, U (x k) y * ψ (Function.update x k y)

/-- The common tensor action commutes with complex scalar multiplication of states. -/
theorem commonApply_smul {n m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (ψ : QState (Fin n → Fin m)) :
    commonApply U (c • ψ) = c • commonApply U ψ := by
  funext x
  simp only [commonApply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Applying the same one-particle matrix to all coordinates commutes with particle
permutations. -/
theorem commonApply_perm {n m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (τ : Equiv.Perm (Fin n)) (ψ : QState (Fin n → Fin m)) :
    commonApply U (permState τ ψ) = permState τ (commonApply U ψ) := by
  funext x
  simp only [commonApply, permState, permCfg]
  refine Fintype.sum_equiv (shiftCfg τ)
    (fun b => (∏ i, U (x i) (b i)) * ψ (fun i => b (τ i)))
    (fun c => (∏ i, U (x (τ i)) (c i)) * ψ c) ?_
  intro b
  simp only [shiftCfg, Equiv.coe_fn_mk]
  have hprod : (∏ i, U (x i) (b i)) = ∏ i, U (x (τ i)) (b (τ i)) :=
    Fintype.prod_equiv τ.symm (fun i => U (x i) (b i))
      (fun j => U (x (τ j)) (b (τ j))) (fun i => by simp)
  rw [hprod]

/-- Applying the same one-particle matrix to every coordinate preserves antisymmetry.
[AbramsLloyd1997] -/
theorem commonApply_preserves_antisym {n m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    {ψ : QState (Fin n → Fin m)} (hψ : IsAntisym ψ) :
    IsAntisym (commonApply U ψ) := by
  rw [isAntisym_iff] at hψ ⊢
  intro τ
  have hcomm := congrArg (commonApply U) (hψ τ)
  rw [commonApply_smul] at hcomm
  rw [← commonApply_perm, hcomm]

/-- An antisymmetric state's amplitude vanishes at a configuration fixed by a permutation of
sign `-1`. [AbramsLloyd1997] -/
theorem antisym_odd_fixed {n m : ℕ} {ψ : QState (Fin n → Fin m)}
    (h : IsAntisym ψ) (τ : Equiv.Perm (Fin n))
    (hτ : SignedOrbit.parity τ = -1) (x : Fin n → Fin m)
    (hx : permCfg x τ = x) : ψ x = 0 := by
  have h1 : ψ x = -1 * ψ x := by
    have := h τ x
    rwa [hx, hτ] at this
  have h2 : ψ x - (-1 * ψ x) = 0 := sub_eq_zero.mpr h1
  have h3 : (2 : ℂ) * ψ x = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- The bit-flip matrix on two labels, with ones off the diagonal and zeros on the diagonal. -/
def flip : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i ≠ j then 1 else 0

/-- The constant-zero configuration of two particles with two possible labels. -/
def zeroCfg : Fin 2 → Fin 2 := fun _ => 0

/-- The configuration assigning each of the two particles its own index as label. -/
def idLabel : Fin 2 → Fin 2 := fun i => i

/-- Applying the bit-flip matrix only to the first particle of the raw signed identity-label
state produces a state that is not antisymmetric. [AbramsLloyd1997] -/
theorem single_x_not_antisym :
    ¬ IsAntisym (singleApply flip 0 (SignedOrbit.raw idLabel)) := by
  intro h
  have hpar : SignedOrbit.parity (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = -1 := by
    simp [SignedOrbit.parity, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  have hfix : permCfg zeroCfg (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = zeroCfg := by
    funext i; simp [permCfg, zeroCfg]
  have hzero := antisym_odd_fixed h (Equiv.swap (0 : Fin 2) (1 : Fin 2)) hpar zeroCfg hfix

  have hupd : Function.update zeroCfg 0 (1 : Fin 2) = Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
    funext i; fin_cases i <;> simp [zeroCfg]
  have hidinj : Function.Injective idLabel := fun a b hab => hab
  have hval : singleApply flip 0 (SignedOrbit.raw idLabel) zeroCfg = -1 := by
    have hraw : SignedOrbit.raw idLabel (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = -1 := by
      have := SignedOrbit.raw_at_permuted idLabel hidinj
        (Equiv.swap (0 : Fin 2) (1 : Fin 2))
      simpa [SignedOrbit.permuted, idLabel, hpar] using! this
    simp only [singleApply, Fin.sum_univ_two, zeroCfg, flip]
    rw [hupd]
    norm_num [hraw]
  rw [hzero] at hval
  norm_num at hval

end Qatlib.Papers.ManyBodyFermi97.MainResults.TensorAction
