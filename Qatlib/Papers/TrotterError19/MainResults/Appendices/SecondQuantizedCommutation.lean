/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic

@[expose] public section

/-!
# Second-quantized commutation rules

Lemma D.3 of [ChildsEtAl2021Trotter] records the commutation rules of the number-conserving
bilinears `A_j^† A_k` built from fermionic creation and annihilation operators.  This module
fixes the two-mode Jordan-Wigner representation on the four-dimensional Fock space
`ℂ² ⊗ ℂ²` and verifies all three rules by explicit matrix computation: the exchange rule
`[A_j^† A_k, A_l^† A_m] = δ_{kl} A_j^† A_m − δ_{jm} A_l^† A_k`, the number-operator rule
`[A_j^† A_k, N_l] = δ_{kl} A_j^† A_l − δ_{jl} A_l^† A_k`, and the two-number-operator rule
with `N_l N_m`. The scope is the finite two-mode model.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

/-- The annihilation operator of mode `0`, `b ⊗ I` with `b = |0⟩⟨1|`: it removes the
excitation of the first tensor factor. -/
def annihMode0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The annihilation operator of mode `1`, `Z ⊗ b` with its Jordan-Wigner string. -/
def annihMode1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0]

/-- The creation operator of mode `0`, the conjugate transpose of `annihMode0`. -/
def createMode0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The creation operator of mode `1`, the conjugate transpose of `annihMode1`. -/
def createMode1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0]

/-- The two annihilation operators `A₀` and `A₁` of the model. -/
def annihTwo (j : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ := ![annihMode0, annihMode1] j

/-- The two creation operators `A₀^†` and `A₁^†` of the model. -/
def createTwo (j : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ := ![createMode0, createMode1] j

/-- The number-conserving bilinear `A_j^† A_k`. -/
def numberBilinear (j k : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  createTwo j * annihTwo k

/-- The number operator `N_j = A_j^† A_j` of mode `j`. -/
def numberOp (j : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ := numberBilinear j j

/-- The creation operators are the conjugate transposes of the annihilation operators. -/
theorem createTwo_eq_conjTranspose (j : Fin 2) : createTwo j = (annihTwo j)ᴴ := by
  fin_cases j <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    simp [createTwo, annihTwo, createMode0, createMode1, annihMode0, annihMode1,
      Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

/-- The canonical anticommutation relation of the annihilation operators:
`A_j A_k + A_k A_j = 0`. -/
theorem car_annih (j k : Fin 2) :
    annihTwo j * annihTwo k + annihTwo k * annihTwo j = 0 := by
  fin_cases j <;> fin_cases k <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    simp [annihTwo, annihMode0, annihMode1,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply]

/-- The canonical anticommutation relation mixing creation and annihilation:
`A_j A_k^† + A_k^† A_j = δ_{jk} 1`. -/
theorem car_mixed (j k : Fin 2) :
    annihTwo j * createTwo k + createTwo k * annihTwo j = if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    simp [annihTwo, createTwo, annihMode0, annihMode1, createMode0, createMode1,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply]

/-- The explicit matrix of `A₀^† A₀`: the number operator of mode `0`. -/
private theorem numberBilinear_zero_zero :
    numberBilinear 0 0 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [numberBilinear, createTwo, annihTwo, createMode0, createMode1, annihMode0,
      annihMode1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply]

/-- The explicit matrix of `A₀^† A₁`. -/
private theorem numberBilinear_zero_one :
    numberBilinear 0 1 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [numberBilinear, createTwo, annihTwo, createMode0, createMode1, annihMode0,
      annihMode1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply]

/-- The explicit matrix of `A₁^† A₀`. -/
private theorem numberBilinear_one_zero :
    numberBilinear 1 0 = !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [numberBilinear, createTwo, annihTwo, createMode0, createMode1, annihMode0,
      annihMode1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply]

/-- The explicit matrix of `A₁^† A₁`: the number operator of mode `1`. -/
private theorem numberBilinear_one_one :
    numberBilinear 1 1 = !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [numberBilinear, createTwo, annihTwo, createMode0, createMode1, annihMode0,
      annihMode1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply]

/-- Lemma D.3, first rule: `[A_j^† A_k, A_l^† A_m] = δ_{kl} A_j^† A_m − δ_{jm} A_l^† A_k`. -/
theorem lemmaD3_exchange : ∀ j k l m : Fin 2,
    numberBilinear j k * numberBilinear l m - numberBilinear l m * numberBilinear j k =
      (if k = l then numberBilinear j m else 0) -
        (if j = m then numberBilinear l k else 0) := by
  simp only [Fin.forall_fin_two]
  repeat' apply And.intro
  all_goals
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [numberBilinear_zero_zero, numberBilinear_zero_one, numberBilinear_one_zero,
        numberBilinear_one_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply, reduceIte]

/-- Lemma D.3, second rule (Eq. (199)):
`[A_j^† A_k, N_l] = δ_{kl} A_j^† A_l − δ_{jl} A_l^† A_k`. -/
theorem lemmaD3_number : ∀ j k l : Fin 2,
    numberBilinear j k * numberOp l - numberOp l * numberBilinear j k =
      (if k = l then numberBilinear j l else 0) -
        (if j = l then numberBilinear l k else 0) := by
  simp only [Fin.forall_fin_two]
  repeat' apply And.intro
  all_goals
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [numberOp, numberBilinear_zero_zero, numberBilinear_zero_one,
        numberBilinear_one_zero, numberBilinear_one_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.of_apply, reduceIte]

/-- Lemma D.3, third rule: the commutator with the product `N_l N_m` expands by the
derivation rule, `[A_j^† A_k, N_l N_m] = (δ_{kl} A_j^† A_l − δ_{jl} A_l^† A_k) N_m
+ N_l (δ_{km} A_j^† A_m − δ_{jm} A_m^† A_k)`. -/
theorem lemmaD3_number_product : ∀ j k l m : Fin 2,
    numberBilinear j k * (numberOp l * numberOp m) -
        numberOp l * numberOp m * numberBilinear j k =
      ((if k = l then numberBilinear j l else 0) -
          (if j = l then numberBilinear l k else 0)) * numberOp m +
        numberOp l * ((if k = m then numberBilinear j m else 0) -
          (if j = m then numberBilinear m k else 0)) := by
  simp only [Fin.forall_fin_two]
  repeat' apply And.intro
  all_goals
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [numberOp, numberBilinear_zero_zero, numberBilinear_zero_one,
        numberBilinear_one_zero, numberBilinear_one_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.of_apply, reduceIte]

end Qatlib.Papers.TrotterError19.MainResults.Appendices
