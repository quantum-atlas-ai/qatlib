/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Commutators

/-!
# Compressed nested commutators of positive local Hamiltonians

This module defines grouped nested commutators, their off-diagonal excursions, and a recursive
fixed-cutoff remainder. Under positivity of the local terms, it proves a leading compressed norm
bound of `2 ^ n * Λ ^ (n + 1)` plus that remainder, as used in [HejaziZiniArrazola2024].

## Main statements

* `excursion`: Measures the two products of off-diagonal block norms.
* `actual_psd_nested_source`: Bounds a compressed nested commutator by its leading cutoff power
  and recursive remainder.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The grouped nested commutator with seed `h.grouped seed`, recursively taking the commutator
with each list head. -/
def nested (h : Hamiltonian N R M k d J) (seed : Fin M) : List (Fin M)→Matrix (Register N) (Register N) ℂ
  | []=>h.grouped seed
  | a::xs=>h.grouped a*nested h seed xs-nested h seed xs*h.grouped a

/-- The sum of the two products of opposite off-diagonal block norms arising when a commutator
is compressed at `Λ`. -/
def excursion (h : Hamiltonian N R M k d J) (Λ : ℝ) (A B : Matrix (Register N) (Register N) ℂ) : ℝ :=
    ‖low h.total h.total_hermitian Λ*A*high h.total h.total_hermitian Λ‖*
      ‖high h.total h.total_hermitian Λ*B*low h.total h.total_hermitian Λ‖+
    ‖low h.total h.total_hermitian Λ*B*high h.total h.total_hermitian Λ‖*
      ‖high h.total h.total_hermitian Λ*A*low h.total h.total_hermitian Λ‖

/-- The fixed-cutoff nested-commutator remainder, initialized at zero and recursively multiplied
by `2 * Λ` before adding the next excursion. -/
def remainder (h : Hamiltonian N R M k d J) (Λ : ℝ) (seed : Fin M) : List (Fin M)→ℝ
  | []=>0
  | a::xs=>2*Λ*remainder h Λ seed xs+excursion h Λ (h.grouped a) (nested h seed xs)

/-- The fixed-cutoff remainder is nonnegative for every nesting list when `Λ` is nonnegative. -/
theorem remainder_nonneg (h : Hamiltonian N R M k d J) (Λ : ℝ) (hΛ : 0 ≤ Λ) (seed : Fin M) (xs : List (Fin M)) :
    0 ≤ remainder h Λ seed xs := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>dsimp only [remainder,excursion]; positivity

/-- For positive semidefinite local terms and nonnegative `Λ`, the compressed nested commutator
is bounded by `(2 * Λ) ^ xs.length * Λ` plus its recursive remainder. -/
theorem actual_psd_nested (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (seed : Fin M) (xs : List (Fin M)) :
    ‖low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ‖ ≤
      (2*Λ)^xs.length*Λ+remainder h Λ seed xs := by
  have hH : h.total.PosSemidef := Matrix.posSemidef_sum _ (fun m _=>h.grouped_psd hp m)
  induction xs with
  | nil=>simpa only [nested,remainder,List.length_nil,pow_zero,one_mul,add_zero] using h.actual_psd_group_cutoff hp seed Λ hΛ
  | cons a xs ih=>
    have hb:=psd_compressed_commutator_norm h.total (h.grouped a) (nested h seed xs) hH
      (h.grouped_psd hp a) (psd_group_domination h.grouped (h.grouped_psd hp) a) Λ hΛ
    rw [add_assoc] at hb
    change ‖low h.total h.total_hermitian Λ*nested h seed (a::xs)*low h.total h.total_hermitian Λ‖ ≤
      2*Λ*‖low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ‖+
      excursion h Λ (h.grouped a) (nested h seed xs) at hb
    calc
      _ ≤ _ := hb
      _ ≤ 2*Λ*((2*Λ)^xs.length*Λ+remainder h Λ seed xs)+excursion h Λ (h.grouped a) (nested h seed xs) := by gcongr
      _ = _ := by simp only [List.length_cons,remainder,pow_succ]; ring

/-- For positive semidefinite local terms, the compressed nested-commutator bound has leading
term `2 ^ xs.length * Λ ^ (xs.length + 1)` and additive recursive remainder. -/
theorem actual_psd_nested_source (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (seed : Fin M) (xs : List (Fin M)) :
    ‖low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ‖ ≤
      2^xs.length*Λ^(xs.length+1)+remainder h Λ seed xs := by
  simpa only [mul_pow,pow_succ,mul_assoc] using actual_psd_nested h hp Λ hΛ seed xs

end Qatlib.Papers.LowEnergyProd24.RetainedError
