/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditConverseTools
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPositiveBranches

/-!
# The qudit teleportation resource marginal converse

`quditResourceMarginalConverse` proves that a positive semidefinite resource supporting fixed
correction teleportation must have maximally mixed Bob marginal. The argument combines
positivity of the corrected branches with no signalling for Alice's complete local operation.

This gives a necessary resource condition for the teleportation setting of
[BennettEtAl1993Teleportation], which can then be specialized to normalized pure resources.

## Main statements

* `quditResourceMarginalConverse`: fixed correction teleportation forces the maximally mixed Bob
  marginal.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- A positive semidefinite resource supporting qudit teleportation with fixed unitary
corrections has Bob marginal equal to `1 / n` times the identity
[BennettEtAl1993Teleportation]. -/
theorem quditResourceMarginalConverse : QuditResourceMarginalConverse := by
  intro n _ K U ω hω htele
  obtain ⟨hU, hK, hsum⟩ := htele
  let F :=
      fun s : Fin n × Fin n => fun ρ : Operator n => U s * quditBobBranchMarginal n K ω s ρ * (U s)ᴴ
  have hadd : ∀ s A B, F s (A + B) = F s A + F s B := by
    intro s A B
    simp only [F, quditBobBranchMarginal_add, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ s (c : ℂ) A, F s (c • A) = c • F s A := by
    intro s c A
    simp only [F, quditBobBranchMarginal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hpos : ∀ s (A : Operator n), A.PosSemidef → (F s A).PosSemidef := by
    intro s A hA
    have h := (quditBobBranchMarginal_positive K ω hω s A hA).conjTranspose_mul_mul_same (U s)ᴴ
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  let e := (finProdFinEquiv (m := n) (n := n))
  have hscalar : ∀ s, ∃ a : ℂ, F s 1 = a • (1 : Operator n) := by
    have hs : ∀ A, ∑ t, F (e.symm t) A = A := by
      intro A
      rw [← e.sum_comp]
      simpa only [Equiv.symm_apply_apply] using hsum A
    have h := qudit_positive_family_scalar_one (n*n) n (fun t => F (e.symm t))
      (fun t => hadd (e.symm t)) (fun t => hsmul (e.symm t))
      (fun t => hpos (e.symm t)) hs
    intro s
    simpa only [Equiv.symm_apply_apply] using h (e s)
  have hraw (s : Fin n × Fin n) : quditBobBranchMarginal n K ω s 1 = F s 1 := by
    obtain ⟨a, ha⟩ := hscalar s
    have hu : (U s)ᴴ * U s = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hU s)
    have hundo : (U s)ᴴ * F s 1 * U s = quditBobBranchMarginal n K ω s 1 := by
      have he : ((U s)ᴴ * U s) * quditBobBranchMarginal n K ω s 1 * ((U s)ᴴ * U s) =
          quditBobBranchMarginal n K ω s 1 := by rw [hu, Matrix.one_mul, Matrix.mul_one]
      simpa only [F, Matrix.mul_assoc] using he
    rw [ha] at hundo
    have hc : (U s)ᴴ * (a • (1 : Operator n)) * U s = a • (1 : Operator n) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hu]
    rw [hc] at hundo
    exact hundo.symm.trans ha.symm
  have hb : (∑ s, quditBobBranchMarginal n K ω s 1) = (1 : Operator n) := by
    simp_rw [hraw]
    exact hsum 1
  have hn := quditBobBranchMarginal_no_signalling K ω hK (1 : Operator n)
  rw [hb, show Matrix.trace (1 : Operator n) = (n : ℂ) by simp] at hn
  ext i j
  have he := congrArg (fun A : Operator n => A i j) hn
  simp only [Matrix.smul_apply, smul_eq_mul] at he ⊢
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  apply (mul_left_cancel₀ hn0)
  rw [← mul_assoc, mul_one_div_cancel hn0, one_mul]
  exact he.symm

end Qatlib.Concepts.QuditTeleport.ResourceIff
