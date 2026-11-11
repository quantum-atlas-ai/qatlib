/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceDecode

/-!
# Teleportation with maximally entangled qudit resources

This module proves `quditMaxEntResourceTeleportation` using the decoded branch Gram identity.
For a resource built from two orthonormal families, scaling each branch adjoint by the dimension
gives a unitary correction and a corrected branch equal to `1 / n²` times the input.

The result formalizes the resource dependent correction mechanism of
[BennettEtAl1993Teleportation].

## Main statements

* `quditMaxEntResourceTeleportation`: unitary branch corrections and exact scaled recovery.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators

/-- For a maximally entangled resource in orthonormal family form, each decoded branch Kraus
operator `K` has unitary correction `n • Kᴴ`, and the corrected branch sends every operator
to `1 / n²` times itself [BennettEtAl1993Teleportation]. -/
theorem quditMaxEntResourceTeleportation : QuditMaxEntResourceTeleportation := by
  intro n _ u v hu hv o
  let K := quditResourceBranchKraus n (quditMaxEntResource n u v) o
  have hg : Kᴴ * K = (1 / (n : ℂ)^2) • (1 : Operator n) :=
    quditResourceBranchKraus_gram n _ (qudit_maxEnt_first_marginal hu hv) o
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnstar : star (n : ℂ) = (n : ℂ) := by simp
  have hcancel : (n : ℂ) • Kᴴ * K = (1 / (n : ℂ)) • (1 : Operator n) := by
    rw [Matrix.smul_mul, hg, smul_smul]
    congr 1
    field_simp
  constructor
  · change (n : ℂ) • Kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hnstar,
      smul_mul_smul, hg, smul_smul]
    have he : (n : ℂ) * (n : ℂ) * (1 / (n : ℂ)^2) = 1 := by field_simp
    rw [he, one_smul]
  · intro ρ
    change ((n : ℂ) • Kᴴ * K) * ρ * ((n : ℂ) • Kᴴ * K)ᴴ = _
    rw [hcancel, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    have hs : star (1 / (n : ℂ)) = 1 / (n : ℂ) := by simp
    rw [hs]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul]
    congr 1
    simp [pow_two]

end Qatlib.Concepts.QuditTeleport.ResourceIff
