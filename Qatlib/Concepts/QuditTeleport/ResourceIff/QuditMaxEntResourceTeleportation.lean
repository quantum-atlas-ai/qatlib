/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceDecode
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators

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
