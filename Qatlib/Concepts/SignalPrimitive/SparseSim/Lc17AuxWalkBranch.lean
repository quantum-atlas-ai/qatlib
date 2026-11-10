/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.SignalPrimitive.SparseSim

open Matrix

def lcBranchVector {W : Type} (a : Fin 2 → ℂ) (w : W → ℂ) : Fin 2 × W → ℂ :=
  fun i => a i.1 * w i.2

theorem lcHad_diagonal_scalar (z : ℂ) :
    lcHad * Matrix.diagonal ![1, z] * lcHad =
      !![(1 + z) / 2, (1 - z) / 2; (1 - z) / 2, (1 + z) / 2] := by
  have hn : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← _root_.mul_inv_rev,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lcHad, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Complex.real_smul, Matrix.diagonal_apply]
  all_goals norm_num
  · linear_combination (1 + z) * hn
  · linear_combination (1 - z) * hn
  · linear_combination (1 - z) * hn
  · linear_combination (1 + z) * hn

theorem lcHad_controlled_scalar (θ : ℝ) :
    lcHad * Matrix.diagonal ![1, Complex.exp (Complex.I * (θ : ℂ))] * lcHad =
      Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) • lcSignalStep θ := by
  rw [lcHad_diagonal_scalar]
  have he : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ha : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      Complex.cos ((θ : ℂ) / 2) + Complex.I * Complex.sin ((θ : ℂ) / 2) := by
    rw [show Complex.I * ((θ / 2 : ℝ) : ℂ) = ((θ : ℂ) / 2) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    ring
  have hc := Complex.sin_sq_add_cos_sq ((θ : ℂ) / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lcSignalStep, lcAxisRotation, Matrix.smul_apply, he, ha]
  all_goals norm_num
  all_goals linear_combination (-((1 : ℂ) / 2)) * hc +
    (((Complex.sin ((θ : ℂ) / 2)) ^ 2) / 2) * Complex.I_mul_I

theorem lcUhat_scalar (φ θ : ℝ) :
    PhaseRotation (-(φ / 2)) *
      (lcHad * Matrix.diagonal ![1, Complex.exp (Complex.I * (θ : ℂ))] * lcHad) *
        PhaseRotation (φ / 2) =
      Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) • lcAxisRotation φ θ := by
  rw [lcHad_controlled_scalar, Matrix.mul_smul, Matrix.smul_mul, lcAxisRotation_factor]
  simp only [Matrix.mul_assoc]

theorem lcAxisRotation_add_pi_adjoint (φ θ : ℝ) :
    (lcAxisRotation (φ + Real.pi) θ)ᴴ = lcAxisRotation φ θ := by
  have hp : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have he : Complex.exp (Complex.I * ((φ + Real.pi : ℝ) : ℂ)) =
      -Complex.exp (Complex.I * (φ : ℂ)) := by
    rw [Complex.ofReal_add, mul_add, Complex.exp_add, hp, mul_neg_one]
  have hen : Complex.exp (Complex.I * (-((φ + Real.pi : ℝ) : ℂ))) =
      -Complex.exp (Complex.I * (-(φ : ℂ))) := by
    rw [mul_neg, Complex.exp_neg, he, inv_neg, ← Complex.exp_neg, ← mul_neg]
  have hs : star (Complex.exp (Complex.I * (φ : ℂ))) =
      Complex.exp (Complex.I * (-(φ : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  have hsneg : star (Complex.exp (-(Complex.I * (φ : ℂ)))) = Complex.exp (Complex.I * (φ : ℂ)) := by
    rw [show -(Complex.I * (φ : ℂ)) = Complex.I * (-(φ : ℂ)) by ring, ← hs, star_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lcAxisRotation, Matrix.conjTranspose_apply, Matrix.of_apply]
  all_goals norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    he, hen, star_mul, star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
    neg_neg]
  all_goals simp only [← Complex.star_def, hs, star_star]
  all_goals simp only [mul_neg, hsneg]
  all_goals ring

section Branch

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem lcAncilla_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) (w : W → ℂ) :
    (Matrix.of fun (i j : Fin 2 × W) => if i.2 = j.2 then M i.1 j.1 else 0) *ᵥ
      lcBranchVector a w = lcBranchVector (M *ᵥ a) w := by
  funext i
  rcases i with ⟨i, x⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.of_apply,
    lcBranchVector, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← mul_assoc, ← Finset.sum_mul]

theorem lcHadAncilla_branch (a : Fin 2 → ℂ) (w : W → ℂ) :
    lcHadAncilla W *ᵥ lcBranchVector a w = lcBranchVector (lcHad *ᵥ a) w :=
  lcAncilla_mulVec lcHad a w

theorem lcPhaseAncilla_branch (γ : ℝ) (a : Fin 2 → ℂ) (w : W → ℂ) :
    lcPhaseAncilla γ W *ᵥ lcBranchVector a w = lcBranchVector (PhaseRotation γ *ᵥ a) w :=
  lcAncilla_mulVec (PhaseRotation γ) a w

theorem lcControlledWalk_branch (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ)
    (hw : V *ᵥ w = z • w) (a : Fin 2 → ℂ) :
    lcControlledWalk V *ᵥ lcBranchVector a w =
      lcBranchVector ((Matrix.diagonal ![1, z]) *ᵥ a) w := by
  funext i
  rcases i with ⟨i, x⟩
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      lcControlledWalk, lcBranchVector]
  · have h := congrFun hw x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      lcControlledWalk, Matrix.of_apply, lcBranchVector]
    norm_num
    calc
      _ = a 1 * (∑ y, V x y * w y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [h]; ring

theorem lcUhat_branch (φ : ℝ) (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ)
    (hw : V *ᵥ w = z • w) (a : Fin 2 → ℂ) :
    lcUhat φ V *ᵥ lcBranchVector a w =
      lcBranchVector ((PhaseRotation (-(φ / 2)) *
        (lcHad * Matrix.diagonal ![1, z] * lcHad) * PhaseRotation (φ / 2)) *ᵥ a) w := by
  unfold lcUhat
  simp only [← Matrix.mulVec_mulVec, lcPhaseAncilla_branch,
    lcHadAncilla_branch, lcControlledWalk_branch V w z hw]

theorem lcPlusFrame_branch (L : Matrix W I ℂ) (ψ : I → ℂ) :
    lcPlusFrame L *ᵥ ψ =
      lcBranchVector (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) (L *ᵥ ψ) := by
  funext i
  simp only [lcPlusFrame, lcBranchVector, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Complex.real_smul, ← mul_assoc, ← Finset.mul_sum]
  rw [Complex.ofReal_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem lcAncilla_adjoint_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ)
    (a : Fin 2 → ℂ) (w : W → ℂ) :
    (Matrix.of fun (i j : Fin 2 × W) => if i.2 = j.2 then M i.1 j.1 else 0)ᴴ *ᵥ
      lcBranchVector a w = lcBranchVector (Mᴴ *ᵥ a) w := by
  have he : (Matrix.of fun (i j : Fin 2 × W) => if i.2 = j.2 then M i.1 j.1 else 0)ᴴ =
      Matrix.of fun (i j : Fin 2 × W) => if i.2 = j.2 then Mᴴ i.1 j.1 else 0 := by
    ext i j
    by_cases h : i.2 = j.2 <;> simp [Matrix.conjTranspose_apply, h, eq_comm]
  rw [he, lcAncilla_mulVec]

theorem lcControlledWalk_adjoint (V : Matrix W W ℂ) :
    (lcControlledWalk V)ᴴ = lcControlledWalk Vᴴ := by
  ext i j
  rcases i with ⟨a, x⟩
  rcases j with ⟨b, y⟩
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0
    · subst a
      simp [lcControlledWalk, Matrix.conjTranspose_apply, eq_comm]
    · simp [lcControlledWalk, Matrix.conjTranspose_apply, ha]
  · simp [lcControlledWalk, Matrix.conjTranspose_apply, hab, Ne.symm hab]

theorem lcWalk_adjoint_eigen (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ)
    (hV : V ∈ Matrix.unitaryGroup W ℂ) (hw : V *ᵥ w = z • w)
    (hz : star z * z = 1) : Vᴴ *ᵥ w = star z • w := by
  have hv : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hV
  calc
    Vᴴ *ᵥ w = star z • (Vᴴ *ᵥ (z • w)) := by
      rw [Matrix.mulVec_smul, smul_smul, hz, one_smul]
    _ = star z • (Vᴴ *ᵥ (V *ᵥ w)) := by rw [hw]
    _ = star z • w := by rw [Matrix.mulVec_mulVec, hv, Matrix.one_mulVec]

theorem lcUhat_adjoint_branch (φ : ℝ) (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ)
    (hV : V ∈ Matrix.unitaryGroup W ℂ) (hw : V *ᵥ w = z • w)
    (hz : star z * z = 1) (a : Fin 2 → ℂ) :
    (lcUhat φ V)ᴴ *ᵥ lcBranchVector a w =
      lcBranchVector ((PhaseRotation (-(φ / 2)) *
        (lcHad * Matrix.diagonal ![1, z] * lcHad) * PhaseRotation (φ / 2))ᴴ *ᵥ a) w := by
  have hh : ∀ a : Fin 2 → ℂ, (lcHadAncilla W)ᴴ *ᵥ lcBranchVector a w =
      lcBranchVector (lcHadᴴ *ᵥ a) w := fun a => lcAncilla_adjoint_mulVec lcHad a w
  have hp : ∀ (γ : ℝ) (a : Fin 2 → ℂ), (lcPhaseAncilla γ W)ᴴ *ᵥ lcBranchVector a w =
      lcBranchVector ((PhaseRotation γ)ᴴ *ᵥ a) w :=
    fun γ a => lcAncilla_adjoint_mulVec (PhaseRotation γ) a w
  have hdiag : (Matrix.diagonal ![1, z])ᴴ = Matrix.diagonal ![1, star z] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  unfold lcUhat
  simp only [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hp, hh,
    lcControlledWalk_adjoint,
    lcControlledWalk_branch Vᴴ w (star z) (lcWalk_adjoint_eigen V w z hV hw hz), hdiag]

theorem lcExp_star_mul (θ : ℝ) :
    star (Complex.exp (Complex.I * (θ : ℂ))) * Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]

theorem lcUhat_source_branch (φ θ : ℝ) (V : Matrix W W ℂ) (w : W → ℂ)
    (hw : V *ᵥ w = Complex.exp (Complex.I * (θ : ℂ)) • w) (a : Fin 2 → ℂ) :
    lcUhat φ V *ᵥ lcBranchVector a w =
      lcBranchVector ((Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) •
        lcAxisRotation φ θ) *ᵥ a) w := by
  rw [lcUhat_branch φ V w _ hw a, lcUhat_scalar]

theorem lcUhat_source_adjoint_branch (φ θ : ℝ) (V : Matrix W W ℂ) (w : W → ℂ)
    (hV : V ∈ Matrix.unitaryGroup W ℂ)
    (hw : V *ᵥ w = Complex.exp (Complex.I * (θ : ℂ)) • w) (a : Fin 2 → ℂ) :
    (lcUhat (φ + Real.pi) V)ᴴ *ᵥ lcBranchVector a w =
      lcBranchVector ((star (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) •
        lcAxisRotation φ θ) *ᵥ a) w := by
  rw [lcUhat_adjoint_branch (φ + Real.pi) V w _ hV hw (lcExp_star_mul θ) a,
    lcUhat_scalar, Matrix.conjTranspose_smul, lcAxisRotation_add_pi_adjoint]

theorem lcSimFactors_pair (V : Matrix W W ℂ) (φ ψ : ℝ) (ls : List ℝ) :
    ((φ :: ψ :: ls).mapIdx (fun j φ =>
      if j % 2 = 0 then lcUhat φ V else (lcUhat (φ + Real.pi) V)ᴴ)).prod =
      lcUhat φ V * ((lcUhat (ψ + Real.pi) V)ᴴ *
        (ls.mapIdx (fun j φ =>
          if j % 2 = 0 then lcUhat φ V else (lcUhat (φ + Real.pi) V)ᴴ)).prod) := by
  simp only [List.mapIdx_cons, List.prod_cons]
  norm_num only [Nat.zero_mod, Nat.reduceMod, if_true, if_false]
  congr 2
  apply congrArg List.prod
  congr 1
  funext i x
  have he : (i + 1 + 1) % 2 = i % 2 := by omega
  rw [he]

theorem lcSimWord_branch (V : Matrix W W ℂ) (w : W → ℂ) (θ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup W ℂ)
    (hw : V *ᵥ w = Complex.exp (Complex.I * (θ : ℂ)) • w)
    (phis : List ℝ) (hlen : Even phis.length) (a : Fin 2 → ℂ) :
    lcSimWord V phis *ᵥ lcBranchVector a w = lcBranchVector (lcWord phis θ *ᵥ a) w := by
  have hword : ∀ (ls : List ℝ), Even ls.length → ∀ a : Fin 2 → ℂ,
      (ls.mapIdx (fun j φ => if j % 2 = 0 then lcUhat φ V else (lcUhat (φ + Real.pi) V)ᴴ)).prod *ᵥ
        lcBranchVector a w = lcBranchVector ((ls.map (fun φ => lcAxisRotation φ θ)).prod *ᵥ a) w := by
    intro ls
    induction ls using List.twoStepInduction with
    | nil => intro _ a; simp
    | singleton φ => intro he a; simp at he
    | cons_cons φ ψ ls ih _ =>
      intro he a
      have hls : Even ls.length := by
        rcases he with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        simp only [List.length_cons] at hk
        omega
      rw [lcSimFactors_pair, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih hls, lcUhat_source_adjoint_branch ψ θ V w hV hw,
        lcUhat_source_branch φ θ V w hw,
        Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
      have hc : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
          star (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) = 1 := by
        rw [mul_comm, lcExp_star_mul]
      rw [hc, one_smul]
      simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
  unfold lcSimWord lcWord
  rw [← List.prod_eq_foldl, ← List.prod_eq_foldl]
  apply hword phis.reverse
  simpa only [List.length_reverse] using! hlen

end Branch

end Qatlib.Concepts.SignalPrimitive.SparseSim
