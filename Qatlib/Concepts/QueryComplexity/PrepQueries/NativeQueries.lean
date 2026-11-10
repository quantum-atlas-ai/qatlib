/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.PrepQueries.NativeOracle
import Qatlib.Concepts.QueryComplexity.PrepQueries.BornWeights

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

def queryRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U Q : ℕ → E →L[ℂ] E) : ℕ → E → E
  | 0, x => U 0 x
  | t+1, x => U (t+1) (Q t (queryRun U Q t x))

theorem queryRun_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U Q : ℕ → E →L[ℂ] E)
    (hU : ∀ i x, ‖U i x‖=‖x‖) (hQ : ∀ i x, ‖Q i x‖=‖x‖) :
    ∀ t x, ‖queryRun U Q t x‖=‖x‖
  | 0,x => by simpa [queryRun] using hU 0 x
  | t+1,x => by simp only [queryRun,hU,hQ,queryRun_norm U Q hU hQ t x]

theorem queryRun_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U Q R : ℕ → E →L[ℂ] E)
    (hU : ∀ i x, ‖U i x‖=‖x‖) (hQ : ∀ i x, ‖Q i x‖=‖x‖)
    (hR : ∀ i x, ‖R i x‖=‖x‖) (delta : ℝ) (hd : ∀ i, ‖Q i-R i‖≤delta) :
    ∀ t x, ‖queryRun U Q t x-queryRun U R t x‖ ≤ (t:ℝ)*delta*‖x‖ := by
  have hd0 : 0≤delta := le_trans (norm_nonneg (Q 0-R 0)) (hd 0)
  intro t
  induction t with
  | zero => intro x;simp [queryRun]
  | succ t ih =>
    intro x
    set a := queryRun U Q t x
    set b := queryRun U R t x
    have ha : ‖a‖=‖x‖ := queryRun_norm U Q hU hQ t x
    have he : queryRun U Q (t+1) x-queryRun U R (t+1) x =
        U (t+1) (Q t a-R t b) := by simp only [queryRun,map_sub,a,b]
    rw [he,hU]
    have hs : Q t a-R t b = (Q t-R t) a+R t (a-b) := by
      simp only [ContinuousLinearMap.sub_apply,map_sub];abel
    rw [hs]
    calc
      _ ≤ ‖(Q t-R t) a‖+‖R t (a-b)‖ := norm_add_le _ _
      _ ≤ ‖Q t-R t‖*‖a‖+‖a-b‖ := by
        rw [hR];exact add_le_add ((Q t-R t).le_opNorm a) (le_refl _)
      _ ≤ delta*‖x‖+(t:ℝ)*delta*‖x‖ := by
        rw [ha];exact add_le_add (mul_le_mul_of_nonneg_right (hd t) (norm_nonneg x)) (ih x)
      _ = ((t+1:ℕ):ℝ)*delta*‖x‖ := by push_cast;ring

def matrixWord {J : Type*} [Fintype J] [DecidableEq J]
    (U Q : ℕ→Matrix J J ℂ) : ℕ→Matrix J J ℂ
  | 0 => U 0
  | t+1 => U (t+1)*Q t*matrixWord U Q t

theorem matrixWord_apply {J : Type*} [Fintype J] [DecidableEq J]
    (U Q : ℕ→Matrix J J ℂ) (t : ℕ) (x : EuclideanSpace ℂ J) :
    Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) (matrixWord U Q t) x =
      queryRun (fun i=>Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) (U i))
        (fun i=>Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) (Q i)) t x := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [matrixWord,map_mul,ContinuousLinearMap.mul_apply,queryRun,ih]

def experiment {W : Type*} [Fintype W] [DecidableEq W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (eps : ℝ) (inverse : ℕ→Bool)
    (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) : EuclideanSpace ℂ (W×Bool) :=
  Matrix.toEuclideanCLM (n:=W×Bool) (𝕜:=ℂ)
    (matrixWord (fun i=>(U i).val) (fun i=>sourceOracle eps (inverse i)) t) x

def reference {W : Type*} [Fintype W] [DecidableEq W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) :
    EuclideanSpace ℂ (W×Bool) :=
  Matrix.toEuclideanCLM (n:=W×Bool) (𝕜:=ℂ)
    (matrixWord (fun i=>(U i).val) (fun _=>1) t) x

theorem experiment_norm {W : Type*} [Fintype W] [DecidableEq W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1)
    (inverse : ℕ→Bool) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) :
    ‖experiment U eps inverse t x‖=‖x‖ := by
  rw [experiment,matrixWord_apply]
  exact queryRun_norm _ _ (fun i y=>native_norm_map _ (U i).property y)
    (fun i y=>native_norm_map _ (sourceOracle_unitary eps he0 he1 (inverse i)) y) t x

theorem reference_norm {W : Type*} [Fintype W] [DecidableEq W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) :
    ‖reference U t x‖=‖x‖ := by
  rw [reference,matrixWord_apply]
  exact queryRun_norm _ _ (fun i y=>native_norm_map _ (U i).property y)
    (fun _ y=>native_norm_map _ (by simp) y) t x

theorem experiment_distance {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1)
    (inverse : ℕ→Bool) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) :
    ‖reference U t x-experiment U eps inverse t x‖ ≤ (t:ℝ)*(2*Real.sqrt eps)*‖x‖ := by
  rw [reference,experiment,matrixWord_apply,matrixWord_apply]
  apply queryRun_distance _ _ _
    (fun i y=>native_norm_map _ (U i).property y)
    (fun _ y=>native_norm_map _ (by simp) y)
    (fun i y=>native_norm_map _ (sourceOracle_unitary eps he0 he1 (inverse i)) y)
  intro i
  rw [← map_sub, Matrix.l2_opNorm_toEuclideanCLM]
  exact sourceOracle_distance eps he0 he1 (inverse i)

theorem actual_preparation_query_lower_bound {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (eps : ℝ) (he0 : 0<eps) (he1 : eps≤1)
    (inverse : ℕ→Bool) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) (hx : ‖x‖=1)
    (S : Finset (W×Bool)) (hyes : 2/3 ≤ born S (reference U t x))
    (hno : born S (experiment U eps inverse t x) ≤ 1/3) :
    1/(12*Real.sqrt eps) ≤ (t:ℝ) := by
  have hy := reference_norm U t x
  have hn := experiment_norm U eps he0.le he1 inverse t x
  rw [hx] at hy hn
  have hp := born_difference S (reference U t x) (experiment U eps inverse t x) hy hn
  have hd := experiment_distance U eps he0.le he1 inverse t x
  rw [hx,mul_one] at hd
  have hsep : 1/3 ≤ born S (reference U t x)-born S (experiment U eps inverse t x) := by linarith
  have hs := Real.sqrt_pos.mpr he0
  rw [div_le_iff₀ (by positivity : 0<12*Real.sqrt eps)]
  have habs := le_abs_self (born S (reference U t x)-born S (experiment U eps inverse t x))
  nlinarith
end Qatlib.Concepts.QueryComplexity.PrepQueries
