/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import QuantumInfo.ForMathlib.HermitianMat.LogExp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Qatlib.Concepts.LchsSimulation.LchsRep.ImaginaryTimeProduct
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.LchsRep

namespace Qatlib.Concepts.MatrixWeights.WeightsCore
open Matrix
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

noncomputable def mmwWeight (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ) : Operator D :=
  NormedSpace.exp (-η • (∑ s∈Finset.range t, M s))

noncomputable def mmwState (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ) : Operator D :=
  ((Matrix.trace (mmwWeight D M η t)).re : ℂ)⁻¹ • mmwWeight D M η t

noncomputable def mmwAverage (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) : Operator D :=
  (T : ℂ)⁻¹ • ∑ t∈Finset.range T, mmwState D M η t

set_option backward.isDefEq.respectTransparency false in

theorem mmw_exp_positive_trace (D : ℕ) (A : Operator D) (hD : 0 < D)
    (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosSemidef ∧ 0 < (Matrix.trace (NormedSpace.exp A)).re ∧
      Matrix.trace (NormedSpace.exp A) = ((Matrix.trace (NormedSpace.exp A)).re : ℂ) := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  let H : HermitianMat (Fin D) ℂ := ⟨A,hA⟩
  have he : H.exp.mat = NormedSpace.exp A := by
    rw [HermitianMat.exp, HermitianMat.mat_cfc]
    letI : ContinuousFunctionalCalculus ℝ (Operator D) IsSelfAdjoint :=
      Matrix.IsHermitian.instContinuousFunctionalCalculus
    exact CFC.real_exp_eq_normedSpace_exp hA
  have hp : H.exp.mat.PosSemidef := HermitianMat.zero_le_iff.mp H.exp_nonneg
  have ht : 0 < H.exp.trace := HermitianMat.trace_pos H.exp_pos
  refine ⟨by rwa [he] at hp, ?_, ?_⟩
  · simpa only [HermitianMat.trace_eq_re_trace, he] using! ht
  · rw [← he]
    have hreal : H.exp.trace = (Matrix.trace H.exp.mat).re :=
      HermitianMat.trace_eq_re_trace H.exp
    rw [← hreal]
    exact (HermitianMat.trace_eq_trace H.exp).symm

theorem matrix_mw_actual_gibbs_iterates_density
    (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ) (hD : 0 < D)
    (hM : ∀ s, (M s).IsHermitian) :
    0 < (Matrix.trace (mmwWeight D M η t)).re ∧ IsDensityOperator (mmwState D M η t) := by
  have hs : (∑ s∈Finset.range t, M s).IsHermitian := by
    exact isSelfAdjoint_sum _ fun s _ => hM s
  have hA : (-η • (∑ s∈Finset.range t, M s)).IsHermitian :=
    hs.smul (by simp [IsSelfAdjoint])
  have hp := mmw_exp_positive_trace D _ hD hA
  change (mmwWeight D M η t).PosSemidef ∧
    0 < (Matrix.trace (mmwWeight D M η t)).re ∧
    Matrix.trace (mmwWeight D M η t) = ((Matrix.trace (mmwWeight D M η t)).re : ℂ) at hp
  refine ⟨hp.2.1, ?_, ?_⟩
  · unfold mmwState
    exact hp.1.smul (by exact_mod_cast (inv_nonneg.mpr hp.2.1.le))
  · unfold mmwState
    rw [Matrix.trace_smul, hp.2.2, Complex.ofReal_re, smul_eq_mul]
    apply inv_mul_cancel₀
    exact_mod_cast ne_of_gt hp.2.1

theorem mmw_commuting_trace_potential (D : ℕ) (A B : Operator D) (h : Commute A B) :
    (Matrix.trace (NormedSpace.exp (A+B))).re =
      (Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)).re := by
  rw [Matrix.exp_add_of_commute A B h]

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem mmw_schatten_power_le (Z : Matrix d d ℂ) (p : ℝ) (hp : 0 < p)
    (n : ℕ) (hn : 0 < n) :
    schattenNorm (Z ^ n) (p / n) ≤ schattenNorm Z p ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn0
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn'
      have hns : (0 : ℝ) < n + 1 := by positivity
      rw [pow_succ]
      have hrel : 1 / (p / (n + 1)) = 1 / (p / n) + 1 / p := by
        field_simp
      have hh := schattenNorm_mul_le (Z ^ n) Z (div_pos hp hns) (div_pos hp hnr) hp hrel
      rw [Nat.cast_add, Nat.cast_one]
      exact hh.trans ((mul_le_mul_of_nonneg_right (ih hn')
        (schattenNorm_nonneg Z p)).trans_eq (pow_succ _ _).symm)

theorem mmw_trace_le_schatten_one (Z : Matrix d d ℂ) :
    ‖Matrix.trace Z‖ ≤ schattenNorm Z 1 := by
  have he : schattenNorm Z 1 = Z.traceNorm := by
    rw [schattenNorm_eq_sum_singularValues_rpow Z (by norm_num),
      Matrix.traceNorm_eq_sum_singularValues]
    simp
  rw [he]
  exact Matrix.abs_trace_le_traceNorm Z

theorem mmw_trace_power_le_schatten (Z : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) :
    ‖Matrix.trace (Z ^ n)‖ ≤ schattenNorm Z n ^ n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  exact (mmw_trace_le_schatten_one _).trans (by
    simpa [ne_of_gt hp] using! mmw_schatten_power_le Z n hp n hn)

theorem mmw_schatten_even_moment (Z : Matrix d d ℂ) (m : ℕ) (hm : 0 < m) :
    schattenNorm Z (2 * m) ^ (2 * m) = (Matrix.trace ((Zᴴ * Z) ^ m)).re := by
  have he : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  rw [he, ← Real.rpow_natCast, schattenNorm_rpow_eq_sum_singularValues _ (by positivity)]
  let H : HermitianMat d ℂ := ⟨Zᴴ * Z, by simpa using! Matrix.isHermitian_mul_conjTranspose_self Zᴴ⟩
  have htrace : (Matrix.trace ((Zᴴ * Z) ^ m)).re =
      ∑ i, (H.H.eigenvalues i) ^ m := by
    have hc := H.trace_cfc_eq (fun x : ℝ => x ^ m)
    rw [HermitianMat.cfc_pow, HermitianMat.trace_eq_re_trace, HermitianMat.mat_pow] at hc
    exact hc
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _
  unfold singularValues
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul]
  swap
  · exact (Matrix.posSemidef_self_mul_conjTranspose Zᴴ).eigenvalues_nonneg i
  have ha : (1 / 2 : ℝ) * ↑(2 * m) = m := by push_cast; ring
  rw [ha, Real.rpow_natCast]
  congr 1
  simp only [H, Matrix.conjTranspose_conjTranspose]

theorem mmw_trace_even_power_le (Z : Matrix d d ℂ) (m : ℕ) (hm : 0 < m) :
    ‖Matrix.trace (Z ^ (2 * m))‖ ≤ (Matrix.trace ((Zᴴ * Z) ^ m)).re := by
  have h := mmw_trace_power_le_schatten Z (2 * m) (by omega)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mmw_schatten_even_moment Z m hm] using! h

theorem mmw_trace_mul_power_swap (A B : Matrix d d ℂ) (n : ℕ) :
    Matrix.trace ((A * B) ^ n) = Matrix.trace ((B * A) ^ n) := by
  have h (k : ℕ) : (A * B) ^ k * A = A * (B * A) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = ((A * B) ^ k * A) * (B * A) := by rw [pow_succ]; noncomm_ring
        _ = (A * (B * A) ^ k) * (B * A) := by rw [ih]
        _ = _ := by rw [pow_succ]; noncomm_ring
  cases n with
  | zero => rfl
  | succ k =>
    rw [pow_succ, ← mul_assoc, h, Matrix.trace_mul_comm, ← mul_assoc, ← pow_succ']

theorem mmw_dyadic_trace_power_le (X Y : Matrix d d ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (k : ℕ) :
    (Matrix.trace ((X * Y) ^ (2 ^ k))).re ≤
      (Matrix.trace (X ^ (2 ^ k) * Y ^ (2 ^ k))).re := by
  induction k generalizing X Y with
  | zero => simp
  | succ k ih =>
    have hp : 0 < 2 ^ k := by positivity
    have hth := mmw_trace_even_power_le (X * Y) (2 ^ k) hp
    have hgram : (X * Y)ᴴ * (X * Y) = Y * X ^ 2 * Y := by
      rw [Matrix.conjTranspose_mul, hX.eq, hY.eq, pow_two]
      noncomm_ring
    have ht : Matrix.trace ((Y * X ^ 2 * Y) ^ (2 ^ k)) =
        Matrix.trace ((X ^ 2 * Y ^ 2) ^ (2 ^ k)) := by
      rw [mul_assoc Y (X ^ 2) Y, mmw_trace_mul_power_swap Y (X ^ 2 * Y)]
      congr 2
      noncomm_ring
    rw [hgram, ht] at hth
    have hi := ih (X ^ 2) (Y ^ 2) (hX.pow 2) (hY.pow 2)
    have hx : (X ^ 2) ^ (2 ^ k) = X ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]; congr 1; omega
    have hy : (Y ^ 2) ^ (2 ^ k) = Y ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]; congr 1; omega
    rw [hx, hy] at hi
    have hn : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    rw [hn]
    exact (Complex.re_le_norm _).trans (hth.trans (by simpa [hn] using! hi))

open Filter
open scoped MatrixOrder Topology

theorem mmw_psd_dyadic_lie_limit (D : ℕ) (A B : Operator D)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun k : ℕ => imaginaryRun A B 1 (2 ^ k)) atTop
      (𝓝 (NormedSpace.exp (-(A+B)))) := by
  have hb (k : ℕ) :
      ‖imaginaryRun A B 1 (2 ^ k) - NormedSpace.exp (-(A+B))‖ ≤
      ‖A * B - B * A‖ / (2 * (2 ^ k : ℕ)) := by
    simpa [add_comm] using! (imaginary_product_contraction_and_commutator_error (Fin D) A B 1
      (2 ^ k) hA hB (by norm_num) (by positivity)).2.2
  have hn : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  have hz : Tendsto (fun k : ℕ => ‖A * B - B * A‖ / (2 * ((2 ^ k : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (hn.const_mul_atTop (by norm_num))
  have ht := (squeeze_zero_norm hb hz).add_const (NormedSpace.exp (-(A+B)))
  simpa using! ht

theorem mmw_golden_thompson_negative_psd (D : ℕ) (A B : Operator D)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (NormedSpace.exp (-(A+B)))).re ≤
      (Matrix.trace (NormedSpace.exp (-A) * NormedSpace.exp (-B))).re := by
  have hc : Continuous (fun Z : Operator D => (Matrix.trace Z).re) := by fun_prop
  have ht := hc.tendsto _ |>.comp (mmw_psd_dyadic_lie_limit D A B hA hB)
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro k
  let s : ℝ := 1 / ((2 ^ k : ℕ) : ℝ)
  have hh := mmw_dyadic_trace_power_le (NormedSpace.exp (-s • A))
    (NormedSpace.exp (-s • B))
    ((hA.isHermitian.smul (by simp [IsSelfAdjoint])).exp)
    ((hB.isHermitian.smul (by simp [IsSelfAdjoint])).exp) k
  have he (Z : Operator D) : NormedSpace.exp (-s • Z) ^ (2 ^ k) = NormedSpace.exp (-Z) := by
    rw [imaginary_exp_power]
    congr 1
    dsimp [s]
    rw [mul_one_div_cancel (by positivity : ((2 ^ k : ℕ) : ℝ) ≠ 0)]
    simp
  rw [he A, he B] at hh
  simpa [imaginaryRun_power, s] using! hh

open Filter
open scoped MatrixOrder Topology

theorem mmw_exp_scalar_shift (D : ℕ) (A : Operator D) (c : ℝ) :
    NormedSpace.exp (A + c • (1 : Operator D)) = (Real.exp c) • NormedSpace.exp A := by
  have hc : Commute A (c • (1 : Operator D)) := (Commute.one_right A).smul_right c
  rw [Matrix.exp_add_of_commute A _ hc]
  have he : NormedSpace.exp (c • (1 : Operator D)) = (Real.exp c) • (1 : Operator D) := by
    have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Operator D) c
    simpa [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using! h.symm
  rw [he, Matrix.mul_smul, Matrix.mul_one]

theorem mmw_shift_posSemidef (D : ℕ) (A : Operator D) (hA : A.IsHermitian) (hD : 0 < D) :
    (‖A‖ • (1 : Operator D) - A).PosSemidef := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  have h : A ≤ ‖A‖ • (1 : Operator D) :=
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA ‖A‖).mp fun i =>
      (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using!
          spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i))
  exact Matrix.le_iff.mp h

theorem matrix_mw_golden_thompson_trace_potential
    (D : ℕ) (A B : Operator D) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (A+B))).re ≤
      (Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)).re := by
  by_cases hD : D = 0
  · subst D
    simp [Matrix.trace]
  · have hDp : 0 < D := Nat.pos_of_ne_zero hD
    let P : Operator D := ‖A‖ • 1 - A
    let Q : Operator D := ‖B‖ • 1 - B
    have hP : P.PosSemidef := mmw_shift_posSemidef D A hA hDp
    have hQ : Q.PosSemidef := mmw_shift_posSemidef D B hB hDp
    have h := mmw_golden_thompson_negative_psd D P Q hP hQ
    have hp : -P = A + (-‖A‖) • (1 : Operator D) := by dsimp [P]; module
    have hq : -Q = B + (-‖B‖) • (1 : Operator D) := by dsimp [Q]; module
    have hpq : -(P+Q) = (A+B) + (-(‖A‖+‖B‖)) • (1 : Operator D) := by
      dsimp [P,Q]; module
    rw [hpq, hp, hq, mmw_exp_scalar_shift, mmw_exp_scalar_shift, mmw_exp_scalar_shift,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, Matrix.trace_smul] at h
    have he : Real.exp (-‖A‖) * Real.exp (-‖B‖) = Real.exp (-(‖A‖+‖B‖)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at h
    simp only [Complex.smul_re, smul_eq_mul] at h
    exact (mul_le_mul_iff_right₀ (Real.exp_pos (-(‖A‖+‖B‖)))).mp (by simpa only [mul_comm] using! h)

open Matrix Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Topology

theorem mmw_scalar_loss_exp_le (η x : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hx : |x| ≤ 1) :
    Real.exp (-η*x) ≤ 1-η*x+η^2 := by
  have ha : |-η*x| ≤ η := by
    rw [abs_mul, abs_neg, abs_of_pos hη]
    simpa using! mul_le_mul_of_nonneg_left hx hη.le
  have hb := Real.abs_exp_sub_one_sub_id_le (ha.trans hη1)
  have hs : (-η*x)^2 ≤ η^2 := by
    simpa only [sq_abs] using! pow_le_pow_left₀ (abs_nonneg (-η*x)) ha 2
  have hh := (le_abs_self (Real.exp (-η*x)-1-(-η*x))).trans hb
  nlinarith

theorem mmw_loss_exp_order (D : ℕ) (M : Operator D) (η : ℝ)
    (hD : 0<D) (hM : M.IsHermitian) (hn : ‖M‖ ≤ 1) (hη : 0<η) (hη1 : η≤1) :
    (NormedSpace.exp (-η • M)) ≤ (1+η^2) • (1 : Operator D) - η • M := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  let H : HermitianMat (Fin D) ℂ := ⟨M,hM⟩
  have hc : H.cfc (fun x => Real.exp (-η*x)) ≤ H.cfc (fun x => (1+η^2)-η*x) := by
    rw [← sub_nonneg, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
    intro i
    have heig : |H.H.eigenvalues i| ≤ ‖M‖ := by
      simpa only [Real.norm_eq_abs] using!
        spectrum.norm_le_norm_of_mem (hM.eigenvalues_mem_spectrum_real i)
    have hl : |H.H.eigenvalues i| ≤ 1 := heig.trans hn
    have hb := mmw_scalar_loss_exp_le η (H.H.eigenvalues i) hη hη1 hl
    linarith
  have he : H.cfc (fun x => Real.exp (-η*x)) = ((-η) • H).exp := by
    rw [HermitianMat.exp, ← HermitianMat.cfc_const_mul_id (r := -η),
      ← HermitianMat.cfc_comp_apply]
  have hr : H.cfc (fun x => (1+η^2)-η*x) = (1+η^2) • (1 : HermitianMat (Fin D) ℂ) - η • H := by
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_const, HermitianMat.cfc_const_mul_id]
  rw [he, hr] at hc
  have hmat : ((-η) • H).exp.mat = NormedSpace.exp (-η • M) := by
    rw [HermitianMat.exp, HermitianMat.mat_cfc]
    letI : ContinuousFunctionalCalculus ℝ (Operator D) IsSelfAdjoint :=
      Matrix.IsHermitian.instContinuousFunctionalCalculus
    exact CFC.real_exp_eq_normedSpace_exp (hM.smul (by simp [IsSelfAdjoint]))
  simpa only [HermitianMat.le_iff, HermitianMat.mat_sub, HermitianMat.mat_smul,
    HermitianMat.mat_one, hmat] using! hc

open Matrix Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Topology

theorem mmw_trace_mul_mono (D : ℕ) (W X Y : Operator D) (hW : W.PosSemidef)
    (hXY : X ≤ Y) : (Matrix.trace (W*X)).re ≤ (Matrix.trace (W*Y)).re := by
  have hp : (Y-X).PosSemidef := Matrix.le_iff.mp hXY
  let HW : HermitianMat (Fin D) ℂ := ⟨W,hW.isHermitian⟩
  let HV : HermitianMat (Fin D) ℂ := ⟨Y-X,hp.isHermitian⟩
  have hn := HermitianMat.inner_ge_zero (A := HW) (B := HV)
    (HermitianMat.zero_le_iff.mpr hW) (HermitianMat.zero_le_iff.mpr hp)
  change 0 ≤ (Matrix.trace (W*(Y-X))).re at hn
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hn
  linarith

theorem mmw_trace_loss_normalization (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ) :
    (Matrix.trace (M t * mmwState D M η t)).re =
      (Matrix.trace (M t * mmwWeight D M η t)).re /
        (Matrix.trace (mmwWeight D M η t)).re := by
  simp only [mmwState, Matrix.mul_smul, Matrix.trace_smul, ← Complex.ofReal_inv,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem mmwWeight_posSemidef (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ)
    (hD : 0<D) (hM : ∀ s, (M s).IsHermitian) : (mmwWeight D M η t).PosSemidef := by
  have hs : (∑ s∈Finset.range t, M s).IsHermitian := isSelfAdjoint_sum _ (fun s _ => hM s)
  exact (mmw_exp_positive_trace D _ hD (hs.smul (by simp [IsSelfAdjoint]))).1

theorem mmw_potential_ratio_step (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ)
    (hD : 0<D) (hη : 0<η) (hη1 : η≤1)
    (hM : ∀ s, (M s).IsHermitian ∧ ‖M s‖≤1) :
    (Matrix.trace (mmwWeight D M η (t+1))).re / (Matrix.trace (mmwWeight D M η t)).re ≤
      1 - η*(Matrix.trace (M t * mmwState D M η t)).re + η^2 := by
  let S := ∑ s∈Finset.range t, M s
  have hs : S.IsHermitian := isSelfAdjoint_sum _ (fun s _ => (hM s).1)
  have hx : (-η • S).IsHermitian := hs.smul (by simp [IsSelfAdjoint])
  have hy : (-η • M t).IsHermitian := (hM t).1.smul (by simp [IsSelfAdjoint])
  have hgt := matrix_mw_golden_thompson_trace_potential D (-η • S) (-η • M t) hx hy
  have hnext : mmwWeight D M η (t+1) = NormedSpace.exp ((-η • S)+(-η • M t)) := by
    simp only [mmwWeight, Finset.sum_range_succ, S, smul_add]
  rw [← hnext] at hgt
  change (Matrix.trace (mmwWeight D M η (t+1))).re ≤
    (Matrix.trace (mmwWeight D M η t * NormedSpace.exp (-η • M t))).re at hgt
  have hm := mmw_trace_mul_mono D (mmwWeight D M η t) _ _
    (mmwWeight_posSemidef D M η t hD (fun s => (hM s).1))
    (mmw_loss_exp_order D (M t) η hD (hM t).1 (hM t).2 hη hη1)
  have hu := hgt.trans hm
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hu
  rw [Matrix.trace_mul_comm (mmwWeight D M η t) (M t)] at hu
  have hz : 0 < (Matrix.trace (mmwWeight D M η t)).re :=
    (matrix_mw_actual_gibbs_iterates_density D M η t hD (fun s => (hM s).1)).1
  rw [mmw_trace_loss_normalization]
  apply (div_le_iff₀ hz).mpr
  have he : (1 - η*((Matrix.trace (M t * mmwWeight D M η t)).re /
      (Matrix.trace (mmwWeight D M η t)).re)+η^2) *
      (Matrix.trace (mmwWeight D M η t)).re =
      (1+η^2)*(Matrix.trace (mmwWeight D M η t)).re -
      η*(Matrix.trace (M t * mmwWeight D M η t)).re := by
    field_simp
    ring
  rw [he]
  exact hu

theorem mmw_log_potential_step (D : ℕ) (M : ℕ → Operator D) (η : ℝ) (t : ℕ)
    (hD : 0<D) (hη : 0<η) (hη1 : η≤1)
    (hM : ∀ s, (M s).IsHermitian ∧ ‖M s‖≤1) :
    Real.log (Matrix.trace (mmwWeight D M η (t+1))).re -
      Real.log (Matrix.trace (mmwWeight D M η t)).re ≤
        -η*(Matrix.trace (M t*mmwState D M η t)).re+η^2 := by
  have hp (s : ℕ) := (matrix_mw_actual_gibbs_iterates_density D M η s hD (fun j => (hM j).1)).1
  have hr := mmw_potential_ratio_step D M η t hD hη hη1 hM
  rw [← Real.log_div (hp (t+1)).ne' (hp t).ne']
  exact (Real.log_le_sub_one_of_pos (div_pos (hp (t+1)) (hp t))).trans (by linarith)

open Matrix Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Topology
set_option warningAsError false

theorem mmw_hermitian_exp_mat {d : Type*} [Fintype d] [DecidableEq d]
    (H : HermitianMat d ℂ) : H.exp.mat = NormedSpace.exp H.mat := by
  rw [HermitianMat.exp, HermitianMat.mat_cfc]
  letI : ContinuousFunctionalCalculus ℝ (Matrix d d ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  exact CFC.real_exp_eq_normedSpace_exp H.H

theorem mmw_density_exp_jensen (D : ℕ) (X σ : Operator D)
    (hX : X.IsHermitian) (hσ : IsDensityOperator σ) :
    Real.exp (Matrix.trace (σ * X)).re ≤ (Matrix.trace (NormedSpace.exp X)).re := by
  let U := hX.eigenvectorUnitary
  let R : Operator D := U.valᴴ * σ * U.val
  let p : Fin D → ℝ := fun i => (R i i).re
  have hR : R.PosSemidef := hσ.1.conjTranspose_mul_mul_same U.val
  have hpn (i : Fin D) : 0 ≤ p i := (Complex.nonneg_iff.mp (hR.diag_nonneg (i := i))).1
  have htr : Matrix.trace R = 1 := by
    dsimp [R]
    rw [Matrix.trace_mul_cycle,
      show U.val * U.valᴴ = 1 from
          (Matrix.mem_unitaryGroup_iff.mp U.property), Matrix.one_mul, hσ.2]
  have hpsum : ∑ i, p i = 1 := by
    change ∑ i, (R i i).re = 1
    simpa [Matrix.trace, ← Complex.re_sum] using! congrArg Complex.re htr
  have hple (i : Fin D) : p i ≤ 1 := by
    rw [← hpsum]
    exact Finset.single_le_sum (fun j _ => hpn j) (Finset.mem_univ i)
  have hex : (Matrix.trace (σ * X)).re = ∑ i, p i * hX.eigenvalues i := by
    conv_lhs => rw [hX.spectral_theorem]
    change (Matrix.trace (σ * (U.val * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * U.valᴴ))).re = _
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
    change (Matrix.trace (R * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)))).re = _
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, p]
  have htex : (Matrix.trace (NormedSpace.exp X)).re = ∑ i, Real.exp (hX.eigenvalues i) := by
    let H : HermitianMat (Fin D) ℂ := ⟨X,hX⟩
    change (Matrix.trace (NormedSpace.exp H.mat)).re = _
    rw [← mmw_hermitian_exp_mat H]
    exact H.trace_cfc_eq Real.exp
  rw [hex, htex]
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p)
    (p := hX.eigenvalues) (fun i _ => hpn i) hpsum (fun _ _ => Set.mem_univ _)
  have hj' : Real.exp (∑ i, p i * hX.eigenvalues i) ≤
      ∑ i, p i * Real.exp (hX.eigenvalues i) := by simpa only [smul_eq_mul] using! hj
  apply hj'.trans
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (hple i) (Real.exp_pos _).le).trans_eq (one_mul _)

theorem matrix_mw_noncommuting_regret
    (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) (σ : Operator D)
    (hD : 0<D) (hη : 0<η) (hη1 : η≤1)
    (hM : ∀ s, (M s).IsHermitian ∧ ‖M s‖≤1) (hσ : IsDensityOperator σ) :
    η*(∑ t∈Finset.range T, (Matrix.trace (M t*mmwState D M η t)).re) ≤
      η*(∑ t∈Finset.range T, (Matrix.trace (M t*σ)).re)+η^2*T+Real.log D := by
  have hu (n : ℕ) : Real.log (Matrix.trace (mmwWeight D M η n)).re ≤
      Real.log D - η*(∑ t∈Finset.range n, (Matrix.trace (M t*mmwState D M η t)).re)+η^2*n := by
    induction n with
    | zero => simp [mmwWeight, Matrix.trace_one]
    | succ n ih =>
      have hs := mmw_log_potential_step D M η n hD hη hη1 hM
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  let X : Operator D := -η • ∑ t∈Finset.range T, M t
  have hs : (∑ t∈Finset.range T, M t).IsHermitian := isSelfAdjoint_sum _ (fun s _ => (hM s).1)
  have hx : X.IsHermitian := hs.smul (by simp [IsSelfAdjoint])
  have hj := mmw_density_exp_jensen D X σ hx hσ
  have hl := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp] at hl
  change (Matrix.trace (σ*X)).re ≤ Real.log (Matrix.trace (mmwWeight D M η T)).re at hl
  have he : (Matrix.trace (σ*X)).re =
      -η*(∑ t∈Finset.range T, (Matrix.trace (M t*σ)).re) := by
    simp only [X, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [Matrix.trace_mul_comm]
  rw [he] at hl
  have hb := hu T
  nlinarith

end Qatlib.Concepts.MatrixWeights.WeightsCore
