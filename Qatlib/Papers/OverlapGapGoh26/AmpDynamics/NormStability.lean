/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.SpinReadoutL2
import Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Euclidean stability of actual field histories

Bounds tensor-contraction vectors and the changes caused by perturbing their tensor and spin
inputs. These estimates control the actual field histories and raw spin outputs used in the
Gaussian analysis of [GohMuller2026].

The stability bounds depend on a scaled multilinear norm bound for the comparison tensor, the
interaction degree, and the finite time horizon.

## Main statements

* `actual_history_norm`: propagates input perturbations through the field history.
* `actual_raw_spin_norm`: bounds the resulting perturbation of the raw spin readout.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.SpinReadoutL2
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability

/-- The tensor interaction vector regarded as an element of Euclidean space. -/
def headVector {r N : ℕ} (A : Tensor (r+1) N) (z : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (interaction (rowTensor A) (WithLp.ofLp z))

/-- The inner product with the tensor interaction vector equals the tensor multilinear form with
the test vector in its first slot. -/
theorem headVector_inner {r N : ℕ} (A : Tensor (r+1) N) (z v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ v (headVector A z)=tensorForm A (Fin.cons v (fun _ : Fin r => z)) := by
  rw [tensorForm_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (r+1) => Fin N)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [headVector,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    interaction,rowTensor,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [Fin.consEquiv,Equiv.coe_fn_mk]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

/-- If `C ≥ 0` and `|⟪v, v⟫| ≤ C * ‖v‖`, then `‖v‖ ≤ C`. -/
theorem norm_le_of_inner_self_bound {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (C : ℝ)
    (hC : 0≤C) (h : |inner ℝ v v|≤C*‖v‖) : ‖v‖≤C := by
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at h
  nlinarith [norm_nonneg v]

/-- The tensor interaction vector has norm at most `‖tensorForm A‖ * ‖z‖ ^ r`. -/
theorem headVector_norm {r N : ℕ} (A : Tensor (r+1) N) (z : EuclideanSpace ℝ (Fin N)) :
    ‖headVector A z‖≤‖tensorForm A‖*‖z‖^r := by
  apply norm_le_of_inner_self_bound _ _ (by positivity)
  rw [headVector_inner]
  have h := (tensorForm A).le_opNorm (Fin.cons (headVector A z) (fun _ : Fin r => z))
  simpa only [Real.norm_eq_abs,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc,mul_comm,mul_left_comm] using h

/-- For positive interaction degree, the interaction-vector difference is bounded by the
multilinear norm times `r * (max ‖z‖ ‖w‖) ^ (r − 1) * ‖z − w‖`. -/
theorem headVector_spin_difference {r N : ℕ} (hr : 0<r) (A : Tensor (r+1) N)
    (z w : EuclideanSpace ℝ (Fin N)) :
    ‖headVector A z-headVector A w‖≤
      ‖tensorForm A‖*(r:ℝ)*max ‖z‖ ‖w‖^(r-1)*‖z-w‖ := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  let v := headVector A z-headVector A w
  apply norm_le_of_inner_self_bound v _ (by positivity)
  rw [inner_sub_right,headVector_inner,headVector_inner]
  have h := ((tensorForm A).curryLeft v).norm_image_sub_le (fun _ : Fin r => z) (fun _ => w)
  have hn := (tensorForm A).curryLeft.le_opNorm v
  rw [ContinuousMultilinearMap.curryLeft_norm] at hn
  have hd : (fun _ : Fin r => z)-(fun _ => w)=(fun _ => z-w) := rfl
  rw [hd] at h
  simp only [Fintype.card_fin] at h
  have hs := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg r)) (by positivity)) (norm_nonneg _))
  simpa only [ContinuousMultilinearMap.curryLeft_apply,Real.norm_eq_abs,Fintype.card_fin,
    pi_norm_const, mul_assoc,mul_comm,mul_left_comm] using hs

/-- A spin vector with each coordinate of absolute value at most one has Euclidean norm at most
`√N`. -/
theorem cube_spin_norm {N : ℕ} (z : EuclideanSpace ℝ (Fin N))
    (hz : ∀ i,|z i|≤1) : ‖z‖≤Real.sqrt (N:ℝ) := by
  apply Real.le_sqrt_of_sq_le
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin N,(1:ℝ) := Finset.sum_le_sum (fun i _ => by nlinarith [hz i,abs_nonneg (z i),sq_abs (z i)])
    _ = _ := by simp

/-- For positive `N` and a spin vector in the cube, changing the source tensor input from `G` to
`D` changes the interaction vector by at most `‖G − D‖`. -/
theorem source_head_tensor_difference {r N : ℕ} (hN : 0<N)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (z : EuclideanSpace ℝ (Fin N))
    (hz : ∀ i,|z i|≤1) :
    ‖headVector (sourceTensor G.ofLp) z-headVector (sourceTensor D.ofLp) z‖≤‖G-D‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hp : (N:ℝ)^r≠0 := pow_ne_zero _ hn.ne'
  have hrow (i : Fin N) :
      (interaction (rowTensor (sourceTensor G.ofLp)) z.ofLp i-
        interaction (rowTensor (sourceTensor D.ofLp)) z.ofLp i)^2≤
      ∑ k : Fin r→Fin N,(G (Fin.cons i k)-D (Fin.cons i k))^2 := by
    have he : interaction (rowTensor (sourceTensor G.ofLp)) z.ofLp i-
        interaction (rowTensor (sourceTensor D.ofLp)) z.ofLp i=
        Real.sqrt (((N:ℝ)^r)⁻¹)*(∑ k : Fin r→Fin N,
          (G (Fin.cons i k)-D (Fin.cons i k))*(∏ a,z (k a))) := by
      simp only [interaction,rowTensor,sourceTensor,Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he,mul_pow,Real.sq_sqrt (by positivity : 0≤((N:ℝ)^r)⁻¹)]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin r→Fin N => G (Fin.cons i k)-D (Fin.cons i k))
      (fun k : Fin r→Fin N => ∏ a,z (k a))
    have hc := cube_coefficient_sq_bound z.ofLp (fun i => by exact abs_le.mp (hz i)) (q:=r)
    have hh := hcs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    refine (mul_le_mul_of_nonneg_left hh (by positivity : 0≤((N:ℝ)^r)⁻¹)).trans_eq ?_
    field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(interaction (rowTensor (sourceTensor G.ofLp)) z.ofLp i-
    interaction (rowTensor (sourceTensor D.ofLp)) z.ofLp i)^2)≤∑ k,(G k-D k)^2
  refine (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq ?_
  simpa only [Fintype.sum_prod_type,Fin.consEquiv_apply] using!
    (Fin.consEquiv (fun _ : Fin (r+1) => Fin N)).sum_comp (fun k => (G k-D k)^2)

/-- For positive degree and dimension, cube-valued spins, and the stated scaled
comparison-tensor norm bound, the interaction-vector difference is at most `‖G − D‖ + K * r
* ‖z − w‖`. -/
theorem source_head_joint_difference {r N : ℕ} (hr : 0<r) (hN : 0<N)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (z w : EuclideanSpace ℝ (Fin N))
    (hz : ∀ i,|z i|≤1) (hw : ∀ i,|w i|≤1) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    ‖headVector (sourceTensor G.ofLp) z-headVector (sourceTensor D.ofLp) w‖≤
      ‖G-D‖+K*(r:ℝ)*‖z-w‖ := by
  have hd := headVector_spin_difference hr (sourceTensor D.ofLp) z w
  have hrad : max ‖z‖ ‖w‖≤Real.sqrt (N:ℝ) := max_le (cube_spin_norm z hz) (cube_spin_norm w hw)
  have hspin : ‖headVector (sourceTensor D.ofLp) z-headVector (sourceTensor D.ofLp) w‖≤
      K*(r:ℝ)*‖z-w‖ := by
    refine hd.trans ?_
    calc
      _ ≤ ‖tensorForm (sourceTensor D.ofLp)‖*(r:ℝ)*(Real.sqrt (N:ℝ))^(r-1)*‖z-w‖ := by gcongr
      _ = (‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1))*(r:ℝ)*‖z-w‖ := by ring
      _ ≤ _ := by gcongr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (source_head_tensor_difference hN G D z hz) hspin)

/-- Applying a scalar 1-Lipschitz map coordinatewise does not increase Euclidean distances. -/
theorem scalar_map_l2 {N : ℕ} (κ : ℝ→ℝ) (hκ : LipschitzWith 1 κ) (u v : Fin N→ℝ) :
    ‖(WithLp.toLp 2 (fun i => κ (u i)) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (fun i => κ (v i))‖≤
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have h : |κ (u i)-κ (v i)|≤|u i-v i| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hκ.dist_le_mul (u i) (v i)
  simpa only [sq_abs] using! pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The Euclidean distance between histories with an appended vector is at most the old history
distance plus the appended-vector distance. -/
theorem snoc_history_norm {t N : ℕ} (U V : Fin (t+1)→Fin N→ℝ) (u v : Fin N→ℝ) :
    ‖historyVector (Fin.snoc U u)-historyVector (Fin.snoc V v)‖≤
      ‖historyVector U-historyVector V‖+
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 v‖ := by
  have he : ‖historyVector (Fin.snoc U u)-historyVector (Fin.snoc V v)‖^2=
      ‖historyVector U-historyVector V‖^2+
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 v‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,historyVector,PiLp.sub_apply,
      Fintype.sum_prod_type,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  nlinarith [norm_nonneg (historyVector (Fin.snoc U u)-historyVector (Fin.snoc V v)),
    norm_nonneg (historyVector U-historyVector V),
    norm_nonneg ((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 v)]

/-- Under the stated schedule and comparison-tensor norm bounds, the next-coordinate distance is
at most the tensor-input distance plus the seed distance plus `2 * K * r * √T` times the
history distance. -/
theorem actual_next_norm {r N T t : ℕ} (hr : 0<r) (hN : 0<N)
    (κ : ℝ→ℝ) (hκ : LipschitzWith 1 κ) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ht : t≤T)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed seed' : Fin N→ℝ) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    let U := fieldHistory κ (rowTensor (sourceTensor G.ofLp)) seed s t
    let V := fieldHistory κ (rowTensor (sourceTensor D.ofLp)) seed' s t
    ‖(WithLp.toLp 2 (historyNext κ (rowTensor (sourceTensor G.ofLp)) s t U) : EuclideanSpace ℝ (Fin N))-
      WithLp.toLp 2 (historyNext κ (rowTensor (sourceTensor D.ofLp)) s t V)‖≤
      ‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖+
      (2*K*(r:ℝ)*Real.sqrt (T:ℝ))*‖historyVector U-historyVector V‖ := by
  (try dsimp only)
  let U := fieldHistory κ (rowTensor (sourceTensor G.ofLp)) seed s t
  let V := fieldHistory κ (rowTensor (sourceTensor D.ofLp)) seed' s t
  let z := spinVector s U
  let w := spinVector s V
  let b : Fin N→ℝ :=
      fun i => FCoord (s t) (interaction (rowTensor (sourceTensor G.ofLp)) (spinReadout s t U) i) (fun a => U a i)
  let b' : Fin N→ℝ :=
      fun i => FCoord (s t) (interaction (rowTensor (sourceTensor D.ofLp)) (spinReadout s t V) i) (fun a => V a i)
  let c := (s t)^2*(1-s t)
  let e : EuclideanSpace ℝ (Fin N) :=
      WithLp.toLp 2 (fun i => κ (seed i))-WithLp.toLp 2 (fun i => κ (seed' i))
  have hK0 : 0≤K := le_trans (by positivity) hK
  have hc : |c|≤1 := by
    have hc := catalyst_coefficient_bounds (s t) (hs t ht)
    rw [abs_of_nonneg hc.1]
    linarith [hc.2]
  have he : (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 b'=
      (headVector (sourceTensor G.ofLp) z-headVector (sourceTensor D.ofLp) w)+c•e := by
    ext i
    change b i-b' i=interaction (rowTensor (sourceTensor G.ofLp)) z.ofLp i-
      interaction (rowTensor (sourceTensor D.ofLp)) w.ofLp i+c*(κ (seed i)-κ (seed' i))
    dsimp only [b,b',FCoord,z,w,spinVector,c]
    have hu := congrFun (fieldHistory_initial κ (rowTensor (sourceTensor G.ofLp)) seed s t) i
    have hv := congrFun (fieldHistory_initial κ (rowTensor (sourceTensor D.ofLp)) seed' s t) i
    change U 0 i=κ (seed i) at hu
    change V 0 i=κ (seed' i) at hv
    rw [hu,hv]
    ring
  have hz : ∀ i,|z i|≤1 := fun i => phi_abs_le_one s t _
  have hw : ∀ i,|w i|≤1 := fun i => phi_abs_le_one s t _
  have hh := source_head_joint_difference hr hN G D z w hz hw K hK
  have hspin : ‖z-w‖≤2*Real.sqrt (T:ℝ)*‖historyVector U-historyVector V‖ := by
    refine (spinReadout_l2 s (fun j hj => hs j (hj.trans ht)) U V).trans ?_
    gcongr
  have hseed := scalar_map_l2 κ hκ seed seed'
  have hb : ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 b'‖≤
      ‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖+
      (2*K*(r:ℝ)*Real.sqrt (T:ℝ))*‖historyVector U-historyVector V‖ := by
    rw [he]
    calc
      _ ≤ ‖headVector (sourceTensor G.ofLp) z-headVector (sourceTensor D.ofLp) w‖+‖c•e‖ := norm_add_le _ _
      _ ≤ (‖G-D‖+K*(r:ℝ)*‖z-w‖)+1*‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add hh (mul_le_mul hc hseed (norm_nonneg e) (by norm_num))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hspin (mul_nonneg hK0 (Nat.cast_nonneg r))]
  exact (scalar_map_l2 κ hκ b b').trans hb

/-- Under the stated nonexpansive update, schedule, and comparison-tensor norm hypotheses, the
stage-`t` history distance is bounded by `(2 + 2 * K * r * √T) ^ t` times the sum of
tensor-input and seed distances. -/
theorem actual_history_norm {r N T : ℕ} (hr : 0<r) (hN : 0<N)
    (κ : ℝ→ℝ) (hκ : LipschitzWith 1 κ) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed seed' : Fin N→ℝ) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    ∀ t≤T, ‖historyVector (fieldHistory κ (rowTensor (sourceTensor G.ofLp)) seed s t)-
      historyVector (fieldHistory κ (rowTensor (sourceTensor D.ofLp)) seed' s t)‖≤
      (2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^t*
      (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖) := by
  have hK0 : 0≤K := le_trans (by positivity) hK
  let B := 2+2*K*(r:ℝ)*Real.sqrt (T:ℝ)
  let d := ‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖
  have hB : 1≤B := by
    have h0 : 0≤2*K*(r:ℝ)*Real.sqrt (T:ℝ) := by positivity
    dsimp [B]
    linarith
  have hd : 0≤d := by dsimp [d]; positivity
  intro t
  induction t with
  | zero =>
    intro _
    have he : ‖historyVector (fieldHistory κ (rowTensor (sourceTensor G.ofLp)) seed s 0)-
        historyVector (fieldHistory κ (rowTensor (sourceTensor D.ofLp)) seed' s 0)‖=
        ‖(WithLp.toLp 2 (fun i => κ (seed i)) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (fun i => κ (seed' i))‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [EuclideanSpace.real_norm_sq_eq,historyVector,fieldHistory,PiLp.sub_apply,
        Fintype.sum_prod_type]
      change (∑ _a : Fin 1,∑ i : Fin N,(κ (seed i)-κ (seed' i))^2)=_
      simp
    rw [he,pow_zero,one_mul]
    exact (scalar_map_l2 κ hκ seed seed').trans (le_add_of_nonneg_left (norm_nonneg _))
  | succ t ih =>
    intro ht
    let U := fieldHistory κ (rowTensor (sourceTensor G.ofLp)) seed s t
    let V := fieldHistory κ (rowTensor (sourceTensor D.ofLp)) seed' s t
    have hp := ih (by omega)
    have hn := actual_next_norm hr hN κ hκ s hs (by omega : t≤T) G D seed seed' K hK
    have htB : 1≤B^t := one_le_pow₀ hB
    have hstep : d≤B^t*d := by nlinarith [mul_nonneg (sub_nonneg.mpr htB) hd]
    change ‖historyVector (Fin.snoc U (historyNext κ (rowTensor (sourceTensor G.ofLp)) s t U))-
      historyVector (Fin.snoc V (historyNext κ (rowTensor (sourceTensor D.ofLp)) s t V))‖≤B^(t+1)*d
    calc
      _ ≤ ‖historyVector U-historyVector V‖+
        ‖(WithLp.toLp 2 (historyNext κ (rowTensor (sourceTensor G.ofLp)) s t U) : EuclideanSpace ℝ (Fin N))-
          WithLp.toLp 2 (historyNext κ (rowTensor (sourceTensor D.ofLp)) s t V)‖ := snoc_history_norm _ _ _ _
      _ ≤ ‖historyVector U-historyVector V‖+(d+(B-2)*‖historyVector U-historyVector V‖) := by
        apply add_le_add le_rfl
        simpa only [B,d,add_sub_cancel_left] using hn
      _ = (B-1)*‖historyVector U-historyVector V‖+d := by ring
      _ ≤ (B-1)*(B^t*d)+d := by gcongr
      _ ≤ (B-1)*(B^t*d)+(B^t*d) := add_le_add le_rfl hstep
      _ = _ := by rw [pow_succ]; ring

/-- Under the stated schedule and comparison-tensor norm hypotheses, the raw spin-output
distance is bounded by `2 * √T * (2 + 2 * K * r * √T) ^ T` times the sum of tensor-input and
seed distances [GohMuller2026]. -/
theorem actual_raw_spin_norm {r N T : ℕ} (hr : 0<r) (hN : 0<N)
    (s : ℕ→ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed seed' : Fin N→ℝ) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    ‖(WithLp.toLp 2 (fun i => feedbackState id (rowTensor (sourceTensor G.ofLp)) seed s T i 2) : EuclideanSpace ℝ (Fin N))-
      WithLp.toLp 2 (fun i => feedbackState id (rowTensor (sourceTensor D.ofLp)) seed' s T i 2)‖≤
      (2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T)*
        (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖) := by
  have he (A : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (u : Fin N→ℝ) :
      (WithLp.toLp 2 (fun i => feedbackState id (rowTensor (sourceTensor A.ofLp)) u s T i 2) : EuclideanSpace ℝ (Fin N))=
      spinVector s (fieldHistory id (rowTensor (sourceTensor A.ofLp)) u s T) := by
    ext i
    exact actual_feedback_phi id _ u s T i
  rw [he G seed,he D seed']
  refine (spinReadout_l2 s hs _ _).trans ?_
  have hh := actual_history_norm hr hN id LipschitzWith.id s hs G D seed seed' K hK T le_rfl
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*Real.sqrt (T:ℝ))).trans_eq (by ring)

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability
