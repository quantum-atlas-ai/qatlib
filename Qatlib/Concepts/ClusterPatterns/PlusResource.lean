/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.CountedClusterSequence
import Mathlib.Analysis.Normed.Module.Connected
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.ClusterPatterns.PlusResource

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable def clusterPlusState : QState (Fin 2) := relabelState boolEquivFin2 Plus

noncomputable def clusterPlusInput (n : ℕ) : QState (Fin (2 ^ (n + 1))) :=
  clusterSequenceInitialFrame n *ᵥ clusterPlusState

noncomputable def clusterPlusOutputVector (zs : List ℂ) (ω : Reg zs.length) :
    QState (Fin (2 ^ (zs.length + 1))) :=
  (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator *ᵥ
    clusterPlusInput zs.length

theorem clusterPlus_unit_phase (a b : ℂ) (h : ‖a‖ = ‖b‖) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ z * b = a := by
  by_cases hb : b = 0
  · have ha : a = 0 := norm_eq_zero.mp (by simpa [hb] using h)
    exact ⟨1, norm_one, by simp [ha, hb]⟩
  · refine ⟨a / b, ?_, div_mul_cancel₀ a hb⟩
    rw [norm_div, h, div_self (norm_ne_zero_iff.mpr hb)]

theorem clusterPlus_circle_intersection (p : ℂ) (r s : ℝ)
    (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hlo : |r - ‖p‖| ≤ s) (hhi : s ≤ r + ‖p‖) :
    ∃ w : ℂ, ‖w‖ = r ∧ ‖w - p‖ = s := by
  obtain ⟨u, hu, hp⟩ := Complex.exists_norm_eq_mul_self p
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hn (x : ℂ) : ‖u * x‖ = ‖x‖ := by rw [norm_mul, hu, one_mul]
  let a : ℂ := u⁻¹ * (r : ℂ)
  have hua : u * a = (r : ℂ) := by dsimp [a]; field_simp
  have ha : ‖a‖ = r := by rw [← hn a, hua, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hb : ‖-a‖ = r := by simpa using ha
  have hda : ‖a - p‖ = |r - ‖p‖| := by
    rw [← hn (a - p), mul_sub, hua, ← hp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdb : ‖-a - p‖ = r + ‖p‖ := by
    rw [← hn (-a - p), mul_sub, mul_neg, hua, ← hp]
    rw [show -(r : ℂ) - (‖p‖ : ℂ) = -((r + ‖p‖ : ℝ) : ℂ) by push_cast; ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc := isPreconnected_sphere (E := ℂ)
    (by rw [Complex.rank_real_complex]; norm_num) 0 r
  have hcont : ContinuousOn (fun w : ℂ => ‖w - p‖) (Metric.sphere 0 r) :=
    (continuous_id.sub continuous_const).norm.continuousOn
  obtain ⟨w, hw, hws⟩ := hc.intermediate_value
    (by simpa [Metric.mem_sphere, dist_zero_right] using ha)
    (by simpa [Metric.mem_sphere, dist_zero_right] using hb) hcont
    (show s ∈ Set.Icc ‖a - p‖ ‖-a - p‖ by simpa [hda, hdb] using And.intro hlo hhi)
  exact ⟨w, by simpa [Metric.mem_sphere, dist_zero_right] using hw, hws⟩

theorem clusterPlus_actual_amplitude (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1)
    (ω v : Reg zs.length) (c : Fin 2) :
    clusterPlusOutputVector zs ω
        (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c)) =
      if v = ω then ((Real.sqrt 2 : ℂ)⁻¹)^zs.length *
        (clusterSequenceUnitary zs *ᵥ clusterPlusState) c else 0 := by
  classical
  unfold clusterPlusOutputVector clusterPlusInput
  rw [Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct,
    cluster_sequence_actual_leaf_full_amplitude zs hzs ω v c]
  by_cases h : v = ω
  · simp only [if_pos h]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [h]

theorem clusterPlus_actual_cost (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1)
    (ω : Reg zs.length) :
    (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).accepted = true ∧
    (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).queries = 0 ∧
    (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).measurements = zs.length ∧
    (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).gates = 6 * zs.length - 1 := by
  have h := (cluster_sequence_actual_program_and_feedback_cost zs hzs).2.2.2 ω
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1⟩

private theorem clusterPlus_q_pos : 0 < (Real.sqrt 2)⁻¹ := by positivity

private theorem clusterPlus_q_sq : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem clusterPlus_hadamard_norm (e f : ℂ) :
    ‖((Real.sqrt 2 : ℂ)⁻¹) * (e + f)‖^2 +
      ‖((Real.sqrt 2 : ℂ)⁻¹) * (e - f)‖^2 = ‖e‖^2 + ‖f‖^2 := by
  have ha := norm_add_sq (𝕜 := ℂ) e f
  have hs := norm_sub_sq (𝕜 := ℂ) e f
  have hq : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, norm_mul, hq, mul_pow, mul_pow, clusterPlus_q_sq]
  nlinarith

theorem clusterPlus_small_component (e t : ℂ) (h : ‖e‖^2 + ‖t‖^2 = 1) :
    ∃ f : ℂ, ‖f‖ = ‖t‖ ∧
      ‖((Real.sqrt 2 : ℂ)⁻¹) * (e + f)‖ ≤ (Real.sqrt 2)⁻¹ := by
  obtain ⟨u, hu, he⟩ := Complex.exists_norm_eq_mul_self e
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let f : ℂ := u⁻¹ * (-‖t‖ : ℂ)
  have huf : u * f = (-‖t‖ : ℂ) := by dsimp [f]; field_simp
  have hn (x : ℂ) : ‖u * x‖ = ‖x‖ := by rw [norm_mul, hu, one_mul]
  have hf : ‖f‖ = ‖t‖ := by
    rw [← hn f, huf, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hsum : ‖e + f‖ = |‖e‖ - ‖t‖| := by
    rw [← hn (e + f), mul_add, ← he, huf]
    simp only [← sub_eq_add_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he1 : ‖e‖ ≤ 1 := by nlinarith [norm_nonneg e, sq_nonneg ‖t‖]
  have ht1 : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg t, sq_nonneg ‖e‖]
  have hdiff : |‖e‖ - ‖t‖| ≤ 1 := abs_le.mpr ⟨by linarith [norm_nonneg e],
    by linarith [norm_nonneg t]⟩
  refine ⟨f, hf, ?_⟩
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hsum]
  simpa using mul_le_mul_of_nonneg_left hdiff clusterPlus_q_pos.le

theorem clusterPlus_actual_density (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1)
    (ω : Reg zs.length) (c c' : Fin 2) :
    (∑ v : Reg zs.length,
      clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
        (v, boolEquivFin2.symm c)) *
      star (clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
        (v, boolEquivFin2.symm c')))) =
      ((Real.sqrt 2 : ℂ)⁻¹)^(2 * zs.length) *
        (clusterSequenceUnitary zs *ᵥ clusterPlusState) c *
        star ((clusterSequenceUnitary zs *ᵥ clusterPlusState) c') := by
  classical
  rw [Fintype.sum_eq_single ω]
  · have hstar : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
    simp only [clusterPlus_actual_amplitude zs hzs, if_true, star_mul, star_pow, hstar]
    rw [Nat.mul_comm 2 zs.length, pow_mul, pow_two]
    ring
  · intro v hv
    simp only [clusterPlus_actual_amplitude zs hzs, if_neg hv, zero_mul]

theorem clusterPlus_actual_mass (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1)
    (φ : QState (Fin 2)) (hφ : (∑ c : Fin 2, ‖φ c‖ * ‖φ c‖) = 1)
    (hword : clusterSequenceUnitary zs *ᵥ clusterPlusState = φ) (ω : Reg zs.length) :
    (∑ r : Fin (2 ^ (zs.length + 1)),
      ‖clusterPlusOutputVector zs ω r‖ * ‖clusterPlusOutputVector zs ω r‖) =
        (1 / 2 : ℝ)^zs.length := by
  classical
  let e : Reg zs.length × Fin 2 ≃ Fin (2 ^ (zs.length + 1)) :=
    (Equiv.prodCongr (Equiv.refl _) boolEquivFin2.symm).trans
      (clusterSequenceRegisterEquiv zs.length)
  rw [← e.sum_comp (fun r => ‖clusterPlusOutputVector zs ω r‖ *
    ‖clusterPlusOutputVector zs ω r‖), Fintype.sum_prod_type]
  change (∑ v : Reg zs.length, ∑ c : Fin 2,
    ‖clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
      (v, boolEquivFin2.symm c))‖ *
    ‖clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
      (v, boolEquivFin2.symm c))‖) = _
  rw [Fintype.sum_eq_single ω]
  · simp only [clusterPlus_actual_amplitude zs hzs, if_true, hword, norm_mul]
    have hq : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ = (Real.sqrt 2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    simp only [norm_pow, hq]
    calc
      _ = (((Real.sqrt 2)⁻¹)^2)^zs.length * (∑ c : Fin 2, ‖φ c‖ * ‖φ c‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [← pow_mul, Nat.mul_comm 2 zs.length, pow_mul, pow_two]
        ring
      _ = _ := by rw [hφ, mul_one, clusterPlus_q_sq]
  · intro v hv
    simp only [clusterPlus_actual_amplitude zs hzs, if_neg hv, norm_zero, zero_mul,
      Finset.sum_const_zero]

theorem clusterPlus_middle_circle (c s : ℂ) (hn : ‖c‖^2 + ‖s‖^2 = 1)
    (hc : ‖c‖ ≤ (Real.sqrt 2)⁻¹) :
    ∃ w : ℂ, ‖w‖ = ‖s‖ ∧
      ‖((Real.sqrt 2 : ℂ) * (c + w)) - 1‖ = 1 := by
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hq : 0 < q := clusterPlus_q_pos
  have hq2 : q^2 = (1 / 2 : ℝ) := clusterPlus_q_sq
  have hcq : ‖c‖ ≤ q := hc
  have hsq : q ≤ ‖s‖ := by nlinarith [norm_nonneg c, norm_nonneg s]
  have hcs : ‖c‖ + ‖s‖ ≤ 2 * q := by
    nlinarith [sq_nonneg (‖c‖ - ‖s‖), norm_nonneg c, norm_nonneg s]
  let p : ℂ := (q : ℂ) - c
  have hp0 : ‖(q : ℂ)‖ = q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hp_lo : q - ‖c‖ ≤ ‖p‖ := by
    simpa only [p, hp0] using norm_sub_norm_le (q : ℂ) c
  have hp_hi : ‖p‖ ≤ q + ‖c‖ := by
    simpa only [p, hp0] using norm_sub_le (q : ℂ) c
  obtain ⟨w, hw, hwp⟩ := clusterPlus_circle_intersection p ‖s‖ q
    (norm_nonneg s) hq.le (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by linarith [norm_nonneg p])
  refine ⟨w, hw, ?_⟩
  have hsqrt0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have heq : (Real.sqrt 2 : ℂ) * (c + w) - 1 =
      (Real.sqrt 2 : ℂ) * (w - p) := by
    dsimp [p, q]
    push_cast
    field_simp
    ring
  rw [heq, norm_mul, hwp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  exact mul_inv_cancel₀ (by positivity)

theorem clusterPlusState_entry (i : Fin 2) :
    clusterPlusState i = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases i <;> simp [clusterPlusState, Plus, Hadamard, relabelState, boolEquivFin2]

theorem clusterPlus_J_apply (z : ℂ) (x : QState (Fin 2)) (i : Fin 2) :
    (clusterJ z *ᵥ x) i = if i = 0 then
      (Real.sqrt 2 : ℂ)⁻¹ * (x 0 + z * x 1) else
      (Real.sqrt 2 : ℂ)⁻¹ * (x 0 - z * x 1) := by
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, clusterJ_entry] <;> ring

theorem clusterPlus_first_two (c w : ℂ) (hn : ‖c‖^2 + ‖w‖^2 = 1)
    (hcirc : ‖(Real.sqrt 2 : ℂ) * (c + w) - 1‖ = 1) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ = 1 ∧ ‖z₂‖ = 1 ∧
      (clusterJ z₂ *ᵥ (clusterJ z₁ *ᵥ clusterPlusState)) 0 = c ∧
      (clusterJ z₂ *ᵥ (clusterJ z₁ *ᵥ clusterPlusState)) 1 = w := by
  let a : ℂ := (Real.sqrt 2 : ℂ) * (c + w)
  let b : ℂ := 2 - a
  let u : ℂ := (Real.sqrt 2 : ℂ) * (c - w)
  have hpar : ‖a‖^2 + ‖u‖^2 = 4 := by
    have hplus := norm_add_sq (𝕜 := ℂ) c w
    have hminus := norm_sub_sq (𝕜 := ℂ) c w
    dsimp [a, u]
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), Real.sq_sqrt (by norm_num)]
    nlinarith
  have hcircle : ‖a - 1‖^2 = 1 := by rw [hcirc]; norm_num
  have ha := Complex.normSq_sub a 1
  have hb := Complex.normSq_sub (2 : ℂ) a
  simp only [Complex.normSq_eq_norm_sq] at ha hb
  norm_num [Complex.mul_re] at ha hb
  have hub : ‖u‖ = ‖b‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖u‖^2 = ‖2 - a‖^2
    nlinarith
  obtain ⟨z₂, hz₂, hz₂b⟩ := clusterPlus_unit_phase u b hub
  have hfirst0 : (clusterJ (a - 1) *ᵥ clusterPlusState) 0 = a / 2 := by
    rw [clusterPlus_J_apply]
    simp only [if_true, clusterPlusState_entry]
    calc
      _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * a := by ring
      _ = a / 2 := by rw [sqrt2_inv_sq]; ring
  have hfirst1 : (clusterJ (a - 1) *ᵥ clusterPlusState) 1 = b / 2 := by
    rw [clusterPlus_J_apply]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, clusterPlusState_entry]
    calc
      _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * b := by dsimp [b]; ring
      _ = b / 2 := by rw [sqrt2_inv_sq]; ring
  have hsqrt0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  refine ⟨a - 1, z₂, hcirc, hz₂, ?_, ?_⟩
  · rw [clusterPlus_J_apply]
    simp only [if_true, hfirst0, hfirst1, ← mul_div_assoc, hz₂b]
    dsimp [a, u]
    field_simp
    ring
  · rw [clusterPlus_J_apply]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, hfirst0, hfirst1,
      ← mul_div_assoc, hz₂b]
    dsimp [a, u]
    field_simp
    ring

theorem cluster_plus_word_surjectivity :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        clusterSequenceUnitary zs *ᵥ clusterPlusState = φ := by
  intro φ hφ
  have hφ2 : ‖φ 0‖^2 + ‖φ 1‖^2 = 1 := by
    simpa only [Fin.sum_univ_two, pow_two] using hφ
  let e : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (φ 0 + φ 1)
  let t : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (φ 0 - φ 1)
  have het : ‖e‖^2 + ‖t‖^2 = 1 :=
    (clusterPlus_hadamard_norm (φ 0) (φ 1)).trans hφ2
  obtain ⟨f, hf, hsmall⟩ := clusterPlus_small_component e t het
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (e + f)
  let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (e - f)
  have hcs : ‖c‖^2 + ‖s‖^2 = 1 := by
    change ‖(Real.sqrt 2 : ℂ)⁻¹ * (e + f)‖^2 +
      ‖(Real.sqrt 2 : ℂ)⁻¹ * (e - f)‖^2 = 1
    rw [clusterPlus_hadamard_norm, hf, het]
  obtain ⟨w, hw, hcircle⟩ := clusterPlus_middle_circle c s hcs hsmall
  have hcw : ‖c‖^2 + ‖w‖^2 = 1 := by rw [hw]; exact hcs
  obtain ⟨z₁, z₂, hz₁, hz₂, h20, h21⟩ := clusterPlus_first_two c w hcw hcircle
  obtain ⟨z₃, hz₃, hz₃w⟩ := clusterPlus_unit_phase s w hw.symm
  obtain ⟨z₄, hz₄, hz₄f⟩ := clusterPlus_unit_phase t f hf.symm
  let v : QState (Fin 2) := clusterJ z₂ *ᵥ (clusterJ z₁ *ᵥ clusterPlusState)
  have h30 : (clusterJ z₃ *ᵥ v) 0 = e := by
    rw [clusterPlus_J_apply]
    simp only [if_true, show v 0 = c from h20, show v 1 = w from h21, hz₃w]
    calc
      _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (2 * e) := by dsimp [c, s]; ring
      _ = e := by rw [sqrt2_inv_sq]; ring
  have h31 : (clusterJ z₃ *ᵥ v) 1 = f := by
    rw [clusterPlus_J_apply]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false,
      show v 0 = c from h20, show v 1 = w from h21, hz₃w]
    calc
      _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (2 * f) := by dsimp [c, s]; ring
      _ = f := by rw [sqrt2_inv_sq]; ring
  have h4 : clusterJ z₄ *ᵥ (clusterJ z₃ *ᵥ v) = φ := by
    funext i
    fin_cases i
    · rw [clusterPlus_J_apply]
      simp only [h30, h31, hz₄f]
      calc
        _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (2 * φ 0) := by
          dsimp [e, t]; ring
        _ = φ 0 := by rw [sqrt2_inv_sq]; ring
    · rw [clusterPlus_J_apply]
      simp only [h30, h31, hz₄f]
      calc
        _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (2 * φ 1) := by
          dsimp [e, t]; ring
        _ = φ 1 := by rw [sqrt2_inv_sq]; ring
  refine ⟨[z₁, z₂, z₃, z₄], rfl, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  · simpa only [clusterSequenceUnitary, Matrix.one_mul, ← Matrix.mulVec_mulVec] using h4

theorem cluster_plus_resource_preparation :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        clusterSequenceUnitary zs *ᵥ clusterPlusState = φ ∧
        (∀ (ω v : Reg zs.length) (c : Fin 2),
          clusterPlusOutputVector zs ω
            (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c)) =
          if v = ω then ((Real.sqrt 2 : ℂ)⁻¹)^zs.length * φ c else 0) ∧
        (∀ ω : Reg zs.length,
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).accepted = true ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).queries = 0 ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).measurements = zs.length ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).gates = 6 * zs.length - 1) := by
  intro φ hφ
  obtain ⟨zs, hlen, hzs, hword⟩ := cluster_plus_word_surjectivity φ hφ
  refine ⟨zs, hlen, hzs, hword, ?_, clusterPlus_actual_cost zs hzs⟩
  intro ω v c
  rw [clusterPlus_actual_amplitude zs hzs, hword]

theorem cluster_plus_resource_output_density :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        (∀ (ω : Reg zs.length) (c c' : Fin 2),
          (∑ v : Reg zs.length,
            clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
              (v, boolEquivFin2.symm c)) *
            star (clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
              (v, boolEquivFin2.symm c')))) =
            ((Real.sqrt 2 : ℂ)⁻¹)^(2 * zs.length) * φ c * star (φ c')) ∧
        (∀ ω : Reg zs.length, (∑ r : Fin (2 ^ (zs.length + 1)),
          ‖clusterPlusOutputVector zs ω r‖ * ‖clusterPlusOutputVector zs ω r‖) =
            (1 / 2 : ℝ)^zs.length) := by
  intro φ hφ
  obtain ⟨zs, hlen, hzs, hword, _hamp, _hcost⟩ := cluster_plus_resource_preparation φ hφ
  refine ⟨zs, hlen, hzs, ?_, clusterPlus_actual_mass zs hzs φ hφ hword⟩
  intro ω c c'
  rw [clusterPlus_actual_density zs hzs, hword]

end Qatlib.Concepts.ClusterPatterns.PlusResource
