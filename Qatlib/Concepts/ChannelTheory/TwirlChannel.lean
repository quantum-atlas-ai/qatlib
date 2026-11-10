/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowChannel

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

namespace Qatlib.Concepts.ChannelTheory.TwirlChannel
set_option maxHeartbeats 800000
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem sum_mul_right_reindex {G : Type} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    (W : G → M) (h : G) : ∑ g, W (g * h) = ∑ k, W k := by
  let e : G ≃ G := ⟨fun x => x * h, fun x => x * h⁻¹,
    fun x => by simp, fun x => by simp [mul_assoc]⟩
  have he : (fun g : G => W (g * h)) = fun g => W (e g) := rfl
  rw [he]
  exact Equiv.sum_comp e W

theorem sum_mul_left_reindex {G : Type} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    (W : G → M) (h : G) : ∑ g, W (h * g) = ∑ k, W k := by
  let e : G ≃ G := ⟨fun x => h * x, fun x => h⁻¹ * x,
    fun x => by simp [mul_assoc], fun x => by simp [mul_assoc]⟩
  have he : (fun g : G => W (h * g)) = fun g => W (e g) := rfl
  rw [he]
  exact Equiv.sum_comp e W

theorem sum_const_card_smul {G : Type} [Fintype G] {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (c : M) : (∑ _j : G, c) = ((Fintype.card G : ℂ)) • c := by
  rw [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ (Fintype.card G) c).symm

theorem familyTwirl_apply {J : Type} [Fintype J] {D : ℕ} (U : J → Operator D) (ρ : Operator D) :
    FamilyTwirl U ρ = ((Fintype.card J : ℂ)⁻¹) • ∑ j, U j * ρ * (U j).conjTranspose := by
  show ((Fintype.card J : ℂ)⁻¹) • (∑ j, conjBranch (U j)) ρ = _
  simp only [LinearMap.sum_apply, conjBranch_apply]

theorem trace_conj_unitary {D : ℕ} {V : Operator D} (hV : IsUnitaryMatrix V) (A : Operator D) :
    Matrix.trace (V * A * V.conjTranspose) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, hV.1, Matrix.one_mul]

theorem completelyPositive_real_smul {D E : ℕ} {F : Operator D →ₗ[ℂ] Operator E}
    (hF : CompletelyPositive F) {c : ℝ} (hc : 0 ≤ c) :
    CompletelyPositive (((c : ℝ) : ℂ) • F) := by
  intro r A hA
  have he : ChannelAmplification (((c : ℝ) : ℂ) • F) r A
      = ((c : ℝ) : ℂ) • ChannelAmplification F r A := by
    ext x y
    simp [ChannelAmplification]
  rw [he]
  exact (hF r A hA).smul (RCLike.nonneg_iff.mpr ⟨hc, rfl⟩)

theorem familyTwirl_completelyPositive {G : Type} [Group G] [Fintype G] {D : ℕ}
    (U : G → Operator D) : CompletelyPositive (FamilyTwirl U) := by
  have hsum : CompletelyPositive (∑ j : G, conjBranch (U j)) :=
    CompletelyPositive.sum fun j _ => completelyPositive_conjBranch (U j)
  have hscal : ((Fintype.card G : ℂ)⁻¹) = ((((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) := by
    simp [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [show FamilyTwirl U = ((Fintype.card G : ℂ)⁻¹) • (∑ j : G, conjBranch (U j)) from rfl, hscal]
  exact completelyPositive_real_smul hsum (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem familyTwirl_tracePreserving {G : Type} [Group G] [Fintype G] {D : ℕ}
    {U : G → Operator D} (hU : IsUnitaryRep U) : TracePreserving (FamilyTwirl U) := by
  intro A
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := by
    haveI : Nonempty G := ⟨1⟩
    exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ j : G, Matrix.trace (U j * A * (U j).conjTranspose) = Matrix.trace A :=
    fun j => trace_conj_unitary (hU.1 j) A
  have hsum : (∑ j : G, Matrix.trace (U j * A * (U j).conjTranspose))
      = ((Fintype.card G : ℂ)) * Matrix.trace A := by
    rw [show (∑ j : G, Matrix.trace (U j * A * (U j).conjTranspose))
        = (∑ j : G, Matrix.trace A) from Finset.sum_congr rfl (fun j _ => htr j),
      sum_const_card_smul, smul_eq_mul]
  rw [familyTwirl_apply U A, Matrix.trace_smul, smul_eq_mul, Matrix.trace_sum, hsum,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem familyTwirl_conj_conj {G : Type} [Group G] [Fintype G] {D : ℕ} {U : G → Operator D}
    (hU : IsUnitaryRep U) (g k : G) (ρ : Operator D) :
    U g * (U k * ρ * (U k).conjTranspose) * (U g).conjTranspose
      = U (g * k) * ρ * (U (g * k)).conjTranspose := by
  rw [hU.2.2 g k, Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

theorem familyTwirl_conj_invariant {G : Type} [Group G] [Fintype G] {D : ℕ} {U : G → Operator D}
    (hU : IsUnitaryRep U) (g : G) (ρ : Operator D) :
    FamilyTwirl U (U g * ρ * (U g).conjTranspose) = FamilyTwirl U ρ := by
  rw [familyTwirl_apply U (U g * ρ * (U g).conjTranspose)]
  have hs : ∀ k : G,
      U k * (U g * ρ * (U g).conjTranspose) * (U k).conjTranspose
        = U (k * g) * ρ * (U (k * g)).conjTranspose :=
    fun k => familyTwirl_conj_conj hU k g ρ
  simp only [hs]
  rw [sum_mul_right_reindex (fun m : G => U m * ρ * (U m).conjTranspose) g,
    ← familyTwirl_apply U ρ]

theorem familyTwirl_idempotent {G : Type} [Group G] [Fintype G] {D : ℕ} {U : G → Operator D}
    (hU : IsUnitaryRep U) (ρ : Operator D) :
    FamilyTwirl U (FamilyTwirl U ρ) = FamilyTwirl U ρ := by
  rw [familyTwirl_apply U (FamilyTwirl U ρ), familyTwirl_apply U ρ]
  have hsm : ∀ g : G,
      U g * (((Fintype.card G : ℂ)⁻¹) • ∑ k, U k * ρ * (U k).conjTranspose) * (U g).conjTranspose
        = ((Fintype.card G : ℂ)⁻¹)
            • (U g * (∑ k, U k * ρ * (U k).conjTranspose) * (U g).conjTranspose) := by
    intro g
    rw [Matrix.mul_smul, Matrix.smul_mul]
  simp only [hsm]
  rw [Finset.smul_sum]
  simp only [smul_smul]
  rw [← Finset.smul_sum]
  have hmul : ∀ g : G,
      U g * (∑ k : G, U k * ρ * (U k).conjTranspose) * (U g).conjTranspose
        = ∑ k : G, U g * (U k * ρ * (U k).conjTranspose) * (U g).conjTranspose := by
    intro g
    rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [hmul]
  have hs : ∀ (g k : G),
      U g * (U k * ρ * (U k).conjTranspose) * (U g).conjTranspose
        = U (g * k) * ρ * (U (g * k)).conjTranspose :=
    fun g k => familyTwirl_conj_conj hU g k ρ
  simp only [hs]
  rw [Finset.sum_comm]
  have hinner : ∀ k : G,
      (∑ g : G, U (g * k) * ρ * (U (g * k)).conjTranspose)
        = ∑ j : G, U j * ρ * (U j).conjTranspose :=
    fun k => sum_mul_right_reindex (fun m : G => U m * ρ * (U m).conjTranspose) k
  simp only [hinner, sum_const_card_smul]
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := by
    haveI : Nonempty G := ⟨1⟩
    exact_mod_cast Fintype.card_ne_zero
  have hscal : (((Fintype.card G : ℂ)⁻¹) * ((Fintype.card G : ℂ)⁻¹)) * (Fintype.card G : ℂ)
      = ((Fintype.card G : ℂ)⁻¹) := by
    rw [mul_assoc, inv_mul_cancel₀ hcard, mul_one]
  rw [smul_smul, hscal]

theorem pauli_family_conj_sum (ρ : Operator 2) :
    ∑ j : Fin 4, pauliFourFamily j * ρ * (pauliFourFamily j).conjTranspose
      = ((2 : ℂ) * Matrix.trace ρ) • 1 := by
  have h0 : pauliFourFamily 0 = (1 : Operator 2) := rfl
  have h1 : pauliFourFamily 1 = pauliX := rfl
  have h2 : pauliFourFamily 2 = pauliY := rfl
  have h3 : pauliFourFamily 3 = pauliZ := rfl
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  have h1c : ((1 : Operator 2)).conjTranspose = (1 : Operator 2) := Matrix.conjTranspose_one
  have hxc : pauliX.conjTranspose = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX]
  have hyc : pauliY.conjTranspose = pauliY := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliY]
  have hzc : pauliZ.conjTranspose = pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliZ]
  rw [h1c, hxc, hyc, hzc, Matrix.one_mul, Matrix.mul_one]
  have he : Matrix.trace ρ = ρ 0 0 + ρ 1 1 := Matrix.trace_fin_two ρ
  have px00 : pauliX 0 0 = 0 := rfl
  have px01 : pauliX 0 1 = 1 := rfl
  have px10 : pauliX 1 0 = 1 := rfl
  have px11 : pauliX 1 1 = 0 := rfl
  have py00 : pauliY 0 0 = 0 := rfl
  have py01 : pauliY 0 1 = -(Complex.I) := rfl
  have py10 : pauliY 1 0 = Complex.I := rfl
  have py11 : pauliY 1 1 = 0 := rfl
  have pz00 : pauliZ 0 0 = 1 := rfl
  have pz01 : pauliZ 0 1 = 0 := rfl
  have pz10 : pauliZ 1 0 = 0 := rfl
  have pz11 : pauliZ 1 1 = -1 := rfl
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, px00, px01, px10, px11, py00, py01, py10, py11,
      pz00, pz01, pz10, pz11, Complex.I_mul_I, Complex.I_sq]
  all_goals try ring_nf
  all_goals try simp only [Complex.I_sq, Complex.I_mul_I]
  all_goals ring

theorem clause4_conj2 (ρ : Operator 2) :
    FamilyTwirl pauliFourFamily ρ = (Matrix.trace ρ * (2 : ℂ)⁻¹) • 1 := by
  rw [familyTwirl_apply pauliFourFamily ρ, pauli_family_conj_sum]
  show ((Fintype.card (Fin 4) : ℂ)⁻¹) • (((2 : ℂ) * Matrix.trace ρ) • 1)
    = (Matrix.trace ρ * (2 : ℂ)⁻¹) • 1
  rw [Fintype.card_fin, smul_smul]
  apply congrArg (fun z : ℂ => z • (1 : Operator 2))
  field_simp; ring

theorem clause4_conj5 {J : Type} [Fintype J] (prob : J → ℝ) (Uf : J → Operator 2) :
    ¬ QubitSecondMomentUnboundaried prob Uf :=
  qubit_real_second_moment_impossible prob Uf

theorem clause4_conj4 : ∃ f : Fin 24 → Operator 2, QubitTwoDesignMoments f := by
  obtain ⟨f, hu, h1, h2⟩ := qubit_conjugation_two_design_exists
  refine ⟨f, ?_, h1, h2⟩
  intro i
  have ha := Matrix.mem_unitaryGroup_iff.mp (hu i)
  have hb := Matrix.mem_unitaryGroup_iff'.mp (hu i)
  rw [Matrix.star_eq_conjTranspose] at ha hb
  exact ⟨hb, ha⟩

theorem clause4_conj1 (D : ℕ) (G : Type) (hG : Fintype G) (hGg : Group G) (U : G → Operator D)
    (hU : IsUnitaryRep U) :
    CompletelyPositive (FamilyTwirl U) ∧ TracePreserving (FamilyTwirl U) ∧
      (∀ ρ : Operator D, FamilyTwirl U (FamilyTwirl U ρ) = FamilyTwirl U ρ) ∧
      (∀ (g : G) (ρ : Operator D),
        FamilyTwirl U (U g * ρ * (U g).conjTranspose) = FamilyTwirl U ρ) := by
  letI := hG
  letI := hGg
  exact ⟨familyTwirl_completelyPositive U, familyTwirl_tracePreserving hU,
    familyTwirl_idempotent hU, familyTwirl_conj_invariant hU⟩

attribute [local instance] operatorMeasurableSpace

theorem measurable_operator_entry {D : ℕ} (i j : Fin D) :
    Measurable (fun A : Operator D => A i j) := by
  fun_prop

theorem measurable_matrix_iff {D E : ℕ} {f : Operator D → Operator E} :
    Measurable f ↔ ∀ i j : Fin E, Measurable (fun A : Operator D => f A i j) := by
  show @Measurable (Operator D) ((Fin E) → (Fin E) → ℂ) operatorMeasurableSpace
        (@MeasurableSpace.pi (Fin E) (fun _ => (Fin E) → ℂ)
          (fun _ => @MeasurableSpace.pi (Fin E) (fun _ => ℂ) (fun _ => Complex.measurableSpace)))
        (fun A => (f A : Matrix (Fin E) (Fin E) ℂ))
    ↔ ∀ i j : Fin E, @Measurable (Operator D) ℂ operatorMeasurableSpace Complex.measurableSpace
        (fun A => f A i j)
  constructor
  · intro h i
    rw [measurable_pi_iff] at h
    have hi := h i
    rw [measurable_pi_iff] at hi
    intro j
    exact hi j
  · intro h
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    exact h i j

theorem measurable_operator_mul_left {D : ℕ} (W : Operator D) :
    Measurable (fun A : Operator D => W * A) := by
  rw [measurable_matrix_iff]
  intro i j
  have h : (fun A : Operator D => (W * A) i j) = fun A => ∑ k, W i k * A k j := by
    funext A
    rw [Matrix.mul_apply]
  rw [h]
  fun_prop

theorem measurable_operator_mul_right {D : ℕ} (W : Operator D) :
    Measurable (fun A : Operator D => A * W) := by
  rw [measurable_matrix_iff]
  intro i j
  have h : (fun A : Operator D => (A * W) i j) = fun A => ∑ k, A i k * W k j := by
    funext A
    rw [Matrix.mul_apply]
  rw [h]
  fun_prop

theorem measurable_conjEntry {D : ℕ} (ρ : Operator D) (i j : Fin D) :
    Measurable (fun A : Operator D => (A * ρ * A.conjTranspose) i j) := by
  have h : (fun A : Operator D => (A * ρ * A.conjTranspose) i j)
      = fun A => ∑ k : Fin D, ∑ l : Fin D, A i l * ρ l k * star (A j k) := by
    funext A
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [h]
  fun_prop

theorem mul_conj_conj_assoc {D : ℕ} (A W ρ : Operator D) :
    A * (W * ρ * W.conjTranspose) * A.conjTranspose
      = (A * W) * ρ * (A * W).conjTranspose := by
  rw [Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

theorem haar_ae_unitary {D : ℕ} (H : HaarUnitaryMeasure D) :
    ∀ᵐ A ∂H.μ, IsUnitaryMatrix A := by
  rw [MeasureTheory.ae_iff]
  exact H.supportedOnUnitary

theorem haar_prob_real_univ {D : ℕ} (H : HaarUnitaryMeasure D) :
    (H.μ).real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real_def, H.isProb.measure_univ]
  simp

theorem unitary_entry_norm_le_one {D : ℕ} {V : Operator D} (hV : IsUnitaryMatrix V)
    (p q : Fin D) : ‖V p q‖ ≤ 1 := by
  have hform : (V.conjTranspose * V) q q = ∑ p : Fin D, star (V p q) * V p q := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.conjTranspose_apply V p q]
  have hdiag : ∑ p : Fin D, star (V p q) * V p q = 1 := by
    have h : (V.conjTranspose * V) q q = (1 : Operator D) q q := by rw [hV.1]
    rw [hform] at h
    have hone : ((1 : Operator D) q q : ℂ) = 1 := by
      simp [Matrix.one_apply]
    rw [hone] at h
    exact h
  have hconj : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    have h1 : star z * z = ((Complex.normSq z : ℝ) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self).symm
    have h2 : ((Complex.normSq z : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm]
    rw [h1, h2]
  have hre : (∑ i : Fin D, ‖V i q‖ ^ 2) = 1 := by
    have h := congrArg Complex.re hdiag
    simp only [Complex.re_sum, hconj, Complex.ofReal_re] at h
    exact h
  have hle : ‖V p q‖ ^ 2 ≤ 1 := by
    have hsingle : ‖V p q‖ ^ 2 ≤ ∑ i : Fin D, ‖V i q‖ ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (‖V i q‖)) (Finset.mem_univ p)
    rw [hre] at hsingle
    exact hsingle
  have h0 : 0 ≤ ‖V p q‖ := norm_nonneg _
  have hsqrt : ‖V p q‖ ≤ Real.sqrt 1 := (Real.le_sqrt h0 (by norm_num)).mpr hle
  rwa [Real.sqrt_one] at hsqrt

theorem haar_conjEntry_integrable {D : ℕ} (H : HaarUnitaryMeasure D) (ρ : Operator D)
    (i j : Fin D) : MeasureTheory.Integrable
      (fun B : Operator D => (B * ρ * B.conjTranspose) i j) H.μ := by
  haveI : MeasureTheory.IsProbabilityMeasure H.μ := H.isProb
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun B : Operator D => (B * ρ * B.conjTranspose) i j) H.μ :=
    (measurable_conjEntry ρ i j).stronglyMeasurable.aestronglyMeasurable
  refine MeasureTheory.Integrable.of_bound hmeas (∑ a : Fin D, ∑ b : Fin D, ‖ρ a b‖) ?_
  filter_upwards [haar_ae_unitary H] with B hB
  have hform : (B * ρ * B.conjTranspose) i j
      = ∑ k : Fin D, ∑ m : Fin D, B i m * ρ m k * star (B j k) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [hform]
  calc ‖∑ k : Fin D, ∑ m : Fin D, B i m * ρ m k * star (B j k)‖
      ≤ ∑ k : Fin D, ‖∑ m : Fin D, B i m * ρ m k * star (B j k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin D, ∑ m : Fin D, ‖B i m * ρ m k * star (B j k)‖ :=
        Finset.sum_le_sum fun k _ => norm_sum_le _ _
    _ ≤ ∑ k : Fin D, ∑ m : Fin D, ‖ρ m k‖ := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul, norm_mul, norm_star]
        have h1 : ‖B i m‖ ≤ 1 := unitary_entry_norm_le_one hB i m
        have h2 : ‖B j k‖ ≤ 1 := unitary_entry_norm_le_one hB j k
        have hz : 0 ≤ ‖ρ m k‖ := norm_nonneg _
        have h3 : ‖B i m‖ * ‖ρ m k‖ ≤ ‖ρ m k‖ := by nlinarith [h1, hz]
        calc ‖B i m‖ * ‖ρ m k‖ * ‖B j k‖
            ≤ ‖ρ m k‖ * ‖B j k‖ := by gcongr
          _ ≤ ‖ρ m k‖ * 1 := by gcongr
          _ = ‖ρ m k‖ := by ring
    _ = ∑ a : Fin D, ∑ b : Fin D, ‖ρ a b‖ := Finset.sum_comm

theorem haarTwirl_conj_invariant {D : ℕ} (H : HaarUnitaryMeasure D)
    (W ρ : Operator D) (hW : IsUnitaryMatrix W) :
    HaarTwirl H (W * ρ * W.conjTranspose) = HaarTwirl H ρ := by
  ext i j
  show MeasureTheory.integral H.μ
        (fun A : Operator D => (A * (W * ρ * W.conjTranspose) * A.conjTranspose) i j)
    = MeasureTheory.integral H.μ (fun A : Operator D => (A * ρ * A.conjTranspose) i j)
  have hA : (fun A : Operator D => (A * (W * ρ * W.conjTranspose) * A.conjTranspose) i j)
      = fun A => ((A * W) * ρ * (A * W).conjTranspose) i j :=
    funext fun A => congrArg (fun M : Operator D => M i j) (mul_conj_conj_assoc A W ρ)
  rw [hA]
  have hmap : MeasureTheory.Measure.map (fun A : Operator D => A * W) H.μ = H.μ :=
    H.rightInvariant W hW
  conv_rhs => rw [← hmap]
  exact (MeasureTheory.integral_map_of_stronglyMeasurable
    (measurable_operator_mul_right W)
    (Measurable.stronglyMeasurable (measurable_conjEntry ρ i j))).symm

theorem haarTwirl_unitary_conj_fixed {D : ℕ} (H : HaarUnitaryMeasure D)
    (A ρ : Operator D) (hA : IsUnitaryMatrix A) :
    A * HaarTwirl H ρ * A.conjTranspose = HaarTwirl H ρ := by
  ext i j
  have hL : (A * HaarTwirl H ρ * A.conjTranspose) i j
      = ∑ k : Fin D, ∑ m : Fin D, A i m * (HaarTwirl H ρ m k) * star (A j k) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [hL]
  have hpull : ∀ (m k : Fin D),
      A i m * (HaarTwirl H ρ m k) * star (A j k)
        = MeasureTheory.integral H.μ
            (fun B : Operator D => A i m * (B * ρ * B.conjTranspose) m k * star (A j k)) := by
    intro m k
    show A i m *
        (MeasureTheory.integral H.μ (fun B : Operator D => (B * ρ * B.conjTranspose) m k)) *
        star (A j k) = _
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
  simp only [hpull]
  have hprod : (∑ k : Fin D, ∑ m : Fin D,
        MeasureTheory.integral H.μ
          (fun B : Operator D => A i m * (B * ρ * B.conjTranspose) m k * star (A j k)))
      = ∑ x : Fin D × Fin D,
        MeasureTheory.integral H.μ
          (fun B : Operator D => A i x.2 * (B * ρ * B.conjTranspose) x.2 x.1 * star (A j x.1)) :=
    (Fintype.sum_prod_type (fun x : Fin D × Fin D => MeasureTheory.integral H.μ
      (fun B : Operator D => A i x.2 * (B * ρ * B.conjTranspose) x.2 x.1 * star (A j x.1)))).symm
  rw [hprod]
  have hswap : (∑ x : Fin D × Fin D,
        MeasureTheory.integral H.μ
          (fun B : Operator D => A i x.2 * (B * ρ * B.conjTranspose) x.2 x.1 * star (A j x.1)))
      = MeasureTheory.integral H.μ
          (fun B : Operator D => ∑ x : Fin D × Fin D,
            A i x.2 * (B * ρ * B.conjTranspose) x.2 x.1 * star (A j x.1)) :=
    (MeasureTheory.integral_finsetSum Finset.univ fun x _ =>
      ((haar_conjEntry_integrable H ρ x.2 x.1).const_mul _).mul_const _).symm
  rw [hswap]
  have hbody : (fun B : Operator D =>
        ∑ x : Fin D × Fin D, A i x.2 * (B * ρ * B.conjTranspose) x.2 x.1 * star (A j x.1))
      = fun B : Operator D => (A * (B * ρ * B.conjTranspose) * A.conjTranspose) i j := by
    funext B
    conv_lhs => rw [Fintype.sum_prod_type]
    symm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [hbody]
  have hmul : (fun B : Operator D => (A * (B * ρ * B.conjTranspose) * A.conjTranspose) i j)
      = fun B : Operator D => ((A * B) * ρ * (A * B).conjTranspose) i j :=
    funext fun B => congrArg (fun M : Operator D => M i j) (mul_conj_conj_assoc A B ρ)
  rw [hmul]
  show MeasureTheory.integral H.μ
      (fun B : Operator D => ((A * B) * ρ * (A * B).conjTranspose) i j)
    = MeasureTheory.integral H.μ (fun B : Operator D => (B * ρ * B.conjTranspose) i j)
  have hmap : MeasureTheory.Measure.map (fun B : Operator D => A * B) H.μ = H.μ :=
    H.leftInvariant A hA
  conv_rhs => rw [← hmap]
  exact (MeasureTheory.integral_map_of_stronglyMeasurable
    (measurable_operator_mul_left A)
    (Measurable.stronglyMeasurable (measurable_conjEntry ρ i j))).symm

theorem haar_projection_formula {D : ℕ} (H : HaarUnitaryMeasure D) :
    HaarProjectionFormula H := by
  intro ρ i j
  have hcongr : (fun A : Operator D => HaarTwirl H (A * ρ * A.conjTranspose) i j)
      =ᵐ[H.μ] fun A : Operator D => (HaarTwirl H ρ) i j := by
    filter_upwards [haar_ae_unitary H] with A hA
    exact congrArg (fun M : Operator D => M i j) (haarTwirl_conj_invariant H A ρ hA)
  have hkey : MeasureTheory.integral H.μ
      (fun A : Operator D => HaarTwirl H (A * ρ * A.conjTranspose) i j)
      = (HaarTwirl H ρ) i j := by
    have h1 : MeasureTheory.integral H.μ
        (fun A : Operator D => HaarTwirl H (A * ρ * A.conjTranspose) i j)
        = MeasureTheory.integral H.μ (fun _ : Operator D => (HaarTwirl H ρ) i j) :=
      MeasureTheory.integral_congr_ae hcongr
    rw [h1]
    change MeasureTheory.integral H.μ (fun _ : Operator D => (HaarTwirl H ρ) i j)
      = (HaarTwirl H ρ) i j
    rw [MeasureTheory.integral_const]
    change (H.μ).real Set.univ • (HaarTwirl H ρ) i j = (HaarTwirl H ρ) i j
    rw [haar_prob_real_univ H]
    change (1 : ℝ) • (HaarTwirl H ρ) i j = (HaarTwirl H ρ) i j
    rw [one_smul]
  exact hkey.symm

theorem haarTwirl_idempotent {D : ℕ} (H : HaarUnitaryMeasure D) (ρ : Operator D) :
    HaarTwirl H (HaarTwirl H ρ) = HaarTwirl H ρ := by
  ext i j
  have hcongr : (fun A : Operator D => (A * HaarTwirl H ρ * A.conjTranspose) i j)
      =ᵐ[H.μ] fun A : Operator D => (HaarTwirl H ρ) i j := by
    filter_upwards [haar_ae_unitary H] with A hA
    exact congrArg (fun M : Operator D => M i j) (haarTwirl_unitary_conj_fixed H A ρ hA)
  show MeasureTheory.integral H.μ
      (fun A : Operator D => (A * HaarTwirl H ρ * A.conjTranspose) i j)
    = MeasureTheory.integral H.μ (fun A : Operator D => (A * ρ * A.conjTranspose) i j)
  simp only [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const,
    haar_prob_real_univ H, one_smul]
  rfl

theorem haarTwirl_tracePreserving {D : ℕ} (H : HaarUnitaryMeasure D) (ρ : Operator D) :
    Matrix.trace (HaarTwirl H ρ) = Matrix.trace ρ := by
  have htr : ∀ᵐ A ∂H.μ, Matrix.trace (A * ρ * A.conjTranspose) = Matrix.trace ρ := by
    filter_upwards [haar_ae_unitary H] with A hA
    exact trace_conj_unitary hA ρ
  have hsum : (∑ i : Fin D, MeasureTheory.integral H.μ
        (fun A : Operator D => (A * ρ * A.conjTranspose) i i))
      = MeasureTheory.integral H.μ
          (fun A : Operator D => ∑ i : Fin D, (A * ρ * A.conjTranspose) i i) :=
    (MeasureTheory.integral_finsetSum Finset.univ
      fun i _ => haar_conjEntry_integrable H ρ i i).symm
  calc Matrix.trace (HaarTwirl H ρ)
      = ∑ i : Fin D, HaarTwirl H ρ i i := rfl
    _ = ∑ i : Fin D, MeasureTheory.integral H.μ
          (fun A : Operator D => (A * ρ * A.conjTranspose) i i) := rfl
    _ = MeasureTheory.integral H.μ
          (fun A : Operator D => ∑ i : Fin D, (A * ρ * A.conjTranspose) i i) := hsum
    _ = MeasureTheory.integral H.μ
          (fun A : Operator D => Matrix.trace (A * ρ * A.conjTranspose)) := rfl
    _ = MeasureTheory.integral H.μ (fun _ : Operator D => Matrix.trace ρ) :=
        MeasureTheory.integral_congr_ae htr
    _ = Matrix.trace ρ := by
        simp only [MeasureTheory.integral_const, haar_prob_real_univ H, one_smul]

theorem channelAmplificationFn_haarTwirl {D r : ℕ} (H : HaarUnitaryMeasure D)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) (x y : Fin r × Fin D) :
    ChannelAmplificationFn (HaarTwirl H) r A x y
      = MeasureTheory.integral H.μ
          (fun M : Operator D => ChannelAmplification (conjBranch M) r A x y) := by
  rfl

theorem channelAmplification_conjEntry_integrable {D r : ℕ} (H : HaarUnitaryMeasure D)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) (u v : Fin r × Fin D) :
    MeasureTheory.Integrable
      (fun M : Operator D => ChannelAmplification (conjBranch M) r A u v) H.μ := by
  haveI : MeasureTheory.IsProbabilityMeasure H.μ := H.isProb
  exact haar_conjEntry_integrable H (fun i j => A (u.1, i) (v.1, j)) u.2 v.2

theorem haarTwirl_amplification_posSemidef {D r : ℕ} (H : HaarUnitaryMeasure D)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) (hA : A.PosSemidef) :
    (ChannelAmplificationFn (HaarTwirl H) r A).PosSemidef := by
  haveI : MeasureTheory.IsProbabilityMeasure H.μ := H.isProb
  have hentry : ∀ u v : Fin r × Fin D,
      (ChannelAmplificationFn (HaarTwirl H) r A) u v
        = MeasureTheory.integral H.μ
            (fun M : Operator D => ChannelAmplification (conjBranch M) r A u v) :=
    fun u v => channelAmplificationFn_haarTwirl H A u v
  have hherm : ∀ (M : Operator D) (u v : Fin r × Fin D),
      ChannelAmplification (conjBranch M) r A u v
        = star (ChannelAmplification (conjBranch M) r A v u) := by
    intro M u v
    have h : (ChannelAmplification (conjBranch M) r A).conjTranspose
        = ChannelAmplification (conjBranch M) r A :=
      (completelyPositive_conjBranch M r A hA).1
    have h2 := congrFun (congrFun h u) v
    rw [Matrix.conjTranspose_apply] at h2
    exact h2.symm
  refine ⟨?_, ?_⟩
  · ext u v
    show (ChannelAmplificationFn (HaarTwirl H) r A).conjTranspose u v
      = (ChannelAmplificationFn (HaarTwirl H) r A) u v
    rw [Matrix.conjTranspose_apply, hentry u v, hentry v u]
    have hconj : star (MeasureTheory.integral H.μ
        (fun M : Operator D => ChannelAmplification (conjBranch M) r A v u))
        = MeasureTheory.integral H.μ
          (fun M : Operator D => star (ChannelAmplification (conjBranch M) r A v u)) :=
      (integral_conj (f := fun M : Operator D =>
        ChannelAmplification (conjBranch M) r A v u) (μ := H.μ)).symm
    rw [hconj]
    exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all H.μ fun M => (hherm M u v).symm)
  · intro x
    have hpull : ∀ u v : Fin r × Fin D,
        star (x u) * (MeasureTheory.integral H.μ
            (fun M : Operator D => ChannelAmplification (conjBranch M) r A u v)) * x v
          = MeasureTheory.integral H.μ (fun M : Operator D =>
              star (x u) * ChannelAmplification (conjBranch M) r A u v * x v) := by
      intro u v
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    have hint : ∀ u v : Fin r × Fin D, MeasureTheory.Integrable
        (fun M : Operator D =>
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v) H.μ := by
      intro u v
      exact ((channelAmplification_conjEntry_integrable H A u v).const_mul _).mul_const _
    have hq : (x.sum fun u xu => x.sum fun v xv =>
          star xu * (ChannelAmplificationFn (HaarTwirl H) r A) u v * xv)
        = MeasureTheory.integral H.μ (fun M : Operator D =>
          x.sum fun u xu => x.sum fun v xv =>
            star xu * ChannelAmplification (conjBranch M) r A u v * xv) := by
      show (∑ u ∈ x.support, ∑ v ∈ x.support,
            star (x u) * (ChannelAmplificationFn (HaarTwirl H) r A) u v * x v)
          = MeasureTheory.integral H.μ (fun M : Operator D =>
            ∑ u ∈ x.support, ∑ v ∈ x.support,
              star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)
      simp only [hentry, hpull]
      have hinner : ∀ u ∈ x.support,
          (∑ v ∈ x.support, MeasureTheory.integral H.μ (fun M : Operator D =>
            star (x u) * ChannelAmplification (conjBranch M) r A u v * x v))
          = MeasureTheory.integral H.μ (fun M : Operator D =>
            ∑ v ∈ x.support,
              star (x u) * ChannelAmplification (conjBranch M) r A u v * x v) := by
        intro u hu
        exact (MeasureTheory.integral_finsetSum x.support fun v _ => hint u v).symm
      have hstep : (∑ u ∈ x.support, ∑ v ∈ x.support,
            MeasureTheory.integral H.μ (fun M : Operator D =>
              star (x u) * ChannelAmplification (conjBranch M) r A u v * x v))
          = ∑ u ∈ x.support, MeasureTheory.integral H.μ (fun M : Operator D =>
            ∑ v ∈ x.support,
              star (x u) * ChannelAmplification (conjBranch M) r A u v * x v) :=
        Finset.sum_congr rfl fun u hu => hinner u hu
      rw [hstep]
      exact (MeasureTheory.integral_finsetSum x.support fun u _ =>
        MeasureTheory.integrable_finsetSum x.support fun v _ => hint u v).symm
    rw [hq]
    show 0 ≤ MeasureTheory.integral H.μ (fun M : Operator D =>
      ∑ u ∈ x.support, ∑ v ∈ x.support,
        star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)
    have hqM : ∀ M : Operator D,
        0 ≤ ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v := by
      intro M
      exact (completelyPositive_conjBranch M r A hA).2 x
    have hintQ : MeasureTheory.Integrable (fun M : Operator D =>
        ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v) H.μ :=
      MeasureTheory.integrable_finsetSum x.support fun u _ =>
        MeasureTheory.integrable_finsetSum x.support fun v _ => hint u v
    have hreE : (MeasureTheory.integral H.μ (fun M : Operator D =>
        ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)).re
        = MeasureTheory.integral H.μ (fun M : Operator D =>
          (∑ u ∈ x.support, ∑ v ∈ x.support,
            star (x u) * ChannelAmplification (conjBranch M) r A u v * x v).re) :=
      (integral_re hintQ).symm
    have himE : (MeasureTheory.integral H.μ (fun M : Operator D =>
        ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)).im
        = MeasureTheory.integral H.μ (fun M : Operator D =>
          (∑ u ∈ x.support, ∑ v ∈ x.support,
            star (x u) * ChannelAmplification (conjBranch M) r A u v * x v).im) :=
      (integral_im hintQ).symm
    have hre : 0 ≤ (MeasureTheory.integral H.μ (fun M : Operator D =>
        ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)).re := by
      rw [hreE]
      exact MeasureTheory.integral_nonneg fun M =>
        (RCLike.nonneg_iff.mp (hqM M)).1
    have him : (MeasureTheory.integral H.μ (fun M : Operator D =>
        ∑ u ∈ x.support, ∑ v ∈ x.support,
          star (x u) * ChannelAmplification (conjBranch M) r A u v * x v)).im = 0 := by
      rw [himE]
      have hz : (fun M : Operator D =>
          (∑ u ∈ x.support, ∑ v ∈ x.support,
            star (x u) * ChannelAmplification (conjBranch M) r A u v * x v).im)
          = fun _ : Operator D => (0 : ℝ) := by
        funext M
        exact (RCLike.nonneg_iff.mp (hqM M)).2
      rw [hz, MeasureTheory.integral_zero]
    exact RCLike.nonneg_iff.mpr ⟨hre, him⟩

theorem clause4_conj3 (D : ℕ) (H : HaarUnitaryMeasure D) :
    CPTPFunction (HaarTwirl H) ∧
      (∀ ρ : Operator D, HaarTwirl H (HaarTwirl H ρ) = HaarTwirl H ρ) ∧
      (∀ (W ρ : Operator D), IsUnitaryMatrix W →
        HaarTwirl H (W * ρ * W.conjTranspose) = HaarTwirl H ρ) ∧
      HaarProjectionFormula H :=
  ⟨⟨fun r A hA => haarTwirl_amplification_posSemidef H A hA, haarTwirl_tracePreserving H⟩,
    haarTwirl_idempotent H, haarTwirl_conj_invariant H, haar_projection_formula H⟩

theorem g4 :
    (∀ (D : ℕ) (G : Type) (_ : Fintype G) (_ : Group G) (U : G → Operator D),
      IsUnitaryRep U →
      CompletelyPositive (FamilyTwirl U) ∧ TracePreserving (FamilyTwirl U) ∧
      (∀ ρ : Operator D, FamilyTwirl U (FamilyTwirl U ρ) = FamilyTwirl U ρ) ∧
      (∀ (g : G) (ρ : Operator D),
        FamilyTwirl U (U g * ρ * (U g).conjTranspose) = FamilyTwirl U ρ)) ∧
    (∀ ρ : Operator 2, FamilyTwirl pauliFourFamily ρ = (Matrix.trace ρ * (2 : ℂ)⁻¹) • 1) ∧
    (∀ (D : ℕ) (H : HaarUnitaryMeasure D),
      CPTPFunction (HaarTwirl H) ∧
      (∀ ρ : Operator D, HaarTwirl H (HaarTwirl H ρ) = HaarTwirl H ρ) ∧
      (∀ (W ρ : Operator D), IsUnitaryMatrix W →
        HaarTwirl H (W * ρ * W.conjTranspose) = HaarTwirl H ρ) ∧
      HaarProjectionFormula H) ∧
    (∃ f : Fin 24 → Operator 2, QubitTwoDesignMoments f) ∧
    (∀ (J : Type) (_ : Fintype J) (prob : J → ℝ) (Uf : J → Operator 2),
      ¬ QubitSecondMomentUnboundaried prob Uf) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D G _ _ U hU
    exact clause4_conj1 D G _ _ U hU
  · intro ρ
    exact clause4_conj2 ρ
  · intro D H
    exact clause4_conj3 D H
  · exact clause4_conj4
  · intro J _ prob Uf
    exact clause4_conj5 prob Uf
end Qatlib.Concepts.ChannelTheory.TwirlChannel
