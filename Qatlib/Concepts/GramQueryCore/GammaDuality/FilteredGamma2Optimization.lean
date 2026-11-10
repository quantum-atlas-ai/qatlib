/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2FiniteSDP
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.GramQueryCore.GammaDuality
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators

noncomputable def filteredGamma2DualValue {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) : ℝ≥0∞ :=
  ⨆ M : {M : Matrix X X ℂ // ∀ j, ‖Z j ⊙ M‖ ≤ 1}, ENNReal.ofReal ‖A ⊙ M.1‖

noncomputable def generalAdversaryValue {X E : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (input : X → Fin n → Bool) (f : X → E) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      (∀ x y, f x = f y → Γ x y = 0) ∧
      ∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1}, ENNReal.ofReal ‖Γ.1‖

theorem filteredGamma2DualValue_le {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) :
    filteredGamma2DualValue A Z ≤ filteredGamma2 A Z := by
  unfold filteredGamma2DualValue
  exact iSup_le fun M => filteredGamma2_dual_ge A Z M.1 M.2

theorem generalAdversaryValue_le_queryDelta {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    generalAdversaryValue input f ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) := by
  unfold generalAdversaryValue
  exact iSup_le fun Γ => adversary_le_filteredGamma2_queryDelta input f Γ.1 Γ.2.2.1 Γ.2.2.2

theorem generalAdversary_filter_bound {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (input : X → Fin n → Bool) (Γ : Matrix X X ℂ)
    (hΓ : ∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) : advFilterBound input Γ ≤ 1 := by
  have he (j : Fin n) : advFilter input Γ j = gramFilterDelta input j ⊙ Γ := by
    ext x y
    by_cases h : input x j = input y j <;>
      simp [advFilter, gramFilterDelta, Matrix.hadamard_apply, h]
  have hf : ∀ (l : List ℝ), (∀ a ∈ l, a ≤ 1) → ∀ b, b ≤ 1 → l.foldl max b ≤ 1 := by
    intro l
    induction l with
    | nil => intro _ b hb; exact hb
    | cons a l ih =>
      intro ha b hb
      exact ih (fun c hc => ha c (List.mem_cons_of_mem a hc)) (max b a)
        (max_le hb (ha a (List.mem_cons_self)))
  apply hf
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    rw [he]
    exact hΓ j
  · norm_num

theorem filteredGamma2_budget_boundary :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ)
      (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (W : ℝ), 0 ≤ W →
      (filteredGamma2 A Z ≤ ENNReal.ofReal W ↔ gramFilteredCert A Z W) :=
  filteredGamma2_fixed_budget_boundary

section DualAttainment
variable {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}

theorem gamma2_operator_entry_bound (M : Matrix X X ℂ) (x y : X) : ‖M x y‖ ≤ ‖M‖ := by
  classical
  have hk : M *ᵥ Ket y = fun z => M z y := by
    funext z
    simp [Matrix.mulVec, dotProduct, Ket]
  have hn := l2_norm_mulVec_fromVec_le M (Ket y)
  have hkn : ‖toEuclidean_fromVec (Ket y)‖ = 1 := by
    have hs := norm_toEuclidean_fromVec_sq (Ket y)
    rw [normalized_ket y] at hs
    nlinarith [norm_nonneg (toEuclidean_fromVec (Ket y))]
  rw [hkn, mul_one, hk] at hn
  have hx : ‖M x y‖ ^ 2 ≤ ‖toEuclidean_fromVec (fun z => M z y)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    exact Finset.single_le_sum (f := fun z : X => ‖M z y‖ ^ 2)
      (fun z _ => sq_nonneg _) (Finset.mem_univ x)
  nlinarith [norm_nonneg (M x y), norm_nonneg M,
    norm_nonneg (toEuclidean_fromVec (fun z => M z y))]

theorem gamma2_finite_support (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hf : filteredGamma2 A Z < ⊤) :
    ∀ x y, (∀ j, Z j x y = 0) → A x y = 0 := by
  have hc := (filteredGamma2_budget_boundary X n A Z (filteredGamma2 A Z).toReal
    ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hf.ne])
  obtain ⟨Q, hQ, u, v, _, _, he⟩ := hc
  intro x y hz
  rw [he]
  simp [hz]

theorem filteredGamma2DualValue_attained (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hf : filteredGamma2 A Z < ⊤) :
    ∃ M : Matrix X X ℂ, (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧
      filteredGamma2DualValue A Z = ENNReal.ofReal ‖A ⊙ M‖ := by
  classical
  let zeroAt (x y : X) : Prop := ∀ j, Z j x y = 0
  let project (M : Matrix X X ℂ) : Matrix X X ℂ :=
    fun x y => if zeroAt x y then 0 else M x y
  have hproject (B : Matrix X X ℂ) (hB : ∀ x y, zeroAt x y → B x y = 0)
      (M : Matrix X X ℂ) : B ⊙ project M = B ⊙ M := by
    ext x y
    by_cases hz : zeroAt x y
    · simp [project, Matrix.hadamard_apply, hz, hB x y hz]
    · simp [project, Matrix.hadamard_apply, hz]
  have hZ (j : Fin n) (M : Matrix X X ℂ) : Z j ⊙ project M = Z j ⊙ M :=
    hproject (Z j) (fun _ _ hz => hz j) M
  have hA (M : Matrix X X ℂ) : A ⊙ project M = A ⊙ M :=
    hproject A (gamma2_finite_support A Z hf) M
  let K : Set (Matrix X X ℂ) :=
    {M | (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ ∀ x y, zeroAt x y → M x y = 0}
  have hm (B : Matrix X X ℂ) : Continuous (fun M : Matrix X X ℂ => B ⊙ M) := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    simp only [Matrix.hadamard_apply]
    fun_prop
  have hKc : IsClosed K := by
    apply IsClosed.inter
    · have hj (j : Fin n) : IsClosed {M : Matrix X X ℂ | ‖Z j ⊙ M‖ ≤ 1} :=
        isClosed_le (continuous_norm.comp (hm (Z j))) continuous_const
      convert! isClosed_iInter hj using 1
      ext M
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    · have ht (x y : X) : IsClosed {M : Matrix X X ℂ | zeroAt x y → M x y = 0} := by
        by_cases hz : zeroAt x y
        · simpa only [hz, forall_const] using!
            (isClosed_eq (show Continuous (fun M : Matrix X X ℂ => M x y) by fun_prop)
              continuous_const)
        · simp only [hz, IsEmpty.forall_iff, Set.setOf_true, isClosed_univ]
      convert! isClosed_iInter (fun x => isClosed_iInter (ht x)) using 1
      ext M
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
  let R : ℝ := ∑ x, ∑ y, ∑ j, ‖Z j x y‖⁻¹
  have hnn (x y : X) (j : Fin n) : 0 ≤ ‖Z j x y‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hR : 0 ≤ R := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun j _ => hnn x y j
  have hb (M : Matrix X X ℂ) (hM : M ∈ K) (x y : X) : ‖M x y‖ ≤ R := by
    by_cases hz : zeroAt x y
    · rw [hM.2 x y hz, norm_zero]; exact hR
    · have hex : ∃ j, Z j x y ≠ 0 := by simpa [zeroAt, not_forall] using! hz
      obtain ⟨j, hj⟩ := hex
      have hn := (gamma2_operator_entry_bound (Z j ⊙ M) x y).trans (hM.1 j)
      rw [Matrix.hadamard_apply, norm_mul] at hn
      have hp : 0 < ‖Z j x y‖ := norm_pos_iff.mpr hj
      have he : ‖M x y‖ ≤ ‖Z j x y‖⁻¹ := by
        calc
          _ = (‖Z j x y‖ * ‖M x y‖) / ‖Z j x y‖ := by field_simp
          _ ≤ 1 / ‖Z j x y‖ := div_le_div_of_nonneg_right hn hp.le
          _ = _ := one_div _
      have hjb : ‖Z j x y‖⁻¹ ≤ ∑ j', ‖Z j' x y‖⁻¹ :=
        Finset.single_le_sum (fun j' _ => hnn x y j') (Finset.mem_univ j)
      have hyb : (∑ j', ‖Z j' x y‖⁻¹) ≤ ∑ y', ∑ j', ‖Z j' x y'‖⁻¹ :=
        Finset.single_le_sum (f := fun y' : X => ∑ j' : Fin n, ‖Z j' x y'‖⁻¹)
          (fun y' _ => Finset.sum_nonneg fun j' _ => hnn x y' j') (Finset.mem_univ y)
      have hxb : (∑ y', ∑ j', ‖Z j' x y'‖⁻¹) ≤ R :=
        Finset.single_le_sum (f := fun x' : X => ∑ y' : X, ∑ j' : Fin n, ‖Z j' x' y'‖⁻¹)
          (fun x' _ => Finset.sum_nonneg fun y' _ => Finset.sum_nonneg
            fun j' _ => hnn x' y' j') (Finset.mem_univ x)
      exact he.trans (hjb.trans (hyb.trans hxb))
  let B : Set (Matrix X X ℂ) := Set.pi Set.univ
    (fun _ : X => Set.pi Set.univ (fun _ : X => Metric.closedBall (0 : ℂ) R))
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi
    fun _ => isCompact_closedBall 0 R
  have hKk : IsCompact K := hBc.of_isClosed_subset hKc (by
    intro M hM
    change ∀ x ∈ Set.univ, ∀ y ∈ Set.univ, M x y ∈ Metric.closedBall (0 : ℂ) R
    intro x _ y _
    simpa only [Metric.mem_closedBall, dist_zero_right] using! hb M hM x y)
  have h0 : (0 : Matrix X X ℂ) ∈ K := by simp [K]
  obtain ⟨M, hM, hmax⟩ := hKk.exists_isMaxOn ⟨0, h0⟩ (continuous_norm.comp (hm A)).continuousOn
  refine ⟨M, hM.1, le_antisymm ?_ ?_⟩
  · unfold filteredGamma2DualValue
    apply iSup_le
    intro N
    have hN : project N.1 ∈ K := by
      constructor
      · intro j; rw [hZ]; exact N.2 j
      · intro x y hz; simp [project, hz]
    rw [← hA N.1]
    exact ENNReal.ofReal_le_ofReal (hmax hN)
  · exact le_iSup_of_le ⟨M, hM.1⟩ le_rfl

end DualAttainment

theorem filteredGamma2_unsupported_top {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (x y : X)
    (ha : A x y ≠ 0) (hz : ∀ j, Z j x y = 0) :
    filteredGamma2 A Z = ⊤ ∧ filteredGamma2DualValue A Z = ⊤ := by
  classical
  have hbound (N : ℕ) : (N : ℝ≥0∞) ≤ filteredGamma2DualValue A Z := by
    let M : Matrix X X ℂ := fun p q => if p = x ∧ q = y then (N : ℂ) / A x y else 0
    have hf (j : Fin n) : ‖Z j ⊙ M‖ ≤ 1 := by
      have he : Z j ⊙ M = 0 := by
        ext p q
        by_cases hp : p = x <;> by_cases hq : q = y <;>
          simp [M, Matrix.hadamard_apply, hp, hq, hz]
      rw [he, norm_zero]
      norm_num
    have he : (A ⊙ M) x y = (N : ℂ) := by
      simp [M, Matrix.hadamard_apply, div_eq_mul_inv, ha, mul_comm]
    have hn := gamma2_operator_entry_bound (A ⊙ M) x y
    rw [he] at hn
    have hn' : (N : ℝ) ≤ ‖A ⊙ M‖ := by simpa using! hn
    have hcast : (N : ℝ≥0∞) ≤ ENNReal.ofReal ‖A ⊙ M‖ := by
      simpa only [ENNReal.ofReal_natCast] using! ENNReal.ofReal_le_ofReal hn'
    exact hcast.trans (le_iSup_of_le ⟨M, hf⟩ le_rfl)
  have hd : filteredGamma2DualValue A Z = ⊤ := by
    apply top_le_iff.mp
    rw [← ENNReal.iSup_natCast]
    exact iSup_le hbound
  have hp : filteredGamma2 A Z = ⊤ := by
    apply top_le_iff.mp
    rw [← hd]
    exact filteredGamma2DualValue_le A Z
  exact ⟨hp, hd⟩

theorem generalAdversaryValue_constant {X E : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (input : X → Fin n → Bool) (f : X → E) (hf : ∀ x y, f x = f y) :
    generalAdversaryValue input f = 0 := by
  apply le_antisymm _ bot_le
  unfold generalAdversaryValue
  apply iSup_le
  intro Γ
  have hΓ : Γ.1 = 0 := by ext x y; exact Γ.2.2.1 x y (hf x y)
  simp [hΓ]

theorem generalAdversaryValue_le_relaxed_dual {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    generalAdversaryValue input f ≤ filteredGamma2DualValue (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) := by
  unfold generalAdversaryValue filteredGamma2DualValue
  apply iSup_le
  intro Γ
  have he : gramFunctionEvaluationMatrix f ⊙ Γ.1 = Γ.1 := by
    ext x y
    by_cases h : f x = f y
    · simp [Matrix.hadamard_apply, gramFunctionEvaluationMatrix, h, Γ.2.2.1 x y h]
    · simp [Matrix.hadamard_apply, gramFunctionEvaluationMatrix, h]
  have hz (j : Fin n) :
      (fun x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) ⊙ Γ.1 =
      gramFilterDelta input j ⊙ Γ.1 := by
    ext x y
    by_cases h : f x = f y
    · simp [Matrix.hadamard_apply, gramFunctionEvaluationMatrix, h, Γ.2.2.1 x y h]
    · simp [Matrix.hadamard_apply, gramFunctionEvaluationMatrix, h]
  exact le_iSup_of_le ⟨Γ.1, fun j => by rw [hz]; exact Γ.2.2.2 j⟩ (by rw [he])

theorem generalAdversaryValueComparison_of_identification {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E)
    (he : generalAdversaryValue input f = filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y)) :
    generalAdversaryValue input f ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ∧
    filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ≤
      ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) * generalAdversaryValue input f := by
  refine ⟨generalAdversaryValue_le_queryDelta input f, ?_⟩
  rw [he]
  exact filteredGamma2_queryDelta_le_of_evalRelaxed input f

theorem generalAdversaryValue_collision_top {X E : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (input : X → Fin n → Bool) (f : X → E) (x y : X)
    (hi : ∀ j, input x j = input y j) (hf : f x ≠ f y) :
    generalAdversaryValue input f = ⊤ := by
  classical
  have hxy : x ≠ y := fun h => hf (congrArg f h)
  have hbound (N : ℕ) : (N : ℝ≥0∞) ≤ generalAdversaryValue input f := by
    let Γ : Matrix X X ℂ := fun p q =>
      if (p = x ∧ q = y) ∨ (p = y ∧ q = x) then (N : ℂ) else 0
    have hherm : Γ.IsHermitian := by
      ext p q
      simp only [Matrix.conjTranspose_apply, Γ]
      by_cases hp : p = x <;> by_cases hq : q = y <;>
        by_cases hp' : p = y <;> by_cases hq' : q = x <;>
        simp [hp, hq, hp', hq', hxy, hxy.symm]
    have hzero (p q : X) (he : f p = f q) : Γ p q = 0 := by
      have ha : ¬(p = x ∧ q = y) := by
        rintro ⟨rfl, rfl⟩
        exact hf he
      have hb : ¬(p = y ∧ q = x) := by
        rintro ⟨rfl, rfl⟩
        exact hf he.symm
      simp [Γ, ha, hb]
    have hfilter (j : Fin n) : gramFilterDelta input j ⊙ Γ = 0 := by
      ext p q
      by_cases he : (p = x ∧ q = y) ∨ (p = y ∧ q = x)
      · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [gramFilterDelta, Matrix.hadamard_apply, hi j]
      · simp [Γ, Matrix.hadamard_apply, he]
    have hn := gamma2_operator_entry_bound Γ x y
    have he : Γ x y = (N : ℂ) := by simp [Γ]
    rw [he] at hn
    have hn' : (N : ℝ) ≤ ‖Γ‖ := by simpa using! hn
    have hc : (N : ℝ≥0∞) ≤ ENNReal.ofReal ‖Γ‖ := by
      simpa only [ENNReal.ofReal_natCast] using! ENNReal.ofReal_le_ofReal hn'
    exact hc.trans (le_iSup_of_le ⟨Γ, hherm, hzero, fun j => by
      rw [hfilter, norm_zero]; norm_num⟩ le_rfl)
  apply top_le_iff.mp
  rw [← ENNReal.iSup_natCast]
  exact iSup_le hbound

theorem gamma2_support_finite {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hs : ∀ x y, (∀ j, Z j x y = 0) → A x y = 0) : filteredGamma2 A Z < ⊤ := by
  classical
  let c (j : Fin n) (x y : X) : ℂ :=
    if h : ∃ k, Z k x y ≠ 0 then
      if j = h.choose then A x y / Z j x y else 0
    else 0
  have hc (x y : X) : A x y = ∑ j, Z j x y * c j x y := by
    by_cases h : ∃ k, Z k x y ≠ 0
    · simp only [c, dif_pos h]
      rw [Finset.sum_eq_single h.choose]
      · simp [div_eq_mul_inv, h.choose_spec, mul_left_comm]
      · intro j _ hj; simp [hj]
      · simp
    · have hz : ∀ j, Z j x y = 0 := by simpa using! h
      simp [c, h, hs x y hz]
  let u : Fin n → X → (X × X) → ℂ := fun _ x q => if x = q.1 then 1 else 0
  let v : Fin n → X → (X × X) → ℂ := fun j y q => if y = q.2 then c j q.1 q.2 else 0
  let ru (x : X) : ℝ := ∑ j, ∑ q, Complex.normSq (u j x q)
  let rv (y : X) : ℝ := ∑ j, ∑ q, Complex.normSq (v j y q)
  have hru (x : X) : 0 ≤ ru x := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hrv (y : X) : 0 ≤ rv y := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  let W : ℝ := (∑ x, ru x) + ∑ y, rv y
  have hcert : gramFilteredCert A Z W := by
    refine ⟨X × X, inferInstance, u, v, ?_, ?_, ?_⟩
    · intro x
      change ru x ≤ W
      exact (Finset.single_le_sum (fun z _ => hru z) (Finset.mem_univ x)).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun z _ => hrv z))
    · intro y
      change rv y ≤ W
      exact (Finset.single_le_sum (fun z _ => hrv z) (Finset.mem_univ y)).trans
        (le_add_of_nonneg_left (Finset.sum_nonneg fun z _ => hru z))
    · intro x y
      rw [hc x y]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp [dotProduct, u, v, Fintype.sum_prod_type]
  exact (filteredGamma2_le_of_gramFilteredCert hcert).trans_lt ENNReal.ofReal_lt_top

theorem filteredGamma2_infinite_duality {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hf : filteredGamma2 A Z = ⊤) : filteredGamma2DualValue A Z = ⊤ := by
  classical
  by_contra hd
  have hs : ∀ x y, (∀ j, Z j x y = 0) → A x y = 0 := by
    intro x y hz
    by_contra ha
    exact hd (filteredGamma2_unsupported_top A Z x y ha hz).2
  have hfin := gamma2_support_finite A Z hs
  rw [hf] at hfin
  exact (lt_irrefl ⊤) hfin

theorem filteredGamma2_zero_matrix {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) : filteredGamma2 (0 : Matrix X X ℂ) Z = 0 := by
  apply bot_unique
  simpa using! filteredGamma2_le_of_gramFilteredCert (gramFilteredCert_zero Z (le_refl (0 : ℝ)))

theorem filteredGamma2_zero_value_duality {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (hz : filteredGamma2 A Z = 0) :
    filteredGamma2 A Z = filteredGamma2DualValue A Z ∧
      ∃ M : Matrix X X ℂ, (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧
        filteredGamma2 A Z = ENNReal.ofReal ‖A ⊙ M‖ := by
  have hd : filteredGamma2DualValue A Z = 0 := bot_unique (by
    simpa only [hz] using! filteredGamma2DualValue_le A Z)
  refine ⟨hz.trans hd.symm, 0, ?_, ?_⟩
  · intro j; simp
  · simp [hz]
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib

theorem gamma2_first_singular_value_norm {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] (Q : Matrix X X ℂ) : matrixSingularValues Q 0 = ‖Q‖ := by
  let i0 : Fin (Fintype.card X) := ⟨0,Fintype.card_pos⟩
  have hupper : ‖Q‖ ≤ matrixSingularValues Q 0 := by
    apply l2_opNorm_le_of_mulVec_le (matrixSingularValues_nonneg Q 0)
    intro v
    have hs : ‖Q.toEuclideanLin (toEuclidean_fromVec v)‖^2 ≤
        (matrixSingularValues Q 0)^2*‖toEuclidean_fromVec v‖^2 := by
      rw [singular_norm_image_sq, spectral_norm_sq_basis (rightSingularBasis Q), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (matrixSingularValues_nonneg Q j) (matrixSingularValues_nonneg Q 0)).mpr
          (Q.toEuclideanLin.singularValues_antitone (Nat.zero_le j)))
        (Complex.normSq_nonneg _)
    change ‖toEuclidean_fromVec (Q*ᵥv)‖^2 ≤
      (matrixSingularValues Q 0)^2*‖toEuclidean_fromVec v‖^2 at hs
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (matrixSingularValues_nonneg Q 0)
      (norm_nonneg _))).mp (by simpa only [mul_pow] using! hs)
  have hlower := Matrix.l2_opNorm_mulVec Q (rightSingularBasis Q i0)
  change ‖Q.toEuclideanLin (rightSingularBasis Q i0)‖ ≤ ‖Q‖*‖rightSingularBasis Q i0‖ at hlower
  rw [norm_apply_rightSingularBasis, norm_rightSingularBasis, mul_one] at hlower
  exact le_antisymm hlower hupper

theorem gamma2_norm_singular_pair {X : Type} [Fintype X] [DecidableEq X]
    (Q : Matrix X X ℂ) (hQ : Q ≠ 0) :
    ∃ u v : X → ℂ, ‖toEuclidean_fromVec u‖=1 ∧ ‖toEuclidean_fromVec v‖=1 ∧
      (star u ⬝ᵥ (Q*ᵥv)).re=‖Q‖ := by
  classical
  have hX : Nonempty X := by
    by_contra hx
    letI : IsEmpty X := not_nonempty_iff.mp hx
    apply hQ
    ext x
    exact isEmptyElim x
  letI := hX
  let i0 : Fin (Fintype.card X) := ⟨0,Fintype.card_pos⟩
  have hσ : 0 < matrixSingularValues Q i0 := by
    change 0 < matrixSingularValues Q 0
    rw [gamma2_first_singular_value_norm]
    exact norm_pos_iff.mpr hQ
  let u := leftSingularVector Q i0
  let v := rightSingularBasis Q i0
  have hu : ‖u‖=1 :=
      norm_leftSingularVector Q i0 ((matrixSingularValues_pos_iff_lt_finrank_range Q).mp hσ)
  have hv : ‖v‖=1 := norm_rightSingularBasis Q i0
  have hp : (inner ℂ u (Q.toEuclideanLin v)).re = ‖Q‖ := by
    rw [apply_rightSingularBasis_eq_smul_leftSingularVector, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu]
    simpa using! gamma2_first_singular_value_norm Q
  refine ⟨WithLp.ofLp u, WithLp.ofLp v, hu, hv, ?_⟩
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using! hp

theorem gamma2_hermitian_dilation_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) (hT : ‖T‖ ≤ 1) :
    ‖Matrix.fromBlocks (0 : Matrix X X ℂ) T Tᴴ 0‖ ≤ 1 := by
  apply l2_opNorm_le_of_mulVec_le zero_le_one
  intro s
  let l : X → ℂ := s ∘ Sum.inl
  let r : X → ℂ := s ∘ Sum.inr
  have ha : ‖toEuclidean_fromVec (T*ᵥr)‖ ≤ ‖toEuclidean_fromVec r‖ :=
    (l2_norm_mulVec_fromVec_le T r).trans (by simpa using! (mul_le_mul_of_nonneg_right hT (norm_nonneg (toEuclidean_fromVec r))))
  have hb : ‖toEuclidean_fromVec (Tᴴ*ᵥl)‖ ≤ ‖toEuclidean_fromVec l‖ :=
    (l2_norm_mulVec_fromVec_le Tᴴ l).trans (by simpa only [Matrix.l2_opNorm_conjTranspose, one_mul] using! (mul_le_mul_of_nonneg_right hT (norm_nonneg (toEuclidean_fromVec l))))
  have hs : s=Sum.elim l r := by ext x; cases x <;> rfl
  have hnorm : ‖toEuclidean_fromVec s‖^2 =
      ‖toEuclidean_fromVec l‖^2+‖toEuclidean_fromVec r‖^2 := by
    rw [hs]
    simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have hnormT : ‖toEuclidean_fromVec ((Matrix.fromBlocks 0 T Tᴴ 0)*ᵥs)‖^2 =
      ‖toEuclidean_fromVec (T*ᵥr)‖^2+‖toEuclidean_fromVec (Tᴴ*ᵥl)‖^2 := by
    rw [hs, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, zero_add, add_zero, norm_toEuclidean_fromVec_sq,
      Fintype.sum_sum_type, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  have has := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ha
  have hbs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
  simp only [one_mul]
  nlinarith [norm_nonneg (toEuclidean_fromVec s),
    norm_nonneg (toEuclidean_fromVec ((Matrix.fromBlocks 0 T Tᴴ 0)*ᵥs))]

theorem gamma2_paired_diagonal_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (p q : X → ℂ) (h : ∀ x, Complex.normSq (p x)+Complex.normSq (q x) ≤ 1) :
    ‖Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)‖ ≤ 1 := by
  let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
  have he : Cᴴ*C = Matrix.diagonal (fun x =>
      ((Complex.normSq (p x)+Complex.normSq (q x) : ℝ) : ℂ)) := by
    dsimp [C]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    ext x
    simp only [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_add]
  have hd : ‖Cᴴ*C‖ ≤ 1 := by
    rw [he, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
    exact h x
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hd
  nlinarith [norm_nonneg C]

theorem gamma2_paired_compression {X : Type} [Fintype X] [DecidableEq X]
    (p q : X → ℂ) (T : Matrix X X ℂ) :
    let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
    Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) T Tᴴ 0*C =
      (Matrix.diagonal p)ᴴ*T*(Matrix.diagonal q) +
      (Matrix.diagonal q)ᴴ*Tᴴ*(Matrix.diagonal p) := by
  (try dsimp only)
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, zero_add, add_zero]
  exact add_comm _ _

theorem gamma2_adjoint_pairing {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) (u v : X → ℂ) :
    star v ⬝ᵥ (Tᴴ*ᵥu) = star (star u ⬝ᵥ (T*ᵥv)) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  exact star_dotProduct _ _

theorem gamma2_rayleigh_re_le_norm {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) (d : X → ℂ) :
    (star d ⬝ᵥ (T*ᵥd)).re ≤ ‖T‖*‖toEuclidean_fromVec d‖^2 := by
  have hi : ‖star d ⬝ᵥ (T*ᵥd)‖ ≤
      ‖toEuclidean_fromVec d‖*‖toEuclidean_fromVec (T*ᵥd)‖ := by
    have hc := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec d) (toEuclidean_fromVec (T*ᵥd))
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, toEuclidean_fromVec,
      WithLp.ofLp_toLp, dotProduct_comm] using! hc
  calc
    _ ≤ ‖star d ⬝ᵥ (T*ᵥd)‖ := Complex.re_le_norm _
    _ ≤ ‖toEuclidean_fromVec d‖*‖toEuclidean_fromVec (T*ᵥd)‖ := hi
    _ ≤ ‖toEuclidean_fromVec d‖*(‖T‖*‖toEuclidean_fromVec d‖) := by
      gcongr
      exact l2_norm_mulVec_fromVec_le T d
    _ = _ := by ring

theorem gamma2_quad_sandwich {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (C : Matrix Y X ℂ) (T : Matrix Y Y ℂ) (d : X → ℂ) :
    star d ⬝ᵥ ((Cᴴ*T*C)*ᵥd) = star (C*ᵥd) ⬝ᵥ (T*ᵥ(C*ᵥd)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]

theorem gamma2_balanced_compression_witness {X : Type} [Fintype X] [DecidableEq X]
    (Q : Matrix X X ℂ) (u v : X → ℂ)
    (hu : ‖toEuclidean_fromVec u‖=1) (hv : ‖toEuclidean_fromVec v‖=1)
    (hpair : (star u ⬝ᵥ (Q*ᵥv)).re=‖Q‖) :
    ∃ (p q : X → ℂ) (d : X → ℝ),
      let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
      let dc : X → ℂ := fun x => (d x : ℂ)
      ‖C‖ ≤ 1 ∧ ‖toEuclidean_fromVec dc‖^2=1 ∧
      (star dc ⬝ᵥ ((Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*C)*ᵥdc)).re=‖Q‖ := by
  let d : X → ℝ := fun x => Real.sqrt ((Complex.normSq (u x)+Complex.normSq (v x))/2)
  have hdsq (x : X) : d x^2=(Complex.normSq (u x)+Complex.normSq (v x))/2 :=
    Real.sq_sqrt (div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num))
  have hd0 (x : X) (hz : d x=0) : u x=0 ∧ v x=0 := by
    have hs := hdsq x
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    have hua : Complex.normSq (u x)=0 := by
      nlinarith [Complex.normSq_nonneg (u x), Complex.normSq_nonneg (v x)]
    have hva : Complex.normSq (v x)=0 := by
      nlinarith [Complex.normSq_nonneg (u x), Complex.normSq_nonneg (v x)]
    exact ⟨Complex.normSq_eq_zero.mp hua, Complex.normSq_eq_zero.mp hva⟩
  let p : X → ℂ := fun x => u x / ((Real.sqrt 2 : ℂ)*(d x : ℂ))
  let q : X → ℂ := fun x => v x / ((Real.sqrt 2 : ℂ)*(d x : ℂ))
  let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
  have htwo : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hpq (x : X) : Complex.normSq (p x)+Complex.normSq (q x) ≤ 1 := by
    dsimp [p, q]
    simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, htwo]
    by_cases hz : d x=0
    · simp [hz]
    · have hpos : 0 < 2*d x^2 := by positivity
      rw [← add_div, div_le_iff₀ hpos]
      nlinarith [hdsq x]
  have hC : ‖C‖ ≤ 1 := gamma2_paired_diagonal_norm_le p q hpq
  let t : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  let dc : X → ℂ := fun x => (d x : ℂ)
  have hPd : (Matrix.diagonal p)*ᵥdc = t • u := by
    ext x
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    dsimp [p, dc, t]
    by_cases hz : d x=0
    · simp [hz, (hd0 x hz).1]
    · have hd : (d x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      field_simp
  have hQd : (Matrix.diagonal q)*ᵥdc = t • v := by
    ext x
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    dsimp [q, dc, t]
    by_cases hz : d x=0
    · simp [hz, (hd0 x hz).2]
    · have hd : (d x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      field_simp
  have hdnorm : ‖toEuclidean_fromVec dc‖^2=1 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [dc, Complex.norm_real, Real.norm_eq_abs, sq_abs, hdsq,
      Complex.normSq_eq_norm_sq]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [← norm_toEuclidean_fromVec_sq u, ← norm_toEuclidean_fromVec_sq v, hu, hv]
    norm_num
  have hscale : t * star t = (1/2 : ℂ) := by
    dsimp [t]
    simp only [map_inv₀, Complex.conj_ofReal]
    have hh : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
      rw [← Complex.ofReal_mul, ← pow_two, htwo]
      norm_num
    rw [← _root_.mul_inv_rev, hh]
    simp only [one_div]
  have hquad : (star dc ⬝ᵥ ((Cᴴ*Matrix.fromBlocks 0 Q Qᴴ 0*C)*ᵥdc)).re=‖Q‖ := by
    rw [gamma2_quad_sandwich]
    dsimp only [C]
    rw [Matrix.fromRows_mulVec, hPd, hQd, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, zero_add, add_zero, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.mulVec_smul, smul_zero, Function.star_sumElim, sumElim_dotProduct_sumElim, star_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [gamma2_adjoint_pairing]
    rw [← mul_assoc, ← mul_assoc, hscale]
    norm_num [Complex.add_re, Complex.mul_re, Complex.star_def]
    linarith [hpair]
  exact ⟨p,q,d,hC,hdnorm,hquad⟩

theorem gamma2_balanced_compression {X : Type} [Fintype X] [DecidableEq X]
    (Q : Matrix X X ℂ) (u v : X → ℂ)
    (hu : ‖toEuclidean_fromVec u‖=1) (hv : ‖toEuclidean_fromVec v‖=1)
    (hpair : (star u ⬝ᵥ (Q*ᵥv)).re=‖Q‖) :
    ∃ p q : X → ℂ,
      ‖Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)‖ ≤ 1 ∧
      ‖Q‖ ≤ ‖(Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))ᴴ*
        Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*
        Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)‖ := by
  obtain ⟨p,q,d,hC,hdnorm,hquad⟩ := gamma2_balanced_compression_witness Q u v hu hv hpair
  refine ⟨p,q,hC,?_⟩
  have hb := gamma2_rayleigh_re_le_norm ((Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))ᴴ*
    Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*
    Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)) (fun x => (d x : ℂ))
  rw [hquad,hdnorm,mul_one] at hb
  exact hb

theorem gamma2_balanced_real_compression {X : Type} [Fintype X] [DecidableEq X]
    (Q : Matrix X X ℂ) (u v : X → ℂ)
    (hu : ‖toEuclidean_fromVec u‖=1) (hv : ‖toEuclidean_fromVec v‖=1)
    (hpair : (star u ⬝ᵥ (Q*ᵥv)).re=‖Q‖) :
    ∃ p q : X → ℂ,
      ‖Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)‖ ≤ 1 ∧
      ‖Q‖ ≤ ‖gamma2RealPart ((Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))ᴴ*
        Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*
        Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))‖ := by
  obtain ⟨p,q,d,hC,hdnorm,hquad⟩ := gamma2_balanced_compression_witness Q u v hu hv hpair
  refine ⟨p,q,hC,?_⟩
  have hb := gamma2_rayleigh_re_le_norm (gamma2RealPart ((Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))ᴴ*
    Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*
    Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q))) (fun x => (d x : ℂ))
  rw [gamma2RealPart_real_rayleigh, hquad,hdnorm,mul_one] at hb
  exact hb

theorem gamma2_masked_compression {X : Type} [Fintype X] [DecidableEq X]
    (p q : X → ℂ) (T R : Matrix X X ℂ)
    (hR : ∀ x y, star (R y x) = R x y) :
    let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
    R ⊙ (Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) T Tᴴ 0*C) =
      Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) (R ⊙ T) (R ⊙ T)ᴴ 0*C := by
  (try dsimp only)
  rw [gamma2_paired_compression, gamma2_paired_compression]
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.add_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, Matrix.conjTranspose_apply,
    star_mul, hR]
  ring

theorem gamma2_masked_real_hermitian_symmetrization {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n : ℕ) (input : X → Fin n → Bool)
    (f : X → E) (M : Matrix X X ℂ)
    (hM : ∀ j, ‖(fun x y => gramFilterDelta input j x y *
      gramFunctionEvaluationMatrix f x y) ⊙ M‖ ≤ 1) :
    ∃ Γ : Matrix X X ℂ, Γ.IsHermitian ∧
      (∀ x y, f x = f y → Γ x y = 0) ∧
      (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) ∧
      (∀ x y, (Γ x y).im=0) ∧
      ‖gramFunctionEvaluationMatrix f ⊙ M‖ ≤ ‖Γ‖ := by
  let Q := gramFunctionEvaluationMatrix f ⊙ M
  by_cases hz : Q=0
  · refine ⟨0, Matrix.isHermitian_zero, ?_, ?_, by simp, ?_⟩
    · simp
    · intro j
      simp
    · change ‖Q‖ ≤ ‖(0 : Matrix X X ℂ)‖
      rw [hz]
  obtain ⟨u,v,hu,hv,hpair⟩ := gamma2_norm_singular_pair Q hz
  obtain ⟨p,q,hC,hbound⟩ := gamma2_balanced_real_compression Q u v hu hv hpair
  let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
  let B := Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*C
  let Γ := gamma2RealPart B
  have hherm : Γ.IsHermitian := gamma2RealPart_isHermitian B
    (Matrix.isHermitian_conjTranspose_mul_mul C
      (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero))
  refine ⟨Γ,hherm,?_,?_,?_,hbound⟩
  · intro x y hxy
    have hq : Q x y=0 := by simp [Q, Matrix.hadamard_apply, gramFunctionEvaluationMatrix, hxy]
    have hq' : Q y x=0 := by simp [Q, Matrix.hadamard_apply, gramFunctionEvaluationMatrix, hxy.symm]
    have hb : B x y=0 := by
      dsimp only [B,C]
      rw [gamma2_paired_compression]
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, hq, hq']
    simp [Γ,gamma2RealPart,hb]
  · intro j
    have hmask (x y : X) : star (gramFilterDelta input j y x)=gramFilterDelta input j x y := by
      by_cases he : input x j=input y j
      · simp only [gramFilterDelta, if_pos he, if_pos he.symm, star_zero]
      · simp only [gramFilterDelta, if_neg he, if_neg (Ne.symm he), star_one]
    have he : gramFilterDelta input j ⊙ Q =
        (fun x y => gramFilterDelta input j x y*gramFunctionEvaluationMatrix f x y) ⊙ M := by
      ext x y
      simp only [Q, Matrix.hadamard_apply]
      ring
    have hreal : gramFilterDelta input j ⊙ Γ=gamma2RealPart (gramFilterDelta input j ⊙ B) := by
      ext x y
      by_cases hxy : input x j=input y j <;>
        simp [Γ,gamma2RealPart,Matrix.hadamard_apply,gramFilterDelta,hxy]
    rw [hreal]
    apply (gamma2RealPart_norm_le _).trans
    change ‖gramFilterDelta input j ⊙ (Cᴴ*Matrix.fromBlocks 0 Q Qᴴ 0*C)‖ ≤ 1
    rw [gamma2_masked_compression p q Q (gramFilterDelta input j) hmask]
    have hd := gamma2_hermitian_dilation_norm_le (gramFilterDelta input j ⊙ Q)
      (by rw [he]; exact hM j)
    calc
      _ ≤ ‖Cᴴ‖*‖Matrix.fromBlocks (0 : Matrix X X ℂ)
          (gramFilterDelta input j ⊙ Q) (gramFilterDelta input j ⊙ Q)ᴴ 0‖*‖C‖ :=
        (Matrix.l2_opNorm_mul (Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ)
          (gramFilterDelta input j ⊙ Q) (gramFilterDelta input j ⊙ Q)ᴴ 0) C).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Cᴴ _) (norm_nonneg C))
      _ ≤ 1*1*1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = 1 := by norm_num

  · intro x y
    simp [Γ,gamma2RealPart]

theorem gamma2_masked_hermitian_symmetrization {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n : ℕ) (input : X → Fin n → Bool)
    (f : X → E) (M : Matrix X X ℂ)
    (hM : ∀ j, ‖(fun x y => gramFilterDelta input j x y *
      gramFunctionEvaluationMatrix f x y) ⊙ M‖ ≤ 1) :
    ∃ Γ : Matrix X X ℂ, Γ.IsHermitian ∧
      (∀ x y, f x = f y → Γ x y = 0) ∧
      (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) ∧
      ‖gramFunctionEvaluationMatrix f ⊙ M‖ ≤ ‖Γ‖ := by
  obtain ⟨Γ,hherm,hzero,hfilter,_,hbound⟩ :=
    gamma2_masked_real_hermitian_symmetrization n input f M hM
  exact ⟨Γ,hherm,hzero,hfilter,hbound⟩

theorem generalAdversaryValue_eq_relaxed_dual {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    generalAdversaryValue input f = filteredGamma2DualValue (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y*gramFunctionEvaluationMatrix f x y) := by
  refine le_antisymm (generalAdversaryValue_le_relaxed_dual input f) ?_
  unfold filteredGamma2DualValue
  apply iSup_le
  intro M
  obtain ⟨Γ,hherm,hzero,hfilter,hbound⟩ :=
    gamma2_masked_hermitian_symmetrization n input f M.1 M.2
  exact (ENNReal.ofReal_le_ofReal hbound).trans
    (le_iSup_of_le ⟨Γ,hherm,hzero,hfilter⟩ le_rfl)

theorem filteredGamma2_strong_duality (X : Type) [Fintype X] [DecidableEq X]
    (n : ℕ) (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) :
    filteredGamma2 A Z=filteredGamma2DualValue A Z ∧
      (filteredGamma2 A Z < ⊤ → ∃ M : Matrix X X ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ filteredGamma2 A Z=ENNReal.ofReal ‖A ⊙ M‖) := by
  classical
  have he : filteredGamma2 A Z=filteredGamma2DualValue A Z := by
    by_cases hp : filteredGamma2 A Z=⊤
    · rw [hp,filteredGamma2_infinite_duality A Z hp]
    have hfin : filteredGamma2 A Z < ⊤ := lt_top_iff_ne_top.mpr hp
    refine le_antisymm ?_ (filteredGamma2DualValue_le A Z)
    by_contra! hlt
    have hd : filteredGamma2DualValue A Z ≠ ⊤ :=
      (lt_of_le_of_lt (filteredGamma2DualValue_le A Z) hfin).ne
    have htr := (ENNReal.toReal_lt_toReal hd hp).mpr hlt
    obtain ⟨t,hdt,htp⟩ := exists_between htr
    have ht : 0 ≤ t := ENNReal.toReal_nonneg.trans hdt.le
    have hnot : ¬gramFilteredCert A Z t := by
      intro hc
      have hh := filteredGamma2_le_of_gramFilteredCert hc
      have hsmall := (ENNReal.ofReal_lt_iff_lt_toReal ht hp).mpr htp
      exact (not_lt_of_ge hh) hsmall
    have hs := gamma2_finite_support A Z hfin
    obtain ⟨a,b,N,hab,hbudget,hB,hpair⟩ := gamma2_psd_separation A Z t ht hs hnot
    obtain ⟨M,hM,hobj⟩ := gamma2_psd_operator_polar A Z hs a b N hab hbudget hB
    have hdual : ENNReal.ofReal ‖A ⊙ M‖ ≤ filteredGamma2DualValue A Z :=
      le_iSup_of_le ⟨M,hM⟩ le_rfl
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hd).mp hdual
    exact (not_lt_of_ge (hobj.trans hreal)) (hdt.trans hpair)
  refine ⟨he,?_⟩
  intro hf
  obtain ⟨M,hM,hmax⟩ := filteredGamma2DualValue_attained A Z hf
  exact ⟨M,hM,he.trans hmax⟩

theorem generalAdversaryValue_eq_real_sup {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    generalAdversaryValue input f =
      ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
        (∀ x y, f x=f y → Γ x y=0) ∧
        (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) ∧
        ∀ x y, (Γ x y).im=0}, ENNReal.ofReal ‖Γ.1‖ := by
  apply le_antisymm
  · rw [generalAdversaryValue_eq_relaxed_dual]
    unfold filteredGamma2DualValue
    apply iSup_le
    intro M
    obtain ⟨Γ,hherm,hzero,hfilter,hreal,hbound⟩ :=
      gamma2_masked_real_hermitian_symmetrization n input f M.1 M.2
    exact (ENNReal.ofReal_le_ofReal hbound).trans
      (le_iSup_of_le ⟨Γ,hherm,hzero,hfilter,hreal⟩ le_rfl)
  · apply iSup_le
    intro Γ
    exact le_iSup_of_le ⟨Γ.1,Γ.2.1,Γ.2.2.1,Γ.2.2.2.1⟩ le_rfl

theorem gamma2_real_hermitian_iff_symmetric {X : Type} (Γ : Matrix X X ℂ)
    (hreal : ∀ x y, (Γ x y).im=0) : Γ.IsHermitian ↔ Γ.IsSymm := by
  have he : Γᴴ=Γᵀ := by
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Complex.star_def]
    apply Complex.ext
    · simp
    · simp [hreal]
  change Γᴴ=Γ ↔ Γᵀ=Γ
  rw [he]

theorem generalAdversaryValue_eq_real_symmetric_sup {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    generalAdversaryValue input f =
      ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsSymm ∧
        (∀ x y, f x=f y → Γ x y=0) ∧
        (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) ∧
        ∀ x y, (Γ x y).im=0}, ENNReal.ofReal ‖Γ.1‖ := by
  apply le_antisymm
  · rw [generalAdversaryValue_eq_real_sup]
    apply iSup_le
    intro Γ
    have hs := (gamma2_real_hermitian_iff_symmetric Γ.1 Γ.2.2.2.2).mp Γ.2.1
    exact le_iSup_of_le ⟨Γ.1,hs,Γ.2.2⟩ le_rfl
  · apply iSup_le
    intro Γ
    have hh := (gamma2_real_hermitian_iff_symmetric Γ.1 Γ.2.2.2.2).mpr Γ.2.1
    exact le_iSup_of_le ⟨Γ.1,hh,Γ.2.2.1,Γ.2.2.2.1⟩ le_rfl

theorem generalAdversaryValue_real_attained {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E)
    (hf : generalAdversaryValue input f < ⊤) :
    ∃ Γ : Matrix X X ℂ, Γ.IsSymm ∧ (∀ x y, (Γ x y).im=0) ∧
      (∀ x y, f x=f y → Γ x y=0) ∧
      (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) ∧
      generalAdversaryValue input f=ENNReal.ofReal ‖Γ‖ := by
  let Z : Fin n → Matrix X X ℂ := fun j x y =>
    gramFilterDelta input j x y*gramFunctionEvaluationMatrix f x y
  have he : generalAdversaryValue input f=filteredGamma2 (gramFunctionEvaluationMatrix f) Z :=
    (generalAdversaryValue_eq_relaxed_dual input f).trans
      (filteredGamma2_strong_duality X n (gramFunctionEvaluationMatrix f) Z).1.symm
  obtain ⟨M,hM,hmax⟩ := (filteredGamma2_strong_duality X n (gramFunctionEvaluationMatrix f) Z).2
    (by rwa [← he])
  obtain ⟨Γ,hherm,hzero,hfilter,hreal,hbound⟩ :=
    gamma2_masked_real_hermitian_symmetrization n input f M hM
  refine ⟨Γ,(gamma2_real_hermitian_iff_symmetric Γ hreal).mp hherm,hreal,hzero,hfilter,?_⟩
  apply le_antisymm
  · rw [he,hmax]
    exact ENNReal.ofReal_le_ofReal hbound
  · exact le_iSup_of_le ⟨Γ,hherm,hzero,hfilter⟩ le_rfl
end Qatlib.Concepts.GramQueryCore.GammaDuality
