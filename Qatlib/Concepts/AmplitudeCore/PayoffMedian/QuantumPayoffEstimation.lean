/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Quantum estimation of bounded payoffs

`payoffPreparation` encodes a payoff in the success probability of an ancillary qubit. The
module identifies this probability with the payoff mean, proves accuracy and sorted median
bounds for the resulting amplitude estimation law, and counts accesses in the repeated circuit.
See [Montanaro2015] for background.

## Main statements

* `payoff_actual_rotation_and_mean`: The payoff preparation is unitary and its ancillary true
  probability equals the Born weighted mean of `f`. See [Montanaro2015].
* `quantum_mean_actual_ae_accuracy`: The payoff mean estimate has error at most `2 * π * sqrt (μ
  * (1 - μ)) / M + π^2 / M^2` with probability at least `8 / π^2`. See [Montanaro2015].
* `quantum_mean_sorted_median_amplification`: The sorted median of `2 * r + 1` fresh payoff
  estimates exceeds the amplitude estimation error bound with probability at most `2^(2 * r + 1)
  * (1 - 8 / π^2)^(r + 1)`. See [Montanaro2015].

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AmplitudeCore.PayoffMedian

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The block diagonal ancillary rotation with coefficients `sqrt (f i)` and `sqrt (1 - f i)`
for each input index. -/
noncomputable def payoffRotation {I : Type} [Fintype I] [DecidableEq I] (f : I → ℝ) :
    Matrix (I × Bool) (I × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then
      match p.2, q.2 with
      | false, false => ((Real.sqrt (1 - f p.1) : ℂ))
      | false, true => (-(Real.sqrt (f p.1) : ℂ))
      | true, false => ((Real.sqrt (f p.1) : ℂ))
      | true, true => ((Real.sqrt (1 - f p.1) : ℂ))
    else 0

/-- The entries of `payoffRotation` are the stated two by two rotation coefficients on each
index block and zero between distinct blocks. -/
theorem payoffRotation_apply (f : I → ℝ) (i k : I) (b c : Bool) :
    payoffRotation f (i, b) (k, c) =
      if i = k then
        (if b then (if c then ((Real.sqrt (1 - f i) : ℂ)) else ((Real.sqrt (f i) : ℂ)))
         else (if c then (-(Real.sqrt (f i) : ℂ)) else ((Real.sqrt (1 - f i) : ℂ))))
      else 0 := by
  by_cases h : i = k
  · subst h
    cases b <;> cases c <;> simp [payoffRotation, Matrix.of_apply]
  · simp [payoffRotation, Matrix.of_apply, h]

/-- For nonnegative `x`, multiplying its real square root by itself in `ℂ` gives the complex
embedding of `x`. -/
private theorem sqrt_real_sq (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℂ) * (Real.sqrt x : ℂ)) = ((x : ℂ)) := by
  rw [show ((Real.sqrt x : ℂ) * (Real.sqrt x : ℂ)) = (((Real.sqrt x)^2 : ℝ) : ℂ) from by
    push_cast; ring, Real.sq_sqrt hx]

/-- The payoff rotation is unitary when every payoff lies in `[0, 1]`. -/
theorem payoffRotation_mem_unitaryGroup {I : Type} [Fintype I] [DecidableEq I] (f : I → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) :
    payoffRotation f ∈ Matrix.unitaryGroup (I × Bool) ℂ := by
  have hdiag : ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → y + z = 1 →
      (((Real.sqrt y : ℂ) * (Real.sqrt y : ℂ)) + ((Real.sqrt z : ℂ) * (Real.sqrt z : ℂ)))
        = (1 : ℂ) := by
    intro y z hy hz hyz
    rw [sqrt_real_sq y hy, sqrt_real_sq z hz]
    exact_mod_cast hyz
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p q
  obtain ⟨i, b⟩ := p
  obtain ⟨i', b'⟩ := q
  have hv : 0 ≤ f i := (hf i).1
  have hu : 0 ≤ 1 - f i := by linarith [(hf i).2]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, payoffRotation_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  by_cases hii : i = i'
  · subst hii
    rw [Finset.sum_eq_single i]
    · cases b <;> cases b' <;>
        simp only [Complex.star_def, Complex.conj_ofReal, map_neg,
          Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false,
          Prod.mk.injEq, and_false, reduceCtorEq] <;>
        first
        | exact hdiag (f i) (1 - f i) hv hu (by ring)
        | (rw [neg_mul_neg]; exact hdiag (1 - f i) (f i) hu hv (by ring))
        | ring
    · intro k _ hki
      simp [hki]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · rw [Finset.sum_eq_single i]
    · have hne : ¬((i, b) = (i', b')) := fun h => hii (congrArg Prod.fst h)
      rw [ite_eq_right hne]
      simp [hii]
    · intro k _ hki
      simp [hki]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon

/-- The preparation matrix obtained by applying `A` to the input register and then rotating the
ancillary qubit according to `f`. -/
noncomputable def payoffPreparation {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (f : I → ℝ) : Matrix (I × Bool) (I × Bool) ℂ :=
  payoffRotation f * TensorGate A 1

/-- Payoff preparation is unitary when `A` is unitary and `f` takes values in `[0, 1]`. -/
theorem payoffPreparation_mem_unitaryGroup (A : Matrix I I ℂ) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) :
    payoffPreparation A f ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  (Matrix.unitaryGroup (I × Bool) ℂ).mul_mem (payoffRotation_mem_unitaryGroup f hf)
    (tensorGate_unitary hA (Submonoid.one_mem _))

/-- A payoff preparation matrix entry factors into an entry of `A` and an ancillary rotation
entry. -/
theorem payoffPreparation_entry (A : Matrix I I ℂ) (f : I → ℝ) (i i' : I) (b b' : Bool) :
    payoffPreparation A f (i, b) (i', b') = A i i' * payoffRotation f (i, b) (i, b') := by
  simp only [payoffPreparation, Matrix.mul_apply, payoffRotation_apply, TensorGate,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, mul_zero, mul_one]
  rw [Finset.sum_eq_single i]
  · cases b <;> cases b' <;> simp <;> ring
  · intro k _ hki
    simp [Ne.symm hki]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- Applying payoff preparation to `Ket (j, false)` gives the stated product of preparation and
rotation amplitudes. -/
theorem payoffPreparation_mulVec_ket (A : Matrix I I ℂ) (f : I → ℝ) (j : I) :
    payoffPreparation A f *ᵥ Ket (j, false) =
      fun p => A p.1 j * payoffRotation f (p.1, p.2) (p.1, false) := by
  funext p
  obtain ⟨i, b⟩ := p
  simp only [Matrix.mulVec, dotProduct, Ket]
  rw [Finset.sum_eq_single (j, false)]
  · rw [ite_eq_left rfl, payoffPreparation_entry, mul_one]
  · intro q _ hq
    rw [ite_eq_right hq, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (j, false)) hcon

/-- The payoff preparation is unitary and its ancillary true probability equals the Born
weighted mean of `f`. See [Montanaro2015]. -/
theorem payoff_actual_rotation_and_mean (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) :
    payoffPreparation A f ∈ Matrix.unitaryGroup (I×Bool) ℂ ∧
    MeasureProb (ApplyGate (payoffPreparation A f) (Ket (j,false)))
      (Finset.univ.filter (fun p => p.2=true))=∑ i, BornProb (ApplyGate A (Ket j)) i*f i := by
  have hv : ∀ i, 0 ≤ f i := fun i => (hf i).1
  have hentry : ∀ i, payoffRotation f (i, true) (i, false) = ((Real.sqrt (f i) : ℂ)) := by
    intro i; simp [payoffRotation_apply]
  have hnorm : ∀ i, ‖((Real.sqrt (f i) : ℂ))‖ = Real.sqrt (f i) := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hk : ∀ i : I, (A *ᵥ Ket j) i = A i j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Ket]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [ite_eq_right hk, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have hterm : ∀ i : I, ‖A i j * payoffRotation f (i, true) (i, false)‖ ^ 2
      = ‖(A *ᵥ Ket j) i‖ ^ 2 * f i := by
    intro i
    rw [hk i, hentry i, norm_mul, hnorm i, mul_pow, Real.sq_sqrt (hv i)]
  have hmain : MeasureProb (ApplyGate (payoffPreparation A f) (Ket (j,false)))
      (Finset.univ.filter (fun p => p.2=true))
      = ∑ i, BornProb (ApplyGate A (Ket j)) i*f i := by
    have hstate := payoffPreparation_mulVec_ket A f j
    simp only [ApplyGate, hstate, MeasureProb, BornProb]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, add_zero]
    exact hterm i
  exact ⟨payoffPreparation_mem_unitaryGroup A f hA hf, hmain⟩

/-- The amplitude estimation outcome law for the ancillary true event of the payoff preparation. -/
noncomputable def meanLaw {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) (hM : 2≤M) :
    FinDist (Fin M) :=
  aeLaw M (payoffPreparation A f) (j, false)
    (Finset.univ.filter (fun p : I × Bool => p.2 = true))
    (payoffPreparation_mem_unitaryGroup A f hA hf) hM

/-- `meanLaw` is the amplitude estimation law of `payoffPreparation` with the ancillary true
outcomes marked. -/
theorem meanLaw_eq (M : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) (hM : 2≤M) :
    meanLaw M A j f hA hf hM =
      aeLaw M (payoffPreparation A f) (j, false)
        (Finset.univ.filter (fun p : I × Bool => p.2 = true))
        (payoffPreparation_mem_unitaryGroup A f hA hf) hM := rfl

/-- The sorted median of the `2 * r + 1` amplitude estimates in a sample record. -/
noncomputable def meanMedian (r M : ℕ) (ω : Fin (2*r+1) → Fin M) : ℝ :=
  sortedBlockMedian r (fun n => aeEstimate M (ω n))

/-- The payoff mean estimate has error at most `2 * π * sqrt (μ * (1 - μ)) / M + π^2 / M^2` with
probability at least `8 / π^2`. See [Montanaro2015]. -/
theorem quantum_mean_actual_ae_accuracy (M : ℕ) (hM : 2≤M) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) :
    let μ:=∑ i, BornProb (ApplyGate A (Ket j)) i*f i;
    ∑ z ∈ Finset.univ.filter (fun z => |aeEstimate M z-μ|≤2*Real.pi*Real.sqrt (μ*(1-μ))/(M:ℝ)+Real.pi^2/(M:ℝ)^2),
      (meanLaw M A j f hA hf hM).prob z ≥ 8/Real.pi^2 := by
  have key := (payoff_actual_rotation_and_mean A j f hA hf).2
  have main := (prepared_ae_bhmt_error_and_endpoints M hM (payoffPreparation A f) (j, false)
    (Finset.univ.filter (fun p : I × Bool => p.2 = true))
    (payoffPreparation_mem_unitaryGroup A f hA hf)).1
  simp only [preparedAAState] at main
  rw [key] at main
  exact main

set_option maxHeartbeats 2000000 in

/-- The sorted median of `2 * r + 1` fresh payoff estimates exceeds the amplitude estimation
error bound with probability at most `2^(2 * r + 1) * (1 - 8 / π^2)^(r + 1)`. See
[Montanaro2015]. -/
theorem quantum_mean_sorted_median_amplification (M r : ℕ) (hM : 2≤M) (A : Matrix I I ℂ)
    (j : I) (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) :
    let μ:=∑ i, BornProb (ApplyGate A (Ket j)) i*f i;
    (meanLaw M A j f hA hf hM).probEvent (fun ω => 2*Real.pi*Real.sqrt (μ*(1-μ))/(M:ℝ)+Real.pi^2/(M:ℝ)^2< |meanMedian r M ω-μ|)≤(2:ℝ)^(2*r+1)*(1-8/Real.pi^2)^(r+1) := by
  classical
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_sq : 8 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three, Real.pi_lt_four]
  have hpi2_pos : 0 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp_le_one : 1 - 8/Real.pi^2 ≤ 1 := by
    have h8nn : (0:ℝ) ≤ 8/Real.pi^2 := div_nonneg (by norm_num) hpi2_pos.le
    linarith
  have hp_nonneg : 0 ≤ 1 - 8/Real.pi^2 := by
    have h8 : 8/Real.pi^2 ≤ 1 := (div_le_one hpi2_pos).mpr hpi_sq
    linarith
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hgood := quantum_mean_actual_ae_accuracy M hM A j f hA hf
  simp only [] at hgood
  (try dsimp only)
  set μ := ∑ i, BornProb (ApplyGate A (Ket j)) i*f i with hμ
  set ε := 2*Real.pi*Real.sqrt (μ*(1-μ))/(M:ℝ)+Real.pi^2/(M:ℝ)^2 with hε
  have hε0 : 0 ≤ ε := by
    have h1 : (0:ℝ) ≤ 2*Real.pi*Real.sqrt (μ*(1-μ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hpi_pos)) (Real.sqrt_nonneg _)
    exact add_nonneg (div_nonneg h1 hMpos.le) (by positivity)
  set p := meanLaw M A j f hA hf hM with hp

  have hbadmass : (∑ z ∈ Finset.univ.filter (fun z : Fin M => ε < |aeEstimate M z-μ|), p.prob z)
      ≤ 1 - 8/Real.pi^2 := by
    have hsplit : ∀ z : Fin M, (if ε < |aeEstimate M z-μ| then p.prob z else 0)
        + (if ¬(ε < |aeEstimate M z-μ|) then p.prob z else 0) = p.prob z := by
      intro z
      by_cases hz : ε < |aeEstimate M z-μ| <;> simp [hz]
    have hsum : (∑ z ∈ Finset.univ.filter (fun z : Fin M => ε < |aeEstimate M z-μ|), p.prob z)
        + (∑ z ∈ Finset.univ.filter (fun z : Fin M => ¬(ε < |aeEstimate M z-μ|)), p.prob z) = 1 := by
      have hcombined : ∑ z ∈ Finset.univ, ((if ε < |aeEstimate M z-μ| then p.prob z else 0)
          + (if ¬(ε < |aeEstimate M z-μ|) then p.prob z else 0)) = 1 := by
        rw [Finset.sum_congr rfl fun z _ => hsplit z]
        exact p.sum_one
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hcombined
      exact hcombined
    have hgoodfilter : Finset.univ.filter (fun z : Fin M => ¬(ε < |aeEstimate M z-μ|))
        = Finset.univ.filter (fun z : Fin M => |aeEstimate M z-μ|≤ε) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [hgoodfilter] at hsum
    linarith

  have hmaj : ∀ ω : Fin (2*r+1) → Fin M, ε < |meanMedian r M ω-μ| →
      r+1 ≤ (Finset.univ.filter (fun n : Fin (2*r+1) =>
        ε < |aeEstimate M (ω n)-μ|)).card := by
    intro ω hω
    have := heterogeneous_sorted_median_majority_witness r (fun n => aeEstimate M (ω n))
      μ ε hε0 hω
    simpa [meanMedian] using this

  set fam : Finset (Finset (Fin (2*r+1))) := Finset.univ.filter (fun J => r+1 ≤ J.card) with hfam
  have hsub : Finset.univ.filter (fun ω => ε < |meanMedian r M ω-μ|)
      ⊆ Finset.univ.filter (fun ω => ∃ J : Finset (Fin (2*r+1)),
          J ∈ fam ∧ ∀ n ∈ J, ε < |aeEstimate M (ω n)-μ|) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard := hmaj ω hω.2
    exact ⟨Finset.univ.filter (fun n : Fin (2*r+1) => ε < |aeEstimate M (ω n)-μ|),
      by rw [hfam]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩,
      fun n hn => (Finset.mem_filter.mp hn).2⟩
  have hub := fintype_union_bound_mass (p.probOf)
    (fun ω => Finset.prod_nonneg fun n _ => p.nonneg _)
    (A := fun (J : Finset (Fin (2*r+1))) ω => J ∈ fam ∧ ∀ n ∈ J,
      ε < |aeEstimate M (ω n)-μ|)
  have hdrop : (∑ J : Finset (Fin (2*r+1)), ∑ ω ∈ Finset.univ.filter
      (fun ω => J ∈ fam ∧ ∀ n ∈ J, ε < |aeEstimate M (ω n)-μ|), p.probOf ω)
      = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter
          (fun ω => ∀ n ∈ J, ε < |aeEstimate M (ω n)-μ|), p.probOf ω := by
    rw [← Finset.sum_subset (Finset.subset_univ fam) (fun J _ hJ =>
      Finset.sum_eq_zero fun ω hω => absurd ((Finset.mem_filter.mp hω).2).1 hJ)]
    exact Finset.sum_congr rfl fun J hJ => Finset.sum_congr
      (Finset.filter_congr fun ω _ => ⟨fun h => h.2, fun h => ⟨hJ, h⟩⟩) fun _ _ => rfl
  have hperJ : ∀ J ∈ fam,
      (∏ n ∈ J, (∑ z ∈ Finset.univ.filter
          (fun z : Fin M => ε < |aeEstimate M z-μ|), p.prob z))
      ≤ (1-8/Real.pi^2)^(r+1) := by
    intro J hJ
    rw [hfam] at hJ
    have hJcard := (Finset.mem_filter.mp hJ).2
    refine le_trans (le_trans
      (Finset.prod_le_prod₀ (fun n _ => Finset.sum_nonneg fun _ _ => p.nonneg _)
        (fun n _ => hbadmass)) (le_of_eq (Finset.prod_const (1-8/Real.pi^2)))) ?_
    rw [← Nat.sub_add_cancel hJcard, pow_add]
    exact mul_le_of_le_one_left (pow_nonneg hp_nonneg _)
      (pow_le_one_of_mem_Icc hp_nonneg hp_le_one _)
  have hcards : fam.card ≤ 2^(2*r+1) := by
    rw [hfam]
    have h1 : (Finset.univ.filter (fun J : Finset (Fin (2*r+1)) => r+1 ≤ J.card)).card
        ≤ (Finset.univ : Finset (Finset (Fin (2*r+1)))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h1
    exact h1
  show (∑ ω ∈ Finset.univ.filter (fun ω => ε < |meanMedian r M ω-μ|), p.probOf ω)
    ≤ (2:ℝ)^(2*r+1)*(1-8/Real.pi^2)^(r+1)
  calc (∑ ω ∈ Finset.univ.filter (fun ω => ε < |meanMedian r M ω-μ|), p.probOf ω)
      ≤ ∑ J : Finset (Fin (2*r+1)), ∑ ω ∈ Finset.univ.filter
          (fun ω => J ∈ fam ∧ ∀ n ∈ J, ε < |aeEstimate M (ω n)-μ|), p.probOf ω :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun ω _ _ => Finset.prod_nonneg fun n _ => p.nonneg _).trans hub
    _ = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter
          (fun ω => ∀ n ∈ J, ε < |aeEstimate M (ω n)-μ|), p.probOf ω := hdrop
    _ = ∑ J ∈ fam, ∏ n ∈ J, (∑ z ∈ Finset.univ.filter
          (fun z : Fin M => ε < |aeEstimate M z-μ|), p.prob z) :=
        Finset.sum_congr rfl fun J _ =>
          Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf_subset_product p (fun z : Fin M => ε < |aeEstimate M z-μ|) J
    _ ≤ ∑ J ∈ fam, (1-8/Real.pi^2)^(r+1) := Finset.sum_le_sum fun J hJ => hperJ J hJ
    _ = (fam.card : ℝ) * (1-8/Real.pi^2)^(r+1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2:ℝ)^(2*r+1) * (1-8/Real.pi^2)^(r+1) := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp_nonneg _)
        exact_mod_cast hcards

/-- Repeating the counted payoff estimation circuit `2 * r + 1` times uses `(2 * r + 1) * (M -
1)` queries and `(2 * r + 1) * (5 * (M - 1) + 3)` gates. See [Montanaro2015]. -/
theorem quantum_mean_repeated_actual_accesses (M r : ℕ) (hM : 2≤M) (A : Matrix I I ℂ)
    (j : I) (f : I → ℝ) :
    let C:=countedAECircuit M (payoffPreparation A f) (j,false);
    QueryCount (RepeatCircuit C (2*r+1))=(2*r+1)*(M-1) ∧
    GateCount (RepeatCircuit C (2*r+1))=(2*r+1)*(5*(M-1)+3) := by
  have hl := prepared_ae_access_ledger (I := I × Bool) M (by omega)
    (payoffPreparation A f) (j, false)
  constructor
  · rw [queryCount_repeatCircuit, hl.1]
  · rw [gateCount_repeatCircuit, hl.2.1]

end Qatlib.Concepts.AmplitudeCore.PayoffMedian
