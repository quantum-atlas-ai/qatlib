/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.LchsSimulation.StaticLchs.CountedPlanSampling
import Qatlib.Concepts.LchsSimulation.StaticLchs.FiniteTrigonometricSums

/-!
# Prepared amplitude amplification sampled with fair bits

`preparedAATrial` measures a prepared amplitude amplification circuit and records its gate and
query counts. `preparedAASampled` selects the iteration count using finite rejection sampling,
retaining separate records for random bits, oracle queries, and gates. The results compute the
window success probability, its lower bound, and the expected resource counts.

The mathematical background is described in [BrassardEtAl2002].

## Main statements

* `prepared_aa_uniform_window`: computes the average success probability over an iteration
  window.
* `prepared_aa_sampled_three_ledgers`: computes the three expected resource counts.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open Matrix
open scoped ENNReal Classical

/-- The Born measurement law of the prepared amplitude amplification circuit with `i`
iterations, carrying its gate count and oracle query cost. -/
noncomputable def preparedAATrial {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    {m : ℕ} (i : Fin m) : CostedLaw (I × ℕ) :=
  (bornDistribution (Run (preparedMark S) (preparedAACircuit A j₀ (i : ℕ)) (Ket j₀))
    ((prepared_aa_actual_circuit A j₀ S (i : ℕ) hA).1.normalized_run
      ((prepared_aa_reflection_and_access A j₀ S hA).1) (normalized_ket j₀))).map
    fun y => ((y, GateCount (preparedAACircuit A j₀ (i : ℕ))),
      QueryCount (preparedAACircuit A j₀ (i : ℕ)))

/-- The joint law obtained by finite fair-bit sampling of an iteration count followed by a
prepared amplitude amplification trial, with separate bit and query costs. -/
noncomputable def preparedAASampled {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (b m fuel : ℕ) : PMF (Option (I × ℕ) × ℕ × ℕ) :=
  finiteCoinThenAttempt b m fuel (fun i => preparedAATrial A hA j₀ S i)

section Sums

/-- The sum of the natural indices in `Fin n`, cast to extended nonnegative reals, is `n * (n -
1) / 2`. -/
private theorem sum_fin_val' (n : ℕ) :
    (∑ i : Fin n, ((i : ℕ) : ℝ≥0∞)) = (((n : ℕ) : ℝ≥0∞)) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hsummap : ∑ i : Fin n, (((i.castSucc : Fin (n + 1)) : ℕ) : ℝ≥0∞)
          = ∑ i : Fin n, ((i : ℕ) : ℝ≥0∞) :=
        Finset.sum_congr rfl fun i _ => by rw [Fin.val_castSucc]
      have hlast : (((Fin.last n : Fin (n + 1)) : ℕ) : ℝ≥0∞) = ((n : ℕ) : ℝ≥0∞) := by simp
      rw [hsummap, ih, hlast]
      by_cases hn : n = 0
      · subst hn
        simp
      · have hnp : (((n - 1 : ℕ) : ℝ≥0∞)) + 1 = ((n : ℕ) : ℝ≥0∞) := by
          have h1 : n - 1 + 1 = n := by omega
          exact_mod_cast h1
        have h2 : ((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by simp)
        calc ((n : ℕ) : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + ((n : ℕ) : ℝ≥0∞)
            = ((n : ℕ) : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + ((n : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹) := by
                rw [h2, mul_one]
          _ = (((n : ℕ) : ℝ≥0∞)) * (((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + (((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)) := (mul_add _ _ _).symm
          _ = (((n : ℕ) : ℝ≥0∞))
                * (((((n - 1 : ℕ) : ℝ≥0∞)) + ((2 : ℝ≥0∞)))
                * ((2 : ℝ≥0∞))⁻¹) := by
                rw [add_mul]
          _ = ((n : ℕ) : ℝ≥0∞)
                * (((((n : ℕ) : ℝ≥0∞)) + ((1 : ℝ≥0∞))) * ((2 : ℝ≥0∞))⁻¹) := by
                have hb2 : (((n - 1 : ℕ) : ℝ≥0∞)) + ((2 : ℝ≥0∞))
                    = (((n : ℕ) : ℝ≥0∞)) + ((1 : ℝ≥0∞)) := by
                  rw [← hnp]
                  ring
                rw [hb2]
          _ = (((n : ℕ) : ℝ≥0∞) + ((1 : ℝ≥0∞)))
                * (((n : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞))⁻¹) := by ring
        rw [show (n + 1 - 1 : ℕ) = n from by omega, Nat.cast_add, Nat.cast_one]

/-- The sum of `3 * i + 1` over `Fin n`, in extended nonnegative reals, is `n * (3 * (n - 1) / 2
+ 1)`. -/
private theorem sum_fin_3add1 (n : ℕ) :
    (∑ i : Fin n, (((3*(i : ℕ)+1 : ℕ) : ℝ≥0∞)))
      = (((n : ℕ) : ℝ≥0∞)) * ((3 : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹) + 1) := by
  have h3 : ∀ i : Fin n,
      (((3*(i : ℕ)+1 : ℕ) : ℝ≥0∞)) = 3 * ((i : ℕ) : ℝ≥0∞) + 1 := by
    intro i
    push_cast
    ring
  have h1sum : ∑ i : Fin n, (1 : ℝ≥0∞) = ((n : ℕ) : ℝ≥0∞) := by simp
  rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_add_distrib, ← Finset.mul_sum,
    h1sum, sum_fin_val']
  ring

/-- The sum of `2 * i + 1` over `Fin n`, in extended nonnegative reals, is `n * n`. -/
private theorem sum_fin_2add1 (n : ℕ) :
    (∑ i : Fin n, (((2*(i : ℕ)+1 : ℕ) : ℝ≥0∞)))
      = (((n : ℕ) : ℝ≥0∞)) * (((n : ℕ) : ℝ≥0∞)) := by
  have hid2 : 2 * ∑ i : Fin n, ((i : ℕ) : ℕ) = n*(n-1) := by
    rw [mul_comm, Fin.sum_univ_eq_sum_range (fun j : ℕ => j) n,
      Finset.sum_range_id_mul_two]
  have hsplit : ∑ i : Fin n, (2*(i : ℕ)+1 : ℕ) = 2*(∑ i : Fin n, ((i:ℕ):ℕ)) + n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hnat : ∑ i : Fin n, (2*(i : ℕ)+1 : ℕ) = n*n := by
    rw [hsplit, hid2]
    cases n with
    | zero => simp
    | succ n' =>
        simp only [Nat.add_sub_cancel]
        ring
  exact_mod_cast hnat

/-- The image of the real number `1 / 4` under `ENNReal.ofReal` is the inverse of `4`. -/
private theorem quarter_cast : ENNReal.ofReal ((1/4:ℝ)) = ((4:ℝ≥0∞))⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4), ENNReal.ofReal_one, one_div]
  norm_num

/-- A nonzero natural mass cancels between division and multiplication in the extended
nonnegative reals. -/
private theorem div_mul_natmass_cancel {c X : ℝ≥0∞} {n : ℕ} (hn : n ≠ 0) :
    (c / ((n : ℕ) : ℝ≥0∞)) * (((n : ℕ) : ℝ≥0∞) * X) = c * X := by
  rw [div_eq_mul_inv, mul_assoc,
    ← mul_assoc (((n : ℕ) : ℝ≥0∞)⁻¹) (((n : ℕ) : ℝ≥0∞)) X,
    mul_comm (((n : ℕ) : ℝ≥0∞)⁻¹) (((n : ℕ) : ℝ≥0∞)),
    ENNReal.mul_inv_cancel (by exact_mod_cast hn : ((n : ℕ) : ℝ≥0∞) ≠ 0)
      (ENNReal.natCast_ne_top n), one_mul]

end Sums

/-- Expectation is the infinite sum of the observable weighted by the probability mass function. -/
private theorem expectation_tsum' {α : Type} (p : PMF α) (f : α → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f = ∑' a, p a * f a := rfl

/-- The probability of membership in a finite set is the sum of the masses of its elements. -/
private theorem event_mem_sum' {α : Type} [Fintype α] (p : PMF α) (T : Finset α) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun b => b ∈ T) = ∑ b ∈ T, p b := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, expectation_tsum',
      tsum_fintype]
  have hEq : ∀ b ∈ Finset.univ,
      (p b * @ite ℝ≥0∞ (b ∈ T) (Classical.propDecidable (b ∈ T)) (1 : ℝ≥0∞) 0)
        = @ite ℝ≥0∞ (b ∈ T) (Classical.propDecidable (b ∈ T)) (p b) 0 := by
    intro b _
    rcases em (b ∈ T) with hb | hb
    · rw [if_pos hb, if_pos hb, mul_one]
    · rw [if_neg hb, if_neg hb, mul_zero]
  have hS : ∑ b ∈ T, (@ite ℝ≥0∞ (b ∈ T) (Classical.propDecidable (b ∈ T)) (p b) 0)
      = ∑ b ∈ T, p b :=
    Finset.sum_congr rfl fun b hb => by rw [if_pos hb]
  have hsub : ∑ b ∈ T, (@ite ℝ≥0∞ (b ∈ T) (Classical.propDecidable (b ∈ T)) (p b) 0)
      = ∑ b ∈ Finset.univ, (@ite ℝ≥0∞ (b ∈ T) (Classical.propDecidable (b ∈ T)) (p b) 0) :=
    Finset.sum_subset (Finset.subset_univ T) fun b _ hb => if_neg hb
  rw [Finset.sum_congr rfl hEq]
  exact hsub.symm.trans hS

/-- For initial success probability `sin θ ^ 2` with `0 < θ < π / 2`, the average success over
`m` prepared amplification iterations is `1 / 2 - sin (4 * m * θ) / (4 * m * sin (2 * θ))`. -/
theorem prepared_aa_uniform_window {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (m : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    0 < m → 0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
    (∑ i : Fin m, MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S)/(m:ℝ) =
    1/2-Real.sin (4*(m:ℝ)*θ)/(4*(m:ℝ)*Real.sin (2*θ)) := by
  intro hm hθ0 hθ1 hprob
  have hs2 : Real.sin (2*θ) ≠ 0 := by
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith : (0:ℝ) < 2*θ)
      (by linarith [Real.pi_pos] : 2*θ < Real.pi))
  have hmR : ((m:ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : (m:ℕ) ≠ 0)
  have hsin2 : ∀ x : ℝ, (Real.sin x)^2 = 1/2 - Real.cos (2*x)/2 := by
    intro x
    have h1 := Real.sin_sq x
    have h2 := Real.cos_sq x
    linarith
  have hEntry : ∀ j : ℕ,
      (Real.sin ((2*(j:ℝ)+1)*θ))^2
        = 1/2 - Real.cos ((2*(j:ℝ)+1)*(2*θ))/2 := by
    intro j
    rw [hsin2]
    congr 1
    ring
  rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ j) (Ket j₀)) S) m,
    Finset.sum_congr rfl (fun j _ =>
      prepared_aa_born_success A j₀ S θ j hA hθ0 hθ1 hprob),
    Finset.sum_congr rfl (fun j _ => hEntry j)]
  have hcossum := cosine_odd_sum (2*θ) m hs2
  have hang : 2*(m:ℝ)*(2*θ) = 4*(m:ℝ)*θ := by ring
  rw [hang] at hcossum
  have hterm : ∀ i ∈ Finset.range m,
      (1/2:ℝ) - Real.cos ((2*((i:ℕ):ℝ)+1)*(2*θ))/2
        = (1/2) - (1/2) * Real.cos ((2*((i:ℕ):ℝ)+1)*(2*θ)) := by
    intro i _
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hsum : ∑ i ∈ Finset.range m, (1/2 - Real.cos ((2*((i:ℕ):ℝ)+1)*(2*θ))/2)
      = ((m:ℝ))/2 - Real.sin (4*(m:ℝ)*θ)/(4*Real.sin (2*θ)) := by
    rw [Finset.sum_congr rfl (fun i hi => hterm i hi), Finset.sum_sub_distrib,
      ← Finset.mul_sum, hcossum]
    simp
    field_simp
    ring
  rw [hsum]
  field_simp

/-- The average prepared amplification success is at least `1 / 4` when `m * sin (2 * θ) ≥ 1`
and the initial success probability is `sin θ ^ 2` with `0 < θ < π / 2`. -/
theorem prepared_aa_uniform_success_lower {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (m : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    0 < m → 0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
    1 ≤ (m:ℝ)*Real.sin (2*θ) →
    (1/4:ℝ) ≤ (∑ i : Fin m, MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S)/(m:ℝ) := by
  intro hm hθ0 hθ1 hprob hms
  rw [prepared_aa_uniform_window A j₀ S θ m hA hm hθ0 hθ1 hprob]
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hs2pos : (0:ℝ) < Real.sin (2*θ) := by nlinarith
  have hs4 : Real.sin (4*(m:ℝ)*θ) ≤ 1 := le_trans (le_abs_self _) (Real.abs_sin_le_one _)
  have hd : (0:ℝ) < 4*(m:ℝ)*Real.sin (2*θ) := by positivity
  rw [le_sub_iff_add_le]
  have hX : Real.sin (4*(m:ℝ)*θ)/(4*(m:ℝ)*Real.sin (2*θ)) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have hquarter : (1/4:ℝ)*(4*(m:ℝ)*Real.sin (2*θ)) = (m:ℝ)*Real.sin (2*θ) := by
      field_simp
    rw [hquarter]
    linarith
  linarith

/-- A prepared trial has query cost `i`, gate count `3 * i + 1` on its support, and marked-event
probability equal to the circuit Born probability. -/
theorem prepared_aa_trial_actual_metadata {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    {m : ℕ} (i : Fin m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (preparedAATrial A hA j₀ S i) = (i.val : ℝ≥0∞) ∧
    (∀ x ∈ (preparedAATrial A hA j₀ S i).support, x.2=i.val ∧ x.1.2=3*i.val+1) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S i) (fun x => x.1.1 ∈ S) =
    ENNReal.ofReal (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S) := by
  have hQC : QueryCount (preparedAACircuit A j₀ (i:ℕ)) = (i:ℕ) :=
    (prepared_aa_actual_circuit A j₀ S (i:ℕ) hA).2.1
  have hGC : GateCount (preparedAACircuit A j₀ (i:ℕ)) = 3*(i:ℕ)+1 :=
    (prepared_aa_actual_circuit A j₀ S (i:ℕ) hA).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((bornDistribution _ _).map
        fun y => ((y, GateCount (preparedAACircuit A j₀ (i:ℕ))),
          QueryCount (preparedAACircuit A j₀ (i:ℕ)))) (fun x => (x.2 : ℝ≥0∞)) = _
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    have hcongr : ∀ a : I,
        ((QueryCount (preparedAACircuit A j₀ (i:ℕ)) : ℕ) : ℝ≥0∞)
          = ((i:ℕ) : ℝ≥0∞) := fun a => by rw [hQC]
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    obtain ⟨rfl⟩ := hxz
    exact ⟨hQC, hGC⟩
  · show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((bornDistribution _ _).map
        fun y => ((y, GateCount (preparedAACircuit A j₀ (i:ℕ))),
          QueryCount (preparedAACircuit A j₀ (i:ℕ)))) (fun x => x.1.1 ∈ S) = _
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (show ∀ z : I,
        ((((z, GateCount (preparedAACircuit A j₀ (i:ℕ))),
          QueryCount (preparedAACircuit A j₀ (i:ℕ))).1.1) ∈ S) ↔ (z ∈ S) from fun z => Iff.rfl),
      event_mem_sum']
    exact bornDistribution_event _ _ S

/-- For a nonempty window fitting in `b` bits, sampled prepared success equals the sum of
iteration success probabilities times `(1 - coinRejectMass b m ^ fuel) / m`. -/
theorem prepared_aa_sampled_success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (b m fuel : ℕ) (hm : 0 < m) (hm2 : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S b m fuel)
    (fun x => ∃ y gates, x.1=some (y,gates) ∧ y ∈ S) =
    ((1-(coinRejectMass b m)^fuel)/(m:ℝ≥0∞)) *
      ∑ i : Fin m, ENNReal.ofReal (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S) := by
  have hmass : ∀ i : Fin m,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun b m fuel) (fun x => x.1 = Sum.inl i)
        = (1 - (coinRejectMass b m)^fuel) / ((m : ℕ) : ℝ≥0∞) :=
    fun i => (finite_coin_return_and_pending b m fuel hm hm2).2 i
  have hiff : ∀ z : Option (I × ℕ) × ℕ × ℕ,
      (∃ y gates, z.1 = some (y, gates) ∧ y ∈ S) ↔ (∃ a, z.1 = some a ∧ a.1 ∈ S) := by
    intro z
    constructor
    · rintro ⟨y, gates, hz, hy⟩
      exact ⟨(y, gates), hz, hy⟩
    · rintro ⟨a, hz, ha⟩
      exact ⟨a.1, a.2, hz, ha⟩
  rw [preparedAASampled, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff,
    finite_coin_attempt_event b m fuel (fun i => preparedAATrial A hA j₀ S i)
      (fun a : I × ℕ => a.1 ∈ S),
    Finset.sum_congr rfl (fun i _ => by
      rw [hmass i, (prepared_aa_trial_actual_metadata A j₀ S hA i).2.2]),
    ← Finset.mul_sum]

/-- The sampled trial preserves the sampler expected bit cost and has expected query and gate
costs `(1 - r ^ fuel) * (m - 1) / 2` and `(1 - r ^ fuel) * (3 * (m - 1) / 2 + 1)`, where `r
= coinRejectMass b m`. -/
theorem prepared_aa_sampled_three_ledgers {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (b m fuel : ℕ) (hm : 0 < m) (hm2 : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S b m fuel) (fun x => (x.2.1 : ℝ≥0∞)) =
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun b m fuel) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S b m fuel) (fun x => (x.2.2 : ℝ≥0∞)) =
    (1-(coinRejectMass b m)^fuel)*(m-1:ℕ)/2 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S b m fuel)
    (fun x => ((match x.1 with | none => 0 | some y => y.2 : ℕ) : ℝ≥0∞)) =
    (1-(coinRejectMass b m)^fuel)*(3*((m-1:ℕ):ℝ≥0∞)/2+1) := by
  have hmass : ∀ i : Fin m,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun b m fuel) (fun x => x.1 = Sum.inl i)
        = (1 - (coinRejectMass b m)^fuel) / ((m : ℕ) : ℝ≥0∞) :=
    fun i => (finite_coin_return_and_pending b m fuel hm hm2).2 i
  have hme : ((m : ℕ) : ℝ≥0∞) ≠ 0 := by
    intro h
    have h0 := Nat.cast_eq_zero.mp h
    omega
  have hc := (finite_coin_attempt_joint_cost b m fuel
    (fun i => preparedAATrial A hA j₀ S i))
  have hunfold : preparedAASampled A hA j₀ S b m fuel
      = finiteCoinThenAttempt b m fuel (fun i => preparedAATrial A hA j₀ S i) := rfl
  refine ⟨by rw [hunfold]; exact hc.1, ?_, ?_⟩
  · rw [hunfold, hc.2, Finset.sum_congr rfl (fun i _ => by
        rw [hmass i, (prepared_aa_trial_actual_metadata A j₀ S hA i).1]),
      ← Finset.mul_sum, sum_fin_val', div_mul_natmass_cancel (by omega : m ≠ 0), div_eq_mul_inv,
      mul_assoc]
  · have hGates : ∀ i : Fin m,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAATrial A hA j₀ S i)
            (fun y => ((y.1.2 : ℕ) : ℝ≥0∞))
          = (((3*(i.val:ℕ)+1 : ℕ) : ℝ≥0∞)) := by
      intro i
      have hGC : GateCount (preparedAACircuit A j₀ (i:ℕ)) = 3*(i:ℕ)+1 :=
        (prepared_aa_actual_circuit A j₀ S (i:ℕ) hA).2.2.1
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((bornDistribution _ _).map
          fun y => ((y, GateCount (preparedAACircuit A j₀ (i:ℕ))),
            QueryCount (preparedAACircuit A j₀ (i:ℕ)))) _ = _
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      have hcongr : ∀ a : I,
          ((GateCount (preparedAACircuit A j₀ (i:ℕ)) : ℕ) : ℝ≥0∞)
            = ((3*(i:ℕ)+1 : ℕ) : ℝ≥0∞) := fun a => by rw [hGC]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    have hobs := finite_coin_attempt_observable b m fuel
      (fun i => preparedAATrial A hA j₀ S i)
      (fun a _ => ((match a with | none => 0 | some y => y.2 : ℕ) : ℝ≥0∞))
    simp only [Nat.cast_zero, mul_zero, add_zero] at hobs
    rw [hunfold, hobs, Finset.sum_congr rfl (fun i _ => by rw [hmass i, hGates i]),
      ← Finset.mul_sum, sum_fin_3add1,
      div_mul_natmass_cancel (by omega : m ≠ 0), div_eq_mul_inv, mul_assoc]

/-- The sampled success is at least one quarter of the sampler acceptance probability under the
amplification window condition; initial success probabilities zero and one give zero and the
acceptance probability, respectively. -/
theorem prepared_aa_sampled_lower_and_endpoints {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (b m fuel : ℕ) (hm : 0 < m) (hm2 : m ≤ 2^b) :
    (0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
    1 ≤ (m:ℝ)*Real.sin (2*θ) → (1-(coinRejectMass b m)^fuel)/4 ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S b m fuel)
        (fun x => ∃ y gates, x.1=some (y,gates) ∧ y ∈ S)) ∧
    (MeasureProb (preparedAAState A j₀) S = 0 → Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S b m fuel)
    (fun x => ∃ y gates, x.1=some (y,gates) ∧ y ∈ S) = 0) ∧
    (MeasureProb (preparedAAState A j₀) S = 1 → Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S b m fuel)
    (fun x => ∃ y gates, x.1=some (y,gates) ∧ y ∈ S) = 1-(coinRejectMass b m)^fuel) := by
  have hE := prepared_aa_sampled_success A j₀ S hA b m fuel hm hm2
  have hme : ((m : ℕ) : ℝ≥0∞) ≠ 0 := by
    intro h
    have h0 := Nat.cast_eq_zero.mp h
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hθ0 hθ1 hprob hms
    have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hlow : ((m:ℝ)) * (1/4) ≤ ∑ i : Fin m,
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S := by
      have hG10 := prepared_aa_uniform_success_lower A j₀ S θ m hA hm hθ0 hθ1 hprob hms
      rw [le_div_iff₀ hmR] at hG10
      linarith
    have hquarter : (((m : ℕ) : ℝ≥0∞)) * ENNReal.ofReal ((1/4:ℝ)) ≤ ∑ i : Fin m, ENNReal.ofReal
        (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S) := by
      have h1 : ENNReal.ofReal (((m:ℕ):ℝ) * (1/4)) ≤ ENNReal.ofReal (∑ i : Fin m,
          MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S) :=
        ENNReal.ofReal_le_ofReal hlow
      rwa [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((m:ℕ):ℝ)),
        ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => measureProb_nonneg _ _)] at h1
    have hm1 : (1:ℝ≥0∞) ≤ ((m : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    rw [hE, show ((1-(coinRejectMass b m)^fuel)/4 : ℝ≥0∞)
        = (1-(coinRejectMass b m)^fuel) * ENNReal.ofReal ((1/4:ℝ)) from by
        rw [div_eq_mul_inv, ← quarter_cast]]
    exact calc ((1-(coinRejectMass b m)^fuel)/((m:ℕ):ℝ≥0∞)) *
              (∑ i : Fin m, ENNReal.ofReal
                (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S))
          ≥ ((1-(coinRejectMass b m)^fuel)/((m:ℕ):ℝ≥0∞)) * ((((m : ℕ) : ℝ≥0∞)) * ENNReal.ofReal ((1/4:ℝ))) :=
            mul_le_mul_right hquarter _
        _ = (1-(coinRejectMass b m)^fuel) * ENNReal.ofReal ((1/4:ℝ)) :=
            div_mul_natmass_cancel (by omega : m ≠ 0)
  · intro ha
    rw [hE]
    have hzero : ∀ i : Fin m,
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S = 0 := by
      intro i
      rw [(prepared_aa_endpoint_states A j₀ S i.val hA).1 ha]
      exact ha
    rw [Finset.sum_congr rfl (fun i _ => by rw [hzero i, ENNReal.ofReal_zero]),
      Finset.sum_const_zero, mul_zero]
  · intro ha
    rw [hE]
    have hone : ∀ i : Fin m,
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Ket j₀)) S = 1 := by
      intro i
      have hrun := (prepared_aa_endpoint_states A j₀ S i.val hA).2 ha
      have hn : ‖((-1:ℂ)^(i:ℕ))‖ = 1 := by
        rw [norm_pow]
        norm_num
      rw [hrun, measureProb_smul, hn, one_pow, ha, one_mul]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hone i, ENNReal.ofReal_one]),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
    rw [div_eq_mul_inv, mul_assoc, mul_comm ((m:ℕ):ℝ≥0∞)⁻¹ ((m:ℕ):ℝ≥0∞),
      ENNReal.mul_inv_cancel hme (ENNReal.natCast_ne_top _), mul_one]

/-- The expected input-access count is `(1 - coinRejectMass b m ^ fuel) * m`, and every accepted
output has gate count equal to its input-access count plus its query count. -/
theorem prepared_aa_sampled_input_access_ledger {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (b m fuel : ℕ) (hm : 0 < m) (hm2 : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S b m fuel)
    (fun x => ((match x.1 with | none => 0 | some _ => 2*x.2.2+1 : ℕ) : ℝ≥0∞)) =
      (1-(coinRejectMass b m)^fuel)*(m:ℝ≥0∞) ∧
    (∀ x ∈ (preparedAASampled A hA j₀ S b m fuel).support, ∀ y,
      x.1 = some y → y.2 = (2*x.2.2+1)+x.2.2) := by
  have hmass : ∀ i : Fin m,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun b m fuel) (fun x => x.1 = Sum.inl i)
        = (1 - (coinRejectMass b m)^fuel) / ((m : ℕ) : ℝ≥0∞) :=
    fun i => (finite_coin_return_and_pending b m fuel hm hm2).2 i
  have hme : ((m : ℕ) : ℝ≥0∞) ≠ 0 := by
    intro h
    have h0 := Nat.cast_eq_zero.mp h
    omega
  constructor
  · have hQC : ∀ i : Fin m, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAATrial A hA j₀ S i)
        (fun y => ((2 * y.2 + 1 : ℕ) : ℝ≥0∞)) = (((2*(i.val:ℕ)+1 : ℕ) : ℝ≥0∞)) := by
      intro i
      have hQCe : QueryCount (preparedAACircuit A j₀ (i:ℕ)) = (i:ℕ) :=
        (prepared_aa_actual_circuit A j₀ S (i:ℕ) hA).2.1
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((bornDistribution _ _).map
          fun y => ((y, GateCount (preparedAACircuit A j₀ (i:ℕ))),
            QueryCount (preparedAACircuit A j₀ (i:ℕ)))) _ = _
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      have hcongr : ∀ a : I,
          ((2 * QueryCount (preparedAACircuit A j₀ (i:ℕ)) + 1 : ℕ) : ℝ≥0∞)
            = ((2*(i:ℕ)+1 : ℕ) : ℝ≥0∞) := fun a => by rw [hQCe]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    have hobs := finite_coin_attempt_observable b m fuel
      (fun i => preparedAATrial A hA j₀ S i)
      (fun a q => ((match a with | none => 0 | some _ => 2*q+1 : ℕ) : ℝ≥0∞))
    simp only [Nat.cast_zero, mul_zero, add_zero] at hobs
    rw [preparedAASampled, hobs,
      Finset.sum_congr rfl (fun i _ => by rw [hmass i, hQC i]),
      ← Finset.mul_sum, sum_fin_2add1, div_mul_natmass_cancel (by omega : m ≠ 0)]

  · intro x hx y hy
    have hxb : x ∈ (PMF.bind (finiteCoinRun b m fuel)
        (fun z => match z.1 with
          | Sum.inl i => (preparedAATrial A hA j₀ S i).map
              (fun w => (some w.1, z.2, w.2))
          | Sum.inr _ => PMF.pure (none, z.2, 0))).support := hx
    obtain ⟨c, hc, hxc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hxb
    obtain ⟨conf, bits⟩ := c
    cases conf with
    | inl i =>
        have hxm : x ∈ ((preparedAATrial A hA j₀ S i).map
            fun w => (some w.1, bits, w.2)).support := hxc
        obtain ⟨z, hz, hxz⟩ := (PMF.mem_support_map_iff _ _ _).mp hxm
        obtain ⟨rfl⟩ := hxz
        have hmeta := ((prepared_aa_trial_actual_metadata A j₀ S hA i).2.1 z hz)
        have hzy : z.1 = y := Option.some.inj hy
        have hy2 : y.2 = z.1.2 := by rw [hzy]
        rw [hy2, hmeta.2]
        show (3*(i:ℕ)+1) = (2*z.2+1)+z.2
        rw [hmeta.1]
        omega
    | inr t =>
        cases t
        have hx0 : x = (none, bits, 0) := by
          have hxp : x ∈ (PMF.pure (none, bits, 0)).support := hxc
          simpa [PMF.mem_support_pure_iff] using hxp
        obtain ⟨rfl⟩ := hx0
        exact absurd hy (by simp)

end Qatlib.Concepts.LchsSimulation.StaticLchs
