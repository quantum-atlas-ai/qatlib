/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupSampling
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Fresh repetitions of hidden subgroup sampling

Defines joint and character-valued probability mass functions for a hidden subgroup sampling
run, together with the finite distribution `hiddenSubgroupSampleDist`. The recursive law
`hiddenSubgroupFreshSamples` describes fresh runs and is identified with independent product
probabilities.

When `f` hides a subgroup, each character sample is uniform on its annihilator. The module also
relates two independent runs to a tensor-product measurement and counts resources in a fresh
sampling schedule, as used in abelian hidden subgroup algorithms [NielsenChuang2010].

## Main statements

* `hiddenSubgroupFreshSamples_apply`: identifies sequence masses with independent product
  probabilities.
* `hiddenSubgroupFreshSamples_hiding`: gives the product of uniform annihilator probabilities.
* `hiddenSubgroupFreshSchedule_resources`: counts queries and gate macros across fresh runs.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.HspRecovery.Distinguisher

open scoped Classical

variable {G R : Type*}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- The joint Born probability mass function after a hidden subgroup sampling circuit runs on a
uniform input register and a zero output register. -/
noncomputable def hiddenSubgroupJointLaw (f : G → R) (e : G ≃ AddChar G ℂ) : PMF (G × R) :=
  bornDistribution
    (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
      (TensorState (Uniform G) (Ket 0)))
    (normalized_run_hiddenSubgroupSampling f e)

/-- The character-valued probability mass function obtained by relabeling the first-register
marginal of `hiddenSubgroupJointLaw` through `e`. -/
noncomputable def hiddenSubgroupSampleLaw (f : G → R) (e : G ≃ AddChar G ℂ) :
    PMF (AddChar G ℂ) :=
  (hiddenSubgroupJointLaw f e).map (fun q => e q.1)

/-- The mass of character `χ` is the `ENNReal.ofReal` conversion of the first-register singleton
marginal at `e.symm χ`. -/
theorem hiddenSubgroupSampleLaw_apply (f : G → R) (e : G ≃ AddChar G ℂ)
    (χ : AddChar G ℂ) :
    hiddenSubgroupSampleLaw f e χ = ENNReal.ofReal
      (MarginalProbLeft
        (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) {e.symm χ}) := by
  simp only [hiddenSubgroupSampleLaw, hiddenSubgroupJointLaw, PMF.map_apply,
    tsum_fintype, Fintype.sum_prod_type, bornDistribution_apply,
    show ∀ x : G, χ = e x ↔ x = e.symm χ from fun x => by
      rw [eq_comm, Equiv.apply_eq_iff_eq_symm_apply]]
  simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, Finset.sum_singleton]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (ENNReal.ofReal_sum_of_nonneg (fun (z : R) _ =>
    bornProb_nonneg
      (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Ket 0))) (e.symm χ, z))).symm

/-- The finite real-valued character distribution given by first-register measurement of the
hidden subgroup sampling circuit. -/
noncomputable def hiddenSubgroupSampleDist (f : G → R) (e : G ≃ AddChar G ℂ) :
    FinDist (AddChar G ℂ) where
  prob χ := MarginalProbLeft
    (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
      (TensorState (Uniform G) (Ket 0))) {e.symm χ}
  nonneg χ := measureProb_nonneg _ _
  sum_one := by
    simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, Finset.sum_singleton]
    let ψ := Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
      (TensorState (Uniform G) (Ket 0))
    change (∑ χ : AddChar G ℂ, ∑ z : R, BornProb ψ (e.symm χ, z)) = 1
    calc
      _ = ∑ x : G, ∑ z : R, BornProb ψ (x, z) :=
        e.symm.sum_comp (fun x : G => ∑ z : R, BornProb ψ (x, z))
      _ = ∑ q : G × R, BornProb ψ q := (Fintype.sum_prod_type _).symm
      _ = 1 := normalized_run_hiddenSubgroupSampling f e

/-- The probability mass function of a sequence of fresh hidden subgroup sampling runs,
recording their first registers as characters. -/
noncomputable def hiddenSubgroupFreshSamples (f : G → R) (e : G ≃ AddChar G ℂ) :
    (m : ℕ) → PMF (Fin m → AddChar G ℂ)
  | 0 => PMF.pure Fin.elim0
  | m + 1 => (hiddenSubgroupJointLaw f e).bind fun q =>
      (hiddenSubgroupFreshSamples f e m).map (Fin.cons (e q.1))

/-- A fresh sequence of length `m + 1` is obtained by sampling `hiddenSubgroupSampleLaw` and
prepending it to an independent fresh sequence of length `m`. -/
theorem hiddenSubgroupFreshSamples_succ (f : G → R) (e : G ≃ AddChar G ℂ) (m : ℕ) :
    hiddenSubgroupFreshSamples f e (m + 1) =
      (hiddenSubgroupSampleLaw f e).bind fun χ =>
        (hiddenSubgroupFreshSamples f e m).map (Fin.cons χ) := by
  simp only [hiddenSubgroupFreshSamples, hiddenSubgroupSampleLaw, PMF.bind_map,
    Function.comp_def]

/-- The mass of a fresh sequence factors as its head's one-sample mass times the fresh tail
mass. -/
theorem hiddenSubgroupFreshSamples_cons (f : G → R) (e : G ≃ AddChar G ℂ)
    (m : ℕ) (χ : AddChar G ℂ) (xs : Fin m → AddChar G ℂ) :
    hiddenSubgroupFreshSamples f e (m + 1) (Fin.cons χ xs) =
      hiddenSubgroupSampleLaw f e χ * hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_succ]
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, Fin.cons_inj, ite_and, Finset.sum_ite_irrel,
    mul_ite]

/-- The mass of a fresh character sequence equals the `ENNReal.ofReal` conversion of its
independent product probability under `hiddenSubgroupSampleDist`. -/
theorem hiddenSubgroupFreshSamples_apply (f : G → R) (e : G ≃ AddChar G ℂ)
    (m : ℕ) (xs : Fin m → AddChar G ℂ) :
    hiddenSubgroupFreshSamples f e m xs =
      ENNReal.ofReal ((hiddenSubgroupSampleDist f e).probOf xs) := by
  induction m with
  | zero =>
    simp [hiddenSubgroupFreshSamples, PMF.pure_apply, Subsingleton.elim xs Fin.elim0,
      FinDist.probOf]
  | succ m ih =>
    conv_lhs => rw [← Fin.cons_self_tail xs]
    rw [hiddenSubgroupFreshSamples_cons, hiddenSubgroupSampleLaw_apply, ih]
    simp only [FinDist.probOf, Fin.prod_univ_succ]
    exact (ENNReal.ofReal_mul ((hiddenSubgroupSampleDist f e).nonneg (xs 0))).symm

/-- A decidable fresh-sample event has probability equal to the `ENNReal.ofReal` conversion of
its independent finite-distribution event probability. -/
theorem hiddenSubgroupFreshSamples_event (f : G → R) (e : G ≃ AddChar G ℂ)
    (m : ℕ) (E : (Fin m → AddChar G ℂ) → Prop) [DecidablePred E] :
    (∑ xs ∈ Finset.univ.filter E, hiddenSubgroupFreshSamples f e m xs) =
      ENNReal.ofReal ((hiddenSubgroupSampleDist f e).probEvent E) := by
  simp only [hiddenSubgroupFreshSamples_apply, FinDist.probEvent]
  exact (ENNReal.ofReal_sum_of_nonneg (fun xs _ =>
    Finset.prod_nonneg (fun i _ => (hiddenSubgroupSampleDist f e).nonneg (xs i)))).symm

/-- If `f` hides `H`, each character in the annihilator has probability the reciprocal
annihilator cardinality, and every other character has probability zero. -/
theorem hiddenSubgroupSampleDist_prob (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (χ : AddChar G ℂ) :
    (hiddenSubgroupSampleDist f e).prob χ =
      if χ ∈ characterAnnihilator H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0 :=
  marginalProbLeft_hiddenSubgroupSampling_singleton f H hf e χ

/-- If `f` hides `H`, the mass of a fresh sequence is the product of the uniform annihilator
probabilities, converted to `ENNReal`. -/
theorem hiddenSubgroupFreshSamples_hiding (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ)
    (m : ℕ) (xs : Fin m → AddChar G ℂ) :
    hiddenSubgroupFreshSamples f e m xs = ENNReal.ofReal
      (∏ i, if xs i ∈ characterAnnihilator H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0) := by
  rw [hiddenSubgroupFreshSamples_apply]
  simp only [FinDist.probOf, hiddenSubgroupSampleDist_prob f H hf]

/-- Measuring specified first-register characters in two tensor copies of the sampling output
gives the product of their individual sample probabilities. -/
theorem twoFreshHiddenSubgroup_measure (f : G → R) (e : G ≃ AddChar G ℂ)
    (χ η : AddChar G ℂ) :
    let ψ := Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
      (TensorState (Uniform G) (Ket 0))
    MeasureProb (TensorState ψ ψ)
      (({e.symm χ} ×ˢ Finset.univ) ×ˢ ({e.symm η} ×ˢ Finset.univ)) =
        (hiddenSubgroupSampleDist f e).prob χ *
          (hiddenSubgroupSampleDist f e).prob η := by
  exact measureProb_tensorState_prod _ _ _ _

omit [DecidableEq G] [AddCommGroup R] [Fintype R] in

/-- A schedule of `m` fresh hidden subgroup sampling circuits contains exactly `m` queries and
`m` gate macros. -/
theorem hiddenSubgroupFreshSchedule_resources (e : G ≃ AddChar G ℂ) (m : ℕ) :
    ((List.replicate m (hiddenSubgroupSamplingCircuit (R := R) e)).map QueryCount).sum = m ∧
      ((List.replicate m (hiddenSubgroupSamplingCircuit (R := R) e)).map GateCount).sum = m := by
  simp [hiddenSubgroupSamplingCircuit, QueryCount, GateCount]

end Qatlib.Concepts.HspRecovery.Distinguisher
