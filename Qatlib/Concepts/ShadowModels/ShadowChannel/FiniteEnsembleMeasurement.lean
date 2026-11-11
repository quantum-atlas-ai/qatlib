/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument

/-!
# Finite ensemble measurement instruments

This module constructs a measurement instrument from a finite distribution of unitary basis
changes. `ensembleProjector` gives the conjugated basis projectors, `ensembleKraus` supplies
their sampling weights, and `ensembleRecordLaw` records the resulting Born probabilities.

The forgotten instrument equals `ensembleMeasurementMap`, which is unital and symmetric for the
trace pairing. An explicit observed circuit realizes each basis measurement, linking its leaves
to the Kraus operators and giving exact fresh-record resource counts. See
[HuangKuengPreskill2020] for background.

## Main statements

* `finite_ensemble_actual_kraus_born`: Kraus completeness and the record law.
* `finite_ensemble_measurement_channel_and_trace_adjoint`: the forgotten channel and trace
  pairing identity.
* `ensemble_grouped_actual_resources`: exact resources for grouped records.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {X : Type} [Fintype X] {D : ℕ}

/-- The computational basis projector for outcome `o.2`, conjugated backward by the ensemble
operator indexed by `o.1`. -/
noncomputable def ensembleProjector (U : X → Operator D) (o : X × Fin D) : Operator D :=
  (U o.1)ᴴ * Projector {o.2} * U o.1

/-- Every conjugated ensemble basis projector is Hermitian. -/
theorem ensembleProjector_conjTranspose (U : X → Operator D) (o : X × Fin D) :
    (ensembleProjector U o)ᴴ = ensembleProjector U o := by
  rw [ensembleProjector, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, projector_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- For a unitary ensemble member, its conjugate transpose times itself is the identity. -/
theorem ensemble_unitary_conj_mul (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : X) : (U a)ᴴ * U a = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp (hU a)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- For a unitary ensemble member, its product with its conjugate transpose is the identity. -/
theorem ensemble_unitary_mul_conj (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : X) : U a * (U a)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (hU a)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- Conjugated basis projectors are idempotent when the ensemble operators are unitary. -/
theorem ensembleProjector_idem (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) :
    ensembleProjector U o * ensembleProjector U o = ensembleProjector U o := by
  have hun := ensemble_unitary_mul_conj U hU o.1
  calc ensembleProjector U o * ensembleProjector U o
      = (U o.1)ᴴ * (Projector {o.2} * (U o.1 * (U o.1)ᴴ) * Projector {o.2}) * U o.1 := by
        simp only [ensembleProjector, Matrix.mul_assoc]
    _ = (U o.1)ᴴ * (Projector {o.2} * Projector {o.2}) * U o.1 := by
        rw [hun, Matrix.mul_one]
    _ = ensembleProjector U o := by
        rw [projector_mul_self, ensembleProjector]

/-- Every backward-conjugated ensemble basis projector is positive semidefinite. -/
theorem ensembleProjector_posSemidef (U : X → Operator D) (o : X × Fin D) :
    (ensembleProjector U o).PosSemidef := by
  have hM : ensembleProjector U o
      = (Projector {o.2} * U o.1)ᴴ * (Projector {o.2} * U o.1) := by
    calc ensembleProjector U o
        = (U o.1)ᴴ * (Projector {o.2} * Projector {o.2}) * U o.1 := by
          rw [ensembleProjector, projector_mul_self]
      _ = (Projector {o.2} * U o.1)ᴴ * (Projector {o.2} * U o.1) := by
          rw [Matrix.conjTranspose_mul, projector_conjTranspose]
          simp only [Matrix.mul_assoc]
  rw [hM]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A singleton computational basis projector has trace one. -/
theorem trace_projector_singleton (b : Fin D) :
    Matrix.trace (Projector ({b} : Finset (Fin D))) = 1 := by
  rw [Projector, Matrix.trace_diagonal]
  simp

/-- Each ensemble basis projector has trace one when the ensemble operators are unitary. -/
theorem ensembleProjector_trace (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) :
    Matrix.trace (ensembleProjector U o) = 1 := by
  have hun := ensemble_unitary_mul_conj U hU o.1
  calc Matrix.trace (ensembleProjector U o)
      = Matrix.trace ((U o.1 * (U o.1)ᴴ) * Projector {o.2}) := by
        rw [ensembleProjector, Matrix.trace_mul_cycle]
      _ = Matrix.trace (Projector {o.2}) := by rw [hun, Matrix.one_mul]
      _ = 1 := trace_projector_singleton o.2

/-- The sum of all singleton computational basis projectors is the identity. -/
theorem projectors_singleton_sum : ∑ b : Fin D, Projector ({b} : Finset (Fin D)) = 1 := by
  ext i j
  simp only [Projector, Matrix.sum_apply, Matrix.diagonal_apply, Finset.mem_singleton,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- For a fixed unitary ensemble member, summing its conjugated basis projectors over outcomes
gives the identity. -/
theorem ensembleProjector_sum_axis (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : X) :
    ∑ b : Fin D, ensembleProjector U (a, b) = 1 := by
  have hun := ensemble_unitary_conj_mul U hU a
  calc ∑ b : Fin D, ensembleProjector U (a, b)
      = (U a)ᴴ * (∑ b : Fin D, Projector ({b} : Finset (Fin D))) * U a := by
        simp only [ensembleProjector]
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = (U a)ᴴ * 1 * U a := by rw [projectors_singleton_sum]
    _ = 1 := by rw [Matrix.mul_one, hun]

/-- Sandwiching a matrix between the basis projector at `b` gives that projector scaled by the
diagonal entry `M b b`. -/
theorem projector_singleton_conj (b : Fin D) (M : Operator D) :
    Projector ({b} : Finset (Fin D)) * M * Projector {b}
      = (M b b) • Projector ({b} : Finset (Fin D)) := by
  have hd : ∀ k l : Fin D, Projector ({b} : Finset (Fin D)) k l
      = if k = b then if k = l then (1 : ℂ) else 0 else 0 := by
    intro k l
    by_cases h : k = l <;> by_cases h2 : k = b <;>
      simp [Projector, Matrix.diagonal_apply, Finset.mem_singleton, h, h2]
  ext i j
  simp only [hd, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hi : i = b <;> by_cases hj : j = b <;> simp [hi, hj]

/-- The trace of a singleton basis projector times a matrix is the corresponding diagonal matrix
entry. -/
theorem trace_projector_singleton_mul (b : Fin D) (M : Operator D) :
    Matrix.trace (Projector ({b} : Finset (Fin D)) * M) = M b b := by
  simp [Matrix.trace, Projector]

/-- Sandwiching an operator between a unitary-conjugated basis projector gives that projector
scaled by its trace pairing with the operator. -/
theorem ensembleProjector_conj_eq_trace_smul (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) (A : Operator D) :
    ensembleProjector U o * A * ensembleProjector U o
      = Matrix.trace (ensembleProjector U o * A) • ensembleProjector U o := by
  have key : ensembleProjector U o * A
      = (U o.1)ᴴ * (Projector {o.2} * (U o.1 * A)) := by
    rw [ensembleProjector]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (ensembleProjector U o * A)
      = (U o.1 * A * (U o.1)ᴴ) o.2 o.2 := by
    rw [key, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    exact trace_projector_singleton_mul o.2 _
  calc ensembleProjector U o * A * ensembleProjector U o
      = (U o.1)ᴴ * (Projector {o.2} * (U o.1 * A * (U o.1)ᴴ) * Projector {o.2}) * U o.1 := by
        rw [ensembleProjector]
        simp only [Matrix.mul_assoc]
    _ = (U o.1)ᴴ * (((U o.1 * A * (U o.1)ᴴ) o.2 o.2) • Projector {o.2}) * U o.1 := by
        rw [projector_singleton_conj]
    _ = ((U o.1 * A * (U o.1)ᴴ) o.2 o.2) • ensembleProjector U o := by
        rw [ensembleProjector, Matrix.mul_smul, Matrix.smul_mul]
    _ = Matrix.trace (ensembleProjector U o * A) • ensembleProjector U o := by rw [htr]

/-- The ensemble record Kraus operator obtained by scaling the conjugated basis projector by the
square root of the ensemble probability. -/
noncomputable def ensembleKraus (p : FinDist X) (U : X → Operator D) (o : X × Fin D) :
    Operator D :=
  (Real.sqrt (p.prob o.1) : ℂ) • ensembleProjector U o

/-- The effect of an ensemble record Kraus operator is its conjugated basis projector scaled by
the ensemble probability. -/
theorem ensembleKraus_conj_mul (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) :
    (ensembleKraus p U o)ᴴ * ensembleKraus p U o
      = (p.prob o.1 : ℂ) • ensembleProjector U o := by
  have hs : star (Real.sqrt (p.prob o.1) : ℂ) = (Real.sqrt (p.prob o.1) : ℂ) := by
    simp [Complex.conj_ofReal]
  have hsq : (Real.sqrt (p.prob o.1) : ℂ) * (Real.sqrt (p.prob o.1) : ℂ)
      = (p.prob o.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (p.nonneg o.1)]
  rw [ensembleKraus, Matrix.conjTranspose_smul, hs, ensembleProjector_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, ensembleProjector_idem U hU o]

/-- The effects of all ensemble record Kraus operators sum to the identity for a unitary
ensemble. -/
theorem ensembleKraus_complete (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ∑ o : X × Fin D, (ensembleKraus p U o)ᴴ * ensembleKraus p U o = 1 := by
  calc ∑ o : X × Fin D, (ensembleKraus p U o)ᴴ * ensembleKraus p U o
      = ∑ o : X × Fin D, (p.prob o.1 : ℂ) • ensembleProjector U o :=
        Finset.sum_congr rfl fun o _ => ensembleKraus_conj_mul p U hU o
    _ = ∑ a : X, (p.prob a : ℂ) • (∑ b : Fin D, ensembleProjector U (a, b)) := by
        rw [Fintype.sum_prod_type' (fun a b => (p.prob a : ℂ) • ensembleProjector U (a, b))]
        exact Finset.sum_congr rfl fun a _ => (Finset.smul_sum).symm
    _ = ∑ a : X, (p.prob a : ℂ) • (1 : Operator D) := by
        exact Finset.sum_congr rfl fun a _ => by rw [ensembleProjector_sum_axis U hU a]
    _ = (∑ a : X, (p.prob a : ℂ)) • (1 : Operator D) := Finset.sum_smul.symm
    _ = 1 := by
        rw [← Complex.ofReal_sum, p.sum_one]
        simp

/-- The quantum instrument generated by the complete family of finite ensemble record Kraus
operators. -/
noncomputable def ensembleInstrument (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument (X × Fin D) D D :=
  Instrument.ofKraus (ensembleKraus p U) (ensembleKraus_complete p U hU)

/-- Each branch of the ensemble instrument acts by sandwiching the input with its Kraus operator
and conjugate transpose. -/
theorem ensembleInstrument_branch (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) (A : Operator D) :
    (ensembleInstrument p U hU).branch o A
      = ensembleKraus p U o * A * (ensembleKraus p U o)ᴴ :=
  Instrument.ofKraus_branch _ _ _ _

/-- The finite distribution of ensemble index and measurement outcome obtained from the
instrument on the density state `ρ`. -/
noncomputable def ensembleRecordLaw (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : FinDist (X × Fin D) where
  prob o := instrumentProb (ensembleInstrument p U hU) ρ o
  nonneg o := instrumentProb_nonneg _ hρ.1 o
  sum_one := sum_instrumentProb_isDensityOperator _ hρ

/-- The trace of an ensemble instrument branch equals the ensemble probability times the Born
trace against its conjugated basis projector. -/
theorem ensembleInstrument_trace_branch (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) (o : X × Fin D) :
    Matrix.trace ((ensembleInstrument p U hU).branch o ρ)
      = (p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * ρ) := by
  have hs : star (Real.sqrt (p.prob o.1) : ℂ) = (Real.sqrt (p.prob o.1) : ℂ) := by
    simp [Complex.conj_ofReal]
  have hsq : (Real.sqrt (p.prob o.1) : ℂ) * (Real.sqrt (p.prob o.1) : ℂ)
      = (p.prob o.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (p.nonneg o.1)]
  rw [ensembleInstrument_branch, ensembleKraus, Matrix.conjTranspose_smul, hs]
  calc Matrix.trace ((Real.sqrt (p.prob o.1) : ℂ) • ensembleProjector U o * ρ *
        ((Real.sqrt (p.prob o.1) : ℂ) • (ensembleProjector U o)ᴴ))
      = ((Real.sqrt (p.prob o.1) : ℂ) * (Real.sqrt (p.prob o.1) : ℂ)) •
          Matrix.trace (ensembleProjector U o * ρ * (ensembleProjector U o)ᴴ) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
          Matrix.trace_smul]
    _ = (p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * ρ) := by
        rw [hsq, smul_eq_mul]
        congr 1
        rw [ensembleProjector_conjTranspose, Matrix.trace_mul_cycle,
          ensembleProjector_idem U hU o]

/-- The finite ensemble Kraus family is complete, and each record has probability equal to its
ensemble weight times its Born probability, realizing the measurement model of
[HuangKuengPreskill2020]. -/
theorem finite_ensemble_actual_kraus_born (X : Type) [Fintype X] (D : ℕ) (p : FinDist X)
    (U : X → Operator D) (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ o : X × Fin D, (ensembleKraus p U o)ᴴ * ensembleKraus p U o) = 1 ∧
      ∀ (ρ : Operator D) (hρ : IsDensityOperator ρ) (o : X × Fin D),
        (ensembleRecordLaw p U hU ρ hρ).prob o
          = p.prob o.1 * (Matrix.trace (ensembleProjector U o * ρ)).re := by
  refine ⟨ensembleKraus_complete p U hU, fun ρ hρ o => ?_⟩
  show instrumentProb (ensembleInstrument p U hU) ρ o = _
  rw [instrumentProb, ensembleInstrument_trace_branch p U hU ρ o]
  simp [Complex.mul_re]

/-- The complex linear measurement map summing conjugated basis projectors weighted by their
trace pairings and ensemble probabilities. -/
noncomputable def ensembleMeasurementMap (p : FinDist X) (U : X → Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun A := ∑ o : X × Fin D,
    ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * A)) • ensembleProjector U o
  map_add' A B := by
    have h : ∀ o : X × Fin D,
        ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * (A + B))) •
            ensembleProjector U o
          = ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * A)) •
              ensembleProjector U o
            + ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * B)) •
                ensembleProjector U o :=
      fun o => by rw [Matrix.mul_add, Matrix.trace_add, mul_add, add_smul]
    rw [Finset.sum_congr rfl fun o _ => h o, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [smul_smul]
    congr 1
    ring

/-- The ensemble measurement map evaluates to its defining weighted sum of trace-paired
projectors. -/
theorem ensembleMeasurementMap_apply (p : FinDist X) (U : X → Operator D) (A : Operator D) :
    ensembleMeasurementMap p U A = ∑ o : X × Fin D,
      ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * A)) • ensembleProjector U o :=
  rfl

/-- Forgetting the classical outcome of the ensemble instrument gives `ensembleMeasurementMap`. -/
theorem ensembleInstrument_forget_map (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (ensembleInstrument p U hU).forget.map = ensembleMeasurementMap p U := by
  apply LinearMap.ext
  intro A
  rw [Instrument.forget_apply, ensembleMeasurementMap_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [ensembleInstrument_branch, ensembleKraus, Matrix.conjTranspose_smul]
  have hs : star (Real.sqrt (p.prob o.1) : ℂ) = (Real.sqrt (p.prob o.1) : ℂ) := by
    simp [Complex.conj_ofReal]
  have hsq : (Real.sqrt (p.prob o.1) : ℂ) * (Real.sqrt (p.prob o.1) : ℂ)
      = (p.prob o.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (p.nonneg o.1)]
  rw [hs, ensembleProjector_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, hsq, ensembleProjector_conj_eq_trace_smul U hU o A,
    smul_smul]

/-- The measurement map of a unitary ensemble sends the identity to the identity. -/
theorem ensembleMeasurementMap_one (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ensembleMeasurementMap p U 1 = 1 := by
  calc ensembleMeasurementMap p U 1
      = ∑ o : X × Fin D, (p.prob o.1 : ℂ) • ensembleProjector U o := by
        rw [ensembleMeasurementMap_apply]
        exact Finset.sum_congr rfl fun o _ => by
          rw [Matrix.mul_one, ensembleProjector_trace U hU o, mul_one]
    _ = ∑ a : X, (p.prob a : ℂ) • (∑ b : Fin D, ensembleProjector U (a, b)) := by
        rw [Fintype.sum_prod_type' (fun a b => (p.prob a : ℂ) • ensembleProjector U (a, b))]
        exact Finset.sum_congr rfl fun a _ => (Finset.smul_sum).symm
    _ = ∑ a : X, (p.prob a : ℂ) • (1 : Operator D) := by
        exact Finset.sum_congr rfl fun a _ => by rw [ensembleProjector_sum_axis U hU a]
    _ = (∑ a : X, (p.prob a : ℂ)) • (1 : Operator D) := Finset.sum_smul.symm
    _ = 1 := by
        rw [← Complex.ofReal_sum, p.sum_one]
        simp

/-- The ensemble measurement map is symmetric for the bilinear trace pairing. -/
theorem ensembleMeasurementMap_trace_adjoint (p : FinDist X) (U : X → Operator D)
    (A B : Operator D) :
    Matrix.trace (A * ensembleMeasurementMap p U B)
      = Matrix.trace (ensembleMeasurementMap p U A * B) := by
  rw [ensembleMeasurementMap_apply, ensembleMeasurementMap_apply, Matrix.mul_sum,
    Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm A (ensembleProjector U o)]
  ring

/-- The forgotten ensemble instrument is the unital measurement map, and that map is symmetric
for the trace pairing, as used in the shadow construction of [HuangKuengPreskill2020]. -/
theorem finite_ensemble_measurement_channel_and_trace_adjoint (X : Type) [Fintype X] (D : ℕ)
    (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (ensembleInstrument p U hU).forget.map = ensembleMeasurementMap p U ∧
      ensembleMeasurementMap p U 1 = 1 ∧
      ∀ A B : Operator D,
        Matrix.trace (A * ensembleMeasurementMap p U B)
          = Matrix.trace (ensembleMeasurementMap p U A * B) :=
  ⟨ensembleInstrument_forget_map p U hU, ensembleMeasurementMap_one p U hU,
    ensembleMeasurementMap_trace_adjoint p U⟩

/-- The observed circuit that applies `U`, measures in the computational basis, applies `Uᴴ`,
and accepts. -/
noncomputable def ensembleAxisProgram {D : ℕ} (U : Operator D) : ObservedCircuit (Fin D) :=
  .step (.gate U) (.measure D id (fun _ => .step (.gate Uᴴ) (.halt true)))

/-- The observed basis-measurement circuit has one leaf per basis outcome, with operator `Uᴴ *
Projector {b} * U`, two gates, one measurement, no queries, and the recorded outcome. -/
theorem ensembleAxis_actual_leaves {D : ℕ} (U : Operator D) :
    observedKrausLeaves 1 (ensembleAxisProgram U) = List.ofFn (fun b : Fin D =>
      (⟨Uᴴ * Projector {b} * U, true, 0, 2, 1, [(D,b.val)]⟩ : ObservedKrausLeaf D)) := by
  have hflat {α : Type} (f : Fin D → α) : (List.ofFn (fun b => [f b])).flatten = List.ofFn f := by
    change (List.ofFn ((fun x : α => [x]) ∘ f)).flatten = List.ofFn f
    rw [← List.map_ofFn]
    have h {α : Type} (xs : List α) : (xs.map (fun x => [x])).flatten = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih]
    exact h _
  simp only [ensembleAxisProgram, observedKrausLeaves, List.map_cons, List.map_nil,
    ObservedKrausLeaf.prepend, Matrix.one_mul, Nat.zero_add]
  rw [hflat, List.map_ofFn]
  congr 1
  funext b
  have hs : (Finset.univ.filter (fun x : Fin D => x = b)) = {b} := by
    ext x
    simp
  simp [ObservedKrausLeaf.prepend, hs]

/-- The observed Kraus leaf selected by basis outcome `b` in `ensembleAxisProgram U`. -/
noncomputable def ensembleAxisLeaf {D : ℕ} (U : Operator D) (b : Fin D) : ObservedKrausLeaf D :=
  (observedKrausLeaves 1 (ensembleAxisProgram U)).getD b.val ⟨0,false,0,0,0,[]⟩

/-- The leaf at basis outcome `b` has the conjugated projector operator, accepts, uses two gates
and one measurement, and records `(D, b.val)`. -/
theorem ensembleAxisLeaf_eq {D : ℕ} (U : Operator D) (b : Fin D) :
    ensembleAxisLeaf U b = ⟨Uᴴ * Projector {b} * U, true, 0, 2, 1, [(D,b.val)]⟩ := by
  rw [ensembleAxisLeaf, ensembleAxis_actual_leaves]
  simp

/-- The ensemble axis program is well formed when its basis-change matrix is unitary. -/
theorem ensembleAxisProgram_wellFormed (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : observedWellFormed (ensembleAxisProgram U) := by
  refine ⟨hU, fun _ => ⟨?_, trivial⟩⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

/-- An ensemble Kraus operator is its actual observed leaf operator scaled by the square root of
the ensemble probability. -/
theorem ensembleKraus_actual_leaf_bridge (p : FinDist X) (U : X → Operator D)
    (o : X × Fin D) : ensembleKraus p U o =
      (Real.sqrt (p.prob o.1) : ℂ) • (ensembleAxisLeaf (U o.1) o.2).operator := by
  rw [ensembleAxisLeaf_eq]
  rfl

/-- The tuple counting fresh records, gates, measurements, and queries in the observed leaves of
a record sequence. -/
noncomputable def ensembleFreshResourceCounts (U : X → Operator D) {m : ℕ}
    (ω : Fin m → X × Fin D) : ℕ × ℕ × ℕ × ℕ :=
  let leaves := List.ofFn fun i => ensembleAxisLeaf (U (ω i).1) (ω i).2
  (leaves.length, (leaves.map (fun l => l.gates)).sum,
    (leaves.map (fun l => l.measurements)).sum, (leaves.map (fun l => l.queries)).sum)

/-- A sequence of `m` ensemble records uses `m` fresh records, `2*m` gates, `m` measurements,
and zero queries. -/
theorem ensembleFreshResourceCounts_spec (U : X → Operator D) {m : ℕ}
    (ω : Fin m → X × Fin D) : ensembleFreshResourceCounts U ω = (m, 2*m, m, 0) := by
  simp [ensembleFreshResourceCounts, ensembleAxisLeaf_eq, List.map_ofFn,
    List.sum_ofFn, Nat.mul_comm]

/-- Each ensemble instrument branch is the Kraus action of the actual observed leaf operator
scaled by the square root of its ensemble probability. -/
theorem ensembleInstrument_actual_branch (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (o : X × Fin D) (A : Operator D) :
    (ensembleInstrument p U hU).branch o A =
      ((Real.sqrt (p.prob o.1) : ℂ) • (ensembleAxisLeaf (U o.1) o.2).operator) * A *
      ((Real.sqrt (p.prob o.1) : ℂ) • (ensembleAxisLeaf (U o.1) o.2).operator)ᴴ := by
  rw [ensembleInstrument_branch, ensembleKraus_actual_leaf_bridge]

/-- Across `K` groups of `L` ensemble records, the total fresh-record, gate, measurement, and
query counts are `K*L`, `2*(K*L)`, `K*L`, and zero. -/
theorem ensemble_grouped_actual_resources (U : X → Operator D) {L K : ℕ}
    (ω : Fin K → Fin L → X × Fin D) :
    (∑ b, (ensembleFreshResourceCounts U (ω b)).1) = K*L ∧
    (∑ b, (ensembleFreshResourceCounts U (ω b)).2.1) = 2*(K*L) ∧
    (∑ b, (ensembleFreshResourceCounts U (ω b)).2.2.1) = K*L ∧
    (∑ b, (ensembleFreshResourceCounts U (ω b)).2.2.2) = 0 := by
  simp [ensembleFreshResourceCounts_spec]
  ring

end Qatlib.Concepts.ShadowModels.ShadowChannel
