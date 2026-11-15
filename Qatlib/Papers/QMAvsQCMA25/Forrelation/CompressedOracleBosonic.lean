/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

/-- A finite sum splits into the term at a chosen member and the sum over the remaining
elements. -/
private theorem Finset.sum_eq_add_sum_diff_singleton {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {s : Finset α} (i : α) (f : α → β) (h : i ∈ s) :
    ∑ x ∈ s, f x = f i + ∑ x ∈ s \ {i}, f x := by
  rw [Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ h]
set_option maxHeartbeats 800000
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Papers.QMAvsQCMA25.Forrelation Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic

open Matrix
open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib
open Qatlib
open Qatlib.Concepts.FreshFallback.BitScanLedger
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- A value collision implies that two distinct indices belong to the valued database support. -/
theorem valueCollision_twoOccupied {I V : Type} [Fintype I] [DecidableEq I]
    (db : ValuedDatabase I V) (h : valueCollision db) :
    ∃ x y : I, x ≠ y ∧ x ∈ valuedSupport db ∧ y ∈ valuedSupport db := by
  obtain ⟨x, y, hxy, v, hx, hy⟩ := h
  exact ⟨x, y, hxy, by simp [valuedSupport, hx], by simp [valuedSupport, hy]⟩

def twoDistinctValues : ValuedDatabase (Fin 2) Bool :=
  fun x => if x = 0 then some false else some true

/-- The database `twoDistinctValues` has support cardinality two. -/
theorem twoDistinctValues_occupied :
    (valuedSupport twoDistinctValues).card = 2 := by
  classical
  decide

/-- The database `twoDistinctValues` has no value collision. -/
theorem twoDistinctValues_noCollision : ¬ valueCollision twoDistinctValues := by
  rintro ⟨x, y, hxy, v, hx, hy⟩
  have hxl : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by omega
  have hyl : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by omega
  rcases hxl with hx0 | hx1 <;> rcases hyl with hy0 | hy1
  · exact hxy (Fin.ext (by omega))
  · have hx0' : x = 0 := Fin.ext hx0
    have hy1' : y = 1 := Fin.ext hy1
    simp [twoDistinctValues, hx0', hy1'] at hx hy
    simp_all
  · have hx1' : x = 1 := Fin.ext hx1
    have hy0' : y = 0 := Fin.ext hy0
    simp [twoDistinctValues, hx1', hy0'] at hx hy
    simp_all
  · exact hxy (Fin.ext (by omega))

def sameValueEverywhere : ValuedDatabase (Fin 2) Bool := fun _ => some true

/-- The database `sameValueEverywhere` has a value collision. -/
theorem sameValueEverywhere_collision : valueCollision sameValueEverywhere := by
  refine ⟨0, 1, ?_, true, rfl, rfl⟩
  intro h
  exact absurd h (by decide)

/-- The value recorded at a new element is not recorded at any other index. -/
theorem newElement_unique {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    (db : ValuedDatabase I V) (x : I) (v : V) (h : newElement db x v) :
    ∀ y, y ≠ x → db y ≠ some v := h.2

/-- A new element belongs to the valued database support. -/
theorem newElement_occupied {I V : Type} [Fintype I] [DecidableEq I]
    (db : ValuedDatabase I V) (x : I) (v : V) (h : newElement db x v) :
    x ∈ valuedSupport db := by
  simp [valuedSupport, h.1]

/-- Converting a Boolean database to a valued database preserves its support. -/
theorem booleanValuedDatabase_support {I : Type} [Fintype I] [DecidableEq I]
    (d : I → Bool) :
    valuedSupport (booleanValuedDatabase d) = databaseSupport d := by
  ext x
  simp [valuedSupport, booleanValuedDatabase, databaseSupport]

/-- Fock creation increases the occupation at the chosen mode by one and leaves every other
occupation unchanged. -/
theorem fockCreation_occupation {N : ℕ} (x : Fin N) (v : Fin N → ℕ) :
    fockCreation x v x = v x + 1 ∧ ∀ y, y ≠ x → fockCreation x v y = v y := by
  constructor
  · simp [fockCreation]
  · intro y hy
    simp [fockCreation, hy]

/-- Fock creation increases the total occupation by one. -/
theorem fockCreation_total {N : ℕ} (x : Fin N) (v : Fin N → ℕ) :
    (∑ y ∈ (Finset.univ : Finset (Fin N)), fockCreation x v y)
      = (∑ y ∈ (Finset.univ : Finset (Fin N)), v y) + 1 := by
  have hmain : (∑ y ∈ (Finset.univ : Finset (Fin N)), fockCreation x v y) = fockCreation x v x +
      ∑ y ∈ ((Finset.univ : Finset (Fin N)).erase x), fockCreation x v y := by
    rw [← Finset.sdiff_singleton_eq_erase]
    exact Finset.sum_eq_add_sum_diff_singleton x (fun y => fockCreation x v y) (by simp)
  have heq : (∑ y ∈ ((Finset.univ : Finset (Fin N)).erase x), fockCreation x v y)
      = ∑ y ∈ ((Finset.univ : Finset (Fin N)).erase x), v y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hne : y ≠ x := (Finset.mem_erase.mp hy).1
    exact (fockCreation_occupation x v).2 y hne
  have hsplit : (∑ y ∈ (Finset.univ : Finset (Fin N)), v y)
      = v x + ∑ y ∈ ((Finset.univ : Finset (Fin N)).erase x), v y := by
    rw [← Finset.sdiff_singleton_eq_erase]
    exact Finset.sum_eq_add_sum_diff_singleton x (fun y => v y) (by simp)
  rw [hmain, heq, (fockCreation_occupation x v).1]
  omega

/-- The total occupation of a query schedule equals its length. -/
theorem scheduleOccupation_total {N : ℕ} (sch : QuerySchedule N) :
    (∑ x : Fin N, scheduleOccupation sch x) = sch.length := by
  induction sch with
  | nil => simp [scheduleOccupation, listCount]
  | cons a sch ih =>
      have hcount (x : Fin N) :
          scheduleOccupation (a :: sch) x =
            (if x = a then 1 else 0) + scheduleOccupation sch x := by
        show (if a = x then 1 else 0) + listCount x sch = (if x = a then 1 else 0) + listCount x sch
        by_cases hx : x = a
        · subst hx
          simp
        · simp [hx, Ne.symm hx]
      have hone : ∑ x : Fin N, (if x = a then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd h (by simp)
      calc (∑ x : Fin N, scheduleOccupation (a :: sch) x)
          = ∑ x : Fin N, ((if x = a then 1 else 0) + scheduleOccupation sch x) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              exact hcount x
        _ = (∑ x : Fin N, (if x = a then 1 else 0))
            + ∑ x : Fin N, scheduleOccupation sch x := by
              rw [Finset.sum_add_distrib]
        _ = 1 + sch.length := by rw [hone, ih]
        _ = (a :: sch).length := by simp [Nat.add_comm]

/-- A mode appearing in a query schedule has occupation at least one. -/
theorem scheduleOccupation_mem {N : ℕ} (sch : QuerySchedule N) (x : Fin N)
    (hx : x ∈ sch) : 1 ≤ scheduleOccupation sch x := by
  induction sch with
  | nil => simp at hx
  | cons a sch ih =>
      show 1 ≤ (if a = x then 1 else 0) + listCount x sch
      by_cases ha : a = x
      · simp [ha]
      · have hmem : x ∈ sch := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h (Ne.symm ha)
          · exact h
        have h := ih hmem
        simpa [ha] using! h

/-- The occupation of any mode is at most the schedule length. -/
theorem scheduleOccupation_le {N : ℕ} (sch : QuerySchedule N) (x : Fin N) :
    scheduleOccupation sch x ≤ sch.length := by
  induction sch with
  | nil => simp [scheduleOccupation, listCount]
  | cons a sch ih =>
      show (if a = x then 1 else 0) + listCount x sch ≤ (a :: sch).length
      have h := ih
      simp [scheduleOccupation] at h
      by_cases ha : a = x
      · simp [ha]
        omega
      · simp [ha]
        omega

/-- Conjugating the Forrelation phase oracle for `S` by the control Hadamard gives the
corresponding bit oracle. -/
theorem forrConjugateUpdate (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    controlHadamard (I := Reg n) (W := (Reg n × Bool) × W) *
        forrPhaseOracleS n S W * controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)
      = forrBitOracleS n S W := by
  simpa [forrPhaseOracleS, forrBitOracleS, workspacePhaseOracle, workspaceBitOracle] using!
    (controlHadamard_mul_phase_mul_controlHadamard
      (I := Reg n) (W := (Reg n × Bool) × W) S)

/-- For `p` between zero and one, each decompressed XOR amplitude factors as a Bernoulli
amplitude times the corresponding workspace bit-oracle execution amplitude. -/
theorem databaseXor_stateTransport (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q : (I × Bool) × W) (x : I → Bool) :
    decompressedXorRun p C ψ (q, x) =
      bernoulliState p x * Run (workspaceBitOracle x) C ψ q :=
  databaseXor_fullstate p hp0 hp1 C ψ q x

/-- The database XOR marginal equals the Bernoulli-weighted mixture of workspace bit-oracle
output outer products. -/
theorem databaseXor_workspaceTransport (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q q' : (I × Bool) × W) :
    databaseXorMarginal p C ψ q q' =
      ∑ x : I → Bool, bernoulliPmf p x * Run (workspaceBitOracle x) C ψ q *
        star (Run (workspaceBitOracle x) C ψ q') :=
  databaseXor_marginal p hp0 hp1 C ψ q q'

/-- The distance from a complex unit phase to one is twice the absolute sine of its half-angle. -/
theorem abs_exp_sub_one_I (a : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - 1‖ = 2 * |Real.sin (a / 2)| := by
  have hexp : Complex.exp (Complex.I * (a : ℂ))
      = (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.exp_re]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.ofReal_re, Complex.cos_ofReal_re]
    · rw [Complex.exp_im]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.ofReal_im, Complex.sin_ofReal_re]
  have htrig : (Real.cos a - 1) ^ 2 + Real.sin a ^ 2 = 4 * Real.sin (a / 2) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq a
    have h2 := Real.sin_sq_add_cos_sq (a / 2)
    have h3' : Real.cos a = 2 * Real.cos (a / 2) ^ 2 - 1 := by
      have h3 := Real.cos_two_mul (a / 2)
      rwa [show 2 * (a / 2) = a by ring] at h3
    nlinarith [h1, h2, h3']
  rw [hexp]
  have hsq : ‖((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - 1)‖ ^ 2
      = (2 * |Real.sin (a / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    have hform : (Real.cos a - 1) * (Real.cos a - 1) + Real.sin a * Real.sin a
        = (Real.cos a - 1) ^ 2 + Real.sin a ^ 2 := by ring
    rw [hform, htrig]
    rw [mul_pow, sq_abs]
    ring
  have hz : 0 ≤ ‖((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I - 1)‖ := norm_nonneg _
  have hs : 0 ≤ 2 * |Real.sin (a / 2)| := by positivity
  nlinarith [hsq]

/-- The phase displacement after multiplying an angle by a natural number is twice the absolute
sine of the resulting half-angle. -/
theorem abs_exp_sub_one_I_nat (θ : ℝ) (m : ℕ) :
    ‖Complex.exp (Complex.I * (θ * m : ℝ)) - 1‖ = 2 * |Real.sin (θ * m / 2)| := by
  simpa [Complex.ofReal_mul] using! (abs_exp_sub_one_I (θ * m))

/-- The norm of a diagonal entry of the bosonic phase oracle minus the identity equals the phase
deviation at that mode's occupation. -/
theorem bosonicPhaseDeviation_entry (N t : ℕ) (θ : ℝ) (x : Fin N) (v : FockBasis N t) :
    ‖(bosonicPhaseOracleBlock N t θ x - 1) v v‖
      = bosonicPhaseDeviation θ (v.1 x : ℕ) := by
  have hexp : Complex.I * θ * ((v.1 x : ℕ) : ℂ)
      = Complex.I * ((θ * (v.1 x : ℕ) : ℝ) : ℂ) := by
    rw [mul_assoc]
    congr 1
    simp
  rw [bosonicPhaseOracleBlock, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.one_apply]
  simp only [ite_true]
  rw [hexp, abs_exp_sub_one_I_nat]
  rfl

/-- For every mode and Fock basis state, the distance of its bosonic phase from one equals
`bosonicPhaseDeviation` at that mode's occupation. -/
theorem bosonicActionNormBound_holds (N t : ℕ) (θ : ℝ) : BosonicActionNormBound N t θ := by
  intro x v
  have hexp : Complex.I * θ * ((v.1 x : ℕ) : ℂ)
      = Complex.I * ((θ * (v.1 x : ℕ) : ℝ) : ℂ) := by
    rw [mul_assoc]
    congr 1
    simp
  rw [hexp, abs_exp_sub_one_I_nat]
  rfl

/-- The bosonic multi-query bound starts at one and is multiplied by `bosonicPerQueryNorm` at
each successive query. -/
theorem bosonicMultiQueryRecurrence_holds (θ : ℝ) : bosonicMultiQueryRecurrence θ := by
  constructor
  · simp [bosonicMultiQueryBound, bosonicPerQueryNorm]
  · intro t
    simp [bosonicMultiQueryBound, bosonicPerQueryNorm]
    ring

/-- A diagonal entry of the product of two diagonal matrices is the product of their
corresponding entries. -/
private theorem mul_diagonal_apply {α : Type} [Fintype α] [DecidableEq α]
    (d e : α → ℂ) (u : α) :
    (Matrix.diagonal d * Matrix.diagonal e) u u = d u * e u := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u]
  · simp []
  · intro k _ hk
    simp [Matrix.diagonal_apply, hk]
  · intro h
    exact absurd h (by simp)

/-- The quasi-even condensate projector equals the product of the condensate and quasi-even
projectors. -/
theorem qec_eq_con_mul_qe (n ℓ r o : ℕ) :
    qecProjector n ℓ r o = conProjector n ℓ r * qeProjector n ℓ o := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [qecProjector, conProjector, qeProjector]
    rw [mul_diagonal_apply]
    by_cases hc : condensate n ℓ r p
    · by_cases hq : quasiEven n ℓ o p
      · simp [
          quasiEvenCondensate, hc, hq]
      · simp [
          quasiEvenCondensate, hc, hq]
    · simp [
        quasiEvenCondensate, hc]
  · rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [qecProjector, conProjector, qeProjector, hpq]
    · intro k _ hk
      have hne : p ≠ k := Ne.symm hk
      have hne' : k ≠ p := hk
      simp [conProjector, qeProjector, Matrix.diagonal_apply, hne]
    · intro h
      exact absurd h (by simp)

/-- The quasi-even condensate projector commutes with the quasi-even projector. -/
theorem qec_commutes_qe (n ℓ r o : ℕ) :
    qecProjector n ℓ r o * qeProjector n ℓ o = qeProjector n ℓ o * qecProjector n ℓ r o := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [qecProjector, qeProjector]
    rw [mul_diagonal_apply, mul_diagonal_apply]
    ring
  · rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [qecProjector, qeProjector, hpq]
    · intro k _ hk
      have hne : p ≠ k := Ne.symm hk
      have hne' : k ≠ p := hk
      simp [qecProjector, qeProjector, Matrix.diagonal_apply, hne]
    · intro h
      exact absurd h (by simp)

/-- The real diagonal entry of the occupied-mode projector is bounded by the corresponding
number-operator entry. -/
theorem fockOccupied_le_fockNumber {N t : ℕ} (x : Fin N) (v : FockBasis N t) :
    (fockOccupied N t x v v).re ≤ (fockNumber N t x v v).re := by
  by_cases hz : v.1 x = 0
  · simp [fockOccupied, fockNumber, Matrix.of_apply, hz]
  · have hne : (v.1 x : ℕ) ≠ 0 := by
      intro h
      exact hz (Fin.ext h)
    have hpos : 1 ≤ (v.1 x : ℕ) := by omega
    simpa [fockOccupied, fockNumber, Matrix.of_apply, hz, Complex.ofReal_re] using! hpos

/-- The joint occupation indicator for guessed modes is bounded by the product of their
occupation numbers. -/
theorem fockGuessesOccupied_le_numberProduct {N t v : ℕ} (z : Fin v → Fin N)
    (w : FockBasis N t) :
    (fockGuessesOccupied z w w).re ≤ ∏ i, (fockNumber N t (z i) w w).re := by
  have hnonneg : 0 ≤ ∏ i, (fockNumber N t (z i) w w).re := by
    apply Finset.prod_nonneg
    intro i _
    simp [fockNumber, Matrix.of_apply]
  by_cases hall : ∀ i, w.1 (z i) ≠ 0
  · have hle : 1 ≤ ∏ i, (fockNumber N t (z i) w w).re := by
      apply Finset.one_le_prod₀
      intro i _
      have hne : (w.1 (z i) : ℕ) ≠ 0 := by
        intro h
        exact hall i (Fin.ext h)
      have hpos : 1 ≤ (w.1 (z i) : ℕ) := by omega
      simpa [fockNumber, Matrix.of_apply, Complex.ofReal_re] using! hpos
    simpa [fockGuessesOccupied, Matrix.of_apply, hall, Complex.ofReal_re] using! hle
  · simpa [fockGuessesOccupied, Matrix.of_apply, hall, Complex.ofReal_re] using! hnonneg

/-- The total momentum occupation of a basis state equals its particle number. -/
theorem momentumOccupation_total {n ℓ : ℕ} (u : MomentumBasis n ℓ) :
    (∑ y : Reg n, momentumOccupation u y) = ℓ := by
  simpa [momentumOccupation] using! u.property

/-- In a condensate basis state, each nonzero mode has occupation at most `r`. -/
theorem momentumOccupation_le_condensate {n ℓ r : ℕ} (u : MomentumBasis n ℓ)
    (h : condensate n ℓ r u) (x : Reg n) (hx : x ≠ zeroMode n) :
    momentumOccupation u x ≤ r := by
  have htotal : (∑ y ∈ (Finset.univ : Finset (Reg n)), momentumOccupation u y) = ℓ := by
    simpa [momentumOccupation] using! u.property
  have hsplit : (∑ y ∈ (Finset.univ : Finset (Reg n)), momentumOccupation u y)
      = momentumOccupation u (zeroMode n)
        + ∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)), momentumOccupation u y := by
    rw [← Finset.sdiff_singleton_eq_erase]
    exact Finset.sum_eq_add_sum_diff_singleton (zeroMode n)
      (fun y => momentumOccupation u y) (by simp)
  have hmem : x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n) := by
    simp [hx]
  have hle : momentumOccupation u x
      ≤ ∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)), momentumOccupation u y := by
    have hsplit2 : (∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)),
          momentumOccupation u y)
        = momentumOccupation u x
          + ∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)) \ {x},
            momentumOccupation u y := by
      exact Finset.sum_eq_add_sum_diff_singleton x
        (fun y => momentumOccupation u y) (by simp [hx])
    rw [hsplit2]
    exact Nat.le_add_right _ _
  have hrest : ℓ ≤ momentumOccupation u (zeroMode n) + r := h
  have hcomb : momentumOccupation u (zeroMode n)
      + (∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)), momentumOccupation u y) = ℓ := by
    rw [← hsplit, htotal]
  have hrest' : (∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)),
      momentumOccupation u y) ≤ r := by
    omega
  exact hle.trans hrest'

/-- An injective guess map can assign the zero mode to at most one index. -/
private theorem zeroModeGuess_unique {n v : ℕ} {z : Fin v → Reg n}
    (hz : Function.Injective z) (i j : Fin v)
    (hi : z i = zeroMode _) (hj : z j = zeroMode _) : i = j :=
  hz (hi.trans hj.symm)

/-- For an injective list of modes in a condensate, the occupation product is bounded by the
particle number times the indicated power of `r`. -/
theorem occupationProduct_le {n ℓ v r : ℕ} (u : MomentumBasis n ℓ)
    (h : condensate n ℓ r u) (hr : 1 ≤ r) (hrℓ : r ≤ ℓ)
    (z : Fin v → Reg n) (hz : Function.Injective z) :
    (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ)) ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  have hzero : momentumOccupation u (zeroMode n) ≤ ℓ := by
    have htotal : (∑ y ∈ (Finset.univ : Finset (Reg n)), momentumOccupation u y) = ℓ := by
      simpa [momentumOccupation] using! u.property
    have hsplit : (∑ y ∈ (Finset.univ : Finset (Reg n)), momentumOccupation u y)
        = momentumOccupation u (zeroMode n)
          + ∑ y ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)), momentumOccupation u y := by
      rw [← Finset.sdiff_singleton_eq_erase]
      exact Finset.sum_eq_add_sum_diff_singleton (zeroMode n)
        (fun y => momentumOccupation u y) (by simp)
    omega
  by_cases hex : ∃ i, z i = zeroMode n
  · obtain ⟨i₀, hi₀⟩ := hex
    have huniq : ∀ i, z i = zeroMode n → i = i₀ := by
      intro i hi
      exact zeroModeGuess_unique hz i i₀ hi hi₀
    have hpoint : ∀ i, (momentumOccupation u (z i) : ℝ)
        ≤ if i = i₀ then (ℓ : ℝ) else (r : ℝ) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        rw [hi₀]
        simp only [ite_true]
        exact Nat.cast_le.2 hzero
      · have hzi : z i ≠ zeroMode n := by
          intro hc
          exact hi (huniq i hc)
        simp only [ite_eq_right hi]
        have hle := momentumOccupation_le_condensate u h (z i) hzi
        exact_mod_cast hle
    have hprod : (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ))
        ≤ ∏ i ∈ (Finset.univ : Finset (Fin v)), (if i = i₀ then (ℓ : ℝ) else (r : ℝ)) := by
      refine Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => hpoint i)
    have heval : (∏ i ∈ (Finset.univ : Finset (Fin v)), (if i = i₀ then (ℓ : ℝ) else (r : ℝ)))
        = (r : ℝ) ^ (v - 1) * (ℓ : ℝ) := by
      have hmain := Finset.prod_erase_mul (Finset.univ : Finset (Fin v))
        (fun i => if i = i₀ then (ℓ : ℝ) else (r : ℝ)) (Finset.mem_univ i₀)
      rw [← hmain]
      simp only [ite_true]
      have hcard : ((Finset.univ : Finset (Fin v)).erase i₀).card = v - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀)]
        simp
      have hinner : (∏ x ∈ ((Finset.univ : Finset (Fin v)).erase i₀),
          (if x = i₀ then (ℓ : ℝ) else (r : ℝ))) = (r : ℝ) ^ (v - 1) := by
        rw [Finset.prod_congr rfl (fun x hx => ?_), Finset.prod_const, hcard]
        have hne : x ≠ i₀ := (Finset.mem_erase.mp hx).1
        simp [hne]
      rw [hinner]
    calc (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ))
        ≤ ∏ i ∈ (Finset.univ : Finset (Fin v)), (if i = i₀ then (ℓ : ℝ) else (r : ℝ)) := hprod
      _ = (r : ℝ) ^ (v - 1) * (ℓ : ℝ) := heval
      _ = (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by ring
  · have hpoint : ∀ i, (momentumOccupation u (z i) : ℝ) ≤ (r : ℝ) := by
      intro i
      have hzi : z i ≠ zeroMode n := by
        intro hc
        exact hex ⟨i, hc⟩
      have hle : momentumOccupation u (z i) ≤ r :=
        momentumOccupation_le_condensate (n := n) (ℓ := ℓ) (r := r) u h (z i) hzi
      exact Nat.cast_le.2 hle
    have hprod : (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ)) ≤ (r : ℝ) ^ v := by
      have hle : (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ)) ≤ ∏ i ∈ (Finset.univ : Finset (Fin v)), (r : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity)
          (fun i _ => hpoint i)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
      exact hle
    calc (∏ i ∈ (Finset.univ : Finset (Fin v)), (momentumOccupation u (z i) : ℝ)) ≤ (r : ℝ) ^ v := hprod
      _ ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
          by_cases hv : v = 0
          · simp [hv]
            omega
          · have hvt : v = (v - 1) + 1 :=
              (Nat.sub_add_cancel (Nat.pos_of_ne_zero hv)).symm
            have hpow : (r : ℝ) ^ v = (r : ℝ) * (r : ℝ) ^ (v - 1) := by
              conv_lhs => rw [hvt]
              exact pow_succ' (r : ℝ) (v - 1)
            rw [hpow]
            have hr' : (r : ℝ) ≤ (ℓ : ℝ) := Nat.cast_le.2 hrℓ
            exact mul_le_mul_of_nonneg_right hr' (pow_nonneg (Nat.cast_nonneg r) _)

/-- The product of two diagonal matrices is diagonal with pointwise multiplied entries. -/
theorem diagonal_mul_diagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (e d : ι → ℂ) :
    (Matrix.diagonal e : Matrix ι ι ℂ) * (Matrix.diagonal d : Matrix ι ι ℂ)
      = Matrix.diagonal (fun i => e i * d i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd h (by simp)
  · rw [Matrix.mul_apply]
    have hRHS : (Matrix.diagonal (fun i => e i * d i) : Matrix ι ι ℂ) i j = 0 := by
      simp [hij]
    rw [hRHS]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hik : i = k
    · have hkj : ¬ (k = j) := fun hkj => hij (hik.trans hkj)
      simp [hik, hkj]
    · simp [hik]

/-- The full quasi-even condensate projector is the diagonal indicator of the quasi-even
condensate condition. -/
theorem qecProjectorFull_eq_diagonal (n ℓ r o v : ℕ) :
    qecProjectorFull n ℓ r o v =
      Matrix.diagonal (fun p => if quasiEvenCondensate n ℓ r o p.2 then 1 else 0) := rfl

/-- The full success operator is diagonal with entries given by `lambdaSuccWeight`. -/
theorem lambdaSuccFull_eq_diagonal (n ℓ v : ℕ) :
    lambdaSuccFull n ℓ v =
      Matrix.diagonal (fun p => Complex.ofReal (lambdaSuccWeight n ℓ v p.1 p.2)) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [lambdaSuccFull]
  · have hne : ¬ (p.1 = q.1 ∧ p.2 = q.2) := by
      intro h
      apply hpq
      exact Prod.ext h.1 h.2
    simp [lambdaSuccFull, hne, hpq]

/-- Sandwiching the success operator by the quasi-even condensate projector multiplies each
success weight by the corresponding indicator on both sides. -/
theorem qec_lambdaSucc_qec_eq_diagonal (n ℓ v r o : ℕ) :
    qecProjectorFull n ℓ r o v * lambdaSuccFull n ℓ v * qecProjectorFull n ℓ r o v
      = Matrix.diagonal (fun p =>
          (if quasiEvenCondensate n ℓ r o p.2 then 1 else 0) *
            Complex.ofReal (lambdaSuccWeight n ℓ v p.1 p.2) *
            (if quasiEvenCondensate n ℓ r o p.2 then 1 else 0)) := by
  rw [qecProjectorFull_eq_diagonal, lambdaSuccFull_eq_diagonal]
  simp only [diagonal_mul_diagonal]

/-- Every success weight `lambdaSuccWeight` is nonnegative. -/
theorem lambdaSuccWeight_nonneg (n ℓ v : ℕ) (z : GuessSpace n v)
    (u : MomentumBasis n ℓ) : 0 ≤ lambdaSuccWeight n ℓ v z u := by
  by_cases hinj : Function.Injective z
  · have h : lambdaSuccWeight n ℓ v z u
      = ∏ i, (momentumOccupation u (z i) : ℝ) := by
      simp [lambdaSuccWeight, hinj]
    rw [h]
    exact Finset.prod_nonneg fun i _ => by positivity
  · have h : lambdaSuccWeight n ℓ v z u = 0 := by
      simp [lambdaSuccWeight, hinj]
    rw [h]

/-- On quasi-even condensates, the absolute success weight is bounded by the particle number
times the indicated power of `r`. -/
theorem lambdaSuccWeight_le {n ℓ v r o : ℕ} (hr : 1 ≤ r) (hrℓ : r ≤ ℓ)
    (z : GuessSpace n v) (u : MomentumBasis n ℓ)
    (hu : quasiEvenCondensate n ℓ r o u) :
    |lambdaSuccWeight n ℓ v z u| ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  by_cases hinj : Function.Injective z
  · have hprod : (∏ i, (momentumOccupation u (z i) : ℝ))
        ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
      occupationProduct_le (n := n) (ℓ := ℓ) (v := v) (r := r) u hu.1 hr hrℓ z hinj
    have hnonneg : 0 ≤ ∏ i, (momentumOccupation u (z i) : ℝ) :=
      Finset.prod_nonneg fun i _ => by positivity
    have h : lambdaSuccWeight n ℓ v z u
        = ∏ i, (momentumOccupation u (z i) : ℝ) := by
      simp [lambdaSuccWeight, hinj]
    rw [h, abs_of_nonneg hnonneg]
    exact hprod
  · have h : lambdaSuccWeight n ℓ v z u = 0 := by
      simp [lambdaSuccWeight, hinj]
    rw [h]
    simp only [abs_zero]
    positivity

/-- The operator norm of the success operator restricted by the quasi-even condensate projector
satisfies the occupation-product bound. -/
theorem lambdaSucc_sandwich_opNorm_le {n ℓ v r o : ℕ} (hr : 1 ≤ r) (hrℓ : r ≤ ℓ) :
    ‖qecProjectorFull n ℓ r o v * lambdaSuccFull n ℓ v * qecProjectorFull n ℓ r o v‖
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  rw [qec_lambdaSucc_qec_eq_diagonal, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
  · positivity
  · intro p
    have hofReal (x : ℝ) : ‖Complex.ofReal x‖ = |x| := RCLike.norm_ofReal (K := ℂ) x
    by_cases hq : quasiEvenCondensate n ℓ r o p.2
    · have hweight : |lambdaSuccWeight n ℓ v p.1 p.2|
          ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
        lambdaSuccWeight_le hr hrℓ p.1 p.2 hq
      simp only [ite_eq_left hq]
      rw [mul_one, one_mul, hofReal]
      exact hweight
    · simp only [ite_eq_right hq, mul_zero, zero_mul, norm_zero]
      positivity

/-- For a normalized state, the probability-weighted sum of absolute diagonal entries is at most
the diagonal matrix's operator norm. -/
theorem diagonal_expectation_le_opNorm {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (φ : QState ι) (hφ : Normalized φ) :
    (∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2 * ‖f i‖)
      ≤ ‖(Matrix.diagonal f : Matrix ι ι ℂ)‖ := by
  rw [Matrix.l2_opNorm_diagonal]
  calc (∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2 * ‖f i‖)
      ≤ ∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2 * ‖f‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f i) (sq_nonneg _)
    _ = (∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2) * ‖f‖ := by
        have h1 := Finset.sum_mul (Finset.univ : Finset ι) (fun i => ‖φ i‖ ^ 2) ‖f‖
        have h2 : (∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2 * ‖f‖)
            = ∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2 * ‖f‖ := rfl
        rw [h2, ← h1]
    _ = ‖f‖ := by
        have hnorm : (∑ i ∈ (Finset.univ : Finset ι), ‖φ i‖ ^ 2) = 1 := by
          show (∑ i : ι, ‖φ i‖ ^ 2) = 1
          exact hφ
        rw [hnorm]
        ring

/-- A normalized state supported on quasi-even condensates has success-weight expectation
bounded by the particle number times the indicated power of `r`. -/
theorem lambdaSucc_expectation_le_of_sandwich {n ℓ v r o : ℕ} (hr : 1 ≤ r)
    (hrℓ : r ≤ ℓ) (φ : QState (GuessSpace n v × MomentumBasis n ℓ)) (hφ : Normalized φ)
    (hsupp : ∀ z u, φ (z, u) ≠ 0 → quasiEvenCondensate n ℓ r o u) :
    (∑ p ∈ (Finset.univ : Finset (GuessSpace n v × MomentumBasis n ℓ)),
        ‖φ p‖ ^ 2 * lambdaSuccWeight n ℓ v p.1 p.2)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  let d : GuessSpace n v × MomentumBasis n ℓ → ℂ := fun p =>
    (if quasiEvenCondensate n ℓ r o p.2 then 1 else 0) *
      Complex.ofReal (lambdaSuccWeight n ℓ v p.1 p.2) *
      (if quasiEvenCondensate n ℓ r o p.2 then 1 else 0)
  have hdiag : qecProjectorFull n ℓ r o v * lambdaSuccFull n ℓ v * qecProjectorFull n ℓ r o v
      = Matrix.diagonal d := by
    exact qec_lambdaSucc_qec_eq_diagonal n ℓ v r o
  have hterm : ∀ p ∈ (Finset.univ : Finset (GuessSpace n v × MomentumBasis n ℓ)),
      ‖φ p‖ ^ 2 * lambdaSuccWeight n ℓ v p.1 p.2
        = ‖φ p‖ ^ 2 * ‖d p‖ := by
    intro p _
    by_cases hne : φ p ≠ 0
    · have hq : quasiEvenCondensate n ℓ r o p.2 := hsupp p.1 p.2 hne
      have hentry : d p = Complex.ofReal (lambdaSuccWeight n ℓ v p.1 p.2) := by
        simp only [d, ite_eq_left hq, mul_one, one_mul]
      rw [hentry]
      have hofReal (x : ℝ) : ‖Complex.ofReal x‖ = |x| := RCLike.norm_ofReal (K := ℂ) x
      rw [hofReal]
      congr 1
      exact (abs_of_nonneg (lambdaSuccWeight_nonneg n ℓ v p.1 p.2)).symm
    · have hz : ‖φ p‖ ^ 2 = 0 := by
        have hφ0 : φ p = 0 := by simpa using! hne
        simp [hφ0]
      simp only [hz, zero_mul]
  have hbound := diagonal_expectation_le_opNorm (f := d) φ hφ
  have hop := lambdaSucc_sandwich_opNorm_le (n := n) (ℓ := ℓ) (v := v) (r := r) (o := o) hr hrℓ
  have hsum : (∑ p ∈ (Finset.univ : Finset (GuessSpace n v × MomentumBasis n ℓ)),
      ‖φ p‖ ^ 2 * lambdaSuccWeight n ℓ v p.1 p.2)
      = (∑ p ∈ (Finset.univ : Finset (GuessSpace n v × MomentumBasis n ℓ)),
        ‖φ p‖ ^ 2 * ‖d p‖) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact hterm p (Finset.mem_univ p)
  rw [hsum]
  rw [← hdiag] at hbound
  exact hbound.trans hop

/-- The success-weight expectation of a normalized state supported on quasi-even condensates
satisfies the occupation-product bound. -/
theorem lambdaSucc_expectation_le {n ℓ v r o : ℕ} (hr : 1 ≤ r) (hrℓ : r ≤ ℓ)
    (φ : QState (GuessSpace n v × MomentumBasis n ℓ)) (hφ : Normalized φ)
    (hsupp : ∀ z u, φ (z, u) ≠ 0 → quasiEvenCondensate n ℓ r o u) :
    (∑ p ∈ (Finset.univ : Finset (GuessSpace n v × MomentumBasis n ℓ)),
        ‖φ p‖ ^ 2 * lambdaSuccWeight n ℓ v p.1 p.2)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
  lambdaSucc_expectation_le_of_sandwich hr hrℓ φ hφ hsupp

/-- A condensate basis state has at most `r` plus one occupied momentum modes. -/
theorem momentumOccupiedModes_card_le {n ℓ r : ℕ} (u : MomentumBasis n ℓ)
    (h : condensate n ℓ r u) : (momentumOccupiedModes u).card ≤ r + 1 := by
  classical
  have htotal : (∑ y : Reg n, momentumOccupation u y) = ℓ := by
    simpa [momentumOccupation] using! u.property
  have hrest : (∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
      momentumOccupation u x) ≤ r := by
    have hsplit : (∑ y : Reg n, momentumOccupation u y)
        = momentumOccupation u (zeroMode n)
          + ∑ y ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
            momentumOccupation u y := by
      rw [← Finset.sdiff_singleton_eq_erase]
      exact Finset.sum_eq_add_sum_diff_singleton (zeroMode n)
        (fun y => momentumOccupation u y) (by simp)
    have hcond : ℓ ≤ momentumOccupation u (zeroMode n) + r := h
    have hkey : momentumOccupation u (zeroMode n)
        + (∑ y ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
          momentumOccupation u y)
        ≤ momentumOccupation u (zeroMode n) + r := by
      rw [← hsplit, htotal]
      exact hcond
    omega
  have hcard : (((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
        (fun x : Reg n => momentumOccupation u x ≠ 0)).card
      ≤ ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        momentumOccupation u x := by
    calc
      (((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
          (fun x : Reg n => momentumOccupation u x ≠ 0)).card
        = ∑ x ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
            (fun x : Reg n => momentumOccupation u x ≠ 0), (1 : ℕ) := by
          rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ ((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
            (fun x : Reg n => momentumOccupation u x ≠ 0), momentumOccupation u x := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx0 : momentumOccupation u x ≠ 0 := (Finset.mem_filter.mp hx).2
          omega
      _ = ∑ y ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
          momentumOccupation u y := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : momentumOccupation u y = 0 <;> simp [hy]
  have hdecomp : (Finset.univ : Finset (Reg n)).filter
        (fun x : Reg n => momentumOccupation u x ≠ 0)
      = ((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
          (fun x : Reg n => momentumOccupation u x ≠ 0)
        ∪ ({zeroMode n} : Finset (Reg n)).filter (fun x : Reg n => momentumOccupation u x ≠ 0) := by
    ext x
    by_cases hx : x = zeroMode n
    · subst hx
      simp
    · simp [hx]
  have hdisj : Disjoint
      (Finset.filter (fun x : Reg n => momentumOccupation u x ≠ 0)
        ((Finset.univ : Finset (Reg n)).erase (zeroMode n)))
      (Finset.filter (fun x : Reg n => momentumOccupation u x ≠ 0)
        ({zeroMode n} : Finset (Reg n))) := by
    refine Finset.disjoint_left.2 fun⦃x⦄ hx1 hx2 => ?_
    have hxne : x ≠ zeroMode n := (Finset.mem_erase.mp (Finset.mem_filter.mp hx1).1).1
    have hxeq : x = zeroMode n := by
      simpa using! (Finset.mem_filter.mp hx2).1
    exact hxne hxeq
  rw [momentumOccupiedModes, hdecomp, Finset.card_union_of_disjoint hdisj]
  calc
    _ ≤ r + 1 := by
      have h1 : (((Finset.univ : Finset (Reg n)).erase (zeroMode n)).filter
            (fun x : Reg n => momentumOccupation u x ≠ 0)).card ≤ r :=
          hcard.trans hrest
      have h2 : (({zeroMode n} : Finset (Reg n)).filter
            (fun x : Reg n => momentumOccupation u x ≠ 0)).card ≤ 1 := by
        calc _ ≤ ({zeroMode n} : Finset (Reg n)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 1 := Finset.card_singleton _
      omega

/-- Twice the absolute difference in zero-mode occupation is at most the momentum distance. -/
theorem momentumDistance_zeroMode_le {n ℓ : ℕ} (u w : MomentumBasis n ℓ) :
    2 * |(momentumOccupation u (zeroMode n) : ℝ) - (momentumOccupation w (zeroMode n) : ℝ)|
      ≤ momentumDistance u w := by
  classical
  have hu : (∑ x : Reg n, (momentumOccupation u x : ℝ)) = (ℓ : ℝ) := by
    have h1 : (∑ x : Reg n, (momentumOccupation u x : ℕ)) = ℓ := by
      simpa [momentumOccupation] using! u.property
    norm_cast
  have hw : (∑ x : Reg n, (momentumOccupation w x : ℝ)) = (ℓ : ℝ) := by
    have h1 : (∑ x : Reg n, (momentumOccupation w x : ℕ)) = ℓ := by
      simpa [momentumOccupation] using! w.property
    norm_cast
  have hsplit (f : Reg n → ℝ) :
      (∑ x : Reg n, f x) = f (zeroMode n)
        + ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n), f x := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Reg n)) f (a := zeroMode n)
      (Finset.mem_univ _)
    rw [← add_comm] at h
    exact h.symm
  have hzero : (∑ x : Reg n,
      ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, hu, hw]
    ring
  have htri : |(∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)))| ≤
      ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        |(momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum : (∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)))
      = -((momentumOccupation u (zeroMode n) : ℝ)
        - (momentumOccupation w (zeroMode n) : ℝ)) := by
    have hrest : (∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)))
        = (∑ x : Reg n,
            ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)))
          - ((momentumOccupation u (zeroMode n) : ℝ)
            - (momentumOccupation w (zeroMode n) : ℝ)) := by
      have h := hsplit
        (fun x => (momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ))
      linarith
    rw [hrest, hzero]
    ring
  have habs : |(momentumOccupation u (zeroMode n) : ℝ)
        - (momentumOccupation w (zeroMode n) : ℝ)|
      = |∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
        ((momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ))| := by
    rw [hsum, abs_neg]
  have hdist : momentumDistance u w
      = |(momentumOccupation u (zeroMode n) : ℝ)
          - (momentumOccupation w (zeroMode n) : ℝ)|
        + ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
          |(momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)| := by
    unfold momentumDistance
    rw [hsplit]
  have hkey : 2 * |(momentumOccupation u (zeroMode n) : ℝ)
        - (momentumOccupation w (zeroMode n) : ℝ)|
      ≤ |(momentumOccupation u (zeroMode n) : ℝ) - (momentumOccupation w (zeroMode n) : ℝ)|
        + ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
          |(momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)| := by
    have h1 : |(momentumOccupation u (zeroMode n) : ℝ)
          - (momentumOccupation w (zeroMode n) : ℝ)| ≤
        ∑ x ∈ (Finset.univ : Finset (Reg n)).erase (zeroMode n),
          |(momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)| := by
      rw [habs]
      exact htri
    linarith
  rw [hdist]
  exact hkey

/-- The verifier completeness and soundness assumptions, together with the averaged sampler
upper bound, imply the displayed failure-adjusted query inequality. -/
theorem clause3_queryLowerBound {n ℓ q t v : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)) (r : ℕ)
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E ≤ (1 / 3 : ℝ))
    (hupper : strongAverage n ℓ κ
        (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v)
        ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1)) :
    (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) *
        ((1 / (2 ^ q : ℝ)) * (1 / (36 * (t : ℝ) ^ 2)) ^ v)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  have hlow := classifier_strong_sampling_lower n ℓ q t v κ hκ W C ψfam E hC hnorm hS hU
    hyes hno
  exact hlow.trans hupper

/-- For nonnegative `κ`, the strong failure probability is at most one. -/
theorem strongFailProb_le_one (n ℓ : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (t1 t2 : ℝ) (v : ℕ) :
    strongFailProb n ℓ κ t1 t2 v ≤ 1 := by
  classical
  have hid : strongFailProb n ℓ κ t1 t2 v
      = strongAverage n ℓ κ
          (fun s U => if IsStrongYes t1 t2 v (multisetInd s) U then 0 else 1) := by
    unfold strongFailProb strongAverage
    rfl
  rw [hid]
  exact (strongAverage_mono n ℓ κ hκ
    (fun s U => if IsStrongYes t1 t2 v (multisetInd s) U then 0 else 1)
    (fun _ _ => 1) (by intro s U; by_cases h : IsStrongYes t1 t2 v (multisetInd s) U <;>
      simp [h])).trans
    (strongAverage_one n ℓ κ).le

/-- Under the stated verifier and sampler bounds, the number of classical witnesses is bounded
below by the displayed expression involving failure probability and query count. -/
theorem clause3_queryExponentialLowerBound {n ℓ q t v : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)) (r : ℕ)
    (hℓ : 0 < ℓ) (hr : 1 ≤ r) (_hrℓ : r ≤ ℓ) (ht : 0 < t)
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E ≤ (1 / 3 : ℝ))
    (hupper : strongAverage n ℓ κ
        (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v)
        ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1)) :
    (2 : ℝ) ^ q ≥ (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) /
        ((ℓ : ℝ) * (r : ℝ) ^ (v - 1) * (36 * (t : ℝ) ^ 2) ^ v) := by
  have hcombined := clause3_queryLowerBound (n := n) (ℓ := ℓ) (q := q) (t := t) (v := v)
    κ hκ W C ψfam E r hC hnorm hS hU hyes hno hupper
  have hfp : strongFailProb n ℓ κ (57 / 100) (59 / 100) v ≤ 1 :=
    strongFailProb_le_one n ℓ κ hκ (57 / 100) (59 / 100) v
  have hA : 0 ≤ 1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v := by linarith
  have hB : 0 < (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by positivity
  have hX : 0 < (2 : ℝ) ^ q := by positivity
  have hY : 0 < (36 * (t : ℝ) ^ 2) ^ v := by positivity

  have hmain : (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) *
        (((2 : ℝ) ^ q)⁻¹ * ((36 * (t : ℝ) ^ 2) ^ v)⁻¹)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
    have hexp : ((1 / (2 ^ q : ℝ)) * (1 / (36 * (t : ℝ) ^ 2)) ^ v)
        = ((2 : ℝ) ^ q)⁻¹ * ((36 * (t : ℝ) ^ 2) ^ v)⁻¹ := by
      simp only [div_eq_mul_inv, one_mul, inv_pow]
    rw [hexp] at hcombined
    exact hcombined
  have hmul := mul_le_mul_of_nonneg_right hmain (le_of_lt (mul_pos hX hY))
  have hL : ((1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) *
        (((2 : ℝ) ^ q)⁻¹ * ((36 * (t : ℝ) ^ 2) ^ v)⁻¹)) *
        (((2 : ℝ) ^ q) * ((36 * (t : ℝ) ^ 2) ^ v)) =
      (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) := by
    field_simp [ne_of_gt hX, ne_of_gt hY]
  rw [hL] at hmul
  have hkey : (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v)
      ≤ (2 : ℝ) ^ q * ((ℓ : ℝ) * (r : ℝ) ^ (v - 1) * (36 * (t : ℝ) ^ 2) ^ v) := by
    nlinarith [hmul]
  have hfinal : (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) /
        ((ℓ : ℝ) * (r : ℝ) ^ (v - 1) * (36 * (t : ℝ) ^ 2) ^ v) ≤ (2 : ℝ) ^ q := by
    rw [div_le_iff₀ (mul_pos hB hY)]
    exact hkey
  exact hfinal

/-- Relabeling a unitary matrix along an equivalence preserves unitarity. -/
private theorem relabelGate_unitary' {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have h : Uᴴ * U = 1 := by
    have h' := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hstar : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
    ext i j
    simp [relabelGate, Matrix.reindex_apply, submatrix_apply, Matrix.conjTranspose_apply]
  have hmul : relabelGate e Uᴴ * relabelGate e U = relabelGate e (Uᴴ * U) := by
    ext i j
    simp only [relabelGate, Matrix.reindex_apply, submatrix_apply, Matrix.mul_apply]
    rw [Equiv.sum_comp e.symm (fun y => Uᴴ (e.symm i) y * U y (e.symm j)),
      ← Matrix.mul_apply]
  rw [hstar, hmul, h]
  ext i j
  simp [relabelGate, Matrix.reindex_apply, submatrix_apply, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- The Fock-mode Hadamard matrix is unitary. -/
theorem hadamardFock_unitary (n : ℕ) :
    hadamardFock n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  relabelGate_unitary' (bitVecEquiv n) (hadamardN_unitary n)

/-- Each entry of the Fock-mode Hadamard matrix is the normalized product of signs determined by
the momentum-mode bits. -/
theorem hadamardFock_apply (n : ℕ) (x y : Fin (2 ^ n)) :
    hadamardFock n x y = ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
      ∏ i, (if momentumMode n x i && momentumMode n y i then (-1 : ℂ) else 1) := by
  have h : hadamardFock n x y = HadamardN n (momentumMode n x) (momentumMode n y) := by
    simp [hadamardFock, relabelGate, Matrix.reindex_apply, submatrix_apply, momentumMode]
  rw [h, hadamardN_apply]

/-- The Fock transform intertwines ordinary creation with momentum creation between successive
particle sectors. -/
theorem momentumCreation_fockDuality (n ℓ : ℕ) (y : Fin (2 ^ n)) :
    Qatlib.Concepts.BosonFock.BosonOperators.gamma (2 ^ n) (ℓ + 1) (hadamardFock n) *
        Qatlib.Concepts.BosonFock.BosonOperators.create (2 ^ n) ℓ y
      = momentumCreation n ℓ y * Qatlib.Concepts.BosonFock.BosonOperators.gamma (2 ^ n) ℓ (hadamardFock n) := by
  have h := (Qatlib.Concepts.BosonFock.BosonOperators.second_quantization_permanent_bridge.2.2.1 (2 ^ n) ℓ
    ⟨hadamardFock n, hadamardFock_unitary n⟩ y).1
  simpa [momentumCreation] using! h

/-- The Gram matrix of the momentum Fock transform is the identity. -/
theorem momentumFockTransform_unitary (n ℓ : ℕ) :
    (Qatlib.Concepts.BosonFock.BosonOperators.gamma (2 ^ n) ℓ (hadamardFock n)).conjTranspose
      * Qatlib.Concepts.BosonFock.BosonOperators.gamma (2 ^ n) ℓ (hadamardFock n) = 1 := by
  have h := (Qatlib.Concepts.BosonFock.BosonOperators.second_quantization_permanent_bridge.1 (2 ^ n) ℓ
    ⟨hadamardFock n, hadamardFock_unitary n⟩
    ⟨hadamardFock n, hadamardFock_unitary n⟩).1
  exact h

/-- Each momentum creation entry is the Hadamard-weighted sum of the allowed single-mode
creation amplitudes. -/
theorem momentumCreation_apply (n ℓ : ℕ) (y : Fin (2 ^ n))
    (w : MomentumFock n (ℓ + 1)) (v : MomentumFock n ℓ) :
    momentumCreation n ℓ y w v =
      ∑ x, hadamardFock n x y *
        (if ∀ j, (w.val j : ℕ) = (v.val j : ℕ) + if j = x then 1 else 0
          then (Real.sqrt ((v.val x : ℕ) + 1) : ℂ) else 0) := by
  simp [momentumCreation, Matrix.sum_apply, Matrix.smul_apply,
      Qatlib.Concepts.BosonFock.BosonOperators.create]

/-- For an injective input mode list with the specified occupation profile, the squared norm of
a Fock-transform entry equals the corresponding boson weight. -/
theorem momentumFockTransform_bosonWeight (n ℓ : ℕ) (f : Fin ℓ → Fin (2 ^ n))
    (s r : Qatlib.Concepts.BosonFock.BosonOperators.Occupation (2 ^ n) ℓ) (hf : Function.Injective f)
    (hs : ∀ i, (s.val i : ℕ) = (Finset.univ.filter (fun a => f a = i)).card) :
    Complex.normSq (Qatlib.Concepts.BosonFock.BosonOperators.gamma (2 ^ n) ℓ (hadamardFock n) r s)
      = bosonWeight ((hadamardFock n).submatrix id f) r := by
  exact (Qatlib.Concepts.BosonFock.BosonOperators.second_quantization_permanent_bridge.2.2.2 (2 ^ n) ℓ
    ⟨hadamardFock n, hadamardFock_unitary n⟩ f s r hf hs)

def scheduleProfile {N : ℕ} (sch : QuerySchedule N) : FockBasis N sch.length :=
  ⟨fun x => ⟨scheduleOccupation sch x, by
      have h := scheduleOccupation_le sch x
      omega⟩, by
      simpa using! (scheduleOccupation_total sch)⟩

/-- The occupation profile of a schedule has entries given by `scheduleOccupation`. -/
theorem scheduleProfile_val {N : ℕ} (sch : QuerySchedule N) (x : Fin N) :
    ((scheduleProfile sch).1 x : ℕ) = scheduleOccupation sch x := rfl

/-- Counting occurrences in an appended list gives the sum of the counts in its two parts. -/
theorem listCount_append {α : Type} [DecidableEq α] (x : α) (l₁ l₂ : List α) :
    listCount x (l₁ ++ l₂) = listCount x l₁ + listCount x l₂ := by
  induction l₁ with
  | nil => simp [listCount]
  | cons a l ih =>
    show (if a = x then 1 else 0) + listCount x (l ++ l₂)
      = (if a = x then 1 else 0) + listCount x l + listCount x l₂
    rw [ih]
    omega

/-- A singleton contains one occurrence of its element and zero occurrences of every other
element. -/
theorem listCount_singleton {α : Type} [DecidableEq α] (x y : α) :
    listCount y [x] = if x = y then 1 else 0 := by
  simp [listCount]

/-- Appending one mode to a schedule increases its profile entry by one exactly at that mode. -/
theorem scheduleProfile_append_val {N : ℕ} (sch : QuerySchedule N) (x y : Fin N) :
    ((scheduleProfile (sch ++ [x])).1 y : ℕ)
      = scheduleOccupation sch y + if y = x then 1 else 0 := by
  have h1 : ((scheduleProfile (sch ++ [x])).1 y : ℕ) = scheduleOccupation (sch ++ [x]) y := rfl
  have h2 : scheduleOccupation (sch ++ [x]) y = listCount y sch + (if x = y then 1 else 0) := by
    simp only [scheduleOccupation, listCount_append, listCount_singleton]
  rw [h1, h2]
  by_cases hy : y = x
  · subst hy
    simp [scheduleOccupation]
  · have hxy : x ≠ y := Ne.symm hy
    simp [hxy, hy, scheduleOccupation]

/-- A creation-operator entry vanishes unless the output profile adds exactly one particle at
the chosen mode. -/
theorem create_zero_of_ne {N t : ℕ} (x : Fin N) (w : FockBasis N (t + 1)) (v : FockBasis N t)
    (h : ¬ (∀ j, (w.val j : ℕ) = (v.val j : ℕ) + if j = x then 1 else 0)) :
    Qatlib.Concepts.BosonFock.BosonOperators.create N t x w v = 0 := by
  simp [Qatlib.Concepts.BosonFock.BosonOperators.create, h]

/-- A creation-operator entry for the required occupation update is the square root of the
initial occupation plus one. -/
theorem create_apply_of_eq {N t : ℕ} (x : Fin N) (w : FockBasis N (t + 1)) (v : FockBasis N t)
    (h : ∀ j, (w.val j : ℕ) = (v.val j : ℕ) + if j = x then 1 else 0) :
    Qatlib.Concepts.BosonFock.BosonOperators.create N t x w v = (Real.sqrt ((v.val x : ℕ) + 1) : ℂ) := by
  simp [Qatlib.Concepts.BosonFock.BosonOperators.create, h]

/-- The bosonic creation matrix agrees entrywise with the standard Fock creation operator. -/
theorem bosonicCreation_eq_create {N t : ℕ} (x : Fin N)
    (w : FockBasis N (t + 1)) (v : FockBasis N t) :
    bosonicCreation N t x w v = Qatlib.Concepts.BosonFock.BosonOperators.create N t x w v := by
  have heq : ((∀ i : Fin N, (i : ℕ) ≠ (x : ℕ) → (w.1 i : ℕ) = (v.1 i : ℕ)) ∧
        ((w.1 x : ℕ) = (v.1 x : ℕ) + 1))
      ↔ (∀ j : Fin N, (w.val j : ℕ) = (v.val j : ℕ) + if j = x then 1 else 0) := by
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = x
      · subst hj
        simpa using! h2
      · have hj' : (j : ℕ) ≠ (x : ℕ) := by
          intro hcon
          apply hj
          exact Fin.ext hcon
        have h3 := h1 j hj'
        simpa [hj] using! h3
    · intro h
      constructor
      · intro i hi
        have hi' : i ≠ x := fun h => hi (congrArg (fun k : Fin N => (k : ℕ)) h)
        have h3 := h i
        simp [hi'] at h3
        exact h3
      · have h3 := h x
        simp at h3
        exact h3
  simp only [bosonicCreation, Qatlib.Concepts.BosonFock.BosonOperators.create, of_apply]
  by_cases h : ∀ j : Fin N, (w.val j : ℕ) = (v.val j : ℕ) + if j = x then 1 else 0
  · have hA := heq.mpr h
    simp [hA, h]
  · have hA : ¬ ((∀ i : Fin N, (i : ℕ) ≠ (x : ℕ) → (w.1 i : ℕ) = (v.1 i : ℕ)) ∧
        ((w.1 x : ℕ) = (v.1 x : ℕ) + 1)) := fun hB => h (heq.mp hB)
    simp [hA, h]

noncomputable def fockRegisterState {N : ℕ} (sch : QuerySchedule N) :
    FockBasis N sch.length → ℂ :=
  fun v => if v = scheduleProfile sch then 1 else 0

/-- The Fock register state associated with any schedule has squared norm one. -/
theorem fockRegisterState_norm_sq {N : ℕ} (sch : QuerySchedule N) :
    (∑ v, ‖fockRegisterState sch v‖ ^ 2) = 1 := by
  classical
  have h : (∑ v, ‖fockRegisterState sch v‖ ^ 2)
      = ∑ v, if v = scheduleProfile sch then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = scheduleProfile sch
    · simp [fockRegisterState, hv]
    · simp [fockRegisterState, hv]
  rw [h, Finset.sum_eq_single (scheduleProfile sch)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcontra
    exact absurd hcontra (by simp)

noncomputable def compressedJointState {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {N t : ℕ}
    (reg : FockBasis N t → ℂ) (ψ : QState (((I × Bool) × W) × (I → Bool))) :
    (FockBasis N t × ((I × Bool) × W) × (I → Bool)) → ℂ :=
  fun p => reg p.1 * ψ (p.2.1, p.2.2)

/-- The squared norm of a compressed joint state factors into the squared norms of its register
and query states. -/
theorem compressedJointState_norm_sq {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {N t : ℕ}
    (reg : FockBasis N t → ℂ) (ψ : QState (((I × Bool) × W) × (I → Bool))) :
    (∑ p, ‖compressedJointState reg ψ p‖ ^ 2)
      = (∑ v, ‖reg v‖ ^ 2) * (∑ q, ‖ψ q‖ ^ 2) := by
  have hmul : ∀ (a b : ℂ), ‖a * b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    intro a b
    rw [norm_mul, mul_pow]
  calc (∑ p, ‖compressedJointState reg ψ p‖ ^ 2)
      = ∑ v, ∑ q, ‖reg v‖ ^ 2 * ‖ψ q‖ ^ 2 := by
        simp only [compressedJointState, hmul]
        rw [Fintype.sum_prod_type]
    _ = (∑ v, ‖reg v‖ ^ 2) * (∑ q, ‖ψ q‖ ^ 2) :=
        (Fintype.sum_mul_sum _ _).symm

/-- Pairing a decompressed XOR run with a schedule's Fock register state preserves its squared
norm. -/
theorem compressedJointState_xor_norm {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {N : ℕ} (p : ℝ)
    (sch : QuerySchedule N) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) :
    (∑ q, ‖compressedJointState (fockRegisterState sch)
        (decompressedXorRun p C ψ) q‖ ^ 2)
      = (∑ q, ‖decompressedXorRun p C ψ q‖ ^ 2) := by
  have h := compressedJointState_norm_sq (fockRegisterState sch) (decompressedXorRun p C ψ)
  rw [fockRegisterState_norm_sq] at h
  simp only [one_mul] at h
  exact h

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
