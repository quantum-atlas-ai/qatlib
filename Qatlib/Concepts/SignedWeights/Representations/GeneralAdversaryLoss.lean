/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignedWeights.Representations.GeneralAdversaryLossDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.SignedWeights.Representations.LossCompletion

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.SignedWeights.Representations

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal MatrixOrder
open Qatlib

namespace LossCompletion

variable {m D : ℕ}

theorem lossKraus_gram (C : LossCompletion m D) :
    (C.lossKraus)ᴴ * C.lossKraus = C.defect := by
  have h := Qatlib.Concepts.AdversaryBounds.AdvDuality.sqrt_gram C.defect C.defect_pos
  simpa [lossKraus] using! h

theorem lossKraus_unique (C : LossCompletion m D) (L : Operator D) (hL : L.PosSemidef)
    (hgram : Lᴴ * L = C.defect) : L = C.lossKraus := by
  have hstar : Lᴴ = L := PosSemidef.isHermitian hL
  have hsq : L * L = C.defect := by
    rw [← hgram]
    congr 1
    exact hstar.symm
  have h := CFC.sqrt_unique (a := C.defect) (b := L) hsq (hL.nonneg)
  simpa [lossKraus] using! h.symm

theorem completed_complete_genuine_loss (C : LossCompletion m D) :
    (∑ i, (C.kraus i)ᴴ * (C.kraus i)) + (C.lossKraus)ᴴ * (C.lossKraus) = 1 := by
  rw [lossKraus_gram, C.defect_eq]
  exact add_sub_cancel _ _

theorem completed_complete (C : LossCompletion m D) :
    ∑ o, (C.completed o)ᴴ * (C.completed o) = 1 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [completed]
  have hunit : (∑ i : Unit, (C.lossKraus)ᴴ * (C.lossKraus))
      = (C.lossKraus)ᴴ * (C.lossKraus) := by simp
  rw [hunit]
  exact completed_complete_genuine_loss C

noncomputable def instrument (C : LossCompletion m D) : Instrument (Fin m ⊕ Unit) D D :=
  Instrument.ofKraus C.completed C.completed_complete

theorem instrument_branch_eq (C : LossCompletion m D) (rho : Operator D)
    (o : Fin m ⊕ Unit) :
    (C.instrument).branch o rho = C.completed o * rho * (C.completed o).conjTranspose := by
  simp only [LossCompletion.instrument, Instrument.ofKraus_branch]

theorem completed_reference_law (C : LossCompletion m D) (A : Operator D) :
    (∑ i, ((C.kraus i)ᴴ * (C.kraus i)) * A) + ((C.lossKraus)ᴴ * (C.lossKraus)) * A = A := by
  classical
  rw [← Finset.sum_mul, ← Matrix.add_mul, completed_complete_genuine_loss]
  simp

theorem completed_trace_split (C : LossCompletion m D) (rho : Operator D) :
    (∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose))
      = (∑ i, Matrix.trace ((C.kraus i) * rho * (C.kraus i).conjTranspose))
        + Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [completed]
  have hunit : (∑ i : Unit, Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose))
      = Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose) := by simp
  rw [hunit]

theorem completed_trace_total (C : LossCompletion m D) (rho : Operator D) :
    (∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose))
      = Matrix.trace rho := by
  classical
  calc
    (∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose))
        = ∑ o, Matrix.trace (((C.completed o).conjTranspose * (C.completed o)) * rho) := by
          exact Finset.sum_congr rfl fun o _ => Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (((∑ i, (C.kraus i)ᴴ * (C.kraus i))
          + ((C.lossKraus)ᴴ * (C.lossKraus))) * rho) := by
      rw [← Matrix.trace_sum, ← Finset.sum_mul, Fintype.sum_sum_type]
      simp only [completed]
      have hunit : (∑ i : Unit, (C.lossKraus)ᴴ * (C.lossKraus))
          = (C.lossKraus)ᴴ * (C.lossKraus) := by simp
      rw [hunit]
    _ = Matrix.trace rho := by
      rw [completed_complete_genuine_loss, Matrix.one_mul]

theorem instrument_total_mass_eq (C : LossCompletion m D) (rho : Operator D) :
    (∑ o, Matrix.trace ((C.instrument).branch o rho)) = Matrix.trace rho := by
  classical
  calc
    (∑ o, Matrix.trace ((C.instrument).branch o rho))
        = ∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose) := by
          exact Finset.sum_congr rfl fun o _ => by
            simp only [LossCompletion.instrument, Instrument.ofKraus_branch]
    _ = Matrix.trace rho := completed_trace_total C rho

theorem completed_no_deletion (C : LossCompletion m D) (rho : Operator D) :
    C.totalMass rho = (Matrix.trace rho).re := by
  unfold totalMass
  exact congrArg Complex.re (completed_trace_total C rho)

theorem completed_genuine_add_loss (C : LossCompletion m D) (rho : Operator D) :
    C.genuineMass rho + C.lossMass rho = (Matrix.trace rho).re := by
  unfold genuineMass lossMass
  rw [← Complex.add_re]
  exact congrArg Complex.re ((completed_trace_split C rho).symm.trans (completed_trace_total C rho))

theorem completed_genuine_mass_eq (C : LossCompletion m D) (rho : Operator D) :
    C.genuineMass rho
      = (∑ i, Matrix.trace ((C.kraus i) * rho * (C.kraus i).conjTranspose)).re := rfl

theorem lossMass_eq_defect_mass (C : LossCompletion m D) (rho : Operator D) :
    C.lossMass rho = (Matrix.trace (C.defect * rho)).re := by
  unfold lossMass
  rw [Matrix.trace_mul_cycle _ _ _, lossKraus_gram]

theorem lossMass_eq_branch_trace (C : LossCompletion m D) (rho : Operator D) :
    C.lossMass rho
      = (Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose)).re := rfl

theorem lossMass_nonneg (C : LossCompletion m D) (rho : Operator D)
    (hrho : rho.PosSemidef) : 0 ≤ C.lossMass rho := by
  have hpsd : (C.lossKraus * rho * (C.lossKraus).conjTranspose).PosSemidef :=
    Matrix.PosSemidef.mul_mul_conjTranspose_same hrho C.lossKraus
  have h' : (0 : ℝ)
      ≤ (Matrix.trace (C.lossKraus * rho * (C.lossKraus).conjTranspose)).re :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
  rw [lossMass_eq_branch_trace]
  exact h'

theorem clause16_complete {m D : ℕ} (C : LossCompletion m D) :
    (∑ o, (C.completed o)ᴴ * (C.completed o) = 1) ∧
      (∀ rho : Operator D, C.totalMass rho = (Matrix.trace rho).re) ∧
      (∀ rho : Operator D, C.genuineMass rho + C.lossMass rho = (Matrix.trace rho).re) ∧
      (∀ rho : Operator D, C.lossMass rho = (Matrix.trace (C.defect * rho)).re) ∧
      (∀ A : Operator D,
        (∑ i, ((C.kraus i)ᴴ * (C.kraus i)) * A) + ((C.lossKraus)ᴴ * (C.lossKraus)) * A = A) := by
  refine ⟨completed_complete C, fun rho => completed_no_deletion C rho,
    fun rho => completed_genuine_add_loss C rho,
    fun rho => lossMass_eq_defect_mass C rho,
    fun A => completed_reference_law C A⟩

end LossCompletion

theorem certifiedCutCostE_le_of_separating {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A]
    (input : X → κ → A) (beta : κ → ℝ≥0∞) (x y : X) (j : κ)
    (hsep : input x j ≠ input y j) :
    certifiedCutCostE input beta x y ≤ beta j := by
  have hj : j ∈ separatingCoords input x y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsep⟩
  have hne : (separatingCoords input x y).Nonempty := ⟨j, hj⟩
  unfold certifiedCutCostE
  rw [dif_pos hne]
  exact Finset.inf'_le (fun k => beta k) hj

theorem certifiedCutCostE_ne_top_of_finite_separating {X : Type} [Fintype X]
    [DecidableEq X] {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A]
    (input : X → κ → A) (beta : κ → ℝ≥0∞) (x y : X) (j : κ)
    (hsep : input x j ≠ input y j) (hfin : beta j ≠ ⊤) :
    certifiedCutCostE input beta x y ≠ ⊤ := by
  have hle := certifiedCutCostE_le_of_separating input beta x y j hsep
  intro h
  rw [h] at hle
  exact hfin (le_antisymm (le_top) hle)

theorem certifiedCutCostE_top_of_all_infinite {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A]
    (input : X → κ → A) (beta : κ → ℝ≥0∞) (x y : X)
    (hsep : ∃ j, input x j ≠ input y j)
    (h : ∀ j ∈ separatingCoords input x y, beta j = ⊤) :
    certifiedCutCostE input beta x y = ⊤ ∧ certifiedCutCost input beta x y = 0 := by
  obtain ⟨j0, hj0⟩ := hsep
  have hj0mem : j0 ∈ separatingCoords input x y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩
  have hne : (separatingCoords input x y).Nonempty := ⟨j0, hj0mem⟩
  obtain ⟨j, hjmem, hjval⟩ :=
    Finset.exists_mem_eq_inf' (s := separatingCoords input x y) hne (fun k => beta k)
  obtain ⟨j', hj'mem, hj'val⟩ :=
    Finset.exists_mem_eq_inf' (s := separatingCoords input x y) hne (fun k => (beta k).toReal)
  rw [h j hjmem] at hjval
  rw [h j' hj'mem] at hj'val
  rw [ENNReal.toReal_top] at hj'val
  constructor
  · unfold certifiedCutCostE
    rw [dif_pos hne]
    exact hjval
  · unfold certifiedCutCost
    rw [dif_pos hne]
    exact hj'val

theorem weightedCutCheck_certifies {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (j : κ) (h : weightedCutCheck input beta x y j = true) :
    input x j ≠ input y j ∧ 0 < beta j := by
  simp only [weightedCutCheck, decide_eq_true_eq] at h
  exact h

theorem executableCutWitness_certifies {X : Type} [DecidableEq X] {κ : Type}
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (beta : κ → RationalCost) (x y : X) (candidates : List κ) (j : κ)
    (h : executableCutWitness input beta x y candidates = some j) :
    input x j ≠ input y j ∧ 0 < beta j := by
  induction candidates with
  | nil => simp [executableCutWitness] at h
  | cons c cs ih =>
      by_cases hc : weightedCutCheck input beta x y c
      · have hj : c = j := by simpa [executableCutWitness, hc] using! h
        subst hj
        exact weightedCutCheck_certifies input beta x y c hc
      · have h' : executableCutWitness input beta x y cs = some j := by
          simpa [executableCutWitness, hc] using! h
        exact ih h'

private theorem minRationalCost_none_iff (l : List RationalCost) :
    minRationalCost l = none ↔ l = [] := by
  induction l with
  | nil => simp [minRationalCost]
  | cons c cs ih =>
      cases hc : minRationalCost cs with
      | none => simp [minRationalCost, hc]
      | some c' => simp [minRationalCost, hc]

private theorem min_le_first (a b : RationalCost) : min a b ≤ a := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact h

private theorem min_le_second (a b : RationalCost) : min a b ≤ b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    exact h
  · rw [min_eq_right h]

private theorem minRationalCost_attained : ∀ (l : List RationalCost) (c : RationalCost),
    minRationalCost l = some c →
      (∀ d ∈ l, c ≤ d) ∧ ∃ d ∈ l, d = c := by
  intro l
  induction l with
  | nil => intro c h; simp [minRationalCost] at h
  | cons a cs ih =>
      intro c h
      cases hc : minRationalCost cs with
      | none =>
          have hempty : cs = [] := minRationalCost_none_iff cs |>.mp hc
          simp [minRationalCost, hc] at h
          subst h
          refine ⟨?_, a, by simp, rfl⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact le_rfl
          · rw [hempty] at hd
            simp at hd
      | some c' =>
          simp [minRationalCost, hc] at h
          subst h
          obtain ⟨hle, hatt⟩ := ih c' hc
          rcases le_total a c' with hab | hab
          · rw [min_eq_left hab]
            refine ⟨?_, a, by simp, rfl⟩
            intro d hd
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact le_rfl
            · exact le_trans hab (hle d hd)
          · rw [min_eq_right hab]
            obtain ⟨d, hd, hdeq⟩ := hatt
            refine ⟨?_, d, by simp [hd], ?_⟩
            · intro d' hd'
              simp only [List.mem_cons] at hd'
              rcases hd' with rfl | hd'
              · exact hab
              · exact hle d' hd'
            · exact hdeq

theorem executableCutCost_attained {X : Type} [DecidableEq X] {κ : Type}
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (beta : κ → RationalCost) (x y : X) (candidates : List κ) (c : RationalCost)
    (h : executableCutCost input beta x y candidates = some c) :
    (∃ j ∈ candidates, weightedCutCheck input beta x y j = true ∧ beta j = c) ∧
      (∀ j ∈ candidates, weightedCutCheck input beta x y j = true → c ≤ beta j) := by
  unfold executableCutCost at h
  obtain ⟨hle, hatt⟩ := minRationalCost_attained _ _ h
  obtain ⟨d, hd, hdeq⟩ := hatt
  obtain ⟨j, hjcert', hjbeta⟩ := List.mem_map.mp hd
  rw [certifyingCoords] at hjcert'
  have hjfilter : j ∈ candidates ∧ weightedCutCheck input beta x y j = true :=
    List.mem_filter.mp hjcert'
  have hjmem : j ∈ candidates := hjfilter.1
  have hjcert : weightedCutCheck input beta x y j = true := hjfilter.2
  have hjcost : beta j = c := hjbeta.trans hdeq
  refine ⟨⟨j, hjmem, hjcert, hjcost⟩, ?_⟩
  intro j hjmem hjcert'
  have hjmem' : j ∈ certifyingCoords input beta x y candidates := by
    rw [certifyingCoords]
    exact List.mem_filter.mpr ⟨hjmem, hjcert'⟩
  have hmap : beta j ∈ (certifyingCoords input beta x y candidates).map beta :=
    List.mem_map.mpr ⟨j, hjmem', rfl⟩
  exact hle (beta j) hmap

theorem clause18_complete {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → ℝ≥0∞)
    (x y : X) :
    (∀ j, input x j ≠ input y j → certifiedCutCostE input beta x y ≤ beta j) ∧
      (∀ j, input x j ≠ input y j → beta j ≠ ⊤ → certifiedCutCostE input beta x y ≠ ⊤) ∧
      ((∃ j, input x j ≠ input y j) →
          (∀ j ∈ separatingCoords input x y, beta j = ⊤) →
            certifiedCutCostE input beta x y = ⊤ ∧ certifiedCutCost input beta x y = 0) := by
  refine ⟨fun j h => certifiedCutCostE_le_of_separating input beta x y j h,
    fun j h hfin => certifiedCutCostE_ne_top_of_finite_separating input beta x y j h hfin,
    fun hsep h => certifiedCutCostE_top_of_all_infinite input beta x y hsep h⟩

theorem genFilterDelta_eq_zero_of_constant {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A) (j : Fin n)
    (hc : ConstantCoordinate input j) : genFilterDelta input j = 0 := by
  obtain ⟨a, ha⟩ := hc
  ext x y
  simp only [genFilterDelta, Matrix.zero_apply]
  by_cases h : input x j = input y j
  · simp [h]
  · have hx : input x j = a := ha x
    have hy : input y j = a := ha y
    rw [hx, hy] at h
    exact (h rfl).elim

theorem crossFilteredGamma2_top_of_zeroFilter {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A) (diff : Matrix X X ℂ)
    (hz : ZeroFilterInstance input) (hne : ∃ x y, diff x y ≠ 0) :
    crossFilteredGamma2 input diff = ⊤ := by
  obtain ⟨x, y, hxy⟩ := hne
  exact (filteredGamma2_unsupported_top diff (genFilterDelta input) x y hxy
    (fun j => by rw [hz j]; simp)).1

theorem stateConversionSDPGeneral_le_crossFilteredGamma2 {X : Type} [Fintype X]
    [DecidableEq X] {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A)
    (delta : ℝ) (rho sigma : Matrix X X ℂ) (hdelta : 0 ≤ delta)
    (hsigma : sigma.PosSemidef) :
    stateConversionSDPGeneral input delta rho sigma
      ≤ crossFilteredGamma2 input (rho - sigma) := by
  have hz : gramFilteredCert (sigma - sigma) (fun _ : Fin 1 => gramFilterAllOnes) delta := by
    rw [sub_self]
    exact gramFilteredCert_zero _ hdelta
  exact iInf_le
    (fun sigma' : {sigma' : Matrix X X ℂ // sigma'.PosSemidef ∧
        gramFilteredCert (sigma' - sigma) (fun _ : Fin 1 => gramFilterAllOnes) delta} =>
      crossFilteredGamma2 input (rho - sigma'.1))
    ⟨sigma, hsigma, hz⟩

theorem crossFilteredGamma2_cert_of_lt {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A) (diff : Matrix X X ℂ)
    {W : ℝ} (h : crossFilteredGamma2 input diff < ENNReal.ofReal W) :
    gramFilteredCert diff (genFilterDelta input) W :=
  gramFilteredCert_of_filteredGamma2_lt h

theorem clause20_complete {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {A : Type}
    [DecidableEq A] (input : X → Fin n → A) (delta : ℝ) (rho sigma : Matrix X X ℂ)
    (hdelta : 0 ≤ delta) (hsigma : sigma.PosSemidef) :
    (stateConversionSDPGeneral input delta rho sigma
        ≤ crossFilteredGamma2 input (rho - sigma)) ∧
      (∀ j, ConstantCoordinate input j → genFilterDelta input j = 0) ∧
      (∀ diff, ZeroFilterInstance input → (∃ x y, diff x y ≠ 0) →
        crossFilteredGamma2 input diff = ⊤) := by
  refine ⟨stateConversionSDPGeneral_le_crossFilteredGamma2 input delta rho sigma hdelta hsigma,
    fun j hc => genFilterDelta_eq_zero_of_constant input j hc,
    fun diff hz hne => crossFilteredGamma2_top_of_zeroFilter input diff hz hne⟩

theorem commonStop_eq_true_iff (budget queries : ℕ) :
    commonStop budget queries = true ↔ queries ≤ budget := by
  simp [commonStop]

theorem truncated_trace_queries_le {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) :
    ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho, t.queries ≤ K := by
  induction P generalizing rho K with
  | halt b =>
      intro t ht
      obtain rfl := List.mem_singleton.mp ht
      simp
  | step action P ih =>
      cases action with
      | gate G =>
          intro t ht
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
          exact ih (conjBranch G rho) K u hu
      | query =>
          cases K with
          | zero =>
              intro t ht
              obtain rfl := List.mem_singleton.mp ht
              simp
          | succ K =>
              intro t ht
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
              exact Nat.succ_le_succ (ih (conjBranch O rho) K u hu)
  | instrument s I next ih =>
      intro t ht
      obtain ⟨xs, hxs, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hxs
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih o (I.branch o rho) K u hu

theorem truncated_total_mass_eq {d : ℕ} (O : Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (P : InstrumentCircuit d)
    (hP : instrumentCircuitWellFormed P) (rho : Operator d) (K : ℕ) :
    instrumentTotalMass O (truncateInstrumentQueries P K) rho = (Matrix.trace rho).re := by
  have hleg := truncateInstrumentQueries_legal P hP K
  exact instrument_total_mass O hO (truncateInstrumentQueries P K) hleg rho

private theorem list_map_sum_add {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem acceptedMass_add_neverMass_eq_total {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) :
    acceptedMass O P rho K + neverMass O P rho K
      = instrumentTotalMass O (truncateInstrumentQueries P K) rho := by
  unfold acceptedMass neverMass instrumentTotalMass instrumentCircuitEventMass
  have hsplit : ∀ t : MixedBranchTrace d,
      (if t.accepted then mixedMass t else 0) + (if !t.accepted then mixedMass t else 0)
        = mixedMass t := by
    intro t
    by_cases h : t.accepted <;> simp [h]
  have hmap : (instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map
      (fun t => (if t.accepted then mixedMass t else 0)
        + (if !t.accepted then mixedMass t else 0))
      = (instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map mixedMass := by
    exact List.map_congr_left (fun t _ => hsplit t)
  calc
    ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
        if t.accepted then mixedMass t else 0).sum
        + ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
          if !t.accepted then mixedMass t else 0).sum
        = ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
            ((if t.accepted then mixedMass t else 0)
              + (if !t.accepted then mixedMass t else 0))).sum :=
      (list_map_sum_add _ _ _).symm
    _ = ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map mixedMass).sum := by
            rw [hmap]

private theorem list_map_sum_le {α : Type} (l : List α) (f g : α → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem neverQueryCost_le_truncated_expected {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ) :
    neverQueryCost O P rho K
      ≤ instrumentCircuitExpectedQueries O (truncateInstrumentQueries P K) rho := by
  unfold neverQueryCost instrumentCircuitExpectedQueries
  have hmass : ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      0 ≤ mixedMass t :=
    instrumentTraceMass_nonneg O (truncateInstrumentQueries P K) rho hrho
  have hpoint : ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      (if neverEvent t.accepted t.outcomes then mixedMass t * t.queries else 0)
        ≤ mixedMass t * t.queries := by
    intro t ht
    by_cases h : neverEvent t.accepted t.outcomes
    · simp [h]
    · simp only [h]
      exact mul_nonneg (hmass t ht) (Nat.cast_nonneg _)
  exact list_map_sum_le _ _ _ hpoint

theorem neverQueryCost_le_budget_mul_neverMass {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ) :
    neverQueryCost O P rho K ≤ (K : ℝ) * neverMass O P rho K := by
  unfold neverQueryCost neverMass
  have hmass : ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      0 ≤ mixedMass t :=
    instrumentTraceMass_nonneg O (truncateInstrumentQueries P K) rho hrho
  have hq : ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      t.queries ≤ K := truncated_trace_queries_le O P rho K
  have hpoint : ∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      (if neverEvent t.accepted t.outcomes then mixedMass t * t.queries else 0)
        ≤ (if neverEvent t.accepted t.outcomes then mixedMass t * (K : ℝ) else 0) := by
    intro t ht
    by_cases h : neverEvent t.accepted t.outcomes
    · have hle : (t.queries : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hq t ht
      simp only [h, if_true]
      exact mul_le_mul_of_nonneg_left hle (hmass t ht)
    · simp [h]
  have hmap : (instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map
      (fun t => (if neverEvent t.accepted t.outcomes then mixedMass t * (K : ℝ) else 0))
      = (instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map
        (fun t => (K : ℝ) * (if neverEvent t.accepted t.outcomes then mixedMass t else 0)) := by
    exact List.map_congr_left (fun t _ => by
      by_cases h : neverEvent t.accepted t.outcomes <;> simp [h, mul_comm])
  calc
    ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
        (if neverEvent t.accepted t.outcomes then mixedMass t * t.queries else 0)).sum
        ≤ ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
          (if neverEvent t.accepted t.outcomes then mixedMass t * (K : ℝ) else 0)).sum :=
      list_map_sum_le _ _ _ hpoint
    _ = (K : ℝ) * ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
          (if neverEvent t.accepted t.outcomes then mixedMass t else 0)).sum := by
            rw [hmap, List.sum_map_mul_left]

theorem clause21_complete {d : ℕ} (O : Operator d) (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P) (rho : Operator d)
    (hrho : rho.PosSemidef) (K : ℕ) :
    (∀ t ∈ instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
        t.queries ≤ K) ∧
      (instrumentTotalMass O (truncateInstrumentQueries P K) rho = (Matrix.trace rho).re) ∧
      (acceptedMass O P rho K + neverMass O P rho K
        = instrumentTotalMass O (truncateInstrumentQueries P K) rho) ∧
      (neverQueryCost O P rho K
        ≤ instrumentCircuitExpectedQueries O (truncateInstrumentQueries P K) rho) ∧
      (neverQueryCost O P rho K ≤ (K : ℝ) * neverMass O P rho K) := by
  refine ⟨fun t ht => truncated_trace_queries_le O P rho K t ht,
    truncated_total_mass_eq O hO P hP rho K,
    acceptedMass_add_neverMass_eq_total O P rho K,
    neverQueryCost_le_truncated_expected O P rho hrho K,
    neverQueryCost_le_budget_mul_neverMass O P rho hrho K⟩

end Qatlib.Concepts.SignedWeights.Representations
