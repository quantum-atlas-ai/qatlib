/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch

/-!
# Instruments and histories for cluster networks

`networkStepInstrument` packages the physical branches of a legal network gate into a quantum
instrument. `networkHistoryInstrument` composes these steps and indexes the resulting branches
by complete outcome histories, following the branch semantics of one-way computation
[RaussendorfBriegel2001].

Valid histories give the same logical conjugation with a scalar determined by the wire and
controlled-Z counts. Forgetting the history recovers the logical unitary channel, including when
the input is correlated with an untouched reference system.

## Main statements

* `cluster_network_history_actual_branch_formula`: the exact map for each complete history.
* `cluster_network_forget_correct_arbitrary_input`: equality of the forgotten instrument and
  logical conjugation.
* `cluster_network_entangled_reference_and_record_mass`: extension to a reference system and
  exact record trace weights.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

set_option linter.unusedSectionVars false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- Multiplying a completely positive map by a nonnegative real scalar preserves complete
positivity. -/
theorem networkCP_const_smul {D E : ℕ} {F : Operator D →ₗ[ℂ] Operator E}
    (hF : CompletelyPositive F) {c : ℝ} (hc : 0 ≤ c) :
    CompletelyPositive (((c : ℝ) : ℂ) • F) := by
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib] at hF ⊢
  exact hF.smul (RCLike.ofReal_nonneg.mpr hc)

/-- The zero complex-linear map between operator spaces is completely positive. -/
theorem networkCP_zero {D E : ℕ} :
    CompletelyPositive (0 : Operator D →ₗ[ℂ] Operator E) := by
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib]
  exact MatrixMap.IsCompletelyPositive.zero _ _

/-- The identity map on an operator space is completely positive. -/
theorem networkCP_id {D : ℕ} :
    CompletelyPositive (LinearMap.id : Operator D →ₗ[ℂ] Operator D) := by
  have h : (LinearMap.id : Operator D →ₗ[ℂ] Operator D) = conjBranch 1 := by
    apply LinearMap.ext
    intro ρ
    simp
  rw [h]
  exact completelyPositive_conjBranch _

/-- A power of the complex scalar one half equals the complex cast of the corresponding real
power. -/
theorem networkHalf_pow_cast (k : ℕ) :
    ((2 : ℂ)⁻¹) ^ k = (((2 : ℝ)⁻¹) ^ k : ℝ) := by
  rw [show ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) from by norm_num, Complex.ofReal_pow]

/-- For a legal gate, its actual step branch is the count-weighted logical conjugation on valid
outcomes and the zero linear map otherwise. -/
theorem networkStepBranch_eq (n : ℕ) (g : ClusterNetworkGate n) (hg : networkLegal [g])
    (o : Bool × Bool) :
    networkActualStepBranch g o
      = (if networkBranchValid [g] (fun _ => o)
        then (((2 : ℂ)⁻¹) ^ ((networkCounts [g]).1 + 2 * (networkCounts [g]).2))
            • conjBranch (networkLogicalMatrix [g])
        else 0) := by
  apply LinearMap.ext
  intro ρ
  by_cases hv : networkBranchValid [g] (fun _ => o)
  · rw [if_pos hv, LinearMap.smul_apply,
      (cluster_network_actual_local_step_branches n g hg).2 o ρ, if_pos hv]
  · rw [if_neg hv, LinearMap.zero_apply,
      (cluster_network_actual_local_step_branches n g hg).2 o ρ, if_neg hv]

/-- Every outcome branch of a legal network step is completely positive. -/
theorem networkStepBranch_cp (n : ℕ) (g : ClusterNetworkGate n) (hg : networkLegal [g])
    (o : Bool × Bool) : CompletelyPositive (networkActualStepBranch g o) := by
  rw [networkStepBranch_eq n g hg o]
  by_cases hv : networkBranchValid [g] (fun _ => o)
  · rw [if_pos hv, networkHalf_pow_cast]
    exact networkCP_const_smul (completelyPositive_conjBranch _) (by positivity)
  · rw [if_neg hv]
    exact networkCP_zero

/-- Summing all outcome branches of a legal network step yields conjugation by its logical
matrix. -/
theorem networkStepBranch_sum (n : ℕ) (g : ClusterNetworkGate n) (hg : networkLegal [g])
    (A : Operator (2 ^ n)) :
    ∑ o : Bool × Bool, networkActualStepBranch g o A
      = conjBranch (networkLogicalMatrix [g]) A := by
  cases g with
  | inl p =>
    obtain ⟨i, ζ⟩ := p
    have hvalid : ∀ a : Bool, networkBranchValid [.inl (i, ζ)] (fun _ => (a, false)) := by
      intro a k
      fin_cases k
      rfl
    have hinvalid : ∀ a : Bool, ¬ networkBranchValid [.inl (i, ζ)] (fun _ => (a, true)) := by
      intro a hv
      have h0 : true = false := hv 0
      exact Bool.noConfusion h0
    have hcount : ((networkCounts [.inl (i, ζ)]).1
        + 2 * (networkCounts [.inl (i, ζ)]).2) = 1 := by
      simp [networkCounts]
    calc ∑ o : Bool × Bool, networkActualStepBranch (.inl (i, ζ)) o A
        = ∑ a : Bool, ∑ b : Bool, networkActualStepBranch (.inl (i, ζ)) (a, b) A :=
          Fintype.sum_prod_type _
      _ = ∑ a : Bool, ((2 : ℂ)⁻¹)
            • conjBranch (networkLogicalMatrix [.inl (i, ζ)]) A := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hbF : networkActualStepBranch (.inl (i, ζ)) (a, false) A
              = ((2 : ℂ)⁻¹) • conjBranch (networkLogicalMatrix [.inl (i, ζ)]) A := by
            rw [(cluster_network_actual_local_step_branches n _ hg).2 (a, false) A,
              if_pos (hvalid a), hcount, pow_one]
          have hbT : networkActualStepBranch (.inl (i, ζ)) (a, true) A = 0 := by
            rw [(cluster_network_actual_local_step_branches n _ hg).2 (a, true) A,
              if_neg (hinvalid a)]
          rw [Fintype.sum_bool, hbF, hbT, zero_add]
      _ = conjBranch (networkLogicalMatrix [.inl (i, ζ)]) A := by
          rw [sum_univ_bool_smul, show ((2 : ℂ) * ((2 : ℂ)⁻¹)) = 1 from by norm_num, one_smul]
  | inr p =>
    obtain ⟨i, j⟩ := p
    have hvalid : ∀ o : Bool × Bool, networkBranchValid [.inr (i, j)] (fun _ => o) := by
      intro o k
      fin_cases k
      trivial
    have hcount : ((networkCounts [.inr (i, j)]).1
        + 2 * (networkCounts [.inr (i, j)]).2) = 2 := by
      simp [networkCounts]
    have hbr : ∀ o : Bool × Bool, networkActualStepBranch (.inr (i, j)) o A
        = ((2 : ℂ)⁻¹) ^ 2 • conjBranch (networkLogicalMatrix [.inr (i, j)]) A := by
      intro o
      rw [(cluster_network_actual_local_step_branches n _ hg).2 o A, if_pos (hvalid o), hcount]
    rw [Finset.sum_congr rfl fun o _ => hbr o, sum_univ_boolPair_smul,
      show ((4 : ℂ) * ((2 : ℂ)⁻¹) ^ 2) = 1 from by norm_num, one_smul]

/-- The sum of all branches of a legal network step preserves the trace of every input operator. -/
theorem networkStepBranch_total (n : ℕ) (g : ClusterNetworkGate n) (hg : networkLegal [g])
    (A : Operator (2 ^ n)) :
    Matrix.trace (∑ o : Bool × Bool, networkActualStepBranch g o A) = Matrix.trace A := by
  rw [networkStepBranch_sum n g hg A, trace_conjBranch_unitary]
  rw [networkLogicalMatrix_cons]
  exact networkGateMatrix_unitary g hg

/-- The four-outcome instrument formed from the actual branches of a legal network step. -/
noncomputable def networkStepInstrument {n : ℕ} (g : ClusterNetworkGate n)
    (hg : networkLegal [g]) : Instrument (Bool × Bool) (2 ^ n) (2 ^ n) :=
  Instrument.ofBranches (networkActualStepBranch g)
    (networkStepBranch_cp n g hg) (networkStepBranch_total n g hg)

/-- Forgetting the outcome of a legal network step yields conjugation by its logical matrix. -/
theorem networkStepInstrument_forget (n : ℕ) (g : ClusterNetworkGate n)
    (hg : networkLegal [g]) (ρ : Operator (2 ^ n)) :
    (networkStepInstrument g hg).forget.map ρ
      = conjBranch (networkLogicalMatrix [g]) ρ := by
  rw [Instrument.forget_apply]
  show ∑ o : Bool × Bool, networkActualStepBranch g o ρ = _
  exact networkStepBranch_sum n g hg ρ

/-- The head of a legal network word is a legal singleton word. -/
theorem networkLegal_cons_self {n : ℕ} (g : ClusterNetworkGate n)
    (gs : List (ClusterNetworkGate n)) (hgs : networkLegal (g :: gs)) :
    networkLegal [g] := by
  intro g' hg'
  rw [List.mem_singleton] at hg'
  subst hg'
  exact hgs _ List.mem_cons_self

/-- The tail of a legal network word is legal. -/
theorem networkLegal_cons_of {n : ℕ} (g : ClusterNetworkGate n)
    (gs : List (ClusterNetworkGate n)) (hgs : networkLegal (g :: gs)) :
    networkLegal gs :=
  fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')

/-- The identity instrument indexed by the unique empty outcome history. -/
noncomputable def networkEmptyInstrument {n : ℕ} :
    Instrument (Fin 0 → Bool × Bool) (2 ^ n) (2 ^ n) :=
  Instrument.ofBranches (fun _ => LinearMap.id)
    (fun _ => networkCP_id) (fun A => by
      show Matrix.trace (∑ o : Fin 0 → Bool × Bool, LinearMap.id A) = Matrix.trace A
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
        one_smul, LinearMap.id_apply])

/-- The sequential instrument of a legal network word, indexed by one Boolean outcome pair per
gate. -/
noncomputable def networkHistoryInstrument {n : ℕ} :
    (gs : List (ClusterNetworkGate n)) → networkLegal gs →
      Instrument (Fin gs.length → Bool × Bool) (2 ^ n) (2 ^ n)
  | [], _ => networkEmptyInstrument
  | g :: gs, hgs =>
      ((networkStepInstrument g (networkLegal_cons_self g gs hgs)).seq
        (networkHistoryInstrument gs (networkLegal_cons_of g gs hgs))).coarsen
        (Fin.consEquiv (fun _ : Fin (gs.length + 1) => Bool × Bool))

/-- Forgetting the outcomes of a sequential composition applies the first forgotten channel and
then the second. -/
theorem networkForget_seq_apply {n : ℕ} {O P : Type*} [Fintype O] [Fintype P]
    (I : Instrument O (2 ^ n) (2 ^ n)) (J : Instrument P (2 ^ n) (2 ^ n))
    (ρ : Operator (2 ^ n)) :
    (I.seq J).forget.map ρ = J.forget.map (I.forget.map ρ) := by
  calc (I.seq J).forget.map ρ
      = ∑ o : O, ∑ p : P, J.branch p (I.branch o ρ) := by
        rw [Instrument.forget_apply]
        rw [Finset.sum_congr rfl fun op _ =>
          LinearMap.comp_apply (J.branch op.2) (I.branch op.1) ρ]
        exact Fintype.sum_prod_type _
    _ = ∑ o : O, J.forget.map (I.branch o ρ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Instrument.forget_apply]
    _ = J.forget.map (I.forget.map ρ) := by
        rw [← map_sum, Instrument.forget_apply I ρ]

/-- A history for a nonempty network word is valid exactly when its head outcome and tail
history are valid. -/
theorem networkBranchValid_cons {n : ℕ} (g : ClusterNetworkGate n)
    (gs : List (ClusterNetworkGate n)) (hist : Fin (g :: gs).length → Bool × Bool) :
    networkBranchValid (g :: gs) hist ↔
      networkBranchValid [g] (fun _ => hist 0) ∧ networkBranchValid gs (Fin.tail hist) := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => h k.succ⟩
    fin_cases k
    exact h 0
  · rintro ⟨h0, h1⟩ k
    exact Fin.cases (h0 0) h1 k

/-- The weighted count of a nonempty network word is the sum of the weighted counts of its head
and tail. -/
theorem networkCounts_cons {n : ℕ} (g : ClusterNetworkGate n)
    (gs : List (ClusterNetworkGate n)) :
    (networkCounts (g :: gs)).1 + 2 * (networkCounts (g :: gs)).2
      = ((networkCounts [g]).1 + 2 * (networkCounts [g]).2)
        + ((networkCounts gs).1 + 2 * (networkCounts gs).2) := by
  cases g <;> simp [networkCounts] <;> omega

/-- The logical matrix of a nonempty network word is the tail matrix multiplied by the singleton
head matrix. -/
theorem networkLogicalMatrix_cons' {n : ℕ} (g : ClusterNetworkGate n)
    (gs : List (ClusterNetworkGate n)) :
    networkLogicalMatrix (g :: gs) = networkLogicalMatrix gs * networkLogicalMatrix [g] := by
  rw [networkLogicalMatrix_cons]
  rfl

/-- Conjugation by a unitary tensored with an identity preserves the trace of an arbitrary
bipartite operator. -/
theorem networkTrace_tensorGate_conj {D R : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (TensorGate U (1 : Operator R) * X * (TensorGate U (1 : Operator R))ᴴ)
      = Matrix.trace X := by
  have hunit : (TensorGate U (1 : Operator R)).conjTranspose * TensorGate U (1 : Operator R)
      = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rw [Matrix.star_eq_conjTranspose] at h
    rw [tensorGate_conjTranspose, tensorGate_mul, h, Matrix.conjTranspose_one, Matrix.mul_one,
      tensorGate_one]
  rw [Matrix.trace_mul_cycle, hunit, Matrix.one_mul]

/-- Each history branch of a legal network word is logical conjugation scaled by `2^(-w-2c)` on
valid histories and zero otherwise, where `w` and `c` are its wire and controlled-Z counts. -/
theorem cluster_network_history_actual_branch_formula :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hgs : networkLegal gs)
      (hist : Fin gs.length → Bool × Bool) (ρ : Operator (2 ^ n)),
      (networkHistoryInstrument gs hgs).branch hist ρ
        = (if networkBranchValid gs hist
          then (((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2)
              • conjBranch (networkLogicalMatrix gs) ρ)
          else 0) := by
  intro n gs
  induction gs with
  | nil =>
    intro hgs hist ρ
    have hvalid : networkBranchValid [] hist := fun k => absurd k.isLt (by simp)
    have hbranch : (networkHistoryInstrument [] hgs).branch hist ρ = ρ := rfl
    rw [hbranch, if_pos hvalid]
    rw [show ((networkCounts []).1 + 2 * (networkCounts []).2) = 0 from rfl, pow_zero, one_smul,
      show networkLogicalMatrix ([] : List (ClusterNetworkGate n))
          = (1 : Operator (2 ^ n)) from rfl]
    simp
  | cons g gs ih =>
    intro hgs hist ρ
    have hsingle : networkLegal [g] := networkLegal_cons_self g gs hgs
    have htail : networkLegal gs := networkLegal_cons_of g gs hgs
    have hcomp : conjBranch (networkLogicalMatrix gs) (conjBranch (networkLogicalMatrix [g]) ρ)
        = conjBranch (networkLogicalMatrix gs * networkLogicalMatrix [g]) ρ := by
      show ((conjBranch (networkLogicalMatrix gs)).comp
          (conjBranch (networkLogicalMatrix [g]))) ρ = _
      rw [conjBranch_comp]
    show (((networkStepInstrument g hsingle).seq
          (networkHistoryInstrument gs htail)).coarsen
          (Fin.consEquiv (fun _ : Fin (gs.length + 1) => Bool × Bool))).branch hist ρ = _
    rw [Instrument.coarsen_branch_equiv_apply]
    show ((networkHistoryInstrument gs htail).branch (Fin.tail hist)).comp
        ((networkStepInstrument g hsingle).branch (hist 0)) ρ = _
    rw [LinearMap.comp_apply,
      show (networkStepInstrument g hsingle).branch (hist 0) ρ
          = networkActualStepBranch g (hist 0) ρ from rfl,
      (cluster_network_actual_local_step_branches n g hsingle).2 (hist 0) ρ]
    by_cases hV1 : networkBranchValid [g] (fun _ => hist 0)
    · rw [if_pos hV1, map_smul]
      by_cases hV2 : networkBranchValid gs (Fin.tail hist)
      · rw [(ih htail (Fin.tail hist) (conjBranch (networkLogicalMatrix [g]) ρ)), if_pos hV2,
          hcomp, smul_smul, ← pow_add,
          if_pos ((networkBranchValid_cons g gs hist).mpr ⟨hV1, hV2⟩),
          networkCounts_cons g gs, networkLogicalMatrix_cons' g gs]
      · rw [(ih htail (Fin.tail hist) (conjBranch (networkLogicalMatrix [g]) ρ)), if_neg hV2,
          smul_zero,
          if_neg (fun hv => hV2 ((networkBranchValid_cons g gs hist).mp hv).2)]
    · rw [if_neg hV1, map_zero,
        if_neg (fun hv => hV1 ((networkBranchValid_cons g gs hist).mp hv).1)]

/-- A legal network word has a unitary logical matrix, and forgetting its history implements
conjugation by that matrix on every input operator. -/
theorem cluster_network_forget_correct_arbitrary_input :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hgs : networkLegal gs),
      networkLogicalMatrix gs ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      ∀ ρ : Operator (2 ^ n),
        (networkHistoryInstrument gs hgs).forget.map ρ
          = conjBranch (networkLogicalMatrix gs) ρ := by
  intro n gs
  induction gs with
  | nil =>
    intro hgs
    refine ⟨Submonoid.one_mem _, ?_⟩
    intro ρ
    rw [Instrument.forget_apply]
    show ∑ o : Fin 0 → Bool × Bool, LinearMap.id ρ
        = conjBranch (networkLogicalMatrix ([] : List (ClusterNetworkGate n))) ρ
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
      one_smul, LinearMap.id_apply,
      show networkLogicalMatrix ([] : List (ClusterNetworkGate n))
          = (1 : Operator (2 ^ n)) from rfl]
    simp
  | cons g gs ih =>
    intro hgs
    have hsingle : networkLegal [g] := networkLegal_cons_self g gs hgs
    have htail : networkLegal gs := networkLegal_cons_of g gs hgs
    refine ⟨networkLogicalMatrix_unitary (g :: gs) hgs, ?_⟩
    intro ρ
    have hcomp : conjBranch (networkLogicalMatrix gs) (conjBranch (networkLogicalMatrix [g]) ρ)
        = conjBranch (networkLogicalMatrix (g :: gs)) ρ := by
      show ((conjBranch (networkLogicalMatrix gs)).comp
          (conjBranch (networkLogicalMatrix [g]))) ρ = _
      rw [conjBranch_comp, networkLogicalMatrix_cons' g gs]
    show (((networkStepInstrument g hsingle).seq
          (networkHistoryInstrument gs htail)).coarsen
          (Fin.consEquiv (fun _ : Fin (gs.length + 1) => Bool × Bool))).forget.map ρ = _
    rw [Instrument.forget_coarsen_apply, networkForget_seq_apply,
      networkStepInstrument_forget n g hsingle ρ,
      (ih htail).2 (conjBranch (networkLogicalMatrix [g]) ρ), hcomp]

/-- The forgotten network channel acts as logical conjugation even with an untouched reference
system. Each valid history has trace weight `2^(-w-2c)` times the input trace, while invalid
histories have zero trace. -/
theorem cluster_network_entangled_reference_and_record_mass :
    ∀ (n r : ℕ) (gs : List (ClusterNetworkGate n)) (hgs : networkLegal gs)
      (X : Matrix (Fin (2 ^ n) × Fin r) (Fin (2 ^ n) × Fin r) ℂ),
      tensorLeft (networkHistoryInstrument gs hgs).forget.map X
        = TensorGate (networkLogicalMatrix gs) (1 : Operator r) * X
          * (TensorGate (networkLogicalMatrix gs) (1 : Operator r))ᴴ ∧
      ∀ hist : Fin gs.length → Bool × Bool,
        (Matrix.trace (tensorLeft ((networkHistoryInstrument gs hgs).branch hist) X)).re
          = (if networkBranchValid gs hist
            then (((2 : ℝ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2)
                * (Matrix.trace X).re)
            else 0) := by
  intro n r gs hgs X
  have hmap : (networkHistoryInstrument gs hgs).forget.map
      = conjBranch (networkLogicalMatrix gs) :=
    LinearMap.ext fun ρ =>
      (cluster_network_forget_correct_arbitrary_input n gs hgs).2 ρ
  refine ⟨?_, ?_⟩
  · rw [hmap, tensorLeft_conjBranch]
  · intro hist
    by_cases hv : networkBranchValid gs hist
    · have hbm : (networkHistoryInstrument gs hgs).branch hist
          = (((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2))
            • conjBranch (networkLogicalMatrix gs) := by
        apply LinearMap.ext
        intro ρ
        rw [(cluster_network_history_actual_branch_formula n gs hgs hist ρ), if_pos hv,
          LinearMap.smul_apply]
      have htsmul : tensorLeft
            ((((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2))
              • conjBranch (networkLogicalMatrix gs)) X
          = (((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2))
            • tensorLeft (conjBranch (networkLogicalMatrix gs)) X := by
        ext x y
        simp only [tensorLeft, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hbm, htsmul, Matrix.trace_smul, smul_eq_mul, tensorLeft_conjBranch,
        networkTrace_tensorGate_conj _
          (cluster_network_forget_correct_arbitrary_input n gs hgs).1 X,
        networkHalf_pow_cast, if_pos hv, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    · have hbm : (networkHistoryInstrument gs hgs).branch hist = 0 := by
        apply LinearMap.ext
        intro ρ
        rw [(cluster_network_history_actual_branch_formula n gs hgs hist ρ), if_neg hv,
          LinearMap.zero_apply]
      have htzero : tensorLeft (0 : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n)) X = 0 := by
        ext x y
        simp [tensorLeft]
      rw [hbm, htzero, if_neg hv]
      simp
end Qatlib.Concepts.MbqcFlow.FlowDecision
