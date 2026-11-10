/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs
import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.LinearAlgebra.Semisimple
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianIrrep
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian.TopBitBundle

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false

open Qatlib
open scoped BigOperators

theorem clause27_costs (N : ℕ) [NeZero N] (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S] :
    QueryCount (dihedralRecordCircuit (N := N) (S := S)) = 1 ∧
      GateCount (dihedralRecordCircuit (N := N) (S := S)) = 1 := by
  refine ⟨?_, ?_⟩ <;> simp [dihedralRecordCircuit, QueryCount, GateCount]

theorem clause27_recordFactor (N : ℕ) [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    ∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
      ∀ t : Bool, ∀ z : S,
        dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t := by
  have hlaw : ∀ (M : ℕ) [NeZero M] (T : Type) [Fintype T] [DecidableEq T] [AddCommGroup T]
    (g : DihedralReg M → T) (u : ZMod M),
    DihedralReflectionHides M g u →
      QueryCount (dihedralRecordCircuit (N := M) (S := T)) = 1 ∧
      GateCount (dihedralRecordCircuit (N := M) (S := T)) = 1 ∧
      ∀ k : ZMod M, ∃ γ : T → ℂ, (∑ z : T, ‖γ z‖ ^ 2) = 1 / (M : ℝ) ∧
        ∀ t z, dihedralRecordJoint M g ((k, t), z) = γ z * dihedralQubitState M u k t :=
    Qatlib.Concepts.HspRecovery.RecordExtract.sourceGeneralRecordLaw
  exact (hlaw N S f s hf).2.2

theorem clause27_extraction_conjunct (N : ℕ) [NeZero N] (s k ℓ : ZMod N) :
    ∃ xiPlus xiMinus : QState Bool, ∃ uPlus uMinus : ℂ,
      ‖uPlus‖ = 1 ∧ ‖uMinus‖ = 1 ∧
      xiPlus = uPlus • dihedralQubitState N s (k + ℓ) ∧
      xiMinus = uMinus • dihedralQubitState N s (k - ℓ) ∧
      ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
        dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
          (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ)
          (b, ⟨ξ, hξ⟩) =
          if (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) then
            (1 / 2 : NNReal) else 0 := by
  obtain ⟨xiPlus, xiMinus, -, -, uPlus, uMinus, huPlus, huMinus, hPlus, hMinus, hex⟩ :=
    dihedralExtractionLaw N s k ℓ
  refine ⟨xiPlus, xiMinus, uPlus, uMinus, huPlus, huMinus, hPlus, hMinus, ?_⟩
  intro b ξ hξ
  rw [hex b ξ hξ]
  split_ifs
  · norm_num
  · rfl

theorem clause27_actual_apply {N : ℕ} [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (k : ZMod N) (t : Bool) (z : S) :
    actualRecordFiniteLaw f (k, t, z) =
      ENNReal.ofReal (BornProb (dihedralRecordJoint N f) ((k, t), z)) := by
  show (bornDistribution (dihedralRecordJoint N f) (normalized_dihedralRecordJoint N f)).map
    (fun q : (ZMod N × Bool) × S => (q.1.1, q.1.2, q.2)) (k, t, z) = _
  rw [PMF.map_apply]
  have hinj : Function.Injective (fun q : (ZMod N × Bool) × S => (q.1.1, q.1.2, q.2)) := by
    intro a₁ a₂ h
    rcases a₁ with ⟨⟨a, b⟩, w⟩
    rcases a₂ with ⟨⟨a', b'⟩, w'⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  have key : (∑' q : (ZMod N × Bool) × S,
      @ite ENNReal ((k, t, z) = (q.1.1, q.1.2, q.2)) (Classical.propDecidable _)
        (bornDistribution (dihedralRecordJoint N f) (normalized_dihedralRecordJoint N f) q) 0) =
      ENNReal.ofReal (BornProb (dihedralRecordJoint N f) ((k, t), z)) := by
    have hzero : ∀ q : (ZMod N × Bool) × S, q ≠ ((k, t), z) →
        @ite ENNReal ((k, t, z) = (q.1.1, q.1.2, q.2)) (Classical.propDecidable _)
          (bornDistribution (dihedralRecordJoint N f) (normalized_dihedralRecordJoint N f) q) 0 = 0 := by
      intro q hq
      apply if_neg
      intro heq
      exact hq (hinj ((rfl : (fun q : (ZMod N × Bool) × S => (q.1.1, q.1.2, q.2)) ((k, t), z)
        = (k, t, z)).trans heq)).symm
    rw [tsum_eq_single ((k, t), z) hzero]
    apply if_pos
    rfl
  rw [key]

theorem clause27_bitMarginal {N : ℕ} [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) (t : Bool) :
    ∑' z : S, actualRecordFiniteLaw f (k, t, z) = ENNReal.ofReal (1 / (2 * (N : ℝ))) := by
  obtain ⟨γ, hnorm, hfactor⟩ := clause27_recordFactor N S f s hf k
  have hmass : (∑' z : S, actualRecordFiniteLaw f (k, t, z)) =
      ENNReal.ofReal (∑ z : S, BornProb (dihedralRecordJoint N f) ((k, t), z)) := by
    conv_lhs => simp only [clause27_actual_apply]
    rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
    exact fun z _ => bornProb_nonneg _ _
  rw [hmass]
  have hborn : ∀ z : S, BornProb (dihedralRecordJoint N f) ((k, t), z) = ‖γ z‖ ^ 2 * (1 / 2) := by
    intro z
    unfold BornProb
    rw [hfactor, norm_mul, mul_pow]
    have hb : ‖dihedralQubitState N s k t‖ ^ 2 = 1 / 2 := dihedralQubitState_born N s k t
    rw [hb]
  conv_lhs => simp only [hborn]
  rw [← Finset.sum_mul, hnorm]
  congr 1
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
  field_simp [hN]

theorem clause2_combineRecords_eq {N : ℕ} (a : ℕ) (r₁ r₂ : HalfWidthRecord N) :
    combineRecords a r₁ r₂ = ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩ :=
  rfl

theorem clause2_resourceCounts (m L0 : ℕ) :
    ∃ (samples records extractions : ℕ),
      samples = L0 ∧ records = 2 * L0 ∧ extractions = L0 ∧
      (L0 = sieveFreshRecordCount m →
        records = sieveRecordCount m ∧ samples = sieveFreshRecordCount m) := by
  refine ⟨L0, 2 * L0, L0, rfl, rfl, rfl, ?_⟩
  intro h
  refine ⟨?_, h⟩
  show 2 * L0 = sieveRecordCount m
  rw [h]
  rfl

theorem clause2_stageLaw {N : ℕ} [NeZero N] (a q w L0 m : ℕ) :
    ∃ (stageLaw : Fin (m + 1) → PMF (List (HalfWidthRecord N))),
      stageLaw 0 = freshHalfWidthRecords N w L0 ∧
      (∀ j : Fin m, stageLaw j.succ = (stageLaw j.castSucc).bind (layerCombine a q)) ∧
      stageLaw ⟨m, by omega⟩ =
        (freshHalfWidthRecords N w L0).bind (layeredCombine a q m) := by
  refine ⟨fun j => (freshHalfWidthRecords N w L0).bind (layeredCombine a q j.val), ?_, ?_, ?_⟩
  · show (freshHalfWidthRecords N w L0).bind (layeredCombine a q 0) = _
    exact PMF.bind_pure _
  · intro j
    show (freshHalfWidthRecords N w L0).bind (layeredCombine a q (j.val + 1)) =
      ((freshHalfWidthRecords N w L0).bind (layeredCombine a q j.val)).bind (layerCombine a q)
    rw [PMF.bind_bind]
    rfl
  · rfl

theorem clause2_pairWindowMod_length {N : ℕ} (q : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod N) (L : List α) :
    (pairWindowMod q label L).length * 2 ≤ L.length ∧
      L.length - (pairWindowMod q label L).length * 2 ≤ L.length := by
  refine ⟨?_, ?_⟩
  · fun_induction pairWindowMod q label L
    · simp
    · rename_i r rest h ih
      simp only [List.length_cons]
      omega
    · rename_i r rest r' h ih
      have hm : r' ∈ rest := List.mem_of_find?_eq_some h
      have hl := List.length_erase_add_one hm
      simp only [List.length_cons]
      omega
  · exact Nat.sub_le _ _

section Clause28Counterexamples

open scoped Classical

theorem clause2_run_at_zero {N : ℕ} [NeZero N] (a q w L0 : ℕ) :
    (freshHalfWidthRecords N w L0).bind (layeredCombine a q 0)
      = freshHalfWidthRecords N w L0 :=
  PMF.bind_pure _

theorem clause2_fresh_one :
    freshHalfWidthRecords 2 0 1 =
      (PMF.uniformOfFintype' (ZMod 2)).bind
        (fun k : ZMod 2 => (PMF.pure [(⟨k, 0⟩ : HalfWidthRecord 2)] :
          PMF (List (HalfWidthRecord 2)))) := by
  have h0 : freshHalfWidthRecords 2 0 0 =
      (PMF.pure ([] : List (HalfWidthRecord 2))) := rfl
  show (PMF.uniformOfFintype' (ZMod 2)).bind
      (fun k => ((freshHalfWidthRecords 2 0 0).map
        (fun L => (⟨k, 0⟩ : HalfWidthRecord 2) :: L))) = _
  simp only [h0]
  congr 1
  funext k
  exact PMF.pure_map _ _

theorem clause2_run_mass_zero :
    ((freshHalfWidthRecords 2 0 1).bind (layeredCombine 1 1 0))
      [⟨(0 : ZMod 2), 0⟩] = (2⁻¹ : ENNReal) := by
  rw [clause2_run_at_zero, clause2_fresh_one, PMF.bind_apply]
  have hsum : (∑' k : ZMod 2,
      (PMF.uniformOfFintype' (ZMod 2)) k *
        (PMF.pure [(⟨k, 0⟩ : HalfWidthRecord 2)] : PMF (List (HalfWidthRecord 2)))
          [⟨(0 : ZMod 2), 0⟩]) =
      ∑ k : ZMod 2,
      (PMF.uniformOfFintype' (ZMod 2)) k *
        (PMF.pure [(⟨k, 0⟩ : HalfWidthRecord 2)] : PMF (List (HalfWidthRecord 2)))
          [⟨(0 : ZMod 2), 0⟩] := tsum_fintype _
  rw [hsum]
  have hpure : ∀ k : ZMod 2,
      ((PMF.pure [(⟨k, 0⟩ : HalfWidthRecord 2)] : PMF (List (HalfWidthRecord 2)))
        [⟨(0 : ZMod 2), 0⟩]) = if (0 : ZMod 2) = k then (1 : ENNReal) else 0 := by
    intro k
    rw [PMF.pure_apply]
    simp only [List.cons.injEq, and_true, HalfWidthRecord.mk.injEq]
  simp only [hpure, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [PMF.uniformOfFintype'_apply, ZMod.card]
  norm_num

theorem clause2_noHit_zero :
    ¬(∃ r : HalfWidthRecord 2, r ∈ [⟨(0 : ZMod 2), 0⟩] ∧ isIdealHit 2 r) := by
  rintro ⟨r, hr, hi⟩
  simp only [List.mem_singleton] at hr
  subst hr
  simp [isIdealHit] at hi

theorem clause2_idealHit_conjunct_false :
    ¬(ENNReal.ofReal (idealHitLowerBound 0) ≤
      ∑' L : List (HalfWidthRecord 2),
        if (∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then
          ((freshHalfWidthRecords 2 0 1).bind (layeredCombine 1 1 0)) L else 0) := by
  set run : PMF (List (HalfWidthRecord 2)) :=
    (freshHalfWidthRecords 2 0 1).bind (layeredCombine 1 1 0) with hrun
  intro hle
  have hbound : idealHitLowerBound 0 = 1 := by
    show (1 - Real.exp (-(2:ℝ) ^ ((0:ℝ) / 3 - 2))) ^ 0 = 1
    simp
  have h1 : ENNReal.ofReal (idealHitLowerBound 0) = (1 : ENNReal) := by
    rw [hbound, ENNReal.ofReal_one]
  rw [h1] at hle
  have hsum : (∑' L : List (HalfWidthRecord 2), run L) = 1 := PMF.tsum_coe run
  have hpoint : ∀ L : List (HalfWidthRecord 2),
      run L =
        (if (∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then run L else 0) +
        (if ¬(∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then run L else 0) := by
    intro L
    by_cases h : ∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r <;> simp [h]
  have hsplit : (1 : ENNReal) =
      (∑' L : List (HalfWidthRecord 2), if (∃ r, r ∈ L ∧ isIdealHit 2 r) then run L else 0) +
      (∑' L : List (HalfWidthRecord 2), if ¬(∃ r, r ∈ L ∧ isIdealHit 2 r) then run L else 0) := by
    rw [← hsum]
    have hadd := ENNReal.tsum_add
      (f := fun L : List (HalfWidthRecord 2) =>
        (if (∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then run L else 0))
      (g := fun L : List (HalfWidthRecord 2) =>
        (if ¬(∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then run L else 0))
    rw [← hadd]
    exact tsum_congr hpoint
  have hmass : run [⟨(0 : ZMod 2), 0⟩] = (2⁻¹ : ENNReal) := by
    rw [hrun]
    exact clause2_run_mass_zero
  have hnohit : ¬(∃ r : HalfWidthRecord 2, r ∈ [⟨(0 : ZMod 2), 0⟩] ∧ isIdealHit 2 r) :=
    clause2_noHit_zero
  have hHc : (2⁻¹ : ENNReal) ≤
      (∑' L : List (HalfWidthRecord 2),
        if ¬(∃ r, r ∈ L ∧ isIdealHit 2 r) then run L else 0) := by
    have h := ENNReal.le_tsum
      (f := fun L : List (HalfWidthRecord 2) =>
        (if ¬(∃ r : HalfWidthRecord 2, r ∈ L ∧ isIdealHit 2 r) then run L else 0))
      (a := [⟨(0 : ZMod 2), 0⟩])
    have hval : (if ¬(∃ r : HalfWidthRecord 2, r ∈ [⟨(0 : ZMod 2), 0⟩] ∧ isIdealHit 2 r) then
        run [⟨(0 : ZMod 2), 0⟩] else 0) = (2⁻¹ : ENNReal) := by
      rw [if_pos hnohit, hmass]
    rw [hval] at h
    exact h
  have hsum2 : (1 : ENNReal) + 2⁻¹ ≤ 1 := by
    have h2 := add_le_add hle hHc
    rw [← hsplit] at h2
    exact h2
  have hsub : (2⁻¹ : ENNReal) ≤ 0 := by
    have hiff :
        ((1 : ENNReal) + (2 : ENNReal)⁻¹ ≤ 1 + 0 ↔ (2 : ENNReal)⁻¹ ≤ 0) :=
      ENNReal.add_le_add_iff_left (a := (1 : ENNReal)) (show (1 : ENNReal) ≠ ⊤ from by norm_num)
    exact hiff.mp (by simpa using hsum2)
  have hpos : (0 : ENNReal) < 2⁻¹ := ENNReal.inv_pos.mpr (by norm_num)
  exact absurd hsub (not_le_of_gt hpos)

theorem clause2_is_false :
    ¬(∀ (N : ℕ) [NeZero N] (a q w L0 : ℕ) (_ha : LegalSlopeFactor a) (_hq : 0 < q)
      (_hL0 : 0 < L0) (m : ℕ),
      let run : PMF (List (HalfWidthRecord N)) :=
        (freshHalfWidthRecords N w L0).bind (layeredCombine a q m)
      (∃ (stageLaw : Fin (m + 1) → PMF (List (HalfWidthRecord N))),
        stageLaw 0 = freshHalfWidthRecords N w L0 ∧
        (∀ j : Fin m, stageLaw j.succ = (stageLaw j.castSucc).bind (layerCombine a q)) ∧
        stageLaw ⟨m, by omega⟩ = run)
      ∧
      (∀ r₁ r₂ : HalfWidthRecord N,
        combineRecords a r₁ r₂ = ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩)
      ∧
      (∀ (L : List (HalfWidthRecord N)),
        (pairWindowMod q HalfWidthRecord.label L).length * 2 ≤ L.length ∧
        L.length - (pairWindowMod q HalfWidthRecord.label L).length * 2 ≤ L.length)
      ∧
      (ENNReal.ofReal (idealHitLowerBound m) ≤
        ∑' L : List (HalfWidthRecord N),
          if (∃ r : HalfWidthRecord N, r ∈ L ∧ isIdealHit N r) then run L else 0)
      ∧
      ((∑' L : List (HalfWidthRecord N),
          if ¬(∃ r : HalfWidthRecord N, r ∈ L ∧ isIdealHit N r) then run L else 0) ≤
        ENNReal.ofReal (failureMass m))
      ∧
      (∃ (samples records extractions : ℕ),
        samples = L0 ∧ records = 2 * L0 ∧ extractions = L0 ∧
        (L0 = sieveFreshRecordCount m →
          records = sieveRecordCount m ∧ samples = sieveFreshRecordCount m))) := by
  intro h
  have hconj := h 2 1 1 0 1 (show LegalSlopeFactor 1 from le_refl 1)
    (show (0 : ℕ) < 1 from by norm_num) (show (0 : ℕ) < 1 from by norm_num) 0
  exact clause2_idealHit_conjunct_false hconj.2.2.2.1

end Clause28Counterexamples

theorem clause27_labelMarginal {N : ℕ} [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) :
    (∑' t : Bool, ∑' z : S, actualRecordFiniteLaw f (k, t, z)) =
      ENNReal.ofReal (1 / (N : ℝ)) := by
  have htrue : ∑' z : S, actualRecordFiniteLaw f (k, true, z) =
      ENNReal.ofReal (1 / (2 * (N : ℝ))) := clause27_bitMarginal S f s hf k true
  have hfalse : ∑' z : S, actualRecordFiniteLaw f (k, false, z) =
      ENNReal.ofReal (1 / (2 * (N : ℝ))) := clause27_bitMarginal S f s hf k false
  rw [tsum_fintype, Fintype.sum_bool, htrue, hfalse]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
  field_simp [hN]; norm_num

theorem clause27_map_fst_apply {α β : Type} [Fintype α] [Fintype β] (p : PMF (α × β)) (a : α) :
    p.map Prod.fst a = ∑' b : β, p (a, b) := by
  rw [PMF.map_apply]
  have hprod : (∑' q : α × β,
      @ite ENNReal (a = q.1) (Classical.propDecidable _) (p q) 0) =
      ∑' a' : α, ∑' b : β, @ite ENNReal (a = a') (Classical.propDecidable _) (p (a', b)) 0 := by
    rw [ENNReal.tsum_prod']
  rw [hprod, ENNReal.tsum_comm]
  have hz : (∑' b : β, ∑' a' : α,
      @ite ENNReal (a = a') (Classical.propDecidable _) (p (a', b)) 0) =
      ∑' b : β, p (a, b) := by
    congr 1
    funext b
    have hsingle : (∑' a' : α,
        @ite ENNReal (a = a') (Classical.propDecidable _) (p (a', b)) 0) =
        @ite ENNReal (a = a) (Classical.propDecidable _) (p (a, b)) 0 := by
      refine tsum_eq_single a ?_
      intro a' ha'
      apply if_neg
      intro heq
      exact ha' heq.symm
    rw [hsingle, if_pos rfl]
  rw [hz]

theorem clause27_map_fst2_apply {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF (α × (β × γ))) (a : α) (b : β) :
    p.map (fun q : α × (β × γ) => (q.1, q.2.1)) (a, b) = ∑' c : γ, p (a, (b, c)) := by
  rw [PMF.map_apply]
  have hprod : (∑' q : α × (β × γ),
      @ite ENNReal ((a, b) = (q.1, q.2.1)) (Classical.propDecidable _) (p q) 0) =
      ∑' ab : α × β, ∑' c : γ,
        @ite ENNReal ((a, b) = ab) (Classical.propDecidable _) (p (ab.1, (ab.2, c))) 0 := by
    rw [← Equiv.tsum_eq (Equiv.prodAssoc α β γ), ENNReal.tsum_prod']
    exact rfl
  rw [hprod]
  let hfun : α × β → ENNReal := fun ab => ∑' c : γ,
    @ite ENNReal ((a, b) = ab) (Classical.propDecidable _) (p (ab.1, (ab.2, c))) 0
  have hzero : ∀ ab : α × β, ab ≠ (a, b) → hfun ab = 0 := by
    intro ab hab
    show (∑' c : γ,
      @ite ENNReal ((a, b) = ab) (Classical.propDecidable _) (p (ab.1, (ab.2, c))) 0) = 0
    apply ENNReal.tsum_eq_zero.mpr
    intro c
    apply if_neg
    intro heq
    exact hab heq.symm
  have houter : (∑' ab : α × β, hfun ab) = hfun (a, b) :=
    tsum_eq_single (a, b) hzero
  show (∑' ab : α × β, hfun ab) = ∑' c : γ, p (a, (b, c))
  rw [houter]
  show (∑' c : γ,
    @ite ENNReal ((a, b) = (a, b)) (Classical.propDecidable _)
      (p ((a, b).1, ((a, b).2, c))) 0) = ∑' c : γ, p (a, (b, c))
  congr 1
  funext c
  exact if_pos rfl

theorem clause27_exists_stages {N : ℕ} [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    ∃ (stages : StagedPmfBridge (recordStages N S) 2),
      (stages.law 0 = actualRecordFiniteLaw f) ∧
      (∀ k : ZMod N, ∀ t : Bool, ENNReal.toReal (stages.law 1 (k, t)) = 1 / (2 * N)) ∧
      (∀ k : ZMod N, ENNReal.toReal (stages.law 2 k) = 1 / N) := by
  let l0 : PMF (recordStages N S 0) := actualRecordFiniteLaw f
  let l1 : PMF (recordStages N S 1) :=
    (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1))
  let l2 : PMF (recordStages N S 2) := l1.map Prod.fst
  let law : (j : Fin 3) → PMF (recordStages N S ↑j) :=
    Fin.cases (motive := fun j => PMF (recordStages N S ↑j))
      l0
      (fun i : Fin 2 => Fin.cases (motive := fun i => PMF (recordStages N S ↑i.succ))
        (show PMF (recordStages N S ↑((0 : Fin 2).succ)) from l1)
        (fun i' : Fin 1 => Fin.cases (motive := fun i' => PMF (recordStages N S ↑i'.succ.succ))
          (show PMF (recordStages N S ↑((0 : Fin 1).succ.succ)) from l2)
          (fun j' : Fin 0 => Fin.elim0 j')
          i')
        i)
  let step : (j : Fin 2) → recordStages N S ↑j.castSucc → recordStages N S ↑j.succ :=
    Fin.cases (motive := fun j => recordStages N S ↑j.castSucc → recordStages N S ↑j.succ)
      (show recordStages N S ↑((0 : Fin 2).castSucc) → recordStages N S ↑((0 : Fin 2).succ) from
        fun q : ZMod N × Bool × S => (q.1, q.2.1))
      (fun i : Fin 1 => Fin.cases
        (motive := fun i => recordStages N S ↑i.succ.castSucc → recordStages N S ↑i.succ.succ)
        (show recordStages N S ↑((0 : Fin 1).succ.castSucc) →
            recordStages N S ↑((0 : Fin 1).succ.succ) from
          fun q : ZMod N × Bool => q.1)
        (fun j' : Fin 0 => Fin.elim0 j')
        i)
  have htransport : ∀ j : Fin 2, law j.succ = (law j.castSucc).map (step j) := by
    refine Fin.cases (motive := fun j => law j.succ = (law j.castSucc).map (step j)) ?_ ?_
    · rfl
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi]
      rfl
  refine ⟨⟨law, step, htransport⟩, ?_, ?_, ?_⟩
  · rfl
  · intro k t
    have hval : law (1 : Fin 3) (k, t) = ENNReal.ofReal (1 / (2 * (N : ℝ))) := by
      show (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1)) (k, t) = _
      rw [clause27_map_fst2_apply]
      exact clause27_bitMarginal S f s hf k t
    show ENNReal.toReal (law (1 : Fin 3) (k, t)) = 1 / (2 * N)
    rw [hval]
    exact ENNReal.toReal_ofReal (by positivity)
  · intro k
    have hval : law (2 : Fin 3) k = ENNReal.ofReal (1 / (N : ℝ)) := by
      show ((actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1))).map
        Prod.fst k = _
      rw [clause27_map_fst_apply]
      have ht : ∀ t : Bool,
          ((actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1))) (k, t) =
            ENNReal.ofReal (1 / (2 * (N : ℝ))) := by
        intro t
        rw [clause27_map_fst2_apply]
        exact clause27_bitMarginal S f s hf k t
      rw [tsum_fintype, Fintype.sum_bool, ht true, ht false]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
      field_simp [hN]; norm_num
    show ENNReal.toReal (law (2 : Fin 3) k) = 1 / N
    rw [hval]
    exact ENNReal.toReal_ofReal (by positivity)

theorem clause27_sum_triple {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α × β × γ → ℝ) :
    ∑ q : α × β × γ, f q = ∑ a : α, ∑ b : β, ∑ c : γ, f (a, (b, c)) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]

theorem clause27_toReal_bitMarginal {N : ℕ} [NeZero N] (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) (t : Bool) :
    ∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) = 1 / (2 * (N : ℝ)) := by
  have hfin : ∀ z : S, actualRecordFiniteLaw f (k, t, z) ≠ ⊤ := by
    intro z hz
    have hle : actualRecordFiniteLaw f (k, t, z) ≤
        ∑' z' : S, actualRecordFiniteLaw f (k, t, z') :=
      ENNReal.le_tsum (f := fun z' : S => actualRecordFiniteLaw f (k, t, z')) (a := z)
    rw [clause27_bitMarginal S f s hf k t, hz] at hle
    exact ENNReal.ofReal_ne_top ((le_antisymm hle le_top).symm)
  rw [← ENNReal.toReal_sum fun z _ => hfin z,
    ← tsum_fintype (L := SummationFilter.unconditional S),
    clause27_bitMarginal S f s hf k t]
  exact ENNReal.toReal_ofReal (by positivity)

noncomputable def transportRowOf {N : ℕ} [NeZero N] {Label : Type} [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N)
    (e : ZMod N ≃ Σ V : Label, Fin ((family.irrep V).dim * dimFixed (family.irrep V) s))
    (k : ZMod N) : ℕ :=
  ((finProdFinEquiv (m := (family.irrep ((e k).1)).dim)
    (n := dimFixed (family.irrep ((e k).1)) s)).symm (e k).2).2.val

theorem clause27_transport_row_count {N : ℕ} [NeZero N] {Label : Type} [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N)
    (e : ZMod N ≃ Σ V : Label, Fin ((family.irrep V).dim * dimFixed (family.irrep V) s))
    (V : Label) (row : Fin (dimFixed (family.irrep V) s)) :
    ∑ k : ZMod N, ∑ _t : Bool,
      (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0)
      = ((family.irrep V).dim : ℝ) * 2 := by
  have hbool : ∀ k : ZMod N,
      (∑ t : Bool,
        (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0))
      = if (e k).1 = V ∧ transportRowOf family s e k = row.val then (2 : ℝ) else 0 := by
    intro k
    rw [Fintype.sum_bool]
    by_cases hk : (e k).1 = V ∧ transportRowOf family s e k = row.val
    · rw [if_pos hk, if_pos hk]
      norm_num
    · rw [if_neg hk, if_neg hk]
      norm_num
  have hred : (∑ k : ZMod N, ∑ t : Bool,
        (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0))
      = ∑ k : ZMod N, if (e k).1 = V ∧ transportRowOf family s e k = row.val then (2 : ℝ) else 0 :=
    Finset.sum_congr rfl fun k _ => hbool k
  rw [hred]
  have hcomp : (∑ k : ZMod N,
        if (e k).1 = V ∧ transportRowOf family s e k = row.val then (2 : ℝ) else 0)
      = ∑ x : Σ V' : Label, Fin ((family.irrep V').dim * dimFixed (family.irrep V') s),
        if x.1 = V ∧ ((finProdFinEquiv (m := (family.irrep x.1).dim)
          (n := dimFixed (family.irrep x.1) s)).symm x.2).2.val = row.val then (2 : ℝ) else 0 :=
    e.sum_comp fun x : Σ V' : Label, Fin ((family.irrep V').dim * dimFixed (family.irrep V') s) =>
      if x.1 = V ∧ ((finProdFinEquiv (m := (family.irrep x.1).dim)
        (n := dimFixed (family.irrep x.1) s)).symm x.2).2.val = row.val then (2 : ℝ) else 0
  rw [hcomp, Fintype.sum_sigma]
  have hinner : ∀ V' : Label,
      (∑ i : Fin ((family.irrep V').dim * dimFixed (family.irrep V') s),
        if V' = V ∧ ((finProdFinEquiv (m := (family.irrep V').dim)
          (n := dimFixed (family.irrep V') s)).symm i).2.val = row.val then (2 : ℝ) else 0)
      = if V' = V then ((family.irrep V').dim : ℝ) * 2 else 0 := by
    intro V'
    by_cases hV' : V' = V
    · rw [hV', if_pos rfl]
      have hpt : ∀ i : Fin ((family.irrep V).dim * dimFixed (family.irrep V) s),
          (if V = V ∧ ((finProdFinEquiv (m := (family.irrep V).dim)
            (n := dimFixed (family.irrep V) s)).symm i).2.val = row.val then (2 : ℝ) else 0)
          = if ((finProdFinEquiv (m := (family.irrep V).dim)
            (n := dimFixed (family.irrep V) s)).symm i).2.val = row.val then (2 : ℝ) else 0 := by
        intro i
        by_cases hi : ((finProdFinEquiv (m := (family.irrep V).dim)
            (n := dimFixed (family.irrep V) s)).symm i).2.val = row.val
        · rw [if_pos ⟨rfl, hi⟩, if_pos hi]
        · rw [if_neg (fun h => hi h.2), if_neg hi]
      rw [Finset.sum_congr rfl fun i _ => hpt i]
      have hswap : (∑ i : Fin ((family.irrep V).dim * dimFixed (family.irrep V) s),
          if ((finProdFinEquiv (m := (family.irrep V).dim)
            (n := dimFixed (family.irrep V) s)).symm i).2.val = row.val then (2 : ℝ) else 0)
          = ∑ x : Fin (family.irrep V).dim × Fin (dimFixed (family.irrep V) s),
            if x.2.val = row.val then (2 : ℝ) else 0 :=
        Fintype.sum_equiv
          (finProdFinEquiv (m := (family.irrep V).dim) (n := dimFixed (family.irrep V) s)).symm
          (fun i => if ((finProdFinEquiv (m := (family.irrep V).dim)
            (n := dimFixed (family.irrep V) s)).symm i).2.val = row.val then (2 : ℝ) else 0)
          (fun x => if x.2.val = row.val then (2 : ℝ) else 0)
          (fun _ => rfl)
      rw [hswap, ← Finset.univ_product_univ, Finset.sum_product]
      have hpt2 : ∀ ρ : Fin (dimFixed (family.irrep V) s),
          (if ρ.val = row.val then (2 : ℝ) else 0) = if ρ = row then (2 : ℝ) else 0 := by
        intro ρ
        by_cases h : ρ = row
        · rw [if_pos h, if_pos (by rw [h])]
        · rw [if_neg h, if_neg fun heq => h (Fin.ext heq)]
      have hrow : (∑ ρ : Fin (dimFixed (family.irrep V) s),
          if ρ.val = row.val then (2 : ℝ) else 0) = 2 := by
        rw [Finset.sum_congr rfl fun ρ _ => hpt2 ρ, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ _)]
      show (∑ x : Fin (family.irrep V).dim, ∑ ρ : Fin (dimFixed (family.irrep V) s),
          if ρ.val = row.val then (2 : ℝ) else 0) = ((family.irrep V).dim : ℝ) * 2
      rw [hrow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    · have hz : ∀ i : Fin ((family.irrep V').dim * dimFixed (family.irrep V') s),
          (if V' = V ∧ ((finProdFinEquiv (m := (family.irrep V').dim)
            (n := dimFixed (family.irrep V') s)).symm i).2.val = row.val then (2 : ℝ) else 0)
            = 0 := by
        intro i
        apply if_neg
        intro h
        exact hV' h.1
      rw [Finset.sum_congr rfl fun i _ => hz i, if_neg hV']
      exact Finset.sum_const_zero
  simp only [hinner]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ V)]

theorem clause27_transport_label_count {N : ℕ} [NeZero N] {Label : Type} [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N)
    (e : ZMod N ≃ Σ V : Label, Fin ((family.irrep V).dim * dimFixed (family.irrep V) s))
    (V : Label) :
    ∑ k : ZMod N, ∑ _t : Bool, (if (e k).1 = V then (1 : ℝ) else 0)
      = ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s * 2 := by
  have hbool : ∀ k : ZMod N,
      (∑ t : Bool, (if (e k).1 = V then (1 : ℝ) else 0))
      = if (e k).1 = V then (2 : ℝ) else 0 := by
    intro k
    rw [Fintype.sum_bool]
    by_cases hk : (e k).1 = V
    · rw [if_pos hk, if_pos hk]
      norm_num
    · rw [if_neg hk, if_neg hk]
      norm_num
  have hred : (∑ k : ZMod N, ∑ t : Bool, (if (e k).1 = V then (1 : ℝ) else 0))
      = ∑ k : ZMod N, if (e k).1 = V then (2 : ℝ) else 0 :=
    Finset.sum_congr rfl fun k _ => hbool k
  rw [hred]
  have hcomp : (∑ k : ZMod N, if (e k).1 = V then (2 : ℝ) else 0)
      = ∑ x : Σ V' : Label, Fin ((family.irrep V').dim * dimFixed (family.irrep V') s),
        if x.1 = V then (2 : ℝ) else 0 :=
    e.sum_comp fun x : Σ V' : Label, Fin ((family.irrep V').dim * dimFixed (family.irrep V') s) =>
      if x.1 = V then (2 : ℝ) else 0
  rw [hcomp, Fintype.sum_sigma]
  have hinner : ∀ V' : Label,
      (∑ _i : Fin ((family.irrep V').dim * dimFixed (family.irrep V') s),
        if V' = V then (2 : ℝ) else 0)
      = if V' = V then ((family.irrep V').dim : ℝ) * dimFixed (family.irrep V') s * 2
        else 0 := by
    intro V'
    by_cases hV' : V' = V
    · rw [if_pos hV', if_pos hV']
      show (∑ _i : Fin ((family.irrep V').dim * dimFixed (family.irrep V') s), (2 : ℝ)) = _
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_mul]
    · rw [if_neg hV', if_neg hV']
      exact Finset.sum_const_zero
  simp only [hinner]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ V)]

theorem clause1_of_dimFixedCount
    (hdim : ∀ (N : ℕ) [NeZero N] (Label : Type) [Fintype Label] [DecidableEq Label]
      (family : IrrepFamily N Label) (s : ZMod N),
      ∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s = N) :
    ∀ (N : ℕ) [NeZero N] (S : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : AddCommGroup S)
      (f : DihedralReg N → S) (s : ZMod N) (_hf : DihedralReflectionHides N f s)
      (Label : Type) (_ : Fintype Label) (_ : DecidableEq Label)
      (family : IrrepFamily N Label),
      ∃ (toLabel : ZMod N → Label) (toRowNat : ZMod N × Bool → ℕ)
        (stages : StagedPmfBridge (recordStages N S) 2),
        (∀ k : ZMod N, ∀ t : Bool,
            toRowNat (k, t) < dimFixed (family.irrep (toLabel k)) s)
        ∧ (∀ V : Label, ∀ row : Fin (dimFixed (family.irrep V) s),
            repJointMass (family.irrep V) row.val =
              ∑' q : ZMod N × Bool × S,
                if toLabel q.1 = V ∧ toRowNat (q.1, q.2.1) = row.val then
                  ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
        ∧ (∀ V : Label,
            repLabelMass (family.irrep V) s =
              ∑' q : ZMod N × Bool × S,
                if toLabel q.1 = V then
                  ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
        ∧ (stages.law 0 = actualRecordFiniteLaw f)
        ∧ (∀ k : ZMod N, ∀ t : Bool,
            ENNReal.toReal (stages.law 1 (k, t)) = 1 / (2 * N))
        ∧ (∀ k : ZMod N, ENNReal.toReal (stages.law 2 k) = 1 / N)
        ∧ (∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
            ∀ t : Bool, ∀ z : S,
              dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t)
        ∧ (∀ k ℓ : ZMod N,
            ∃ xiPlus xiMinus : QState Bool, ∃ uPlus uMinus : ℂ,
              ‖uPlus‖ = 1 ∧ ‖uMinus‖ = 1 ∧
              xiPlus = uPlus • dihedralQubitState N s (k + ℓ) ∧
              xiMinus = uMinus • dihedralQubitState N s (k - ℓ) ∧
              ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
                dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
                  (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ)
                  (b, ⟨ξ, hξ⟩) =
                  if (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) then
                    (1 / 2 : NNReal) else 0)
        ∧ (QueryCount (dihedralRecordCircuit (N := N) (S := S)) = 1)
        ∧ (GateCount (dihedralRecordCircuit (N := N) (S := S)) = 1) := by
  intro N _instN S _hS _hdS _hAS f s hf Label _hL _hdL family
  set w : Label → ℕ := fun V => (family.irrep V).dim * dimFixed (family.irrep V) s with _hw
  have hsum : ∑ V : Label, w V = N := hdim N Label family s
  have hcard : Fintype.card (ZMod N) = Fintype.card (Σ V : Label, Fin (w V)) := by
    rw [ZMod.card, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum.symm
  let e : ZMod N ≃ Σ V : Label, Fin (w V) := Fintype.equivOfCardEq hcard
  obtain ⟨stages, hst0, hst1, hst2⟩ := clause27_exists_stages S f s hf
  refine ⟨fun k => (e k).1, fun p => transportRowOf family s e p.1, stages,
    ?_, ?_, ?_, hst0, hst1, hst2, ?_, ?_, ?_, ?_⟩
  · intro k t
    exact ((finProdFinEquiv (m := (family.irrep ((e k).1)).dim)
      (n := dimFixed (family.irrep ((e k).1)) s)).symm (e k).2).2.isLt
  · intro V row
    have hmass : repJointMass (family.irrep V) row.val = ((family.irrep V).dim : ℝ) / N := rfl
    rw [hmass, tsum_fintype, clause27_sum_triple]
    show ((family.irrep V).dim : ℝ) / N =
      (∑ k : ZMod N, ∑ t : Bool, ∑ z : S,
        if (e k).1 = V ∧ transportRowOf family s e k = row.val then
          ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
    have hz : ∀ k : ZMod N, ∀ t : Bool,
        (∑ z : S, if (e k).1 = V ∧ transportRowOf family s e k = row.val then
          ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
        = if (e k).1 = V ∧ transportRowOf family s e k = row.val then
          (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z))) else 0 := by
      intro k t
      by_cases h : (e k).1 = V ∧ transportRowOf family s e k = row.val
      · rw [if_pos h]
        exact Finset.sum_congr rfl fun z _ => if_pos h
      · rw [if_neg h]
        have hz' : ∀ z : S, (if (e k).1 = V ∧ transportRowOf family s e k = row.val then
            ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0) = 0 := fun z => if_neg h
        rw [Finset.sum_congr rfl fun z _ => hz' z]
        exact Finset.sum_const_zero
    have hstep1 : (∑ k : ZMod N, ∑ t : Bool, ∑ z : S,
          if (e k).1 = V ∧ transportRowOf family s e k = row.val then
            ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
        = ∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V ∧ transportRowOf family s e k = row.val then
            (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z))) else 0 :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => hz k t
    rw [hstep1]
    have hstep2 : (∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V ∧ transportRowOf family s e k = row.val then
            (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z))) else 0)
        = ∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V ∧ transportRowOf family s e k = row.val then
            (1 / (2 * (N : ℝ))) else 0 := by
      simp only [clause27_toReal_bitMarginal S f s hf]
    rw [hstep2]
    have hscale : ∀ k : ZMod N, ∀ t : Bool,
        (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 / (2 * (N : ℝ))) else 0)
        = (1 / (2 * (N : ℝ))) *
            (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0) := by
      intro k t
      by_cases h : (e k).1 = V ∧ transportRowOf family s e k = row.val
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    have hstep3 : (∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 / (2 * (N : ℝ))) else 0)
        = (1 / (2 * (N : ℝ))) * (∑ k : ZMod N, ∑ t : Bool,
            (if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0)) :=
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => hscale k t).trans <|
        (Finset.sum_congr rfl fun k _ =>
          (Finset.mul_sum (s := Finset.univ) (a := 1 / (2 * (N : ℝ)))
            (f := fun t : Bool =>
              if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0)).symm).trans <|
          (Finset.mul_sum (s := Finset.univ) (a := 1 / (2 * (N : ℝ)))
            (f := fun k : ZMod N => ∑ t : Bool,
              if (e k).1 = V ∧ transportRowOf family s e k = row.val then (1 : ℝ) else 0)).symm
    rw [hstep3, clause27_transport_row_count family s e V row]
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
    field_simp [hN]; try ring
  · intro V
    have hmass : repLabelMass (family.irrep V) s
        = ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s * 2 / (2 * N) := rfl
    rw [hmass, tsum_fintype, clause27_sum_triple]
    show ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s * 2 / (2 * N) =
      (∑ k : ZMod N, ∑ t : Bool, ∑ z : S,
        if (e k).1 = V then ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
    have hz : ∀ k : ZMod N, ∀ t : Bool,
        (∑ z : S, if (e k).1 = V then ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
        = if (e k).1 = V then
          (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z))) else 0 := by
      intro k t
      by_cases h : (e k).1 = V
      · rw [if_pos h]
        exact Finset.sum_congr rfl fun z _ => if_pos h
      · rw [if_neg h]
        have hz' : ∀ z : S, (if (e k).1 = V then
            ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0) = 0 := fun z => if_neg h
        rw [Finset.sum_congr rfl fun z _ => hz' z]
        exact Finset.sum_const_zero
    have hstep1 : (∑ k : ZMod N, ∑ t : Bool, ∑ z : S,
          if (e k).1 = V then ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)) else 0)
        = ∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V then (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)))
            else 0 :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => hz k t
    rw [hstep1]
    have hstep2 : (∑ k : ZMod N, ∑ t : Bool,
          if (e k).1 = V then (∑ z : S, ENNReal.toReal (actualRecordFiniteLaw f (k, t, z)))
            else 0)
        = ∑ k : ZMod N, ∑ t : Bool, if (e k).1 = V then (1 / (2 * (N : ℝ))) else 0 := by
      simp only [clause27_toReal_bitMarginal S f s hf]
    rw [hstep2]
    have hscale : ∀ k : ZMod N, ∀ t : Bool,
        (if (e k).1 = V then (1 / (2 * (N : ℝ))) else 0)
        = (1 / (2 * (N : ℝ))) * (if (e k).1 = V then (1 : ℝ) else 0) := by
      intro k t
      by_cases h : (e k).1 = V
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    have hstep3 : (∑ k : ZMod N, ∑ t : Bool, if (e k).1 = V then (1 / (2 * (N : ℝ))) else 0)
        = (1 / (2 * (N : ℝ))) * (∑ k : ZMod N, ∑ t : Bool,
            (if (e k).1 = V then (1 : ℝ) else 0)) :=
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => hscale k t).trans <|
        (Finset.sum_congr rfl fun k _ =>
          (Finset.mul_sum (s := Finset.univ) (a := 1 / (2 * (N : ℝ)))
            (f := fun t : Bool => if (e k).1 = V then (1 : ℝ) else 0)).symm).trans <|
          (Finset.mul_sum (s := Finset.univ) (a := 1 / (2 * (N : ℝ)))
            (f := fun k : ZMod N => ∑ t : Bool, if (e k).1 = V then (1 : ℝ) else 0)).symm
    rw [hstep3, clause27_transport_label_count family s e V]
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
    field_simp [hN]; try ring
  · exact clause27_recordFactor N S f s hf
  · intro k ℓ
    exact clause27_extraction_conjunct N s k ℓ
  · exact (clause27_costs N S).1
  · exact (clause27_costs N S).2

open Matrix

open scoped ComplexConjugate

theorem g1 :
∀ (N : ℕ) [NeZero N] (S : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : AddCommGroup S)
      (f : DihedralReg N → S) (s : ZMod N) (_hf : DihedralReflectionHides N f s)
      (Label : Type) (_ : Fintype Label) (_ : DecidableEq Label)
      (family : IrrepFamily N Label),
      ∃ (toLabel : ZMod N → Label) (toRowNat : ZMod N × Bool → ℕ)
        (stages : StagedPmfBridge (recordStages N S) 2),
        (∀ k : ZMod N, ∀ t : Bool,
            toRowNat (k, t) < dimFixed (family.irrep (toLabel k)) s)
        ∧ (∀ V : Label, ∀ row : Fin (dimFixed (family.irrep V) s),
            repJointMass (family.irrep V) row.val =
              ∑' q : ZMod N × Bool × S,
                if toLabel q.1 = V ∧ toRowNat (q.1, q.2.1) = row.val then
                  ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
        ∧ (∀ V : Label,
            repLabelMass (family.irrep V) s =
              ∑' q : ZMod N × Bool × S,
                if toLabel q.1 = V then
                  ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
        ∧ (stages.law 0 = actualRecordFiniteLaw f)
        ∧ (∀ k : ZMod N, ∀ t : Bool,
            ENNReal.toReal (stages.law 1 (k, t)) = 1 / (2 * N))
        ∧ (∀ k : ZMod N, ENNReal.toReal (stages.law 2 k) = 1 / N)
        ∧ (∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
            ∀ t : Bool, ∀ z : S,
              dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t)
        ∧ (∀ k ℓ : ZMod N,
            ∃ xiPlus xiMinus : QState Bool, ∃ uPlus uMinus : ℂ,
              ‖uPlus‖ = 1 ∧ ‖uMinus‖ = 1 ∧
              xiPlus = uPlus • dihedralQubitState N s (k + ℓ) ∧
              xiMinus = uMinus • dihedralQubitState N s (k - ℓ) ∧
              ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
                dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
                  (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ)
                  (b, ⟨ξ, hξ⟩) =
                  if (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) then
                    (1 / 2 : NNReal) else 0)
        ∧ (QueryCount (dihedralRecordCircuit (N := N) (S := S)) = 1)
        ∧ (GateCount (dihedralRecordCircuit (N := N) (S := S)) = 1)
    := clause1_of_dimFixedCount dimFixedCount_identity

end Qatlib.Concepts.HspRecovery.RecordExtract
