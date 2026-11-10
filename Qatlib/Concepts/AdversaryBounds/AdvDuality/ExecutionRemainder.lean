/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainderDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedFeedbackConsumer
import Mathlib.Tactic.FinCases
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainderFairFeedback
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainderHybrid
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped ENNReal
namespace CoinCode
variable {α : Type}

theorem paths_normalized (p : CoinCode α) : (p.paths.map (fun z => wordWeight z.2)).sum = 1 := by
  induction p with
  | ret a => simp [paths, wordWeight]
  | bit p q hp hq =>
      simp only [paths, List.map_append, List.map_map, Function.comp_def, wordWeight_cons,
        List.sum_append, List.sum_map_mul_left, hp, hq]
      norm_num

theorem paths_run (p : CoinCode α) (z : α × List Bool) (hz : z ∈ p.paths) :
    p.run z.2 = (.ret z.1, z.2.length) := by
  induction p generalizing z with
  | ret a =>
      simp only [paths, List.mem_singleton] at hz
      subst z
      rfl
  | bit p q hp hq =>
      simp only [paths, List.mem_append, List.mem_map] at hz
      rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · simp [run, hp y hy, Nat.add_comm]
      · simp [run, hq y hy, Nat.add_comm]

theorem paths_expectation (p : CoinCode α) (F : α × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law F =
      (p.paths.map (fun z => (1 / 2 : ℝ≥0∞) ^ z.2.length * F (z.1, z.2.length))).sum := by
  induction p generalizing F with
  | ret a => simp [law, paths, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret]
  | bit p q hp hq =>
      rw [law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      change (∑' b : Bool, PMF.uniformOfFintype' Bool b *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (if b then q.law else p.law) (fun x => F (x.1, 1 + x.2))) = _
      rw [tsum_fintype, Fintype.sum_bool]
      simp only [Bool.false_eq_true, ↓reduceIte, PMF.uniformOfFintype'_apply, Fintype.card_bool]
      rw [hp, hq]
      simp only [paths, List.map_append, List.map_map, Function.comp_def, List.length_cons,
        pow_succ', List.sum_append, mul_assoc, List.sum_map_mul_left, one_div, Nat.add_comm 1, Nat.cast_ofNat]
      exact add_comm _ _

theorem paths_weight_sum (p : CoinCode α) :
    (∑ c : Fin p.paths.length, wordWeight (p.paths.get c).2) = 1 := by
  have he := congrArg (fun L : List (α × List Bool) =>
    (L.map (fun z => wordWeight z.2)).sum) (List.ofFn_get p.paths)
  (try dsimp only at he)
  rw [List.map_ofFn, List.sum_ofFn] at he
  dsimp only [Function.comp_def] at he
  rw [he]
  exact paths_normalized p

theorem wordWeight_nonneg (w : List Bool) : 0 ≤ wordWeight w := by
  unfold wordWeight
  positivity
variable {β : Type}

theorem paths_words_nodup (p : CoinCode α) : (p.paths.map Prod.snd).Nodup := by
  induction p with
  | ret a => simp [paths]
  | bit p q hp hq =>
    simp only [paths,List.map_append,List.map_map,Function.comp_def]
    suffices ((p.paths.map Prod.snd).map (List.cons false) ++
        (q.paths.map Prod.snd).map (List.cons true)).Nodup by
      simpa only [List.map_map,Function.comp_def] using this
    refine List.nodup_append.mpr ⟨hp.map List.cons_injective,hq.map List.cons_injective,?_⟩
    intro a ha b hb he
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
    simp at he

theorem paths_word_get_injective (p : CoinCode α) :
    Function.Injective (fun i : Fin p.paths.length => (p.paths.get i).2) := by
  intro i j h
  have hi : i.val < (p.paths.map Prod.snd).length := by simp
  have hj : j.val < (p.paths.map Prod.snd).length := by simp
  have he : (p.paths.map Prod.snd).get ⟨i.val,hi⟩ = (p.paths.map Prod.snd).get ⟨j.val,hj⟩ := by
    simpa using h
  have hv := (paths_words_nodup p).get_inj_iff.mp he
  exact Fin.ext (congrArg (fun k : Fin (p.paths.map Prod.snd).length => k.val) hv)

theorem paths_bind (p : CoinCode α) (f : α → CoinCode β) :
    (p.bind f).paths = p.paths.flatMap (fun x => (f x.1).paths.map (fun y => (y.1,x.2++y.2))) := by
  induction p with
  | ret a => simp [bind,paths]
  | bit p q hp hq =>
    simp [bind,paths,hp,hq,List.flatMap_append,List.map_flatMap,List.flatMap_map,
      List.map_map,Function.comp_def]

theorem mem_paths_bind (p : CoinCode α) (f : α → CoinCode β) (y : β) (w : List Bool) :
    (y,w) ∈ (p.bind f).paths ↔ ∃ a u v, (a,u) ∈ p.paths ∧ (y,v) ∈ (f a).paths ∧ w = u++v := by
  rw [paths_bind]
  constructor
  · intro h
    obtain ⟨⟨a,u⟩,hu,h⟩ := List.mem_flatMap.mp h
    obtain ⟨⟨z,v⟩,hv,he⟩ := List.mem_map.mp h
    have hz : z = y := congrArg Prod.fst he
    subst z
    have hw : u++v = w := congrArg Prod.snd he
    exact ⟨a,u,v,hu,hv,hw.symm⟩
  · rintro ⟨a,u,v,hu,hv,rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨(a,u),hu,List.mem_map.mpr ⟨(y,v),hv,rfl⟩⟩

theorem paths_bind_ret (p : CoinCode α) (f : α → β) :
    (p.bind (fun a => .ret (f a))).paths = p.paths.map (fun z => (f z.1,z.2)) := by
  induction p with
  | ret a => rfl
  | bit p q hp hq => simp [bind,paths,hp,hq,List.map_map,Function.comp_def]

theorem ofFn_regSucc_symm (b : ℕ) (ω : Reg b) (x : Bool) :
    List.ofFn ((regSuccEquiv b).symm (ω,x)) = List.ofFn ω ++ [x] := by
  change List.ofFn (Fin.append ω (fun _ : Fin 1 => x)) = _
  rw [List.ofFn_fin_append]
  simp

theorem block_path_word (b : ℕ) (ω : Reg b) (w : List Bool) (h : (ω,w) ∈ (block b).paths) :
    w = List.ofFn ω := by
  induction b generalizing w with
  | zero =>
    simp only [block,paths,List.mem_singleton,Prod.mk.injEq] at h
    rw [h.2]
    simp
  | succ b ih =>
    rw [block] at h
    obtain ⟨ω',u,v,hu,hv,hw⟩ := (mem_paths_bind _ _ _ _).mp h
    have huw := ih ω' u hu
    simp only [paths,List.map_singleton,List.singleton_append,List.mem_cons,List.not_mem_nil,or_false,
      Prod.mk.injEq] at hv
    rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simpa only [huw,ofFn_regSucc_symm] using hw

theorem paths_probability_sum (p : CoinCode α) :
    (∑ i : Fin p.paths.length, (1/2 : ℝ≥0∞) ^ (p.paths.get i).2.length) = 1 := by
  have hl : (p.paths.map (fun z => (1/2 : ℝ≥0∞)^z.2.length)).sum = 1 := by
    simpa using (paths_expectation p (fun _ => 1)).symm
  have he := congrArg (fun L : List (α × List Bool) =>
    (L.map (fun z => (1/2 : ℝ≥0∞)^z.2.length)).sum) (List.ofFn_get p.paths)
  (try dsimp only at he)
  rw [List.map_ofFn,List.sum_ofFn] at he
  exact he.trans hl

noncomputable def pathLaw (p : CoinCode α) : PMF (Fin p.paths.length) :=
  PMF.ofFintype (fun i => (1/2 : ℝ≥0∞)^(p.paths.get i).2.length) (paths_probability_sum p)

theorem pathLaw_apply (p : CoinCode α) (i : Fin p.paths.length) :
    p.pathLaw i = (1/2 : ℝ≥0∞)^(p.paths.get i).2.length := rfl

theorem pathLaw_map (p : CoinCode α) :
    p.pathLaw.map (fun i => ((p.paths.get i).1,(p.paths.get i).2.length)) = p.law := by
  classical
  ext z
  rw [PMF.map_apply,tsum_fintype]
  simp only [pathLaw_apply]
  have h := paths_expectation p (fun y => if z = y then 1 else 0)
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,mul_ite,mul_one,mul_zero] at h
  have hz : (∑' a : α × ℕ, if z = a then p.law a else 0) = p.law z := by
    rw [tsum_eq_single z (fun a ha => if_neg (Ne.symm ha))]
    simp
  rw [hz] at h
  rw [← List.ofFn_get p.paths,List.map_ofFn,List.sum_ofFn] at h
  simpa only [Function.comp_def,mul_ite,mul_one,mul_zero] using h.symm

end CoinCode
namespace FairFeedback
variable {D : ℕ} {A : Type}

theorem kraus_adjoint_mul (M : FairFeedback D A) (O : Operator D) (z : M.Outcome) :
    (M.kraus O z).conjTranspose * M.kraus O z =
      ((CoinCode.wordWeight (M.codeWord z) : ℝ) : ℂ) •
        ((M.prefixLeaf O z.1).operator.conjTranspose *
          ((M.suffixLeaf O z).operator.conjTranspose * (M.suffixLeaf O z).operator) *
            (M.prefixLeaf O z.1).operator) := by
  have hs : ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) * star ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) =
      ((CoinCode.wordWeight (M.codeWord z) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (CoinCode.wordWeight_nonneg _)]
  simp only [kraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hs]
  simp only [Matrix.mul_assoc]

theorem kraus_sum_suffix (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal)
    (i : Fin (observedLeafCount M.first)) (c : Fin (M.choose i).paths.length) :
    (∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
      (M.kraus O ⟨i,c,j⟩).conjTranspose * M.kraus O ⟨i,c,j⟩) =
      ((CoinCode.wordWeight (M.path i c).2 : ℝ) : ℂ) •
        ((M.prefixLeaf O i).operator.conjTranspose * (M.prefixLeaf O i).operator) := by
  simp only [kraus_adjoint_mul, codeWord, suffixLeaf]
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    observedLeaf_complete O hO _ (hM.2 i (M.path i c).1)]
  simp

theorem kraus_complete (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) :
    ∑ z : M.Outcome, (M.kraus O z).conjTranspose * M.kraus O z = 1 := by
  simp only [Outcome, Fintype.sum_sigma, kraus_sum_suffix M O hO hM]
  have hi (i : Fin (observedLeafCount M.first)) :
      (∑ c : Fin (M.choose i).paths.length,
        ((CoinCode.wordWeight (M.path i c).2 : ℝ) : ℂ) •
          ((M.prefixLeaf O i).operator.conjTranspose * (M.prefixLeaf O i).operator)) =
        (M.prefixLeaf O i).operator.conjTranspose * (M.prefixLeaf O i).operator := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]
    change ((∑ c : Fin (M.choose i).paths.length,
      CoinCode.wordWeight ((M.choose i).paths.get c).2 : ℝ) : ℂ) • _ = _
    rw [CoinCode.paths_weight_sum]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  exact observedLeaf_complete O hO M.first hM.1

noncomputable def instrument (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) : Instrument M.Outcome D D :=
  Instrument.ofKraus (M.kraus O) (M.kraus_complete O hO hM)
end FairFeedback

namespace CoinCode
variable {α : Type}

theorem paths_native (p : CoinCode α) (z : α × List Bool) (hz : z ∈ p.paths)
    (f : α → Bool) (T : Turing.Tape (Option Bool)) :
    coinTapeRunAux p.nativeTable (p.nativeAccept f) z.2 ⟨p.root, T⟩ =
      (some (f z.1), z.2.length) := by
  rw [native_run_root, paths_run p z hz]
  rfl

theorem paths_native_transitions (p : CoinCode α) (z : α × List Bool) (hz : z ∈ p.paths)
    (T : Turing.Tape (Option Bool)) :
    coinTapeTransitionCountAux p.nativeTable z.2 ⟨p.root, T⟩ = z.2.length := by
  rw [native_transition_count, atPosition_root, paths_run p z hz]

theorem paths_prefix_free (p : CoinCode α) (x y : α × List Bool)
    (hx : x ∈ p.paths) (hy : y ∈ p.paths) (hpre : x.2.IsPrefix y.2) : x = y := by
  obtain ⟨w, hw⟩ := hpre
  have hyRun := paths_run p y hy
  rw [← hw, run_append, paths_run p x hx] at hyRun
  dsimp only at hyRun
  rw [run_ret] at hyRun
  have hlen := congrArg (fun z => z.2) hyRun
  dsimp only at hlen
  simp only [Nat.add_zero, List.length_append] at hlen
  have hwlen : w.length = 0 := by
    have hly := congrArg List.length hw
    rw [List.length_append] at hly
    omega
  have hw0 : w = [] := List.eq_nil_of_length_eq_zero hwlen
  have hxy : x.2 = y.2 := by simpa only [hw0, List.append_nil] using hw
  have ha := congrArg (fun z => z.1) hyRun
  exact Prod.ext (CoinCode.ret.inj ha) hxy
end CoinCode
namespace FairFeedback
variable {D : ℕ} {A : Type}

theorem branch_law (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal)
    (z : M.Outcome) (ρ : Operator D) :
    (M.instrument O hO hM).branch z ρ =
      ((CoinCode.wordWeight (M.codeWord z) : ℝ) : ℂ) •
        conjBranch (M.suffixLeaf O z).operator (conjBranch (M.prefixLeaf O z.1).operator ρ) := by
  have hs : star ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) *
      ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) =
      ((CoinCode.wordWeight (M.codeWord z) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (CoinCode.wordWeight_nonneg _)]
  rw [instrument, Instrument.ofKraus_branch]
  simp only [kraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjBranch_apply]
  rw [hs]
  simp only [Matrix.mul_assoc]

theorem probability_law (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal)
    (z : M.Outcome) (ρ : Operator D) :
    instrumentProb (M.instrument O hO hM) ρ z =
      CoinCode.wordWeight (M.codeWord z) *
        instrumentProb (observedInstrument O hO (M.next z.1 (M.path z.1 z.2.1).1)
          (hM.2 z.1 (M.path z.1 z.2.1).1))
          (conjBranch (M.prefixLeaf O z.1).operator ρ) z.2.2 := by
  rw [instrumentProb, branch_law, Matrix.trace_smul]
  rw [instrumentProb, observedInstrument, Instrument.ofKraus_branch]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, suffixLeaf, conjBranch_apply]
end FairFeedback

namespace FairFeedback
variable {D : ℕ} {A : Type}

theorem sum_suffix_probability (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (i : Fin (observedLeafCount M.first)) (c : Fin (M.choose i).paths.length) :
    (∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
      instrumentProb (M.instrument O hO hM) ρ ⟨i,c,j⟩) =
      CoinCode.wordWeight (M.path i c).2 *
        instrumentProb (observedInstrument O hO M.first hM.1) ρ i := by
  let σ := conjBranch (M.prefixLeaf O i).operator ρ
  let J := observedInstrument O hO (M.next i (M.path i c).1) (hM.2 i (M.path i c).1)
  have hsum : (∑ j, instrumentProb J σ j) = (Matrix.trace σ).re := sum_instrumentProb J σ
  have hp : instrumentProb (observedInstrument O hO M.first hM.1) ρ i =
      (Matrix.trace σ).re := by
    rw [instrumentProb, observedInstrument, Instrument.ofKraus_branch]
    rfl
  calc
    _ = CoinCode.wordWeight (M.path i c).2 * ∑ j, instrumentProb J σ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => probability_law M O hO hM ⟨i,c,j⟩ ρ)
    _ = _ := by rw [hsum, hp]

theorem prefix_probability (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (i : Fin (observedLeafCount M.first)) :
    (∑ c : Fin (M.choose i).paths.length,
      ∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
        instrumentProb (M.instrument O hO hM) ρ ⟨i,c,j⟩) =
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i := by
  calc
    _ = ∑ c : Fin (M.choose i).paths.length,
        CoinCode.wordWeight (M.path i c).2 *
          instrumentProb (observedInstrument O hO M.first hM.1) ρ i :=
      Finset.sum_congr rfl (fun c _ => sum_suffix_probability M O hO hM ρ i c)
    _ = _ := by
      have h := CoinCode.paths_weight_sum (M.choose i)
      change (∑ c : Fin (M.choose i).paths.length, CoinCode.wordWeight (M.path i c).2) = 1 at h
      rw [← Finset.sum_mul, h, one_mul]

theorem expected_coin_reads (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) :
    (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
      ((M.record O z).coinWord.length : ℝ)) =
      ∑ i : Fin (observedLeafCount M.first),
        instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
          ∑ c : Fin (M.choose i).paths.length,
            CoinCode.wordWeight (M.path i c).2 * ((M.path i c).2.length : ℝ) := by
  change (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
    ((M.codeWord z).length : ℝ)) = _
  simp only [Fintype.sum_sigma, codeWord]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ c : Fin (M.choose i).paths.length,
        (∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
          instrumentProb (M.instrument O hO hM) ρ ⟨i,c,j⟩) * ((M.path i c).2.length : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Finset.sum_mul _ _ _).symm
    _ = _ := by
      have he : ∀ c : Fin (M.choose i).paths.length,
          (∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
            instrumentProb (M.instrument O hO hM) ρ ⟨i,c,j⟩) =
          CoinCode.wordWeight (M.path i c).2 *
            instrumentProb (observedInstrument O hO M.first hM.1) ρ i :=
        fun c => sum_suffix_probability M O hO hM ρ i c
      simp_rw [he]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

end FairFeedback

theorem measuredFeedbackFlip_unitary : measuredFeedbackFlip ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Qatlib.Concepts.GateVocabulary.GateVocab.toFinGate_unitary pauliX_unitary

theorem measuredFeedback_legal : measuredFeedback.Legal := by
  constructor
  · intro o
    trivial
  · intro i a
    change observedWellFormed (measuredFeedbackNext i a)
    unfold measuredFeedbackNext
    split_ifs
    · exact ⟨measuredFeedbackFlip_unitary, trivial⟩
    · exact ⟨Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin_unitary, trivial⟩
    · trivial
    · trivial

theorem measuredFeedbackInput_density : IsDensityOperator measuredFeedbackInput ∧
    ¬ IsPureDensityOperator measuredFeedbackInput := by
  simpa only [measuredFeedbackInput, mixedFeedbackInput] using
    (show IsDensityOperator mixedFeedbackInput ∧ ¬ IsPureDensityOperator mixedFeedbackInput from
      ⟨mixed_feedback_consumer_data.1, mixed_feedback_consumer_data.2.1⟩)

theorem measuredFeedback_coin_paths :
    (measuredFeedbackCoins 0).paths = [((some 0, 1), [])] ∧
    (measuredFeedbackCoins 1).paths = [((some 0, 1), [false]), ((some 1, 2), [true])] := by
  decide

theorem measuredFeedback_outcomes : Fintype.card measuredFeedback.Outcome = 3 := by
  decide +kernel

theorem measuredFeedback_record_zero (O : Operator 2) :
    measuredFeedback.record O measuredFeedbackZero =
      ⟨(some 0, 1), false, true, [], 0, 1, 1, [(2, 0)], []⟩ := by
  rfl

theorem measuredFeedback_record_hadamard (O : Operator 2) :
    measuredFeedback.record O measuredFeedbackHadamard =
      ⟨(some 0, 1), true, true, [false], 0, 1, 1, [(2, 1)], []⟩ := by
  rfl

theorem measuredFeedback_record_query (O : Operator 2) :
    measuredFeedback.record O measuredFeedbackQuery =
      ⟨(some 1, 2), true, false, [true], 1, 0, 1, [(2, 1)], []⟩ := by
  rfl

theorem measuredFeedback_first_operator (O : Operator 2) (i : Fin 2) :
    (observedLeaf O measuredFeedbackFirst i).operator =
      Projector (Finset.univ.filter fun j : Fin 2 => j = i) := by
  fin_cases i <;> change (1 : Operator 2) * Projector _ = Projector _ <;> rw [Matrix.one_mul]

theorem measuredFeedback_first_probability (O : Operator 2)
    (hO : O ∈ Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    instrumentProb (observedInstrument O hO measuredFeedbackFirst measuredFeedback_legal.1)
      measuredFeedbackInput i = 1 / 2 := by
  rw [instrumentProb, observedInstrument, Instrument.ofKraus_branch,
    measuredFeedback_first_operator]
  rw [measuredFeedbackInput, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    projector_conjTranspose, projector_mul_self, Matrix.trace_smul]
  fin_cases i <;> norm_num [Projector, Matrix.trace, Fin.sum_univ_two]

noncomputable def measuredFeedbackInstrument :=
  measuredFeedback.instrument measuredFeedbackFlip measuredFeedbackFlip_unitary measuredFeedback_legal

theorem measuredFeedback_probability_zero :
    instrumentProb measuredFeedbackInstrument measuredFeedbackInput measuredFeedbackZero = 1 / 2 := by
  have h := FairFeedback.sum_suffix_probability measuredFeedback measuredFeedbackFlip
    measuredFeedbackFlip_unitary measuredFeedback_legal measuredFeedbackInput
    measuredFeedbackZero.1 measuredFeedbackZero.2.1
  change (∑ j : Fin 1, instrumentProb measuredFeedbackInstrument measuredFeedbackInput
      ⟨measuredFeedbackZero.1, measuredFeedbackZero.2.1, j⟩) =
    CoinCode.wordWeight [] * instrumentProb (observedInstrument measuredFeedbackFlip
      measuredFeedbackFlip_unitary measuredFeedbackFirst measuredFeedback_legal.1)
      measuredFeedbackInput (0 : Fin 2) at h
  rw [Fin.sum_univ_one, measuredFeedback_first_probability] at h
  norm_num [CoinCode.wordWeight] at h
  exact h

theorem measuredFeedback_probability_hadamard :
    instrumentProb measuredFeedbackInstrument measuredFeedbackInput measuredFeedbackHadamard = 1 / 4 := by
  have h := FairFeedback.sum_suffix_probability measuredFeedback measuredFeedbackFlip
    measuredFeedbackFlip_unitary measuredFeedback_legal measuredFeedbackInput
    measuredFeedbackHadamard.1 measuredFeedbackHadamard.2.1
  change (∑ j : Fin 1, instrumentProb measuredFeedbackInstrument measuredFeedbackInput
      ⟨measuredFeedbackHadamard.1, measuredFeedbackHadamard.2.1, j⟩) =
    CoinCode.wordWeight [false] * instrumentProb (observedInstrument measuredFeedbackFlip
      measuredFeedbackFlip_unitary measuredFeedbackFirst measuredFeedback_legal.1)
      measuredFeedbackInput (1 : Fin 2) at h
  rw [Fin.sum_univ_one, measuredFeedback_first_probability] at h
  norm_num [CoinCode.wordWeight] at h
  exact h

theorem measuredFeedback_probability_query :
    instrumentProb measuredFeedbackInstrument measuredFeedbackInput measuredFeedbackQuery = 1 / 4 := by
  have h := FairFeedback.sum_suffix_probability measuredFeedback measuredFeedbackFlip
    measuredFeedbackFlip_unitary measuredFeedback_legal measuredFeedbackInput
    measuredFeedbackQuery.1 measuredFeedbackQuery.2.1
  change (∑ j : Fin 1, instrumentProb measuredFeedbackInstrument measuredFeedbackInput
      ⟨measuredFeedbackQuery.1, measuredFeedbackQuery.2.1, j⟩) =
    CoinCode.wordWeight [true] * instrumentProb (observedInstrument measuredFeedbackFlip
      measuredFeedbackFlip_unitary measuredFeedbackFirst measuredFeedback_legal.1)
      measuredFeedbackInput (1 : Fin 2) at h
  rw [Fin.sum_univ_one, measuredFeedback_first_probability] at h
  norm_num [CoinCode.wordWeight] at h
  exact h

theorem measuredFeedback_exhaustive (z : measuredFeedback.Outcome) :
    z = measuredFeedbackZero ∨ z = measuredFeedbackHadamard ∨ z = measuredFeedbackQuery := by
  rcases z with ⟨i,c,j⟩
  change Fin 2 at i
  fin_cases i
  · change Fin 1 at c
    fin_cases c
    change Fin 1 at j
    fin_cases j
    exact Or.inl rfl
  · change Fin 2 at c
    fin_cases c
    · change Fin 1 at j
      fin_cases j
      exact Or.inr (Or.inl rfl)
    · change Fin 1 at j
      fin_cases j
      exact Or.inr (Or.inr rfl)

theorem measuredFeedback_sum {B : Type} [AddCommMonoid B] (f : measuredFeedback.Outcome → B) :
    (∑ z, f z) = f measuredFeedbackZero + f measuredFeedbackHadamard + f measuredFeedbackQuery := by
  have hu : (Finset.univ : Finset measuredFeedback.Outcome) =
      {measuredFeedbackZero, measuredFeedbackHadamard, measuredFeedbackQuery} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact measuredFeedback_exhaustive z
  rw [hu]
  rw [Finset.sum_insert (by decide +kernel : measuredFeedbackZero ∉
      ({measuredFeedbackHadamard, measuredFeedbackQuery} : Finset _)),
    Finset.sum_insert (by decide +kernel : measuredFeedbackHadamard ∉ ({measuredFeedbackQuery} : Finset _)),
    Finset.sum_singleton]
  exact (add_assoc _ _ _).symm

theorem measuredFeedback_statistics :
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      ((measuredFeedback.record measuredFeedbackFlip z).coinWord.length : ℝ)) = 1 / 2 ∧
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      ((measuredFeedback.record measuredFeedbackFlip z).queries : ℝ)) = 1 / 4 ∧
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      ((measuredFeedback.record measuredFeedbackFlip z).gates : ℝ)) = 3 / 4 ∧
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      ((measuredFeedback.record measuredFeedbackFlip z).measurements : ℝ)) = 1 ∧
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      (if (measuredFeedback.record measuredFeedbackFlip z).accepted then 1 else 0)) = 3 / 4 ∧
    (∑ z, instrumentProb measuredFeedbackInstrument measuredFeedbackInput z *
      ((measuredFeedback.record measuredFeedbackFlip z).value.2 : ℝ)) = 5 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [measuredFeedback_sum, measuredFeedback_probability_zero, measuredFeedback_probability_hadamard,
      measuredFeedback_probability_query, measuredFeedback_record_zero,
      measuredFeedback_record_hadamard, measuredFeedback_record_query] <;> norm_num

theorem measuredFeedbackFlip_apply (i j : Fin 2) :
    measuredFeedbackFlip i j = if i = j then (0 : ℂ) else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem measuredFeedback_suffix_zero (O : Operator 2) :
    (measuredFeedback.suffixLeaf O measuredFeedbackZero).operator = measuredFeedbackFlip := by
  change (1 : Operator 2) * measuredFeedbackFlip = _
  rw [Matrix.one_mul]

theorem measuredFeedback_suffix_hadamard (O : Operator 2) :
    (measuredFeedback.suffixLeaf O measuredFeedbackHadamard).operator = Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin := by
  change (1 : Operator 2) * Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin = _
  rw [Matrix.one_mul]

theorem measuredFeedback_suffix_query (O : Operator 2) :
    (measuredFeedback.suffixLeaf O measuredFeedbackQuery).operator = O := by
  change (1 : Operator 2) * O = _
  rw [Matrix.one_mul]

theorem measuredFeedback_state_zero :
    measuredFeedbackInstrument.branch measuredFeedbackZero measuredFeedbackInput =
      ((1 / 2 : ℝ) : ℂ) • Projector (Finset.univ.filter fun i : Fin 2 => i = 1) := by
  have hp : (measuredFeedback.prefixLeaf measuredFeedbackFlip measuredFeedbackZero.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 0) :=
    measuredFeedback_first_operator measuredFeedbackFlip (0 : Fin 2)
  rw [measuredFeedbackInstrument, FairFeedback.branch_law, measuredFeedback_suffix_zero, hp]
  change (1 : ℂ) • conjBranch measuredFeedbackFlip
    (conjBranch (Projector (Finset.univ.filter fun i : Fin 2 => i = 0)) measuredFeedbackInput) = _
  rw [one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [conjBranch_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, measuredFeedbackFlip_apply,
    measuredFeedbackInput, Projector, Matrix.smul_apply, Matrix.one_apply]

theorem measuredFeedback_state_query :
    measuredFeedbackInstrument.branch measuredFeedbackQuery measuredFeedbackInput =
      ((1 / 4 : ℝ) : ℂ) • Projector (Finset.univ.filter fun i : Fin 2 => i = 0) := by
  have hp : (measuredFeedback.prefixLeaf measuredFeedbackFlip measuredFeedbackQuery.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  rw [measuredFeedbackInstrument, FairFeedback.branch_law, measuredFeedback_suffix_query, hp]
  have hw : CoinCode.wordWeight (measuredFeedback.codeWord measuredFeedbackQuery) = 1 / 2 := by
    change (1 / 2 : ℝ) ^ 1 = 1 / 2
    exact pow_one _
  rw [hw]
  change ((1 / 2 : ℝ) : ℂ) • conjBranch measuredFeedbackFlip
    (conjBranch (Projector (Finset.univ.filter fun i : Fin 2 => i = 1)) measuredFeedbackInput) = _
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [conjBranch_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, measuredFeedbackFlip_apply,
    measuredFeedbackInput, Projector, Matrix.smul_apply, Matrix.one_apply]

theorem measuredFeedbackHadamard_apply (i j : Fin 2) :
    Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin i j =
      (Real.sqrt 2 : ℂ)⁻¹ * (if i = 1 ∧ j = 1 then -1 else 1) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem measuredFeedback_hadamard_coherence :
    (measuredFeedbackInstrument.branch measuredFeedbackHadamard measuredFeedbackInput) 0 1 = -1 / 8 := by
  have hp : (measuredFeedback.prefixLeaf measuredFeedbackFlip measuredFeedbackHadamard.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  rw [measuredFeedbackInstrument, FairFeedback.branch_law, measuredFeedback_suffix_hadamard, hp]
  have hw : CoinCode.wordWeight (measuredFeedback.codeWord measuredFeedbackHadamard) = 1 / 2 := by
    change (1 / 2 : ℝ) ^ 1 = 1 / 2
    exact pow_one _
  rw [hw]
  change (((1 / 2 : ℝ) : ℂ) • conjBranch Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin
    (conjBranch (Projector (Finset.univ.filter fun i : Fin 2 => i = 1)) measuredFeedbackInput)) 0 1 = _
  norm_num [conjBranch_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    measuredFeedbackHadamard_apply, measuredFeedbackInput, Projector, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  rw [inv_pow, sqrt2_sq]
  norm_num

theorem measuredFeedback_forgotten_coherence :
    (∑ z, measuredFeedbackInstrument.branch z measuredFeedbackInput) 0 1 = -1 / 8 := by
  rw [measuredFeedback_sum]
  simp only [Matrix.add_apply, measuredFeedback_state_zero, measuredFeedback_state_query,
    measuredFeedback_hadamard_coherence, Matrix.smul_apply]
  norm_num [Projector]

theorem measuredFeedback_zero_Born_branches :
    measuredFeedbackInstrument.branch measuredFeedbackHadamard
        (Projector (Finset.univ.filter fun i : Fin 2 => i = 0)) = 0 ∧
    measuredFeedbackInstrument.branch measuredFeedbackQuery
        (Projector (Finset.univ.filter fun i : Fin 2 => i = 0)) = 0 := by
  have hz : conjBranch (Projector (Finset.univ.filter fun i : Fin 2 => i = 1))
      (Projector (Finset.univ.filter fun i : Fin 2 => i = 0)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conjBranch_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Projector, Fin.sum_univ_two]
  have hpH : (measuredFeedback.prefixLeaf measuredFeedbackFlip measuredFeedbackHadamard.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  have hpQ : (measuredFeedback.prefixLeaf measuredFeedbackFlip measuredFeedbackQuery.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  constructor
  · rw [measuredFeedbackInstrument, FairFeedback.branch_law, hpH, hz]
    simp
  · rw [measuredFeedbackInstrument, FairFeedback.branch_law, hpQ, hz]
    simp

namespace CoinCode
variable {A : Type}

theorem paths_real_expectation (p : CoinCode A) (F : A × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ENNReal.ofReal (∑ c : Fin p.paths.length,
      wordWeight (p.paths.get c).2 * F ((p.paths.get c).1, (p.paths.get c).2.length)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law (fun x => ENNReal.ofReal (F x)) := by
  rw [paths_expectation]
  have he := congrArg (fun L : List (A × List Bool) =>
    (L.map (fun z => (1 / 2 : ℝ≥0∞) ^ z.2.length * ENNReal.ofReal (F (z.1, z.2.length)))).sum)
    (List.ofFn_get p.paths)
  (try dsimp only at he)
  rw [List.map_ofFn, List.sum_ofFn] at he
  dsimp only [Function.comp_def] at he
  rw [← he, ENNReal.ofReal_sum_of_nonneg (fun c _ =>
    mul_nonneg (wordWeight_nonneg _) (hF _))]
  apply Finset.sum_congr rfl
  intro c _
  rw [ENNReal.ofReal_mul (wordWeight_nonneg _)]
  congr 1
  simp [wordWeight, ENNReal.inv_pow]
end CoinCode
namespace FairFeedback
open Classical
variable {D : ℕ} {A : Type}

theorem classical_expectation (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (F : (i : Fin (observedLeafCount M.first)) → A × ℕ → ℝ) :
    (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
      F z.1 ((M.path z.1 z.2.1).1, (M.codeWord z).length)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        ∑ c : Fin (M.choose i).paths.length,
          CoinCode.wordWeight (M.path i c).2 * F i ((M.path i c).1, (M.path i c).2.length) := by
  simp only [Fintype.sum_sigma, codeWord]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ c : Fin (M.choose i).paths.length,
        (∑ j : Fin (observedLeafCount (M.next i (M.path i c).1)),
          instrumentProb (M.instrument O hO hM) ρ ⟨i,c,j⟩) *
            F i ((M.path i c).1, (M.path i c).2.length) := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Finset.sum_mul _ _ _).symm
    _ = _ := by
      simp_rw [M.sum_suffix_probability O hO hM ρ i]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem classical_expectation_toReal (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (F : (i : Fin (observedLeafCount M.first)) → A × ℕ → ℝ) (hF : ∀ i x, 0 ≤ F i x) :
    (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
      F z.1 ((M.path z.1 z.2.1).1, (M.codeWord z).length)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (M.choose i).law (fun x => ENNReal.ofReal (F i x))).toReal := by
  rw [classical_expectation]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have he := congrArg ENNReal.toReal ((M.choose i).paths_real_expectation (F i) (hF i))
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun c _ =>
    mul_nonneg (CoinCode.wordWeight_nonneg _) (hF i _)))] at he
  exact he

theorem classical_event (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (E : (i : Fin (observedLeafCount M.first)) → A × ℕ → Prop) :
    (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
      (if E z.1 ((M.path z.1 z.2.1).1, (M.codeWord z).length) then 1 else 0)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (M.choose i).law (E i)).toReal := by
  classical
  simpa only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, apply_ite ENNReal.ofReal, ENNReal.ofReal_one,
    ENNReal.ofReal_zero] using
    M.classical_expectation_toReal O hO hM ρ
      (fun i x => if E i x then 1 else 0) (by intros; (try dsimp); split_ifs <;> norm_num)

end FairFeedback

namespace FairFeedback
open scoped ComplexOrder
variable {D : ℕ} {A : Type}

theorem classical_expectation_ofReal (M : FairFeedback D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hρ : ρ.PosSemidef)
    (F : (i : Fin (observedLeafCount M.first)) → A × ℕ → ℝ) (hF : ∀ i x, 0 ≤ F i x) :
    ENNReal.ofReal (∑ z : M.Outcome, instrumentProb (M.instrument O hO hM) ρ z *
      F z.1 ((M.path z.1 z.2.1).1, (M.codeWord z).length)) =
    ∑ i : Fin (observedLeafCount M.first),
      ENNReal.ofReal (instrumentProb (observedInstrument O hO M.first hM.1) ρ i) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (M.choose i).law (fun x => ENNReal.ofReal (F i x)) := by
  rw [M.classical_expectation O hO hM ρ F]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (instrumentProb_nonneg _ hρ _) (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (CoinCode.wordWeight_nonneg _) (hF i _))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (instrumentProb_nonneg _ hρ _)]
  congr 1
  exact (M.choose i).paths_real_expectation (F i) (hF i)
end FairFeedback

namespace CoinCode
open Classical
variable {A : Type}

theorem paths_event_toReal (p : CoinCode A) (E : A × ℕ → Prop) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p.law E).toReal =
      ∑ c : Fin p.paths.length, wordWeight (p.paths.get c).2 *
        (if E ((p.paths.get c).1, (p.paths.get c).2.length) then 1 else 0) := by
  have h := p.paths_real_expectation (fun x => if E x then (1 : ℝ) else 0)
    (by intro x; (try dsimp); split_ifs <;> norm_num)
  have hn : 0 ≤ ∑ c : Fin p.paths.length, wordWeight (p.paths.get c).2 *
      (if E ((p.paths.get c).1, (p.paths.get c).2.length) then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (wordWeight_nonneg _)
      (by split_ifs <;> norm_num))
  have he := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hn] at he
  simpa only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, apply_ite ENNReal.ofReal,
      ENNReal.ofReal_one, ENNReal.ofReal_zero] using he.symm
end CoinCode

namespace HybridLeaf
end HybridLeaf

namespace HybridLeaf
variable {D : ℕ} {A : Type}

theorem effect_quantum (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ)) (leaf : HybridLeaf D A) :
    (leaf.quantum U q g m out).effect = U.conjTranspose * leaf.effect * U := by
  simp only [effect, quantum, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]

theorem effect_coin (b : Bool) (leaf : HybridLeaf D A) :
    (leaf.coin b).effect = (1 / 2 : ℂ) • leaf.effect := by
  simp only [effect, coin, Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,
      Complex.ofReal_mul, smul_smul]
  norm_num

theorem kraus_adjoint_mul (leaf : HybridLeaf D A) :
    leaf.kraus.conjTranspose * leaf.kraus = leaf.effect := by
  have hs : star ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) *
      ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) =
        ((CoinCode.wordWeight leaf.coins : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (CoinCode.wordWeight_nonneg _)]
  simp only [kraus, effect, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm] at hs
  rw [hs]

theorem kraus_branch (leaf : HybridLeaf D A) (ρ : Operator D) :
    conjBranch leaf.kraus ρ = ((CoinCode.wordWeight leaf.coins : ℝ) : ℂ) • conjBranch leaf.operator ρ := by
  have hs : ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) *
      star ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) =
        ((CoinCode.wordWeight leaf.coins : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (CoinCode.wordWeight_nonneg _)]
  simp only [kraus, conjBranch_apply, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
  rw [mul_comm] at hs
  rw [hs]

theorem sum_quantum (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ)) (ls : List (HybridLeaf D A)) :
    ((ls.map (quantum U q g m out)).map effect).sum = U.conjTranspose * (ls.map effect).sum * U := by
  induction ls with
  | nil => simp
  | cons leaf ls ih => simp only [List.map_cons, List.sum_cons, effect_quantum, ih,
      Matrix.mul_add, Matrix.add_mul]

theorem sum_coin (b : Bool) (ls : List (HybridLeaf D A)) :
    ((ls.map (coin b)).map effect).sum = (1 / 2 : ℂ) • (ls.map effect).sum := by
  induction ls with
  | nil => simp
  | cons leaf ls ih => simp only [List.map_cons, List.sum_cons, effect_coin, ih, smul_add]
end HybridLeaf

namespace HybridProgram
variable {D : ℕ} {A B : Type}

theorem runCoins_frontier (bs : List Bool) (p : HybridProgram D A) (hp : p.Frontier) :
    p.runCoins bs = (p,0) := by
  cases bs <;> cases p <;> simp_all [runCoins, Frontier]

theorem runCoins_ofCoins (bs : List Bool) (p : CoinCode B) (k : B → HybridProgram D A)
    (hk : ∀ a, (k a).Frontier) :
    (ofCoins p k).runCoins bs = (ofCoins (p.run bs).1 k, (p.run bs).2) := by
  induction p generalizing bs with
  | ret a => rw [ofCoins, CoinCode.run_ret, runCoins_frontier _ _ (hk a)]; rfl
  | bit p q hp hq =>
      cases bs with
      | nil => rfl
      | cons b bs => cases b <;> simp only [ofCoins, runCoins, CoinCode.run, Bool.false_eq_true,
          ↓reduceIte, hp, hq]

theorem runCoins_append (xs ys : List Bool) (p : HybridProgram D A) :
    p.runCoins (xs ++ ys) =
      let z := p.runCoins xs
      let z' := z.1.runCoins ys
      (z'.1,z.2 + z'.2) := by
  induction xs generalizing p with
  | nil => simp [runCoins]
  | cons b xs ih =>
      cases p with
      | bit p q =>
          cases b <;> simp only [List.cons_append, runCoins, Bool.false_eq_true,
            ↓reduceIte, ih, Nat.add_assoc]
      | ret a => cases ys <;> simp [runCoins]
      | step s p => cases ys <;> simp [runCoins]
      | measure n label k => cases ys <;> simp [runCoins]
      | project P p q => cases ys <;> simp [runCoins]

theorem leaves_length (O : Operator D) (p : HybridProgram D A) : (p.leaves O).length = p.leafCount := by
  induction p with
  | ret a => rfl
  | step s p ih => cases s <;> simpa [leaves, leafCount] using ih
  | bit p q hp hq => simp [leaves, leafCount, hp, hq]
  | measure n label next ih =>
      simp only [leaves, List.length_flatten, List.map_ofFn, Function.comp_def,
        List.length_map, List.sum_ofFn, leafCount]
      exact Finset.sum_congr rfl (fun i _ => ih i)
  | project P p q hp hq => simp [leaves, leafCount, hp, hq]

theorem bind_legal (p : HybridProgram D A) (hp : p.Legal) (k : A → HybridProgram D B)
    (hk : ∀ a, (k a).Legal) : (p.bind k).Legal := by
  induction p with
  | ret a => exact hk a
  | step s p ih => cases s with
      | gate U => exact ⟨hp.1, ih hp.2⟩
      | query => exact ih hp
  | bit p q hpi hqi => exact ⟨hpi hp.1,hqi hp.2⟩
  | measure n label next ih => exact fun i => ih i (hp i)
  | project P p q hpi hqi => exact ⟨hp.1,hpi hp.2.1,hqi hp.2.2⟩

theorem ofCoins_legal (p : CoinCode B) (k : B → HybridProgram D A) (hk : ∀ a, (k a).Legal) :
    (ofCoins p k).Legal := by
  induction p with
  | ret a => exact hk a
  | bit p q hp hq => exact ⟨hp,hq⟩

theorem ofObserved_legal (p : ObservedCircuit (Fin D)) (hp : observedWellFormed p) :
    (ofObserved p).Legal := by
  induction p with
  | halt b => trivial
  | step s p ih => cases s with
      | gate U => exact ⟨hp.1, ih hp.2⟩
      | query => exact ih hp
  | measure n label next ih => exact fun i => ih i (hp i)
  | project P p q hpi hqi => exact ⟨hp.1,hpi hp.2.1,hqi hp.2.2⟩

theorem prependCircuit_legal (C : Circuit (Fin D)) (hC : IsUnitaryCircuit C)
    (p : HybridProgram D A) (hp : p.Legal) : (prependCircuit C p).Legal := by
  induction C with
  | nil => exact hp
  | cons s C ih => cases s with
      | gate U => obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC; exact ⟨hU,ih hC⟩
      | query => exact ih ((isUnitaryCircuit_query C).mp hC)

theorem cut_legal (n : ℕ) (p : HybridProgram D A) (hp : p.Legal) : (p.cut n).Legal := by
  induction n generalizing p with
  | zero => cases p <;> trivial
  | succ n ih =>
      cases p with
      | ret a => trivial
      | step s p => cases s with
          | gate U => exact ⟨hp.1, ih p hp.2⟩
          | query => exact ih p hp
      | bit p q => exact ⟨ih p hp.1,ih q hp.2⟩
      | measure m label k => exact fun i => ih (k i) (hp i)
      | project P p q => exact ⟨hp.1,ih p hp.2.1,ih q hp.2.2⟩

theorem cut_ret (n : ℕ) (a : A) : (ret a : HybridProgram D A).cut n = .ret (.inl a) := by
  cases n <;> rfl

theorem cut_add (n m : ℕ) (p : HybridProgram D A) :
    p.cut (n + m) = (p.cut n).bind
      (fun z => match z with | .inl a => .ret (.inl a) | .inr q => q.cut m) := by
  induction n generalizing p with
  | zero => cases p <;> simp [cut, bind, cut_ret]
  | succ n ih =>
      cases p with
      | ret a => simp [cut_ret, bind]
      | step s p => simpa only [Nat.succ_add, cut, bind] using congrArg (HybridProgram.step s) (ih p)
      | bit p q => simp only [Nat.succ_add, cut, bind, ih]
      | measure k label next => simp only [Nat.succ_add, cut, bind, ih]
      | project P p q => simp only [Nat.succ_add, cut, bind, ih]

theorem basis_partition {n : ℕ} (label : Fin D → Fin n) :
    ∑ i : Fin n, (Projector (Finset.univ.filter fun x => label x = i)).conjTranspose *
      Projector (Finset.univ.filter fun x => label x = i) = (1 : Operator D) := by
  simp_rw [projector_conjTranspose, projector_mul_self]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Projector, Matrix.sum_apply]
  · simp [Projector, Matrix.sum_apply, hxy]

theorem complete (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) :
    ((p.leaves O).map HybridLeaf.effect).sum = 1 := by
  induction p with
  | ret a => simp [leaves, HybridLeaf.effect, CoinCode.wordWeight]
  | step s p ih =>
      cases s with
      | gate U =>
          rw [leaves, HybridLeaf.sum_quantum, ih hp.2, Matrix.mul_one]
          simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hp.1
      | query =>
          rw [leaves, HybridLeaf.sum_quantum, ih hp, Matrix.mul_one]
          simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hO
  | bit p q hpi hqi =>
      rw [leaves, List.map_append, List.sum_append, HybridLeaf.sum_coin,
        HybridLeaf.sum_coin, hpi hp.1, hqi hp.2, ← add_smul]
      norm_num
  | measure n label next ih =>
      simp only [leaves, List.map_flatten, List.sum_flatten, List.map_ofFn,
        Function.comp_def, List.sum_ofFn]
      simp_rw [HybridLeaf.sum_quantum, ih _ (hp _), Matrix.mul_one]
      exact basis_partition label
  | project P p q hpi hqi =>
      rw [leaves, List.map_append, List.sum_append, HybridLeaf.sum_quantum,
        HybridLeaf.sum_quantum, hpi hp.2.1, hqi hp.2.2, Matrix.mul_one, Matrix.mul_one]
      have hC := isOrthogonalProjector_compl hp.1
      have hP : P.conjTranspose = P := hp.1.2
      have hCs : (1 - P).conjTranspose = 1 - P := hC.2
      rw [hP, hp.1.1, hCs, hC.1]
      exact sub_add_cancel 1 P
noncomputable def leaf (p : HybridProgram D A) (O : Operator D) (i : Fin p.leafCount) : HybridLeaf D A :=
  (p.leaves O).get (Fin.cast (p.leaves_length O).symm i)

theorem leaf_ofFn (p : HybridProgram D A) (O : Operator D) :
    List.ofFn (p.leaf O) = p.leaves O := by
  have h := List.ofFn_congr (p.leaves_length O) (p.leaves O).get
  simpa only [List.ofFn_get, leaf] using! h.symm

theorem kraus_complete (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) :
    ∑ i : Fin p.leafCount, (p.leaf O i).kraus.conjTranspose * (p.leaf O i).kraus = 1 := by
  simp only [HybridLeaf.kraus_adjoint_mul]
  have h := p.complete O hO hp
  rw [← p.leaf_ofFn O, List.map_ofFn, List.sum_ofFn] at h
  exact h

noncomputable def instrument (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) : Instrument (Fin p.leafCount) D D :=
  Instrument.ofKraus (fun i => (p.leaf O i).kraus) (p.kraus_complete O hO hp)

theorem branch_law (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) (ρ : Operator D) (i : Fin p.leafCount) :
    (p.instrument O hO hp).branch i ρ =
      ((CoinCode.wordWeight (p.leaf O i).coins : ℝ) : ℂ) • conjBranch (p.leaf O i).operator ρ := by
  rw [instrument, Instrument.ofKraus_branch]
  exact HybridLeaf.kraus_branch _ _

theorem probability_law (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) (ρ : Operator D) (i : Fin p.leafCount) :
    instrumentProb (p.instrument O hO hp) ρ i =
      CoinCode.wordWeight (p.leaf O i).coins * (Matrix.trace (conjBranch (p.leaf O i).operator ρ)).re := by
  rw [instrumentProb, branch_law, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem statistic_law (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) (ρ : Operator D)
    (F : HybridLeaf D A → ℝ) :
    (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) ρ i * F (p.leaf O i)) =
      ((p.leaves O).map (fun t => CoinCode.wordWeight t.coins *
        (Matrix.trace (conjBranch t.operator ρ)).re * F t)).sum := by
  rw [← p.leaf_ofFn O, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl (fun i _ => by rw [p.probability_law]; rfl)

theorem cutQueries_legal (n : ℕ) (p : HybridProgram D A) (hp : p.Legal) :
    (p.cutQueries n).Legal := by
  induction p generalizing n with
  | ret a => trivial
  | step s p ih => cases s with
      | gate U => exact ⟨hp.1,ih n hp.2⟩
      | query => cases n with
          | zero => trivial
          | succ n => exact ih n hp
  | bit p q hpi hqi => exact ⟨hpi n hp.1,hqi n hp.2⟩
  | measure m label k ih => exact fun i => ih i n (hp i)
  | project P p q hpi hqi => exact ⟨hp.1,hpi n hp.2.1,hqi n hp.2.2⟩

theorem cutQueries_add (n m : ℕ) (p : HybridProgram D A) :
    p.cutQueries (n + m) = (p.cutQueries n).bind
      (fun z => match z with | .inl a => .ret (.inl a) | .inr q => q.cutQueries m) := by
  induction p generalizing n with
  | ret a => rfl
  | step s p ih => cases s with
      | gate U => simpa only [cutQueries,bind] using congrArg (step (.gate U)) (ih n)
      | query => cases n with
          | zero => simp [cutQueries,bind]
          | succ n => simpa only [Nat.succ_add,cutQueries,bind] using congrArg (step .query) (ih n)
  | bit p q hpi hqi => simp only [cutQueries,bind,hpi,hqi]
  | measure k label next ih => simp only [cutQueries,bind,ih]
  | project P p q hpi hqi => simp only [cutQueries,bind,hpi,hqi]

theorem cutQueries_bound (O : Operator D) (p : HybridProgram D A) (n : ℕ)
    (t : HybridLeaf D (A ⊕ HybridProgram D A)) (ht : t ∈ (p.cutQueries n).leaves O) :
    t.queries ≤ n := by
  induction p generalizing n t with
  | ret a => simp only [cutQueries,leaves,List.mem_singleton] at ht; subst t; exact Nat.zero_le n
  | step s p ih => cases s with
      | gate U =>
          obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
          exact ih n z hz
      | query => cases n with
          | zero => simp only [cutQueries,leaves,List.mem_singleton] at ht; subst t; rfl
          | succ n =>
              obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
              change z.queries + 1 ≤ n + 1
              exact Nat.add_le_add_right (ih n z hz) 1
  | bit p q hpi hqi =>
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hpi n z hz
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hqi n z hz
  | measure m label k ih =>
      obtain ⟨ls,hls,ht⟩ := List.mem_flatten.mp ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hls
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
      exact ih i n z hz
  | project P p q hpi hqi =>
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hpi n z hz
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hqi n z hz

theorem ofObserved_leaves {D : ℕ} (O : Operator D) (p : ObservedCircuit (Fin D)) :
    (((ofObserved p).leaves O).map HybridLeaf.toObserved) = observedKrausLeaves O p := by
  induction p with
  | halt b => rfl
  | step s p ih => cases s <;> simp only [ofObserved,leaves,observedKrausLeaves,List.map_map,
      Function.comp_def, Qatlib.Concepts.AdversaryBounds.AdvDuality.toObserved_quantum] <;>
      rw [← Function.comp_def,← List.map_map,ih]
  | measure n label k ih =>
      simp only [ofObserved,leaves,observedKrausLeaves,List.map_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,Qatlib.Concepts.AdversaryBounds.AdvDuality.toObserved_quantum]
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [← Function.comp_def,← List.map_map,ih]
  | project P p q hp hq =>
      simp only [ofObserved,leaves,observedKrausLeaves,List.map_append,List.map_map,
        Function.comp_def,Qatlib.Concepts.AdversaryBounds.AdvDuality.toObserved_quantum]
      rw [← Function.comp_def,← List.map_map,hp,← Function.comp_def,← List.map_map,hq]

theorem ofObserved_no_coins {D : ℕ} (O : Operator D) (p : ObservedCircuit (Fin D))
    (t : HybridLeaf D Bool) (ht : t ∈ (ofObserved p).leaves O) : t.coins = [] := by
  induction p generalizing t with
  | halt b => simp only [ofObserved,leaves,List.mem_singleton] at ht; subst t; rfl
  | step s p ih => cases s <;> obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht <;> exact ih z hz
  | measure n label k ih =>
      obtain ⟨ls,hls,ht⟩ := List.mem_flatten.mp ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hls
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
      exact ih i z hz
  | project P p q hp hq =>
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hp z hz
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hq z hz

theorem eval_bind (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B)
    (ψ : QState (Fin D)) (F : B → QState (Fin D) → ℝ) :
    (p.bind k).eval O ψ F = p.eval O ψ (fun a φ => (k a).eval O φ F) := by
  induction p generalizing ψ with
  | ret a => rfl
  | step s p ih => cases s <;> simp only [bind,eval,ih]
  | bit p q hp hq => simp only [bind,eval,hp,hq]
  | measure n label next ih => simp only [bind,eval,ih]
  | project P p q hp hq => simp only [bind,eval,hp,hq]

theorem eval_leaves (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F : A → QState (Fin D) → ℝ) :
    p.eval O ψ F = ((p.leaves O).map (fun t => CoinCode.wordWeight t.coins *
      F t.value (ApplyGate t.operator ψ))).sum := by
  induction p generalizing ψ with
  | ret a => simp [eval,leaves,CoinCode.wordWeight,applyGate_one]
  | step s p ih => cases s <;>
      simp only [eval,leaves,ih,List.map_map,Function.comp_def,HybridLeaf.quantum,applyGate_mul]
  | bit p q hp hq =>
      simp only [eval,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.coin,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add, List.sum_map_mul_left,List.sum_map_mul_left]
  | measure n label k ih =>
      simp only [eval,leaves,List.map_flatten,List.sum_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,List.sum_ofFn,HybridLeaf.quantum,applyGate_mul,Collapse,ih]
  | project P p q hp hq =>
      simp only [eval,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.quantum,applyGate_mul]

theorem eval_instrument (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ψ : QState (Fin D)) (f : A → ℝ) :
    (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) (outerProduct ψ) i *
      f (p.leaf O i).value) = p.eval O ψ (fun a φ => branchMass φ * f a) := by
  rw [eval_leaves,← p.leaf_ofFn O,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [p.probability_law,conjBranch_outerProduct,trace_outerProduct]
  simp only [Complex.ofReal_re]
  change (CoinCode.wordWeight (p.leaf O i).coins * branchMass (ApplyGate (p.leaf O i).operator ψ)) *
    f (p.leaf O i).value = CoinCode.wordWeight (p.leaf O i).coins *
      (branchMass (ApplyGate (p.leaf O i).operator ψ) * f (p.leaf O i).value)
  exact mul_assoc _ _ _

theorem eval_ofCoins (O : Operator D) (p : CoinCode B) (k : B → HybridProgram D A)
    (ψ : QState (Fin D)) (F : A → QState (Fin D) → ℝ) :
    (ofCoins p k).eval O ψ F =
      (p.paths.map (fun z => CoinCode.wordWeight z.2 * (k z.1).eval O ψ F)).sum := by
  induction p with
  | ret a => simp [ofCoins,CoinCode.paths,CoinCode.wordWeight]
  | bit p q hp hq =>
      simp only [ofCoins,eval,hp,hq,CoinCode.paths,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]

theorem eval_prepend (O : Operator D) (C : Circuit (Fin D)) (p : HybridProgram D A)
    (ψ : QState (Fin D)) (F : A → QState (Fin D) → ℝ) :
    (prependCircuit C p).eval O ψ F = p.eval O (Run O C ψ) F := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [prependCircuit,eval,Run,ih]

theorem eval_ofObserved (O : Operator D) (p : ObservedCircuit (Fin D))
    (ψ : QState (Fin D)) (F : Bool → QState (Fin D) → ℝ) :
    (ofObserved p).eval O ψ F = ((observedTraces O p ψ).map (fun t => F t.accepted t.state)).sum := by
  induction p generalizing ψ with
  | halt b => simp [ofObserved,eval,observedTraces]
  | step s p ih => cases s <;> simp only [ofObserved,eval,observedTraces,ih,List.map_map,Function.comp_def]
  | measure n label k ih =>
      simp only [ofObserved,eval,observedTraces,List.map_flatten,List.sum_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,List.sum_ofFn,ih]
  | project P p q hp hq =>
      simp only [ofObserved,eval,observedTraces,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,ProjectiveBranch,hp,hq,Bool.false_eq_true,↓reduceIte]

theorem eval_add (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F G : A → QState (Fin D) → ℝ) :
    p.eval O ψ (fun a φ => F a φ + G a φ) = p.eval O ψ F + p.eval O ψ G := by
  simp only [eval_leaves,mul_add, List.sum_map_add]

theorem eval_mul (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F : A → QState (Fin D) → ℝ) (c : ℝ) :
    p.eval O ψ (fun a φ => c * F a φ) = c * p.eval O ψ F := by
  simp only [eval_leaves]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

theorem eval_mass_smul (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (f : A → ℝ) (c : ℂ) :
    p.eval O (c • ψ) (fun a φ => branchMass φ * f a) =
      ‖c‖ ^ 2 * p.eval O ψ (fun a φ => branchMass φ * f a) := by
  simp only [eval_leaves,ApplyGate,Matrix.mulVec_smul,branchMass,measureProb_smul]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

theorem eval_mass (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ψ : QState (Fin D)) :
    p.eval O ψ (fun _ φ => branchMass φ) = branchMass ψ := by
  have h := p.eval_instrument O hO hp ψ (fun _ => 1)
  simp only [mul_one] at h
  rw [← h,sum_instrumentProb,trace_outerProduct,Complex.ofReal_re]
  rfl

namespace Path

theorem record_value (O : Operator D) {p : HybridProgram D A} (h : Path p) :
    (h.record O).value = h.result := by
  induction h with
  | ret a => rfl
  | step s h ih => cases s <;> exact ih
  | bitFalse h ih => exact ih
  | bitTrue h ih => exact ih
  | measure i h ih => exact ih
  | projectFalse h ih => exact ih
  | projectTrue h ih => exact ih

theorem record_mem (O : Operator D) {p : HybridProgram D A} (h : Path p) :
    h.record O ∈ p.leaves O := by
  induction h with
  | ret a => exact List.mem_singleton_self _
  | step s h ih => cases s <;> exact List.mem_map.mpr ⟨_,ih,rfl⟩
  | bitFalse h ih => exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
  | bitTrue h ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
  | measure i h ih =>
      apply List.mem_flatten.mpr
      exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_map.mpr ⟨_,ih,rfl⟩⟩
  | projectFalse h ih => exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
  | projectTrue h ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)

theorem record_index (O : Operator D) {p : HybridProgram D A} (h : Path p) :
    ∃ i : Fin p.leafCount, p.leaf O i = h.record O := by
  have hm := h.record_mem O
  rw [← p.leaf_ofFn O] at hm
  exact List.mem_ofFn.mp hm

end Path

end HybridProgram

namespace HybridLeaf
variable {D : ℕ} {A B : Type}

theorem join_quantum (a : HybridLeaf D A) (b : HybridLeaf D B) (U : Operator D)
    (q g m : ℕ) (out : List (ℕ × ℕ)) :
    (a.quantum U q g m out).join b = (a.join b).quantum U q g m out := by
  simp only [join,quantum,Matrix.mul_assoc,Nat.add_assoc,List.append_assoc]

theorem join_coin (a : HybridLeaf D A) (b : HybridLeaf D B) (c : Bool) :
    (a.coin c).join b = (a.join b).coin c := by
  simp only [join,coin,List.cons_append]

theorem quantum_value (a : HybridLeaf D A) (U : Operator D)
    (q g m : ℕ) (out : List (ℕ × ℕ)) : (a.quantum U q g m out).value = a.value := rfl

theorem coin_value (a : HybridLeaf D A) (c : Bool) : (a.coin c).value = a.value := rfl

end HybridLeaf

namespace HybridProgram
variable {D : ℕ} {A B : Type}

private theorem flatten_flatMap {X Y : Type} (ls : List (List X)) (f : X → List Y) :
    ls.flatten.flatMap f = (ls.map (fun l => l.flatMap f)).flatten := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.flatten_cons,List.flatMap_append,List.map_cons,ih]

theorem leaves_bind (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B) :
    (p.bind k).leaves O = (p.leaves O).flatMap
      (fun a => ((k a.value).leaves O).map (a.join ·)) := by
  induction p with
  | ret a =>
      simp only [bind,leaves,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      simp [HybridLeaf.join]
  | step s p ih => cases s <;>
      simp only [bind,leaves,ih,List.map_flatMap,List.flatMap_map,List.map_map,
        Function.comp_def,HybridLeaf.quantum_value,HybridLeaf.join_quantum]
  | bit p q hp hq =>
      simp only [bind,leaves,hp,hq,List.flatMap_append,List.map_flatMap,
        List.flatMap_map,List.map_map,Function.comp_def,HybridLeaf.coin_value,HybridLeaf.join_coin]
  | measure n label next ih =>
      simp only [bind,leaves,ih]
      rw [flatten_flatMap]
      simp only [List.map_ofFn,Function.comp_def,List.flatMap_map,List.map_flatMap,
        List.map_map,HybridLeaf.quantum_value,HybridLeaf.join_quantum]
  | project P p q hp hq =>
      simp only [bind,leaves,hp,hq,List.flatMap_append,List.map_flatMap,
        List.flatMap_map,List.map_map,Function.comp_def,HybridLeaf.quantum_value,HybridLeaf.join_quantum]

theorem bind_queries_le (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B)
    (q r : ℕ) (hp : ∀ a ∈ p.leaves O, a.queries ≤ q)
    (hk : ∀ a, ∀ b ∈ (k a).leaves O, b.queries ≤ r)
    (t : HybridLeaf D B) (ht : t ∈ (p.bind k).leaves O) : t.queries ≤ q + r := by
  rw [leaves_bind] at ht
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  change b.queries + a.queries ≤ q + r
  have h1 := hp a ha
  have h2 := hk a.value b hb
  omega

theorem ofCoins_queries_le (O : Operator D) (p : CoinCode B) (k : B → HybridProgram D A)
    (q : ℕ) (hk : ∀ a, ∀ t ∈ (k a).leaves O, t.queries ≤ q)
    (t : HybridLeaf D A) (ht : t ∈ (ofCoins p k).leaves O) : t.queries ≤ q := by
  induction p generalizing t with
  | ret a => exact hk a t ht
  | bit p r hp hr =>
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht; exact hp u hu
      · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht; exact hr u hu

theorem prependCircuit_queries (O : Operator D) (C : Circuit (Fin D)) (p : HybridProgram D A)
    (t : HybridLeaf D A) (ht : t ∈ (prependCircuit C p).leaves O) :
    ∃ a ∈ p.leaves O, t.queries = a.queries + QueryCount C := by
  induction C generalizing t with
  | nil => exact ⟨t,ht,rfl⟩
  | cons s C ih =>
      cases s with
      | gate U =>
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
          obtain ⟨a,ha,hq⟩ := ih u hu
          exact ⟨a,ha,hq⟩
      | query =>
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
          obtain ⟨a,ha,hq⟩ := ih u hu
          refine ⟨a,ha,?_⟩
          change u.queries + 1 = a.queries + (QueryCount C + 1)
          omega

end HybridProgram

namespace HybridLeaf
variable {D : ℕ} {A B : Type}

theorem join_branch (a : HybridLeaf D A) (b : HybridLeaf D B) (ρ : Operator D) :
    conjBranch (a.join b).kraus ρ = conjBranch b.kraus (conjBranch a.kraus ρ) := by
  simp only [kraus_branch,join,CoinCode.wordWeight,List.length_append,pow_add,Complex.ofReal_mul,
    map_smul,smul_smul]
  simp only [conjBranch_apply,Matrix.conjTranspose_mul,Matrix.mul_assoc]
end HybridLeaf
namespace HybridProgram.Path
variable {D : ℕ} {A B : Type}

theorem record_sequence (O : Operator D) {p : HybridProgram D A} (h : HybridProgram.Path p)
    (k : A → HybridProgram D B) (next : HybridProgram.Path (k h.result)) :
    (h.sequence k next).record O = (h.record O).join (next.record O) := by
  induction h with
  | ret a => simp [sequence,record,HybridLeaf.join]
  | step s h ih => cases s <;> simp only [sequence,record,ih,HybridLeaf.join_quantum] <;> rfl
  | bitFalse h ih => simp only [sequence,record,ih,HybridLeaf.join_coin]
  | bitTrue h ih => simp only [sequence,record,ih,HybridLeaf.join_coin]
  | measure i h ih => simp only [sequence,record,ih,HybridLeaf.join_quantum]
  | projectFalse h ih => simp only [sequence,record,ih,HybridLeaf.join_quantum]
  | projectTrue h ih => simp only [sequence,record,ih,HybridLeaf.join_quantum]
end HybridProgram.Path

namespace HybridCounts

theorem plus_shuffle (a b c : HybridCounts) : a.plus (b.plus c) = (a.plus c).plus b := by
  simp only [plus,Nat.add_left_comm,Nat.add_comm]

theorem zero_plus (c : HybridCounts) : zero.plus c = c := by
  cases c
  simp [zero,plus]

theorem plus_assoc (a b c : HybridCounts) : (a.plus b).plus c = a.plus (b.plus c) := by
  simp only [plus,Nat.add_assoc]

theorem read_cons (c : HybridCounts) (b : Bool) (w : List Bool) :
    c.plus ⟨0,0,0,(b :: w).length⟩ = (c.plus ⟨0,0,0,1⟩).plus ⟨0,0,0,w.length⟩ := by
  simp only [plus,List.length_cons,Nat.add_zero]
  congr 1
  omega
end HybridCounts

namespace HybridLeaf
variable {D : ℕ} {A : Type}

theorem counts_quantum (t : HybridLeaf D A) (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ)) :
    (t.quantum U q g m out).counts = t.counts.plus ⟨q,g,m,0⟩ := rfl

theorem counts_coin (t : HybridLeaf D A) (b : Bool) :
    (t.coin b).counts = t.counts.plus ⟨0,0,0,1⟩ := by
  simp only [counts,coin,HybridCounts.plus,List.length_cons,Nat.add_zero]

theorem quantum_coins (t : HybridLeaf D A) (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ)) :
    (t.quantum U q g m out).coins = t.coins := rfl

theorem quantum_operator (t : HybridLeaf D A) (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ)) :
    (t.quantum U q g m out).operator = t.operator * U := rfl

theorem coin_coins (t : HybridLeaf D A) (b : Bool) : (t.coin b).coins = b :: t.coins := rfl

theorem coin_operator (t : HybridLeaf D A) (b : Bool) : (t.coin b).operator = t.operator := rfl
end HybridLeaf

namespace HybridProgram
variable {D : ℕ} {A B : Type}

theorem evalCounts_bind (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B)
    (ψ : QState (Fin D)) (c : HybridCounts) (F : B → QState (Fin D) → HybridCounts → ℝ) :
    (p.bind k).evalCounts O ψ c F = p.evalCounts O ψ c (fun a φ c' => (k a).evalCounts O φ c' F) := by
  induction p generalizing ψ c with
  | ret a => rfl
  | step s p ih => cases s <;> simp only [bind,evalCounts,ih]
  | bit p q hp hq => simp only [bind,evalCounts,hp,hq]
  | measure n label k ih => simp only [bind,evalCounts,ih]
  | project P p q hp hq => simp only [bind,evalCounts,hp,hq]

theorem evalCounts_leaves (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ) :
    p.evalCounts O ψ c F = ((p.leaves O).map (fun t => CoinCode.wordWeight t.coins *
      F t.value (ApplyGate t.operator ψ) (c.plus t.counts))).sum := by
  induction p generalizing ψ c with
  | ret a => simp [evalCounts,leaves,CoinCode.wordWeight,applyGate_one,HybridLeaf.counts,
      HybridCounts.plus]
  | step s p ih => cases s <;>
      simp only [evalCounts,leaves,ih,List.map_map,Function.comp_def,HybridLeaf.counts_quantum,
        HybridCounts.plus_shuffle,HybridLeaf.quantum_value,HybridLeaf.quantum_coins,HybridLeaf.quantum_operator,applyGate_mul]
  | bit p q hp hq =>
      simp only [evalCounts,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.counts_coin,HybridCounts.plus_shuffle,HybridLeaf.coin_value,HybridLeaf.coin_coins,HybridLeaf.coin_operator,
        Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]
  | measure n label next ih =>
      simp only [evalCounts,leaves,List.map_flatten,List.sum_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,List.sum_ofFn,HybridLeaf.counts_quantum,
        HybridCounts.plus_shuffle,HybridLeaf.quantum_value,HybridLeaf.quantum_coins,HybridLeaf.quantum_operator,applyGate_mul,Collapse,ih]
  | project P p q hp hq =>
      simp only [evalCounts,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.counts_quantum,HybridCounts.plus_shuffle,
        HybridLeaf.quantum_value,HybridLeaf.quantum_coins,HybridLeaf.quantum_operator,applyGate_mul]

theorem evalCounts_ignore (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F : A → QState (Fin D) → ℝ) :
    p.evalCounts O ψ c (fun a φ _ => F a φ) = p.eval O ψ F := by
  rw [evalCounts_leaves,eval_leaves]

theorem evalCounts_instrument (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ψ : QState (Fin D)) (f : A → HybridCounts → ℝ) :
    (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) (outerProduct ψ) i *
      f (p.leaf O i).value (p.leaf O i).counts) =
      p.evalCounts O ψ HybridCounts.zero (fun a φ c => branchMass φ * f a c) := by
  rw [evalCounts_leaves,← p.leaf_ofFn O,List.map_ofFn,List.sum_ofFn]
  simp only [HybridCounts.zero_plus]
  apply Finset.sum_congr rfl
  intro i _
  rw [p.probability_law,conjBranch_outerProduct,trace_outerProduct]
  simp only [Complex.ofReal_re]
  change (CoinCode.wordWeight (p.leaf O i).coins * branchMass (ApplyGate (p.leaf O i).operator ψ)) *
    f (p.leaf O i).value (p.leaf O i).counts = CoinCode.wordWeight (p.leaf O i).coins *
      (branchMass (ApplyGate (p.leaf O i).operator ψ) * f (p.leaf O i).value (p.leaf O i).counts)
  exact mul_assoc _ _ _

theorem evalCounts_add_start (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ) :
    p.evalCounts O ψ c F = p.evalCounts O ψ HybridCounts.zero (fun a φ d => F a φ (c.plus d)) := by
  rw [evalCounts_leaves,evalCounts_leaves]
  simp only [HybridCounts.zero_plus]

theorem evalCounts_add (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F G : A → QState (Fin D) → HybridCounts → ℝ) :
    p.evalCounts O ψ c (fun a φ d => F a φ d + G a φ d) =
      p.evalCounts O ψ c F + p.evalCounts O ψ c G := by
  simp only [evalCounts_leaves,mul_add,List.sum_map_add]

theorem evalCounts_mul (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ) (r : ℝ) :
    p.evalCounts O ψ c (fun a φ d => r * F a φ d) = r * p.evalCounts O ψ c F := by
  simp only [evalCounts_leaves]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

theorem evalCounts_mass_smul (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (f : A → HybridCounts → ℝ) (z : ℂ) :
    p.evalCounts O (z • ψ) c (fun a φ d => branchMass φ * f a d) =
      ‖z‖ ^ 2 * p.evalCounts O ψ c (fun a φ d => branchMass φ * f a d) := by
  simp only [evalCounts_leaves,ApplyGate,Matrix.mulVec_smul,branchMass,measureProb_smul]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

theorem evalCounts_fixed (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c d : HybridCounts) (hd : ∀ t ∈ p.leaves O, t.counts = d)
    (F : A → QState (Fin D) → HybridCounts → ℝ) :
    p.evalCounts O ψ c F = p.eval O ψ (fun a φ => F a φ (c.plus d)) := by
  rw [evalCounts_leaves,eval_leaves]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [hd t ht]

theorem prependCircuit_counts (O : Operator D) (C : Circuit (Fin D)) (p : HybridProgram D A)
    (t : HybridLeaf D A) (ht : t ∈ (prependCircuit C p).leaves O) :
    ∃ a ∈ p.leaves O, t.counts = a.counts.plus ⟨QueryCount C,GateCount C,0,0⟩ := by
  induction C generalizing t with
  | nil => exact ⟨t,ht,rfl⟩
  | cons s C ih =>
      cases s with
      | gate U =>
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
          obtain ⟨a,ha,hc⟩ := ih u hu
          refine ⟨a,ha,?_⟩
          rw [HybridLeaf.counts_quantum,hc]
          simp [HybridCounts.plus,QueryCount,GateCount,Nat.add_assoc]
      | query =>
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
          obtain ⟨a,ha,hc⟩ := ih u hu
          refine ⟨a,ha,?_⟩
          rw [HybridLeaf.counts_quantum,hc]
          simp [HybridCounts.plus,QueryCount,GateCount,Nat.add_assoc]

theorem evalCounts_ofCoins (O : Operator D) (p : CoinCode B) (k : B → HybridProgram D A)
    (ψ : QState (Fin D)) (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ) :
    (ofCoins p k).evalCounts O ψ c F =
      (p.paths.map (fun z => CoinCode.wordWeight z.2 *
        (k z.1).evalCounts O ψ (c.plus ⟨0,0,0,z.2.length⟩) F)).sum := by
  induction p generalizing c with
  | ret a => simp [ofCoins,CoinCode.paths,CoinCode.wordWeight,HybridCounts.plus]
  | bit p q hp hq =>
      simp only [ofCoins,evalCounts,hp,hq,CoinCode.paths,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,HybridCounts.read_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]

theorem evalCounts_prepend (O : Operator D) (C : Circuit (Fin D)) (p : HybridProgram D A)
    (ψ : QState (Fin D)) (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ) :
    (prependCircuit C p).evalCounts O ψ c F =
      p.evalCounts O (Run O C ψ) (c.plus ⟨QueryCount C,GateCount C,0,0⟩) F := by
  induction C generalizing ψ c with
  | nil => simp [prependCircuit,Run,QueryCount,GateCount,HybridCounts.plus]
  | cons s C ih => cases s <;> simp [prependCircuit,evalCounts,Run,ih,QueryCount,GateCount,
      HybridCounts.plus,Nat.add_assoc,Nat.add_comm]

end HybridProgram

namespace HybridProgram
variable {D : ℕ} {A : Type}

theorem evalCounts_statistic_start (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ψ : QState (Fin D)) (c : HybridCounts)
    (f : HybridCounts → ℝ) (hf : ∀ a b, f (a.plus b) = f a + f b) :
    p.evalCounts O ψ c (fun _ φ d => branchMass φ * f d) =
      branchMass ψ * f c + p.evalCounts O ψ HybridCounts.zero (fun _ φ d => branchMass φ * f d) := by
  rw [evalCounts_add_start]
  simp only [hf,mul_add]
  rw [evalCounts_add]
  congr 1
  rw [evalCounts_ignore]
  have hpay : (fun (_ : A) (φ : QState (Fin D)) => branchMass φ * f c) = (fun (_ : A) φ => f c * branchMass φ) := by
    funext a φ
    ring
  rw [hpay,eval_mul,eval_mass O hO p hp]
  ring
end HybridProgram

namespace HybridCounts

theorem charge_plus (q g m r : ℝ) (a b : HybridCounts) :
    charge q g m r (a.plus b) = charge q g m r a + charge q g m r b := by
  simp only [charge,plus,Nat.cast_add]
  ring
end HybridCounts

namespace HybridProgram
variable {D : ℕ} {A : Type}

theorem eval_mono (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F G : A → QState (Fin D) → ℝ) (h : ∀ a φ, F a φ ≤ G a φ) :
    p.eval O ψ F ≤ p.eval O ψ G := by
  induction p generalizing ψ with
  | ret a => exact h a ψ
  | step s p ih => cases s <;> exact ih _
  | bit p q hp hq =>
      exact mul_le_mul_of_nonneg_left (add_le_add (hp ψ) (hq ψ)) (by norm_num)
  | measure n label next ih => exact Finset.sum_le_sum (fun i _ => ih i _)
  | project P p q hp hq => exact add_le_add (hp _) (hq _)
end HybridProgram

namespace CoinCode
variable {A : Type}

theorem readMean_expectedCost (p : CoinCode A) :
    ENNReal.ofReal p.readMean = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost p.law := by
  have h := p.paths_real_expectation (fun x => (x.2 : ℝ)) (fun x => Nat.cast_nonneg x.2)
  simp only [ENNReal.ofReal_natCast] at h
  rw [readMean,← List.ofFn_get p.paths,List.map_ofFn,List.sum_ofFn]
  exact h

theorem readMean_nonneg (p : CoinCode A) : 0 ≤ p.readMean := by
  rw [readMean,← List.ofFn_get p.paths,List.map_ofFn,List.sum_ofFn]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (wordWeight_nonneg _) (Nat.cast_nonneg _))

theorem weightedSampler_readMean {N : ℕ} (w : Fin N → ℕ) (b cap : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    (weightedSampler w b cap).readMean = (b : ℝ) * ∑ t ∈ Finset.range cap, (rationalRejectMass w b).toReal ^ t := by
  have hq : rationalRejectMass w b ≤ 1 := by
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one (weightedSampler w b 1).law
      (fun z => rejectionOutcome z.1.1 = .inr ())
    rwa [weightedSampler_timeout w b 1 hb,pow_one] at h
  have hqt : rationalRejectMass w b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  calc
    _ = (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler w b cap).law).toReal := by
      rw [← readMean_expectedCost,ENNReal.toReal_ofReal (readMean_nonneg _)]
    _ = _ := by
      rw [(weightedSampler_expectations w b cap hW hb).1,ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ENNReal.toReal_sum (fun _ _ => ENNReal.pow_ne_top hqt)]
      simp only [ENNReal.toReal_pow]
end CoinCode

namespace HybridCounts

theorem charge_nonneg (q g m r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (c : HybridCounts) : 0 ≤ charge q g m r c := by
  unfold charge
  positivity
end HybridCounts

namespace HybridProgram
variable {D : ℕ} {A : Type}

theorem evalCounts_nonneg (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (c : HybridCounts) (F : A → QState (Fin D) → HybridCounts → ℝ)
    (hF : ∀ a φ d, 0 ≤ F a φ d) : 0 ≤ p.evalCounts O ψ c F := by
  rw [evalCounts_leaves,← p.leaf_ofFn O,List.map_ofFn,List.sum_ofFn]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (CoinCode.wordWeight_nonneg _) (hF _ _ _))

theorem eval_zero (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D)) :
    p.eval O ψ (fun _ _ => 0) = 0 := by
  have h := p.eval_mul O ψ (fun _ _ => (0 : ℝ)) 0
  simpa only [zero_mul] using h

theorem eval_nonneg (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F : A → QState (Fin D) → ℝ) (hF : ∀ a φ, 0 ≤ F a φ) : 0 ≤ p.eval O ψ F := by
  have h := p.eval_mono O ψ (fun _ _ => 0) F hF
  simpa only [eval_zero] using h
end HybridProgram

namespace HybridProgram
variable {D : ℕ} {A : Type}

theorem eval_smul (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F : A → QState (Fin D) → ℝ) (hF : ∀ a (z : ℂ) φ, F a (z • φ) = ‖z‖ ^ 2 * F a φ) (z : ℂ) :
    p.eval O (z • ψ) F = ‖z‖ ^ 2 * p.eval O ψ F := by
  simp only [eval_leaves,ApplyGate,Matrix.mulVec_smul,hF]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring
end HybridProgram

end Qatlib.Concepts.AdversaryBounds.AdvDuality
