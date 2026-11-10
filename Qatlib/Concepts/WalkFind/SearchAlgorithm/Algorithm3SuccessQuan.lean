/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3SuccessStat
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Native
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationQuan
import Qatlib.Foundations.BornMetrics.EventProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open scoped Classical BigOperators

theorem verifiedOutput_hasCollision {N M k w : ℕ} (x : Fin N → ZMod M)
    (q : OutputSpace N M k w) (hq : verifiedOutput x q) : HasCollision k x := by
  obtain ⟨_, hinj, v, hv⟩ := hq
  refine ⟨Finset.univ.image q.2.2.2, ?_, v, ?_⟩
  · simp [Finset.card_image_of_injective _ hinj]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hv j

theorem frameCallProbability_bounds {N M k : ℕ} [NeZero M]
    (A : RandomQueryAlgorithm N M k) (f : Algorithm3Frame N) (x : Fin N → ZMod M) :
    0 ≤ frameCallProbability A f x ∧ frameCallProbability A f x ≤ 1 := by
  letI : Nonempty (OutputSpace N M k A.workBits) := ⟨A.start ⟨0, A.positiveSeeds⟩⟩
  have hseeds : (0 : ℝ) < A.seeds := by exact_mod_cast A.positiveSeeds
  have hb (s : Fin A.seeds) :
      MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
        (Finset.univ.filter (verifiedInFrame f x)) ≤ 1 :=
    measureProb_le_one ((A.unitary s).normalized_run
      (alphabet_oracle_actual_unitarity_and_filter _ N M x) (normalized_ket _)) _
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun s _ => measureProb_nonneg _ _) hseeds.le
  · unfold frameCallProbability
    apply (div_le_one hseeds).mpr
    simpa using! Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hb s)

theorem frameCallProbability_no_collision {N M k : ℕ} [NeZero M]
    (A : RandomQueryAlgorithm N M k) (f : Algorithm3Frame N) (x : Fin N → ZMod M)
    (hx : ¬HasCollision k x) : frameCallProbability A f x = 0 := by
  letI : Nonempty (OutputSpace N M k A.workBits) := ⟨A.start ⟨0, A.positiveSeeds⟩⟩
  have hevent : (Finset.univ : Finset (OutputSpace N M k A.workBits)).filter
      (verifiedInFrame f x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro q _ hq
    exact hx (verifiedOutput_hasCollision x q hq.1)
  simp [frameCallProbability, hevent, MeasureProb]

theorem algorithm3Tree_no_collision {N M k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (hx : ¬HasCollision k x) (P : Algorithm3Tree N M k) :
    treeProbability x P = 0 := by
  induction P with
  | readAll f A => exact frameCallProbability_no_collision A f x hx
  | grover f A => exact frameCallProbability_no_collision A f x hx
  | walk f memory A plan children ih =>
    simp [treeProbability, frameCallProbability_no_collision A.actual f x hx, ih]

theorem algorithm3Tree_probability_bounds {N M k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (P : Algorithm3Tree N M k) :
    0 ≤ treeProbability x P ∧ treeProbability x P ≤ 1 := by
  induction P with
  | readAll f A => exact frameCallProbability_bounds A f x
  | grover f A => exact frameCallProbability_bounds A f x
  | walk f memory A plan children ih =>
    obtain ⟨hA0, hA1⟩ := frameCallProbability_bounds A.actual f x
    have hs : (0 : ℝ) < plan.seeds := by exact_mod_cast plan.positiveSeeds
    have hmean0 : 0 ≤ (∑ s, treeProbability x (children s))/(plan.seeds : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun s _ => (ih s).1) hs.le
    have hmean1 : (∑ s, treeProbability x (children s))/(plan.seeds : ℝ) ≤ 1 := by
      apply (div_le_one hs).mpr
      simpa using! Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => (ih s).2)
    simp only [treeProbability]
    constructor
    · exact add_nonneg hA0 (mul_nonneg (sub_nonneg.mpr hA1) hmean0)
    · nlinarith

theorem algorithm3Tree_first_call {N M k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (f : Algorithm3Frame N) (memory : ℕ)
    (A : Algorithm3NativeCall (M:=M) k f memory) (plan : Algorithm3Plan k N f)
    (children : Fin plan.seeds → Algorithm3Tree N M k) :
    frameCallProbability A.actual f x ≤
      treeProbability x (.walk f memory A plan children) := by
  have hA := frameCallProbability_bounds A.actual f x
  have hmean : 0 ≤ (∑ s, treeProbability x (children s))/(plan.seeds : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun s _ =>
      (algorithm3Tree_probability_bounds x (children s)).1) (Nat.cast_nonneg _)
  dsimp only [treeProbability]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hA.2) hmean)

theorem algorithm3Tree_children_mean {N M k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (f : Algorithm3Frame N) (memory : ℕ)
    (A : Algorithm3NativeCall (M:=M) k f memory) (plan : Algorithm3Plan k N f)
    (children : Fin plan.seeds → Algorithm3Tree N M k) :
    (∑ s, treeProbability x (children s))/(plan.seeds : ℝ) ≤
      treeProbability x (.walk f memory A plan children) := by
  have hA := frameCallProbability_bounds A.actual f x
  have hs : (0 : ℝ) < plan.seeds := by exact_mod_cast plan.positiveSeeds
  have hmean : (∑ s, treeProbability x (children s))/(plan.seeds : ℝ) ≤ 1 := by
    apply (div_le_one hs).mpr
    simpa using! Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
      (algorithm3Tree_probability_bounds x (children s)).2)
  dsimp only [treeProbability]
  nlinarith

theorem frameSet_initial (N : ℕ) : frameSet (initialFrame N) = Finset.univ := by
  ext i
  simp [frameSet, initialFrame]

theorem algorithm3Tree_unique_success {N M k r : ℕ} [NeZero M]
    (hN : 2 ≤ N) (ε C p : ℝ) (hε : 0 < ε) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Algorithm3Tree N M k) (hroot : treeFrame P = initialFrame N)
    (hvalid : algorithm3Valid r C P) (hp : uniqueCallProbability p P)
    (x : Fin N → ZMod M) (hx : ∃! S, IsCollision k x S) :
    (1-ε)*p/2 ≤ treeProbability x P := by
  have hunique : ∃! S, S ⊆ frameSet (initialFrame N) ∧ IsCollision k x S := by
    simpa [frameSet_initial] using! hx
  have hlo : (1-ε)*p/2 ≤ p := by nlinarith
  have hhalf : (1-ε)*p/2 ≤ 1/2 := by nlinarith
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnge : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hninv : 1/(N : ℝ) ≤ 1/2 := (div_le_div_iff₀ hnpos (by norm_num)).mpr (by simpa using! hnge)
  cases P with
  | readAll f A =>
    have hf : f = initialFrame N := hroot
    subst f
    obtain ⟨_, _, _, _, hcall⟩ := hvalid
    have hc : frameHasCollision k x (initialFrame N) := ⟨hunique.choose,
      hunique.choose_spec.1⟩
    simpa [treeProbability, hcall x, hc] using! (show (1-ε)*p/2 ≤ 1 by linarith)
  | grover f A =>
    have hf : f = initialFrame N := hroot
    subst f
    obtain ⟨_, _, _, _, _, hcall⟩ := hvalid
    have hc : frameHasCollision k x (initialFrame N) := ⟨hunique.choose,
      hunique.choose_spec.1⟩
    exact le_trans hhalf (le_trans (by linarith : (1 : ℝ)/2 ≤ 1-1/(N : ℝ))
      ((hcall x).1 hc))
  | walk f memory A plan children =>
    have hf : f = initialFrame N := hroot
    have hpcall : p ≤ frameCallProbability A.actual f x := hp.1 x (hf ▸ hunique)
    exact le_trans hlo (le_trans hpcall
      (algorithm3Tree_first_call x f memory A plan children))

theorem isolationSuccess_mean {R : ℕ} (hR : 0 < R)
    (collision unique : Fin R → Prop) (funique : ∀ s, unique s → collision s)
    (success : Fin R → ℝ) (hs0 : ∀ s, 0 ≤ success s)
    (α p δ : ℝ) (hα : 0 ≤ α) (hp : 2*α ≤ p)
    (hcoll : ∀ s, collision s → α ≤ success s)
    (hunique : ∀ s, unique s → p ≤ success s)
    (hisolate : eventProbability (fun s => ¬collision s) ≤ eventProbability unique+δ) :
    α*(1-δ) ≤ (∑ s, success s)/(R : ℝ) := by
  classical
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hpart : (∑ s : Fin R, if collision s then (1 : ℝ) else 0)/(R : ℝ) =
      1-eventProbability (fun s => ¬collision s) := by
    unfold eventProbability
    have hcount : ((Finset.univ.filter collision).card : ℝ)+
        ((Finset.univ.filter (fun s => ¬collision s)).card : ℝ) = R := by
      have h :=
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin R))) collision
      rw [Finset.card_univ,Fintype.card_fin] at h
      exact_mod_cast h
    rw [Finset.sum_boole]
    apply (div_eq_iff hr.ne').mpr
    field_simp
    convert! (eq_sub_iff_add_eq.mpr hcount) using 1
    congr
  have huniqueprob : (∑ s : Fin R, if unique s then (1 : ℝ) else 0)/(R : ℝ) =
      eventProbability unique := by simp [eventProbability]
  have hsumlow : (∑ s : Fin R,
      (α*(if collision s then 1 else 0)+(p-α)*(if unique s then 1 else 0))) ≤
      ∑ s, success s := by
    apply Finset.sum_le_sum
    intro s _
    by_cases hu : unique s
    · simp [hu, funique s hu]
      exact hunique s hu
    · by_cases hc : collision s
      · simpa [hu,hc] using! hcoll s hc
      · simpa [hu,hc] using! hs0 s
  have havglow := div_le_div_of_nonneg_right hsumlow hr.le
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at havglow
  rw [add_div, mul_div_assoc, mul_div_assoc, hpart, huniqueprob] at havglow
  have hup0 : 0 ≤ eventProbability unique :=
    div_nonneg (Nat.cast_nonneg _) hr.le
  nlinarith [mul_nonneg hα (sub_nonneg.mpr hisolate)]

def algorithm3Depth {N M k : ℕ} [NeZero M] : Algorithm3Tree N M k → ℕ
  | .readAll _ _ | .grover _ _ => 0
  | .walk _ _ _ plan children => 1+maximumFinite plan.seeds
      (fun s => algorithm3Depth (children s))

def algorithm3Isolates {N M k : ℕ} [NeZero M] (x : Fin N → ZMod M) (δ : ℝ) :
    Algorithm3Tree N M k → Prop
  | .readAll _ _ | .grover _ _ => True
  | .walk f _ _ _plan children =>
      (frameHasCollision k x f →
        eventProbability (fun s => ¬frameHasCollision k x (treeFrame (children s))) ≤
        eventProbability (fun s => ∃! S, S ⊆ frameSet (treeFrame (children s)) ∧
          IsCollision k x S)+δ) ∧ ∀ s, algorithm3Isolates x δ (children s)

theorem algorithm3Tree_frame_unique {N M k r : ℕ} [NeZero M]
    (hN : 2 ≤ N) (C p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P)
    (hp : uniqueCallProbability p P) (x : Fin N → ZMod M)
    (hx : ∃! S, S ⊆ frameSet (treeFrame P) ∧ IsCollision k x S) :
    p*(1-1/(N : ℝ)) ≤ treeProbability x P := by
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnu : 0 ≤ 1-1/(N : ℝ) := by
    have := (div_le_one hnpos).mpr hnr
    linarith
  have hup : p*(1-1/(N : ℝ)) ≤ p := by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnpos.le]
  have hterminal : p*(1-1/(N : ℝ)) ≤ 1-1/(N : ℝ) := by nlinarith
  cases P with
  | readAll f A =>
    obtain ⟨_,_,_,_,hcall⟩ := hvalid
    have hc : frameHasCollision k x f := ⟨hx.choose,hx.choose_spec.1⟩
    simp only [treeProbability, hcall x, if_pos hc]
    exact le_trans hup hp1
  | grover f A =>
    obtain ⟨_,_,_,_,_,hcall⟩ := hvalid
    exact le_trans hterminal ((hcall x).1 ⟨hx.choose,hx.choose_spec.1⟩)
  | walk f memory A plan children =>
    exact le_trans hup (le_trans (hp.1 x hx)
      (algorithm3Tree_first_call x f memory A plan children))

theorem algorithm3Tree_isolation_success {N M k r : ℕ} [NeZero M]
    (hN : 2 ≤ N) (C p δ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P)
    (hp : uniqueCallProbability p P) (x : Fin N → ZMod M)
    (hisolation : algorithm3Isolates x δ P) (hx : frameHasCollision k x (treeFrame P)) :
    p*(1-1/(N : ℝ))/2*(1-(algorithm3Depth P : ℝ)*δ) ≤ treeProbability x P := by
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hnu : 0 ≤ 1-1/(N : ℝ) := by
    have := (div_le_one hnpos).mpr hnr
    linarith
  let u := p*(1-1/(N : ℝ))
  have hu0 : 0 ≤ u := mul_nonneg hp0 hnu
  have hu1 : u ≤ 1-1/(N : ℝ) := by dsimp [u]; nlinarith
  induction P with
  | readAll f A =>
    obtain ⟨_,_,_,_,hcall⟩ := hvalid
    change frameHasCollision k x f at hx
    simp only [treeProbability,algorithm3Depth,hcall x,if_pos hx,Nat.cast_zero,zero_mul,
      sub_zero,mul_one]
    have hu : u ≤ 1 := by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnpos.le]
    change u/2 ≤ 1
    linarith
  | grover f A =>
    obtain ⟨_,_,_,_,_,hcall⟩ := hvalid
    simp only [algorithm3Depth,Nat.cast_zero,zero_mul,sub_zero,mul_one]
    change u/2 ≤ frameCallProbability A f x
    exact le_trans (by linarith : u/2 ≤ 1-1/(N : ℝ)) ((hcall x).1 hx)
  | walk f memory A plan children ih =>
    obtain ⟨_,_,_,_,_,_,hchildren⟩ := hvalid
    let D := maximumFinite plan.seeds (fun s => algorithm3Depth (children s))
    let α := u/2*(1-(D : ℝ)*δ)
    have hdepth (s : Fin plan.seeds) : algorithm3Depth (children s) ≤ D := by
      dsimp [D,maximumFinite]
      exact Finset.le_sup (f := fun s => algorithm3Depth (children s)) (Finset.mem_univ s)
    have hαu : 2*α ≤ u := by
      dsimp [α]
      nlinarith [mul_nonneg (Nat.cast_nonneg D) hδ]
    by_cases hα : 0 ≤ α
    · have hmean := isolationSuccess_mean plan.positiveSeeds
        (fun s => frameHasCollision k x (treeFrame (children s)))
        (fun s => ∃! S, S ⊆ frameSet (treeFrame (children s)) ∧ IsCollision k x S)
        (fun s hs => ⟨hs.choose,hs.choose_spec.1⟩)
        (fun s => treeProbability x (children s))
        (fun s => (algorithm3Tree_probability_bounds x (children s)).1)
        α u δ hα hαu
        (fun s hs => le_trans (by
          have hd : (algorithm3Depth (children s) : ℝ) ≤ D := by exact_mod_cast hdepth s
          dsimp [α]
          nlinarith [mul_nonneg hu0 (mul_nonneg hδ (sub_nonneg.mpr hd))])
          (ih s (hchildren s).2 (hp.2 s) (hisolation.2 s) hs))
        (fun s hs => algorithm3Tree_frame_unique hN C p hp0 hp1 (children s)
          (hchildren s).2 (hp.2 s) x hs)
        (hisolation.1 hx)
      have hfirst := algorithm3Tree_children_mean x f memory A plan children
      change u/2*(1-(1+D : ℕ)*δ) ≤ _
      have hαupper : α ≤ u/2 := by nlinarith
      have haloss : u/2*(1-(1+D : ℕ)*δ) ≤ α*(1-δ) := by
        push_cast
        dsimp [α] at *
        nlinarith [mul_nonneg hδ (sub_nonneg.mpr hαupper)]
      exact le_trans haloss (le_trans hmean hfirst)
    · have hneg : α < 0 := lt_of_not_ge hα
      have htarget : u/2*(1-(1+D : ℕ)*δ) ≤ 0 := by
        push_cast
        dsimp [α] at hneg
        nlinarith [mul_nonneg hu0 hδ]
      exact le_trans htarget
          (algorithm3Tree_probability_bounds x (.walk f memory A plan children)).1

theorem algorithm3Depth_le_frameSize {N M k r : ℕ} [NeZero M]
    (C : ℝ) (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P) :
    algorithm3Depth P ≤ (treeFrame P).size := by
  induction P with
  | readAll f A => simp [algorithm3Depth,treeFrame]
  | grover f A => simp [algorithm3Depth,treeFrame]
  | walk f memory A plan children ih =>
    obtain ⟨_,_,_,_,_,_,hchildren⟩ := hvalid
    have hsup : maximumFinite plan.seeds (fun s => algorithm3Depth (children s)) ≤ plan.kept := by
      apply Finset.sup_le
      intro s _
      have h := ih s (hchildren s).2
      rw [(hchildren s).1] at h
      exact h
    change 1+maximumFinite plan.seeds (fun s => algorithm3Depth (children s)) ≤ f.size
    exact le_trans (Nat.add_le_add_left hsup 1) (by
      have hdec := plan.decreases
      omega)

def algorithm3Shrinks {N M k : ℕ} [NeZero M] (a : ℝ) : Algorithm3Tree N M k → Prop
  | .readAll _ _ | .grover _ _ => True
  | .walk f _ _ _plan children => ∀ s,
      (treeFrame (children s)).size ≤ a*f.size ∧ algorithm3Shrinks a (children s)

private theorem nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)

theorem algorithm3Depth_log_bound {N M k r : ℕ} [NeZero M]
    (C a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (P : Algorithm3Tree N M k)
    (hvalid : algorithm3Valid r C P) (hshrink : algorithm3Shrinks a P) :
    ((algorithm3Depth P-1 : ℕ) : ℝ)*(-Real.log a) ≤ Real.log ((treeFrame P).size : ℝ) := by
  have hloga : Real.log a < 0 := Real.log_neg ha0 ha1
  induction P with
  | readAll f A => simpa [algorithm3Depth,treeFrame] using! nat_log_nonneg f.size
  | grover f A => simpa [algorithm3Depth,treeFrame] using! nat_log_nonneg f.size
  | walk f memory A plan children ih =>
    obtain ⟨_,hfsize,_,_,_,_,hchildren⟩ := hvalid
    have hfpos : (0 : ℝ) < f.size := by exact_mod_cast (show 0 < f.size by omega)
    let D := maximumFinite plan.seeds (fun s => algorithm3Depth (children s))
    change ((1+D-1 : ℕ) : ℝ)*(-Real.log a) ≤ Real.log (f.size : ℝ)
    rw [Nat.add_sub_cancel_left]
    by_cases hD : D = 0
    · simp only [hD,Nat.cast_zero,zero_mul]
      exact nat_log_nonneg f.size
    · have hnonempty : (Finset.univ : Finset (Fin plan.seeds)).Nonempty :=
        ⟨⟨0,plan.positiveSeeds⟩,Finset.mem_univ _⟩
      obtain ⟨s,_,hs⟩ := Finset.exists_mem_eq_sup Finset.univ hnonempty
        (fun s => algorithm3Depth (children s))
      have heq : algorithm3Depth (children s) = D := hs.symm
      have hchildpos : 0 < (treeFrame (children s)).size := by
        have hbound := algorithm3Depth_le_frameSize C (children s) (hchildren s).2
        rw [heq] at hbound
        exact lt_of_lt_of_le (Nat.pos_of_ne_zero hD) hbound
      have hchildreal : (0 : ℝ) < (treeFrame (children s)).size := by exact_mod_cast hchildpos
      have hlogshrink := Real.log_le_log hchildreal (hshrink s).1
      rw [Real.log_mul ha0.ne' hfpos.ne'] at hlogshrink
      have hih := ih s (hchildren s).2 (hshrink s).2
      rw [heq] at hih
      have hpred : ((D-1 : ℕ) : ℝ) = (D : ℝ)-1 := by
        simpa using!
            (Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hD) : ((D-1 : ℕ) : ℝ) = (D : ℝ)-(1 : ℕ))
      rw [hpred] at hih
      linarith

theorem algorithm3Shrinks_valid {N M k r : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hN : (8*k*k : ℝ) ≤ Real.sqrt N)
    (C : ℝ) (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P) :
    algorithm3Shrinks (1-1/(10*(k : ℝ))) P := by
  induction P with
  | readAll f A => trivial
  | grover f A => trivial
  | walk f memory A plan children ih =>
    obtain ⟨_,_,hfsize,_,_,_,hchildren⟩ := hvalid
    have hn : 8*k*k ≤ f.size := by
      have hreal : (8*k*k : ℝ) ≤ f.size := le_trans hN hfsize.le
      exact_mod_cast hreal
    have hratio := algorithm3_prefix_ratio k f.size plan.q hk hn plan.near
    rw [← plan.kept_eq] at hratio
    intro s
    constructor
    · rw [(hchildren s).1]
      exact hratio
    · exact ih s (hchildren s).2

theorem algorithm3Depth_source_log_bound {N M k r : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hN : (8*k*k : ℝ) ≤ Real.sqrt N)
    (C : ℝ) (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P) :
    (algorithm3Depth P : ℝ) ≤ 1+10*(k : ℝ)*Real.log ((treeFrame P).size : ℝ) := by
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have htenpos : (0 : ℝ) < 10*k := by linarith
  let a : ℝ := 1-1/(10*(k : ℝ))
  have ha0 : 0 < a := by
    have hdiv : 1/(10*(k : ℝ)) < 1 := (div_lt_one htenpos).mpr (by linarith)
    dsimp [a]
    linarith
  have ha1 : a < 1 := by
    have hdiv : 0 < 1/(10*(k : ℝ)) := div_pos (by norm_num) htenpos
    dsimp [a]
    linarith
  have hlog := algorithm3Depth_log_bound C a ha0 ha1 P hvalid
    (algorithm3Shrinks_valid hk hN C P hvalid)
  have hloga := Real.log_le_sub_one_of_pos ha0
  have hbeta : 1/(10*(k : ℝ)) ≤ -Real.log a := by dsimp [a] at hloga; linarith
  have hprod := mul_le_mul_of_nonneg_left hbeta
    (Nat.cast_nonneg (algorithm3Depth P-1))
  have hsmall := le_trans hprod hlog
  have hpred : ((algorithm3Depth P-1 : ℕ) : ℝ) ≤
      Real.log ((treeFrame P).size : ℝ)*(10*(k : ℝ)) := by
    apply (div_le_iff₀ htenpos).mp
    simpa only [div_eq_mul_inv,one_mul] using! hsmall
  by_cases hdepth : algorithm3Depth P = 0
  · simp only [hdepth,Nat.cast_zero]
    nlinarith [nat_log_nonneg (treeFrame P).size]
  · have hcast : ((algorithm3Depth P-1 : ℕ) : ℝ) =
        (algorithm3Depth P : ℝ)-1 := by
      simpa using! (Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hdepth) :
        ((algorithm3Depth P-1 : ℕ) : ℝ) = (algorithm3Depth P : ℝ)-(1 : ℕ))
    rw [hcast] at hpred
    linarith

theorem algorithm3Tree_epsilon_success {N M k r : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hN : 2 ≤ N) (hscale : (8*k*k : ℝ) ≤ Real.sqrt N)
    (ε C p : ℝ) (hε : 0 < ε) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hterminal : 1/(N : ℝ) ≤ ε/2) (P : Algorithm3Tree N M k)
    (hroot : treeFrame P = initialFrame N) (hvalid : algorithm3Valid r C P)
    (hp : uniqueCallProbability p P) (x : Fin N → ZMod M)
    (hisolation : algorithm3Isolates x (ε/(20*(1+(k : ℝ)*Real.log N))) P)
    (hx : HasCollision k x) : (1-ε)*p/2 ≤ treeProbability x P := by
  have hprob0 := (algorithm3Tree_probability_bounds x P).1
  by_cases heps1 : 1 ≤ ε
  · have hleft : (1-ε)*p/2 ≤ 0 := by nlinarith
    exact le_trans hleft hprob0
  · have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 ≤ Real.log (N : ℝ) := nat_log_nonneg N
    let L := (k : ℝ)*Real.log N
    let δ := ε/(20*(1+L))
    have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) hlogN
    have hden : 0 < 20*(1+L) := by linarith
    have hδ : 0 ≤ δ := div_nonneg hε.le hden.le
    have hd := algorithm3Depth_source_log_bound hk hscale C P hvalid
    rw [hroot] at hd
    change (algorithm3Depth P : ℝ) ≤ 1+10*(k : ℝ)*Real.log N at hd
    have hdL : (algorithm3Depth P : ℝ) ≤ 1+10*L := by dsimp [L]; nlinarith only [hd]
    have hDδ : (algorithm3Depth P : ℝ)*δ ≤ ε/2 := by
      have hid : (algorithm3Depth P : ℝ)*δ =
          ((algorithm3Depth P : ℝ)*ε)/(20*(1+L)) := by dsimp [δ]; ring
      rw [hid]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hdL)]
    have hDδ0 : 0 ≤ (algorithm3Depth P : ℝ)*δ :=
      mul_nonneg (Nat.cast_nonneg _) hδ
    have hnu0 : 0 ≤ 1/(N : ℝ) := div_nonneg (by norm_num) hnpos.le
    have hfactor : 1-ε ≤ (1-1/(N : ℝ))*(1-(algorithm3Depth P : ℝ)*δ) := by
      nlinarith [mul_nonneg hnu0 hDδ0]
    have hframeCollision : frameHasCollision k x (treeFrame P) := by
      rw [hroot]
      obtain ⟨S,hS⟩ := hx
      exact ⟨S,by simp [frameSet_initial],hS⟩
    have hactual := algorithm3Tree_isolation_success hN C p δ hp0 hp1 hδ P hvalid hp x
      hisolation hframeCollision
    calc
      (1-ε)*p/2 = (p/2)*(1-ε) := by ring
      _ ≤ (p/2)*((1-1/(N : ℝ))*(1-(algorithm3Depth P : ℝ)*δ)) :=
        mul_le_mul_of_nonneg_left hfactor (div_nonneg hp0 (by norm_num))
      _ = p*(1-1/(N : ℝ))/2*(1-(algorithm3Depth P : ℝ)*δ) := by ring
      _ ≤ _ := hactual

def algorithm3ExtendedOrigin {N q : ℕ} (f : Algorithm3Frame N) (_h : f.size ≤ q)
    (j : Fin q) : Option (Fin N) :=
  if hj : j.val < f.size then f.origin ⟨j.val,hj⟩ else none

def algorithm3ExtendedInput {N M q : ℕ} (f : Algorithm3Frame N) (h : f.size ≤ q)
    (x : Fin N → ZMod M) (j : Fin q) : ZMod (M+q+1) :=
  match algorithm3ExtendedOrigin f h j with
  | some i => (x i).val
  | none => ((M+j.val : ℕ) : ZMod (M+q+1))

theorem algorithm3ExtendedOrigin_injective {N q : ℕ} (f : Algorithm3Frame N)
    (h : f.size ≤ q) (hf : frameWellFormed f) {j l : Fin q} {v : Fin N}
    (hj : algorithm3ExtendedOrigin f h j = some v)
    (hl : algorithm3ExtendedOrigin f h l = some v) : j = l := by
  have hjb : j.val < f.size := by
    by_contra hn
    simp [algorithm3ExtendedOrigin,hn] at hj
  have hlb : l.val < f.size := by
    by_contra hn
    simp [algorithm3ExtendedOrigin,hn] at hl
  have hj' : f.origin ⟨j.val,hjb⟩ = some v := by simpa [algorithm3ExtendedOrigin,hjb] using! hj
  have hl' : f.origin ⟨l.val,hlb⟩ = some v := by simpa [algorithm3ExtendedOrigin,hlb] using! hl
  have he := hf ⟨j.val,hjb⟩ ⟨l.val,hlb⟩ v hj' hl'
  apply Fin.ext
  exact congrArg (fun z : Fin f.size => z.val) he

theorem algorithm3ExtendedInput_val {N M q : ℕ} [NeZero M] (f : Algorithm3Frame N)
    (h : f.size ≤ q) (x : Fin N → ZMod M) (j : Fin q) :
    (algorithm3ExtendedInput f h x j).val =
      match algorithm3ExtendedOrigin f h j with
      | some i => (x i).val
      | none => M+j.val := by
  letI : NeZero (M+q+1) := ⟨by omega⟩
  cases hj : algorithm3ExtendedOrigin f h j with
  | none =>
    simp only [algorithm3ExtendedInput, hj, ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have ht := j.isLt
    omega
  | some i =>
    simp only [algorithm3ExtendedInput, hj, ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have ht := (x i).val_lt
    omega

theorem algorithm3ExtendedInput_dummy_eq {N M q : ℕ} [NeZero M] (f : Algorithm3Frame N)
    (h : f.size ≤ q) (x : Fin N → ZMod M) (j l : Fin q)
    (hj : algorithm3ExtendedOrigin f h j = none)
    (he : algorithm3ExtendedInput f h x j = algorithm3ExtendedInput f h x l) : j = l := by
  have hv := congrArg ZMod.val he
  rw [algorithm3ExtendedInput_val, algorithm3ExtendedInput_val, hj] at hv
  cases hl : algorithm3ExtendedOrigin f h l with
  | none =>
    rw [hl] at hv
    (try dsimp only at hv)
    exact Fin.ext (Nat.add_left_cancel hv)
  | some i =>
    rw [hl] at hv
    (try dsimp only at hv)
    have ht := (x i).val_lt
    have hle : M ≤ (x i).val := by rw [← hv]; exact Nat.le_add_right _ _
    exact False.elim (Nat.not_le_of_gt ht hle)

theorem algorithm3ExtendedInput_real_eq {N M q : ℕ} [NeZero M] (f : Algorithm3Frame N)
    (h : f.size ≤ q) (x : Fin N → ZMod M) (j l : Fin q) (a b : Fin N)
    (hj : algorithm3ExtendedOrigin f h j = some a)
    (hl : algorithm3ExtendedOrigin f h l = some b) :
    algorithm3ExtendedInput f h x j = algorithm3ExtendedInput f h x l ↔ x a = x b := by
  constructor
  · intro he
    have hv := congrArg ZMod.val he
    rw [algorithm3ExtendedInput_val,algorithm3ExtendedInput_val,hj,hl] at hv
    (try dsimp only at hv)
    rw [← ZMod.natCast_zmod_val (x a),← ZMod.natCast_zmod_val (x b),hv]
  · intro he
    simp only [algorithm3ExtendedInput,hj,hl,he]

theorem algorithm3ExtendedInput_collision_real {N M q : ℕ} [NeZero M]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (x : Fin N → ZMod M)
    (k : ℕ) (hk : 2 ≤ k) (S : Finset (Fin q))
    (hS : IsCollision k (algorithm3ExtendedInput f h x) S) :
    ∀ j ∈ S, ∃ v, algorithm3ExtendedOrigin f h j = some v := by
  intro j hj
  obtain ⟨hcard,val,hval⟩ := hS
  cases ho : algorithm3ExtendedOrigin f h j with
  | some v => exact ⟨v,rfl⟩
  | none =>
    have hs : 1 < S.card := by omega
    obtain ⟨l,hl,hne⟩ := S.exists_mem_ne hs j
    have heq := algorithm3ExtendedInput_dummy_eq f h x j l ho ((hval j hj).trans (hval l hl).symm)
    exact False.elim (hne heq.symm)

def algorithm3OriginSet {N q : ℕ} (f : Algorithm3Frame N) (h : f.size ≤ q)
    (U : Finset (Fin q)) : Finset (Fin N) :=
  Finset.univ.filter (fun v => ∃ j ∈ U, algorithm3ExtendedOrigin f h j = some v)

def algorithm3Position {N q : ℕ} [NeZero q] (f : Algorithm3Frame N) (h : f.size ≤ q)
    (U : Finset (Fin q)) (v : Fin N) : Fin q :=
  if hv : v ∈ algorithm3OriginSet f h U then
    Classical.choose ((Finset.mem_filter.mp hv).2) else 0

def algorithm3Address {N q : ℕ} [NeZero N] (f : Algorithm3Frame N) (h : f.size ≤ q)
    (j : Fin q) : Fin N := (algorithm3ExtendedOrigin f h j).getD 0

theorem algorithm3Position_spec {N q : ℕ} [NeZero q] (f : Algorithm3Frame N)
    (h : f.size ≤ q) (U : Finset (Fin q)) (v : Fin N)
    (hv : v ∈ algorithm3OriginSet f h U) :
    algorithm3Position f h U v ∈ U ∧
      algorithm3ExtendedOrigin f h (algorithm3Position f h U v) = some v := by
  simp only [algorithm3Position,dif_pos hv]
  exact Classical.choose_spec ((Finset.mem_filter.mp hv).2)

theorem algorithm3Address_some {N q : ℕ} [NeZero N] (f : Algorithm3Frame N)
    (h : f.size ≤ q) (j : Fin q) (v : Fin N)
    (hv : algorithm3ExtendedOrigin f h j = some v) : algorithm3Address f h j = v := by
  simp [algorithm3Address,hv]

theorem algorithm3Address_position {N q : ℕ} [NeZero N] [NeZero q]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (U : Finset (Fin q)) (v : Fin N)
    (hv : v ∈ algorithm3OriginSet f h U) :
    algorithm3Address f h (algorithm3Position f h U v) = v :=
  algorithm3Address_some f h _ v (algorithm3Position_spec f h U v hv).2

theorem algorithm3Position_address {N q : ℕ} [NeZero N] [NeZero q]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (hf : frameWellFormed f)
    (U : Finset (Fin q)) (j : Fin q) (hj : j ∈ U)
    (hreal : ∃ v, algorithm3ExtendedOrigin f h j = some v) :
    algorithm3Position f h U (algorithm3Address f h j) = j := by
  obtain ⟨v,hv⟩ := hreal
  rw [algorithm3Address_some f h j v hv]
  have ho : v ∈ algorithm3OriginSet f h U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,hv⟩
  exact algorithm3ExtendedOrigin_injective f h hf (algorithm3Position_spec f h U v ho).2 hv

theorem algorithm3AddressPosition_image {N q : ℕ} [NeZero N] [NeZero q]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (U : Finset (Fin q))
    (S : Finset (Fin N)) (hS : S ⊆ algorithm3OriginSet f h U) :
    (S.image (algorithm3Position f h U)).image (algorithm3Address f h) = S := by
  rw [Finset.image_image]
  calc
    _ = S.image id := Finset.image_congr (fun v hv => algorithm3Address_position f h U v (hS hv))
    _ = _ := Finset.image_id

theorem algorithm3PositionAddress_image {N M q : ℕ} [NeZero N] [NeZero q] [NeZero M]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (hf : frameWellFormed f)
    (U : Finset (Fin q)) (x : Fin N → ZMod M) (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (Fin q)) (hS : CollisionIn k (algorithm3ExtendedInput f h x) U S) :
    (S.image (algorithm3Address f h)).image (algorithm3Position f h U) = S := by
  rw [Finset.image_image]
  calc
    _ = S.image id := Finset.image_congr (fun j hj =>
      algorithm3Position_address f h hf U j (hS.1 hj)
        (algorithm3ExtendedInput_collision_real f h x k hk S hS.2 j hj))
    _ = _ := Finset.image_id

theorem algorithm3LiftCollision {N M q : ℕ} [NeZero q]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (U : Finset (Fin q))
    (x : Fin N → ZMod M) (k : ℕ) (S : Finset (Fin N))
    (hS : CollisionIn k x (algorithm3OriginSet f h U) S) :
    CollisionIn k (algorithm3ExtendedInput f h x) U (S.image (algorithm3Position f h U)) := by
  have hi : Set.InjOn (algorithm3Position f h U) (S : Set (Fin N)) := by
    intro v hv w hw he
    have hv' := (algorithm3Position_spec f h U v (hS.1 hv)).2
    have hw' := (algorithm3Position_spec f h U w (hS.1 hw)).2
    exact Option.some.inj (hv'.symm.trans ((congrArg (algorithm3ExtendedOrigin f h) he).trans hw'))
  constructor
  · intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    exact (algorithm3Position_spec f h U v (hS.1 hv)).1
  · obtain ⟨hcard,val,hval⟩ := hS.2
    refine ⟨(Finset.card_image_iff.mpr hi).trans hcard, ((val.val : ℕ) : ZMod (M+q+1)), ?_⟩
    intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    simp only [algorithm3ExtendedInput, (algorithm3Position_spec f h U v (hS.1 hv)).2,
      hval v hv]

theorem algorithm3DropCollision {N M q : ℕ} [NeZero N] [NeZero M]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (hf : frameWellFormed f)
    (U : Finset (Fin q)) (x : Fin N → ZMod M) (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (Fin q)) (hS : CollisionIn k (algorithm3ExtendedInput f h x) U S) :
    CollisionIn k x (algorithm3OriginSet f h U) (S.image (algorithm3Address f h)) := by
  have hreal := algorithm3ExtendedInput_collision_real f h x k hk S hS.2
  have hi : Set.InjOn (algorithm3Address f h) (S : Set (Fin q)) := by
    intro j hj l hl he
    obtain ⟨v,hv⟩ := hreal j hj
    obtain ⟨w,hw⟩ := hreal l hl
    rw [algorithm3Address_some f h j v hv,algorithm3Address_some f h l w hw] at he
    subst w
    exact algorithm3ExtendedOrigin_injective f h hf hv hw
  constructor
  · intro v hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw⟩ := hreal j hj
    rw [algorithm3Address_some f h j w hw]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hS.1 hj,hw⟩
  · obtain ⟨hcard,val,hval⟩ := hS.2
    have hnon : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j,hj⟩ := hnon
    obtain ⟨v,hv⟩ := hreal j hj
    refine ⟨(Finset.card_image_iff.mpr hi).trans hcard,x v,?_⟩
    intro w hw
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨u,hu⟩ := hreal l hl
    rw [algorithm3Address_some f h l u hu]
    exact (algorithm3ExtendedInput_real_eq f h x l j u v hu hv).mp
      ((hval l hl).trans (hval j hj).symm)

theorem algorithm3Origin_collision_exists_iff {N M q : ℕ} [NeZero q] [NeZero M]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (hf : frameWellFormed f)
    (U : Finset (Fin q)) (x : Fin N → ZMod M) (k : ℕ) (hk : 2 ≤ k) :
    (∃ S,CollisionIn k x (algorithm3OriginSet f h U) S) ↔
      ∃ S,CollisionIn k (algorithm3ExtendedInput f h x) U S := by
  constructor
  · rintro ⟨S,hS⟩
    exact ⟨_,algorithm3LiftCollision f h U x k S hS⟩
  · rintro ⟨S,hS⟩
    have hnon : S.Nonempty := Finset.card_pos.mp (by have hs := hS.2.1; omega)
    obtain ⟨j,hj⟩ := hnon
    obtain ⟨v,_⟩ := algorithm3ExtendedInput_collision_real f h x k hk S hS.2 j hj
    letI : NeZero N := ⟨by have ht := v.isLt; omega⟩
    exact ⟨_,algorithm3DropCollision f h hf U x k hk S hS⟩

theorem algorithm3Origin_collision_unique_iff {N M q : ℕ} [NeZero q] [NeZero M]
    (f : Algorithm3Frame N) (h : f.size ≤ q) (hf : frameWellFormed f)
    (U : Finset (Fin q)) (x : Fin N → ZMod M) (k : ℕ) (hk : 2 ≤ k) :
    (∃! S,CollisionIn k x (algorithm3OriginSet f h U) S) ↔
      ∃! S,CollisionIn k (algorithm3ExtendedInput f h x) U S := by
  constructor
  · rintro ⟨S,hS,hunique⟩
    have hnon : S.Nonempty := Finset.card_pos.mp (by have hs := hS.2.1; omega)
    obtain ⟨v,_⟩ := hnon
    letI : NeZero N := ⟨by have ht := v.isLt; omega⟩
    refine ⟨S.image (algorithm3Position f h U),algorithm3LiftCollision f h U x k S hS,?_⟩
    intro B hB
    have heq :=
        hunique (B.image (algorithm3Address f h)) (algorithm3DropCollision f h hf U x k hk B hB)
    calc
      B = (B.image (algorithm3Address f h)).image (algorithm3Position f h U) :=
        (algorithm3PositionAddress_image f h hf U x k hk B hB).symm
      _ = _ := congrArg (fun A => A.image (algorithm3Position f h U)) heq
  · rintro ⟨B,hB,hunique⟩
    have hnon : B.Nonempty := Finset.card_pos.mp (by have hs := hB.2.1; omega)
    obtain ⟨j,hj⟩ := hnon
    obtain ⟨v,_⟩ := algorithm3ExtendedInput_collision_real f h x k hk B hB.2 j hj
    letI : NeZero N := ⟨by have ht := v.isLt; omega⟩
    refine ⟨B.image (algorithm3Address f h),algorithm3DropCollision f h hf U x k hk B hB,?_⟩
    intro S hS
    have heq :=
        hunique (S.image (algorithm3Position f h U)) (algorithm3LiftCollision f h U x k S hS)
    calc
      S = (S.image (algorithm3Position f h U)).image (algorithm3Address f h) :=
        (algorithm3AddressPosition_image f h U S hS.1).symm
      _ = _ := congrArg (fun A => A.image (algorithm3Address f h)) heq

def algorithm3ExtendedDomain {N q : ℕ} (f : Algorithm3Frame N) : Finset (Fin q) :=
  Finset.univ.filter (fun j => j.val < f.size)

theorem algorithm3OriginSet_initial {N q : ℕ} (f : Algorithm3Frame N) (h : f.size ≤ q) :
    algorithm3OriginSet f h (algorithm3ExtendedDomain f) = frameSet f := by
  ext v
  simp only [algorithm3OriginSet,frameSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,hori⟩
    have hjb : j.val < f.size := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val,hjb⟩,?_⟩
    simpa [algorithm3ExtendedOrigin,hjb] using! hori
  · rintro ⟨j,hj⟩
    refine ⟨Fin.castLE h j,?_,?_⟩
    · simp [algorithm3ExtendedDomain,j.isLt]
    · simpa [algorithm3ExtendedOrigin,j.isLt] using! hj

theorem algorithm3OriginSet_nextFrame {k N : ℕ} {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (s : Fin P.seeds) :
    algorithm3OriginSet f P.enough (retained k (algorithm3ExtendedDomain f) P.permutation s) =
      frameSet (nextFrame P s) := by
  have hkeep : Nat.ceil ((2*k : ℝ)/(2*k+1)*P.q) = P.kept := P.kept_eq.symm
  ext v
  rw [mem_frameSet_nextFrame]
  simp only [algorithm3OriginSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,hori⟩
    obtain ⟨hTU,hret⟩ := Finset.mem_filter.mp hj
    have hjb : j.val < f.size := (Finset.mem_filter.mp hTU).2
    refine ⟨⟨j.val,hjb⟩,?_,?_⟩
    · simpa [algorithm3ExtendedOrigin,hjb] using! hori
    · have hjcast : Fin.castLE P.enough (⟨j.val,hjb⟩ : Fin f.size) = j := Fin.ext rfl
      rw [hjcast]
      simpa only [hkeep] using! hret
  · rintro ⟨j,hj,hret⟩
    refine ⟨Fin.castLE P.enough j,?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by simp [algorithm3ExtendedDomain,j.isLt],by simpa only [hkeep] using! hret⟩
    · simpa [algorithm3ExtendedOrigin,j.isLt] using! hj

theorem frame_extended_collision_iff {k N M : ℕ} [NeZero M] {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (hk : 2 ≤ k) (hf : frameWellFormed f)
    (x : Fin N → ZMod M) :
    (∃ S,S ⊆ frameSet f ∧ IsCollision k x S) ↔
      ∃ S,CollisionIn k (algorithm3ExtendedInput f P.enough x) (algorithm3ExtendedDomain f) S := by
  letI : NeZero P.q := ⟨by have hd := P.decreases; have he := P.enough; omega⟩
  have hh := algorithm3Origin_collision_exists_iff f P.enough hf (algorithm3ExtendedDomain f) x k hk
  rw [algorithm3OriginSet_initial] at hh
  exact hh

theorem frame_extended_unique_iff {k N M : ℕ} [NeZero M] {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (hk : 2 ≤ k) (hf : frameWellFormed f)
    (x : Fin N → ZMod M) :
    (∃! S,S ⊆ frameSet f ∧ IsCollision k x S) ↔
      ∃! S,CollisionIn k (algorithm3ExtendedInput f P.enough x) (algorithm3ExtendedDomain f) S := by
  letI : NeZero P.q := ⟨by have hd := P.decreases; have he := P.enough; omega⟩
  have hh := algorithm3Origin_collision_unique_iff f P.enough hf (algorithm3ExtendedDomain f) x k hk
  rw [algorithm3OriginSet_initial] at hh
  exact hh

theorem nextFrame_extended_collision_iff {k N M : ℕ} [NeZero M] {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (hk : 2 ≤ k) (hf : frameWellFormed f)
    (x : Fin N → ZMod M) (s : Fin P.seeds) :
    (∃ S,S ⊆ frameSet (nextFrame P s) ∧ IsCollision k x S) ↔
      ∃ S,CollisionIn k (algorithm3ExtendedInput f P.enough x)
        (retained k (algorithm3ExtendedDomain f) P.permutation s) S := by
  letI : NeZero P.q := ⟨by have hd := P.decreases; have he := P.enough; omega⟩
  have hh := algorithm3Origin_collision_exists_iff f P.enough hf
    (retained k (algorithm3ExtendedDomain f) P.permutation s) x k hk
  rw [algorithm3OriginSet_nextFrame] at hh
  exact hh

theorem nextFrame_extended_unique_iff {k N M : ℕ} [NeZero M] {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (hk : 2 ≤ k) (hf : frameWellFormed f)
    (x : Fin N → ZMod M) (s : Fin P.seeds) :
    (∃! S,S ⊆ frameSet (nextFrame P s) ∧ IsCollision k x S) ↔
      ∃! S,CollisionIn k (algorithm3ExtendedInput f P.enough x)
        (retained k (algorithm3ExtendedDomain f) P.permutation s) S := by
  letI : NeZero P.q := ⟨by have hd := P.decreases; have he := P.enough; omega⟩
  have hh := algorithm3Origin_collision_unique_iff f P.enough hf
    (retained k (algorithm3ExtendedDomain f) P.permutation s) x k hk
  rw [algorithm3OriginSet_nextFrame] at hh
  exact hh

theorem algorithm3Tree_isolates_of_step {N M k r : ℕ} [NeZero M]
    (C δ : ℝ) (x : Fin N → ZMod M)
    (hstep : ∀ (f : Algorithm3Frame N) (plan : Algorithm3Plan k N f),
      frameWellFormed f → Real.sqrt N < f.size → f.size ≤ N →
      frameHasCollision k x f →
      eventProbability (fun s => ¬frameHasCollision k x (nextFrame plan s)) ≤
        eventProbability (fun s => ∃! S, S ⊆ frameSet (nextFrame plan s) ∧ IsCollision k x S)+δ)
    (P : Algorithm3Tree N M k) (hvalid : algorithm3Valid r C P)
    (hsize : (treeFrame P).size ≤ N) : algorithm3Isolates x δ P := by
  induction P with
  | readAll f A => trivial
  | grover f A => trivial
  | walk f memory A plan children ih =>
    obtain ⟨hf,_,hlarge,_,_,_,hchildren⟩ := hvalid
    constructor
    · intro hx
      have hs := hstep f plan hf hlarge hsize hx
      have hn : (fun s => ¬frameHasCollision k x (treeFrame (children s))) =
          (fun s => ¬frameHasCollision k x (nextFrame plan s)) := by
        funext s
        rw [(hchildren s).1]
      have hu : (fun s => ∃! S, S ⊆ frameSet (treeFrame (children s)) ∧ IsCollision k x S) =
          (fun s => ∃! S, S ⊆ frameSet (nextFrame plan s) ∧ IsCollision k x S) := by
        funext s
        rw [(hchildren s).1]
      rw [hn,hu]
      exact hs
    · intro s
      apply ih s (hchildren s).2
      rw [(hchildren s).1]
      change plan.kept ≤ N
      exact le_trans plan.decreases.le hsize

theorem algorithm3Isolation_implies_success (hIsolation : Algorithm3IsolationContract) :
    Algorithm3SuccessContract := by
  intro k hk ε hε
  obtain ⟨Niso,hiso⟩ := hIsolation k hk (ε/20) (div_pos hε (by norm_num))
  let N0 := max Niso (max ((8*k*k)^2) (max 2 (Nat.ceil (2/ε))))
  refine ⟨N0,?_⟩
  intro N M r _inst hN _hM _hkr _hrN C p P _hC hp0 hp1 hroot hvalid hp x
  have hNiso : Niso ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hNrest : max ((8*k*k)^2) (max 2 (Nat.ceil (2/ε))) ≤ N :=
    le_trans (Nat.le_max_right _ _) hN
  have hNpow : (8*k*k)^2 ≤ N := le_trans (Nat.le_max_left _ _) hNrest
  have hNmore : max 2 (Nat.ceil (2/ε)) ≤ N := le_trans (Nat.le_max_right _ _) hNrest
  have hN2 : 2 ≤ N := le_trans (Nat.le_max_left _ _) hNmore
  have hNceil : Nat.ceil (2/ε) ≤ N := le_trans (Nat.le_max_right _ _) hNmore
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hscale : (8*k*k : ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg N)).mpr
    exact_mod_cast hNpow
  have hterminal : 1/(N : ℝ) ≤ ε/2 := by
    have hceilReal : 2/ε ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hNceil)
    have hprod := (div_le_iff₀ hε).mp hceilReal
    apply (div_le_iff₀ hNp).mpr
    nlinarith
  let δ := ε/(20*(1+(k : ℝ)*Real.log N))
  have hstep : ∀ (f : Algorithm3Frame N) (plan : Algorithm3Plan k N f),
      frameWellFormed f → Real.sqrt N < f.size → f.size ≤ N →
      frameHasCollision k x f →
      eventProbability (fun s => ¬frameHasCollision k x (nextFrame plan s)) ≤
        eventProbability (fun s => ∃! S, S ⊆ frameSet (nextFrame plan s) ∧ IsCollision k x S)+δ := by
    intro f plan hf hlarge hfN hx
    let T : Finset (Fin plan.q) := algorithm3ExtendedDomain f
    have hT : T.card = f.size := by
      simpa only [T,algorithm3ExtendedDomain,Nat.min_eq_right plan.enough] using!
        (Fin.card_filter_val_lt (n := plan.q) (m := f.size))
    have hxext : ∃ S, CollisionIn k (algorithm3ExtendedInput f plan.enough x) T S :=
      (frame_extended_collision_iff plan hk hf x).mp hx
    have hbound := hiso N plan.q plan.seeds (M+plan.q+1) hNiso plan.positiveSeeds (by omega)
      (algorithm3ExtendedInput f plan.enough x) T plan.permutation
      (by rw [hT]; exact hlarge.le) (by rw [hT]; exact hfN)
      (by rw [hT]; exact plan.enough) (by rw [hT]; exact plan.near)
      plan.independent hxext
    have hnone : (fun s => ¬frameHasCollision k x (nextFrame plan s)) =
        (fun s => ¬∃ S, CollisionIn k (algorithm3ExtendedInput f plan.enough x)
          (retained k T plan.permutation s) S) := by
      funext s
      apply propext
      exact not_congr (nextFrame_extended_collision_iff plan hk hf x s)
    have hunique : (fun s => ∃! S, S ⊆ frameSet (nextFrame plan s) ∧ IsCollision k x S) =
        (fun s => ∃! S, CollisionIn k (algorithm3ExtendedInput f plan.enough x)
          (retained k T plan.permutation s) S) := by
      funext s
      apply propext
      exact nextFrame_extended_unique_iff plan hk hf x s
    rw [hnone,hunique]
    have herror : (ε/20)/(1+(k : ℝ)*Real.log N) = δ := by simp only [δ,div_div]
    rw [herror] at hbound
    exact hbound
  have hsize : (treeFrame P).size ≤ N := by rw [hroot]; exact le_rfl
  have hisolates := algorithm3Tree_isolates_of_step C δ x hstep P hvalid hsize
  constructor
  · exact algorithm3Tree_epsilon_success hk hN2 hscale ε C p hε hp0 hp1 hterminal P hroot
      hvalid hp x hisolates
  · intro hno
    exact algorithm3Tree_no_collision x hno P

theorem algorithm3Success_answer : Algorithm3Success :=
  algorithm3Isolation_implies_success algorithm3Isolation_answer

end Qatlib.Concepts.WalkFind.SearchAlgorithm
