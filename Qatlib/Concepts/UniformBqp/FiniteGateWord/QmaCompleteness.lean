/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Mathlib.Order.Interval.Finset.Fin
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UniformBqp.FiniteGateWord
open Qatlib Matrix
open scoped Classical BigOperators Kronecker
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

abbrev Clock (m : ℕ) := Fin m→Bool

def unary {m : ℕ} (t : Fin (m+1)) : Clock m := fun i => decide (i.val<t.val)

def LegalClock {m : ℕ} (c : Clock m) : Prop :=
  ∀i j : Fin m,i<j → c j=true → c i=true

def violations {m : ℕ} (c : Clock m) : Finset (Fin m×Fin m) :=
  Finset.univ.filter (fun p => p.1<p.2 ∧ c p.1=false ∧ c p.2=true)

theorem violations_zero_iff {m : ℕ} (c : Clock m) : (violations c).card=0 ↔ LegalClock c := by
  rw [Finset.card_eq_zero]
  constructor
  · intro h i j hij hj
    by_contra hi
    have hi0 : c i=false := by cases hc : c i <;> simp_all
    have hp : (i,j)∈violations c := by simp [violations,hij,hi0,hj]
    rw [h] at hp
    simp at hp
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hij,hi,hj⟩ := (Finset.mem_filter.mp hp).2
    have ht := h p.1 p.2 hij hj
    simp only [hi,Bool.false_eq_true] at ht

theorem unary_legal {m : ℕ} (t : Fin (m+1)) : LegalClock (unary t) := by
  intro i j hij hj
  have hjt : j.val<t.val := of_decide_eq_true hj
  exact decide_eq_true (lt_trans hij hjt)

theorem unary_injective (m : ℕ) : Function.Injective (@unary m) := by
  intro t s h
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hts | hst
  · have ht : t.val < m := by omega
    have hh := congrFun h ⟨t.val,ht⟩
    simp [unary,hts] at hh
  · have hs : s.val < m := by omega
    have hh := congrFun h ⟨s.val,hs⟩
    simp [unary,hst] at hh

def ones {m : ℕ} (c : Clock m) : Finset (Fin m) := Finset.univ.filter (fun i => c i=true)

def decode {m : ℕ} (c : Clock m) : Fin (m+1) :=
  ⟨(ones c).card,Nat.lt_succ_of_le ((Finset.card_le_card (Finset.subset_univ _)).trans_eq
    (Fintype.card_fin m))⟩

theorem unary_decode {m : ℕ} (c : Clock m) (h : LegalClock c) : unary (decode c)=c := by
  funext i
  cases hc : c i with
  | false =>
      have hs : ones c⊆Finset.Iio i := by
        intro j hj
        have hj1 := (Finset.mem_filter.mp hj).2
        apply Finset.mem_Iio.mpr
        by_contra hjlt
        have hij : i≤j := le_of_not_gt hjlt
        rcases lt_or_eq_of_le hij with hij | hij
        · have hi1 := h i j hij hj1
          simp [hc] at hi1
        · subst j
          simp [hc] at hj1
      have hn : (ones c).card ≤ i.val := by simpa only [Fin.card_Iio] using Finset.card_le_card hs
      simp only [unary,decode,show ¬i.val < (ones c).card from by omega,decide_false]
  | true =>
      have hs : Finset.Iic i⊆ones c := by
        intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rcases lt_or_eq_of_le (Finset.mem_Iic.mp hj) with hji | hji
        · exact h j i hji hc
        · simpa only [hji] using hc
      have hn : i.val+1 ≤ (ones c).card := by
        simpa only [Fin.card_Iic] using Finset.card_le_card hs
      simp only [unary,decode,show i.val < (ones c).card from by omega,decide_true]

theorem decode_unary {m : ℕ} (t : Fin (m+1)) : decode (unary t)=t :=
  unary_injective m (unary_decode (unary t) (unary_legal t))

theorem legal_iff_unary {m : ℕ} (c : Clock m) : LegalClock c ↔ ∃t,unary t=c :=
  ⟨fun h => ⟨decode c,unary_decode c h⟩,by rintro ⟨t,rfl⟩; exact unary_legal t⟩

theorem illegal_has_penalty {m : ℕ} (c : Clock m) (h : ¬LegalClock c) :
    1≤(violations c).card := by
  have hn : (violations c).card≠0 := fun hz => h ((violations_zero_iff c).mp hz)
  omega

def clockFrame (m : ℕ) : Matrix (Clock m) (Fin (m+1)) ℂ :=
  fun c t => if c=unary t then 1 else 0

theorem clockFrame_isometry (m : ℕ) : (clockFrame m)ᴴ*clockFrame m=1 := by
  ext t s
  simp [clockFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    apply_ite,← (unary_injective m).eq_iff,eq_comm]

def clockPenalty (m : ℕ) : Matrix (Clock m) (Clock m) ℂ :=
  Matrix.diagonal (fun c => ((violations c).card:ℂ))

theorem clockPenalty_annihilates_history (m : ℕ) : clockPenalty m*clockFrame m=0 := by
  ext c t
  simp only [clockPenalty,Matrix.diagonal_mul,Matrix.zero_apply]
  by_cases hc : c=unary t
  · subst c
    rw [(violations_zero_iff _).mpr (unary_legal t)]
    simp
  · simp [clockFrame,hc]

def energy {I : Type} [Fintype I] (H : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  (Qatlib.Foundations.PureStateMath.Inner ψ (H*ᵥψ)).re

def mass {I : Type} [Fintype I] (ψ : QState I) : ℝ := ∑i,‖ψ i‖^2

theorem energy_diagonal {I : Type} [Fintype I] [DecidableEq I]
    (w : I→ℝ) (ψ : QState I) :
    energy (Matrix.diagonal (fun i => (w i:ℂ))) ψ=∑i,w i*‖ψ i‖^2 := by
  simp only [energy,inner_apply,Matrix.mulVec_diagonal,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (starRingEnd ℂ) (ψ i)*((w i:ℂ)*ψ i)=
      (w i:ℂ)*((starRingEnd ℂ) (ψ i)*ψ i) := by ring
  rw [he,← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.normSq_eq_norm_sq]

theorem clockPenalty_energy_lower {m : ℕ} (ψ : QState (Clock m)) :
    (∑c,if LegalClock c then (0:ℝ) else ‖ψ c‖^2)≤energy (clockPenalty m) ψ := by
  have he := energy_diagonal (fun c : Clock m => ((violations c).card:ℝ)) ψ
  change _≤energy (Matrix.diagonal (fun c : Clock m => (((violations c).card:ℝ):ℂ))) ψ
  rw [he]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : LegalClock c
  · rw [(violations_zero_iff c).mpr hc]
    simp [hc]
  · simp only [hc,ite_false]
    have hn : (1:ℝ)≤((violations c).card:ℝ) := by exact_mod_cast illegal_has_penalty c hc
    exact le_mul_of_one_le_left (sq_nonneg _) hn

def pairPenalty {m : ℕ} (i j : Fin m) : Matrix (Clock m) (Clock m) ℂ :=
  Matrix.diagonal (fun c => if i<j ∧ c i=false ∧ c j=true then 1 else 0)

theorem clockPenalty_eq_pair_sum (m : ℕ) :
    clockPenalty m=∑p : Fin m×Fin m,pairPenalty p.1 p.2 := by
  ext c d
  by_cases h : c=d
  · subst d
    simp only [clockPenalty,pairPenalty,Matrix.sum_apply,Matrix.diagonal_apply_eq]
    rw [violations,Finset.card_filter]
    simp only [Nat.cast_sum,apply_ite,Nat.cast_one,Nat.cast_zero]
  · simp [clockPenalty,pairPenalty,Matrix.sum_apply,h]

def bit {m : ℕ} (c : Clock m) (k : ℕ) : Bool :=
  if hz : k=0 then true
  else if hk : k ≤ m then c ⟨k-1,by omega⟩ else false

def Pre {m : ℕ} (i : Fin m) (c : Clock m) : Prop :=
  bit c i.val=true ∧ c i=false ∧ bit c (i.val+2)=false

def Post {m : ℕ} (i : Fin m) (c : Clock m) : Prop :=
  bit c i.val=true ∧ c i=true ∧ bit c (i.val+2)=false

def Outside {m : ℕ} (i : Fin m) (r c : Clock m) : Prop :=
  ∀ j : Fin m, j ≠ i → r j=c j

def hop {m : ℕ} (i : Fin m) : Matrix (Clock m) (Clock m) ℂ :=
  fun r c => if Post i r ∧ Pre i c ∧ Outside i r c then 1 else 0

theorem bit_unary {m : ℕ} (t : Fin (m+1)) (k : ℕ) :
    bit (unary t) k=decide (k ≤ t.val) := by
  by_cases hz : k=0
  · subst k
    simp [bit]
  · by_cases hk : k ≤ m
    · have he : (k-1 < t.val) ↔ k ≤ t.val := by omega
      simp [bit,hz,hk,unary,he]
    · have he : ¬k ≤ t.val := by
        have ht := t.isLt
        omega
      simp [bit,hz,hk,he]

theorem pre_unary_iff {m : ℕ} (i : Fin m) (t : Fin (m+1)) :
    Pre i (unary t) ↔ t=i.castSucc := by
  constructor
  · intro h
    have hl : decide (i.val ≤ t.val)=true := by
      simpa only [bit_unary] using h.1
    have hl' : i.val ≤ t.val := of_decide_eq_true hl
    have hc : ¬i.val < t.val := by
      intro hlt
      have ht : unary t i=true := decide_eq_true hlt
      rw [h.2.1] at ht
      cases ht
    apply Fin.ext
    change t.val=i.val
    omega
  · intro ht
    subst t
    simp [Pre,bit_unary,unary]

theorem post_unary_iff {m : ℕ} (i : Fin m) (t : Fin (m+1)) :
    Post i (unary t) ↔ t=i.succ := by
  constructor
  · intro h
    have hc : i.val < t.val := of_decide_eq_true h.2.1
    have hr : ¬i.val+2 ≤ t.val := by
      intro hle
      have ht : bit (unary t) (i.val+2)=true := by
        rw [bit_unary]
        exact decide_eq_true hle
      rw [h.2.2] at ht
      cases ht
    apply Fin.ext
    change t.val=i.val+1
    omega
  · intro ht
    subst t
    simp [Post,bit_unary,unary]

theorem unary_off_center {m : ℕ} (i j : Fin m) (hji : j ≠ i) :
    unary i.castSucc j=unary i.succ j := by
  have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have he : (j.val < i.val) ↔ j.val < i.val+1 := by omega
  simp [unary,he]

theorem outside_symm {m : ℕ} (i : Fin m) {r c : Clock m}
    (h : Outside i r c) : Outside i c r := fun j hj => (h j hj).symm

theorem post_row_iff {m : ℕ} (i : Fin m) (r : Clock m) :
    Post i r ∧ Outside i r (unary i.castSucc) ↔ r=unary i.succ := by
  constructor
  · rintro ⟨hp,ho⟩
    funext j
    by_cases hj : j=i
    · subst j
      simpa [unary] using hp.2.1
    · exact (ho j hj).trans (unary_off_center i j hj)
  · intro hr
    subst r
    refine ⟨(post_unary_iff i i.succ).mpr rfl,?_⟩
    exact fun j hj => (unary_off_center i j hj).symm

theorem pre_row_iff {m : ℕ} (i : Fin m) (r : Clock m) :
    Pre i r ∧ Outside i r (unary i.succ) ↔ r=unary i.castSucc := by
  constructor
  · rintro ⟨hp,ho⟩
    funext j
    by_cases hj : j=i
    · subst j
      simpa [unary] using hp.2.1
    · exact (ho j hj).trans (unary_off_center i j hj).symm
  · intro hr
    subst r
    refine ⟨(pre_unary_iff i i.castSucc).mpr rfl,?_⟩
    exact fun j hj => unary_off_center i j hj

theorem hop_unary_entry {m : ℕ} (i : Fin m) (t : Fin (m+1)) (r : Clock m) :
    hop i r (unary t) =
      if t=i.castSucc then Qatlib.Foundations.PureStateMath.Ket (unary i.succ) r else 0 := by
  by_cases ht : t=i.castSucc
  · subst t
    have he : (Post i r ∧ Pre i (unary i.castSucc) ∧
        Outside i r (unary i.castSucc)) ↔ r=unary i.succ := by
      constructor
      · rintro ⟨hp,_,ho⟩
        exact (post_row_iff i r).mp ⟨hp,ho⟩
      · intro hr
        subst r
        exact ⟨(post_unary_iff i i.succ).mpr rfl,
          (pre_unary_iff i i.castSucc).mpr rfl,
          fun j hj => (unary_off_center i j hj).symm⟩
    simp [hop,he,Qatlib.Foundations.PureStateMath.Ket]
  · simp [hop,pre_unary_iff,ht]

theorem hop_adjoint_unary_entry {m : ℕ} (i : Fin m) (t : Fin (m+1)) (r : Clock m) :
    (hop i)ᴴ r (unary t) =
      if t=i.succ then Qatlib.Foundations.PureStateMath.Ket (unary i.castSucc) r else 0 := by
  by_cases ht : t=i.succ
  · subst t
    have he : (Post i (unary i.succ) ∧ Pre i r ∧
        Outside i (unary i.succ) r) ↔ r=unary i.castSucc := by
      constructor
      · rintro ⟨_,hp,ho⟩
        exact (pre_row_iff i r).mp ⟨hp,outside_symm i ho⟩
      · intro hr
        subst r
        exact ⟨(post_unary_iff i i.succ).mpr rfl,
          (pre_unary_iff i i.castSucc).mpr rfl,
          fun j hj => (unary_off_center i j hj).symm⟩
    simp [Matrix.conjTranspose_apply,hop,he,Qatlib.Foundations.PureStateMath.Ket]
  · simp [Matrix.conjTranspose_apply,hop,post_unary_iff,ht]

theorem mulVec_ket_column {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (c : H) :
    M *ᵥ Qatlib.Foundations.PureStateMath.Ket c = fun r => M r c := by
  funext r
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]

theorem hop_unary_ket {m : ℕ} (i : Fin m) (t : Fin (m+1)) :
    hop i *ᵥ Qatlib.Foundations.PureStateMath.Ket (unary t) =
      if t=i.castSucc then Qatlib.Foundations.PureStateMath.Ket (unary i.succ) else 0 := by
  rw [mulVec_ket_column]
  funext r
  by_cases ht : t=i.castSucc <;> simpa [ht] using hop_unary_entry i t r

theorem hop_adjoint_unary_ket {m : ℕ} (i : Fin m) (t : Fin (m+1)) :
    (hop i)ᴴ *ᵥ Qatlib.Foundations.PureStateMath.Ket (unary t) =
      if t=i.succ then Qatlib.Foundations.PureStateMath.Ket (unary i.castSucc) else 0 := by
  rw [mulVec_ket_column]
  funext r
  by_cases ht : t=i.succ <;> simpa [ht] using hop_adjoint_unary_entry i t r

theorem hop_nonzero_sector {m : ℕ} (i : Fin m) (r c : Clock m) (hne : hop i r c ≠ 0) :
    LegalClock r ↔ LegalClock c := by
  have hh : Post i r ∧ Pre i c ∧ Outside i r c := by
    by_contra hn
    simp [hop,hn] at hne
  constructor
  · intro hr
    obtain ⟨t,ht⟩ := (legal_iff_unary r).mp hr
    rw [← ht] at hh
    have htime := (post_unary_iff i t).mp hh.1
    subst t
    have hc := (pre_row_iff i c).mp ⟨hh.2.1,outside_symm i hh.2.2⟩
    rw [hc]
    exact unary_legal _
  · intro hc
    obtain ⟨t,ht⟩ := (legal_iff_unary c).mp hc
    rw [← ht] at hh
    have htime := (pre_unary_iff i t).mp hh.2.1
    subst t
    have hr := (post_row_iff i r).mp ⟨hh.1,hh.2.2⟩
    rw [hr]
    exact unary_legal _

def timeUnit {m : ℕ} (t s : Fin (m+1)) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  fun u v => if u=t ∧ v=s then 1 else 0

theorem mul_clockFrame {m : ℕ} (M : Matrix (Clock m) (Clock m) ℂ)
    (r : Clock m) (t : Fin (m+1)) : (M*clockFrame m) r t=M r (unary t) := by
  simp [Matrix.mul_apply,clockFrame,mul_ite]

theorem clockFrame_timeUnit {m : ℕ} (t s q : Fin (m+1)) (r : Clock m) :
    (clockFrame m*timeUnit t s) r q=if q=s then clockFrame m r t else 0 := by
  simp [Matrix.mul_apply,timeUnit,mul_ite,ite_and]

theorem hop_frame {m : ℕ} (i : Fin m) :
    hop i*clockFrame m=clockFrame m*timeUnit i.succ i.castSucc := by
  ext r t
  rw [mul_clockFrame,clockFrame_timeUnit]
  exact hop_unary_entry i t r

theorem hop_adjoint_frame {m : ℕ} (i : Fin m) :
    (hop i)ᴴ*clockFrame m=clockFrame m*timeUnit i.castSucc i.succ := by
  ext r t
  rw [mul_clockFrame,clockFrame_timeUnit]
  exact hop_adjoint_unary_entry i t r

def clockIndicator {m : ℕ} (P : Clock m→Prop) : Matrix (Clock m) (Clock m) ℂ :=
  Matrix.diagonal (fun c => if P c then 1 else 0)

theorem indicator_frame {m : ℕ} (P : Clock m→Prop) (t : Fin (m+1))
    (hP : ∀s : Fin (m+1),P (unary s) ↔ s=t) :
    clockIndicator P*clockFrame m=clockFrame m*timeUnit t t := by
  ext c s
  rw [clockFrame_timeUnit]
  simp only [clockIndicator,Matrix.diagonal_mul]
  by_cases hc : c=unary s
  · subst c
    simp [clockFrame,hP,(unary_injective m).eq_iff,eq_comm]
  · by_cases hs : s=t
    · subst s
      simp [clockFrame,hc]
    · simp [clockFrame,hc,hs]

def preProjector {m : ℕ} (i : Fin m) : Matrix (Clock m) (Clock m) ℂ := clockIndicator (Pre i)
def postProjector {m : ℕ} (i : Fin m) : Matrix (Clock m) (Clock m) ℂ := clockIndicator (Post i)

theorem preProjector_frame {m : ℕ} (i : Fin m) :
    preProjector i*clockFrame m=clockFrame m*timeUnit i.castSucc i.castSucc :=
  indicator_frame (Pre i) i.castSucc (pre_unary_iff i)

theorem postProjector_frame {m : ℕ} (i : Fin m) :
    postProjector i*clockFrame m=clockFrame m*timeUnit i.succ i.succ :=
  indicator_frame (Post i) i.succ (post_unary_iff i)

def atStart {m : ℕ} (c : Clock m) : Prop := bit c 1=false
def atEnd {m : ℕ} (c : Clock m) : Prop := bit c m=true

theorem atStart_unary {m : ℕ} (t : Fin (m+1)) : atStart (unary t) ↔ t=0 := by
  simp only [atStart,bit_unary,decide_eq_false_iff_not,Fin.ext_iff,Fin.val_zero]
  omega

theorem atEnd_unary {m : ℕ} (t : Fin (m+1)) : atEnd (unary t) ↔ t=Fin.last m := by
  simp only [atEnd,bit_unary,decide_eq_true_eq,Fin.ext_iff,Fin.val_last]
  have ht := t.isLt
  omega

def historyFrame (m n : ℕ) : Matrix (Clock m×Reg n) (Fin (m+1)×Reg n) ℂ :=
  clockFrame m⊗ₖ(1:Matrix (Reg n) (Reg n) ℂ)

theorem historyFrame_isometry (m n : ℕ) : (historyFrame m n)ᴴ*historyFrame m n=1 := by
  simp only [historyFrame,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,clockFrame_isometry,Matrix.one_mul,Matrix.one_kronecker_one]

theorem isometry_mass {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix J I ℂ) (hV : Vᴴ*V=1) (ψ : QState I) :
    mass (V*ᵥψ)=mass ψ := by
  have he : Qatlib.Foundations.PureStateMath.Inner (V*ᵥψ) (V*ᵥψ)=Qatlib.Foundations.PureStateMath.Inner ψ ψ := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,hV,Matrix.one_mulVec]
  simpa only [mass,inner_self,Complex.re_sum,Complex.ofReal_re] using congrArg Complex.re he

theorem historyFrame_mass (m n : ℕ) (ψ : QState (Fin (m+1)×Reg n)) :
    mass (historyFrame m n*ᵥψ)=mass ψ := isometry_mass _ (historyFrame_isometry m n) ψ

theorem tensor_frame {m n : ℕ} (H : Matrix (Clock m) (Clock m) ℂ)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (U : Matrix (Reg n) (Reg n) ℂ)
    (h : H*clockFrame m=clockFrame m*A) :
    TensorGate H U*historyFrame m n=historyFrame m n*TensorGate A U := by
  simp only [TensorGate,historyFrame,← Matrix.mul_kronecker_mul,Matrix.mul_one,
    Matrix.one_mul,h]

def abstractPropagation {m n : ℕ} (i : Fin m) (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Fin (m+1)×Reg n) (Fin (m+1)×Reg n) ℂ :=
  ((1:ℂ)/2) • (TensorGate (timeUnit i.succ i.succ) 1+
    TensorGate (timeUnit i.castSucc i.castSucc) 1-
    TensorGate (timeUnit i.succ i.castSucc) U-
    TensorGate (timeUnit i.castSucc i.succ) Uᴴ)

def physicalPropagation {m n : ℕ} (i : Fin m) (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ :=
  ((1:ℂ)/2) • (TensorGate (postProjector i) 1+TensorGate (preProjector i) 1-
    TensorGate (hop i) U-TensorGate (hop i)ᴴ Uᴴ)

theorem physicalPropagation_frame {m n : ℕ} (i : Fin m) (U : Matrix (Reg n) (Reg n) ℂ) :
    physicalPropagation i U*historyFrame m n=historyFrame m n*abstractPropagation i U := by
  have h0 := tensor_frame (preProjector i) (timeUnit i.castSucc i.castSucc)
    (1:Matrix (Reg n) (Reg n) ℂ) (preProjector_frame i)
  have h1 := tensor_frame (postProjector i) (timeUnit i.succ i.succ)
    (1:Matrix (Reg n) (Reg n) ℂ) (postProjector_frame i)
  have hh := tensor_frame (hop i) (timeUnit i.succ i.castSucc) U (hop_frame i)
  have ha := tensor_frame (hop i)ᴴ (timeUnit i.castSucc i.succ) Uᴴ (hop_adjoint_frame i)
  simp only [physicalPropagation,abstractPropagation,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.add_mul,Matrix.sub_mul,Matrix.mul_add,Matrix.mul_sub,h0,h1,hh,ha]

def physicalInput {m n : ℕ} (j : Fin n) : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ :=
  TensorGate (clockIndicator atStart) (Matrix.diagonal (fun z : Reg n => if z j then 1 else 0))

def physicalOutput {m n : ℕ} (j : Fin n) : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ :=
  TensorGate (clockIndicator atEnd) (Matrix.diagonal (fun z : Reg n => if z j then 0 else 1))

theorem physicalInput_frame {m n : ℕ} (j : Fin n) :
    physicalInput j*historyFrame m n=historyFrame m n*
      TensorGate (timeUnit (0:Fin (m+1)) 0)
        (Matrix.diagonal (fun z : Reg n => if z j then 1 else 0)) :=
  tensor_frame _ _ _ (indicator_frame atStart 0 atStart_unary)

theorem physicalOutput_frame {m n : ℕ} (j : Fin n) :
    physicalOutput j*historyFrame m n=historyFrame m n*
      TensorGate (timeUnit (Fin.last m) (Fin.last m))
        (Matrix.diagonal (fun z : Reg n => if z j then 0 else 1)) :=
  tensor_frame _ _ _ (indicator_frame atEnd (Fin.last m) atEnd_unary)

theorem lifted_clockPenalty_annihilates_history (m n : ℕ) :
    TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)*historyFrame m n=0 := by
  simp only [TensorGate,historyFrame,← Matrix.mul_kronecker_mul,
    clockPenalty_annihilates_history,Matrix.one_mul,Matrix.zero_kronecker]

end
end Qatlib.Concepts.UniformBqp.FiniteGateWord
