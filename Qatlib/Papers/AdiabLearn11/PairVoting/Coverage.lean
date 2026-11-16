/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLearn11.PairVoting.FiniteCover

@[expose] public section


/-! # Complete finite coverage consequences of the old conditions -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AdiabLearn11.PairVoting.Coverage
open Models FiniteCover

/-- A finite family bounded above by one achieves maximal mean only pointwise. -/
theorem eachOne {V : Type*} [Fintype V] (f : V → ℚ) (hf : ∀ x, f x ≤ 1)
    (hs : ∑ x, f x=(Fintype.card V : ℚ)) : ∀ x, f x=1 := by
  have hz : ∑ x, (1-f x)=0 := by
    rw [Finset.sum_sub_distrib,hs]
    simp
  have hn : ∀ x, 0 ≤ 1-f x := fun x => sub_nonneg.mpr (hf x)
  intro x
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hn y)).mp hz x (Finset.mem_univ x)
  linarith

/-- The whole directed overlap identity forces actual finite event coverage. -/
theorem coverSets {V κ : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq κ] (E : κ → Finset V) (J : Finset κ)
    (h : (∑ p ∈ J, Pr (E p))-
      (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (E p ∩ E q))=1) :
    ∀ x, ∃ p ∈ J, x ∈ E p := by
  rw [scoreMean] at h
  have hn : (Fintype.card V : ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hs := (div_eq_one_iff_eq hn).mp h
  have hall := eachOne (score E J) (scoreBound E J) hs
  intro x
  by_contra hc
  push Not at hc
  have hk : ∑ p ∈ J, hit E p x=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [hit,hc p hp]
  have he : score E J x=0 := by rw [score,pairMoment,hk]; norm_num
  have hone := hall x
  linarith

/-- The actual extra-event score subtracts each extra overlap once. -/
def extraScore {V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (A : Finset V) (x : V) : ℚ :=
  score E J x+hit (fun _ : Unit => A) () x-
    hit (fun _ : Unit => A) () x*(∑ p ∈ J, hit E p x)

/-- The entire old extra-event score is pointwise at most one. -/
theorem extraBound {V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (A : Finset V) (x : V) :
    extraScore E J A x ≤ 1 := by
  by_cases ha : x ∈ A
  · have he : hit (fun _ : Unit => A) () x=1 := by simp [hit,ha]
    rw [extraScore,he,score,pairMoment]
    by_cases hex : ∃ p ∈ J, x ∈ E p
    · obtain ⟨p,hp,hpx⟩ := hex
      have hk : (1 : ℚ) ≤ ∑ q ∈ J, hit E q x := by
        have hs := Finset.single_le_sum (fun q (_ : q ∈ J) => hitNonneg E q x) hp
        simpa [hit,hpx] using hs
      nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ ∑ q ∈ J, hit E q x)
        (by linarith : (0 : ℚ) ≤ (∑ q ∈ J, hit E q x)-1)]
    · have hk : ∑ p ∈ J, hit E p x=0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hx : x ∉ E p := fun h => hex ⟨p,hp,h⟩
        simp [hit,hx]
      rw [hk]
      norm_num
  · simpa [extraScore,hit,ha] using scoreBound E J x

/-- The extra-event probability expression is exactly its actual finite score mean. -/
theorem extraMean {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (A : Finset V) :
    (∑ p ∈ J, Pr (E p))+Pr A-
      (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (E p ∩ E q))-
      (∑ p ∈ J, Pr (A ∩ E p))=
        (∑ x : V, extraScore E J A x)/(Fintype.card V : ℚ) := by
  have hi (p : κ) : Pr (A ∩ E p)=
      (∑ x : V, hit (fun _ : Unit => A) () x*hit E p x)/(Fintype.card V : ℚ) := by
    rw [massSum (fun _ : Unit => A ∩ E p) ()]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : x ∈ A <;> by_cases hp : x ∈ E p <;> simp [hit,ha,hp]
  have ht : ∑ p ∈ J, Pr (A ∩ E p)=
      (∑ x : V, hit (fun _ : Unit => A) () x*(∑ p ∈ J, hit E p x))/(Fintype.card V : ℚ) := by
    simp_rw [hi,← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  calc
    _ = ((∑ p ∈ J, Pr (E p))-
        (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (E p ∩ E q)))+
        Pr A-(∑ p ∈ J, Pr (A ∩ E p)) := by ring
    _ = _ := by
      rw [scoreMean,ht,massSum (fun _ : Unit => A) (),← add_div,← sub_div]
      congr 1
      simp only [extraScore,Finset.sum_add_distrib,Finset.sum_sub_distrib]

/-- The complete extra-classifier overlap identity forces the stated actual coverage. -/
theorem coverExtra {V κ : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq κ] (E : κ → Finset V) (J : Finset κ) (A : Finset V)
    (h : (∑ p ∈ J, Pr (E p))+Pr A-
      (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (E p ∩ E q))-
      (∑ p ∈ J, Pr (A ∩ E p))=1) :
    ∀ x, (∃ p ∈ J, x ∈ E p) ∨ x ∈ A := by
  rw [extraMean] at h
  have hn : (Fintype.card V : ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hall := eachOne (extraScore E J A) (extraBound E J A) ((div_eq_one_iff_eq hn).mp h)
  intro x
  by_contra hc
  have hp : ¬∃ p ∈ J, x ∈ E p := fun h => hc (Or.inl h)
  have ha : x ∉ A := fun h => hc (Or.inr h)
  have hk : ∑ p ∈ J, hit E p x=0 := by
    apply Finset.sum_eq_zero
    intro p hJ
    have hx : x ∉ E p := fun h => hp ⟨p,hJ,h⟩
    simp [hit,hx]
  have he : extraScore E J A x=0 := by
    rw [extraScore,score,pairMoment,hk]
    simp [hit,ha]
  have hone := hall x
  linarith

/-- The entire original Condition3 target follows without an added cover premise. -/
theorem covers {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq ι] (c : ι → V → ℤ) (J : Finset (ι × ι)) (h : Condition3 c J) :
    ∀ x, ∃ p ∈ J, x ∈ pairMeet c p := coverSets (pairMeet c) J h

/-- The entire original Condition3a target follows with the actual extra set. -/
theorem coversExtra {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq ι] (c : ι → V → ℤ) (J : Finset (ι × ι)) (a : ι) (h : Condition3a c J a) :
    ∀ x, (∃ p ∈ J, x ∈ pairMeet c p) ∨ x ∈ CorrectSet c a :=
  coverExtra (pairMeet c) J (CorrectSet c a) h

end Qatlib.Papers.AdiabLearn11.PairVoting.Coverage
