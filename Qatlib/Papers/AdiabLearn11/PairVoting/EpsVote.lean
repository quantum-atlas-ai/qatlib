/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLearn11.PairVoting.Claims

@[expose] public section


/-! # The complete original finite error-union argument

The cover condition supplies a genuine positive pair. Unless some pair has
negative correctness, that pair forces a positive full pair vote. The actual
negative-pair masses are the errors from Condition2a, and their finite union
is bounded by the sum of those errors. Binary weight bookkeeping remains an
explicit structural premise, exactly as in the complete historical target.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AdiabLearn11.PairVoting.EpsVote
open Models Claims

/-- Monotonicity of the actual uniform finite-event mass. -/
theorem massMono {V : Type*} [Fintype V] (s t : Finset V) (h : s ⊆ t) : Pr s ≤ Pr t := by
  unfold Pr
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card h
  · positivity

/-- The actual finite union bound, with no event probability supplied as a conclusion. -/
theorem massUnionBound {V κ : Type*} [Fintype V] [DecidableEq V]
    (E : κ → Finset V) (J : Finset κ) : Pr (J.biUnion E) ≤ ∑ p ∈ J, Pr (E p) := by
  unfold Pr
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_biUnion_le
  · positivity

/-- The exact complementary mass identity on a nonempty finite sample domain. -/
theorem massCompl {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (s : Finset V) : Pr (Finset.univ\s)=1-Pr s := by
  have h := massUnion s (Finset.univ\s)
  have hu : s ∪ (Finset.univ\s)=Finset.univ := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hi : s ∩ (Finset.univ\s)=∅ := by ext x; simp
  have hz : Pr (∅ : Finset V)=0 := by simp [Pr]
  rw [hu,hi,massAll,hz] at h
  linarith

/-- The entire old Theorem3 target follows from actual event coverage and a union bound. -/
theorem epsPairs {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype ι] [DecidableEq ι]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x=1 ∨ c i x=-1)
    (J : Finset (ι × ι)) (ε : ι × ι → ℚ)
    (h2a : Condition2a c J ε) (h3 : Condition3 c J)
    (hbook : ∀ x, ∑ i, pairWeight J i*c i x=∑ p ∈ J, (c p.1 x+c p.2 x)) :
    EpsPerfect c (pairWeight J) (∑ p ∈ J, ε p) := by
  let E : (ι × ι) → Finset V :=
    fun p => Finset.univ.filter (fun x => c p.1 x+c p.2 x<0)
  let good := Finset.univ.filter (fun x => 0<∑ i, pairWeight J i*c i x)
  let bad := Finset.univ\good
  have he (p : ι × ι) (hp : p ∈ J) : Pr (E p)=ε p := by
    have hh := lemmaOneA c hrange p.1 p.2 (ε p) (h2a p hp)
    have hc : E p=Finset.univ\
        (Finset.univ.filter (fun x => 0≤c p.1 x+c p.2 x)) := by
      ext x
      simp [E,not_le]
    rw [hc,massCompl,hh]
    ring
  have hsub : bad ⊆ J.biUnion E := by
    intro x hx
    have hx0 : (∑ i, pairWeight J i*c i x)≤0 := by simpa [bad,good,not_lt] using hx
    by_contra hn
    have hnonneg (p : ι × ι) (hp : p ∈ J) : 0≤c p.1 x+c p.2 x := by
      by_contra hlt
      have hm : x ∈ E p := by simp [E,lt_of_not_ge hlt]
      exact hn (Finset.mem_biUnion.mpr ⟨p,hp,hm⟩)
    obtain ⟨p,hp,hpx⟩ := Coverage.covers c J h3 x
    have htwo : c p.1 x+c p.2 x=2 := by
      simp only [pairMeet,CorrectSet,Finset.mem_inter,Finset.mem_filter,
        Finset.mem_univ,true_and] at hpx
      omega
    have hs := Finset.single_le_sum hnonneg hp
    rw [htwo] at hs
    rw [hbook] at hx0
    linarith
  have hb : Pr bad ≤ ∑ p ∈ J, ε p := by
    calc
      _ ≤ Pr (J.biUnion E) := massMono bad _ hsub
      _ ≤ ∑ p ∈ J, Pr (E p) := massUnionBound E J
      _ = _ := Finset.sum_congr rfl (fun p hp => he p hp)
  have hc : Pr bad=1-Pr good := massCompl good
  change 1-(∑ p ∈ J, ε p) ≤ Pr good
  linarith

end Qatlib.Papers.AdiabLearn11.PairVoting.EpsVote
