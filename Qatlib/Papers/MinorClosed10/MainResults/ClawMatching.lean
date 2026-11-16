/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.ClawCover

@[expose] public section


/-! # Disjoint-edge lower bounds for subdivided stars

Demand: Childs--Kothari, arXiv1011.1443v2 Proposition 4.1.
Each family is an embedding of actual edge endpoints, so no matching
size or vertex-cover conclusion is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.MinorClosed10.MainResults.ClawMatching
open PathCover ClawCover

/-- The consecutive pairs along each branch are mutually disjoint actual vertex pairs. -/
def branchPairs {I : Type} (d : I → ℕ) :
    ((Σ i, Fin (d i/2)) × Bool) ↪ (Unit ⊕ (Σ i, Fin (d i))) where
  toFun p := .inr ⟨p.1.1,⟨2*p.1.2.val+(if p.2 then 1 else 0),
    by have := p.1.2.isLt; split_ifs <;> omega⟩⟩
  inj' := by
    rintro ⟨⟨i,a⟩,b⟩ ⟨⟨j,c⟩,e⟩ h
    have hij : i=j := congrArg Sigma.fst (Sum.inr.inj h)
    subst j
    have hv := congrArg (fun v : Σ i, Fin (d i) => v.2.val) (Sum.inr.inj h)
    cases b <;> cases e <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv
    all_goals first
      | (exfalso; omega)
      | (have hac : a=c := Fin.ext (by omega); subst c; rfl)

/-- Every pair in the branch family is a genuine consecutive star edge. -/
theorem branchAdj {I : Type} (d : I → ℕ) (p : Σ i, Fin (d i/2)) :
    (starG d).Adj (branchPairs d (p,false)) (branchPairs d (p,true)) := by
  refine ⟨(branchPairs d).injective.ne (by simp), Or.inl ?_⟩
  constructor
  · rfl
  · change 2*p.2.val+0+1=2*p.2.val+1
    omega

/-- All branch pairs force at least the sum of the half-lengths into every actual cover. -/
theorem branchLower {I : Type} [Fintype I] (d : I → ℕ) :
    ((∑ i, d i/2 : ℕ) : ℕ∞) ≤ (starG d).vertexCoverNum := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    matchLower (starG d) (branchPairs d) (branchAdj d)

/-- When every branch is even, the actual even-indexed cover and branch matching have equal size. -/
theorem evenNumber {I : Type} [Fintype I] (d : I → ℕ) (hd : ∀ i, Even (d i)) :
    (starG d).vertexCoverNum = ((∑ i, d i/2 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · have he : ∀ i, (d i+1)/2=d i/2 := by
      intro i
      obtain ⟨k,hk⟩ := hd i
      omega
    simpa only [he] using (noCover d).vertexCoverNum_le.trans_eq (noCard d)
  · exact branchLower d

/-- Shift the matching one step along one odd branch, leaving its first vertex free. -/
def shiftedPairs {I : Type} [DecidableEq I] (d : I → ℕ) (s : I) (hs : Odd (d s)) :
    ((Σ i, Fin (d i/2)) × Bool) ↪ (Σ i, Fin (d i)) where
  toFun p := ⟨p.1.1,⟨2*p.1.2.val+(if p.1.1=s then 1 else 0)+(if p.2 then 1 else 0), by
    have hj := p.1.2.isLt
    by_cases hi : p.1.1=s
    · have hj' : p.1.2.val < d s/2 := by simpa only [hi] using hj
      obtain ⟨k,hk⟩ := hs
      simp only [hi, ite_true]
      split_ifs <;> omega
    · simp only [hi, ite_false]
      split_ifs <;> omega⟩⟩
  inj' := by
    rintro ⟨⟨i,a⟩,b⟩ ⟨⟨j,c⟩,e⟩ h
    have hij : i=j := congrArg Sigma.fst h
    subst j
    have hv := congrArg (fun v : Σ i, Fin (d i) => v.2.val) h
    cases b <;> cases e <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv
    all_goals first
      | (exfalso; omega)
      | (have hac : a=c := Fin.ext (by omega); subst c; rfl)

/-- The shifted branch matching does not use the first vertex of the distinguished odd branch. -/
theorem shiftedAvoid {I : Type} [DecidableEq I] (d : I → ℕ) (s : I) (hs : Odd (d s))
    (p : (Σ i, Fin (d i/2)) × Bool) (h : (shiftedPairs d s hs p).1=s) :
    0 < (shiftedPairs d s hs p).2.val := by
  change p.1.1=s at h
  change 0 < 2*p.1.2.val+(if p.1.1=s then 1 else 0)+(if p.2 then 1 else 0)
  simp only [h, ite_true]
  split_ifs <;> omega

/-- Add a centre edge to the shifted branch matching, obtaining one more disjoint actual edge. -/
def oddPairs {I : Type} [DecidableEq I] (d : I → ℕ) (s : I) (hs : Odd (d s)) :
    ((Unit ⊕ (Σ i, Fin (d i/2))) × Bool) ↪ (Unit ⊕ (Σ i, Fin (d i))) where
  toFun p := match p.1 with
    | .inl _ => if p.2 then .inr ⟨s,⟨0, by obtain ⟨k,hk⟩ := hs; omega⟩⟩ else .inl ()
    | .inr a => .inr (shiftedPairs d s hs (a,p.2))
  inj' := by
    rintro ⟨u | a,b⟩ ⟨v | c,e⟩ h
    · cases u; cases v; cases b <;> cases e <;> simp_all
    · cases b
      · simp at h
      · have he := Sum.inr.inj h
        have hi := congrArg Sigma.fst he
        have hv := congrArg (fun v : Σ i, Fin (d i) => v.2.val) he
        change s=(shiftedPairs d s hs (c,e)).1 at hi
        change 0=(shiftedPairs d s hs (c,e)).2.val at hv
        have hp := shiftedAvoid d s hs (c,e) hi.symm
        omega
    · cases e
      · simp at h
      · have he := Sum.inr.inj h
        have hi := congrArg Sigma.fst he
        have hv := congrArg (fun v : Σ i, Fin (d i) => v.2.val) he
        change (shiftedPairs d s hs (a,b)).1=s at hi
        change (shiftedPairs d s hs (a,b)).2.val=0 at hv
        have hp := shiftedAvoid d s hs (a,b) hi
        omega
    · have he := (shiftedPairs d s hs).injective (Sum.inr.inj h)
      cases he
      rfl

/-- Every member of the extended odd-branch matching is an actual edge. -/
theorem oddAdj {I : Type} [DecidableEq I] (d : I → ℕ) (s : I) (hs : Odd (d s))
    (p : Unit ⊕ (Σ i, Fin (d i/2))) :
    (starG d).Adj (oddPairs d s hs (p,false)) (oddPairs d s hs (p,true)) := by
  refine ⟨(oddPairs d s hs).injective.ne (by simp), Or.inl ?_⟩
  rcases p with u | ⟨i,j⟩
  · rfl
  · constructor
    · rfl
    · change 2*j.val+(if i=s then 1 else 0)+0+1 =
        2*j.val+(if i=s then 1 else 0)+1
      omega

/-- An odd branch makes the centre cover optimal by supplying the extra disjoint centre edge. -/
theorem oddNumber {I : Type} [Fintype I] [DecidableEq I] (d : I → ℕ) (s : I)
    (hs : Odd (d s)) :
    (starG d).vertexCoverNum = ((1+∑ i, d i/2 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact (withCover d).vertexCoverNum_le.trans_eq (withCard d)
  · simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma,
      Fintype.card_fin] using matchLower (starG d) (oddPairs d s hs) (oddAdj d s hs)

end Qatlib.Papers.MinorClosed10.MainResults.ClawMatching
