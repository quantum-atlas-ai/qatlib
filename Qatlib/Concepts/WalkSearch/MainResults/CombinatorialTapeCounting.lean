/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialRejectionBound
import Qatlib.Concepts.WalkSearch.Primitives.VertexSamplingQuan

/-!
# Counting failure events on complete algorithm tapes

Product equivalences isolate each random component of `sourceCombTape`, allowing fiberwise
failure bounds to be lifted to the full tape space. `sourceComb_reject_card_from_local_bounds`
combines sampling and degree test bounds with the search family guarantees to bound rejection on
graphs containing a triangle. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `source_event_fiber_bound`: A bound `fiber * R ≤ C * Fintype.card X` on every fiber of a
  product presentation `Ω ≃ A × X` yields `event * R ≤ C * Fintype.card Ω`.
* `sourceComb_reject_card_from_local_bounds`: For a graph containing a triangle and the stated
  search and threshold assumptions, the local sampling and degree test bounds imply `rejecting
  tapes * n ≤ 2 * total tapes`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- A bound `fiber * R ≤ C * Fintype.card X` on every fiber of a product presentation `Ω ≃ A ×
X` yields `event * R ≤ C * Fintype.card Ω`. -/
theorem source_event_fiber_bound {Ω A X : Type} [Fintype Ω] [Fintype A] [Fintype X]
    (e : Ω ≃ A×X) (P : Ω → Prop) (R C : ℕ)
    (h : ∀ a, (Finset.univ.filter (fun x => P (e.symm (a,x)))).card*R ≤ C*Fintype.card X) :
    (Finset.univ.filter P).card*R ≤ C*Fintype.card Ω := by
  have he : (Finset.univ.filter P).card =
      (Finset.univ.filter (fun z : A×X => P (e.symm z))).card := by
    apply Finset.card_bij (fun t _ => e t)
    · intro t ht
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply] using! ht
    · intro a _ b _ hab
      exact e.injective hab
    · intro z hz
      exact ⟨e.symm z, by simpa using! hz, by simp⟩
  rw [he,Fintype.card_congr e]
  exact product_event_card_bound (fun a x => P (e.symm (a,x))) R C h

/-- Reassociate and reorder a source tape to isolate the sampled vertex function as the final
product factor. -/
def sourceTape_sample_equiv (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) :
    sourceCombTape n k K c sgs ets ≃ ((Fin n→sgs.seed)×(Fin n→Fin K→Fin c→Fin n)×(Fin n→sgs.seed)×sgs.seed×ets.seed n)×(Fin k→Fin n) :=
  { toFun := fun t => ((t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2),t.1)
    invFun := fun u => (u.2,u.1.1,u.1.2.1,u.1.2.2.1,u.1.2.2.2.1,u.1.2.2.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Reassociate and reorder a source tape to isolate the preparation seed function as the final
product factor. -/
def sourceTape_preparation_equiv (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) :
    sourceCombTape n k K c sgs ets ≃ ((Fin k→Fin n)×(Fin n→Fin K→Fin c→Fin n)×(Fin n→sgs.seed)×sgs.seed×ets.seed n)×(Fin n→sgs.seed) :=
  { toFun := fun t => ((t.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2),t.2.1)
    invFun := fun u => (u.1.1,u.2,u.1.2.1,u.1.2.2.1,u.1.2.2.2.1,u.1.2.2.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Reassociate and reorder a source tape to isolate the degree test tape as the final product
factor. -/
def sourceTape_degree_equiv (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) :
    sourceCombTape n k K c sgs ets ≃ ((Fin k→Fin n)×(Fin n→sgs.seed)×(Fin n→sgs.seed)×sgs.seed×ets.seed n)×(Fin n→Fin K→Fin c→Fin n) :=
  { toFun := fun t => ((t.1,t.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2),t.2.2.1)
    invFun := fun u => (u.1.1,u.1.2.1,u.2,u.1.2.2.1,u.1.2.2.2.1,u.1.2.2.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Reassociate and reorder a source tape to isolate the final triangle search seed as the final
product factor. -/
def sourceTape_triangle_equiv (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) :
    sourceCombTape n k K c sgs ets ≃ ((Fin k→Fin n)×(Fin n→sgs.seed)×(Fin n→Fin K→Fin c→Fin n)×(Fin n→sgs.seed)×ets.seed n)×sgs.seed :=
  { toFun := fun t => ((t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.2),t.2.2.2.2.1)
    invFun := fun u => (u.1.1,u.1.2.1,u.1.2.2.1,u.1.2.2.2.1,u.2,u.1.2.2.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Present a source tape as its other components paired with the final promised edge search
seed. -/
def sourceTape_edge_equiv (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) :
    sourceCombTape n k K c sgs ets ≃ ((Fin k→Fin n)×(Fin n→sgs.seed)×(Fin n→Fin K→Fin c→Fin n)×(Fin n→sgs.seed)×sgs.seed)×ets.seed n :=
  { toFun := fun t => ((t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1),t.2.2.2.2.2)
    invFun := fun u => (u.1.1,u.1.2.1,u.1.2.2.1,u.1.2.2.2.1,u.1.2.2.2.2,u.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- With the prescribed positive sample size, the number of full tapes failing the sampled
survivor thinness condition times `n` is at most the total tape count. -/
theorem source_joint_sampling_bad_card (n : ℕ) (ε : ℝ) (hn : 0<n) (hε : 0<ε) (hε1 : ε<1)
    (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) (K c : ℕ)
    (hk : 0<Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1))) :
    let k:=Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1))
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      ¬sampledSurvivors G t.1 ⊆ thinPairs G.edges (Nat.floor ((n:ℝ)^(1-ε))))).card*n ≤
      Fintype.card (sourceCombTape n k K c sgs ets) := by
  intro k
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  have hh := source_event_fiber_bound (sourceTape_sample_equiv n k K c sgs ets)
    (fun t => ¬sampledSurvivors G t.1 ⊆ thinPairs G.edges (Nat.floor ((n:ℝ)^(1-ε)))) n 1 (by
    intro a
    simpa only [sourceTape_sample_equiv,Equiv.coe_fn_symm_mk,one_mul] using!
      (lemma3Sampling_withReplacement n ε hn hε hε1 hk G).le

  )
  convert! hh using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext t <;> try simp

/-- For a search family with exponent at least three, the number of full tapes with a bad
preparation call times `(n * n + 1)^3` is at most `n` times the total tape count. -/
theorem source_joint_preparation_bad_card (n k K c τ : ℕ) (G : UGraph n)
    (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily) (hc : 3≤family.cExp) :
    let sgs:=sourceSearchExecution family n τ
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      ¬preparationCallsGood G sgs t.2.1 (Finset.univ.image t.1).toList)).card*(n*n+1)^3 ≤
      n*Fintype.card (sourceCombTape n k K c sgs ets) := by
  intro sgs
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  have hh := source_event_fiber_bound (sourceTape_preparation_equiv n k K c sgs ets)
    (fun t => ¬preparationCallsGood G sgs t.2.1 (Finset.univ.image t.1).toList) ((n*n+1)^3) n (by
    intro a
    simpa only [sourceTape_preparation_equiv,Equiv.coe_fn_symm_mk] using!
      preparation_bad_calls_card G family (sourceSearchScope n τ) hc
        (source_preparation_call_supported n τ) (Finset.univ.image a.1).toList

  )
  convert! hh using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext t <;> try simp

/-- With the prescribed degree test parameters, the number of full tapes failing classification
test correctness times `n^3` is at most `2 * n` times the total tape count. -/
theorem source_joint_degree_bad_card (n : ℕ) (δ : ℝ) (hn : 0<n) (hδ : 0<δ) (hδ1 : δ<1)
    (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) (k τ : ℕ)
    (hc : 0<Nat.ceil ((n:ℝ)^δ)) :
    let K:=64*(Nat.log 2 n+2)
    let c:=Nat.ceil ((n:ℝ)^δ)
    let dHi:=10*Nat.ceil ((n:ℝ)^(1-δ))
    let dLo:=Nat.floor ((n:ℝ)^(1-δ)/10)
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
        ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩)).card*n^3 ≤
      (2*n)*Fintype.card (sourceCombTape n k K c sgs ets) := by
  intro K c dHi dLo
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  have hh := source_event_fiber_bound (sourceTape_degree_equiv n k K c sgs ets)
    (fun t => ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
      ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩) (n^3) (2*n) (by
    intro a
    simpa only [sourceTape_degree_equiv,Equiv.coe_fn_symm_mk] using!
      classifyScan_bad_tests_card_positive n δ hn hδ hδ1 hc G sgs τ a.2.2.1
        ⟨sampledSurvivors G a.1,sampledSurvivors_symmetric G a.1⟩

  )
  convert! hh using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext t <;> try simp

/-- For a scoped search family with exponent at least three, full tapes with a bad final
triangle search seed satisfy `bad * (n * n + 1)^3 ≤ total`. -/
theorem source_joint_triangle_bad_card (n k K c τ : ℕ) (G : UGraph n)
    (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily) (hc : 3≤family.cExp) :
    let sgs:=sourceSearchExecution family n τ
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      t.2.2.2.2.1 ∈ safeGroverBadSeeds sgs
        (triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset) 3 (n*n))).card*(n*n+1)^3 ≤
      Fintype.card (sourceCombTape n k K c sgs ets) := by
  intro sgs
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  have hh := source_event_fiber_bound (sourceTape_triangle_equiv n k K c sgs ets)
    (fun t => t.2.2.2.2.1 ∈ safeGroverBadSeeds sgs
      (triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset) 3 (n*n)) ((n*n+1)^3) 1 (by
    intro a
    let T := (classifyScan G sgs τ K c a.2.2.1 a.2.2.2.1 Finset.univ.toList
      ⟨sampledSurvivors G a.1,sampledSurvivors_symmetric G a.1⟩).movedT.toFinset
    have hT := classifyScan_triCount_bound G sgs τ K c a.2.2.1 a.2.2.2.1 Finset.univ.toList
      ⟨sampledSurvivors G a.1,sampledSurvivors_symmetric G a.1⟩
    have hb := safeGroverBadSeeds_padded_bound family (sourceSearchScope n τ) (triangleMarked G T) n 3 hc
      (source_triangle_call_supported n τ T hT)
    have he : (Finset.univ.filter (fun ρ : sgs.seed => ρ ∈ safeGroverBadSeeds sgs (triangleMarked G T) 3 (n*n))) =
        safeGroverBadSeeds sgs (triangleMarked G T) 3 (n*n) := by ext ρ; simp
    have hf : (Finset.univ.filter (fun ρ : sgs.seed => ρ ∈ safeGroverBadSeeds sgs (triangleMarked G T) 3 (n*n))).card*(n*n+1)^3≤
        1*Fintype.card sgs.seed := by rw [he,one_mul]; exact hb
    convert! hf using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext ρ <;> simp <;> rfl

  )
  convert! hh using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext t <;> try simp

/-- The classification edge set meets its graph mass promise and contains a graph triangle, but
the final promised edge search returns `none`. -/
def sourceEdgeBad {n : ℕ} (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) (t : sourceCombTape n k K c sgs ets) : Prop :=
  let E := (sourceTapeClass G sgs ets k K c τ t).movedE
  (E∩G.edges).card ≤ sourceEdgeMassBound n dHi dLo τ tThin ∧
    edgeTriangleExists G E ∧ ets.run G E (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 = none

/-- For a promised edge search family with exponent at least three, full tapes satisfying
`sourceEdgeBad` obey `bad * (n * n + 1)^3 ≤ total`. -/
theorem source_joint_edge_bad_card (n k K c dHi dLo τ tThin : ℕ) (G : UGraph n)
    (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) (hc : 3≤ets.cExp) :
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (sourceEdgeBad G sgs ets k K c dHi dLo τ tThin)).card*(n*n+1)^3 ≤
      Fintype.card (sourceCombTape n k K c sgs ets) := by
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  have hh := source_event_fiber_bound (sourceTape_edge_equiv n k K c sgs ets)
    (sourceEdgeBad G sgs ets k K c dHi dLo τ tThin) ((n*n+1)^3) 1 (by
    intro a
    let E := (classifyScan G sgs τ K c a.2.2.1 a.2.2.2.1 Finset.univ.toList
      ⟨sampledSurvivors G a.1,sampledSurvivors_symmetric G a.1⟩).movedE
    let M := sourceEdgeMassBound n dHi dLo τ tThin
    dsimp only [sourceTape_edge_equiv,sourceEdgeBad,sourceTapeClass,Equiv.coe_fn_symm_mk]
    have hb : (Finset.univ.filter (fun ρ : ets.seed n => (E∩G.edges).card≤M ∧ edgeTriangleExists G E ∧
      ets.run G E M ρ=none)).card*(n*n+1)^3 ≤ 1*Fintype.card (ets.seed n) := by
      by_cases hp : (E∩G.edges).card≤M ∧ edgeTriangleExists G E
      · have he : (Finset.univ.filter (fun ρ : ets.seed n => (E∩G.edges).card≤M ∧ edgeTriangleExists G E ∧ ets.run G E M ρ=none)) =
            Finset.univ.filter (fun ρ : ets.seed n => ets.run G E M ρ=none) := by ext ρ; simp [hp.1,hp.2]
        rw [he,one_mul]
        have hb := ets.finds G E M hp.1 hp.2
        exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1≤n*n+1) hc)).trans hb
      · have he : (Finset.univ.filter (fun ρ : ets.seed n => (E∩G.edges).card≤M ∧ edgeTriangleExists G E ∧ ets.run G E M ρ=none)) = ∅ := by
          ext ρ
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
          tauto
        rw [he]
        simp
    convert! hb using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext ρ <;>
      simp [sourceTape_edge_equiv,sourceEdgeBad,sourceTapeClass,E,M]

  )
  convert! hh using 1 <;> (try simp only [one_mul]) <;> congr 2 <;> ext t <;> try simp

/-- For `3 ≤ n`, the five stated bounds on the error counts and `r ≤ b0 + b1 + b2 + b3 + b4`
imply `r * n ≤ 2 * Ω`. -/
theorem source_five_error_budget (n Ω r b0 b1 b2 b3 b4 : ℕ) (hn : 3≤n)
    (hr : r≤b0+b1+b2+b3+b4) (h0 : b0*n≤Ω) (h1 : b1*(n*n+1)^3≤n*Ω)
    (h2 : b2*n^3≤2*n*Ω) (h3 : b3*(n*n+1)^3≤Ω) (h4 : b4*(n*n+1)^3≤Ω) :
    r*n≤2*Ω := by
  have hD : n^6≤(n*n+1)^3 := by
    calc
      _ = (n*n)^3 := by ring
      _ ≤ _ := Nat.pow_le_pow_left (by omega) 3
  have hb0 := Nat.mul_le_mul_right (n^5) h0
  have hb1 := (Nat.mul_le_mul_left b1 hD).trans h1
  have hb2 := Nat.mul_le_mul_right (n^3) h2
  have hb3 := (Nat.mul_le_mul_left b3 hD).trans h3
  have hb4 := (Nat.mul_le_mul_left b4 hD).trans h4
  have hsum : (b0+b1+b2+b3+b4)*n^6≤Ω*(n^5+2*n^4+n+2) := by
    nlinarith only [hb0,hb1,hb2,hb3,hb4]
  have hp : 2*n^4+n+2≤n^5 := by
    have hmul := Nat.mul_le_mul_right (n^4) hn
    have h24 : n^2≤n^4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith only [hmul,h24,hn]
  have hmul := Nat.mul_le_mul_left Ω hp
  have hr' := Nat.mul_le_mul_right (n^6) hr
  have hh : (r*n)*n^5≤(2*Ω)*n^5 := by nlinarith only [hr',hsum,hmul]
  exact Nat.le_of_mul_le_mul_right hh (by positivity : 0<n^5)

/-- For a graph containing a triangle and the stated search and threshold assumptions, the local
sampling and degree test bounds imply `rejecting tapes * n ≤ 2 * total tapes`. -/
theorem sourceComb_reject_card_from_local_bounds (n k K c dHi dLo τ tThin : ℕ) (G : UGraph n)
    (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily)
    (hc : 3≤family.cExp) (hec : 3≤ets.cExp) (hn : 3≤n)
    (hdLo : 1≤dLo) (hhi : dLo≤dHi) (hτ : 1≤τ) (htri : 1≤triCount G.edges) :
    let sgs:=sourceSearchExecution family n τ
    letI:=sgs.seedFin
    letI:=ets.seedFin n
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      ¬sampledSurvivors G t.1 ⊆ thinPairs G.edges tThin)).card*n ≤ Fintype.card (sourceCombTape n k K c sgs ets) →
    (Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
      ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
        ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩)).card*n^3 ≤
      2*n*Fintype.card (sourceCombTape n k K c sgs ets) →
    (Finset.univ.filter (sourceCombRejects G sgs ets k K c dHi dLo τ tThin)).card*n ≤
      2*Fintype.card (sourceCombTape n k K c sgs ets) := by
  intro sgs
  letI:=sgs.seedFin
  letI:=ets.seedFin n
  intro h0 h2
  let B0 :=
      Finset.univ.filter
      (fun t : sourceCombTape n k K c sgs ets => ¬sampledSurvivors G t.1 ⊆ thinPairs G.edges tThin)
  let B1 :=
      Finset.univ.filter
      (fun t : sourceCombTape n k K c sgs ets => ¬preparationCallsGood G sgs t.2.1 (Finset.univ.image t.1).toList)
  let B2 := Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets =>
    ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
      ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩)
  let B3 := Finset.univ.filter (fun t : sourceCombTape n k K c sgs ets => t.2.2.2.2.1 ∈ safeGroverBadSeeds sgs
    (triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset) 3 (n*n))
  let B4 := Finset.univ.filter (sourceEdgeBad G sgs ets k K c dHi dLo τ tThin)
  have h1 : B1.card*(n*n+1)^3 ≤ n*Fintype.card (sourceCombTape n k K c sgs ets) := by
    exact source_joint_preparation_bad_card n k K c τ G family ets hc
  have h3 : B3.card*(n*n+1)^3 ≤ Fintype.card (sourceCombTape n k K c sgs ets) := by
    exact source_joint_triangle_bad_card n k K c τ G family ets hc
  have h4 : B4.card*(n*n+1)^3 ≤ Fintype.card (sourceCombTape n k K c sgs ets) := by
    exact source_joint_edge_bad_card n k K c dHi dLo τ tThin G sgs ets hec
  have hs : Finset.univ.filter (sourceCombRejects G sgs ets k K c dHi dLo τ tThin) ⊆ B0∪B1∪B2∪B3∪B4 := by
    intro t ht
    by_contra hb
    have hb' : t∉B0 ∧ t∉B1 ∧ t∉B2 ∧ t∉B3 ∧ t∉B4 := by
      simpa only [Finset.mem_union,not_or,and_assoc] using! hb
    have hsamp : sampledSurvivors G t.1 ⊆ thinPairs G.edges tThin := by
      simpa only [B0,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using! hb'.1
    have hprep : preparationCallsGood G sgs t.2.1 (Finset.univ.image t.1).toList := by
      simpa only [B1,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using! hb'.2.1
    have htest : classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
        ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩ := by
      simpa only [B2,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using! hb'.2.2.1
    have hT : (∃ z,triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset z=true) →
        operationalSgsFind sgs (triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset) 3 (n*n) t.2.2.2.2.1≠none := by
      intro hm hf
      apply hb'.2.2.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm,hf⟩⟩
    have hE : edgeTriangleExists G (sourceTapeClass G sgs ets k K c τ t).movedE →
        ets.run G (sourceTapeClass G sgs ets k K c τ t).movedE (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2≠none := by
      intro hm hf
      apply hb'.2.2.2.2
      have hp := classifyScan_E_bound G sgs τ dHi dLo K c tThin t.2.2.1 t.2.2.2.1
        ⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩ (by omega) (by omega) (by omega) htest hsamp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hm,hf⟩
    exact sourceComb_good_tape_not_reject G sgs ets k K c dHi dLo τ tThin t
      (by omega) hdLo hhi hτ htri hsamp hprep htest hT hE (Finset.mem_filter.mp ht).2
  have hcard : (Finset.univ.filter (sourceCombRejects G sgs ets k K c dHi dLo τ tThin)).card ≤
      B0.card+B1.card+B2.card+B3.card+B4.card := by
    have hsub := Finset.card_le_card hs
    have h01 := Finset.card_union_le B0 B1
    have h012 := Finset.card_union_le (B0∪B1) B2
    have h0123 := Finset.card_union_le (B0∪B1∪B2) B3
    have h01234 := Finset.card_union_le (B0∪B1∪B2∪B3) B4
    omega
  exact source_five_error_budget n _ _ B0.card B1.card B2.card B3.card B4.card hn hcard h0 h1 h2 h3 h4

end Qatlib.Concepts.WalkSearch.MainResults
