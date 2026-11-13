/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Theorem4Quan

/-!
# A checker amplification counterexample

Constructs a collision solver with one failing seed and a noisy-search implementation that
selects marked vertices exactly. On the three-vertex triangle these primitives refute
`triCheckSpec`, exposing a composition obstruction in the bounded-error search setting of
[HoyerMoscaDeWolf2003].

## Main statements

* `triCheckSpec_amplification_obstruction`: The checker specification `triCheckSpec` fails for
  the three-vertex triangle with the supplied collision and exact marked-search primitives at
  parameters `r' = 1` and `c₀ = 4`.

## References

* [Hoyer, Mosca and de Wolf, 2003][HoyerMoscaDeWolf2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- A zero-cost collision solver that returns no witness for seed zero when the domain size is
at most three, and otherwise chooses a satisfying witness whenever one exists. -/
def oneBadCollisionSolver : KCollisionSolver where
  seed := Fin 4
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 1
  κ := 1
  run := fun {n _k} _r R _s _u _c ρ =>
    if h : ∃ t,R t=true then
      if n≤3 ∧ ρ=0 then none else some (Classical.choose h)
    else none
  cost := fun {_n _k} _r _R _s _u _c _ρ => 0
  sound := by
    intro n k r R s u c ρ t ht
    split at ht
    · rename_i h
      split at ht
      · cases ht
      · cases ht
        exact Classical.choose_spec h
    · cases ht
  reject := by
    intro n k r R s u c ρ hR
    have hn : ¬∃ t,R t=true := by rintro ⟨t,ht⟩; rw [hR t] at ht; cases ht
    simp [hn]
  finds := by
    intro n k r R s u c hR
    by_cases hn : n≤3
    · have hs : (Finset.univ.filter fun ρ : Fin 4 =>
          (if h : ∃ t,R t=true then if n≤3 ∧ ρ=0 then none else some (Classical.choose h) else none)=none)={0} := by
        ext ρ
        simp [hR,hn]
      rw [hs]
      simp only [Finset.card_singleton,one_mul,pow_one,Fintype.card_fin]
      omega
    · simp [hR,hn]
  charges := by intros; simp

/-- A zero-cost noisy-search implementation that ignores the supplied test and returns a marked
vertex whenever one exists, preferring vertex zero when marked. -/
def exactMarkedNoisySearch : NoisySearch where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 4
  κ := 1
  run := fun {N} marked _test _tcost _floor _ρ =>
    if hN : 0<N then
      if marked ⟨0,hN⟩ then some ⟨0,hN⟩
      else if h : ∃ v,marked v=true then some (Classical.choose h) else none
    else none
  cost := fun {_N} _marked _test _tcost _floor _ρ => 0
  sound := by
    intro N marked test tcost floor ρ v ht
    split at ht
    · split at ht
      · rename_i h
        cases ht
        exact h
      · split at ht
        · rename_i h
          cases ht
          exact Classical.choose_spec h
        · cases ht
    · cases ht
  reject := by
    intro N marked test tcost floor ρ hR
    have hn : ¬∃ v,marked v=true := by rintro ⟨v,hv⟩; rw [hR v] at hv; cases hv
    split
    · rename_i hN
      simp [hR ⟨0,hN⟩]
    · rfl
  finds := by
    intro N marked test tcost floor hR _
    have hN : 0<N := by
      obtain ⟨v,_⟩ := hR; exact Nat.pos_of_ne_zero (by intro h; subst N; exact Fin.elim0 v)
    by_cases hm : marked ⟨0,hN⟩=true
    · simp [hN,hm]
    · simp [hN,hR,hm]
  charges := by intros; simp

/-- The Boolean adjacency relation on three vertices that holds exactly for distinct vertices. -/
def threeVertexTriangle (a b : Fin 3) : Bool := decide (a≠b)

/-- The three-vertex triangle adjacency relation is false on every diagonal pair. -/
theorem threeVertexTriangle_loopless (a : Fin 3) : threeVertexTriangle a a=false := by
  simp [threeVertexTriangle]

/-- The three-vertex triangle adjacency relation is symmetric. -/
theorem threeVertexTriangle_symm (a b : Fin 3) : threeVertexTriangle a b=threeVertexTriangle b a := by
  simp [threeVertexTriangle,ne_comm]

/-- The checker specification `triCheckSpec` fails for the three-vertex triangle with the
supplied collision and exact marked-search primitives at parameters `r' = 1` and `c₀ = 4`. -/
theorem triCheckSpec_amplification_obstruction :
    ¬triCheckSpec threeVertexTriangle Finset.univ oneBadCollisionSolver exactMarkedNoisySearch 1 4 := by
  intro h
  have htriangle : ∃ v : Fin 3,∃ u₁∈(Finset.univ : Finset (Fin 3)),∃ u₂∈Finset.univ,
      u₁≠u₂ ∧ threeVertexTriangle v u₁=true ∧ threeVertexTriangle v u₂=true ∧ threeVertexTriangle u₁ u₂=true := by
    refine ⟨0,1,Finset.mem_univ _,2,Finset.mem_univ _,?_⟩
    norm_num [threeVertexTriangle]
  have hzero : (decide (∃ u₁∈(Finset.univ : Finset (Fin 3)),∃ u₂∈Finset.univ,
      u₁≠u₂ ∧ threeVertexTriangle 0 u₁ ∧ threeVertexTriangle 0 u₂ ∧ threeVertexTriangle u₁ u₂) : Bool)=true := by
    simp only [decide_eq_true_eq]
    refine ⟨1,Finset.mem_univ _,2,Finset.mem_univ _,?_⟩
    norm_num [threeVertexTriangle]
  have hbad (τ : Fin 13 → Fin 4) (hτ : τ 0=0) :
      (triCheck threeVertexTriangle Finset.univ oneBadCollisionSolver exactMarkedNoisySearch 1 4
        (@extSeed 13 (Fin 4) inferInstance τ) ()).1=none := by
    simp only [triCheck,exactMarkedNoisySearch,show (0 : ℕ)<3 by decide,↓reduceDIte,show (⟨0,by decide⟩ : Fin 3)=(0 : Fin 3) by rfl,hzero,
      ↓reduceIte,Fin.val_zero,zero_mul,extSeed,show (0 : ℕ)<13 by decide,↓reduceDIte]
    simp only [oneBadCollisionSolver,Fintype.card_coe,Finset.card_univ,Fintype.card_fin,
      show (3 : ℕ)≤3 by decide]
    simp only [show (⟨0,by decide⟩ : Fin 13)=(0 : Fin 13) by rfl,hτ,true_and,↓reduceIte]
    simp
  have hcount : (Finset.univ.filter fun τ : Fin 13 → Fin 4 => τ 0=0).card=4^12 := by
    simpa only [Fintype.piFinset_univ,Fintype.card_fin,Finset.card_univ] using
      Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset (Fin 4)) (0 : Fin 13) (Finset.mem_univ (0 : Fin 4))
  have hsubset : (Finset.univ.filter fun ρ : Unit × (Fin 13 → Fin 4) => ρ.2 0=0)⊆
      (Finset.univ.filter fun ρ : Unit × (Fin 13 → Fin 4) =>
        (triCheck threeVertexTriangle Finset.univ oneBadCollisionSolver exactMarkedNoisySearch 1 4
          (@extSeed 13 (Fin 4) inferInstance ρ.2) ρ.1).1=none) := by
    intro ρ hρ
    have hrho : ρ.1=() := Subsingleton.elim _ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrho ▸ hbad ρ.2 (Finset.mem_filter.mp hρ).2⟩
  have hprod : (Finset.univ.filter fun ρ : Unit × (Fin 13 → Fin 4) => ρ.2 0=0).card=4^12 := by
    have hs : (Finset.univ.filter fun ρ : Unit × (Fin 13 → Fin 4) => ρ.2 0=0)=
        Finset.univ.product (Finset.univ.filter fun τ : Fin 13 → Fin 4 => τ 0=0) := by ext ⟨⟨⟩, τ⟩; simp
    rw [hs,Finset.product_eq_sprod,Finset.card_product,hcount]
    simp
  have hb := h.2.1 htriangle
  have hl := Finset.card_le_card hsubset
  rw [hprod] at hl
  change _≤_ at hb
  have hseed : @Fintype.card exactMarkedNoisySearch.seed exactMarkedNoisySearch.seedFin=1 := rfl
  have hseed4 : @Fintype.card oneBadCollisionSolver.seed oneBadCollisionSolver.seedFin=4 := rfl
  simp only [Fintype.card_fun,Fintype.card_fin,hseed,hseed4] at hb
  simp only [show oneBadCollisionSolver.cExp=1 by rfl,show exactMarkedNoisySearch.cExp=4 by rfl,mul_one,min_self] at hb
  have hcontra := (Nat.mul_le_mul_right (4^4) hl).trans hb
  norm_num at hcontra
end Qatlib.Concepts.WalkSearch.Primitives
