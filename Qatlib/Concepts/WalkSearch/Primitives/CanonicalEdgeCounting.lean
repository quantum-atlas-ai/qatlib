/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.GraphVocabulary
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

def canonicalPairs (n : ℕ) : Finset (Fin n×Fin n) := Finset.univ.filter (fun e=>e.1<e.2)

theorem canonical_pair_vertexset_injective (n : ℕ) :
    Set.InjOn (fun e : Fin n×Fin n=>({e.1,e.2}:Finset (Fin n))) (canonicalPairs n) := by
  intro ⟨a,b⟩ he ⟨c,d⟩ hf hh
  change ({a,b}:Finset (Fin n))={c,d} at hh
  have hab : a<b := (Finset.mem_filter.mp he).2
  have hcd : c<d := (Finset.mem_filter.mp hf).2
  have ha : a=c ∨ a=d := by
    have hx : a∈({c,d}:Finset (Fin n)) := by rw [← hh];simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hx
  have hb : b=c ∨ b=d := by
    have hx : b∈({c,d}:Finset (Fin n)) := by rw [← hh];simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hx
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · exact Prod.ext ha hb
  · omega
  · omega

theorem canonicalPairs_card_le_choose (n : ℕ) : (canonicalPairs n).card≤n.choose 2 := by
  let f := fun e : Fin n×Fin n=>({e.1,e.2}:Finset (Fin n))
  have hi : (canonicalPairs n).image f⊆(Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro s hs
    obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp hs
    have hab : a<b := (Finset.mem_filter.mp he).2
    simp only [f,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    exact Finset.card_pair hab.ne
  calc _=((canonicalPairs n).image f).card := (Finset.card_image_of_injOn (canonical_pair_vertexset_injective n)).symm
       _≤((Finset.univ : Finset (Fin n)).powersetCard 2).card := Finset.card_le_card hi
       _=n.choose 2 := by rw [Finset.card_powersetCard];simp
end Qatlib.Concepts.WalkSearch.Primitives
