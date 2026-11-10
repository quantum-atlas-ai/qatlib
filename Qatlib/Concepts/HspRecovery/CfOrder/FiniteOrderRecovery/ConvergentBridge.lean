/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Max
import Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery.OrderDecode

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery

open Finset

def cfPartialsAux : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | k + 1, num, den@(d + 1) => (num / (d + 1)) :: cfPartialsAux k (d + 1) (num % (d + 1))

def cfPartials (num den : ℕ) : List ℕ := cfPartialsAux (den + 1) num den

def convPairs : List ℕ → ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | a :: as, p2, p1 =>
      (a * p1.1 + p2.1, a * p1.2 + p2.2)
        :: convPairs as p1 (a * p1.1 + p2.1, a * p1.2 + p2.2)

def cfDenoms (j Q : ℕ) : List ℕ :=
  ((convPairs (cfPartials j Q) (0, 1) (1, 0)).map Prod.snd)
    |>.filter (fun d => 2 ≤ d)

def d1Find {G : Type*} [Group G] [Fintype G] [DecidableEq G] (u : G)
    (ds : List ℕ) : Option ℕ :=
  ds.find? (fun d => decide (u ^ d = 1))

theorem d1Find_eq_orderOf {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {u : G} {ds : List ℕ}
    (hpos : ∀ d ∈ ds, 0 < d) (hw : ds.Pairwise (· < ·)) :
    d1Find u ds = some (orderOf u) ↔ orderOf u ∈ ds := by
  constructor
  · exact List.mem_of_find?_eq_some
  · intro hmem
    induction ds with
    | nil => cases hmem
    | cons d ds ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hw
      by_cases hr : orderOf u = d
      · subst hr
        rw [d1Find, List.find?_cons,
          show decide (u ^ orderOf u = 1) = true by simp [pow_orderOf_eq_one]]
      · have hmem' : orderOf u ∈ ds := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h hr
          · exact h
        have hdlt : d < orderOf u := hhead _ hmem'
        have hnpos : ¬ (u ^ d = 1) := by
          intro hp
          have hdvd : orderOf u ∣ d := (pow_eq_one_iff_orderOf_dvd u d).mp hp
          have hle : orderOf u ≤ d := Nat.le_of_dvd (hpos d (by simp)) hdvd
          omega
        rw [d1Find, List.find?_cons,
          show decide (u ^ d = 1) = false by simp [hnpos]]
        exact ih (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')) htail hmem'

def d2bSet {G : Type*} [Group G] [Fintype G] [DecidableEq G] (u : G)
    (ds : List ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter
    (fun y => 0 < y ∧ decide (u ^ y = 1) ∧ ds.any (fun d => d ∣ y))

theorem d2bSet_eq_candSet {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (u : G) (ds : List ℕ) (N : ℕ) :
    d2bSet u ds N = d2bCandSet (orderOf u) ds N := by
  ext y
  simp only [d2bSet, d2bCandSet, mem_filter, mem_range, decide_eq_true_eq]
  rw [pow_eq_one_iff_orderOf_dvd]

theorem d2bSet_min_char {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (u : G) (ds : List ℕ) (N : ℕ) (h0 : 0 < orderOf u)
    (hb : orderOf u < N) (hne : (d2bSet u ds N).Nonempty) :
    (d2bSet u ds N).min' hne = orderOf u ↔ ∃ d ∈ ds, d ∣ orderOf u := by
  have hlift : ∀ s t : Finset ℕ, s = t → ∀ H1 : s.Nonempty, ∀ H2 : t.Nonempty,
      s.min' H1 = t.min' H2 := by
    intro s t he H1 H2
    subst he
    rfl
  have heq : d2bSet u ds N = d2bCandSet (orderOf u) ds N :=
    d2bSet_eq_candSet u ds N
  have hne' : (d2bCandSet (orderOf u) ds N).Nonempty := heq ▸ hne
  rw [hlift _ _ heq hne hne']
  exact d2bCandSet_min _ _ _ h0 hb hne'

end Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery
