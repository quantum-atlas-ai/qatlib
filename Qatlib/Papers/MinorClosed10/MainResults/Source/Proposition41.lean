/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects

set_option backward.isDefEq.respectTransparency false

/-!
# Vertex-Cover Numbers of Paths and Subdivided Claws

This module formalizes Proposition 4.1 of Childs and Kothari giving exact
formulas for the minimum vertex-cover number of `k`-edge paths `PathGraph k`
and subdivided claws `ClawGraph d1 d2 d3`.

## Main statements

* `proposition41`: Proposition 4.1, establishing `vc (PathGraph k) = (k + 1) / 2`,
  `vc (ClawGraph d1 d2 d3) = (d1 + d2 + d3) / 2` when all three branch lengths
  are even, and `vc (ClawGraph d1 d2 d3) = 1 + d1 / 2 + d2 / 2 + d3 / 2` when at
  least one branch length is odd.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 4, Proposition 4.1, p. 18.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source

open Qatlib.Papers.MinorClosed10.MainResults

private lemma vc_le_cover {V : Type} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) :
    vc G ≤ (S.card : ℕ∞) := by
  classical
  simpa [vc] using (show G.IsVertexCover (S : Set V) from hS).vertexCoverNum_le

private lemma matching_le_vc {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (V × V))
    (hE : ∀ p ∈ M, G.Adj p.1 p.2)
    (hD : ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      ({p.1, p.2} : Finset V) ∩ {q.1, q.2} = ∅) :
    (M.card : ℕ∞) ≤ vc G := by
  classical
  change _ ≤ G.vertexCoverNum
  rw [SimpleGraph.vertexCoverNum]
  refine le_iInf₂ fun S hS => ?_
  let f : V × V → V := fun p => if p.1 ∈ S then p.1 else p.2
  have hf (p : V × V) : f p ∈ ({p.1, p.2} : Finset V) := by
    dsimp [f]
    split <;> simp
  have hc : M.card ≤ S.toFinset.card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have := hS (hE p hp)
      change f p ∈ S.toFinset
      rw [Set.mem_toFinset]
      dsimp [f]
      split <;> tauto
    · intro p hp q hq hpq
      by_contra hne
      have hmem := Finset.mem_inter.mpr ⟨hf p, hpq.symm ▸ hf q⟩
      rw [hD p hp q hq hne] at hmem
      exact Finset.notMem_empty _ hmem
  rw [Set.encard_eq_coe_toFinset_card]
  exact_mod_cast hc

/-- An indexed cover and a matching with the same number of members certify optimality. -/
private lemma vc_eq_of_certificate {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (c a b : I → V) (hc : Function.Injective c)
    (hC : ∀ u v, G.Adj u v → (∃ i, c i = u) ∨ ∃ i, c i = v)
    (hE : ∀ i, G.Adj (a i) (b i))
    (hD : ∀ i j, a i = a j ∨ a i = b j ∨ b i = a j ∨ b i = b j → i = j) :
    vc G = (Fintype.card I : ℕ∞) := by
  classical
  let S := Finset.univ.image c
  let e : I → V × V := fun i => (a i, b i)
  let M := Finset.univ.image e
  have he : Function.Injective e := fun i j h => hD i j (Or.inl (congrArg Prod.fst h))
  have hScard : S.card = Fintype.card I := Finset.card_image_of_injective _ hc
  have hMcard : M.card = Fintype.card I := Finset.card_image_of_injective _ he
  apply le_antisymm
  · rw [← hScard]
    apply vc_le_cover G S
    intro u v huv
    rcases hC u v huv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [S]
  · rw [← hMcard]
    apply matching_le_vc G M
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact hE i
    · intro p hp q hq hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, e] at hv
      have hij : i = j := hD i j (by rcases hv with ⟨h | h, h' | h'⟩ <;> simp_all)
      exact hne (congrArg e hij)

private lemma path_vc (k : ℕ) :
    vc (PathGraph k) = (((k + 1) / 2 : ℕ) : ℕ∞) := by
  let a : Fin ((k + 1) / 2) → Fin (k + 1) := fun t => ⟨2 * t.val, by omega⟩
  let b : Fin ((k + 1) / 2) → Fin (k + 1) := fun t => ⟨2 * t.val + 1, by omega⟩
  suffices vc (PathGraph k) = (Fintype.card (Fin ((k + 1) / 2)) : ℕ∞) by
    simpa using this
  apply vc_eq_of_certificate (PathGraph k) b a b
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [b] at this
    omega
  · intro u v huv
    have h := (SimpleGraph.fromRel_adj _ _ _).mp huv
    change u ≠ v ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val) at h
    have odd_mem (w : Fin (k + 1)) (hw : w.val % 2 = 1) : ∃ i, b i = w := by
      refine ⟨⟨w.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [b]
      omega
    by_cases hu : u.val % 2 = 1
    · exact Or.inl (odd_mem u hu)
    · exact Or.inr (odd_mem v (by omega))
  · intro i
    rw [PathGraph, SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have := congrArg Fin.val h
      dsimp [a, b] at this
      omega
    · exact Or.inl rfl
  · intro i j h
    apply Fin.ext
    rcases h with h | h | h | h <;>
      have hv := congrArg Fin.val h <;> dsimp [a, b] at hv <;> omega

private def armGraph (d : Fin 3 → ℕ) : SimpleGraph (Unit ⊕ Sigma (fun i => Fin (d i))) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | .inl _, .inr ⟨_, j⟩ => j.val = 0
    | .inr ⟨i, j⟩, .inr ⟨i', j'⟩ => i = i' ∧ j.val + 1 = j'.val
    | _, _ => False)

private lemma armGraph_eq_claw (d1 d2 d3 : ℕ) :
    armGraph ![d1, d2, d3] = ClawGraph d1 d2 d3 := by
  ext u v
  rcases u with u | ⟨i, j⟩ <;> rcases v with v | ⟨i', j'⟩ <;> rfl

private lemma arm_eq {d : Fin 3 → ℕ} {i j : Fin 3} {u : Fin (d i)} {v : Fin (d j)}
    (h : (Sum.inr ⟨i, u⟩ : Unit ⊕ Sigma (fun r => Fin (d r))) = .inr ⟨j, v⟩) :
    i = j ∧ u.val = v.val := by
  exact ⟨congrArg Sigma.fst (Sum.inr.inj h),
    congrArg (fun x : Sigma (fun r => Fin (d r)) => x.2.val) (Sum.inr.inj h)⟩

private lemma arm_adj {d : Fin 3 → ℕ} (i : Fin 3) (u v : Fin (d i))
    (h : u.val + 1 = v.val) :
    (armGraph d).Adj (.inr ⟨i, u⟩) (.inr ⟨i, v⟩) := by
  rw [armGraph, SimpleGraph.fromRel_adj]
  exact ⟨fun he => by have := (arm_eq he).2; omega, Or.inl ⟨rfl, h⟩⟩

private lemma even_arm_vc (d : Fin 3 → ℕ) (hd : ∀ i, Even (d i)) :
    vc (armGraph d) = (Fintype.card (Sigma (fun i => Fin (d i / 2))) : ℕ∞) := by
  let a : (Sigma fun i => Fin (d i / 2)) → Unit ⊕ Sigma (fun i => Fin (d i)) :=
    fun ⟨i, t⟩ => .inr ⟨i, ⟨2 * t.val, by have := t.isLt; omega⟩⟩
  let b : (Sigma fun i => Fin (d i / 2)) → Unit ⊕ Sigma (fun i => Fin (d i)) :=
    fun ⟨i, t⟩ => .inr ⟨i, ⟨2 * t.val + 1, by have := t.isLt; omega⟩⟩
  apply vc_eq_of_certificate (armGraph d) a a b
  · rintro ⟨i, t⟩ ⟨j, u⟩ h
    obtain ⟨hij, hval⟩ := arm_eq h
    dsimp [a] at hij hval
    subst j
    congr 1
    apply Fin.ext
    omega
  · intro u v huv
    have h := (SimpleGraph.fromRel_adj _ _ _).mp huv
    have mem (i : Fin 3) (j : Fin (d i)) (hj : j.val % 2 = 0) :
        ∃ t, a t = .inr ⟨i, j⟩ := by
      obtain ⟨n, hn⟩ := hd i
      refine ⟨⟨i, ⟨j.val / 2, by omega⟩⟩, ?_⟩
      dsimp [a]
      congr 2
      apply Fin.ext
      dsimp
      omega
    cases u with
    | inl u =>
      cases v with
      | inl v => simp at h
      | inr v =>
        rcases v with ⟨i, j⟩
        have hj : j.val = 0 := by simpa [armGraph] using h.2
        exact Or.inr (mem i j (by omega))
    | inr u =>
      rcases u with ⟨i, j⟩
      cases v with
      | inl v =>
        have hj : j.val = 0 := by simpa [armGraph] using h.2
        exact Or.inl (mem i j (by omega))
      | inr v =>
        rcases v with ⟨i', j'⟩
        have hh : (i = i' ∧ j.val + 1 = j'.val) ∨
            (i' = i ∧ j'.val + 1 = j.val) := by simpa [armGraph] using h.2
        by_cases hj : j.val % 2 = 0
        · exact Or.inl (mem i j hj)
        · exact Or.inr (mem i' j' (by omega))
  · rintro ⟨i, t⟩
    exact arm_adj i _ _ rfl
  · rintro ⟨i, t⟩ ⟨j, u⟩ h
    rcases h with h | h | h | h <;>
      obtain ⟨hij, hval⟩ := arm_eq h <;>
      dsimp [a, b] at hij hval <;> subst j <;>
      congr 1 <;> apply Fin.ext <;> omega

private lemma odd_arm_vc (d : Fin 3 → ℕ) (r : Fin 3) (hr : Odd (d r)) :
    vc (armGraph d) = (Fintype.card (Option (Sigma (fun i => Fin (d i / 2)))) : ℕ∞) := by
  have hodd : d r % 2 = 1 := by obtain ⟨n, hn⟩ := hr; omega
  let c : Option (Sigma fun i => Fin (d i / 2)) → Unit ⊕ Sigma (fun i => Fin (d i))
    | none => .inl ()
    | some ⟨i, t⟩ => .inr ⟨i, ⟨2 * t.val + 1, by have := t.isLt; omega⟩⟩
  let a : Option (Sigma fun i => Fin (d i / 2)) → Unit ⊕ Sigma (fun i => Fin (d i))
    | none => .inl ()
    | some ⟨i, t⟩ => .inr ⟨i, ⟨2 * t.val + (if i = r then 1 else 0), by
        have := t.isLt
        split <;> omega⟩⟩
  let b : Option (Sigma fun i => Fin (d i / 2)) → Unit ⊕ Sigma (fun i => Fin (d i))
    | none => .inr ⟨r, ⟨0, by omega⟩⟩
    | some ⟨i, t⟩ => .inr ⟨i, ⟨2 * t.val + (if i = r then 2 else 1), by
        have := t.isLt
        split
        · rename_i hi
          subst i
          omega
        · omega⟩⟩
  apply vc_eq_of_certificate (armGraph d) c a b
  · rintro (_ | ⟨i, t⟩) (_ | ⟨j, u⟩) h
    · rfl
    · cases h
    · cases h
    · obtain ⟨hij, hval⟩ := arm_eq h
      dsimp [c] at hij hval
      subst j
      congr 2
      apply Fin.ext
      omega
  · intro u v huv
    have h := (SimpleGraph.fromRel_adj _ _ _).mp huv
    have mem (i : Fin 3) (j : Fin (d i)) (hj : j.val % 2 = 1) :
        ∃ t, c t = .inr ⟨i, j⟩ := by
      refine ⟨some ⟨i, ⟨j.val / 2, by omega⟩⟩, ?_⟩
      dsimp [c]
      congr 2
      apply Fin.ext
      dsimp
      omega
    cases u with
    | inl u => exact Or.inl ⟨none, by cases u; rfl⟩
    | inr u =>
      rcases u with ⟨i, j⟩
      cases v with
      | inl v => exact Or.inr ⟨none, by cases v; rfl⟩
      | inr v =>
        rcases v with ⟨i', j'⟩
        have hh : (i = i' ∧ j.val + 1 = j'.val) ∨
            (i' = i ∧ j'.val + 1 = j.val) := by simpa [armGraph] using h.2
        by_cases hj : j.val % 2 = 1
        · exact Or.inl (mem i j hj)
        · exact Or.inr (mem i' j' (by omega))
  · rintro (_ | ⟨i, t⟩)
    · simp [armGraph, SimpleGraph.fromRel_adj, a, b]
    · apply arm_adj
      dsimp [a, b]
      by_cases hi : i = r <;> simp [hi]
  · rintro (_ | ⟨i, t⟩) (_ | ⟨j, u⟩) h
    · rfl
    · rcases h with h | h | h | h
      · cases h
      · cases h
      · obtain ⟨hij, hval⟩ := arm_eq h
        dsimp [a, b] at hij hval
        subst j
        simp at hval
      · obtain ⟨hij, hval⟩ := arm_eq h
        dsimp [b] at hij hval
        subst j
        simp at hval
    · rcases h with h | h | h | h
      · cases h
      · obtain ⟨hij, hval⟩ := arm_eq h
        dsimp [a, b] at hij hval
        subst i
        simp at hval
      · cases h
      · obtain ⟨hij, hval⟩ := arm_eq h
        dsimp [b] at hij hval
        subst i
        simp at hval
    · rcases h with h | h | h | h <;>
        obtain ⟨hij, hval⟩ := arm_eq h <;>
        dsimp [a, b] at hij hval <;> subst j <;>
        congr 2 <;> apply Fin.ext <;>
        (by_cases hi : i = r <;> simp [hi] at hval <;> omega)

/-- Proposition 4.1: exact vertex-cover numbers for paths and subdivided claws. -/
theorem proposition41 :
    (∀ k : ℕ, vc (PathGraph k) = (((k + 1) / 2 : ℕ) : ℕ∞)) ∧
    (∀ d1 d2 d3 : ℕ, Even d1 → Even d2 → Even d3 →
      vc (ClawGraph d1 d2 d3) = (((d1 + d2 + d3) / 2 : ℕ) : ℕ∞)) ∧
    (∀ d1 d2 d3 : ℕ, (Odd d1 ∨ Odd d2 ∨ Odd d3) →
      vc (ClawGraph d1 d2 d3) = ((1 + d1 / 2 + d2 / 2 + d3 / 2 : ℕ) : ℕ∞)) := by
  refine ⟨path_vc, ?_, ?_⟩
  · intro d1 d2 d3 h1 h2 h3
    have he : ∀ i : Fin 3, Even (![d1, d2, d3] i) := by
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
    have hc : Fintype.card (Sigma (fun i : Fin 3 => Fin (![d1, d2, d3] i / 2))) =
        (d1 + d2 + d3) / 2 := by
      simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
      obtain ⟨n1, hn1⟩ := h1
      obtain ⟨n2, hn2⟩ := h2
      obtain ⟨n3, hn3⟩ := h3
      omega
    simpa only [hc, armGraph_eq_claw] using even_arm_vc ![d1, d2, d3] he
  · intro d1 d2 d3 h
    obtain ⟨r, hr⟩ : ∃ r : Fin 3, Odd (![d1, d2, d3] r) := by
      rcases h with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    have hc : Fintype.card (Option (Sigma (fun i : Fin 3 => Fin (![d1, d2, d3] i / 2)))) =
        1 + d1 / 2 + d2 / 2 + d3 / 2 := by
      simp only [Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      omega
    simpa only [hc, armGraph_eq_claw] using odd_arm_vc ![d1, d2, d3] r hr

end Qatlib.Papers.MinorClosed10.MainResults.Source
