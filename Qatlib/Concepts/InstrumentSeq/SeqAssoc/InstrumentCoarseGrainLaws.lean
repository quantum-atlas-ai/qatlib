/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Instrument coarse-graining laws

This module proves finite-sum identities for composed fibers and pairs of fibers, then applies
them to instrument outcome coarse-graining. Successive coarse-grainings agree with
coarse-graining by the composite map, both on branches and on probabilities.

The sequential laws also identify the channel obtained by forgetting outcomes and show that
separate coarse-graining of two instruments commutes with their sequential composition. The
channel interpretation follows the quantum information framework of [Wilde2017].

## Main statements

* `Instrument.coarsen_composition_laws`: composition of outcome maps preserves branches and
  probabilities.
* `Instrument.seq_coarsen_forget_laws`: sequential composition, forgetting, and coarse-graining.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.InstrumentSeq.SeqAssoc

open Matrix
open scoped ComplexOrder

/-- A finite sum over a fiber of `g ∘ f` equals the iterated sum over the corresponding fibers
of `g` and `f`. -/
theorem sum_fiber_compose {α β γ M : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] [AddCommMonoid M] (F : α → M) (f : α → β) (g : β → γ) (q : γ) :
    (∑ o ∈ Finset.univ.filter (fun o => g (f o) = q), F o)
      = (∑ o' ∈ Finset.univ.filter (fun o' => g o' = q),
          ∑ o ∈ Finset.univ.filter (fun o => f o = o'), F o) := by
  classical
  have h1 : (∑ o : α, (if g (f o) = q then F o else 0))
      = ∑ o : α, ∑ o' : β, (if g o' = q ∧ f o = o' then F o else 0) := by
    refine Finset.sum_congr rfl fun o _ => ?_
    have key : ∑ o' : β, (if g o' = q ∧ f o = o' then F o else 0)
        = (if g (f o) = q ∧ f o = f o then F o else 0) := by
      refine Finset.sum_eq_single (f o) ?_ ?_
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    calc (if g (f o) = q then F o else 0)
        = (if g (f o) = q ∧ f o = f o then F o else 0) := by simp
      _ = ∑ o' : β, (if g o' = q ∧ f o = o' then F o else 0) := key.symm
  have h2 : (∑ o' : β, (if g o' = q then (∑ o : α, (if f o = o' then F o else 0)) else 0))
      = ∑ o' : β, ∑ o : α, (if g o' = q ∧ f o = o' then F o else 0) := by
    refine Finset.sum_congr rfl fun o' _ => ?_
    by_cases h : g o' = q
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun o _ => ?_
      simp [h]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun o _ => ?_
      simp [h]
  calc (∑ o ∈ Finset.univ.filter (fun o => g (f o) = q), F o)
      = ∑ o : α, (if g (f o) = q then F o else 0) := Finset.sum_filter _ _
    _ = ∑ o : α, ∑ o' : β, (if g o' = q ∧ f o = o' then F o else 0) := h1
    _ = ∑ o' : β, ∑ o : α, (if g o' = q ∧ f o = o' then F o else 0) := Finset.sum_comm
    _ = ∑ o' : β, (if g o' = q then (∑ o : α, (if f o = o' then F o else 0)) else 0) :=
          h2.symm
    _ = (∑ o' ∈ Finset.univ.filter (fun o' => g o' = q),
          ∑ o ∈ Finset.univ.filter (fun o => f o = o'), F o) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun o' _ => ?_
          by_cases h : g o' = q
          · simp only [if_pos h]
            exact (Finset.sum_filter _ _).symm
          · simp [h]

/-- A finite sum over a fiber of the product map `(u, v)` equals the iterated sum over the
separate fibers of `u` and `v`. -/
theorem sum_fiber_pair {α β γ δ M : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    [DecidableEq δ] [AddCommMonoid M] (F : α → β → M) (u : α → γ) (v : β → δ) (a : γ)
    (b : δ) :
    (∑ x ∈ Finset.univ.filter (fun x : α × β => (u x.1, v x.2) = (a, b)), F x.1 x.2)
      = (∑ x ∈ Finset.univ.filter (fun x => u x = a),
          ∑ y ∈ Finset.univ.filter (fun y => v y = b), F x y) := by
  classical
  have hsplit : (∑ x : α × β, (if (u x.1, v x.2) = (a, b) then F x.1 x.2 else 0))
      = ∑ x : α, ∑ y : β, (if u x = a ∧ v y = b then F x y else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Prod.mk.injEq]
  have hsplit' : (∑ x : α, (if u x = a then (∑ y : β, (if v y = b then F x y else 0)) else 0))
      = ∑ x : α, ∑ y : β, (if u x = a ∧ v y = b then F x y else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : u x = a
    · rw [if_pos hx]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [hx]
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hx]
  calc (∑ x ∈ Finset.univ.filter (fun x : α × β => (u x.1, v x.2) = (a, b)), F x.1 x.2)
      = ∑ x : α × β, (if (u x.1, v x.2) = (a, b) then F x.1 x.2 else 0) :=
          Finset.sum_filter _ _
    _ = ∑ x : α, ∑ y : β, (if u x = a ∧ v y = b then F x y else 0) := hsplit
    _ = ∑ x : α, (if u x = a then (∑ y : β, (if v y = b then F x y else 0)) else 0) :=
          hsplit'.symm
    _ = (∑ x ∈ Finset.univ.filter (fun x => u x = a),
          ∑ y ∈ Finset.univ.filter (fun y => v y = b), F x y) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : u x = a
          · simp only [if_pos hx]
            exact (Finset.sum_filter _ _).symm
          · simp [hx]

/-- Coarse-graining first by `f` and then by `g` gives the same branch maps and outcome
probabilities as coarse-graining by `g ∘ f`. -/
theorem Instrument.coarsen_composition_laws {O P Q : Type*} [Fintype O] [Fintype P]
    [DecidableEq P] [Fintype Q] [DecidableEq Q] {D E : ℕ}
    (I : Instrument O D E) (f : O → P) (g : P → Q) (q : Q) (ρ : Operator D) :
    ((I.coarsen f).coarsen g).branch q = (I.coarsen (g ∘ f)).branch q ∧
    instrumentProb ((I.coarsen f).coarsen g) ρ q =
      instrumentProb (I.coarsen (g ∘ f)) ρ q := by
  have hpt : ∀ ρ' : Operator D,
      ((I.coarsen f).coarsen g).branch q ρ' = (I.coarsen (g ∘ f)).branch q ρ' := by
    intro ρ'
    simp only [Instrument.coarsen, LinearMap.sum_apply, Function.comp_apply]
    exact (sum_fiber_compose (fun o => I.branch o ρ') f g q).symm
  exact ⟨LinearMap.ext hpt, by
    show (Matrix.trace (((I.coarsen f).coarsen g).branch q ρ)).re
      = (Matrix.trace ((I.coarsen (g ∘ f)).branch q ρ)).re
    rw [hpt ρ]⟩

/-- Forgetting the outcomes of sequential instruments gives the composite of their forgotten
channels. Coarse-graining the paired outcomes agrees branchwise with sequencing the
separately coarse-grained instruments. -/
theorem Instrument.seq_coarsen_forget_laws {O P O' P' : Type*} [Fintype O] [Fintype P]
    [DecidableEq P] [Fintype O'] [DecidableEq O'] [Fintype P'] [DecidableEq P']
    {D E F : ℕ} (I : Instrument O D E) (J : Instrument P E F)
    (f : O → O') (g : P → P') (o : O') (p : P') (ρ : Operator D) :
    (I.seq J).forget.map ρ = (J.forget.comp I.forget).map ρ ∧
    ((I.seq J).coarsen (fun op => (f op.1, g op.2))).branch (o, p) =
      ((I.coarsen f).seq (J.coarsen g)).branch (o, p) := by
  refine ⟨?_, ?_⟩
  · calc (I.seq J).forget.map ρ
        = ∑ op : O × P, J.branch op.2 (I.branch op.1 ρ) := by
            rw [Instrument.forget_apply]
            refine Finset.sum_congr rfl fun op _ => ?_
            rfl
      _ = ∑ x : O, ∑ y : P, J.branch y (I.branch x ρ) :=
            Fintype.sum_prod_type' (fun x y => J.branch y (I.branch x ρ))
      _ = J.forget.map (∑ x : O, I.branch x ρ) := by
            simp only [map_sum, Instrument.forget_apply]
      _ = (J.forget.comp I.forget).map ρ := by
            rw [show (J.forget.comp I.forget).map ρ
              = J.forget.map (I.forget.map ρ) from rfl]
            exact congrArg J.forget.map (Instrument.forget_apply I ρ).symm
  · ext ρ'
    simp only [Instrument.coarsen, Instrument.seq, LinearMap.comp_apply,
      LinearMap.sum_apply, map_sum]
    rw [sum_fiber_pair (fun x y => J.branch y (I.branch x ρ')) f g o p, Finset.sum_comm]

end Qatlib.Concepts.InstrumentSeq.SeqAssoc
