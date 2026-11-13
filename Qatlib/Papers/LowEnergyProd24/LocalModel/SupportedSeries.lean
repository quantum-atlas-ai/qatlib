/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Expansion

/-!
# Supported commutator expansions for selected interactions

This module iterates commutators of selected interaction sums around an arbitrary supported
matrix. The connected words in `words` track support growth and give `connected_expansion`;
their ascending-factorial count yields the estimate `nested_norm`. See [HejaziZiniArrazola2024].

## Main statements

* `words_count`: For an initial region of size at most `m * k`, the number of connected words is
  at most `(k * d)^xs.length * m.ascFactorial xs.length`.
* `connected_expansion`: For `A` supported on `s`, the nested commutator of selected sums equals
  the sum of its local-word commutators over the generated connected words.
* `nested_norm`: For nonnegative `J` and an operator supported on at most `m * k` sites, the
  selected nested commutator norm is at most `(k * d)^xs.length * m.ascFactorial xs.length *
  J^xs.length * ‖A‖`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.LowEnergyProd24.LocalModel.SupportedSeries
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Hamiltonian
variable {N R M k d : ℕ} {J : ℝ}

/-- The sum of the interaction terms indexed by the finite set `e`. -/
def selected (h : Hamiltonian N R M k d J) (e : Finset (Fin R)) :
    Matrix (Register N) (Register N) ℂ := ∑i∈e,h.term i

/-- Selecting all interaction labels gives the total Hamiltonian. -/
theorem total_selected (h : Hamiltonian N R M k d J) : h.total=selected h Finset.univ := by
  unfold Hamiltonian.total Hamiltonian.grouped Hamiltonian.labels selected
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The local nested commutator around `A` indexed by an interaction word, with the list head
outermost. -/
def op (h : Hamiltonian N R M k d J) (A : Matrix (Register N) (Register N) ℂ) : List (Fin R)→Matrix (Register N) (Register N) ℂ
  | []=>A
  | a::w=>h.term a*op h A w-op h A w*h.term a

/-- The union of the initial site set with the supports of all labels in the word. -/
def region (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) : List (Fin R)→Finset (Fin N)
  | []=>s
  | a::w=>h.support a∪region h s w

/-- If `A` is supported on `s`, its local nested commutator is supported on the union region
determined by `s` and the word. -/
theorem op_supported (h : Hamiltonian N R M k d J) (s : Finset (Fin N))
    (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) (w : List (Fin R)) :
    op h A w∈onSupport (region h s w) := by
  induction w with
  | nil=>exact hA
  | cons a w ih=>exact commutator_mem_union _ _ (h.supported a) ih

/-- If `s` has at most `m * k` sites, adjoining the interaction supports of a word gives a
region of size at most `(m + w.length) * k`. -/
theorem region_card (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) (m : ℕ) (hs : s.card ≤ m*k) (w : List (Fin R)) :
    (region h s w).card ≤ (m+w.length)*k := by
  induction w with
  | nil=>simpa only [region,List.length_nil,add_zero] using hs
  | cons a w ih=>
    simp only [region,List.length_cons]
    calc
      _ ≤ (h.support a).card+(region h s w).card := Finset.card_union_le _ _
      _ ≤ k+(m+w.length)*k := Nat.add_le_add (h.locality a) ih
      _ = (m+(w.length+1))*k := by ring

/-- For nonnegative `J`, a local nested commutator around `A` has norm at most `J^w.length *
‖A‖`. -/
theorem op_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J)
    (A : Matrix (Register N) (Register N) ℂ) (w : List (Fin R)) :
    ‖op h A w‖ ≤ J^w.length*‖A‖ := by
  induction w with
  | nil=>simp [op]
  | cons a w ih=>
    simp only [op,List.length_cons]
    calc
      _ ≤ ‖h.term a*op h A w‖+‖op h A w*h.term a‖ := norm_sub_le _ _
      _ ≤ ‖h.term a‖*‖op h A w‖+‖op h A w‖*‖h.term a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (J/2)*(J^w.length*‖A‖)+(J^w.length*‖A‖)*(J/2) := by gcongr <;> exact h.strength a
      _ = J^(w.length+1)*‖A‖ := by rw [pow_succ]; ring

/-- The labels in the selected set `e` whose interaction supports meet `s`. -/
def active (h : Hamiltonian N R M k d J) (e : Finset (Fin R)) (s : Finset (Fin N)) :
    Finset (Fin R) := e.filter (fun i=>i∈h.neighbors s)

/-- The number of active labels in any selected set is at most `s.card * d`. -/
theorem active_card (h : Hamiltonian N R M k d J) (e : Finset (Fin R)) (s : Finset (Fin N)) :
    (active h e s).card ≤ s.card*d :=
  (Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).2)).trans (h.neighbors_card s)

/-- The commutator of a selected interaction sum with an operator supported on `s` is the sum of
commutators over its active labels. -/
theorem selected_commutator (h : Hamiltonian N R M k d J) (e : Finset (Fin R)) (s : Finset (Fin N))
    (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) :
    selected h e*A-A*selected h e=∑i∈active h e s,(h.term i*A-A*h.term i) := by
  unfold selected active
  rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hn:i∈h.neighbors s
  · simp [hn]
  · have hc:=h.nonneighbor_commute s A hA i hn
    simp only [hn,if_false,hc.eq,sub_self]

/-- The connected interaction words for successive selected label sets, extending each tail by a
label whose support meets its current region. -/
def words (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) : List (Finset (Fin R))→List (List (Fin R))
  | []=>[[]]
  | e::xs=>(words h s xs).flatMap (fun w=>(active h e (region h s w)).toList.map (fun a=>a::w))

/-- Each generated connected word has length equal to the number of selected label sets. -/
theorem words_length (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) (xs : List (Finset (Fin R))) :
    ∀ w∈words h s xs,w.length=xs.length := by
  induction xs with
  | nil=>intro w hw; simp only [words,List.mem_singleton] at hw; subst w; rfl
  | cons e xs ih=>
    intro w hw
    obtain ⟨v,hv,hw⟩:=List.mem_flatMap.mp hw
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hw
    simpa only [List.length_cons] using congrArg (fun n=>n+1) (ih v hv)

/-- For an initial region of size at most `m * k`, the number of connected words is at most `(k
* d)^xs.length * m.ascFactorial xs.length`. -/
theorem words_count (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) (m : ℕ) (hs : s.card ≤ m*k)
    (xs : List (Finset (Fin R))) :
    (words h s xs).length ≤ (k*d)^xs.length*m.ascFactorial xs.length := by
  induction xs with
  | nil=>simp [words]
  | cons e xs ih=>
    rw [words,List.length_flatMap]
    have hc : ((words h s xs).map (fun w=>((active h e (region h s w)).toList.map (fun a=>a::w)).length)).sum ≤
        (words h s xs).length*((m+xs.length)*k*d) := by
      apply sum_map_bound
      intro w hw
      rw [List.length_map,Finset.length_toList]
      calc
        _ ≤ (region h s w).card*d := active_card h e _
        _ ≤ ((m+xs.length)*k)*d := Nat.mul_le_mul_right d (by simpa only [words_length h s xs w hw] using region_card h s m hs w)
    calc
      _ ≤ (words h s xs).length*((m+xs.length)*k*d) := hc
      _ ≤ ((k*d)^xs.length*m.ascFactorial xs.length)*((m+xs.length)*k*d) := Nat.mul_le_mul_right _ ih
      _ = (k*d)^(e::xs).length*m.ascFactorial (e::xs).length := by
        simp only [List.length_cons,Nat.ascFactorial_succ,pow_succ]
        ring

/-- The nested commutator of the successive selected interaction sums around `A`, with the list
head outermost. -/
def nested (h : Hamiltonian N R M k d J) (A : Matrix (Register N) (Register N) ℂ) : List (Finset (Fin R))→Matrix (Register N) (Register N) ℂ
  | []=>A
  | e::xs=>selected h e*nested h A xs-nested h A xs*selected h e

/-- For `A` supported on `s`, the nested commutator of selected sums equals the sum of its
local-word commutators over the generated connected words. -/
theorem connected_expansion (h : Hamiltonian N R M k d J) (s : Finset (Fin N))
    (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) (xs : List (Finset (Fin R))) :
    nested h A xs=((words h s xs).map (op h A)).sum := by
  induction xs with
  | nil=>simp [nested,words,op]
  | cons e xs ih=>
    rw [nested,ih,commutator_list_sum,words,flatMap_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro w hw
    rw [selected_commutator h e (region h s w) (op h A w) (op_supported h s A hA w)]
    simp only [List.map_map,op,Function.comp_def]
    simpa only [Finset.toList_toFinset] using (List.sum_toFinset (fun i=>h.term i*op h A w-op h A w*h.term i)
      (Finset.nodup_toList (active h e (region h s w))))

/-- For nonnegative `J` and an operator supported on at most `m * k` sites, the selected nested
commutator norm is at most `(k * d)^xs.length * m.ascFactorial xs.length * J^xs.length *
‖A‖`. -/
theorem nested_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (s : Finset (Fin N))
    (m : ℕ) (hs : s.card ≤ m*k) (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s)
    (xs : List (Finset (Fin R))) :
    ‖nested h A xs‖ ≤ ((k*d)^xs.length*m.ascFactorial xs.length:ℕ)*(J^xs.length*‖A‖) := by
  rw [connected_expansion h s A hA]
  calc
    _ ≤ ((words h s xs).map (fun w=>‖op h A w‖)).sum := norm_map_sum_le _ _
    _ ≤ ((words h s xs).map (fun _=>J^xs.length*‖A‖)).sum := List.sum_le_sum (fun w hw=>by
      simpa only [words_length h s xs w hw] using op_norm h hJ A w)
    _ = (words h s xs).length*(J^xs.length*‖A‖) := by
      induction words h s xs with
      | nil=>simp
      | cons w l ih=>simp only [List.map_cons,List.sum_cons,List.length_cons] at *; push_cast; rw [ih]; ring
    _ ≤ ((k*d)^xs.length*m.ascFactorial xs.length:ℕ)*(J^xs.length*‖A‖) := by gcongr; exact words_count h s m hs xs

end Qatlib.Papers.LowEnergyProd24.LocalModel.SupportedSeries
