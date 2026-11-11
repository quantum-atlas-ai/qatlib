/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Nested

/-!
# Counting connected interaction words

The recursive list `words` enumerates local interaction words by extending through terms whose
supports meet the current region. The bounds `words_count` and `grouped_words_count` control the
number of words by a factorial times powers of the locality and degree bounds. See
[HejaziZiniArrazola2024].

## Main statements

* `words_length`: Every generated interaction word has the same length as its group-index list.
* `words_count`: The number of generated words for one local seed is at most `(k * d)^xs.length
  * xs.length!`.
* `grouped_words_count`: If the seed group has at most `L` labels, the total number of generated
  words across its seeds is at most `L * (k * d)^xs.length * xs.length!`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
variable {N R M k d : ℕ} {J : ℝ}

/-- If every value of a natural-valued function on a list is at most `C`, the sum of those
values is at most the list length times `C`. -/
theorem sum_map_bound {α : Type*} (l : List α) (f : α→ℕ) (C : ℕ) (hf : ∀ a∈l,f a ≤ C) :
    (l.map f).sum ≤ l.length*C := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      _ ≤ C+l.length*C := Nat.add_le_add (hf a (List.mem_cons_self)) (ih (fun b hb=>hf b (List.mem_cons_of_mem a hb)))
      _ = (l.length+1)*C := by ring

/-- The recursively generated local interaction words for a group-index list, extending each
tail by labels in the indicated group whose support meets the tail region. -/
def words (h : Hamiltonian N R M k d J) (seed : Fin R) : List (Fin M)→List (List (Fin R))
  | []=>[[]]
  | m::xs=>(h.words seed xs).flatMap (fun w=>(h.active m (h.region seed w)).toList.map (fun a=>a::w))

/-- Every generated interaction word has the same length as its group-index list. -/
theorem words_length (h : Hamiltonian N R M k d J) (seed : Fin R) (xs : List (Fin M)) :
    ∀ w∈h.words seed xs,w.length=xs.length := by
  induction xs with
  | nil=>
    intro w hw
    simp only [words,List.mem_singleton] at hw
    subst w
    rfl
  | cons m xs ih=>
    intro w hw
    obtain ⟨v,hv,hw⟩:=List.mem_flatMap.mp hw
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hw
    simpa only [List.length_cons] using congrArg (fun n=>n+1) (ih v hv)

/-- The number of generated words for one local seed is at most `(k * d)^xs.length *
xs.length!`. -/
theorem words_count (h : Hamiltonian N R M k d J) (seed : Fin R) (xs : List (Fin M)) :
    (h.words seed xs).length ≤ (k*d)^xs.length*xs.length.factorial := by
  induction xs with
  | nil=>simp [words]
  | cons m xs ih=>
    simp only [words,List.length_flatMap]
    have hs : ((h.words seed xs).map (fun w=>((h.active m (h.region seed w)).toList.map (fun a=>a::w)).length)).sum ≤
        (h.words seed xs).length*((xs.length+1)*k*d) := by
      apply sum_map_bound
      intro w hw
      rw [List.length_map,Finset.length_toList]
      calc
        _ ≤ (h.region seed w).card*d := h.active_card m _
        _ ≤ ((xs.length+1)*k)*d := Nat.mul_le_mul_right d (by simpa only [h.words_length seed xs w hw] using h.region_card seed w)
    calc
      _ ≤ (h.words seed xs).length*((xs.length+1)*k*d) := hs
      _ ≤ ((k*d)^xs.length*xs.length.factorial)*((xs.length+1)*k*d) := Nat.mul_le_mul_right _ ih
      _ = (k*d)^(m::xs).length*(m::xs).length.factorial := by
        simp only [List.length_cons,Nat.factorial_succ,pow_succ]
        ring

/-- If the seed group has at most `L` labels, the total number of generated words across its
seeds is at most `L * (k * d)^xs.length * xs.length!`. See [HejaziZiniArrazola2024]. -/
theorem grouped_words_count (h : Hamiltonian N R M k d J) (m : Fin M) (xs : List (Fin M))
    (L : ℕ) (hL : (h.labels m).card ≤ L) :
    ((h.labels m).toList.flatMap (fun seed=>h.words seed xs)).length ≤ L*(k*d)^xs.length*xs.length.factorial := by
  rw [List.length_flatMap]
  have hs:=sum_map_bound (h.labels m).toList (fun seed=>(h.words seed xs).length)
    ((k*d)^xs.length*xs.length.factorial) (fun seed _=>h.words_count seed xs)
  rw [Finset.length_toList] at hs
  exact hs.trans (by nlinarith [Nat.mul_le_mul_right ((k*d)^xs.length*xs.length.factorial) hL])

end Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
