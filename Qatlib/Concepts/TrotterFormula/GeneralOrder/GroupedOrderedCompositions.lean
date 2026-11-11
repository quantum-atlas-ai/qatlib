/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefined
import Mathlib.Data.Fin.Rev

/-!
# Grouped ordered compositions

The map `unparts` inverts the reversed list representation `sourceParts` of a finite
multiplicity vector. These inverse laws support `grouped_sum_last`, which reindexes a sum over
grouped compositions by separating the final positive part from the preceding multiplicities.
For background, see [ChildsEtAl2021Trotter].

## Main statements

* `sourceParts_injective`: injectivity of the multiplicity-list representation.
* `grouped_sum_last`: decomposition of a grouped composition sum by its final part.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open scoped Classical BigOperators
set_option warningAsError false

/-- The sum of the list `sourceParts s r` equals the sum of the multiplicities `r i`. -/
theorem sourceParts_sum (s : ℕ) (r : Fin s → ℕ) : (sourceParts s r).sum=∑ i,r i := by
  rw [sourceParts,List.sum_ofFn]
  calc
    _ = ∑ i : Fin s,r (Fin.revPerm i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply Fin.ext
      change s-1-i.val=s-(i.val+1)
      omega
    _ = _ := Equiv.sum_comp Fin.revPerm r

/-- The multiplicity vector obtained by reading the first `s` list positions in reverse order,
using zero for missing entries. -/
def unparts (s : ℕ) (q : List ℕ) : Fin s → ℕ := fun i => q.getD (s-1-i.val) 0

/-- Converting `sourceParts s r` back with `unparts s` recovers `r`. -/
theorem unparts_sourceParts (s : ℕ) (r : Fin s → ℕ) : unparts s (sourceParts s r)=r := by
  funext i
  rw [unparts,clause49_sourceParts_getD r (s-1-i.val) (by omega)]
  congr 1
  apply Fin.ext
  change s-1-(s-1-i.val)=i.val
  omega

/-- For a list of length `s`, converting it to multiplicities with `unparts s` and back with
`sourceParts s` recovers the list. -/
theorem sourceParts_unparts (s : ℕ) (q : List ℕ) (hq : q.length=s) : sourceParts s (unparts s q)=q := by
  apply List.ext_get
  · simp [sourceParts,hq]
  · intro n h1 h2
    have hn : n < s := by omega
    simp only [sourceParts,List.get_eq_getElem,List.getElem_ofFn]
    change q.getD (s-1-(s-1-n)) 0=q[n]
    have he : s-1-(s-1-n)=n := by omega
    rw [he,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2,Option.getD_some]

/-- The map `sourceParts s` from multiplicity vectors to lists is injective. -/
theorem sourceParts_injective (s : ℕ) : Function.Injective (sourceParts s) := by
  intro a b h
  have hh := congrArg (unparts s) h
  simpa only [unparts_sourceParts] using! hh

/-- A sum over grouped compositions of total `p` and length `s + 1` equals the sum over prefix
totals below `p` and their multiplicity vectors, appending the final part `p - n.val`. -/
theorem grouped_sum_last {E : Type*} [AddCommMonoid E] (s p : ℕ) (f : List ℕ → E) :
    (∑ q∈groupedCompositions p (s+1),f q)=
      ∑ n : Fin p,∑ r∈pfCompositions s n.val,f (sourceParts s r++[p-n.val]) := by
  rw [Finset.sum_sigma' (Finset.univ : Finset (Fin p))
    (fun n => pfCompositions s n.val) (fun n r => f (sourceParts s r++[p-n.val]))]
  symm
  apply Finset.sum_bij (fun z _ => sourceParts s z.2++[p-z.1.val])
  · rintro ⟨n,r⟩ hz
    have hr := (pfCompositions_mem r).mp (Finset.mem_sigma.mp hz).2
    apply (clause49_grouped_compositions_mem _).mpr
    refine ⟨by simp [sourceParts],?_,?_⟩
    · simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero,sourceParts_sum,hr]
      omega
    · simp only [List.getLastD_concat]
      omega
  · rintro ⟨n,r⟩ hn ⟨m,u⟩ hm he
    have hlast := congrArg (fun q : List ℕ => q.getLastD 0) he
    simp only [List.getLastD_concat] at hlast
    have hnm : n=m := by apply Fin.ext; have := n.isLt; have := m.isLt; omega
    subst m
    have hru : sourceParts s r=sourceParts s u := List.append_cancel_right he
    have hrr := sourceParts_injective s hru
    subst u
    rfl
  · intro q hq
    obtain ⟨hlen,hsum,hlast⟩ := (clause49_grouped_compositions_mem q).mp hq
    have hsplit : q.dropLast++[q.getLastD 0]=q := by
      have hne : q ≠ [] := by intro he; simp [he] at hlen
      simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
        Option.getD_some] using! List.dropLast_concat_getLast hne
    have hlen' : q.dropLast.length=s := by simp only [List.length_dropLast,hlen]; omega
    have hsum' : q.dropLast.sum+q.getLastD 0=p := by
      have hh := congrArg List.sum hsplit
      simpa only [List.sum_append,List.sum_cons,List.sum_nil,add_zero,hsum] using! hh
    let n : Fin p := ⟨q.dropLast.sum,by omega⟩
    let r : Fin s → ℕ := unparts s q.dropLast
    have hparts : sourceParts s r=q.dropLast := sourceParts_unparts s q.dropLast hlen'
    refine ⟨⟨n,r⟩,Finset.mem_sigma.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · rw [pfCompositions_mem]
      have hh := sourceParts_sum s r
      rw [hparts] at hh
      exact hh.symm
    · rw [hparts]
      have he : p-n.val=q.getLastD 0 := by dsimp [n]; omega
      rw [he]
      exact hsplit
  · intro z _
    rfl

end Qatlib.Concepts.TrotterFormula.GeneralOrder
