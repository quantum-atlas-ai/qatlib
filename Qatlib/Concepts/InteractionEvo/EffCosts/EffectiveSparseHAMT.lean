/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics

/-!
# Unitarity of sparse Hamiltonian oracles

This module proves that the sparse value oracle `effectiveSparseOH` and the sparse location
oracle `effectiveSparseOF` are unitary. Their definitions use reversible value XOR and location
permutations, the sparse-oracle interfaces used in the setting of [LowWiebe2018].

## Main statements

* `effectiveSparseOH_unitary`: unitarity of the value oracle.
* `effectiveSparseOF_unitary`: unitarity of the location oracle.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.InteractionEvo.EffCosts
open Matrix

/-- The sparse value oracle is unitary for every supplied value table. This verifies one oracle
interface used in the setting of [Low and Wiebe, Lemma 8][LowWiebe2018]. -/
theorem effectiveSparseOH_unitary (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    effectiveSparseOH p S ∈ Matrix.unitaryGroup (Reg (p.nd+2*p.ns+2*p.np)) ℂ := by
  let f : Reg (p.nd+2*p.ns+2*p.np) → Reg (p.nd+2*p.ns+2*p.np) := fun x =>
    let r : Reg p.nd := fun i => x ⟨i.val,by omega⟩
    let j : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
    let k : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
    fun i => if h : p.nd+2*p.ns ≤ i.val then
      x i ^^ S.values r j k ⟨i.val-(p.nd+2*p.ns),by omega⟩ else x i
  have hpre (x : Reg (p.nd+2*p.ns+2*p.np)) (i : Fin (p.nd+2*p.ns+2*p.np))
      (hi : i.val<p.nd+2*p.ns) : f x i=x i := by
    dsimp [f]
    rw [dif_neg (by omega)]
  have hr (x : Reg (p.nd+2*p.ns+2*p.np)) :
      (fun i : Fin p.nd => f x ⟨i.val,by omega⟩) = (fun i : Fin p.nd => x ⟨i.val,by omega⟩) := by
    funext i
    exact hpre x _ (by (try dsimp only); have := i.isLt; omega)
  have hj (x : Reg (p.nd+2*p.ns+2*p.np)) :
      (fun i : Fin p.ns => f x ⟨p.nd+i.val,by omega⟩) = (fun i : Fin p.ns => x ⟨p.nd+i.val,by omega⟩) := by
    funext i
    exact hpre x _ (by (try dsimp only); have := i.isLt; omega)
  have hk (x : Reg (p.nd+2*p.ns+2*p.np)) :
      (fun i : Fin p.ns => f x ⟨p.nd+p.ns+i.val,by omega⟩) =
        (fun i : Fin p.ns => x ⟨p.nd+p.ns+i.val,by omega⟩) := by
    funext i
    exact hpre x _ (by (try dsimp only); have := i.isLt; omega)
  have hi : Function.Involutive f := by
    intro x
    funext i
    by_cases h : p.nd+2*p.ns ≤ i.val
    · change (if h' : p.nd+2*p.ns ≤ i.val then f x i ^^
        S.values (fun j => f x ⟨j.val,by omega⟩)
          (fun j => f x ⟨p.nd+j.val,by omega⟩)
          (fun j => f x ⟨p.nd+p.ns+j.val,by omega⟩) ⟨i.val-(p.nd+2*p.ns),by omega⟩ else f x i) = x i
      rw [dif_pos h,hr,hj,hk]
      dsimp [f]
      rw [dif_pos h]
      simp
    · rw [hpre (f x) i (by omega),hpre x i (by omega)]
  exact permMatrix_unitary hi

/-- The sparse location oracle is unitary for every supplied family of location permutations. -/
theorem effectiveSparseOF_unitary (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    effectiveSparseOF p S ∈ Matrix.unitaryGroup (Reg (p.nd+2*p.ns)) ℂ := by
  let r (x : Reg (p.nd+2*p.ns)) : Reg p.nd := fun i => x ⟨i.val,by omega⟩
  let j (x : Reg (p.nd+2*p.ns)) : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
  let l (x : Reg (p.nd+2*p.ns)) : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
  let f : Reg (p.nd+2*p.ns) → Reg (p.nd+2*p.ns) := fun x i =>
    if h : p.nd+p.ns ≤ i.val then
      S.locations (r x) (j x) (l x) ⟨i.val-(p.nd+p.ns),by omega⟩ else x i
  have hpre (x : Reg (p.nd+2*p.ns)) (i : Fin (p.nd+2*p.ns))
      (hi : i.val<p.nd+p.ns) : f x i=x i := by
    dsimp [f]
    rw [dif_neg (by omega)]
  have hr (x : Reg (p.nd+2*p.ns)) : r (f x)=r x := by
    funext i
    exact hpre x _ (by (try dsimp only); have := i.isLt; omega)
  have hj (x : Reg (p.nd+2*p.ns)) : j (f x)=j x := by
    funext i
    exact hpre x _ (by (try dsimp only); have := i.isLt; omega)
  have hl (x : Reg (p.nd+2*p.ns)) : l (f x)=S.locations (r x) (j x) (l x) := by
    funext i
    dsimp only [l,f]
    rw [dif_pos (by omega)]
    apply congrArg (S.locations (r x) (j x) (l x))
    apply Fin.ext
    simp
  have hf : Function.Injective f := by
    intro x y h
    have hre : r x=r y := by rw [← hr x,← hr y,h]
    have hje : j x=j y := by rw [← hj x,← hj y,h]
    have hle : l x=l y := by
      apply (S.locations (r x) (j x)).injective
      rw [← hl x,h,hl y,hre,hje]
    funext i
    by_cases hi : i.val<p.nd+p.ns
    · have hh := congrArg (fun z => z i) h
      (try dsimp only at hh)
      rwa [hpre x i hi,hpre y i hi] at hh
    · have hh := congrFun hle ⟨i.val-(p.nd+p.ns),by have := i.isLt; omega⟩
      dsimp [l] at hh
      convert! hh using 1 <;> congr 1 <;> apply Fin.ext <;> (try dsimp only) <;> omega
  exact permMatrix_unitary_of_injective hf

end Qatlib.Concepts.InteractionEvo.EffCosts
