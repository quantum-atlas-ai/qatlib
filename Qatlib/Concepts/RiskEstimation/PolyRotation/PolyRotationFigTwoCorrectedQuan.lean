/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoCorrectedStat
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoModelCorrected

/-!
# Correctness and size of the Figure 2 rotation program

This module proves that the subset expansion of a polynomial angle reconstructs that angle on
binary registers. It establishes the corrected circuit's basis-state semantics, exact cost, and
the gate bound `31 * (k + 1) * n ^ (k + 1)`.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `figTwoProgramAngle_polynomial`: For a polynomial of degree at most `k`, the Figure 2 program
  angle equals the polynomial evaluated at the register's binary value.
* `riskPolyRotationFigTwoCorrected`: The corrected Figure 2 circuit realizes polynomial angles
  exactly and satisfies the stated exact length formula and polynomial gate bound; see
  [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation
open Matrix Polynomial
open scoped Classical BigOperators

/-- The sum over sublists of `a :: l` splits into sums over sublists excluding and including the
head. -/
private theorem figSublist_sum_cons {α : Type} (a : α) (l : List α) (F : List α → ℝ) :
    ((a::l).sublists.map F).sum=(l.sublists.map F).sum+(l.sublists.map fun t=>F (a::t)).sum := by
  rw [List.sublists_cons,List.bind_eq_flatMap]
  generalize l.sublists=ts
  induction ts with
  | nil=>simp
  | cons t ts ih=>simp [List.flatMap_cons,ih];ring

/-- For a list without repetitions, summing a function of the underlying finite set over all
sublists equals summing over the powerset. -/
theorem figSublist_sum_powerset {α : Type} [DecidableEq α] (l : List α) (hn : l.Nodup)
    (F : Finset α → ℝ) : (l.sublists.map fun t=>F t.toFinset).sum=∑ S∈l.toFinset.powerset,F S := by
  induction l generalizing F with
  | nil=>simp
  | cons a l ih=>
    have ha : a∉l.toFinset := by simpa using! (List.nodup_cons.mp hn).1
    have hl : l.Nodup := (List.nodup_cons.mp hn).2
    rw [figSublist_sum_cons,List.toFinset_cons,Finset.sum_powerset_insert ha]
    rw [ih hl F]
    have he : (l.sublists.map fun t=>F (a::t).toFinset).sum=
        (l.sublists.map fun t=>F (insert a t.toFinset)).sum := by simp
    rw [he,ih hl (fun S=>F (insert a S))]

/-- Filtering paired sublists by a Boolean conjunction retains both forms when the new head
passes the test, and only the form without the head otherwise. -/
private theorem figSublist_filter_pairs {α : Type} (a : α) (ts : List (List α)) (f : α → Bool) :
    (ts.flatMap fun t=>[t,a::t]).filter (fun t=>t.all f)=
      if f a then (ts.filter fun t=>t.all f).flatMap (fun t=>[t,a::t]) else ts.filter (fun t=>t.all f) := by
  induction ts with
  | nil=>simp
  | cons t ts ih=>
    cases ha : f a <;> cases ht : t.all f <;> simp [List.flatMap_cons,List.all_cons,ha,ht,ih]

/-- The sublists on which every element passes a Boolean test are exactly the sublists of the
filtered original list. -/
theorem figSublist_filter_all {α : Type} (l : List α) (f : α → Bool) :
    l.sublists.filter (fun t=>t.all f)=(l.filter f).sublists := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    rw [List.sublists_cons,List.bind_eq_flatMap,figSublist_filter_pairs]
    cases ha : f a <;> simp [ha,ih,List.sublists_cons]

/-- Filtering a list does not change its mapped sum when every removed term has value zero. -/
private theorem figList_sum_filter_zero {α : Type} (l : List α) (P : α → Bool) (F : α → ℝ)
    (hz : ∀ a∈l,P a=false → F a=0) : ((l.filter P).map F).sum=(l.map F).sum := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    have hl : ∀ b∈l,P b=false → F b=0 := fun b hb=>hz b (List.mem_cons_of_mem _ hb)
    cases ha : P a with
    | false=>simp [ha,ih hl,hz a (by simp) ha]
    | true=>simp [ha,ih hl]

/-- A polynomial subset angle vanishes for any selected sublist whose length exceeds the
polynomial degree bound. -/
theorem figTwoAngle_sublist_vanish {n : ℕ} (p : Polynomial ℝ) (k : ℕ) (hp : p.natDegree ≤ k)
    (l : List (Fin n)) (hl : l∈(figTwoDataList n).sublists) (hk : k < l.length) :
    figTwoAngle (fun x : Reg n=>p.eval (figTwoRegEval x : ℝ)) l.toFinset=0 := by
  have hn : l.Nodup := (List.mem_sublists.mp hl).nodup (List.nodup_finRange n)
  have hc : k < l.toFinset.card := by rw [List.toFinset_card_of_nodup hn];exact hk
  rw [figTwoAngle_polynomial_cube]
  exact figCubeCoeff_polynomial_vanish (fun i : Fin n=>(2 : ℝ)^i.val) k p l.toFinset hp hc

/-- For a polynomial of degree at most `k`, the Figure 2 program angle equals the polynomial
evaluated at the register's binary value. -/
theorem figTwoProgramAngle_polynomial (n k : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ k) (x : Reg n) :
    figTwoProgramAngle k (fun y=>p.eval (figTwoRegEval y : ℝ)) x=p.eval (figTwoRegEval x : ℝ) := by
  let g : Reg n → ℝ:=fun y=>p.eval (figTwoRegEval y : ℝ)
  let F : List (Fin n) → ℝ:=fun l=>figTwoAngle g l.toFinset
  have hswap : (((figTwoDataList n).sublists.filter (fun l=>l.length ≤ k)).filter (fun l=>l.all x))=
      (((figTwoDataList n).sublists.filter (fun l=>l.all x)).filter (fun l=>l.length ≤ k)) := by
    simp only [List.filter_filter]
    congr 1
    funext l
    exact Bool.and_comm _ _
  have hz : ∀ l∈((figTwoDataList n).sublists.filter (fun l=>l.all x)),
      decide (l.length ≤ k)=false → F l=0 := by
    intro l hl hk
    have hgt : k < l.length := by simp only [decide_eq_false_iff_not] at hk;omega
    exact figTwoAngle_sublist_vanish p k hp l (List.mem_filter.mp hl).1 hgt
  unfold figTwoProgramAngle figTwoTerms
  rw [hswap,figList_sum_filter_zero _ _ F hz,figSublist_filter_all]
  change ((((figTwoDataList n).filter x).sublists).map (fun l=>figTwoAngle g l.toFinset)).sum=_
  have hn : ((figTwoDataList n).filter x).Nodup := (List.nodup_finRange n).filter _
  rw [figSublist_sum_powerset ((figTwoDataList n).filter x) hn (fun S=>figTwoAngle g S)]
  change (∑ S∈((figTwoDataList n).filter x).toFinset.powerset,
      figCubeCoeff (fun T=>g (fun i=>decide (i∈T))) S)=_
  rw [figCubeCoeff_inversion]
  have he : (fun i : Fin n=>decide (i∈((figTwoDataList n).filter x).toFinset))=x := by
    funext i
    cases hx : x i <;> simp [figTwoDataList,hx]
  rw [he]

/-- The number of lists of length at most `k` equals the sum of their counts at each length from
zero to `k`. -/
private theorem figList_lengths_partition {α : Type} (ts : List (List α)) (k : ℕ) :
    (ts.filter (fun l=>l.length ≤ k)).length=
      ∑ j∈Finset.range (k+1),(ts.filter (fun l=>l.length=j)).length := by
  induction ts with
  | nil=>simp
  | cons l ts ih=>
    have he (j : ℕ) : ((l::ts).filter (fun t=>t.length=j)).length=
        (if l.length=j then 1 else 0)+(ts.filter (fun t=>t.length=j)).length := by
      by_cases hj : l.length=j <;> simp [hj,Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib,← ih]
    have hc : (∑ j∈Finset.range (k+1),if l.length=j then (1 : ℕ) else 0)=
        if l.length ≤ k then 1 else 0 := by simp
    rw [hc]
    by_cases hl : l.length ≤ k <;> simp [hl,Nat.add_comm]

/-- A list without repetitions has exactly `l.length.choose j` sublists of length `j`. -/
private theorem figSublist_length_layer {α : Type} [DecidableEq α] (l : List α) (hn : l.Nodup) (j : ℕ) :
    (l.sublists.filter (fun t=>t.length=j)).length=l.length.choose j := by
  have h1 : (l.sublists.filter (fun t=>t.length=j)).Nodup := hn.sublists.filter _
  have h2 : (List.sublistsLen j l).Nodup := List.nodup_sublistsLen j hn
  have he : (l.sublists.filter (fun t=>t.length=j)).Perm (List.sublistsLen j l) := by
    apply (List.perm_ext_iff_of_nodup h1 h2).mpr
    intro t
    simp [List.mem_sublistsLen]
  rw [he.length_eq,List.length_sublistsLen]

/-- For `n ≥ 1`, the number of Figure 2 terms of degree at most `k` is at most `(k + 1) * n ^
k`. -/
theorem figTwoTerms_length_bound (n k : ℕ) (hn : 1 ≤ n) :
    (figTwoTerms (n := n) k).length ≤ (k+1)*n^k := by
  unfold figTwoTerms
  rw [figList_lengths_partition]
  have hd : (figTwoDataList n).Nodup := List.nodup_finRange n
  simp_rw [figSublist_length_layer (figTwoDataList n) hd]
  simp only [figTwoDataList,List.length_finRange]
  calc
    _ ≤ ∑ j∈Finset.range (k+1),n^k := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by simp only [Finset.mem_range] at hj;omega
      exact (Nat.choose_le_pow n j).trans (Nat.pow_le_pow_right hn hjk)
    _ = _ := by simp

/-- A sum of natural-valued list terms each bounded by `C` is at most `C * l.length`. -/
private theorem figList_sum_upper {α : Type} (l : List α) (F : α → ℕ) (C : ℕ)
    (h : ∀ a∈l,F a ≤ C) : (l.map F).sum ≤ C*l.length := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    have hh:=ih (fun b hb=>h b (List.mem_cons_of_mem _ hb))
    have ha:=h a (by simp)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- For `n ≥ 1`, the sum of the selected subset-rotation costs is at most `31 * (k + 1) * n ^ (k
+ 1)`. -/
theorem figTwoTerms_gate_bound (n k : ℕ) (hn : 1 ≤ n) :
    ((figTwoTerms (n := n) k).map (fun l=>multiKnownCost l.length)).sum ≤ 31*(k+1)*n^(k+1) := by
  have hterm : ∀ l∈figTwoTerms (n := n) k,multiKnownCost l.length ≤ 31*n := by
    intro l hl
    have hsub : l.Sublist (figTwoDataList n) := List.mem_sublists.mp (List.mem_filter.mp hl).1
    have hlen : l.length ≤ n := by simpa [figTwoDataList] using! hsub.length_le
    unfold multiKnownCost
    split_ifs <;> omega
  calc
    _ ≤ (31*n)*(figTwoTerms (n := n) k).length := figList_sum_upper _ _ _ hterm
    _ ≤ (31*n)*((k+1)*n^k) := Nat.mul_le_mul_left _ (figTwoTerms_length_bound n k hn)
    _ = _ := by rw [pow_succ];ring

/-- Every selected Figure 2 control subset satisfies the corrected frame with the designated
target and work wires. -/
theorem figTwo_subset_frame (n k : ℕ) (l : List (Fin n)) (hl : l∈figTwoTerms (n := n) k) :
    subsetRotationFrameCorrected (l.map (figTwoDataWire n)) (figTwoTargetWire n) (figTwoWorkWires n) := by
  have hsub : l.Sublist (figTwoDataList n) := List.mem_sublists.mp (List.mem_filter.mp hl).1
  have hnd : l.Nodup := hsub.nodup (List.nodup_finRange n)
  have hi : Function.Injective (figTwoDataWire n) := by
    intro i j h
    apply Fin.ext
    have he : (figTwoDataWire n i).val=(figTwoDataWire n j).val := congrArg Fin.val h
    exact he
  have hwi : Function.Injective (fun j : Fin (n-1)=> (⟨n+1+j.val,by omega⟩ : Fin (n+1+(n-1)))) := by
    intro i j h
    apply Fin.ext
    have he:=congrArg Fin.val h
    simp only at he
    omega
  refine ⟨hnd.map hi,(List.nodup_finRange (n-1)).map hwi,?_,?_,?_,?_⟩
  · have hlen : l.length ≤ n := by simpa [figTwoDataList] using! hsub.length_le
    simp only [List.length_map,figTwoWorkWires,List.length_map,List.length_finRange]
    omega
  · intro w hw
    obtain ⟨i,hiw,rfl⟩:=List.mem_map.mp hw
    intro h
    have he:=congrArg Fin.val h
    simp only [figTwoDataWire,figTwoTargetWire] at he
    omega
  · intro w hw
    obtain ⟨j,hjw,rfl⟩:=List.mem_map.mp hw
    intro h
    have he:=congrArg Fin.val h
    simp only [figTwoTargetWire] at he
    omega
  · intro w hw u hu
    obtain ⟨i,hiw,rfl⟩:=List.mem_map.mp hw
    obtain ⟨j,hjw,rfl⟩:=List.mem_map.mp hu
    intro h
    have he:=congrArg Fin.val h
    simp only [figTwoDataWire] at he
    omega

/-- The corrected Figure 2 program is legal and its length is the sum of `multiKnownCost` over
the selected subsets. -/
theorem figTwoProgramCorrected_cost (n k : ℕ) (g : Reg n → ℝ) :
    reflectionLegal (figTwoProgramCorrected k g) ∧
    (figTwoProgramCorrected k g).length=((figTwoTerms (n := n) k).map fun l=>multiKnownCost l.length).sum := by
  have hf : ∀ p∈((figTwoTerms (n := n) k).map (fun l=>(l.map (figTwoDataWire n),figTwoAngle g l.toFinset))),
      subsetRotationFrameCorrected p.1 (figTwoTargetWire n) (figTwoWorkWires n) := by
    intro p hp
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hp
    exact figTwo_subset_frame n k l hl
  have hs:=figtwo_rotation_program_semantics_and_cost_corrected (n+1+(n-1))
    (figTwoTargetWire n) (figTwoWorkWires n) _ hf
  refine ⟨hs.1,?_⟩
  simpa [figTwoProgramCorrected,List.map_map,Function.comp_def] using! hs.2.1

/-- Testing the embedded data-control wires equals testing the corresponding original data bits. -/
theorem figTwo_subset_control (n : ℕ) (l : List (Fin n)) (x : Reg n) (b : Bool) (w : Reg (n-1)) :
    subsetControlTrue (l.map (figTwoDataWire n)) ((multiKnownSplit n).symm ((x,b),w))=l.all x := by
  unfold subsetControlTrue
  simp only [List.all_map]
  congr 1
  funext i
  exact multiKnownJoin_control n x b w i

/-- The sum of enabled angles on the expanded register equals `figTwoProgramAngle` on its data
register. -/
theorem figTwo_angle_wire (n k : ℕ) (g : Reg n → ℝ) (x : Reg n) (b : Bool) (w : Reg (n-1)) :
    subsetRotationAngle ((figTwoTerms (n := n) k).map (fun l=>(l.map (figTwoDataWire n),figTwoAngle g l.toFinset)))
      ((multiKnownSplit n).symm ((x,b),w))=figTwoProgramAngle k g x := by
  unfold subsetRotationAngle figTwoProgramAngle
  rw [List.filter_map]
  simp only [figTwo_subset_control,List.map_map,Function.comp_def]

/-- On an initial data ket with false flag and clean work wires, the corrected Figure 2 program
rotates the flag by `figTwoProgramAngle` and restores the work register. -/
theorem figTwoProgramCorrected_state (n k : ℕ) (g : Reg n → ℝ) (x : Reg n) :
    let embed:=fun b : Bool=>(multiKnownSplit n).symm ((x,b),fun _=>false)
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (figTwoProgramCorrected k g)) (Ket (embed false))=
      ∑ b : Bool,((qubitEulerRotation (figTwoProgramAngle k g x))*ᵥKet false) b • Ket (embed b) := by
  (try dsimp only)
  let X : Reg (n+1+(n-1)):=(multiKnownSplit n).symm ((x,false),fun _=>false)
  have hf : ∀ p∈((figTwoTerms (n := n) k).map (fun l=>(l.map (figTwoDataWire n),figTwoAngle g l.toFinset))),
      subsetRotationFrameCorrected p.1 (figTwoTargetWire n) (figTwoWorkWires n) := by
    intro p hp
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hp
    exact figTwo_subset_frame n k l hl
  have hs:=figtwo_rotation_program_semantics_and_cost_corrected (n+1+(n-1))
    (figTwoTargetWire n) (figTwoWorkWires n) _ hf
  have hc : ∀ w∈figTwoWorkWires n,X w=false := by
    intro w hw
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hw
    exact multiKnownJoin_work n x false (fun _=>false) j
  have hxt : X (figTwoTargetWire n)=false := multiKnownJoin_target n x false (fun _=>false)
  have hk : multiWireState (figTwoTargetWire n) X (Ket false)=Ket X := by
    simpa only [hxt] using! multiWireState_ket (figTwoTargetWire n) X
  have hrun:=hs.2.2 X (Ket false) hc
  rw [hk,figTwo_angle_wire] at hrun
  have he := multiKnownJoin_wireState n x false (fun _=>false)
    (ApplyGate (qubitEulerRotation (figTwoProgramAngle k g x)) (Ket false))
  have hw : multiWireState (figTwoTargetWire n) X
      (ApplyGate (qubitEulerRotation (figTwoProgramAngle k g x)) (Ket false))=
      ∑ b : Bool,((qubitEulerRotation (figTwoProgramAngle k g x))*ᵥKet false) b •
        Ket ((multiKnownSplit n).symm ((x,b),fun _=>false)) := by
    simpa only [X,ApplyGate] using! he
  exact hrun.trans hw

/-- The corrected Figure 2 circuit realizes polynomial angles exactly and satisfies the stated
exact length formula and polynomial gate bound; see [WoernerEgger2019]. -/
theorem riskPolyRotationFigTwoCorrected : PolyRotationFigTwoCorrected := by
  intro n k p hp
  (try dsimp only)
  let g : Reg n → ℝ:=fun y=>p.eval (figTwoRegEval y : ℝ)
  have ha:=figTwoProgramAngle_polynomial n k p hp
  have hc:=figTwoProgramCorrected_cost n k g
  refine ⟨ha,?_,hc.2,?_⟩
  · intro x
    have hs:=figTwoProgramCorrected_state n k g x
    rw [ha x] at hs
    exact hs
  · intro hn
    rw [hc.2]
    exact figTwoTerms_gate_bound n k hn

end Qatlib.Concepts.RiskEstimation.PolyRotation
