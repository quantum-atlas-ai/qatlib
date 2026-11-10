/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

set_option linter.unusedSectionVars false

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

def eRegSplitToF (n : ℕ) (v : Reg (n + 2)) : Reg n × Reg 2 :=
  (fun k => v (k.castLE (by omega : n ≤ n + 2)),
    fun f => v ⟨n + (f : Fin 2).val, by omega⟩)

def eRegSplitFromF (n : ℕ) (p : Reg n × Reg 2) : Reg (n + 2) :=
  fun q =>
    if h : (q : Fin (n + 2)).val < n then p.1 ⟨(q : Fin (n + 2)).val, h⟩
    else p.2 ⟨(q : Fin (n + 2)).val - n, by omega⟩

theorem eRegSplitFromF_apply (n : ℕ) (p : Reg n × Reg 2) (q : Fin (n + 2)) :
    eRegSplitFromF n p q =
      (if h : (q : Fin (n + 2)).val < n then p.1 ⟨(q : Fin (n + 2)).val, h⟩
    else p.2 ⟨(q : Fin (n + 2)).val - n, by omega⟩) := rfl

theorem eRegSplitFromF_left (n : ℕ) (v : Reg (n + 2)) :
    eRegSplitFromF n (eRegSplitToF n v) = v := by
  funext q
  have hq : (q : Fin (n + 2)).val < n + 2 := q.isLt
  rw [eRegSplitFromF_apply]
  by_cases h1 : (q : Fin (n + 2)).val < n
  · rw [dif_pos h1]
    show (eRegSplitToF n v).1 ⟨(q : Fin (n + 2)).val, h1⟩ = v q
    unfold eRegSplitToF
    show v ((⟨(q : Fin (n + 2)).val, h1⟩ : Fin n).castLE (by omega : n ≤ n + 2)) = v q
    have hv : ((⟨(q : Fin (n + 2)).val, h1⟩ : Fin n).castLE (by omega : n ≤ n + 2)) = q := by
      apply Fin.ext
      rw [Fin.val_castLE]
    rw [hv]
  · rw [dif_neg h1]
    show (eRegSplitToF n v).2 ⟨(q : Fin (n + 2)).val - n, by omega⟩ = v q
    unfold eRegSplitToF
    show v ⟨n + ((⟨(q : Fin (n + 2)).val - n, by omega⟩ : Fin 2)).val, by omega⟩ = v q
    refine congrArg v ?_
    apply Fin.ext
    show n + ((q : Fin (n + 2)).val - n) = (q : Fin (n + 2)).val
    omega

theorem eRegSplitFromF_right (n : ℕ) (p : Reg n × Reg 2) :
    eRegSplitToF n (eRegSplitFromF n p) = p := by
  refine Prod.ext (funext fun k => ?_) (funext fun f => ?_)
  · show (eRegSplitFromF n p) (k.castLE (by omega : n ≤ n + 2)) = p.1 k
    rw [eRegSplitFromF_apply,
      dif_pos (by rw [Fin.val_castLE]; exact k.isLt)]
    show p.1 ⟨(k : ℕ), k.isLt⟩ = p.1 k
    rfl
  · show (eRegSplitFromF n p) ⟨n + (f : Fin 2).val, by omega⟩ = p.2 f
    rw [eRegSplitFromF_apply,
      dif_neg (show ¬(n + (f : Fin 2).val < n) from by have := f.isLt; omega)]
    refine congrArg p.2 ?_
    apply Fin.ext
    show (n + (f : Fin 2).val) - n = (f : Fin 2).val
    have := f.isLt
    omega

def eRegSplit (n : ℕ) : Reg (n + 2) ≃ Reg n × Reg 2 :=
  ⟨eRegSplitToF n, eRegSplitFromF n, eRegSplitFromF_left n, eRegSplitFromF_right n⟩

theorem eRegSplit_fst (n : ℕ) (v : Reg (n + 2)) (k : Fin n) :
    (eRegSplit n v).1 k = v (k.castLE (by omega : n ≤ n + 2)) := rfl

theorem eRegSplit_snd (n : ℕ) (v : Reg (n + 2)) (f : Fin 2) :
    (eRegSplit n v).2 f = v ⟨n + (f : Fin 2).val, by omega⟩ := rfl

theorem eRegSplit_symm_of_lt {n : ℕ} {m : ℕ} (hm : m < n) (p : Reg n × Reg 2) :
    (eRegSplit n).symm p ⟨m, by omega⟩ = p.1 ⟨m, hm⟩ := by
  show (eRegSplitFromF n p) ⟨m, by omega⟩ = p.1 ⟨m, hm⟩
  rw [eRegSplitFromF_apply, dif_pos hm]

theorem eRegSplit_symm_of_ge {n : ℕ} {m : ℕ} (hm : n ≤ m) (hm2 : m < n + 2)
    (p : Reg n × Reg 2) :
    (eRegSplit n).symm p ⟨m, hm2⟩ = p.2 ⟨m - n, by omega⟩ := by
  show (eRegSplitFromF n p) ⟨m, hm2⟩ = p.2 ⟨m - n, by omega⟩
  rw [eRegSplitFromF_apply, dif_neg (show ¬(m < n) by omega)]

def networkFrameVec (n : ℕ) (w : Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm (w, fun _ => false)

theorem networkFrameVec_apply (n : ℕ) (w : Reg n) (q : Fin (n + 2)) :
    networkFrameVec n w q
      = if h : (q : Fin (n + 2)).val < n then w ⟨(q : Fin (n + 2)).val, h⟩ else false := by
  by_cases hq : (q : Fin (n + 2)).val < n
  · rw [networkFrameVec, eRegSplit_symm_of_lt hq, dif_pos hq]
  · have hge : n ≤ (q : Fin (n + 2)).val := by omega
    have hlt : (q : Fin (n + 2)).val < n + 2 := q.isLt
    rw [networkFrameVec, eRegSplit_symm_of_ge hge hlt, dif_neg hq]

def networkCzSpec (lo hi : ℕ) (k : ℕ) : ℕ :=
  k + (if k < lo then 0 else if k + 1 < hi then 1 else 2)

def networkCzSlot (lo hi : ℕ) (m : ℕ) : ℕ :=
  m - (if lo < m then 1 else 0) - (if hi < m then 1 else 0)

theorem networkCzSpec_slot (lo hi k : ℕ) (h1 : lo < hi) :
    networkCzSlot lo hi (networkCzSpec lo hi k) = k := by
  unfold networkCzSpec networkCzSlot
  split_ifs <;> omega

theorem networkCzSlot_spec (lo hi m : ℕ) (h1 : lo < hi) (hm1 : m ≠ lo) (hm2 : m ≠ hi) :
    networkCzSpec lo hi (networkCzSlot lo hi m) = m := by
  unfold networkCzSpec networkCzSlot
  split_ifs <;> omega

theorem networkCzSpec_lt (n lo hi k : ℕ) (h1 : lo < hi) (h2 : hi < n) (hk : k < n - 2) :
    networkCzSpec lo hi k < n := by
  unfold networkCzSpec
  split_ifs <;> omega

theorem networkCzSlot_lt (n lo hi m : ℕ) (h1 : lo < hi) (h2 : hi < n) (hm : m < n)
    (hm1 : m ≠ lo) (hm2 : m ≠ hi) : networkCzSlot lo hi m < n - 2 := by
  unfold networkCzSlot
  split_ifs <;> omega

theorem networkCzSpec_ne (lo hi k : ℕ) (h1 : lo < hi) :
    networkCzSpec lo hi k ≠ lo ∧ networkCzSpec lo hi k ≠ hi := by
  unfold networkCzSpec
  split_ifs <;> omega

def networkWireWireVec (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg n :=
  fun k => if k = i then p.1.1 else p.2 k

theorem networkWireWireVec_apply (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) (k : Fin n) :
    networkWireWireVec n i p k = (if k = i then p.1.1 else p.2 k) := rfl

def networkWireRouteToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    (networkWireWireVec n i p, ![p.1.2, p.2 i])

def networkWireRouteFromF (n : ℕ) (i : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 i, (eRegSplit n v).2 0),
    fun k : Fin n => if k = i then (eRegSplit n v).2 1 else (eRegSplit n v).1 k)

def networkWireOutToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    ((fun k : Fin n => if k = i then p.1.1 else p.2 k), ![p.2 i, p.1.2])

def networkWireOutFromF (n : ℕ) (i : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 i, (eRegSplit n v).2 1),
    fun k : Fin n => if k = i then (eRegSplit n v).2 0 else (eRegSplit n v).1 k)

theorem networkWireRouteFromF_fst_fst (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireRouteFromF n i v).1).1 = (eRegSplit n v).1 i := rfl

theorem networkWireRouteFromF_fst_snd (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireRouteFromF n i v).1).2 = (eRegSplit n v).2 0 := rfl

theorem networkWireRouteFromF_snd_apply (n : ℕ) (i : Fin n) (v : Reg (n + 2)) (k : Fin n) :
    (networkWireRouteFromF n i v).2 k
      = if k = i then (eRegSplit n v).2 1 else (eRegSplit n v).1 k := rfl

theorem networkWireRoute_left (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) :
    networkWireRouteFromF n i (networkWireRouteToF n i p) = p := by
  have hss : eRegSplit n (networkWireRouteToF n i p)
      = (networkWireWireVec n i p, ![p.1.2, p.2 i]) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkWireRouteFromF
  rw [hss]
  have h1 : networkWireWireVec n i p i = p.1.1 := by
    rw [networkWireWireVec_apply, if_pos rfl]
  have h3 : ∀ k : Fin n, (if k = i then (![p.1.2, p.2 i] : Fin 2 → Bool) 1
      else networkWireWireVec n i p k) = p.2 k := by
    intro k
    by_cases hk : k = i
    · rw [if_pos hk, hk]
      rfl
    · rw [if_neg hk, networkWireWireVec_apply, if_neg hk]
  refine Prod.ext (Prod.ext h1 rfl) (funext fun k => h3 k)

theorem networkWireRoute_right (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    networkWireRouteToF n i (networkWireRouteFromF n i v) = v := by
  refine (eRegSplit n).injective ?_
  have hss : eRegSplit n (networkWireRouteToF n i (networkWireRouteFromF n i v))
      = (networkWireWireVec n i (networkWireRouteFromF n i v),
          ![((networkWireRouteFromF n i v).1).2, (networkWireRouteFromF n i v).2 i]) :=
    (eRegSplit n).apply_symm_apply _
  rw [hss]
  refine Prod.ext (funext fun m => ?_) (funext fun f => ?_)
  · show networkWireWireVec n i (networkWireRouteFromF n i v) m = (eRegSplit n v).1 m
    rw [networkWireWireVec_apply]
    by_cases hm : m = i
    · rw [if_pos hm, networkWireRouteFromF_fst_fst, hm]
    · rw [if_neg hm, networkWireRouteFromF_snd_apply, if_neg hm]
  · fin_cases f
    · rfl
    · rw [networkWireRouteFromF_snd_apply, if_pos rfl]
      rfl

def networkWireRoute (n : ℕ) (i : Fin n) : (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkWireRouteToF n i, networkWireRouteFromF n i,
    networkWireRoute_left n i, networkWireRoute_right n i⟩

theorem networkWireOutFromF_fst_fst (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireOutFromF n i v).1).1 = (eRegSplit n v).1 i := rfl

theorem networkWireOutFromF_fst_snd (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireOutFromF n i v).1).2 = (eRegSplit n v).2 1 := rfl

theorem networkWireOutFromF_snd_apply (n : ℕ) (i : Fin n) (v : Reg (n + 2)) (k : Fin n) :
    (networkWireOutFromF n i v).2 k
      = if k = i then (eRegSplit n v).2 0 else (eRegSplit n v).1 k := rfl

theorem networkWireOut_left (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) :
    networkWireOutFromF n i (networkWireOutToF n i p) = p := by
  have hss : eRegSplit n (networkWireOutToF n i p)
      = ((fun k : Fin n => if k = i then p.1.1 else p.2 k), ![p.2 i, p.1.2]) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkWireOutFromF
  rw [hss]
  have h1 : (if (i : Fin n) = i then p.1.1 else p.2 i) = p.1.1 := by
    rw [if_pos rfl]
  have h3 : ∀ k : Fin n, (if k = i then (![p.2 i, p.1.2] : Fin 2 → Bool) 0
      else (if k = i then p.1.1 else p.2 k)) = p.2 k := by
    intro k
    by_cases hk : k = i
    · rw [if_pos hk, hk]
      rfl
    · rw [if_neg hk, if_neg hk]
  refine Prod.ext (Prod.ext h1 rfl) (funext fun k => h3 k)

theorem networkWireOut_right (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    networkWireOutToF n i (networkWireOutFromF n i v) = v := by
  refine (eRegSplit n).injective ?_
  have hss : eRegSplit n (networkWireOutToF n i (networkWireOutFromF n i v))
      = ((fun m : Fin n => if m = i then ((networkWireOutFromF n i v).1).1
            else (networkWireOutFromF n i v).2 m),
          ![(networkWireOutFromF n i v).2 i, ((networkWireOutFromF n i v).1).2]) :=
    (eRegSplit n).apply_symm_apply _
  rw [hss]
  refine Prod.ext (funext fun m => ?_) (funext fun f => ?_)
  · show (if m = i then ((networkWireOutFromF n i v).1).1
        else (networkWireOutFromF n i v).2 m) = (eRegSplit n v).1 m
    by_cases hm : m = i
    · rw [if_pos hm, networkWireOutFromF_fst_fst, hm]
    · rw [if_neg hm, networkWireOutFromF_snd_apply, if_neg hm]
  · fin_cases f
    · rw [networkWireOutFromF_snd_apply, if_pos rfl]
      rfl
    · rfl

def networkWireOutEquiv (n : ℕ) (i : Fin n) : (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkWireOutToF n i, networkWireOutFromF n i,
    networkWireOut_left n i, networkWireOut_right n i⟩

theorem networkWireOutFromF_routeToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) :
    networkWireOutFromF n i (networkWireRouteToF n i p)
      = ((p.1.1, p.2 i), fun k => if k = i then p.1.2 else p.2 k) := by
  have hss : eRegSplit n (networkWireRouteToF n i p)
      = (networkWireWireVec n i p, ![p.1.2, p.2 i]) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkWireOutFromF
  rw [hss]
  have h1 : networkWireWireVec n i p i = p.1.1 := by
    rw [networkWireWireVec_apply, if_pos rfl]
  have h3 : ∀ k : Fin n, (if k = i then (![p.1.2, p.2 i] : Fin 2 → Bool) 0
      else networkWireWireVec n i p k) = if k = i then p.1.2 else p.2 k := by
    intro k
    by_cases hk : k = i
    · rw [if_pos hk, if_pos hk]
      rfl
    · rw [if_neg hk, networkWireWireVec_apply, if_neg hk, if_neg hk]
  refine Prod.ext (Prod.ext h1 rfl) (funext fun k => h3 k)

def networkCzWireVec (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) : Reg n :=
  fun m =>
    if hm : m = lo then p.1.1.1
    else if hm2 : m = hi then p.1.1.2
    else p.2 ⟨networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ),
      networkCzSlot_lt n (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hi.isLt m.isLt
        (fun h => hm (Fin.ext h)) (fun h => hm2 (Fin.ext h))⟩

theorem networkCzWireVec_apply (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) (m : Fin n) :
    networkCzWireVec n lo hi h1 p m
      = if hm : m = lo then p.1.1.1
    else if hm2 : m = hi then p.1.1.2
    else p.2 ⟨networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ),
      networkCzSlot_lt n (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hi.isLt m.isLt
        (fun h => hm (Fin.ext h)) (fun h => hm2 (Fin.ext h))⟩ := rfl

def networkCzRouteToF (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) : Reg (n + 2) :=
  (eRegSplit n).symm
    (networkCzWireVec n lo hi h1 p, ![p.1.2.1, p.1.2.2])

def networkCzRouteFromF (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2) :=
  ((((eRegSplit n v).1 lo, (eRegSplit n v).1 hi),
      ((eRegSplit n v).2 0, (eRegSplit n v).2 1)),
    fun k : Fin (n - 2) =>
      (eRegSplit n v).1 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
        networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)

theorem networkCzRouteFromF_fst_fst_fst (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).1).1 = (eRegSplit n v).1 lo := rfl

theorem networkCzRouteFromF_fst_fst_snd (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).1).2 = (eRegSplit n v).1 hi := rfl

theorem networkCzRouteFromF_fst_snd_fst (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).2).1 = (eRegSplit n v).2 0 := rfl

theorem networkCzRouteFromF_fst_snd_snd (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).2).2 = (eRegSplit n v).2 1 := rfl

theorem networkCzRouteFromF_snd_apply (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) (k : Fin (n - 2)) :
    (networkCzRouteFromF n lo hi h1 v).2 k
      = (eRegSplit n v).1 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
        networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩ := rfl

theorem networkCzRoute_left (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) :
    networkCzRouteFromF n lo hi h1 (networkCzRouteToF n lo hi h1 p) = p := by
  have hss : eRegSplit n (networkCzRouteToF n lo hi h1 p)
      = (networkCzWireVec n lo hi h1 p, ![p.1.2.1, p.1.2.2]) :=
    (eRegSplit n).apply_symm_apply _
  have hne : ¬(hi = lo) := by
    intro h
    have hv : (hi : ℕ) = (lo : ℕ) := congrArg Fin.val h
    omega
  unfold networkCzRouteFromF
  rw [hss]
  have hA : networkCzWireVec n lo hi h1 p lo = p.1.1.1 := by
    rw [networkCzWireVec_apply, dif_pos rfl]
  have hD : networkCzWireVec n lo hi h1 p hi = p.1.1.2 := by
    rw [networkCzWireVec_apply, dif_neg hne, dif_pos rfl]
  have hS : ∀ k : Fin (n - 2), networkCzWireVec n lo hi h1 p
      ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
        networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) (by omega) hi.isLt k.isLt⟩ = p.2 k := by
    intro k
    rw [networkCzWireVec_apply]
    have hσne := networkCzSpec_ne (lo : ℕ) (hi : ℕ) (k : ℕ) h1
    have hpair : ∀ pf : networkCzSlot (lo : ℕ) (hi : ℕ)
          (networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ)) < n - 2,
        (⟨networkCzSlot (lo : ℕ) (hi : ℕ) (networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ)),
            pf⟩ : Fin (n - 2)) = k :=
      fun pf => Fin.ext (networkCzSpec_slot (lo : ℕ) (hi : ℕ) (k : ℕ) h1)
    rw [dif_neg (fun h => hσne.1 (congrArg Fin.val h)),
      dif_neg (fun h => hσne.2 (congrArg Fin.val h)),
      hpair _]
  refine Prod.ext (Prod.ext (Prod.ext hA hD) (Prod.ext rfl rfl)) (funext fun k => hS k)

theorem networkCzRoute_right (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    networkCzRouteToF n lo hi h1 (networkCzRouteFromF n lo hi h1 v) = v := by
  refine (eRegSplit n).injective ?_
  have hss : eRegSplit n (networkCzRouteToF n lo hi h1 (networkCzRouteFromF n lo hi h1 v))
      = (networkCzWireVec n lo hi h1 (networkCzRouteFromF n lo hi h1 v),
          ![((networkCzRouteFromF n lo hi h1 v).1).2.1,
            ((networkCzRouteFromF n lo hi h1 v).1).2.2]) :=
    (eRegSplit n).apply_symm_apply _
  rw [hss]
  refine Prod.ext (funext fun m => ?_) (funext fun f => ?_)
  · show networkCzWireVec n lo hi h1 (networkCzRouteFromF n lo hi h1 v) m
        = (eRegSplit n v).1 m
    rw [networkCzWireVec_apply]
    by_cases hm1 : m = lo
    · rw [dif_pos hm1, networkCzRouteFromF_fst_fst_fst, hm1]
    · rw [dif_neg hm1]
      by_cases hm2 : m = hi
      · rw [dif_pos hm2, networkCzRouteFromF_fst_fst_snd, hm2]
      · rw [dif_neg hm2, networkCzRouteFromF_snd_apply]
        refine congrArg ((eRegSplit n v).1) ?_
        apply Fin.ext
        exact networkCzSlot_spec (lo : ℕ) (hi : ℕ) (m : ℕ) h1
          (fun h => hm1 (Fin.ext h)) (fun h => hm2 (Fin.ext h))
  · fin_cases f
    · rfl
    · rfl

def networkCzRoute (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2) ≃ Reg (n + 2) :=
  ⟨networkCzRouteToF n lo hi h1, networkCzRouteFromF n lo hi h1,
    networkCzRoute_left n lo hi h1, networkCzRoute_right n lo hi h1⟩

def networkCzOutToF (n : ℕ) (lo hi : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    ((fun m : Fin n => if m = lo then p.1.1 else if m = hi then p.1.2 else p.2 m),
      ![p.2 lo, p.2 hi])

def networkCzOutFromF (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 lo, (eRegSplit n v).1 hi),
    fun m : Fin n =>
      if m = lo then (eRegSplit n v).2 0
      else if m = hi then (eRegSplit n v).2 1 else (eRegSplit n v).1 m)

theorem networkCzOutFromF_fst_fst (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) :
    ((networkCzOutFromF n lo hi v).1).1 = (eRegSplit n v).1 lo := rfl

theorem networkCzOutFromF_fst_snd (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) :
    ((networkCzOutFromF n lo hi v).1).2 = (eRegSplit n v).1 hi := rfl

theorem networkCzOutFromF_snd_apply (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) (m : Fin n) :
    (networkCzOutFromF n lo hi v).2 m
      = if m = lo then (eRegSplit n v).2 0
    else if m = hi then (eRegSplit n v).2 1 else (eRegSplit n v).1 m := rfl

theorem networkCzOut_left (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : (Bool × Bool) × Reg n) :
    networkCzOutFromF n lo hi (networkCzOutToF n lo hi p) = p := by
  have hss : eRegSplit n (networkCzOutToF n lo hi p)
      = ((fun m : Fin n => if m = lo then p.1.1 else if m = hi then p.1.2 else p.2 m),
          ![p.2 lo, p.2 hi]) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkCzOutFromF
  rw [hss]
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun k => ?_)
  · show (if (lo : Fin n) = lo then p.1.1 else if lo = hi then p.1.2 else p.2 lo) = p.1.1
    rw [if_pos rfl]
  · show (if (hi : Fin n) = lo then p.1.1 else if hi = hi then p.1.2 else p.2 hi) = p.1.2
    rw [if_neg (by
        intro h
        have hv : (hi : ℕ) = (lo : ℕ) := congrArg Fin.val h
        omega), if_pos rfl]
  · show (if k = lo then (![p.2 lo, p.2 hi] : Fin 2 → Bool) 0
        else if k = hi then (![p.2 lo, p.2 hi] : Fin 2 → Bool) 1
        else (if k = lo then p.1.1 else if k = hi then p.1.2 else p.2 k)) = p.2 k
    by_cases h1' : k = lo
    · rw [if_pos h1', h1']
      rfl
    · rw [if_neg h1', if_neg h1']
      by_cases h2' : k = hi
      · rw [if_pos h2', h2']
        rfl
      · rw [if_neg h2', if_neg h2']

theorem networkCzOut_right (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    networkCzOutToF n lo hi (networkCzOutFromF n lo hi v) = v := by
  refine (eRegSplit n).injective ?_
  have hss : eRegSplit n (networkCzOutToF n lo hi (networkCzOutFromF n lo hi v))
      = ((fun m : Fin n => if m = lo then ((networkCzOutFromF n lo hi v).1).1
            else if m = hi then ((networkCzOutFromF n lo hi v).1).2
            else (networkCzOutFromF n lo hi v).2 m),
          ![(networkCzOutFromF n lo hi v).2 lo, (networkCzOutFromF n lo hi v).2 hi]) := by
    unfold networkCzOutToF
    exact (eRegSplit n).apply_symm_apply _
  rw [hss]
  refine Prod.ext (funext fun m => ?_) (funext fun f => ?_)
  · show (if m = lo then ((networkCzOutFromF n lo hi v).1).1
        else if m = hi then ((networkCzOutFromF n lo hi v).1).2
        else (networkCzOutFromF n lo hi v).2 m) = (eRegSplit n v).1 m
    by_cases hm1 : m = lo
    · rw [if_pos hm1, networkCzOutFromF_fst_fst, hm1]
    · rw [if_neg hm1]
      by_cases hm2 : m = hi
      · rw [if_pos hm2, networkCzOutFromF_fst_snd, hm2]
      · rw [if_neg hm2, networkCzOutFromF_snd_apply, if_neg hm1, if_neg hm2]
  · have hne : ¬((hi : Fin n) = lo) := by
      intro h
      have hv : (hi : ℕ) = (lo : ℕ) := congrArg Fin.val h
      omega
    have hslot0 : (networkCzOutFromF n lo hi v).2 lo = (eRegSplit n v).2 0 := by
      rw [networkCzOutFromF_snd_apply, if_pos rfl]
    have hslot1 : (networkCzOutFromF n lo hi v).2 hi = (eRegSplit n v).2 1 := by
      rw [networkCzOutFromF_snd_apply, if_neg hne, if_pos rfl]
    fin_cases f
    · show (![ (networkCzOutFromF n lo hi v).2 lo, (networkCzOutFromF n lo hi v).2 hi ]) 0
          = (eRegSplit n v).2 0
      rw [hslot0]
      rfl
    · show (![ (networkCzOutFromF n lo hi v).2 lo, (networkCzOutFromF n lo hi v).2 hi ]) 1
          = (eRegSplit n v).2 1
      rw [hslot1]
      rfl

def networkCzOutEquiv (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkCzOutToF n lo hi, networkCzOutFromF n lo hi,
    networkCzOut_left n lo hi h1, networkCzOut_right n lo hi h1⟩

def eWireFin (n : ℕ) (i : Fin n) : Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkWireRoute n i)).trans (bitVecEquiv (n + 2))

def eWireOutFin (n : ℕ) (i : Fin n) : Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkWireOutEquiv n i)).trans (bitVecEquiv (n + 2))

def eCzFin (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    Fin 16 × Fin (2 ^ (n - 2)) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr Qatlib.Concepts.ClusterPatterns.WireComposition.clusterCZRegisterEquiv.symm (bitVecEquiv (n - 2)).symm).trans
    (networkCzRoute n lo hi h1)).trans (bitVecEquiv (n + 2))

def eCzOutFin (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkCzOutEquiv n lo hi h1)).trans (bitVecEquiv (n + 2))

theorem relabelGate_prodCongr_tensorGate_one {I I' J J' : Type*} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
    (e₁ : I ≃ I') (e₂ : J ≃ J') (U : Matrix I I ℂ) :
    relabelGate (Equiv.prodCongr e₁ e₂) (TensorGate U (1 : Matrix J J ℂ))
      = TensorGate (relabelGate e₁ U) (1 : Matrix J' J' ℂ) := by
  ext p q
  show U (e₁.symm p.1) (e₁.symm q.1) * (if e₂.symm p.2 = e₂.symm q.2 then (1 : ℂ) else 0)
      = U (e₁.symm p.1) (e₁.symm q.1) * (if p.2 = q.2 then (1 : ℂ) else 0)
  by_cases h : p.2 = q.2
  · have h' : e₂.symm p.2 = e₂.symm q.2 := congrArg (Equiv.symm e₂) h
    rw [if_pos h', if_pos h]
  · have h' : ¬(e₂.symm p.2 = e₂.symm q.2) := fun hh => h (e₂.symm.injective hh)
    rw [if_neg h', if_neg h]

theorem relabelGate_matOuter_fwd {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (u w : QState I) :
    relabelGate e (matOuter u w) = matOuter (relabelState e u) (relabelState e w) := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, matOuter,
    Matrix.of_apply, relabelState, Function.comp_apply]

theorem applyGate_relabelGate' {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ) (v : QState J) :
    ApplyGate (relabelGate e U) v
      = relabelState e (ApplyGate U (relabelState e.symm v)) := by
  have hv : relabelState e (relabelState e.symm v) = v := by
    have h := relabelState_relabelState e.symm v
    rwa [Equiv.symm_symm] at h
  have hstep : ApplyGate (relabelGate e U) v
      = ApplyGate (relabelGate e U) (relabelState e (relabelState e.symm v)) := by
    rw [hv]
  rw [hstep, applyGate_relabelGate]

theorem relabelState_trans {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] (e : I ≃ J) (f : J ≃ K) (v : QState I) :
    relabelState f (relabelState e v) = relabelState (e.trans f) v := by
  funext k
  simp only [relabelState, Function.comp_apply, Equiv.symm_trans_apply]

noncomputable def networkMatUnit {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    Matrix I I ℂ := Matrix.of fun c c' => if c = i ∧ c' = j then (1 : ℂ) else 0

theorem networkMatUnit_eq_matOuter_ket {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    networkMatUnit i j = matOuter (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) := by
  ext r r'
  simp only [networkMatUnit, Matrix.of_apply, matOuter, Qatlib.Foundations.PureStateMath.Ket]
  by_cases h1 : r = i <;> by_cases h2 : r' = j <;> simp [h1, h2]

theorem networkMul_matUnit_conj {D : ℕ} (M : Operator D) (i j : Fin D) :
    M * networkMatUnit i j * M.conjTranspose = matOuter (M *ᵥ Qatlib.Foundations.PureStateMath.Ket i) (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
  rw [networkMatUnit_eq_matOuter_ket, matOuter_sandwich]
  rfl

theorem networkMatUnit_decomp {D : ℕ} (ρ : Operator D) :
    ρ = ∑ p : Fin D × Fin D, ρ p.1 p.2 • networkMatUnit p.1 p.2 := by
  ext c c'
  have hentry : ∀ p : Fin D × Fin D,
      (ρ p.1 p.2 • networkMatUnit p.1 p.2) c c'
        = if c = p.1 ∧ c' = p.2 then ρ p.1 p.2 else 0 := by
    intro p
    simp only [networkMatUnit, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    by_cases h1 : c = p.1 <;> by_cases h2 : c' = p.2 <;> simp [h1, h2]
  rw [Matrix.sum_apply, Finset.sum_congr rfl (fun p _ => hentry p),
    Fintype.sum_eq_single (c, c')]
  · rw [if_pos ⟨rfl, rfl⟩]
  · intro p hp
    have hnc : ¬(c = p.1 ∧ c' = p.2) := by
      intro hc
      apply hp
      rw [Prod.mk.injEq]
      exact ⟨hc.1.symm, hc.2.symm⟩
    rw [if_neg hnc]

noncomputable def networkFrameB (n : ℕ) : Matrix (Reg (n + 2)) (Reg n) ℂ :=
  Matrix.of fun y x => if y = networkFrameVec n x then (1 : ℂ) else 0

noncomputable def networkFrame (n : ℕ) : Matrix (Fin (2 ^ (n + 2))) (Fin (2 ^ n)) ℂ :=
  (networkFrameB n).submatrix (bitVecEquiv (n + 2)).symm (bitVecEquiv n).symm

theorem networkFrame_column (n : ℕ) (x : Fin (2 ^ n)) :
    (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (Qatlib.Foundations.PureStateMath.Ket (networkFrameVec n ((bitVecEquiv n).symm x))) := by
  funext r
  simp only [networkFrame, Matrix.submatrix_apply, networkFrameB, Matrix.of_apply,
    relabelState, Function.comp_apply, Qatlib.Foundations.PureStateMath.Ket]

theorem networkFrame_matUnit (n : ℕ) (x y : Fin (2 ^ n)) :
    networkFrame n * networkMatUnit x y * (networkFrame n).conjTranspose
      = matOuter (fun r => networkFrame n r x) (fun r => networkFrame n r y) := by
  ext r r'
  have hinner : ∀ k : Fin (2 ^ n),
      (∑ b : Fin (2 ^ n), networkFrame n r b * (if b = x ∧ k = y then (1 : ℂ) else 0))
        = if k = y then networkFrame n r x else 0 := by
    intro k
    rw [Fintype.sum_eq_single x]
    · by_cases hk : k = y
      · rw [if_pos ⟨rfl, hk⟩, mul_one, if_pos hk]
      · rw [if_neg (fun hc => hk hc.2), mul_zero, if_neg hk]
    · intro b hb
      rw [if_neg (fun hc => hb hc.1), mul_zero]
  have houter : ∀ k : Fin (2 ^ n),
      ((∑ b : Fin (2 ^ n), networkFrame n r b * (if b = x ∧ k = y then (1 : ℂ) else 0))
          * (starRingEnd ℂ) (networkFrame n r' k))
        = (if k = y then networkFrame n r x else 0)
            * (starRingEnd ℂ) (networkFrame n r' k) :=
    fun k => congrArg (· * (starRingEnd ℂ) (networkFrame n r' k)) (hinner k)
  simp only [Matrix.mul_apply, conjTranspose_apply, networkMatUnit, Matrix.of_apply,
    matOuter, Matrix.of_apply, RCLike.star_def]
  rw [Finset.sum_congr rfl fun k _ => houter k, Fintype.sum_eq_single y]
  · rw [if_pos rfl]
  · intro k hk
    rw [if_neg hk, zero_mul]
end Qatlib.Concepts.MbqcFlow.FlowDecision
