/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument

/-!
# Register routing for local cluster patterns

This module supplies the basis equivalences used to place small cluster patterns inside an `n +
2` qubit network register. `networkWireRoute` and `networkCzRoute` isolate local input systems,
while `networkWireOutEquiv` and `networkCzOutEquiv` isolate record registers and logical outputs
for one-way computation [RaussendorfBriegel2001].

`networkFrame` appends two zero ancillary bits. Matrix-unit decompositions and compatibility
lemmas for relabeling, tensor gates, and outer products support later branch calculations.

## Main statements

* `networkWireRoute` and `networkCzRoute`: input routing equivalences.
* `eWireOutFin` and `eCzOutFin`: finite-index output routing equivalences.
* `networkMatUnit_decomp`: expansion of arbitrary operators in matrix units.
* `networkFrame_matUnit`: the effect of the input frame on a matrix unit.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

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

/-- Splits an `n + 2` bit register into its first `n` bits and its final two bits. -/
def eRegSplitToF (n : ℕ) (v : Reg (n + 2)) : Reg n × Reg 2 :=
  (fun k => v (k.castLE (by omega : n ≤ n + 2)),
    fun f => v ⟨n + (f : Fin 2).val, by omega⟩)

/-- Concatenates an `n`-bit register and a two-bit register into an `n + 2` bit register. -/
def eRegSplitFromF (n : ℕ) (p : Reg n × Reg 2) : Reg (n + 2) :=
  fun q =>
    if h : (q : Fin (n + 2)).val < n then p.1 ⟨(q : Fin (n + 2)).val, h⟩
    else p.2 ⟨(q : Fin (n + 2)).val - n, by omega⟩

/-- Evaluates register concatenation by selecting the first register below index `n` and the
second register at the shifted index otherwise. -/
theorem eRegSplitFromF_apply (n : ℕ) (p : Reg n × Reg 2) (q : Fin (n + 2)) :
    eRegSplitFromF n p q =
      (if h : (q : Fin (n + 2)).val < n then p.1 ⟨(q : Fin (n + 2)).val, h⟩
    else p.2 ⟨(q : Fin (n + 2)).val - n, by omega⟩) := rfl

/-- Concatenating the two parts of a split register recovers the register. -/
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

/-- Splitting a concatenated pair of registers recovers the pair. -/
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

/-- The equivalence splitting an `n + 2` bit register into an `n`-bit register and a two-bit
register. -/
def eRegSplit (n : ℕ) : Reg (n + 2) ≃ Reg n × Reg 2 :=
  ⟨eRegSplitToF n, eRegSplitFromF n, eRegSplitFromF_left n, eRegSplitFromF_right n⟩

/-- The first component of `eRegSplit` reads the original register at the same index. -/
theorem eRegSplit_fst (n : ℕ) (v : Reg (n + 2)) (k : Fin n) :
    (eRegSplit n v).1 k = v (k.castLE (by omega : n ≤ n + 2)) := rfl

/-- The second component of `eRegSplit` reads the original register at index `n + f`. -/
theorem eRegSplit_snd (n : ℕ) (v : Reg (n + 2)) (f : Fin 2) :
    (eRegSplit n v).2 f = v ⟨n + (f : Fin 2).val, by omega⟩ := rfl

/-- The inverse split reads from the first component at every index below `n`. -/
theorem eRegSplit_symm_of_lt {n : ℕ} {m : ℕ} (hm : m < n) (p : Reg n × Reg 2) :
    (eRegSplit n).symm p ⟨m, by omega⟩ = p.1 ⟨m, hm⟩ := by
  show (eRegSplitFromF n p) ⟨m, by omega⟩ = p.1 ⟨m, hm⟩
  rw [eRegSplitFromF_apply, dif_pos hm]

/-- The inverse split reads from the second component at every index at least `n`, after
subtracting `n`. -/
theorem eRegSplit_symm_of_ge {n : ℕ} {m : ℕ} (hm : n ≤ m) (hm2 : m < n + 2)
    (p : Reg n × Reg 2) :
    (eRegSplit n).symm p ⟨m, hm2⟩ = p.2 ⟨m - n, by omega⟩ := by
  show (eRegSplitFromF n p) ⟨m, hm2⟩ = p.2 ⟨m - n, by omega⟩
  rw [eRegSplitFromF_apply, dif_neg (show ¬(m < n) by omega)]

/-- Extends a logical bit register by two ancillary bits set to false. -/
def networkFrameVec (n : ℕ) (w : Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm (w, fun _ => false)

/-- The embedded register agrees with the logical register below `n` and is false at the final
two indices. -/
theorem networkFrameVec_apply (n : ℕ) (w : Reg n) (q : Fin (n + 2)) :
    networkFrameVec n w q
      = if h : (q : Fin (n + 2)).val < n then w ⟨(q : Fin (n + 2)).val, h⟩ else false := by
  by_cases hq : (q : Fin (n + 2)).val < n
  · rw [networkFrameVec, eRegSplit_symm_of_lt hq, dif_pos hq]
  · have hge : n ≤ (q : Fin (n + 2)).val := by omega
    have hlt : (q : Fin (n + 2)).val < n + 2 := q.isLt
    rw [networkFrameVec, eRegSplit_symm_of_ge hge hlt, dif_neg hq]

/-- Maps a complementary-register index to a wire index by skipping the positions `lo` and `hi`. -/
def networkCzSpec (lo hi : ℕ) (k : ℕ) : ℕ :=
  k + (if k < lo then 0 else if k + 1 < hi then 1 else 2)

/-- Compresses a wire index by subtracting the number of selected positions strictly below it. -/
def networkCzSlot (lo hi : ℕ) (m : ℕ) : ℕ :=
  m - (if lo < m then 1 else 0) - (if hi < m then 1 else 0)

/-- For `lo < hi`, compressing an index produced by skipping the two selected positions recovers
the complementary index. -/
theorem networkCzSpec_slot (lo hi k : ℕ) (h1 : lo < hi) :
    networkCzSlot lo hi (networkCzSpec lo hi k) = k := by
  unfold networkCzSpec networkCzSlot
  split_ifs <;> omega

/-- For `lo < hi`, expanding a compressed index recovers any wire index distinct from both
selected positions. -/
theorem networkCzSlot_spec (lo hi m : ℕ) (h1 : lo < hi) (hm1 : m ≠ lo) (hm2 : m ≠ hi) :
    networkCzSpec lo hi (networkCzSlot lo hi m) = m := by
  unfold networkCzSpec networkCzSlot
  split_ifs <;> omega

/-- Skipping two ordered selected positions sends an index below `n - 2` to an index below `n`. -/
theorem networkCzSpec_lt (n lo hi k : ℕ) (h1 : lo < hi) (h2 : hi < n) (hk : k < n - 2) :
    networkCzSpec lo hi k < n := by
  unfold networkCzSpec
  split_ifs <;> omega

/-- Compressing an index below `n` distinct from the two ordered selected positions gives an
index below `n - 2`. -/
theorem networkCzSlot_lt (n lo hi m : ℕ) (h1 : lo < hi) (h2 : hi < n) (hm : m < n)
    (hm1 : m ≠ lo) (hm2 : m ≠ hi) : networkCzSlot lo hi m < n - 2 := by
  unfold networkCzSlot
  split_ifs <;> omega

/-- For ordered selected positions, an expanded complementary index equals neither selected
position. -/
theorem networkCzSpec_ne (lo hi k : ℕ) (h1 : lo < hi) :
    networkCzSpec lo hi k ≠ lo ∧ networkCzSpec lo hi k ≠ hi := by
  unfold networkCzSpec
  split_ifs <;> omega

/-- Replaces wire `i` of the register component by the first local bit. -/
def networkWireWireVec (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg n :=
  fun k => if k = i then p.1.1 else p.2 k

/-- The routed wire register reads the first local bit at `i` and the original register
elsewhere. -/
theorem networkWireWireVec_apply (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) (k : Fin n) :
    networkWireWireVec n i p k = (if k = i then p.1.1 else p.2 k) := rfl

/-- Places the two-bit local wire input and its complementary register into the physical network
layout. -/
def networkWireRouteToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    (networkWireWireVec n i p, ![p.1.2, p.2 i])

/-- Extracts the local wire input and complementary register from a physical network register. -/
def networkWireRouteFromF (n : ℕ) (i : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 i, (eRegSplit n v).2 0),
    fun k : Fin n => if k = i then (eRegSplit n v).2 1 else (eRegSplit n v).1 k)

/-- Places a wire record pair and logical output register into the physical output layout. -/
def networkWireOutToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    ((fun k : Fin n => if k = i then p.1.1 else p.2 k), ![p.2 i, p.1.2])

/-- Extracts the wire record pair and logical output register from the physical output layout. -/
def networkWireOutFromF (n : ℕ) (i : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 i, (eRegSplit n v).2 1),
    fun k : Fin n => if k = i then (eRegSplit n v).2 0 else (eRegSplit n v).1 k)

/-- The first extracted wire input bit is the physical register bit at wire `i`. -/
theorem networkWireRouteFromF_fst_fst (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireRouteFromF n i v).1).1 = (eRegSplit n v).1 i := rfl

/-- The second extracted wire input bit is the first ancillary bit. -/
theorem networkWireRouteFromF_fst_snd (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireRouteFromF n i v).1).2 = (eRegSplit n v).2 0 := rfl

/-- The wire input layout stores the second ancillary bit at the selected complementary-register
position and reads the other positions directly. -/
theorem networkWireRouteFromF_snd_apply (n : ℕ) (i : Fin n) (v : Reg (n + 2)) (k : Fin n) :
    (networkWireRouteFromF n i v).2 k
      = if k = i then (eRegSplit n v).2 1 else (eRegSplit n v).1 k := rfl

/-- Extracting a local wire input after placing it in the physical layout recovers the input. -/
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

/-- Reconstructing a physical register from its extracted wire input layout recovers the
register. -/
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

/-- The equivalence between a local two-bit wire input with an `n`-bit complementary register
and the physical `n + 2` bit layout. -/
def networkWireRoute (n : ℕ) (i : Fin n) : (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkWireRouteToF n i, networkWireRouteFromF n i,
    networkWireRoute_left n i, networkWireRoute_right n i⟩

/-- The first extracted wire record bit is the physical bit at wire `i`. -/
theorem networkWireOutFromF_fst_fst (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireOutFromF n i v).1).1 = (eRegSplit n v).1 i := rfl

/-- The second extracted wire record bit is the second ancillary bit. -/
theorem networkWireOutFromF_fst_snd (n : ℕ) (i : Fin n) (v : Reg (n + 2)) :
    ((networkWireOutFromF n i v).1).2 = (eRegSplit n v).2 1 := rfl

/-- The extracted logical wire output uses the first ancillary bit at wire `i` and the physical
register at all other wires. -/
theorem networkWireOutFromF_snd_apply (n : ℕ) (i : Fin n) (v : Reg (n + 2)) (k : Fin n) :
    (networkWireOutFromF n i v).2 k
      = if k = i then (eRegSplit n v).2 0 else (eRegSplit n v).1 k := rfl

/-- Extracting a wire output after placing it in the physical output layout recovers the output. -/
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

/-- Reconstructing a physical register from its extracted wire output layout recovers the
register. -/
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

/-- The equivalence between a wire record pair with its logical output register and the physical
network layout. -/
def networkWireOutEquiv (n : ℕ) (i : Fin n) : (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkWireOutToF n i, networkWireOutFromF n i,
    networkWireOut_left n i, networkWireOut_right n i⟩

/-- Converting the local wire input layout to the output layout exchanges the second local bit
with the selected complementary-register bit. -/
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

/-- Reconstructs an `n`-bit register from its two selected local bits and the `n - 2`
complementary bits. -/
def networkCzWireVec (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) : Reg n :=
  fun m =>
    if hm : m = lo then p.1.1.1
    else if hm2 : m = hi then p.1.1.2
    else p.2 ⟨networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ),
      networkCzSlot_lt n (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hi.isLt m.isLt
        (fun h => hm (Fin.ext h)) (fun h => hm2 (Fin.ext h))⟩

/-- The reconstructed controlled-Z register reads the selected local bits at `lo` and `hi` and
the compressed complementary index elsewhere. -/
theorem networkCzWireVec_apply (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) (m : Fin n) :
    networkCzWireVec n lo hi h1 p m
      = if hm : m = lo then p.1.1.1
    else if hm2 : m = hi then p.1.1.2
    else p.2 ⟨networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ),
      networkCzSlot_lt n (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hi.isLt m.isLt
        (fun h => hm (Fin.ext h)) (fun h => hm2 (Fin.ext h))⟩ := rfl

/-- Places the four local controlled-Z input bits and the complementary register into the
physical network layout. -/
def networkCzRouteToF (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2)) : Reg (n + 2) :=
  (eRegSplit n).symm
    (networkCzWireVec n lo hi h1 p, ![p.1.2.1, p.1.2.2])

/-- Extracts the two selected logical bits, the two ancillary bits, and the complementary
register from a physical controlled-Z input. -/
def networkCzRouteFromF (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2) :=
  ((((eRegSplit n v).1 lo, (eRegSplit n v).1 hi),
      ((eRegSplit n v).2 0, (eRegSplit n v).2 1)),
    fun k : Fin (n - 2) =>
      (eRegSplit n v).1 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
        networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)

/-- The first selected controlled-Z input bit is the physical register bit at `lo`. -/
theorem networkCzRouteFromF_fst_fst_fst (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).1).1 = (eRegSplit n v).1 lo := rfl

/-- The second selected controlled-Z input bit is the physical register bit at `hi`. -/
theorem networkCzRouteFromF_fst_fst_snd (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).1).2 = (eRegSplit n v).1 hi := rfl

/-- The first local controlled-Z ancillary bit is the first physical ancillary bit. -/
theorem networkCzRouteFromF_fst_snd_fst (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).2).1 = (eRegSplit n v).2 0 := rfl

/-- The second local controlled-Z ancillary bit is the second physical ancillary bit. -/
theorem networkCzRouteFromF_fst_snd_snd (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) :
    (((networkCzRouteFromF n lo hi h1 v).1).2).2 = (eRegSplit n v).2 1 := rfl

/-- The extracted complementary controlled-Z register reads physical wire indices obtained by
skipping `lo` and `hi`. -/
theorem networkCzRouteFromF_snd_apply (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (v : Reg (n + 2)) (k : Fin (n - 2)) :
    (networkCzRouteFromF n lo hi h1 v).2 k
      = (eRegSplit n v).1 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
        networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩ := rfl

/-- Extracting a controlled-Z input after placing it in the physical layout recovers the input. -/
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

/-- Reconstructing a physical register from its extracted controlled-Z input layout recovers the
register. -/
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

/-- The equivalence between a four-bit controlled-Z input with its complementary register and
the physical network layout. -/
def networkCzRoute (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    ((Bool × Bool) × (Bool × Bool)) × Reg (n - 2) ≃ Reg (n + 2) :=
  ⟨networkCzRouteToF n lo hi h1, networkCzRouteFromF n lo hi h1,
    networkCzRoute_left n lo hi h1, networkCzRoute_right n lo hi h1⟩

/-- Places a controlled-Z record pair at the selected wires and the two corresponding logical
output bits in the ancillary positions. -/
def networkCzOutToF (n : ℕ) (lo hi : Fin n) (p : (Bool × Bool) × Reg n) : Reg (n + 2) :=
  (eRegSplit n).symm
    ((fun m : Fin n => if m = lo then p.1.1 else if m = hi then p.1.2 else p.2 m),
      ![p.2 lo, p.2 hi])

/-- Extracts the controlled-Z record pair from the selected wires and restores their logical
output bits from the ancillary positions. -/
def networkCzOutFromF (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) : (Bool × Bool) × Reg n :=
  (((eRegSplit n v).1 lo, (eRegSplit n v).1 hi),
    fun m : Fin n =>
      if m = lo then (eRegSplit n v).2 0
      else if m = hi then (eRegSplit n v).2 1 else (eRegSplit n v).1 m)

/-- The first extracted controlled-Z record bit is the physical bit at `lo`. -/
theorem networkCzOutFromF_fst_fst (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) :
    ((networkCzOutFromF n lo hi v).1).1 = (eRegSplit n v).1 lo := rfl

/-- The second extracted controlled-Z record bit is the physical bit at `hi`. -/
theorem networkCzOutFromF_fst_snd (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) :
    ((networkCzOutFromF n lo hi v).1).2 = (eRegSplit n v).1 hi := rfl

/-- The extracted controlled-Z logical output reads the ancillary bits at the selected wires and
the physical register elsewhere. -/
theorem networkCzOutFromF_snd_apply (n : ℕ) (lo hi : Fin n) (v : Reg (n + 2)) (m : Fin n) :
    (networkCzOutFromF n lo hi v).2 m
      = if m = lo then (eRegSplit n v).2 0
    else if m = hi then (eRegSplit n v).2 1 else (eRegSplit n v).1 m := rfl

/-- For ordered distinct endpoints, extracting a controlled-Z output after placing it in the
physical layout recovers the output. -/
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

/-- For ordered distinct endpoints, reconstructing a physical register from its controlled-Z
output layout recovers the register. -/
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

/-- The equivalence between a controlled-Z record pair with its logical output register and the
physical network layout. -/
def networkCzOutEquiv (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    (Bool × Bool) × Reg n ≃ Reg (n + 2) :=
  ⟨networkCzOutToF n lo hi, networkCzOutFromF n lo hi,
    networkCzOut_left n lo hi h1, networkCzOut_right n lo hi h1⟩

/-- The finite-index equivalence placing a four-dimensional local wire system and its
complementary register in the physical network layout. -/
def eWireFin (n : ℕ) (i : Fin n) : Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkWireRoute n i)).trans (bitVecEquiv (n + 2))

/-- The finite-index equivalence placing a four-dimensional wire record and its logical output
register in the physical output layout. -/
def eWireOutFin (n : ℕ) (i : Fin n) : Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkWireOutEquiv n i)).trans (bitVecEquiv (n + 2))

/-- The finite-index equivalence placing a sixteen-dimensional local controlled-Z system and its
complementary register in the physical layout. -/
def eCzFin (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    Fin 16 × Fin (2 ^ (n - 2)) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr Qatlib.Concepts.ClusterPatterns.WireComposition.clusterCZRegisterEquiv.symm (bitVecEquiv (n - 2)).symm).trans
    (networkCzRoute n lo hi h1)).trans (bitVecEquiv (n + 2))

/-- The finite-index equivalence placing a four-dimensional controlled-Z record and its logical
output register in the physical output layout. -/
def eCzOutFin (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ)) :
    Fin 4 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 2)) :=
  ((Equiv.prodCongr teleportOutcomeEquiv.symm (bitVecEquiv n).symm).trans
    (networkCzOutEquiv n lo hi h1)).trans (bitVecEquiv (n + 2))

/-- Relabeling a tensor product of a gate and an identity along a product equivalence relabels
the gate and preserves the identity factor. -/
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

/-- Relabeling an outer-product matrix equals the outer product of the relabeled states. -/
theorem relabelGate_matOuter_fwd {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (u w : QState I) :
    relabelGate e (matOuter u w) = matOuter (relabelState e u) (relabelState e w) := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, matOuter,
    Matrix.of_apply, relabelState, Function.comp_apply]

/-- Applying a relabeled gate equals moving the state to the original indices, applying the
original gate, and relabeling the result. -/
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

/-- Successive state relabelings agree with relabeling along the composite equivalence. -/
theorem relabelState_trans {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] (e : I ≃ J) (f : J ≃ K) (v : QState I) :
    relabelState f (relabelState e v) = relabelState (e.trans f) v := by
  funext k
  simp only [relabelState, Function.comp_apply, Equiv.symm_trans_apply]

/-- The matrix unit whose only nonzero entry is one at row `i` and column `j`. -/
noncomputable def networkMatUnit {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    Matrix I I ℂ := Matrix.of fun c c' => if c = i ∧ c' = j then (1 : ℂ) else 0

/-- A matrix unit is the outer product of its row and column basis kets. -/
theorem networkMatUnit_eq_matOuter_ket {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    networkMatUnit i j = matOuter (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) := by
  ext r r'
  simp only [networkMatUnit, Matrix.of_apply, matOuter, Qatlib.Foundations.PureStateMath.Ket]
  by_cases h1 : r = i <;> by_cases h2 : r' = j <;> simp [h1, h2]

/-- Conjugating a matrix unit by `M` gives the outer product of the corresponding columns of
`M`. -/
theorem networkMul_matUnit_conj {D : ℕ} (M : Operator D) (i j : Fin D) :
    M * networkMatUnit i j * M.conjTranspose = matOuter (M *ᵥ Qatlib.Foundations.PureStateMath.Ket i) (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
  rw [networkMatUnit_eq_matOuter_ket, matOuter_sandwich]
  rfl

/-- Every finite operator is the sum of its matrix entries times the corresponding matrix units. -/
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

/-- The register-indexed embedding that appends two zero ancillary bits to each logical basis
state. -/
noncomputable def networkFrameB (n : ℕ) : Matrix (Reg (n + 2)) (Reg n) ℂ :=
  Matrix.of fun y x => if y = networkFrameVec n x then (1 : ℂ) else 0

/-- The finite-indexed matrix embedding of an `n`-qubit register into the network register with
two zero ancillary bits. -/
noncomputable def networkFrame (n : ℕ) : Matrix (Fin (2 ^ (n + 2))) (Fin (2 ^ n)) ℂ :=
  (networkFrameB n).submatrix (bitVecEquiv (n + 2)).symm (bitVecEquiv n).symm

/-- Each column of the network frame is the relabeled basis ket obtained by appending two zero
ancillary bits. -/
theorem networkFrame_column (n : ℕ) (x : Fin (2 ^ n)) :
    (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (Qatlib.Foundations.PureStateMath.Ket (networkFrameVec n ((bitVecEquiv n).symm x))) := by
  funext r
  simp only [networkFrame, Matrix.submatrix_apply, networkFrameB, Matrix.of_apply,
    relabelState, Function.comp_apply, Qatlib.Foundations.PureStateMath.Ket]

/-- Embedding a matrix unit with the network frame yields the outer product of the corresponding
frame columns. -/
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
