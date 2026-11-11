/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
Finite LIFO allocation with explicit stack invariants.
Preserves the original proof bodies and contributor history in the source PR.
The event/bill definitions come from the same source NativeCostedInstrument.
This scoped implementation is proposed in Dev intake PR #1134; maintainer acceptance is pending.
No Born law, Python extraction, exception rollback or host-bit complexity is asserted.
-/
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.LifoAllocator

set_option autoImplicit false

/-- Constructors for HCNative Event in the lifo allocator model. -/
inductive HCNativeEvent where
  | zero (wire : ℕ)
  | gate (code : FiniteGateCode)
  | measure (wire : ℕ) (outcome : Bool)
  | discard (wire : ℕ)
  deriving DecidableEq, Repr

/-- Prefix extrema are signed live-count changes, relative to the caller.
They do not replace an address-ownership or free-stack correctness theorem. -/
structure HCNativeBill where
  gates : ℕ
  zeros : ℕ
  measurements : ℕ
  discards : ℕ
  net : ℤ
  low : ℤ
  high : ℤ
  deriving DecidableEq, Repr

/-- Construction for bill Zero in the lifo allocator model. -/
private def billZero : HCNativeBill := ⟨0,0,0,0,0,0,0⟩
/-- Construction for bill Then in the lifo allocator model. -/
private def billThen (a b : HCNativeBill) : HCNativeBill :=
  ⟨a.gates+b.gates, a.zeros+b.zeros, a.measurements+b.measurements,
   a.discards+b.discards, a.net+b.net, min a.low (a.net+b.low),
   max a.high (a.net+b.high)⟩
/-- Construction for event Bill in the lifo allocator model. -/
private def eventBill : HCNativeEvent → HCNativeBill
  | .zero _ => ⟨0,1,0,0,1,0,1⟩
  | .gate _ => ⟨1,0,0,0,0,0,0⟩
  | .measure _ _ => ⟨0,0,1,0,0,0,0⟩
  | .discard _ => ⟨0,0,0,1,-1,-1,0⟩

/-- Construction for hc Native Bill in the lifo allocator model. -/
def hcNativeBill (events : List HCNativeEvent) : HCNativeBill :=
  events.foldr (fun e b => billThen (eventBill e) b) billZero



set_option autoImplicit false

/-- Data and invariants for HCNative Allocator State in the lifo allocator model. -/
structure HCNativeAllocatorState where
  live : List ℕ
  free : List ℕ
  next : ℕ
  deriving DecidableEq, Repr

namespace HCNativeAllocatorState

/-- Construction for empty in the lifo allocator model. -/
def empty : HCNativeAllocatorState := ⟨[], [], 0⟩

/-- Unique live/free ownership, with no lost or out-of-range allocated slot. -/
structure WellFormed (s : HCNativeAllocatorState) : Prop where
  live_nodup : s.live.Nodup
  free_nodup : s.free.Nodup
  separate : ∀ x, x ∈ s.live → x ∉ s.free
  bounded : ∀ x, x ∈ s.live ∨ x ∈ s.free → x < s.next
  complete : ∀ x, x < s.next → x ∈ s.live ∨ x ∈ s.free

/-- Construction for allocate One in the lifo allocator model. -/
def allocateOne (s : HCNativeAllocatorState) : HCNativeAllocatorState × ℕ :=
  match s.free with
  | slot :: rest => ({s with live := slot :: s.live, free := rest}, slot)
  | [] => ({s with live := s.next :: s.live, next := s.next + 1}, s.next)

/-- Construction for allocate Many in the lifo allocator model. -/
def allocateMany : ℕ → HCNativeAllocatorState → HCNativeAllocatorState × List ℕ
  | 0, s => (s, [])
  | k + 1, s =>
      let (s', slot) := allocateOne s
      let (s'', slots) := allocateMany k s'
      (s'', slot :: slots)

/-- Failure does not assert rollback of a Python callback's prior effects. -/
def releaseOne (slot : ℕ) (s : HCNativeAllocatorState) : Option HCNativeAllocatorState :=
  if slot ∈ s.live then
    some {s with live := s.live.erase slot, free := slot :: s.free}
  else none

/-- Construction for release Many in the lifo allocator model. -/
def releaseMany : List ℕ → HCNativeAllocatorState → Option HCNativeAllocatorState
  | [], s => some s
  | slot :: slots, s => do
      let s' ← releaseOne slot s
      releaseMany slots s'

/-- The finite allocator and event interpreter preserve the stated exact invariant under the displayed source hypotheses. -/
theorem empty_wellFormed : empty.WellFormed := by
  refine ⟨by simp [empty], by simp [empty], ?_, ?_, ?_⟩
  · simp [empty]
  · simp [empty]
  · simp [empty]

/-- Every single allocation preserves ownership, returns a newly live slot,
and keeps every previously live slot. This includes arbitrary LIFO reuse. -/
theorem allocateOne_spec (s : HCNativeAllocatorState) (hs : s.WellFormed) :
    (allocateOne s).1.WellFormed ∧
    (allocateOne s).2 ∈ (allocateOne s).1.live ∧
    (allocateOne s).2 ∉ s.live ∧
    (∀ x, x ∈ s.live → x ∈ (allocateOne s).1.live) := by
  rcases s with ⟨live, free, next⟩
  cases free with
  | nil =>
      have hn : next ∉ live := fun h => (Nat.lt_irrefl next) (hs.bounded next (Or.inl h))
      refine ⟨?_, by simp [allocateOne], hn, ?_⟩
      · refine ⟨List.nodup_cons.mpr ⟨hn, hs.live_nodup⟩, by simp [allocateOne], ?_, ?_, ?_⟩
        · simp [allocateOne]
        · intro x hx
          change x < next + 1
          simp only [allocateOne, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | hx
          · omega
          · have hb := hs.bounded x (Or.inl hx)
            change x < next at hb
            omega
        · intro x hx
          change x < next + 1 at hx
          simp only [allocateOne, List.mem_cons, List.not_mem_nil, or_false]
          by_cases he : x = next
          · exact Or.inl he
          · right
            have hx' : x < next := by omega
            simpa using hs.complete x hx'
      · intro x hx; simp [allocateOne, hx]
  | cons slot rest =>
      have hf := List.nodup_cons.mp hs.free_nodup
      have hslot : slot ∉ live := by
        intro h
        exact hs.separate slot h (by simp)
      refine ⟨?_, by simp [allocateOne], hslot, ?_⟩
      · refine ⟨List.nodup_cons.mpr ⟨hslot, hs.live_nodup⟩, hf.2, ?_, ?_, ?_⟩
        · intro x hx hxr
          change x ∈ rest at hxr
          simp only [allocateOne, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hf.1 hxr
          · exact hs.separate x hx (by simp [hxr])
        · intro x hx
          simp only [allocateOne, List.mem_cons] at hx
          rcases hx with (rfl | hx) | hx
          · exact hs.bounded x (Or.inr (by simp))
          · exact hs.bounded x (Or.inl hx)
          · exact hs.bounded x (Or.inr (by simp [hx]))
        · intro x hx
          have hc := hs.complete x hx
          simp only [List.mem_cons] at hc
          simp only [allocateOne, List.mem_cons]
          tauto
      · intro x hx; simp [allocateOne, hx]

/-- Arbitrary allocation batches return a distinct, wholly live frame disjoint
from the caller's old live slots, while retaining the caller's ownership. -/
theorem allocateMany_spec (k : ℕ) (s : HCNativeAllocatorState) (hs : s.WellFormed) :
    (allocateMany k s).1.WellFormed ∧
    (allocateMany k s).2.Nodup ∧
    (∀ x, x ∈ (allocateMany k s).2 → x ∈ (allocateMany k s).1.live) ∧
    (∀ x, x ∈ (allocateMany k s).2 → x ∉ s.live) ∧
    (∀ x, x ∈ s.live → x ∈ (allocateMany k s).1.live) := by
  induction k generalizing s with
  | zero => exact ⟨hs, by simp [allocateMany], by simp [allocateMany],
      by simp [allocateMany], by simp [allocateMany]⟩
  | succ k ih =>
      have hone := allocateOne_spec s hs
      generalize he : allocateOne s = pair at hone ⊢
      rcases pair with ⟨s', slot⟩
      rcases hone with ⟨hw, hlive, hfresh, hold⟩
      have hi := ih s' hw
      generalize ht : allocateMany k s' = pair at hi
      rcases pair with ⟨t, slots⟩
      rcases hi with ⟨htwf, hnd, howned, hf, hkeep⟩
      simp only [allocateMany, he, ht]
      refine ⟨htwf, List.nodup_cons.mpr ⟨?_, hnd⟩, ?_, ?_, ?_⟩
      · intro hm
        exact hf slot hm hlive
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hkeep x hlive
        · exact howned x hx
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfresh
        · intro hxold
          exact hf x hx (hold x hxold)
      · intro x hx
        exact hkeep x (hold x hx)

/-- Every successful release preserves the exact live/free partition. -/
theorem releaseOne_wellFormed (s : HCNativeAllocatorState) (hs : s.WellFormed)
    (slot : ℕ) (t : HCNativeAllocatorState) (h : releaseOne slot s = some t) :
    t.WellFormed := by
  unfold releaseOne at h
  split at h
  next hm =>
    cases h
    refine ⟨hs.live_nodup.erase slot, List.nodup_cons.mpr ⟨hs.separate slot hm, hs.free_nodup⟩,
      ?_, ?_, ?_⟩
    · intro x hx hxfree
      rcases List.mem_cons.mp hxfree with rfl | hxfree
      · exact hs.live_nodup.not_mem_erase hx
      · exact hs.separate x (List.mem_of_mem_erase hx) hxfree
    · intro x hx
      rcases hx with hx | hx
      · exact hs.bounded x (Or.inl (List.mem_of_mem_erase hx))
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hs.bounded x (Or.inl hm)
        · exact hs.bounded x (Or.inr hx)
    · intro x hx
      rcases hs.complete x hx with hx | hx
      · by_cases he : x = slot
        · right; simp [he]
        · left; exact (hs.live_nodup.mem_erase_iff).mpr ⟨he, hx⟩
      · right; simp [hx]
  next => cases h

/-- The actual release program satisfies the stated ownership, rejection or stack-order property under the displayed hypotheses. -/
theorem releaseMany_wellFormed (slots : List ℕ) (s : HCNativeAllocatorState)
    (hs : s.WellFormed) (t : HCNativeAllocatorState) (h : releaseMany slots s = some t) :
    t.WellFormed := by
  induction slots generalizing s with
  | nil =>
      simp only [releaseMany, Option.some.injEq] at h
      cases h
      exact hs
  | cons slot slots ih =>
      cases he : releaseOne slot s with
      | none => simp [releaseMany, he] at h
      | some s' =>
          have hw := releaseOne_wellFormed s hs slot s' he
          exact ih s' hw (by simpa [releaseMany, he] using h)

/-- The actual allocator satisfies the stated ownership and returned-frame property, including the displayed LIFO order where applicable. -/
theorem allocateMany_slots_length (k : ℕ) (s : HCNativeAllocatorState) :
    (allocateMany k s).2.length = k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [allocateMany]
      generalize he : allocateOne s = pair
      rcases pair with ⟨s', slot⟩
      have hi := ih s'
      generalize ht : allocateMany k s' = pair at hi ⊢
      rcases pair with ⟨t, slots⟩
      dsimp only at hi ⊢
      simp [hi]

/-- The actual allocator satisfies the stated ownership and returned-frame property, including the displayed LIFO order where applicable. -/
theorem allocateMany_live_length (k : ℕ) (s : HCNativeAllocatorState) :
    (allocateMany k s).1.live.length = s.live.length + k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      have h1 : (allocateOne s).1.live.length = s.live.length + 1 := by
        cases he : s.free <;> simp [allocateOne, he]
      simp only [allocateMany]
      generalize he : allocateOne s = pair at h1 ⊢
      rcases pair with ⟨s', slot⟩
      have hi := ih s'
      generalize ht : allocateMany k s' = pair at hi ⊢
      rcases pair with ⟨t, slots⟩
      dsimp only at h1 hi ⊢
      omega

/-- The actual release program satisfies the stated ownership, rejection or stack-order property under the displayed hypotheses. -/
theorem releaseOne_live_length (s : HCNativeAllocatorState) (slot : ℕ)
    (t : HCNativeAllocatorState) (h : releaseOne slot s = some t) :
    t.live.length + 1 = s.live.length := by
  unfold releaseOne at h
  split at h
  next hm =>
    cases h
    simp only [List.length_erase_of_mem hm]
    have hp := List.length_pos_of_mem hm
    omega
  next => cases h

/-- The actual release program satisfies the stated ownership, rejection or stack-order property under the displayed hypotheses. -/
theorem releaseMany_live_length (slots : List ℕ) (s t : HCNativeAllocatorState)
    (h : releaseMany slots s = some t) :
    t.live.length + slots.length = s.live.length := by
  induction slots generalizing s with
  | nil =>
      simp only [releaseMany, Option.some.injEq] at h
      cases h
      simp
  | cons slot slots ih =>
      cases he : releaseOne slot s with
      | none => simp [releaseMany, he] at h
      | some s' =>
          have h1 := releaseOne_live_length s slot s' he
          have hi := ih s' (by simpa [releaseMany, he] using h)
          simp only [List.length_cons]
          omega

/-- The actual release program satisfies the stated ownership, rejection or stack-order property under the displayed hypotheses. -/
theorem releaseOne_rejects_dead (s : HCNativeAllocatorState) (slot : ℕ)
    (h : slot ∉ s.live) : releaseOne slot s = none := by
  simp [releaseOne, h]

end HCNativeAllocatorState

/-- Pure coordinate lookup. No ownership/legality is asserted here. -/
def frameAddress (frame : List ℕ) (address : ℕ) : Option ℕ := frame[address]?

/-- Construction for frame Gate in the lifo allocator model. -/
def frameGate (frame : List ℕ) : FiniteGateCode → Option FiniteGateCode
  | .h a => (frameAddress frame a).map FiniteGateCode.h
  | .x a => (frameAddress frame a).map FiniteGateCode.x
  | .t a => (frameAddress frame a).map FiniteGateCode.t
  | .tdg a => (frameAddress frame a).map FiniteGateCode.tdg
  | .cx a b => do
      let pa ← frameAddress frame a
      let pb ← frameAddress frame b
      pure (.cx pa pb)

/-- Construction for frame Word in the lifo allocator model. -/
def frameWord (frame : List ℕ) (word : List FiniteGateCode) : Option (List FiniteGateCode) :=
  word.mapM (frameGate frame)

/-- Construction for frame Events in the lifo allocator model. -/
def frameEvents (frame : List ℕ) (word : List FiniteGateCode) : Option (List HCNativeEvent) :=
  (frameWord frame word).map (List.map HCNativeEvent.gate)

/-- A sufficient frame domain, stronger than Python's referenced-wire checks. -/
def allocatorFrameOwned (s : HCNativeAllocatorState) (frame : List ℕ) : Prop :=
  frame.Nodup ∧ ∀ x ∈ frame, x ∈ s.live

instance (s : HCNativeAllocatorState) (frame : List ℕ) : Decidable (allocatorFrameOwned s frame) :=
  inferInstanceAs (Decidable (frame.Nodup ∧ ∀ x ∈ frame, x ∈ s.live))

/-- Construction for allocator Gate Owned in the lifo allocator model. -/
def allocatorGateOwned (s : HCNativeAllocatorState) : FiniteGateCode → Prop
  | .h a | .x a | .t a | .tdg a => a ∈ s.live
  | .cx a b => a ≠ b ∧ a ∈ s.live ∧ b ∈ s.live

instance (s : HCNativeAllocatorState) (g : FiniteGateCode) : Decidable (allocatorGateOwned s g) := by
  cases g <;> unfold allocatorGateOwned <;> infer_instance

/-- Guarded physical gate relabeling. Self-CX is rejected even in an owned frame. -/
def ownedFrameGate (s : HCNativeAllocatorState) (frame : List ℕ) (g : FiniteGateCode) :
    Option FiniteGateCode :=
  if allocatorFrameOwned s frame then
    match frameGate frame g with
    | none => none
    | some physical => if allocatorGateOwned s physical then some physical else none
  else none

/-- The finite allocator and event interpreter preserve the stated exact invariant under the displayed source hypotheses. -/
theorem ownedFrameGate_sound (s : HCNativeAllocatorState) (frame : List ℕ)
    (g physical : FiniteGateCode) (h : ownedFrameGate s frame g = some physical) :
    allocatorFrameOwned s frame ∧ frameGate frame g = some physical ∧ allocatorGateOwned s physical := by
  unfold ownedFrameGate at h
  split at h
  next hf =>
    cases he : frameGate frame g with
    | none => simp [he] at h
    | some p =>
        simp only [he] at h
        split at h
        next hp => cases h; exact ⟨hf, rfl, hp⟩
        next => cases h
  next => cases h

/-- Ownership commands emit primitive labels, with no Born law or matrix field. -/
inductive HCNativeAllocatorOp where
  | allocate (width : ℕ)
  | release (slots : List ℕ)
  | gate (frame : List ℕ) (code : FiniteGateCode)
  | measure (slot : ℕ) (outcome : Bool)
  deriving DecidableEq, Repr

/-- Construction for execute Allocator Op in the lifo allocator model. -/
def executeAllocatorOp (op : HCNativeAllocatorOp) (s : HCNativeAllocatorState) :
    Option (HCNativeAllocatorState × List HCNativeEvent) :=
  match op with
  | .allocate width =>
      let (t, slots) := s.allocateMany width
      some (t, slots.map HCNativeEvent.zero)
  | .release slots => (s.releaseMany slots).map (fun t => (t, slots.map HCNativeEvent.discard))
  | .gate frame code => (ownedFrameGate s frame code).map (fun g => (s, [.gate g]))
  | .measure slot b => if slot ∈ s.live then some (s, [.measure slot b]) else none

/-- Successful executions preserve the full ownership invariant for every op. -/
theorem executeAllocatorOp_wellFormed (op : HCNativeAllocatorOp) (s t : HCNativeAllocatorState)
    (hs : s.WellFormed) (es : List HCNativeEvent) (h : executeAllocatorOp op s = some (t, es)) :
    t.WellFormed := by
  cases op with
  | allocate k =>
      simp only [executeAllocatorOp, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ (HCNativeAllocatorState.allocateMany_spec k s hs).1
  | release slots =>
      cases he : s.releaseMany slots with
      | none => simp [executeAllocatorOp, he] at h
      | some u =>
          have hu := HCNativeAllocatorState.releaseMany_wellFormed slots s hs u he
          simp only [executeAllocatorOp, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact h.1 ▸ hu
  | gate frame code =>
      cases he : ownedFrameGate s frame code with
      | none => simp [executeAllocatorOp, he] at h
      | some g =>
          simp only [executeAllocatorOp, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact h.1 ▸ hs
  | measure slot b =>
      simp only [executeAllocatorOp] at h
      split at h
      next => cases h; exact hs
      next => cases h

/-- Construction for execute Allocator Ops in the lifo allocator model. -/
def executeAllocatorOps : List HCNativeAllocatorOp → HCNativeAllocatorState →
    Option (HCNativeAllocatorState × List HCNativeEvent)
  | [], s => some (s, [])
  | op :: ops, s => do
      let (s', beforeEvents) ← executeAllocatorOp op s
      let (t, suffix) ← executeAllocatorOps ops s'
      pure (t, beforeEvents ++ suffix)

/-- The finite allocator and event interpreter preserve the stated exact invariant under the displayed source hypotheses. -/
theorem executeAllocatorOps_wellFormed (ops : List HCNativeAllocatorOp)
    (s t : HCNativeAllocatorState) (hs : s.WellFormed) (es : List HCNativeEvent)
    (h : executeAllocatorOps ops s = some (t, es)) : t.WellFormed := by
  induction ops generalizing s t es with
  | nil => cases h; exact hs
  | cons op ops ih =>
      cases he : executeAllocatorOp op s with
      | none => simp [executeAllocatorOps, he] at h
      | some pair =>
          rcases pair with ⟨s', beforeEvents⟩
          have hw := executeAllocatorOp_wellFormed op s s' hs beforeEvents he
          cases hr : executeAllocatorOps ops s' with
          | none => simp [executeAllocatorOps, he, hr] at h
          | some pair =>
              rcases pair with ⟨u, suffix⟩
              simp [executeAllocatorOps, he, hr] at h
              have hu := ih s' u hw suffix hr
              exact h.1 ▸ hu

/-- Construction for allocator Event Delta in the lifo allocator model. -/
private def allocatorEventDelta : HCNativeEvent → ℤ
  | .zero _ => 1
  | .discard _ => -1
  | .gate _ | .measure _ _ => 0

/-- The bill of the stated actual finite event trace satisfies the displayed exact live-count accounting identity. -/
private theorem allocator_net_cons (e : HCNativeEvent) (es : List HCNativeEvent) :
    (hcNativeBill (e :: es)).net = allocatorEventDelta e + (hcNativeBill es).net := by
  cases e <;> rfl

/-- The bill of the stated actual finite event trace satisfies the displayed exact live-count accounting identity. -/
private theorem allocator_net_append (a b : List HCNativeEvent) :
    (hcNativeBill (a ++ b)).net = (hcNativeBill a).net + (hcNativeBill b).net := by
  induction a with
  | nil => simp only [List.nil_append]; change _ = 0 + _; omega
  | cons e a ih =>
      rw [List.cons_append, allocator_net_cons, ih, allocator_net_cons]
      omega

/-- The bill of the stated actual finite event trace satisfies the displayed exact live-count accounting identity. -/
private theorem allocator_zero_net (slots : List ℕ) :
    (hcNativeBill (slots.map HCNativeEvent.zero)).net = (slots.length : ℤ) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      simp only [List.map_cons, allocator_net_cons, allocatorEventDelta, ih, List.length_cons]
      omega

/-- The bill of the stated actual finite event trace satisfies the displayed exact live-count accounting identity. -/
private theorem allocator_discard_net (slots : List ℕ) :
    (hcNativeBill (slots.map HCNativeEvent.discard)).net = -(slots.length : ℤ) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      simp only [List.map_cons, allocator_net_cons, allocatorEventDelta, ih, List.length_cons]
      omega

/-- Exact signed live-count conservation for every successful primitive command.
It does not identify the relative bill.high with allocator capacity/next. -/
theorem executeAllocatorOp_net (op : HCNativeAllocatorOp) (s t : HCNativeAllocatorState)
    (es : List HCNativeEvent) (h : executeAllocatorOp op s = some (t, es)) :
    (hcNativeBill es).net = (t.live.length : ℤ) - (s.live.length : ℤ) := by
  cases op with
  | allocate k =>
      have he : (s.allocateMany k).1 = t ∧
          (s.allocateMany k).2.map HCNativeEvent.zero = es := by
        simpa only [executeAllocatorOp, Option.some.injEq, Prod.mk.injEq] using h
      rw [← he.2, allocator_zero_net, ← he.1]
      have hl := HCNativeAllocatorState.allocateMany_live_length k s
      have hk := HCNativeAllocatorState.allocateMany_slots_length k s
      omega
  | release slots =>
      cases hr : s.releaseMany slots with
      | none => simp [executeAllocatorOp, hr] at h
      | some u =>
          have he : u = t ∧ slots.map HCNativeEvent.discard = es := by
            simpa only [executeAllocatorOp, hr, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] using h
          rw [← he.2, allocator_discard_net, ← he.1]
          have hl := HCNativeAllocatorState.releaseMany_live_length slots s u hr
          omega
  | gate frame code =>
      cases hg : ownedFrameGate s frame code with
      | none => simp [executeAllocatorOp, hg] at h
      | some g =>
          have he : s = t ∧ [HCNativeEvent.gate g] = es := by
            simpa only [executeAllocatorOp, hg, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] using h
          rw [← he.1, ← he.2]
          change 0 = _ - _
          omega
  | measure slot b =>
      simp only [executeAllocatorOp] at h
      split at h
      next =>
        cases h
        change 0 = _ - _
        omega
      next => cases h

/-- Successful event execution ties the existing signed bill to actual final
and initial live-list lengths, for arbitrary command lists and allocator states. -/
theorem executeAllocatorOps_net (ops : List HCNativeAllocatorOp) (s t : HCNativeAllocatorState)
    (es : List HCNativeEvent) (h : executeAllocatorOps ops s = some (t, es)) :
    (hcNativeBill es).net = (t.live.length : ℤ) - (s.live.length : ℤ) := by
  induction ops generalizing s t es with
  | nil =>
      cases h
      change 0 = _ - _
      omega
  | cons op ops ih =>
      cases he : executeAllocatorOp op s with
      | none => simp [executeAllocatorOps, he] at h
      | some pair =>
          rcases pair with ⟨s', beforeEvents⟩
          have h1 := executeAllocatorOp_net op s s' beforeEvents he
          cases hr : executeAllocatorOps ops s' with
          | none => simp [executeAllocatorOps, he, hr] at h
          | some pair =>
              rcases pair with ⟨u, suffix⟩
              have heq : u = t ∧ beforeEvents ++ suffix = es := by
                simpa [executeAllocatorOps, he, hr] using h
              have hi := ih s' u suffix hr
              rw [← heq.2, allocator_net_append, h1, hi, ← heq.1]
              omega

/-- Original finite regression stream, retained as a fixture rather than a
claim of all-parameter Python extraction. -/
def allocatorBridgeEvents : List HCNativeEvent :=
  [.zero 0, .zero 1, .zero 2,
   .discard 1, .discard 2,
   .zero 2, .zero 1,
   .discard 1, .discard 2, .discard 0]

open HCNativeAllocatorState

/-- The actual allocator satisfies the stated ownership and returned-frame property, including the displayed LIFO order where applicable. -/
theorem allocate_three_fresh : allocateMany 3 empty =
    (⟨[2, 1, 0], [], 3⟩, [0, 1, 2]) := by decide

/-- The actual release program satisfies the stated ownership, rejection or stack-order property under the displayed hypotheses. -/
theorem release_two_stack_order : releaseMany [1, 2] ⟨[2, 1, 0], [], 3⟩ =
    some ⟨[0], [2, 1], 3⟩ := by decide

/-- The actual allocator satisfies the stated ownership and returned-frame property, including the displayed LIFO order where applicable. -/
theorem allocate_two_lifo_reuse : allocateMany 2 ⟨[0], [2, 1], 3⟩ =
    (⟨[1, 2, 0], [], 3⟩, [2, 1]) := by decide

/-- The finite address relabeling or guarded gate operation satisfies its displayed ownership and rejection contract. -/
theorem frame_word_concrete : frameWord [10, 11] [.cx 1 0, .h 0, .tdg 1] =
    some [.cx 11 10, .h 10, .tdg 11] := by decide

/-- The finite address relabeling or guarded gate operation satisfies its displayed ownership and rejection contract. -/
theorem frame_word_rejects_missing_address : frameWord [10] [.cx 1 0] = none := by decide

/-- The bill of the stated actual finite event trace satisfies the displayed exact live-count accounting identity. -/
theorem allocator_bridge_bill : hcNativeBill allocatorBridgeEvents =
    ⟨0, 5, 0, 5, 0, 0, 3⟩ := by decide

end Qatlib.Concepts.MatrixAccess.MatrixBackend.LifoAllocator
