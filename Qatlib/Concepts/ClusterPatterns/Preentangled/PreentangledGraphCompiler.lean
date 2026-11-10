/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphLayout
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.WireComposition

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker
namespace Qatlib.Concepts.ClusterPatterns.Preentangled

theorem graphOverlay_spectator (n L : ℕ) (lay : Fin n → Fin (n+L))
    (z : Reg (n+L)) (y : Reg n) (q : Fin (n+L)) (hq : ∀ i, q ≠ lay i) :
    graphOverlay n L lay z y q = z q := by
  have h : ∀ (ts : List (Fin n)) (z : Reg (n+L)),
      ts.foldl (fun z i => Function.update z (lay i) (y i)) z q = z q := by
    intro ts
    induction ts with
    | nil => intro z; rfl
    | cons i ts ih =>
      intro z
      simp only [List.foldl_cons, ih, Function.update_of_ne (hq i)]
  exact h _ z

theorem graphOverlay_active (n L : ℕ) (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (z : Reg (n+L)) (y : Reg n) (i : Fin n) :
    graphOverlay n L lay z y (lay i) = y i := by
  have keep : ∀ (ts : List (Fin n)) (z : Reg (n+L)), z (lay i) = y i →
      ts.foldl (fun z j => Function.update z (lay j) (y j)) z (lay i) = y i := by
    intro ts
    induction ts with
    | nil => intro z hz; exact hz
    | cons j ts ih =>
      intro z hz
      apply ih
      by_cases hj : j = i
      · subst j; simp
      · (try dsimp only)
        rw [Function.update_of_ne (fun he => hj (hlay he.symm))]
        exact hz
  have set : ∀ (ts : List (Fin n)) (z : Reg (n+L)), i ∈ ts →
      ts.foldl (fun z j => Function.update z (lay j) (y j)) z (lay i) = y i := by
    intro ts
    induction ts with
    | nil => simp
    | cons j ts ih =>
      intro z hi
      rcases List.mem_cons.mp hi with he | hi
      · subst j
        exact keep ts _ (by simp)
      · exact ih _ hi
  exact set _ z (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem graphCorrectionGates_zero {n L : ℕ} (gs : GraphWord n L) :
    graphCorrectionGates gs (zeroPauliFrame n) = [] := by
  simp [graphCorrectionGates, zeroPauliFrame, List.ofFn_const]

theorem graphProgram_empty (n : ℕ) (pre : Bool) :
    graphProgram pre (Fin.elim0 : GraphWord n 0) = .halt true := by
  cases pre <;> simp [graphProgram, graphFreshGates, graphEdgeGates, graphTail,
    graphCorrectionGates_zero, graphPrepend]

theorem graphInputFrame_empty (n : ℕ) : graphInputFrame n 0 = (1 : Operator (2^n)) := by
  ext r j
  rw [graphInputFrame_entry]
  have hi : graphInputIndex n 0 j = j := by
    apply (bitVecEquiv n).symm.injective
    funext i
    simpa [graphInputIndex] using! Fin.append_left ((bitVecEquiv n).symm j)
      (fun _ : Fin 0 => false) i
  simp [hi, Matrix.one_apply]

theorem graphDiscardReference_empty (n R : ℕ)
    (A : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :
    graphDiscardReference n 0 R (Fin.castAdd 0) A = A := by
  have ho : ∀ (z : Reg n) (y : Reg n), graphOverlay n 0 (Fin.castAdd 0) z y = y := by
    intro z y
    funext i
    simpa using! graphOverlay_active n 0 (Fin.castAdd 0) (Fin.castAdd_injective n 0) z y i
  ext p q
  unfold graphDiscardReference
  have he : ∀ z : Reg n, (∀ i, z (Fin.castAdd 0 i) = (bitVecEquiv n).symm p.1 i) ↔
      z = (bitVecEquiv n).symm p.1 := by
    intro z
    simp only [Fin.castAdd_zero]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp only [he, ho]
  simp

def graphBitsIndex (bs : List Bool) : ℕ :=
  bs.foldl (fun a b => 2*a+(if b then 1 else 0)) 0

theorem graphBitsIndex_acc (bs : List Bool) (a : ℕ) :
    bs.foldl (fun a b => 2*a+(if b then 1 else 0)) a =
      2^bs.length*a+graphBitsIndex bs := by
  induction bs generalizing a with
  | nil => simp [graphBitsIndex]
  | cons b bs ih =>
    change bs.foldl _ (2*a+(if b then 1 else 0)) =
      2^(bs.length+1)*a + bs.foldl _ (2*0+(if b then 1 else 0))
    rw [ih, ih, pow_succ]
    ring

theorem graphBitsIndex_cons (b : Bool) (bs : List Bool) :
    graphBitsIndex (b::bs) = (if b then 2^bs.length else 0)+graphBitsIndex bs := by
  change bs.foldl _ (2*0+(if b then 1 else 0)) = _
  rw [graphBitsIndex_acc]
  cases b <;> simp

theorem graphBitsIndex_lt (bs : List Bool) : graphBitsIndex bs < 2^bs.length := by
  induction bs with
  | nil => simp [graphBitsIndex]
  | cons b bs ih =>
    rw [graphBitsIndex_cons, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add] <;>
      omega

theorem graphBitsIndex_injective (bs cs : List Bool) (hlen : bs.length=cs.length)
    (he : graphBitsIndex bs=graphBitsIndex cs) : bs=cs := by
  induction bs generalizing cs with
  | nil => simpa using! hlen.symm
  | cons b bs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hl : bs.length=cs.length := by simpa using! hlen
      have hb := graphBitsIndex_lt bs
      have hc := graphBitsIndex_lt cs
      rw [graphBitsIndex_cons, graphBitsIndex_cons, hl] at he
      have hbc : b=c := by
        cases b <;> cases c <;> (simp_all; try omega)
      subst c
      have hi : graphBitsIndex bs=graphBitsIndex cs := by omega
      exact congrArg (List.cons b) (ih cs hl hi)

theorem graphHistoryIndex_lt {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    graphHistoryIndex gs h < 2^(graphWireCount gs) := by
  simpa [graphHistoryIndex, graphBitsIndex, graphMessage_length] using!
    graphBitsIndex_lt (graphMessage gs h)

theorem graphHistoryIndex_injective {n L : ℕ} (gs : GraphWord n L) :
    Function.Injective (graphHistoryIndex gs) := by
  intro h k he
  apply graphMessage_injective gs
  exact graphBitsIndex_injective _ _ (by rw [graphMessage_length, graphMessage_length]) he

noncomputable def graphPrependLeaf {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) : ObservedKrausLeaf D :=
  Us.foldr (fun U leaf => leaf.prepend U 0 1 0 []) leaf

theorem graphPrependLeaf_get {D : ℕ} (Us : List (Operator D))
    (P : ObservedCircuit (Fin D)) (k : ℕ) (leaf : ObservedKrausLeaf D)
    (hk : (observedKrausLeaves 1 P)[k]?=some leaf) :
    (observedKrausLeaves 1 (graphPrepend Us P))[k]?=some (graphPrependLeaf Us leaf) := by
  induction Us with
  | nil => exact hk
  | cons U Us ih =>
    change ((observedKrausLeaves 1 (graphPrepend Us P)).map
      (ObservedKrausLeaf.prepend U 0 1 0 []))[k]? = _
    rw [List.getElem?_map, ih]
    rfl

theorem graphGateLeaf_get {D : ℕ} (U : Operator D) (P : ObservedCircuit (Fin D))
    (k : ℕ) (leaf : ObservedKrausLeaf D)
    (hk : (observedKrausLeaves 1 P)[k]?=some leaf) :
    (observedKrausLeaves 1 (.step (.gate U) P))[k]?=some (leaf.prepend U 0 1 0 []) := by
  change ((observedKrausLeaves 1 P).map _)[k]? = _
  rw [List.getElem?_map, hk]
  rfl

noncomputable def graphTailLeaf {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) : List (Fin L) → PauliFrame n → ObservedKrausLeaf (2^(n+L))
  | [], F => graphPrependLeaf (graphCorrectionGates gs F) ⟨1,true,0,0,0,[]⟩
  | t::ts, F =>
    let rest := graphTailLeaf pre gs h ts (graphFrameAdvance gs h F t)
    let measured := match gs t with
      | .inl (i,ζ) =>
        ((rest.prepend (graphPhysicalProjector n L (graphLayoutBefore gs t i) (h.1 t))
          0 0 1 [(2,(boolEquivFin2 (h.1 t)).val)]).prepend
          (graphPhysicalH n L (graphLayoutBefore gs t i)) 0 1 0 []).prepend
          (graphPhysicalPhase n L (graphLayoutBefore gs t i)
            (if F.1 i then star ζ else ζ)) 0 1 0 []
      | .inr _ => rest
    if pre then measured else measured.prepend
      (networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2) 0 1 0 []

def graphTailMessage {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) : List Bool :=
  ts.filterMap (fun t => if graphWireAt gs t then some (h.1 t) else none)

theorem graphTailMessage_length {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) : (graphTailMessage gs h ts).length=graphSlotCount gs ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    dsimp [graphTailMessage, graphSlotCount] at ih
    cases ht : graphWireAt gs t <;>
      simp [graphTailMessage, graphSlotCount, ht, ih, Nat.add_comm]

theorem graphMeasurementLeaf_get {D : ℕ} (label : Fin D → Fin 2)
    (next : Fin 2 → ObservedCircuit (Fin D)) (a : Bool) (k N : ℕ)
    (hlen : ∀ o, (observedKrausLeaves 1 (next o)).length=N) (hk : k<N)
    (leaf : ObservedKrausLeaf D)
    (he : (observedKrausLeaves 1 (next (boolEquivFin2 a)))[k]?=some leaf) :
    (observedKrausLeaves 1 (.measure 2 label next))[(if a then N else 0)+k]?=
      some (leaf.prepend (Projector (Finset.univ.filter
        (fun i => label i=boolEquivFin2 a))) 0 0 1 [(2,(boolEquivFin2 a).val)]) := by
  cases a
  · simp only [Bool.false_eq_true, if_false, zero_add, observedKrausLeaves,
      List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.getElem?_append_left (by simpa [hlen] using! hk), List.getElem?_map]
    simpa [boolEquivFin2] using! congrArg
      (Option.map (ObservedKrausLeaf.prepend
        (Projector (Finset.univ.filter (fun i => label i=0))) 0 0 1 [(2,0)])) he
  · simp only [if_true, observedKrausLeaves, List.ofFn_succ, List.ofFn_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.getElem?_append_right (by simp [hlen]), List.length_map, hlen,
      Nat.add_sub_cancel_left, List.getElem?_map]
    simpa [boolEquivFin2] using! congrArg
      (Option.map (ObservedKrausLeaf.prepend
        (Projector (Finset.univ.filter (fun i => label i=1))) 0 0 1 [(2,1)])) he

theorem graphTailLeaf_get {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) (ts : List (Fin L)) (F : PauliFrame n) :
    (observedKrausLeaves 1 (graphTail pre gs ts F))[graphBitsIndex (graphTailMessage gs h ts)]?=
      some (graphTailLeaf pre gs h ts F) := by
  induction ts generalizing F with
  | nil =>
    exact graphPrependLeaf_get _ (.halt true) 0 _ rfl
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      have hm := graphMeasurementLeaf_get (graphPhysicalLabel n L (graphLayoutBefore gs t i))
        (fun a => graphTail pre gs ts (graphWireFrame F i (boolEquivFin2.symm a)))
        (h.1 t) (graphBitsIndex (graphTailMessage gs h ts)) (2^(graphSlotCount gs ts))
        (fun o => by rw [observedKrausLeaves_length, graphTail_leafCount])
        (by simpa [graphTailMessage_length] using! graphBitsIndex_lt (graphTailMessage gs h ts))
        _ (by simpa using! ih (graphWireFrame F i (h.1 t)))
      have hmH := graphGateLeaf_get (graphPhysicalH n L (graphLayoutBefore gs t i)) _ _ _ hm
      have hmP := graphGateLeaf_get (graphPhysicalPhase n L (graphLayoutBefore gs t i)
        (if F.1 i then star ζ else ζ)) _ _ _ hmH
      have hmsg : graphTailMessage gs h (t::ts) = h.1 t::graphTailMessage gs h ts := by
        simp [graphTailMessage, graphWireAt, hg]
      rw [hmsg, graphBitsIndex_cons, graphTailMessage_length]
      cases pre
      · have he := graphGateLeaf_get
          (networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2) _ _ _ hmP
        simpa only [graphTail, graphTailLeaf, hg, graphFrameAdvance, Bool.false_eq_true,
          if_false, graphPhysicalProjector] using! he
      · simpa only [graphTail, graphTailLeaf, hg, graphFrameAdvance, if_true,
          graphPhysicalProjector] using! hmP
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hmsg : graphTailMessage gs h (t::ts) = graphTailMessage gs h ts := by
        simp [graphTailMessage, graphWireAt, hg]
      rw [hmsg]
      cases pre
      · simpa only [graphTail, graphTailLeaf, hg, graphFrameAdvance, Bool.false_eq_true,
          if_false] using! graphGateLeaf_get
          (networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2) _ _ _
          (ih (graphCzFrame F i j))
      · simpa only [graphTail, graphTailLeaf, hg, graphFrameAdvance, if_true] using!
          ih (graphCzFrame F i j)

@[simp] theorem graphPrependLeaf_accepted {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) : (graphPrependLeaf Us leaf).accepted=leaf.accepted := by
  induction Us with
  | nil => rfl
  | cons U Us ih => simpa [graphPrependLeaf, ObservedKrausLeaf.prepend] using! ih

@[simp] theorem graphPrependLeaf_queries {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) : (graphPrependLeaf Us leaf).queries=leaf.queries := by
  induction Us with
  | nil => rfl
  | cons U Us ih => simpa [graphPrependLeaf, ObservedKrausLeaf.prepend] using! ih

@[simp] theorem graphPrependLeaf_gates {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) : (graphPrependLeaf Us leaf).gates=leaf.gates+Us.length := by
  induction Us with
  | nil => simp [graphPrependLeaf]
  | cons U Us ih =>
    change (graphPrependLeaf Us leaf).gates+1=leaf.gates+(Us.length+1)
    rw [ih, Nat.add_assoc]

@[simp] theorem graphPrependLeaf_measurements {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) : (graphPrependLeaf Us leaf).measurements=leaf.measurements := by
  induction Us with
  | nil => rfl
  | cons U Us ih => simpa [graphPrependLeaf, ObservedKrausLeaf.prepend] using! ih

theorem graphTailLeaf_resources {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    (graphTailLeaf true gs h ts F).accepted=true ∧
    (graphTailLeaf true gs h ts F).queries=0 ∧
    (graphTailLeaf true gs h ts F).gates=2*graphSlotCount gs ts+
      frameCorrectionCost (ts.foldl (graphFrameAdvance gs h) F) ∧
    (graphTailLeaf true gs h ts F).measurements=graphSlotCount gs ts := by
  induction ts generalizing F with
  | nil => simp only [graphTailLeaf, graphPrependLeaf_accepted, graphPrependLeaf_queries,
      graphPrependLeaf_gates, graphPrependLeaf_measurements, graphCorrectionGates_length,
      graphSlotCount, List.map_nil, List.sum_nil, List.foldl_nil, mul_zero, zero_add,
      and_self]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      obtain ⟨ha,hq,hgates,hm⟩ := ih (graphWireFrame F i (h.1 t))
      have hc : graphSlotCount gs (t::ts)=graphSlotCount gs ts+1 := by
        simp [graphSlotCount, graphWireAt, hg, Nat.add_comm]
      simp only [graphTailLeaf, hg, if_true, graphFrameAdvance, ObservedKrausLeaf.prepend,
        ha, hq, hgates, hm, hc, List.foldl_cons, Nat.add_zero]
      exact ⟨trivial,trivial,by omega,trivial⟩
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hc : graphSlotCount gs (t::ts)=graphSlotCount gs ts := by
        simp [graphSlotCount, graphWireAt, hg]
      simpa only [graphTailLeaf, hg, if_true, graphFrameAdvance, hc, List.foldl_cons] using!
        ih (graphCzFrame F i j)

theorem graphProgramLeaf_eq {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) :
    graphProgramLeaf pre gs h = graphPrependLeaf (graphFreshGates n L)
      (if pre then graphPrependLeaf (graphEdgeGates gs)
        (graphTailLeaf true gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))
       else graphTailLeaf false gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)) := by
  have ht := graphTailLeaf_get pre gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  have he : (observedKrausLeaves 1 (graphProgram pre gs))[graphHistoryIndex gs h]?=
      some (graphPrependLeaf (graphFreshGates n L)
        (if pre then graphPrependLeaf (graphEdgeGates gs)
          (graphTailLeaf true gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))
         else graphTailLeaf false gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))) := by
    cases pre
    · exact graphPrependLeaf_get _ _ _ _ ht
    · exact graphPrependLeaf_get _ _ _ _ (graphPrependLeaf_get _ _ _ _ ht)
  rw [graphProgramLeaf, List.getD_eq_getElem?_getD, he]
  rfl

noncomputable def graphGateProduct {D : ℕ} (Us : List (Operator D)) : Operator D :=
  Us.foldr (fun U K => K*U) 1

theorem graphPrependLeaf_operator {D : ℕ} (Us : List (Operator D))
    (leaf : ObservedKrausLeaf D) :
    (graphPrependLeaf Us leaf).operator=leaf.operator*graphGateProduct Us := by
  induction Us with
  | nil => simp [graphPrependLeaf, graphGateProduct]
  | cons U Us ih =>
    change (graphPrependLeaf Us leaf).operator*U=leaf.operator*(graphGateProduct Us*U)
    rw [ih, Matrix.mul_assoc]

theorem graphGateProduct_commute {D : ℕ} (Us : List (Operator D)) (A : Operator D)
    (hcomm : ∀ U ∈ Us, U*A=A*U) : graphGateProduct Us*A=A*graphGateProduct Us := by
  induction Us with
  | nil => simp [graphGateProduct]
  | cons U Us ih =>
    change (graphGateProduct Us*U)*A=A*(graphGateProduct Us*U)
    rw [Matrix.mul_assoc, hcomm U (by simp), ← Matrix.mul_assoc,
      ih (fun V hV => hcomm V (by simp [hV])), Matrix.mul_assoc]

theorem graphTailLeaf_retiming {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs)
    (ts : List (Fin L)) (horder : ts.Pairwise (· < ·)) (F : PauliFrame n) :
    (graphTailLeaf false gs h ts F).operator = (graphTailLeaf true gs h ts F).operator *
      graphGateProduct (ts.map (fun t =>
        networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2)) := by
  induction ts generalizing F with
  | nil => simp [graphTailLeaf, graphGateProduct]
  | cons t ts ih =>
    obtain ⟨hfuture,hrest⟩ := List.pairwise_cons.mp horder
    specialize ih hrest
    cases hg : gs t with
    | inr p =>
      obtain ⟨i,j⟩ := p
      simpa only [graphTailLeaf, hg, graphFrameAdvance, Bool.false_eq_true, if_false,
        if_true, ObservedKrausLeaf.prepend, List.map_cons, graphGateProduct,
        List.foldr_cons, Matrix.mul_assoc] using!
        congrArg (fun K => K*networkCzGate (graphEdgeEndpoints gs t).1
          (graphEdgeEndpoints gs t).2) (ih (graphCzFrame F i j))
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      let E := graphGateProduct (ts.map (fun s =>
        networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2))
      have hcomm : ∀ (s : Fin L), s ∈ ts →
          networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 *
              graphPhysicalH n L (graphLayoutBefore gs t i) =
            graphPhysicalH n L (graphLayoutBefore gs t i) *
              networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 ∧
          networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 *
              graphPhysicalPhase n L (graphLayoutBefore gs t i) (if F.1 i then star ζ else ζ) =
            graphPhysicalPhase n L (graphLayoutBefore gs t i) (if F.1 i then star ζ else ζ) *
              networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 ∧
          networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 *
              graphPhysicalProjector n L (graphLayoutBefore gs t i) (h.1 t) =
            graphPhysicalProjector n L (graphLayoutBefore gs t i) (h.1 t) *
              networkCzGate (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2 := by
        intro s hs
        obtain ⟨hu,hv,_⟩ := (graph_layout_geometry gs hlegal).2.2.2 t s i ζ (hfuture s hs) hg
        exact (preentangled_graph_physical_disjoint_commutation n L
          (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2
          (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2
          (graphLayoutBefore gs t i) (if F.1 i then star ζ else ζ) (h.1 t)).2
          (Ne.symm hu) (Ne.symm hv)
      have hE (A : Operator (2^(n+L)))
          (hA : ∀ s ∈ ts, networkCzGate (graphEdgeEndpoints gs s).1
            (graphEdgeEndpoints gs s).2*A=A*networkCzGate
              (graphEdgeEndpoints gs s).1 (graphEdgeEndpoints gs s).2) : E*A=A*E := by
        apply graphGateProduct_commute
        intro U hU
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hU
        exact hA s hs
      have hH := hE _ (fun s hs => (hcomm s hs).1)
      have hPhase := hE _ (fun s hs => (hcomm s hs).2.1)
      have hP := hE _ (fun s hs => (hcomm s hs).2.2)
      simp only [graphTailLeaf, hg, graphFrameAdvance, Bool.false_eq_true, if_false,
        if_true, ObservedKrausLeaf.prepend, List.map_cons, graphGateProduct,
        List.foldr_cons]
      rw [ih (graphWireFrame F i (h.1 t))]
      change ((((_*E)*_)*_)*_)*_ = (((_*_)*_)*_)*(E*_)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc E, hP, Matrix.mul_assoc, ← Matrix.mul_assoc E, hH,
        Matrix.mul_assoc, ← Matrix.mul_assoc E, hPhase, Matrix.mul_assoc]

theorem graphPrepend_wellFormed {D : ℕ} (Us : List (Operator D))
    (P : ObservedCircuit (Fin D)) (hUs : ∀ U ∈ Us, U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hP : observedWellFormed P) : observedWellFormed (graphPrepend Us P) := by
  induction Us with
  | nil => exact hP
  | cons U Us ih =>
    exact ⟨hUs U (by simp), ih (fun V hV => hUs V (by simp [hV]))⟩

theorem graphPhysicalH_unitary (n L : ℕ) (q : Fin (n+L)) :
    graphPhysicalH n L q ∈ Matrix.unitaryGroup (Fin (2^(n+L))) ℂ :=
  tensorPauliWireGate_unitary _ _ _ (teleportRelabelGate_mem_unitaryGroup hadamard_unitary _)

theorem graphPhysicalPhase_unitary (n L : ℕ) (q : Fin (n+L)) (ζ : ℂ) (hζ : ‖ζ‖=1) :
    graphPhysicalPhase n L q ζ ∈ Matrix.unitaryGroup (Fin (2^(n+L))) ℂ :=
  tensorPauliWireGate_unitary _ _ _ (clusterPhase_unitary hζ)

theorem graphCorrectionGates_unitary {n L : ℕ} (gs : GraphWord n L) (F : PauliFrame n) :
    ∀ U ∈ graphCorrectionGates gs F, U ∈ Matrix.unitaryGroup (Fin (2^(n+L))) ℂ := by
  have hx : pauliX = relabelGate boolEquivFin2 PauliX := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hz : pauliZ = relabelGate boolEquivFin2 PauliZ := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  intro U hU
  obtain ⟨Us,hUs,hU⟩ := List.mem_flatten.mp hU
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hUs
  subst Us
  rcases List.mem_append.mp hU with hU | hU
  · split_ifs at hU with h
    · simp only [List.mem_singleton] at hU
      subst U
      exact tensorPauliWireGate_unitary _ _ _
        (hx.symm ▸ teleportRelabelGate_mem_unitaryGroup pauliX_unitary boolEquivFin2)
    · simp at hU
  · split_ifs at hU with h
    · simp only [List.mem_singleton] at hU
      subst U
      exact tensorPauliWireGate_unitary _ _ _
        (hz.symm ▸ teleportRelabelGate_mem_unitaryGroup pauliZ_unitary boolEquivFin2)
    · simp at hU

theorem graphTail_wellFormed {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (ts : List (Fin L)) (F : PauliFrame n) :
    observedWellFormed (graphTail pre gs ts F) := by
  induction ts generalizing F with
  | nil => exact graphPrepend_wellFormed _ _ (graphCorrectionGates_unitary gs F) trivial
  | cons t ts ih =>
    have hl := hlegal (gs t) (List.mem_ofFn.mpr ⟨t,rfl⟩)
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      simp only [hg] at hl
      have hζ : ‖(if F.1 i then star ζ else ζ)‖=1 := by split_ifs <;> simpa using! hl
      have hm : observedWellFormed
          (.step (.gate (graphPhysicalPhase n L (graphLayoutBefore gs t i)
              (if F.1 i then star ζ else ζ)))
            (.step (.gate (graphPhysicalH n L (graphLayoutBefore gs t i)))
              (.measure 2 (graphPhysicalLabel n L (graphLayoutBefore gs t i))
                (fun a => graphTail pre gs ts
                  (graphWireFrame F i (boolEquivFin2.symm a)))))) :=
        ⟨graphPhysicalPhase_unitary _ _ _ _ hζ,graphPhysicalH_unitary _ _ _,fun a => ih _⟩
      simp only [graphTail, hg]
      cases pre
      · exact ⟨networkCzGate_unitary _ _,hm⟩
      · exact hm
    | inr p =>
      obtain ⟨i,j⟩ := p
      simp only [graphTail, hg]
      cases pre
      · exact ⟨networkCzGate_unitary _ _,ih _⟩
      · exact ih _

theorem graphProgram_wellFormed {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) : observedWellFormed (graphProgram pre gs) := by
  apply graphPrepend_wellFormed
  · intro U hU
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hU
    exact graphPhysicalH_unitary _ _ _
  · cases pre
    · exact graphTail_wellFormed false gs hlegal _ _
    · apply graphPrepend_wellFormed
      · intro U hU
        obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hU
        exact networkCzGate_unitary _ _
      · exact graphTail_wellFormed true gs hlegal _ _

theorem preentangled_graph_actual_leaf_retiming :
    ∀ (n L : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
    observedWellFormed (graphProgram false gs) ∧ observedWellFormed (graphProgram true gs) ∧
    ∀ h : GraphHistory gs,
      (graphProgramLeaf false gs h).operator=(graphProgramLeaf true gs h).operator ∧
      graphHistoryIndex gs h < (observedKrausLeaves 1 (graphProgram true gs)).length ∧
      Function.Injective (graphHistoryIndex gs) := by
  intro n L gs hlegal
  refine ⟨graphProgram_wellFormed false gs hlegal,graphProgram_wellFormed true gs hlegal,?_⟩
  intro h
  refine ⟨?_,?_,graphHistoryIndex_injective gs⟩
  · have hr := graphTailLeaf_retiming gs hlegal h (List.ofFn (fun t : Fin L => t))
      (List.pairwise_ofFn.mpr (fun i j hij => hij)) (zeroPauliFrame n)
    simpa only [graphProgramLeaf_eq, Bool.false_eq_true, if_false, if_true,
      graphPrependLeaf_operator, graphEdgeGates, List.map_ofFn] using!
      congrArg (fun K => K*graphGateProduct (graphFreshGates n L)) hr
  · rw [observedKrausLeaves_length, graphProgram_leafCount]
    exact graphHistoryIndex_lt gs h

abbrev GraphSpectator {n L : ℕ} (lay : Fin n → Fin (n+L)) :=
  {q : Fin (n+L) // ∀ i, q ≠ lay i}

noncomputable def graphCoordinates {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) : Reg (n+L) ≃ Reg n × (GraphSpectator lay → Bool) where
  toFun z := (fun i => z (lay i),fun q => z q.1)
  invFun p q := if h : ∃ i, lay i=q then p.1 (Classical.choose h)
    else p.2 ⟨q,fun i hi => h ⟨i,hi.symm⟩⟩
  left_inv z := by
    funext q
    (try dsimp only)
    split_ifs with h
    · rw [Classical.choose_spec h]
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      (try dsimp only)
      have h : ∃ j, lay j=lay i := ⟨i,rfl⟩
      rw [dif_pos h]
      rw [hlay (Classical.choose_spec h)]
    · funext q
      (try dsimp only)
      have h : ¬∃ i, lay i=q.1 := by
        rintro ⟨i,hi⟩
        exact q.2 i hi.symm
      rw [dif_neg h]

theorem graphCoordinates_overlay {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (z : Reg (n+L)) (y : Reg n) :
    graphCoordinates lay hlay (graphOverlay n L lay z y)=
      (y,(graphCoordinates lay hlay z).2) := by
  apply Prod.ext
  · funext i
    exact graphOverlay_active n L lay hlay z y i
  · funext q
    exact graphOverlay_spectator n L lay z y q.1 q.2

theorem graphDiscardReference_coordinates (n L R : ℕ) (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay)
    (A : Matrix (Fin (2^(n+L)) × Fin R) (Fin (2^(n+L)) × Fin R) ℂ)
    (p q : Fin (2^n) × Fin R) :
    graphDiscardReference n L R lay A p q =
      ∑ s : GraphSpectator lay → Bool,
        A ((bitVecEquiv (n+L)) ((graphCoordinates lay hlay).symm
            ((bitVecEquiv n).symm p.1,s)),p.2)
          ((bitVecEquiv (n+L)) ((graphCoordinates lay hlay).symm
            ((bitVecEquiv n).symm q.1,s)),q.2) := by
  unfold graphDiscardReference
  rw [← (graphCoordinates lay hlay).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have hrestrict : ∀ (x : Reg n) (s : GraphSpectator lay → Bool),
      (∀ i, (graphCoordinates lay hlay).symm (x,s) (lay i)=(bitVecEquiv n).symm p.1 i) ↔
        x=(bitVecEquiv n).symm p.1 := by
    intro x s
    have ha := congrArg Prod.fst ((graphCoordinates lay hlay).apply_symm_apply (x,s))
    change (fun i => (graphCoordinates lay hlay).symm (x,s) (lay i))=x at ha
    simp only [congrFun ha]
    exact ⟨fun he => funext he,fun he i => congrFun he i⟩
  have hover : ∀ (x y : Reg n) (s : GraphSpectator lay → Bool),
      graphOverlay n L lay ((graphCoordinates lay hlay).symm (x,s)) y =
        (graphCoordinates lay hlay).symm (y,s) := by
    intro x y s
    apply (graphCoordinates lay hlay).injective
    rw [graphCoordinates_overlay, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [hrestrict, hover]
  simp

theorem graphWireB_mul_rows {N : ℕ} {J : Type*} (q : Fin N) (U : Operator 2)
    (A : Matrix (Reg N) J ℂ) (z : Reg N) (j : J) :
    (pauliProductDensity (fun k => if k=q then U else 1)*A) z j =
      ∑ b : Bool, U (boolEquivFin2 (z q)) (boolEquivFin2 b)*A (Function.update z q b) j := by
  rw [Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (fun b => Function.update z q b)
  · intro b c he
    simpa using! congrFun he q
  · intro y hy
    have hdiff : ∃ k, k ≠ q ∧ z k ≠ y k := by
      by_contra h
      push Not at h
      apply hy
      refine ⟨y q,?_⟩
      funext k
      by_cases hk : k=q
      · subst k; simp
      · simp [Function.update_of_ne hk, h k hk]
    obtain ⟨k,hk,hzk⟩ := hdiff
    rw [graph_wire_entry_zero q k U z y hk hzk, zero_mul]
  · intro b
    have hg : pauliProductDensity (fun k => if k=q then U else 1)
        z (Function.update z q b)=U (boolEquivFin2 (z q)) (boolEquivFin2 b) := by
      change (∏ k : Fin N, (if k=q then U else (1 : Operator 2))
        (boolEquivFin2 (z k)) (boolEquivFin2 (Function.update z q b k)))=_
      rw [Finset.prod_eq_single q]
      · simp
      · intro k _ hk
        rw [if_neg hk, Function.update_of_ne hk, Matrix.one_apply_eq]
      · simp
    rw [hg]

noncomputable def graphRowLiftB {n L : ℕ} {J : Type*} (lay : Fin n → Fin (n+L))
    (f : Reg (n+L) → ℂ) (A : Matrix (Reg n) J ℂ) : Matrix (Reg (n+L)) J ℂ :=
  fun z j => f z*A (fun i => z (lay i)) j

noncomputable def graphRowLift {n L : ℕ} {J : Type*} (lay : Fin n → Fin (n+L))
    (f : Reg (n+L) → ℂ) (A : Matrix (Reg n) J ℂ) : Matrix (Fin (2^(n+L))) J ℂ :=
  fun r j => graphRowLiftB lay f A ((bitVecEquiv (n+L)).symm r) j

theorem graphPhysicalWire_mul_rows {N : ℕ} {J : Type*} (q : Fin N) (U : Operator 2)
    (A : Matrix (Fin (2^N)) J ℂ) (z : Reg N) (j : J) :
    (tensorPauliWireGate N q U*A) ((bitVecEquiv N) z) j =
      ∑ b : Bool, U (boolEquivFin2 (z q)) (boolEquivFin2 b)*
        A ((bitVecEquiv N) (Function.update z q b)) j := by
  rw [Matrix.mul_apply, ← (bitVecEquiv N).sum_comp]
  simpa only [Matrix.mul_apply, tensorPauliWireGate, tensorPauliProduct, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using!
    graphWireB_mul_rows q U (fun y j => A ((bitVecEquiv N) y) j) z j

theorem graphLogicalCoords_update {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (i : Fin n) (z : Reg (n+L)) (b : Bool) :
    (fun k => Function.update z (lay i) b (lay k))=
      Function.update (fun k => z (lay k)) i b := by
  funext k
  by_cases hk : k=i
  · subst k; simp
  · simp [hk, Function.update_of_ne (fun he => hk (hlay he))]

theorem graphRowLift_active_wire {n L : ℕ} {J : Type*}
    (lay : Fin n → Fin (n+L)) (hlay : Function.Injective lay) (i : Fin n)
    (f : Reg (n+L) → ℂ) (hf : ∀ z b, f (Function.update z (lay i) b)=f z)
    (U : Operator 2) (A : Matrix (Reg n) J ℂ) :
    tensorPauliWireGate (n+L) (lay i) U * graphRowLift lay f A =
      graphRowLift lay f (pauliProductDensity (fun k => if k=i then U else 1)*A) := by
  ext r j
  obtain ⟨z,rfl⟩ := (bitVecEquiv (n+L)).surjective r
  rw [graphPhysicalWire_mul_rows]
  simp only [graphRowLift, graphRowLiftB, Equiv.symm_apply_apply,
    graphLogicalCoords_update lay hlay, hf]
  rw [graphWireB_mul_rows, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem graphRowLift_active_cz {n L : ℕ} {J : Type*}
    (lay : Fin n → Fin (n+L)) (i j : Fin n) (f : Reg (n+L) → ℂ)
    (A : Matrix (Reg n) J ℂ) :
    networkCzGate (lay i) (lay j)*graphRowLift lay f A =
      graphRowLift lay f (networkCzGateB i j*A) := by
  ext r k
  simp only [graph_cz_numeric_diagonal, networkCzGateB,
    graphRowLift, graphRowLiftB, Matrix.diagonal_mul]
  ring

theorem graphPhysicalPhase_mul_rows {n L : ℕ} {J : Type*} (v : Fin (n+L)) (ζ : ℂ)
    (A : Matrix (Fin (2^(n+L))) J ℂ) (z : Reg (n+L)) (j : J) :
    (graphPhysicalPhase n L v ζ*A) ((bitVecEquiv (n+L)) z) j =
      (if z v then ζ else 1)*A ((bitVecEquiv (n+L)) z) j := by
  rw [graphPhysicalPhase, graphPhysicalWire_mul_rows]
  cases hv : z v <;>
    simp [clusterPhase, Matrix.diagonal_apply, boolEquivFin2, ← hv]

theorem graphPhysicalProjector_mul_rows {n L : ℕ} {J : Type*} (v : Fin (n+L)) (a : Bool)
    (A : Matrix (Fin (2^(n+L))) J ℂ) (z : Reg (n+L)) (j : J) :
    (graphPhysicalProjector n L v a*A) ((bitVecEquiv (n+L)) z) j =
      if z v=a then A ((bitVecEquiv (n+L)) z) j else 0 := by
  rw [graph_physical_projector_diagonal, Matrix.diagonal_mul]
  simp [graphPhysicalLabel, (boolEquivFin2.injective.eq_iff)]

theorem graphPhysicalCz_mul_rows {N : ℕ} {J : Type*} (v q : Fin N)
    (A : Matrix (Fin (2^N)) J ℂ) (z : Reg N) (j : J) :
    (networkCzGate v q*A) ((bitVecEquiv N) z) j =
      (if z v && z q then (-1 : ℂ) else 1)*A ((bitVecEquiv N) z) j := by
  rw [graph_cz_numeric_diagonal, Matrix.diagonal_mul]
  simp

theorem graphLocalJ_entry (ζ : ℂ) (a b c : Bool) :
    relabelGate boolEquivFin2 Hadamard (boolEquivFin2 a) (boolEquivFin2 b) *
      (if b then ζ else 1)*(if b && c then (-1 : ℂ) else 1) =
        (pauliXChoice a*clusterJ ζ) (boolEquivFin2 c) (boolEquivFin2 b) := by
  cases a <;> cases b <;> cases c <;>
    simp [pauliXChoice, clusterJ_entry, relabelGate, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, Hadamard, PauliX,
      permMatrix, boolEquivFin2]

def graphSelectEnvelope {N : ℕ} (f : Reg N → ℂ) (v : Fin N) (a : Bool) : Reg N → ℂ :=
  fun z => if z v=a then f z else 0

theorem graphLogicalCoords_move {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (i : Fin n) (q : Fin (n+L))
    (z : Reg (n+L)) (b : Bool) :
    (fun k => Function.update z (lay i) b (lay k))=
      Function.update (fun k => z (Function.update lay i q k)) i b := by
  funext k
  by_cases hk : k=i
  · subst k; simp
  · simp [hk, Function.update_of_ne (fun he => hk (hlay he))]

theorem graphRowLift_actual_J {n L : ℕ} {J : Type*}
    (lay : Fin n → Fin (n+L)) (hlay : Function.Injective lay) (i : Fin n)
    (q : Fin (n+L)) (hq : q ≠ lay i) (f : Reg (n+L) → ℂ)
    (hf : ∀ z b, f (Function.update z (lay i) b)=f z)
    (A : Matrix (Reg n) J ℂ) (ζ : ℂ) (a : Bool) :
    (graphPhysicalProjector n L (lay i) a*graphPhysicalH n L (lay i)*
      graphPhysicalPhase n L (lay i) ζ*networkCzGate (lay i) q)*graphRowLift lay f A =
        graphRowLift (Function.update lay i q) (graphSelectEnvelope f (lay i) a)
          (pauliProductDensity (fun k => if k=i then pauliXChoice a*clusterJ ζ else 1)*A) := by
  ext r j
  obtain ⟨z,rfl⟩ := (bitVecEquiv (n+L)).surjective r
  simp only [Matrix.mul_assoc]
  rw [graphPhysicalProjector_mul_rows]
  by_cases ha : z (lay i)=a
  · rw [if_pos ha, graphPhysicalH, graphPhysicalWire_mul_rows]
    simp_rw [graphPhysicalPhase_mul_rows, graphPhysicalCz_mul_rows]
    simp only [graphRowLift, graphRowLiftB, Equiv.symm_apply_apply, graphSelectEnvelope,
      ha, if_true, graphWireB_mul_rows]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Function.update_self, Function.update_of_ne hq, hf]
    rw [graphLogicalCoords_move lay hlay i q z b]
    have he := graphLocalJ_entry ζ a b (z q)
    linear_combination he * (f z * A
      (Function.update (fun k => z (Function.update lay i q k)) i b) j)
  · simp [graphRowLift, graphRowLiftB, graphSelectEnvelope, ha]

def GraphEnvelopeInvariant {n L : ℕ} (lay : Fin n → Fin (n+L))
    (f : Reg (n+L) → ℂ) : Prop := ∀ i z b, f (Function.update z (lay i) b)=f z

theorem graphEnvelope_overlay {n L : ℕ} (lay : Fin n → Fin (n+L))
    (f : Reg (n+L) → ℂ) (hf : GraphEnvelopeInvariant lay f)
    (z : Reg (n+L)) (y : Reg n) : f (graphOverlay n L lay z y)=f z := by
  have h : ∀ (ts : List (Fin n)) (z : Reg (n+L)),
      f (ts.foldl (fun z i => Function.update z (lay i) (y i)) z)=f z := by
    intro ts
    induction ts with
    | nil => intro z; rfl
    | cons i ts ih => intro z; rw [List.foldl_cons, ih, hf]
  exact h _ z

theorem graphEnvelope_coordinates {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (f : Reg (n+L) → ℂ)
    (hf : GraphEnvelopeInvariant lay f) (x y : Reg n) (s : GraphSpectator lay → Bool) :
    f ((graphCoordinates lay hlay).symm (x,s))=
      f ((graphCoordinates lay hlay).symm (y,s)) := by
  have he : graphOverlay n L lay ((graphCoordinates lay hlay).symm (x,s)) y=
      (graphCoordinates lay hlay).symm (y,s) := by
    apply (graphCoordinates lay hlay).injective
    rw [graphCoordinates_overlay, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← he, graphEnvelope_overlay lay f hf]

noncomputable def graphEnvelopeMass {N : ℕ} (n : ℕ) (f : Reg N → ℂ) : ℂ :=
  (2^n : ℂ)⁻¹ * ∑ z : Reg N, f z*star (f z)

theorem graphEnvelopeMass_coordinates {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (f : Reg (n+L) → ℂ)
    (hf : GraphEnvelopeInvariant lay f) :
    graphEnvelopeMass n f = ∑ s : GraphSpectator lay → Bool,
      f ((graphCoordinates lay hlay).symm (ZeroStr n,s))*
        star (f ((graphCoordinates lay hlay).symm (ZeroStr n,s))) := by
  unfold graphEnvelopeMass
  rw [← (graphCoordinates lay hlay).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [graphEnvelope_coordinates lay hlay f hf _ (ZeroStr n)]
  simp only [Finset.sum_const, Finset.card_univ, card_reg, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ)≠0)), one_mul]

theorem graphEnvelopeMass_select {N : ℕ} (n : ℕ) (v : Fin N) (a : Bool)
    (f : Reg N → ℂ) (hf : ∀ z b, f (Function.update z v b)=f z) :
    graphEnvelopeMass n (graphSelectEnvelope f v a)=(1/2 : ℂ)*graphEnvelopeMass n f := by
  let e := Equiv.funSplitAt v Bool
  have hu : ∀ (b : Bool) (s : {q : Fin N // q≠v} → Bool),
      e.symm (b,s)=Function.update (e.symm (false,s)) v b := by
    intro b s
    funext q
    by_cases hq : q=v
    · subst q; simp [e]
    · simp [e, hq]
  have he : ∀ b s, f (e.symm (b,s))=f (e.symm (false,s)) := by
    intro b s
    rw [hu, hf]
  unfold graphEnvelopeMass
  rw [← e.symm.sum_comp, ← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, graphSelectEnvelope]
  have hv : ∀ b s, e.symm (b,s) v=b := by intro b s; simp [e]
  simp_rw [hv, he]
  cases a <;> simp [Finset.mul_sum] <;> ring

theorem graphEnvelopeInvariant_select_move {n L : ℕ} (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (i : Fin n) (q : Fin (n+L)) (hq : q≠lay i)
    (f : Reg (n+L) → ℂ) (hf : GraphEnvelopeInvariant lay f)
    (hqf : ∀ z b, f (Function.update z q b)=f z) (a : Bool) :
    GraphEnvelopeInvariant (Function.update lay i q) (graphSelectEnvelope f (lay i) a) := by
  intro k z b
  by_cases hk : k=i
  · subst k
    rw [Function.update_self]
    change (if Function.update z q b (lay i)=a then f (Function.update z q b) else 0)=_
    rw [Function.update_of_ne (Ne.symm hq), hqf]
    rfl
  · rw [Function.update_of_ne hk]
    change (if Function.update z (lay k) b (lay i)=a then
      f (Function.update z (lay k) b) else 0)=_
    rw [Function.update_of_ne (fun he => hk (hlay he.symm)), hf]
    rfl

theorem graphRowLift_reference_entry {n L D R : ℕ} (lay : Fin n → Fin (n+L))
    (f : Reg (n+L) → ℂ) (A : Matrix (Reg n) (Fin D) ℂ)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (z w : Reg (n+L)) (r s : Fin R) :
    (((graphRowLift lay f A) ⊗ₖ (1 : Operator R))*X*
      ((graphRowLift lay f A) ⊗ₖ (1 : Operator R))ᴴ)
        ((bitVecEquiv (n+L)) z,r) ((bitVecEquiv (n+L)) w,s) =
      (f z*star (f w)) *
        (((fun u j => A ((bitVecEquiv n).symm u) j) ⊗ₖ (1 : Operator R))*X*
          ((fun u j => A ((bitVecEquiv n).symm u) j) ⊗ₖ (1 : Operator R))ᴴ)
            ((bitVecEquiv n) (fun i => z (lay i)),r)
            ((bitVecEquiv n) (fun i => w (lay i)),s) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap, Matrix.of_apply,
    graphRowLift, graphRowLiftB, Equiv.symm_apply_apply, star_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem graphDiscardReference_rowLift (n L D R : ℕ) (lay : Fin n → Fin (n+L))
    (hlay : Function.Injective lay) (f : Reg (n+L) → ℂ)
    (hf : GraphEnvelopeInvariant lay f) (A : Matrix (Reg n) (Fin D) ℂ)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    graphDiscardReference n L R lay
      (((graphRowLift lay f A) ⊗ₖ (1 : Operator R))*X*
        ((graphRowLift lay f A) ⊗ₖ (1 : Operator R))ᴴ) =
      graphEnvelopeMass n f •
        (((fun u j => A ((bitVecEquiv n).symm u) j) ⊗ₖ (1 : Operator R))*X*
          ((fun u j => A ((bitVecEquiv n).symm u) j) ⊗ₖ (1 : Operator R))ᴴ) := by
  ext p q
  rw [graphDiscardReference_coordinates n L R lay hlay]
  simp_rw [graphRowLift_reference_entry]
  have hc : ∀ (x : Reg n) (s : GraphSpectator lay → Bool),
      (fun i => (graphCoordinates lay hlay).symm (x,s) (lay i))=x := by
    intro x s
    exact congrArg Prod.fst ((graphCoordinates lay hlay).apply_symm_apply (x,s))
  simp_rw [hc, Equiv.apply_symm_apply,
    graphEnvelope_coordinates lay hlay f hf _ (ZeroStr n)]
  rw [← Finset.sum_mul, ← graphEnvelopeMass_coordinates lay hlay f hf]
  rfl

theorem graphGateProduct_distinct_wires {N : ℕ} (qs : List (Fin N)) (hqs : qs.Nodup)
    (U : Operator 2) :
    graphGateProduct (qs.map (fun q => tensorPauliWireGate N q U))=
      tensorPauliProduct N (fun q => if q ∈ qs then U else 1) := by
  induction qs with
  | nil => simp [graphGateProduct, tensorPauliProduct_one]
  | cons q qs ih =>
    obtain ⟨hq,hs⟩ := List.nodup_cons.mp hqs
    change graphGateProduct (qs.map _)*tensorPauliWireGate N q U=_
    rw [ih hs, tensorPauliWireGate, tensorPauliProduct_mul]
    congr 1
    funext k
    by_cases hk : k=q
    · subst k; simp [hq]
    · simp [hk]

theorem graphFreshPreparation (n L : ℕ) :
    graphGateProduct (graphFreshGates n L)*graphInputFrame n L =
      graphRowLift (Fin.castAdd L) (fun _ => ((Real.sqrt 2 : ℂ)⁻¹)^L)
        (fun x j => if (bitVecEquiv n) x=j then (1 : ℂ) else 0) := by
  have hinj : Function.Injective (graphFresh n L) := by
    intro s t he
    apply Fin.ext
    have h := congrArg Fin.val he
    simpa [graphFresh] using! h
  have hr := graphGateProduct_distinct_wires (List.ofFn (graphFresh n L))
    (List.nodup_ofFn.mpr hinj) (relabelGate boolEquivFin2 Hadamard)
  rw [List.map_ofFn] at hr
  change graphGateProduct (graphFreshGates n L)=_ at hr
  ext r j
  obtain ⟨z,rfl⟩ := (bitVecEquiv (n+L)).surjective r
  rw [Matrix.mul_apply]
  simp_rw [graphInputFrame_entry]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hr]
  simp only [tensorPauliProduct, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    graphInputIndex, Equiv.symm_apply_apply]
  change (∏ q : Fin (n+L),
    (if q ∈ List.ofFn (graphFresh n L) then relabelGate boolEquivFin2 Hadamard else
      (1 : Operator 2)) (boolEquivFin2 (z q))
        (boolEquivFin2 ((Fin.append ((bitVecEquiv n).symm j) (fun _ => false)) q))) = _
  rw [Fin.prod_univ_add]
  have hd : ∀ i : Fin n, Fin.castAdd L i ∉ List.ofFn (graphFresh n L) := by
    intro i hi
    obtain ⟨t,ht⟩ := List.mem_ofFn.mp hi
    have h := congrArg Fin.val ht
    simp only [graphFresh, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hp : ∀ t : Fin L, Fin.natAdd n t ∈ List.ofFn (graphFresh n L) := by
    intro t
    exact List.mem_ofFn.mpr ⟨t,rfl⟩
  simp only [hd, if_false, hp, if_true, Fin.append_left, Fin.append_right]
  have hh : ∀ b : Bool, relabelGate boolEquivFin2 Hadamard (boolEquivFin2 b)
      (boolEquivFin2 false)=(Real.sqrt 2 : ℂ)⁻¹ := by
    intro b
    cases b <;> simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Hadamard,
      boolEquivFin2, one_div]
  simp_rw [hh]
  have hid : (∏ i : Fin n, (1 : Operator 2) (boolEquivFin2 (z (Fin.castAdd L i)))
      (boolEquivFin2 ((bitVecEquiv n).symm j i)))=
      if (bitVecEquiv n) (fun i => z (Fin.castAdd L i))=j then (1 : ℂ) else 0 := by
    have h := congrFun (congrFun (pauliProductDensity_one n)
      (fun i => z (Fin.castAdd L i))) ((bitVecEquiv n).symm j)
    simpa [pauliProductDensity, Matrix.one_apply,
      ← (bitVecEquiv n).injective.eq_iff] using! h
  rw [hid]
  simp [graphRowLift, graphRowLiftB, mul_comm]

theorem graphEnvelopeMass_initial (n L : ℕ) :
    graphEnvelopeMass n (fun _ : Reg (n+L) => ((Real.sqrt 2 : ℂ)⁻¹)^L)=1 := by
  have hc : (Real.sqrt 2 : ℂ)⁻¹*star ((Real.sqrt 2 : ℂ)⁻¹)=(1/2 : ℂ) := by
    simpa using! sqrt2_inv_sq
  simp only [graphEnvelopeMass, Finset.sum_const, Finset.card_univ, card_reg, nsmul_eq_mul]
  rw [star_pow, ← mul_pow, hc]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  have hp : (2 : ℂ)^L*(1/2 : ℂ)^L=1 := by rw [← mul_pow]; norm_num
  rw [mul_assoc ((2 : ℂ)^n) (2^L) ((1/2)^L),hp,mul_one,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ)≠0))]

theorem graphCzFrame_sign {n : ℕ} (F : PauliFrame n) (i j : Fin n) (hij : i≠j)
    (v : Reg n) :
    frameSign (graphCzFrame F i j) v =
      frameSign F v*frameBitSign (F.1 j) (v i)*frameBitSign (F.1 i) (v j) := by
  have he : ∀ k, frameBitSign ((graphCzFrame F i j).2 k) (v k)=
      frameBitSign (F.2 k) (v k)*(if k=i then frameBitSign (F.1 j) (v k) else 1)*
        (if k=j then frameBitSign (F.1 i) (v k) else 1) := by
    intro k
    by_cases hki : k=i
    · subst k
      simp [graphCzFrame, hij, frameBitSign_xor]
    · by_cases hkj : k=j
      · subst k
        simp [graphCzFrame, hki, frameBitSign_xor]
      · simp [graphCzFrame, hki, hkj]
  unfold frameSign
  simp_rw [he, Finset.prod_mul_distrib]
  simp

theorem graphCzFrameTransportB {n : ℕ} (F : PauliFrame n) (i j : Fin n) (hij : i≠j) :
    networkCzGateB i j*pauliFrameGateB F =
      frameBitSign (F.1 i) (F.1 j) •
        (pauliFrameGateB (graphCzFrame F i j)*networkCzGateB i j) := by
  ext w v
  simp only [networkCzGateB, Matrix.diagonal_mul, Matrix.mul_diagonal,
    pauliFrameGateB_entry, Matrix.smul_apply, smul_eq_mul]
  have hx : frameShift (graphCzFrame F i j) v=frameShift F v := rfl
  rw [hx]
  by_cases hw : w=frameShift F v
  · subst w
    rw [if_pos rfl, graphCzFrame_sign F i j hij v]
    cases hi : F.1 i <;> cases hj : F.1 j <;> cases hvi : v i <;> cases hvj : v j <;>
      simp [frameShift, frameBitSign, hi, hj, hvi, hvj] <;> ring
  · simp [hw]

theorem graphGateProduct_append {D : ℕ} (Us Vs : List (Operator D)) :
    graphGateProduct (Us++Vs)=graphGateProduct Vs*graphGateProduct Us := by
  induction Us with
  | nil => simp [graphGateProduct]
  | cons U Us ih =>
    change graphGateProduct (Us++Vs)*U=graphGateProduct Vs*(graphGateProduct Us*U)
    rw [ih, Matrix.mul_assoc]

@[simp] theorem graphGateProduct_nil {D : ℕ} : graphGateProduct ([] : List (Operator D))=1 := rfl

@[simp] theorem graphGateProduct_cons {D : ℕ} (U : Operator D) (Us : List (Operator D)) :
    graphGateProduct (U::Us)=graphGateProduct Us*U := rfl

theorem graphCorrection_rowLift {n L : ℕ} {J : Type*} (gs : GraphWord n L)
    (hlay : Function.Injective (graphLayoutFinal gs)) (F : PauliFrame n)
    (f : Reg (n+L) → ℂ) (hf : GraphEnvelopeInvariant (graphLayoutFinal gs) f)
    (A : Matrix (Reg n) J ℂ) :
    graphGateProduct (graphCorrectionGates gs F)*graphRowLift (graphLayoutFinal gs) f A =
      graphRowLift (graphLayoutFinal gs) f
        (relabelGate (bitVecEquiv n).symm ((pauliFrameGate n F)ᴴ)*A) := by
  have hx : pauliX=relabelGate boolEquivFin2 PauliX := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hz : pauliZ=relabelGate boolEquivFin2 PauliZ := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hw (i : Fin n) (U : Matrix Bool Bool ℂ) : wireGate n i U=
      pauliProductDensity (fun k => if k=i then relabelGate boolEquivFin2 U else 1) := by
    ext x y
    simp [wireGate, tensorPauliWireGate, tensorPauliProduct, relabelGate,
      Matrix.reindex_apply, Matrix.submatrix_apply]
  have hX (i : Fin n) (B : Matrix (Reg n) J ℂ) :
      tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliX*
        graphRowLift (graphLayoutFinal gs) f B =
          graphRowLift (graphLayoutFinal gs) f (wireGate n i PauliX*B) := by
    rw [hx]
    simpa only [hw] using! graphRowLift_active_wire _ hlay i f (hf i)
      (relabelGate boolEquivFin2 PauliX) B
  have hZ (i : Fin n) (B : Matrix (Reg n) J ℂ) :
      tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliZ*
        graphRowLift (graphLayoutFinal gs) f B =
          graphRowLift (graphLayoutFinal gs) f (wireGate n i PauliZ*B) := by
    rw [hz]
    simpa only [hw] using! graphRowLift_active_wire _ hlay i f (hf i)
      (relabelGate boolEquivFin2 PauliZ) B
  have hs : ∀ (is : List (Fin n)) (B : Matrix (Reg n) J ℂ),
      graphGateProduct (is.flatMap (fun i =>
        (if F.1 i then [tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliX] else []) ++
        (if F.2 i then [tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliZ] else [])))*
          graphRowLift (graphLayoutFinal gs) f B =
        graphRowLift (graphLayoutFinal gs) f
          (reflectionProgramMatrix (is.flatMap (fun i =>
            (if F.1 i then [Sum.inl (i,PauliX)] else []) ++
            (if F.2 i then [Sum.inl (i,PauliZ)] else [])))*B) := by
    intro is
    induction is with
    | nil => intro B; simp [graphGateProduct, reflectionProgramMatrix]
    | cons i is ih =>
      intro B
      rw [List.flatMap_cons, graphGateProduct_append, Matrix.mul_assoc]
      cases hxi : F.1 i <;> cases hzi : F.2 i <;>
        simp only [hxi,hzi,Bool.false_eq_true,if_false,if_true,List.nil_append,
          List.append_nil, List.singleton_append,graphGateProduct_nil,graphGateProduct_cons,Matrix.one_mul,
          Matrix.mul_one,Matrix.mul_assoc] <;>
        simp only [hX,hZ,ih,List.flatMap_cons,reflectionProgramMatrix_append,hxi,hzi,
          Bool.false_eq_true,if_false,if_true,List.nil_append,List.append_nil,
          reflectionProgramMatrix,reflectionGateMatrix,Matrix.one_mul,Matrix.mul_one,
          Matrix.mul_assoc]
  have hh := hs (List.ofFn (fun i : Fin n => i)) A
  have he : (List.ofFn (fun i : Fin n => i)).flatMap (fun i =>
      (if F.1 i then [Sum.inl (i,PauliX)] else []) ++
      (if F.2 i then [Sum.inl (i,PauliZ)] else []))=frameCorrectionSteps F := by
    simp only [frameCorrectionSteps,List.flatMap,List.map_ofFn,Function.comp_def]
  rw [he] at hh
  rw [frameCorrectionSteps_matrix] at hh
  simpa only [graphCorrectionGates, frameCorrectionSteps, List.flatMap, List.map_ofFn,
    Function.comp_def] using! hh

def graphLayoutList {n L : ℕ} (gs : GraphWord n L) (ps : List (Fin L)) :
    Fin n → Fin (n+L) := ps.foldl (graphAdvance gs) (Fin.castAdd L)

theorem graphLayoutBefore_prefix {n L : ℕ} (gs : GraphWord n L)
    (ps ts : List (Fin L)) (t : Fin L)
    (hall : List.ofFn (fun s : Fin L => s)=ps++t::ts) :
    graphLayoutBefore gs t=graphLayoutList gs ps := by
  have hi : ps.length<(List.ofFn (fun s : Fin L => s)).length := by rw [hall]; simp
  have ht : (List.ofFn (fun s : Fin L => s))[ps.length]?=some t := by
    rw [hall, List.getElem?_append_right le_rfl]
    simp
  have he : (List.ofFn (fun s : Fin L => s))[ps.length]?=
      some (⟨ps.length,by simpa using! hi⟩ : Fin L) :=
    List.getElem?_eq_some_iff.mpr ⟨hi,List.getElem_ofFn hi⟩
  have hv : ps.length=t.val := congrArg Fin.val (Option.some.inj (he.symm.trans ht))
  unfold graphLayoutBefore graphLayoutList
  rw [← hv, hall, List.take_left]

noncomputable def graphLogicalTailB {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    List (Fin L) → PauliFrame n → Matrix (Reg n) (Reg n) ℂ
  | [], F => relabelGate (bitVecEquiv n).symm ((pauliFrameGate n F)ᴴ)
  | t::ts, F =>
    match gs t with
    | .inl (i,ζ) => graphLogicalTailB gs h ts (graphWireFrame F i (h.1 t))*
        pauliProductDensity (fun k => if k=i then
          pauliXChoice (h.1 t)*clusterJ (if F.1 i then star ζ else ζ) else 1)
    | .inr (i,j) => graphLogicalTailB gs h ts (graphCzFrame F i j)*networkCzGateB i j

def graphTailEnvelope {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    List (Fin L) → (Reg (n+L) → ℂ) → (Reg (n+L) → ℂ)
  | [], f => f
  | t::ts, f => match gs t with
    | .inl (i,_) => graphTailEnvelope gs h ts
        (graphSelectEnvelope f (graphLayoutBefore gs t i) (h.1 t))
    | .inr _ => graphTailEnvelope gs h ts f

theorem graphTail_actual_transfer {n L : ℕ} {J : Type*} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs)
    (ts ps : List (Fin L)) (hall : List.ofFn (fun s : Fin L => s)=ps++ts)
    (F : PauliFrame n) (f : Reg (n+L) → ℂ)
    (hf : GraphEnvelopeInvariant (graphLayoutList gs ps) f)
    (hfresh : ∀ t ∈ ts, ∀ z b, f (Function.update z (graphFresh n L t) b)=f z)
    (A : Matrix (Reg n) J ℂ) :
    (graphTailLeaf false gs h ts F).operator*graphRowLift (graphLayoutList gs ps) f A =
      graphRowLift (graphLayoutFinal gs) (graphTailEnvelope gs h ts f)
        (graphLogicalTailB gs h ts F*A) ∧
    GraphEnvelopeInvariant (graphLayoutFinal gs) (graphTailEnvelope gs h ts f) ∧
    graphEnvelopeMass n (graphTailEnvelope gs h ts f)=
      (1/2 : ℂ)^(graphSlotCount gs ts)*graphEnvelopeMass n f := by
  induction ts generalizing ps F f A with
  | nil =>
    have hlay : graphLayoutList gs ps=graphLayoutFinal gs := by
      simp only [List.append_nil] at hall
      rw [← hall]
      rfl
    rw [hlay] at hf ⊢
    refine ⟨?_,hf,?_⟩
    · simp only [graphTailLeaf, graphPrependLeaf_operator, Matrix.one_mul,
        graphLogicalTailB, graphTailEnvelope]
      exact graphCorrection_rowLift gs (graph_layout_geometry gs hlegal).1 F f hf A
    · simp [graphTailEnvelope,graphSlotCount]
  | cons t ts ih =>
    have hb := graphLayoutBefore_prefix gs ps ts t hall
    have ho : (t::ts).Pairwise (· < ·) := by
      have ho := List.pairwise_ofFn.mpr (fun (i j : Fin L) hij => hij)
      rw [hall] at ho
      exact (List.pairwise_append.mp ho).2.1
    have hfuture := (List.pairwise_cons.mp ho).1
    have hall' : List.ofFn (fun s : Fin L => s)=(ps++[t])++ts := by
      simpa only [List.append_assoc,List.singleton_append] using! hall
    have hnext : graphLayoutList gs (ps++[t])=graphAdvance gs (graphLayoutList gs ps) t := by
      simp [graphLayoutList,List.foldl_append]
    rw [← hb] at hf ⊢
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      have hi := (graph_layout_geometry gs hlegal).2.2.1 t
      have hq : graphFresh n L t≠graphLayoutBefore gs t i := by
        intro he
        have hv := congrArg Fin.val he
        have hi := hi.2.1 i
        simp only [graphFresh,Fin.val_natAdd] at hv
        omega
      have hf' := graphEnvelopeInvariant_select_move (graphLayoutBefore gs t) hi.1 i
        (graphFresh n L t) hq f hf (hfresh t (by simp)) (h.1 t)
      have hnext' : graphLayoutList gs (ps++[t])=
          Function.update (graphLayoutBefore gs t) i (graphFresh n L t) := by
        rw [hnext,← hb,graphAdvance,hg]
      rw [← hnext'] at hf'
      have hfresh' : ∀ s ∈ ts, ∀ z b,
          graphSelectEnvelope f (graphLayoutBefore gs t i) (h.1 t)
              (Function.update z (graphFresh n L s) b)=
            graphSelectEnvelope f (graphLayoutBefore gs t i) (h.1 t) z := by
        intro s hs z b
        have hsold : graphLayoutBefore gs t i≠graphFresh n L s := by
          intro he
          have hv := congrArg Fin.val he
          have ht := hi.2.1 i
          have hts : t.val<s.val := hfuture s hs
          simp only [graphFresh,Fin.val_natAdd] at hv
          omega
        simp only [graphSelectEnvelope,Function.update_of_ne hsold,
          hfresh s (List.mem_cons_of_mem t hs)]
      obtain ⟨htrans,hinv,hmass⟩ := ih (ps++[t]) hall' (graphWireFrame F i (h.1 t))
        _ hf' hfresh' (pauliProductDensity (fun k => if k=i then
          pauliXChoice (h.1 t)*clusterJ (if F.1 i then star ζ else ζ) else 1)*A)
      refine ⟨?_,?_,?_⟩
      · have hJ := graphRowLift_actual_J (graphLayoutBefore gs t) hi.1 i
          (graphFresh n L t) hq f (hf i) A (if F.1 i then star ζ else ζ) (h.1 t)
        simp only [Matrix.mul_assoc] at hJ
        simp only [graphTailLeaf,hg,graphFrameAdvance,Bool.false_eq_true,if_false,
          ObservedKrausLeaf.prepend,Matrix.mul_assoc,graphEdgeEndpoints]
        rw [hJ,← hnext',htrans]
        simp only [graphTailEnvelope,graphLogicalTailB,hg,Matrix.mul_assoc]
      · simpa only [graphTailEnvelope,hg] using! hinv
      · simp only [graphTailEnvelope,hg,hmass]
        rw [graphEnvelopeMass_select n _ _ f (hf i)]
        have hc : graphSlotCount gs (t::ts)=graphSlotCount gs ts+1 := by
          simp [graphSlotCount,graphWireAt,hg,Nat.add_comm]
        rw [hc,pow_succ]
        ring
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hnext' : graphLayoutList gs (ps++[t])=graphLayoutBefore gs t := by
        rw [hnext,← hb,graphAdvance,hg]
      rw [← hnext'] at hf
      obtain ⟨htrans,hinv,hmass⟩ := ih (ps++[t]) hall' (graphCzFrame F i j)
        f hf (fun s hs => hfresh s (List.mem_cons_of_mem t hs)) (networkCzGateB i j*A)
      refine ⟨?_,?_,?_⟩
      · simp only [graphTailLeaf,hg,graphFrameAdvance,Bool.false_eq_true,if_false,
          ObservedKrausLeaf.prepend,Matrix.mul_assoc,graphEdgeEndpoints]
        rw [graphRowLift_active_cz,← hnext',htrans]
        simp only [graphTailEnvelope,graphLogicalTailB,hg,Matrix.mul_assoc]
      · simpa only [graphTailEnvelope,hg] using! hinv
      · simpa [graphTailEnvelope,hg,graphSlotCount,graphWireAt] using! hmass

theorem graphPauliFrameB_eq (n : ℕ) (F : PauliFrame n) :
    pauliFrameGateB F=relabelGate (bitVecEquiv n).symm (pauliFrameGate n F) := by
  unfold pauliFrameGateB pauliFrameGate
  rw [relabelGate_relabelGate]

theorem graphRelabel_smul {I J : Type*} (e : I ≃ J) (c : ℂ) (U : Matrix I I ℂ) :
    relabelGate e (c • U)=c • relabelGate e U := rfl

theorem graphWireFrameTransportB (n : ℕ) (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖=1)
    (F : PauliFrame n) (a : Bool) :
    pauliProductDensity (fun k => if k=i then
      pauliXChoice a*clusterJ (if F.1 i then star ζ else ζ) else 1)*pauliFrameGateB F =
      wireFramePhase ζ (F.1 i) (F.2 i) •
        (pauliFrameGateB (graphWireFrame F i a)*networkWireGateB i ζ) := by
  have he := congrArg (relabelGate (bitVecEquiv n).symm)
    (wireFrameTransport_network n i ζ hζ F a)
  simpa only [teleportRelabelGate_mul, graphRelabel_smul, ← graphPauliFrameB_eq,
    ← rawNetworkWireGateB_eq, ← networkWireGateB_eq, rawNetworkWireGateB,
    frameUpdate, graphWireFrame] using! he

theorem graphPauliFrameB_unitary (n : ℕ) (F : PauliFrame n) :
    pauliFrameGateB F ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [graphPauliFrameB_eq]
  exact teleportRelabelGate_mem_unitaryGroup (pauliFrameGate_unitary n F) _

theorem graphLogicalTailB_correct (n L : ℕ) (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    ∃ c : ℂ, ‖c‖=1 ∧ graphLogicalTailB gs h ts F*pauliFrameGateB F =
      c • relabelGate (bitVecEquiv n).symm (networkLogicalMatrix (ts.map gs)) := by
  induction ts generalizing F with
  | nil =>
    refine ⟨1,by norm_num,?_⟩
    simp only [graphLogicalTailB, List.map_nil, networkLogicalMatrix, one_smul,
      graphPauliFrameB_eq, ← teleportRelabelGate_mul]
    have hp : (pauliFrameGate n F)ᴴ*pauliFrameGate n F=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
        (Matrix.mem_unitaryGroup_iff').mp (pauliFrameGate_unitary n F)
    rw [hp]
  | cons t ts ih =>
    have hl := hlegal (gs t) (List.mem_ofFn.mpr ⟨t,rfl⟩)
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      change (match gs t with | .inl (_,ζ) => ‖ζ‖=1 | .inr (i,j) => i≠j) at hl
      rw [hg] at hl
      obtain ⟨c,hc,he⟩ := ih (graphWireFrame F i (h.1 t))
      refine ⟨c*wireFramePhase ζ (F.1 i) (F.2 i),?_,?_⟩
      · rw [norm_mul,hc,wireFramePhase_norm ζ hl]
        norm_num
      · simp only [graphLogicalTailB,hg,Matrix.mul_assoc]
        rw [graphWireFrameTransportB n i ζ hl F (h.1 t), Matrix.mul_smul,
          ← Matrix.mul_assoc,he,Matrix.smul_mul,smul_smul]
        simp only [List.map_cons,networkLogicalMatrix,hg,networkGateMatrix]
        rw [teleportRelabelGate_mul, ← networkWireGateB_eq, mul_comm c]
    | inr p =>
      obtain ⟨i,j⟩ := p
      simp only [hg] at hl
      obtain ⟨c,hc,he⟩ := ih (graphCzFrame F i j)
      refine ⟨c*frameBitSign (F.1 i) (F.1 j),?_,?_⟩
      · cases F.1 i <;> cases F.1 j <;> simp [frameBitSign,norm_mul,hc]
      · simp only [graphLogicalTailB,hg,Matrix.mul_assoc]
        rw [graphCzFrameTransportB F i j hl,Matrix.mul_smul,← Matrix.mul_assoc,he,
          Matrix.smul_mul,smul_smul]
        simp only [List.map_cons,networkLogicalMatrix,hg,networkGateMatrix]
        rw [teleportRelabelGate_mul]
        have hb : networkCzGateB i j=relabelGate (bitVecEquiv n).symm (networkCzGate i j) := by
          rw [networkCzGate,relabelGate_relabelGate]
        rw [← hb,mul_comm c]

noncomputable def graphInitialLogicalRows (n : ℕ) : Matrix (Reg n) (Fin (2^n)) ℂ :=
  fun y k => if (bitVecEquiv n) y=k then 1 else 0

theorem graphLogicalRows_init_mul (n : ℕ) (B : Matrix (Reg n) (Reg n) ℂ)
    (x : Reg n) (j : Fin (2^n)) :
    (B*graphInitialLogicalRows n) x j=
      B x ((bitVecEquiv n).symm j) := by
  rw [Matrix.mul_apply, ← (bitVecEquiv n).symm.sum_comp]
  simp [graphInitialLogicalRows]

theorem graphConj_phase {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ) (hc : ‖c‖=1)
    (U X : Matrix I I ℂ) : (c • U)*X*(c • U)ᴴ=U*X*Uᴴ := by
  have hh : star c*c=1 := by
    have he := Complex.normSq_eq_conj_mul_self (z := c)
    rw [Complex.normSq_eq_norm_sq,hc,one_pow] at he
    exact he.symm
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hh, one_smul]

theorem preentangled_graph_actual_reference_branch :
    ∀ (n L R : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
    ∀ (h : GraphHistory gs) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
      graphActualReference true gs h R X=(1/2:ℂ)^(graphWireCount gs) •
        (TensorGate (networkLogicalMatrix (List.ofFn gs)) (1:Operator R)*X*
          (TensorGate (networkLogicalMatrix (List.ofFn gs)) (1:Operator R))ᴴ) := by
  intro n L R gs hlegal h X
  let ts := List.ofFn (fun t : Fin L => t)
  let f₀ : Reg (n+L) → ℂ := fun _ => ((Real.sqrt 2 : ℂ)⁻¹)^L
  let A₀ : Matrix (Reg n) (Fin (2^n)) ℂ := graphInitialLogicalRows n
  let f := graphTailEnvelope gs h ts f₀
  let A := graphLogicalTailB gs h ts (zeroPauliFrame n)*A₀
  have ht := graphTail_actual_transfer gs hlegal h ts [] (by simp [ts])
    (zeroPauliFrame n) f₀ (by intro i z b; rfl) (by intro t ht z b; rfl) A₀
  have hphys : (graphProgramLeaf true gs h).operator*graphInputFrame n L=
      graphRowLift (graphLayoutFinal gs) f A := by
    have hleaf := ((preentangled_graph_actual_leaf_retiming n L gs hlegal).2.2 h).1
    rw [← hleaf, graphProgramLeaf_eq]
    simp only [Bool.false_eq_true,if_false,graphPrependLeaf_operator,Matrix.mul_assoc]
    rw [graphFreshPreparation]
    exact ht.1
  have hmass : graphEnvelopeMass n f=(1/2 : ℂ)^(graphWireCount gs) := by
    have he := ht.2.2
    have hcount : graphSlotCount gs ts=graphWireCount gs := by
      simp [ts,graphSlotCount,List.map_ofFn,List.sum_ofFn,graphWireCount_eq_sum]
    rw [hcount,graphEnvelopeMass_initial,mul_one] at he
    exact he
  obtain ⟨c,hc,he⟩ := graphLogicalTailB_correct n L gs hlegal h ts (zeroPauliFrame n)
  have hzero : pauliFrameGateB (zeroPauliFrame n)=1 := by
    rw [graphPauliFrameB_eq,zeroPauliFrame_gate,teleportRelabelGate_one]
  rw [hzero,Matrix.mul_one] at he
  have hA : (fun u j => A ((bitVecEquiv n).symm u) j)=
      c • networkLogicalMatrix (List.ofFn gs) := by
    ext u j
    change (graphLogicalTailB gs h ts (zeroPauliFrame n)*A₀) ((bitVecEquiv n).symm u) j=_
    rw [graphLogicalRows_init_mul]
    have hj := congrFun (congrFun he ((bitVecEquiv n).symm u)) ((bitVecEquiv n).symm j)
    simpa [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,ts,List.map_ofFn] using! hj
  have hgroup :
      TensorGate (graphProgramLeaf true gs h).operator (1 : Operator R)*
        (((graphInputFrame n L) ⊗ₖ (1 : Operator R))*X*
          ((graphInputFrame n L) ⊗ₖ (1 : Operator R))ᴴ)*
        (TensorGate (graphProgramLeaf true gs h).operator (1 : Operator R))ᴴ=
      ((graphRowLift (graphLayoutFinal gs) f A) ⊗ₖ (1 : Operator R))*X*
        ((graphRowLift (graphLayoutFinal gs) f A) ⊗ₖ (1 : Operator R))ᴴ := by
    have hk : TensorGate (graphProgramLeaf true gs h).operator (1 : Operator R)*
        ((graphInputFrame n L) ⊗ₖ (1 : Operator R))=
          ((graphRowLift (graphLayoutFinal gs) f A) ⊗ₖ (1 : Operator R)) := by
      rw [TensorGate, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hphys]
    rw [← hk]
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  unfold graphActualReference
  (try dsimp only)
  rw [hgroup,graphDiscardReference_rowLift n L (2^n) R (graphLayoutFinal gs)
    (graph_layout_geometry gs hlegal).1 f ht.2.1 A X,hmass,hA]
  have hk : (c • networkLogicalMatrix (List.ofFn gs)) ⊗ₖ (1 : Operator R)=
      c • TensorGate (networkLogicalMatrix (List.ofFn gs)) (1 : Operator R) := by
    ext p q
    simp only [Matrix.kroneckerMap,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,TensorGate]
    ring
  rw [hk,graphConj_phase c hc]

theorem graphActualBranch_formula (n L : ℕ) (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs) (ρ : Operator (2^n)) :
    graphActualBranch true gs h ρ=(1/2 : ℂ)^(graphWireCount gs) •
      (networkLogicalMatrix (List.ofFn gs)*ρ*(networkLogicalMatrix (List.ofFn gs))ᴴ) := by
  ext i j
  simp only [graphActualBranch,preentangled_graph_actual_reference_branch n L 1 gs hlegal,
    tensorGate_conjTranspose,Matrix.conjTranspose_one,tensorGate_mul,Matrix.one_mul,
    Matrix.smul_apply]
  simp only [TensorGate,Matrix.kronecker_apply,Matrix.one_apply_eq,mul_one]

theorem graphAmplitude_square (w : ℕ) :
    star (((Real.sqrt 2 : ℂ)⁻¹)^w)*((Real.sqrt 2 : ℂ)⁻¹)^w=(1/2 : ℂ)^w := by
  rw [star_pow,← mul_pow]
  congr 1
  simpa using! sqrt2_inv_sq

theorem graphProbability_sum_scalar (w : ℕ) : (2 : ℂ)^w*(1/2 : ℂ)^w=1 := by
  rw [← mul_pow]
  norm_num

theorem graphAmplitude_square_rev (w : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹)^w*star (((Real.sqrt 2 : ℂ)⁻¹)^w)=(1/2 : ℂ)^w := by
  rw [mul_comm]
  exact graphAmplitude_square w

theorem preentangled_graph_actual_cp_instrument_and_forget :
    ∀ (n L : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
    ∃ I : Instrument (GraphHistory gs) (2^n) (2^n),
      (∀ (h : GraphHistory gs) (ρ : Operator (2^n)), I.branch h ρ=graphActualBranch true gs h ρ) ∧
      (∀ (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) (h : GraphHistory gs),
        instrumentProb I ρ h=(1/2:ℝ)^(graphWireCount gs)) ∧
      (∀ (R : ℕ) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
        (∑ h : GraphHistory gs, graphActualReference true gs h R X)=
          TensorGate (networkLogicalMatrix (List.ofFn gs)) (1:Operator R)*X*
            (TensorGate (networkLogicalMatrix (List.ofFn gs)) (1:Operator R))ᴴ) := by
  intro n L gs hlegal
  let U := networkLogicalMatrix (List.ofFn gs)
  let w := graphWireCount gs
  let K : GraphHistory gs → Operator (2^n) := fun _ => ((Real.sqrt 2 : ℂ)⁻¹)^w • U
  have hu := networkLogicalMatrix_unitary (List.ofFn gs) hlegal
  have hunit : Uᴴ*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hu
  have hK : ∑ h : GraphHistory gs, (K h)ᴴ*K h=1 := by
    simp only [K,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      graphAmplitude_square_rev,hunit,Finset.sum_const,Finset.card_univ,graphHistory_card]
    ext i j
    simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
    rw [nsmul_eq_mul]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [← mul_assoc,graphProbability_sum_scalar,one_mul]
  let I := Instrument.ofKraus K hK
  have hb (h : GraphHistory gs) (ρ : Operator (2^n)) :
      I.branch h ρ=(1/2 : ℂ)^w • (U*ρ*Uᴴ) := by
    simp only [I,Instrument.ofKraus_branch,K,Matrix.conjTranspose_smul,Matrix.smul_mul,
      Matrix.mul_smul,smul_smul,graphAmplitude_square]
  refine ⟨I,?_,?_,?_⟩
  · intro h ρ
    rw [hb,graphActualBranch_formula n L gs hlegal h ρ]
  · intro ρ hρ h
    unfold instrumentProb
    rw [hb,Matrix.trace_smul]
    change (((1/2 : ℂ)^w)*Matrix.trace (conjBranch U ρ)).re=(1/2 : ℝ)^w
    rw [trace_conjBranch_unitary U hu,hρ.2,mul_one]
    have hh : (1/2 : ℂ)=((1/2 : ℝ) : ℂ) := by norm_num
    rw [hh,← Complex.ofReal_pow,Complex.ofReal_re]
  · intro R X
    simp_rw [preentangled_graph_actual_reference_branch n L R gs hlegal]
    rw [Finset.sum_const,Finset.card_univ,graphHistory_card]
    ext p q
    simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
    rw [nsmul_eq_mul]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [← mul_assoc,graphProbability_sum_scalar,one_mul]

theorem graphActualBranch_forget (n L : ℕ) (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (ρ : Operator (2^n)) :
    (∑ h : GraphHistory gs,graphActualBranch true gs h ρ)=
      networkLogicalMatrix (List.ofFn gs)*ρ*(networkLogicalMatrix (List.ofFn gs))ᴴ := by
  obtain ⟨I,_,_,hforget⟩ := preentangled_graph_actual_cp_instrument_and_forget n L gs hlegal
  have he := hforget 1 (TensorGate ρ (1 : Operator 1))
  ext i j
  have hx := congrFun (congrFun he (i,0)) (j,0)
  simp only [tensorGate_conjTranspose,Matrix.conjTranspose_one,tensorGate_mul,
    Matrix.one_mul] at hx
  simpa only [Matrix.sum_apply,graphActualBranch,TensorGate,Matrix.kronecker_apply,
    Matrix.one_apply_eq,mul_one] using! hx

end Qatlib.Concepts.ClusterPatterns.Preentangled
