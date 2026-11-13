/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PauliNetwork.DeferredPauliNetwork
import Qatlib.Concepts.ClusterPatterns.PauliNetwork.DeferredPauliNetworkConsumers

/-!
# Physical layouts for preentangled graph patterns

`GraphWord` and `GraphHistory` describe finite logical networks and their measurement outcomes.
The module assigns physical vertices, graph edges, adaptive gates, and Pauli corrections, and
defines both sequential and preentangled observed programs with their branch maps.

The layout geometry, history cardinality, and disjoint commutation results provide the
infrastructure for moving entangling gates before measurements in the resource construction of
[RaussendorfBriegel2000].

## Main statements

* `preentangled_graph_actual_layout_and_history`: input isometry, layout geometry, and history
  count.
* `graphProgram_leafCount`: the compiled program has one leaf for each measurement history.
* `preentangled_graph_physical_disjoint_commutation`: commutation relations used to retime graph
  edges.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker
namespace Qatlib.Concepts.ClusterPatterns.Preentangled
/-- A length-`L` word of cluster-network gates on `n` logical wires. -/
abbrev GraphWord (n L : ℕ) := Fin L → ClusterNetworkGate n

/-- The Boolean indicator that a graph-word position is a one-wire gate rather than a CZ gate. -/
def graphWireAt {n L : ℕ} (gs : GraphWord n L) (t : Fin L) : Bool :=
  match gs t with | .inl _ => true | .inr _ => false
/-- A Boolean outcome assignment to graph-word positions, constrained to be false at positions
without a wire measurement. -/
abbrev GraphHistory {n L : ℕ} (gs : GraphWord n L) :=
  {h : Fin L → Bool // ∀ t, graphWireAt gs t = false → h t = false}
/-- The number of one-wire measurement steps in a graph word. -/
def graphWireCount {n L : ℕ} (gs : GraphWord n L) : ℕ := (networkCounts (List.ofFn gs)).1

/-- The fresh physical vertex allocated to a graph-word position after the initial `n` vertices. -/
def graphFresh (n L : ℕ) (t : Fin L) : Fin (n+L) := Fin.natAdd n t

/-- The layout update that moves a measured logical wire to its fresh vertex and leaves the
layout unchanged at a CZ step. -/
def graphAdvance {n L : ℕ} (gs : GraphWord n L)
    (active : Fin n → Fin (n+L)) (t : Fin L) : Fin n → Fin (n+L) :=
  match gs t with
  | .inl (i,_) => Function.update active i (graphFresh n L t)
  | .inr _ => active

/-- The active logical-to-physical layout obtained by processing all positions before `t`. -/
def graphLayoutBefore {n L : ℕ} (gs : GraphWord n L) (t : Fin L) : Fin n → Fin (n+L) :=
  ((List.ofFn (fun s : Fin L => s)).take t.val).foldl (graphAdvance gs) (Fin.castAdd L)
/-- The logical-to-physical layout after processing the full graph word. -/
def graphLayoutFinal {n L : ℕ} (gs : GraphWord n L) : Fin n → Fin (n+L) :=
  (List.ofFn (fun s : Fin L => s)).foldl (graphAdvance gs) (Fin.castAdd L)

/-- The physical endpoints of the edge for a graph step, joining an active wire to its fresh
vertex or joining two active logical wires. -/
def graphEdgeEndpoints {n L : ℕ} (gs : GraphWord n L) (t : Fin L) : Fin (n+L) × Fin (n+L) :=
  match gs t with
  | .inl (i,_) => (graphLayoutBefore gs t i,graphFresh n L t)
  | .inr (i,j) => (graphLayoutBefore gs t i,graphLayoutBefore gs t j)

/-- The Hadamard gate acting on one physical graph vertex and as the identity on all others. -/
noncomputable def graphPhysicalH (n L : ℕ) (v : Fin (n+L)) : Operator (2^(n+L)) :=
  tensorPauliWireGate (n+L) v (relabelGate boolEquivFin2 Hadamard)
/-- The cluster phase gate with parameter `ζ` acting on one physical graph vertex. -/
noncomputable def graphPhysicalPhase (n L : ℕ) (v : Fin (n+L)) (ζ : ℂ) : Operator (2^(n+L)) :=
  tensorPauliWireGate (n+L) v (clusterPhase ζ)
/-- The computational-basis bit at a physical graph vertex, encoded as an element of `Fin 2`. -/
def graphPhysicalLabel (n L : ℕ) (v : Fin (n+L)) (r : Fin (2^(n+L))) : Fin 2 :=
  boolEquivFin2 ((bitVecEquiv (n+L)).symm r v)
/-- The projector onto the computational-basis outcome `a` at a physical graph vertex. -/
noncomputable def graphPhysicalProjector (n L : ℕ) (v : Fin (n+L)) (a : Bool) : Operator (2^(n+L)) :=
  Projector (Finset.univ.filter (fun r => graphPhysicalLabel n L v r=boolEquivFin2 a))
/-- The list of physical CZ gates associated with all graph-word edges in position order. -/
noncomputable def graphEdgeGates {n L : ℕ} (gs : GraphWord n L) : List (Operator (2^(n+L))) :=
  List.ofFn (fun t : Fin L => networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2)
/-- The list of Hadamard gates preparing the `L` fresh graph vertices from zero to plus. -/
noncomputable def graphFreshGates (n L : ℕ) : List (Operator (2^(n+L))) :=
  List.ofFn (fun t : Fin L => graphPhysicalH n L (graphFresh n L t))
/-- The observed circuit formed by executing a list of gates before a continuation circuit. -/
noncomputable def graphPrepend {D : ℕ} (Us : List (Operator D)) (P : ObservedCircuit (Fin D)) :
    ObservedCircuit (Fin D) := Us.foldr (fun U P => .step (.gate U) P) P

/-- The Pauli-frame update for measuring logical wire `i` with outcome `a`. -/
def graphWireFrame {n : ℕ} (F : PauliFrame n) (i : Fin n) (a : Bool) : PauliFrame n :=
  (Function.update F.1 i (a ^^ F.2 i),Function.update F.2 i (F.1 i))
/-- The Pauli-frame update across a CZ gate, adding each endpoint's X-frame bit to the other's
Z-frame bit. -/
def graphCzFrame {n : ℕ} (F : PauliFrame n) (i j : Fin n) : PauliFrame n :=
  (F.1,Function.update (Function.update F.2 i (F.2 i ^^ F.1 j)) j (F.2 j ^^ F.1 i))
/-- The Pauli-frame update at a graph-word position using its gate and the selected history. -/
def graphFrameAdvance {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (F : PauliFrame n) (t : Fin L) : PauliFrame n :=
  match gs t with | .inl (i,_) => graphWireFrame F i (h.1 t) | .inr (i,j) => graphCzFrame F i j
/-- The Pauli frame obtained from the zero frame by processing the full graph word and history. -/
def graphFinalFrame {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) : PauliFrame n :=
  (List.ofFn (fun t : Fin L => t)).foldl (graphFrameAdvance gs h) (zeroPauliFrame n)

/-- The physical X and Z gates correcting a Pauli frame on the final logical layout. -/
noncomputable def graphCorrectionGates {n L : ℕ} (gs : GraphWord n L) (F : PauliFrame n) :
    List (Operator (2^(n+L))) :=
  (List.ofFn (fun i : Fin n =>
    (if F.1 i then [tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliX] else []) ++
    (if F.2 i then [tensorPauliWireGate (n+L) (graphLayoutFinal gs i) pauliZ] else []))).flatten

/-- The adaptive observed circuit for a graph-word tail with an incoming Pauli frame, using
either preentangled edges or sequential CZ gates. -/
noncomputable def graphTail {n L : ℕ} (preentangled : Bool) (gs : GraphWord n L) :
    List (Fin L) → PauliFrame n → ObservedCircuit (Fin (2^(n+L)))
  | [],F => graphPrepend (graphCorrectionGates gs F) (.halt true)
  | t::ts,F =>
    match gs t with
    | .inl (i,ζ) =>
      let v := graphLayoutBefore gs t i
      let measurement :=
        .step (.gate (graphPhysicalPhase n L v (if F.1 i then star ζ else ζ)))
          (.step (.gate (graphPhysicalH n L v))
            (.measure 2 (graphPhysicalLabel n L v) (fun a =>
              graphTail preentangled gs ts (graphWireFrame F i (boolEquivFin2.symm a)))))
      if preentangled then measurement else
        .step (.gate (networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2)) measurement
    | .inr (i,j) =>
      let rest := graphTail preentangled gs ts (graphCzFrame F i j)
      if preentangled then rest else
        .step (.gate (networkCzGate (graphEdgeEndpoints gs t).1 (graphEdgeEndpoints gs t).2)) rest

/-- The full observed graph circuit, including fresh-state preparation, the chosen entanglement
schedule, adaptive measurements, and final corrections. -/
noncomputable def graphProgram {n L : ℕ} (preentangled : Bool) (gs : GraphWord n L) :
    ObservedCircuit (Fin (2^(n+L))) :=
  graphPrepend (graphFreshGates n L)
    (if preentangled then graphPrepend (graphEdgeGates gs)
      (graphTail true gs (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))
     else graphTail false gs (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))

/-- The Boolean measurement outcomes of a graph history, listed in wire-step order. -/
def graphMessage {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) : List Bool :=
  (List.ofFn (fun t : Fin L => t)).filterMap (fun t => if graphWireAt gs t then some (h.1 t) else none)
/-- The binary index encoded by the graph history's measurement message. -/
def graphHistoryIndex {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) : ℕ :=
  (graphMessage gs h).foldl (fun a b => 2*a+(if b then 1 else 0)) 0
/-- The observed Kraus leaf selected by a graph history index, with a rejecting zero leaf as the
default for an invalid index. -/
noncomputable def graphProgramLeaf {n L : ℕ} (preentangled : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) : ObservedKrausLeaf (2^(n+L)) :=
  (observedKrausLeaves 1 (graphProgram preentangled gs)).getD (graphHistoryIndex gs h)
    ⟨0,false,0,0,0,[]⟩

/-- The embedding of the logical input into the initial physical vertices with all fresh
vertices set to zero. -/
noncomputable def graphInputFrame (n L : ℕ) : Matrix (Fin (2^(n+L))) (Fin (2^n)) ℂ :=
  fun r j =>
    let x := (bitVecEquiv (n+L)).symm r
    let y := (bitVecEquiv n).symm j
    if (∀ i, x (Fin.castAdd L i)=y i) ∧ (∀ t, x (graphFresh n L t)=false) then 1 else 0

/-- The physical bit assignment obtained by replacing the active layout coordinates with a given
logical register. -/
def graphOverlay (n L : ℕ) (lay : Fin n → Fin (n+L)) (z : Reg (n+L)) (y : Reg n) : Reg (n+L) :=
  (List.ofFn (fun i : Fin n => i)).foldl (fun z i => Function.update z (lay i) (y i)) z
/-- The contraction over physical spectator bits determined by a logical layout, retaining the
reference-system indices. -/
noncomputable def graphDiscardReference (n L R : ℕ) (lay : Fin n → Fin (n+L))
    (A : Matrix (Fin (2^(n+L)) × Fin R) (Fin (2^(n+L)) × Fin R) ℂ) :
    Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ :=
  fun p q =>
    let x := (bitVecEquiv n).symm p.1
    let y := (bitVecEquiv n).symm q.1
    ∑ z : Reg (n+L), if (∀ i, z (lay i)=x i) then
      A ((bitVecEquiv (n+L)) z,p.2)
        ((bitVecEquiv (n+L)) (graphOverlay n L lay z y),q.2) else 0
/-- The actual branch action on a logical input and reference system, obtained by input
embedding, physical leaf conjugation, and spectator contraction. -/
noncomputable def graphActualReference {n L : ℕ} (preentangled : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) (R : ℕ) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :=
  let F := (graphInputFrame n L) ⊗ₖ (1:Operator R)
  let K := TensorGate (graphProgramLeaf preentangled gs h).operator (1:Operator R)
  graphDiscardReference n L R (graphLayoutFinal gs) (K*(F*X*Fᴴ)*Kᴴ)
/-- The logical branch map extracted from `graphActualReference` with a one-dimensional
reference system. -/
noncomputable def graphActualBranch {n L : ℕ} (preentangled : Bool) (gs : GraphWord n L)
    (h : GraphHistory gs) (ρ : Operator (2^n)) : Operator (2^n) :=
  let X := TensorGate ρ (1:Operator 1)
  let Y := graphActualReference preentangled gs h 1 X
  fun i j => Y (i,0) (j,0)

/-- The pure-state density matrix of the zero-state and plus-state product used as the Bell
graph input. -/
noncomputable def graphBellInput : Operator 4 :=
  outerProduct (relabelState finProdFinEquiv
    (TensorState (Ket (0:Fin 2))
      (relabelState boolEquivFin2 (ApplyGate Hadamard (Ket false)))))
/-- The Bell resource density matrix relabeled to a four-dimensional computational basis. -/
noncomputable def graphBellOutput : Operator 4 :=
  outerProduct (relabelState
    ((Equiv.prodCongr boolEquivFin2 boolEquivFin2).trans finProdFinEquiv) teleportBellResource)
/-- The three-step two-wire word consisting of a parameter-one wire gate, a CZ, and a
parameter-one gate on the other wire. -/
def graphBellWord : GraphWord 2 3 := ![.inl (0,1),.inr (0,1),.inl (1,1)]

/-- The active layout obtained by processing the first `k` graph-word positions. -/
def graphLayoutPrefix {n L : ℕ} (gs : GraphWord n L) (k : ℕ) : Fin n → Fin (n+L) :=
  ((List.ofFn (fun s : Fin L => s)).take k).foldl (graphAdvance gs) (Fin.castAdd L)

/-- Extending a valid layout prefix by one position applies the corresponding `graphAdvance`
update. -/
theorem graphLayoutPrefix_step {n L : ℕ} (gs : GraphWord n L) (k : ℕ) (hk : k < L) :
    graphLayoutPrefix gs (k+1) = graphAdvance gs (graphLayoutPrefix gs k) ⟨k,hk⟩ := by
  unfold graphLayoutPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using! hk), List.foldl_append]
  simp

/-- A layout prefix is injective, uses only vertices allocated so far, and avoids every earlier
measured vertex. -/
theorem graphLayoutPrefix_invariant {n L : ℕ} (gs : GraphWord n L) (k : ℕ) (hk : k ≤ L) :
    Function.Injective (graphLayoutPrefix gs k) ∧
    (∀ i, (graphLayoutPrefix gs k i).val < n+k) ∧
    (∀ (s : Fin L) (i : Fin n) (ζ : ℂ), s.val < k → gs s = .inl (i,ζ) →
      ∀ j, graphLayoutPrefix gs k j ≠ graphLayoutBefore gs s i) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp only [graphLayoutPrefix, List.take_zero, List.foldl_nil]
      refine ⟨Fin.castAdd_injective n L, ?_, ?_⟩
      · intro i
        simp
      · intro s i ζ hs
        omega
    | succ k =>
      have hkl : k < L := by omega
      obtain ⟨hinj, hbound, hretired⟩ := ih k (by omega) (by omega)
      rw [graphLayoutPrefix_step gs k hkl]
      generalize hg : gs ⟨k,hkl⟩ = g
      cases g with
      | inl p =>
        obtain ⟨i,ζ⟩ := p
        simp only [graphAdvance, hg]
        have hfresh : ∀ j, graphFresh n L ⟨k,hkl⟩ ≠ graphLayoutPrefix gs k j := by
          intro j he
          have he' := congrArg Fin.val he
          have hb := hbound j
          simp only [graphFresh, Fin.val_natAdd] at he'
          omega
        refine ⟨?_, ?_, ?_⟩
        · intro a b hab
          by_cases ha : a = i
          · subst a
            by_cases hb : b = i
            · exact hb.symm
            · simp only [Function.update_self, Function.update_of_ne hb] at hab
              exact False.elim (hfresh b hab)
          · by_cases hb : b = i
            · subst b
              simp only [Function.update_self, Function.update_of_ne ha] at hab
              exact False.elim (hfresh a hab.symm)
            · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
              exact hinj hab
        · intro j
          by_cases hj : j = i
          · subst j
            simp [graphFresh]
          · rw [Function.update_of_ne hj]
            have := hbound j
            omega
        · intro s a η hs hgs j
          by_cases hsk : s.val < k
          · by_cases hj : j = i
            · subst j
              rw [Function.update_self]
              intro he
              have hbs := (ih s.val (by omega) (by omega)).2.1 a
              change (graphLayoutBefore gs s a).val < n+s.val at hbs
              have he' := congrArg Fin.val he
              simp only [graphFresh, Fin.val_natAdd] at he'
              omega
            · rw [Function.update_of_ne hj]
              exact hretired s a η hsk hgs j
          · have hse : s = ⟨k,hkl⟩ := Fin.ext (by change s.val = k; omega)
            subst s
            have hp : i = a := congrArg Prod.fst (Sum.inl.inj (hg.symm.trans hgs))
            subst a
            change Function.update (graphLayoutPrefix gs k) i (graphFresh n L ⟨k,hkl⟩) j ≠
              graphLayoutPrefix gs k i
            by_cases hj : j = i
            · subst j
              simpa using! hfresh i
            · rw [Function.update_of_ne hj]
              exact fun he => hj (hinj he)
      | inr p =>
        simp only [graphAdvance, hg]
        refine ⟨hinj, ?_, ?_⟩
        · intro j
          have := hbound j
          omega
        · intro s a η hs hgs j
          have hsk : s.val < k := by
            by_contra h
            have hse : s = ⟨k,hkl⟩ := Fin.ext (by change s.val = k; omega)
            subst s
            simp [hg] at hgs
          exact hretired s a η hsk hgs j

/-- For a legal graph word, the active and final layouts are injective, edges have distinct
endpoints, and later edges and active wires avoid previously measured vertices. -/
theorem graph_layout_geometry {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) :
    Function.Injective (graphLayoutFinal gs) ∧
    (∀ (s : Fin L) (i : Fin n) (ζ : ℂ), gs s = .inl (i,ζ) →
      ∀ j, graphLayoutFinal gs j ≠ graphLayoutBefore gs s i) ∧
    (∀ t : Fin L, Function.Injective (graphLayoutBefore gs t) ∧
      (∀ i, (graphLayoutBefore gs t i).val < n+t.val) ∧
      (graphEdgeEndpoints gs t).1 ≠ (graphEdgeEndpoints gs t).2) ∧
    (∀ (s t : Fin L) (i : Fin n) (ζ : ℂ), s<t → gs s=.inl (i,ζ) →
      (graphEdgeEndpoints gs t).1 ≠ graphLayoutBefore gs s i ∧
      (graphEdgeEndpoints gs t).2 ≠ graphLayoutBefore gs s i ∧
      (∀ j, graphLayoutBefore gs t j ≠ graphLayoutBefore gs s i)) := by
  have hfinal : graphLayoutPrefix gs L = graphLayoutFinal gs := by
    unfold graphLayoutPrefix graphLayoutFinal
    rw [List.take_of_length_le (by simp)]
  obtain ⟨hinj, _, hretired⟩ := graphLayoutPrefix_invariant gs L le_rfl
  rw [hfinal] at hinj hretired
  refine ⟨hinj, ?_, ?_, ?_⟩
  · intro s i ζ hs j
    exact hretired s i ζ s.isLt hs j
  · intro t
    obtain ⟨hi, hb, _⟩ := graphLayoutPrefix_invariant gs t.val (Nat.le_of_lt t.isLt)
    change Function.Injective (graphLayoutBefore gs t) at hi
    change (∀ i, (graphLayoutBefore gs t i).val < n+t.val) at hb
    refine ⟨hi, hb, ?_⟩
    have hl := hlegal (gs t) (List.mem_ofFn.mpr ⟨t,rfl⟩)
    cases hg : gs t with
    | inl p =>
      simp only [graphEdgeEndpoints, hg]
      intro he
      have hv := congrArg Fin.val he
      have hbi := hb p.1
      simp only [graphFresh, Fin.val_natAdd] at hv
      omega
    | inr p =>
      simp only [hg] at hl
      simp only [graphEdgeEndpoints, hg]
      exact fun he => hl (hi he)
  · intro s t i ζ hst hs
    have hr := (graphLayoutPrefix_invariant gs t.val (Nat.le_of_lt t.isLt)).2.2
      s i ζ hst hs
    change ∀ j, graphLayoutBefore gs t j ≠ graphLayoutBefore gs s i at hr
    refine ⟨?_, ?_, hr⟩
    · cases hg : gs t <;> simp only [graphEdgeEndpoints, hg] <;> exact hr _
    · cases hg : gs t with
      | inl p =>
        simp only [graphEdgeEndpoints, hg]
        intro he
        have hb := (graphLayoutPrefix_invariant gs s.val (Nat.le_of_lt s.isLt)).2.1 i
        change (graphLayoutBefore gs s i).val < n+s.val at hb
        have hv := congrArg Fin.val he
        simp only [graphFresh, Fin.val_natAdd] at hv
        change s.val < t.val at hst
        omega
      | inr p =>
        simp only [graphEdgeEndpoints, hg]
        exact hr _

/-- The equivalence between graph histories and arbitrary Boolean assignments to the
wire-measurement positions. -/
noncomputable def graphHistoryEquiv {n L : ℕ} (gs : GraphWord n L) :
    GraphHistory gs ≃ ({t : Fin L // graphWireAt gs t = true} → Bool) where
  toFun h t := h.1 t.1
  invFun f := ⟨fun t => if ht : graphWireAt gs t = true then f ⟨t,ht⟩ else false,
    by intro t ht; simp [ht]⟩
  left_inv h := by
    apply Subtype.ext
    funext t
    cases ht : graphWireAt gs t
    · simp [ht, h.2 t ht]
    · simp [ht]
  right_inv f := by
    funext t
    simp [t.2]

/-- The wire count equals the sum of the wire-position indicators over the graph word. -/
theorem graphWireCount_eq_sum {n L : ℕ} (gs : GraphWord n L) :
    graphWireCount gs = ∑ t : Fin L, if graphWireAt gs t then 1 else 0 := by
  have hc : ∀ ts : List (Fin L), (networkCounts (ts.map gs)).1 =
      (ts.map (fun t => if graphWireAt gs t then 1 else 0)).sum := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      cases hg : gs t <;> simp [List.map_cons, networkCounts, hg, graphWireAt, ih, Nat.add_comm]
  have := hc (List.ofFn (fun t : Fin L => t))
  simpa [graphWireCount, List.map_ofFn, List.sum_ofFn] using! this

/-- The number of graph histories is `2^(graphWireCount gs)`. -/
theorem graphHistory_card {n L : ℕ} (gs : GraphWord n L) :
    Fintype.card (GraphHistory gs) = 2^(graphWireCount gs) := by
  rw [Fintype.card_congr (graphHistoryEquiv gs), Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype, Finset.card_filter, graphWireCount_eq_sum]

/-- The computational-basis index obtained by appending zero-valued fresh vertices to a logical
basis index. -/
def graphInputIndex (n L : ℕ) (j : Fin (2^n)) : Fin (2^(n+L)) :=
  bitVecEquiv (n+L) (Fin.append ((bitVecEquiv n).symm j) (fun _ : Fin L => false))

/-- Appending zero-valued fresh vertices gives an injective map on logical basis indices. -/
theorem graphInputIndex_injective (n L : ℕ) : Function.Injective (graphInputIndex n L) := by
  intro i j hij
  apply (bitVecEquiv n).symm.injective
  funext a
  have h := congrArg (fun r => (bitVecEquiv (n+L)).symm r (Fin.castAdd L a)) hij
  simpa [graphInputIndex] using! h

/-- An input-frame entry is one precisely at the embedded logical basis index and zero
elsewhere. -/
theorem graphInputFrame_entry (n L : ℕ) (r : Fin (2^(n+L))) (j : Fin (2^n)) :
    graphInputFrame n L r j = if r = graphInputIndex n L j then 1 else 0 := by
  have he : ((∀ i, (bitVecEquiv (n+L)).symm r (Fin.castAdd L i) =
      (bitVecEquiv n).symm j i) ∧
      (∀ t, (bitVecEquiv (n+L)).symm r (graphFresh n L t) = false)) ↔
      r = graphInputIndex n L j := by
    constructor
    · rintro ⟨hl,hr⟩
      apply (bitVecEquiv (n+L)).symm.injective
      funext a
      refine Fin.addCases (fun i => ?_) (fun t => ?_) a
      · simpa [graphInputIndex] using! hl i
      · simpa [graphInputIndex, graphFresh] using! hr t
    · intro h
      subst r
      simp [graphInputIndex, graphFresh]
  simp only [graphInputFrame, he]

/-- The graph input frame is an isometry. -/
theorem graphInputFrame_isometry (n L : ℕ) : IsIsometry (graphInputFrame n L) := by
  unfold IsIsometry
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, graphInputFrame_entry]
  rw [Finset.sum_eq_single (graphInputIndex n L i)]
  · simp [Matrix.one_apply, (graphInputIndex_injective n L).eq_iff]
  · intro r _ hr
    simp [hr]
  · simp

/-- A legal graph word has an isometric input embedding, injective layouts avoiding measured
vertices, distinct edge endpoints, and exactly `2^(graphWireCount gs)` histories. See
[RaussendorfBriegel2000]. -/
theorem preentangled_graph_actual_layout_and_history :
    ∀ (n L : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
    IsIsometry (graphInputFrame n L) ∧
    Function.Injective (graphLayoutFinal gs) ∧
    (∀ (s : Fin L) (i : Fin n) (ζ : ℂ), gs s = .inl (i,ζ) →
      ∀ j, graphLayoutFinal gs j ≠ graphLayoutBefore gs s i) ∧
    (∀ t : Fin L, Function.Injective (graphLayoutBefore gs t) ∧
      (∀ i, (graphLayoutBefore gs t i).val < n+t.val) ∧
      (graphEdgeEndpoints gs t).1 ≠ (graphEdgeEndpoints gs t).2) ∧
    (∀ (s t : Fin L) (i : Fin n) (ζ : ℂ), s<t → gs s=.inl (i,ζ) →
      (graphEdgeEndpoints gs t).1 ≠ graphLayoutBefore gs s i ∧
      (graphEdgeEndpoints gs t).2 ≠ graphLayoutBefore gs s i ∧
      (∀ j, graphLayoutBefore gs t j ≠ graphLayoutBefore gs s i)) ∧
    Fintype.card (GraphHistory gs)=2^(graphWireCount gs) := by
  intro n L gs hgs
  obtain ⟨hi, hm, he, hf⟩ := graph_layout_geometry gs hgs
  exact ⟨graphInputFrame_isometry n L, hi, hm, he, hf, graphHistory_card gs⟩

/-- A graph history message has one bit for each wire measurement. -/
theorem graphMessage_length {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (graphMessage gs h).length = graphWireCount gs := by
  have hc : ∀ ts : List (Fin L),
      (ts.filterMap (fun t => if graphWireAt gs t then some (h.1 t) else none)).length =
      (ts.map (fun t => if graphWireAt gs t then 1 else 0)).sum := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => cases ht : graphWireAt gs t <;> simp [ht, ih, Nat.add_comm]
  simpa [graphMessage, List.map_ofFn, List.sum_ofFn, graphWireCount_eq_sum] using!
    hc (List.ofFn (fun t : Fin L => t))

/-- The measurement message uniquely determines a graph history. -/
theorem graphMessage_injective {n L : ℕ} (gs : GraphWord n L) :
    Function.Injective (graphMessage gs) := by
  have hd : ∀ (ts : List (Fin L)) (h k : GraphHistory gs),
      ts.filterMap (fun t => if graphWireAt gs t then some (h.1 t) else none) =
      ts.filterMap (fun t => if graphWireAt gs t then some (k.1 t) else none) →
      ∀ t ∈ ts, h.1 t = k.1 t := by
    intro ts
    induction ts with
    | nil => simp
    | cons s ts ih =>
      intro h k he t ht
      cases hs : graphWireAt gs s
      · simp only [List.filterMap_cons, hs, Bool.false_eq_true, if_false] at he
        rcases List.mem_cons.mp ht with rfl | ht
        · rw [h.2 t hs, k.2 t hs]
        · exact ih h k he t ht
      · simp only [List.filterMap_cons, hs, if_true, List.cons.injEq] at he
        rcases List.mem_cons.mp ht with rfl | ht
        · exact he.1
        · exact ih h k he.2 t ht
  intro h k he
  apply Subtype.ext
  funext t
  exact hd (List.ofFn (fun t : Fin L => t)) h k he t (List.mem_ofFn.mpr ⟨t,rfl⟩)

/-- The number of physical correction gates equals the Pauli-frame correction cost. -/
theorem graphCorrectionGates_length {n L : ℕ} (gs : GraphWord n L) (F : PauliFrame n) :
    (graphCorrectionGates gs F).length = frameCorrectionCost F := by
  simp only [graphCorrectionGates, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.sum_ofFn, frameCorrectionCost, List.length_append]
  apply Finset.sum_congr rfl
  intro i _
  cases F.1 i <;> cases F.2 i <;> simp

/-- Prepending gates preserves the number of observed circuit leaves. -/
theorem graphPrepend_leafCount {D : ℕ} (Us : List (Operator D))
    (P : ObservedCircuit (Fin D)) : observedLeafCount (graphPrepend Us P) = observedLeafCount P := by
  induction Us with
  | nil => rfl
  | cons U Us ih => simpa [graphPrepend, observedLeafCount] using! ih

/-- The number of wire-measurement slots among a specified list of graph-word positions. -/
def graphSlotCount {n L : ℕ} (gs : GraphWord n L) (ts : List (Fin L)) : ℕ :=
  (ts.map (fun t => if graphWireAt gs t then 1 else 0)).sum

/-- A compiled graph tail has `2^(graphSlotCount gs ts)` leaves. -/
theorem graphTail_leafCount {n L : ℕ} (pre : Bool) (gs : GraphWord n L)
    (ts : List (Fin L)) (F : PauliFrame n) :
    observedLeafCount (graphTail pre gs ts F) = 2^(graphSlotCount gs ts) := by
  induction ts generalizing F with
  | nil => simp [graphTail, graphPrepend_leafCount, observedLeafCount, graphSlotCount]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      cases pre <;>
        simp [graphTail, hg, observedLeafCount, ih, graphSlotCount, graphWireAt,
          pow_succ, pow_add, two_mul]
    | inr p =>
      cases pre <;>
        simp [graphTail, hg, observedLeafCount, ih, graphSlotCount, graphWireAt]

/-- A full graph program has `2^(graphWireCount gs)` leaves under either entanglement schedule. -/
theorem graphProgram_leafCount {n L : ℕ} (pre : Bool) (gs : GraphWord n L) :
    observedLeafCount (graphProgram pre gs) = 2^(graphWireCount gs) := by
  have hc : graphSlotCount gs (List.ofFn (fun t : Fin L => t)) = graphWireCount gs := by
    simp [graphSlotCount, List.map_ofFn, List.sum_ofFn, graphWireCount_eq_sum]
  cases pre <;> simp [graphProgram, graphPrepend_leafCount, graphTail_leafCount, hc]

/-- Any two physical CZ gates commute. -/
theorem graph_cz_commute {N : ℕ} (u v a b : Fin N) :
    networkCzGate u v * networkCzGate a b = networkCzGate a b * networkCzGate u v := by
  simp only [networkCzGate, ← teleportRelabelGate_mul]
  congr 1
  simp only [networkCzGateB, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

/-- A one-wire gate has a zero matrix entry whenever the input and output registers differ on
another wire. -/
theorem graph_wire_entry_zero {N : ℕ} (q k : Fin N) (U : Operator 2)
    (x y : Reg N) (hk : k ≠ q) (hxy : x k ≠ y k) :
    pauliProductDensity (fun i => if i = q then U else 1) x y = 0 := by
  unfold pauliProductDensity
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  (try dsimp only)
  rw [if_neg hk]
  exact Matrix.one_apply_ne (fun h => hxy (boolEquivFin2.injective h))

/-- A physical CZ commutes with any one-qubit gate on a wire distinct from both endpoints. -/
theorem graph_cz_disjoint_wire_commute {N : ℕ} (u v q : Fin N) (U : Operator 2)
    (hu : q ≠ u) (hv : q ≠ v) :
    networkCzGate u v * tensorPauliWireGate N q U =
      tensorPauliWireGate N q U * networkCzGate u v := by
  simp only [networkCzGate, tensorPauliWireGate, tensorPauliProduct, ← teleportRelabelGate_mul]
  congr 1
  ext x y
  simp only [networkCzGateB, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : x u = y u
  · by_cases hy : x v = y v
    · rw [hx, hy, mul_comm]
    · rw [graph_wire_entry_zero q v U x y (Ne.symm hv) hy, mul_zero, zero_mul]
  · rw [graph_wire_entry_zero q u U x y (Ne.symm hu) hx, mul_zero, zero_mul]

/-- The physical outcome projector is diagonal, with entries indicating the specified
measurement label. -/
theorem graph_physical_projector_diagonal (n L : ℕ) (q : Fin (n+L)) (o : Bool) :
    graphPhysicalProjector n L q o = Matrix.diagonal (fun r =>
      if graphPhysicalLabel n L q r = boolEquivFin2 o then (1 : ℂ) else 0) := by
  ext x y
  simp [graphPhysicalProjector, Projector, Matrix.diagonal_apply]

/-- A physical CZ is diagonal, with entry minus one exactly when both endpoint bits are true. -/
theorem graph_cz_numeric_diagonal {N : ℕ} (u v : Fin N) :
    networkCzGate u v = Matrix.diagonal (fun r =>
      if ((bitVecEquiv N).symm r u) && ((bitVecEquiv N).symm r v) then (-1 : ℂ) else 1) := by
  ext x y
  simp [networkCzGate, networkCzGateB, relabelGate, Matrix.reindex_apply, Matrix.diagonal_apply,
    (bitVecEquiv N).symm.injective.eq_iff]

/-- Physical CZ gates commute with one another and with Hadamards, phase gates, and outcome
projectors on disjoint vertices. See [RaussendorfBriegel2000]. -/
theorem preentangled_graph_physical_disjoint_commutation :
∀ (n L : ℕ) (u v a b q : Fin (n+L)) (ζ : ℂ) (o : Bool),
  networkCzGate u v*networkCzGate a b=networkCzGate a b*networkCzGate u v ∧
  (q≠u → q≠v →
    networkCzGate u v*graphPhysicalH n L q=graphPhysicalH n L q*networkCzGate u v ∧
    networkCzGate u v*graphPhysicalPhase n L q ζ=graphPhysicalPhase n L q ζ*networkCzGate u v ∧
    networkCzGate u v*graphPhysicalProjector n L q o=graphPhysicalProjector n L q o*networkCzGate u v) := by
  intro n L u v a b q ζ o
  refine ⟨graph_cz_commute u v a b, fun hu hv => ⟨?_, ?_, ?_⟩⟩
  · exact graph_cz_disjoint_wire_commute u v q _ hu hv
  · exact graph_cz_disjoint_wire_commute u v q _ hu hv
  · rw [graph_physical_projector_diagonal, graph_cz_numeric_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact mul_comm _ _

end Qatlib.Concepts.ClusterPatterns.Preentangled
