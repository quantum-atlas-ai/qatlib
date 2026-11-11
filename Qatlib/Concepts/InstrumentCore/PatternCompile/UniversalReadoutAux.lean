/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalRawGraphAux

/-!
# Auxiliary laws for graph output readout

This module describes the leaves of graph measurement programs with a final computational-basis
readout. It proves well-formedness for legal graph words, identifies leaf operators and outcome
records, and gives a bijection between leaves and pairs consisting of a graph history and an
output label.

The map `mbqcDiscard` extracts the logical output by discarding the other physical qubits. Its
trace identities connect the physical output measurement to the logical branch probabilities in
measurement-based computation [RaussendorfBriegel2000].

## Main statements

* `mbqcReadoutLeaf_fields`: exact operators, acceptance tests, resources, and records.
* `mbqcReadoutIndex_bijective`: histories and output labels enumerate all readout leaves.
* `mbqcOutputLabel_mass`: physical readout mass equals a diagonal entry of the discarded output.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- Construct the readout-tail leaf for a fixed history and output label, ending with the
corresponding output projector and decoded event test. -/
def mbqcReadoutTailLeaf {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) :
    List (Fin L) → PauliFrame n → ObservedKrausLeaf (2^(n+L))
  | [],F => ⟨Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y)),
      decide (mbqcFrameDecode F y ∈ E),0,0,1,[(2^n,y.val)]⟩
  | t::ts,F =>
    let rest := mbqcReadoutTailLeaf G E h y ts (graphFrameAdvance G h F t)
    match G t with
    | .inl (i,z) =>
      ((rest.prepend (graphPhysicalProjector n L (graphLayoutBefore G t i) (h.1 t))
        0 0 1 [(2,(boolEquivFin2 (h.1 t)).val)]).prepend
        (graphPhysicalH n L (graphLayoutBefore G t i)) 0 1 0 []).prepend
        (graphPhysicalPhase n L (graphLayoutBefore G t i)
          (if F.1 i then star z else z)) 0 1 0 []
    | .inr _ => rest

/-- The readout tail has `2^graphSlotCount G ts * 2^n` leaves. -/
theorem mbqcReadoutTail_leafCount {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (ts : List (Fin L)) (F : PauliFrame n) :
    observedLeafCount (mbqcReadoutTail G E ts F) = 2^(graphSlotCount G ts)*2^n := by
  induction ts generalizing F with
  | nil => simp [mbqcReadoutTail,observedLeafCount,graphSlotCount]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      simp [mbqcReadoutTail,hg,observedLeafCount,ih,graphSlotCount,graphWireAt,
        pow_succ,pow_add,two_mul,add_mul]
    | inr p => simp [mbqcReadoutTail,hg,ih,graphSlotCount,graphWireAt]

/-- The full readout program has `2^graphWireCount G * 2^n` leaves. -/
theorem mbqcReadoutProgram_leafCount {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n))) :
    observedLeafCount (mbqcReadoutProgram G E) = 2^(graphWireCount G)*2^n := by
  have hc : graphSlotCount G (List.ofFn (fun t : Fin L => t))=graphWireCount G := by
    simp [graphSlotCount,List.map_ofFn,List.sum_ofFn,graphWireCount_eq_sum]
  simp [mbqcReadoutProgram,graphPrepend_leafCount,mbqcReadoutTail_leafCount,hc]

/-- The readout tail of a legal graph word is well formed for any event, slot list, and initial
Pauli frame. -/
theorem mbqcReadoutTail_wellFormed {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (E : Finset (Fin (2^n)))
    (ts : List (Fin L)) (F : PauliFrame n) : observedWellFormed (mbqcReadoutTail G E ts F) := by
  induction ts generalizing F with
  | nil => intro y; trivial
  | cons t ts ih =>
    have hl := hlegal (G t) (List.mem_ofFn.mpr ⟨t,rfl⟩)
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      simp only [hg] at hl
      have hz : ‖(if F.1 i then star z else z)‖=1 := by split_ifs <;> simpa using! hl
      simp only [mbqcReadoutTail,hg]
      exact ⟨graphPhysicalPhase_unitary _ _ _ _ hz,graphPhysicalH_unitary _ _ _,fun a => ih _⟩
    | inr p =>
      obtain ⟨i,j⟩ := p
      simpa only [mbqcReadoutTail,hg] using! ih (graphCzFrame F i j)

/-- The complete readout program of a legal graph word is well formed for every output event. -/
theorem mbqcReadoutProgram_wellFormed {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (E : Finset (Fin (2^n))) :
    observedWellFormed (mbqcReadoutProgram G E) := by
  apply graphPrepend_wellFormed
  · intro U hU
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hU
    exact graphPhysicalH_unitary _ _ _
  · apply graphPrepend_wellFormed
    · intro U hU
      obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hU
      exact networkCzGate_unitary _ _
    · exact mbqcReadoutTail_wellFormed G hlegal E _ _

/-- Flattening the list of singleton lists formed from `ls` returns `ls`. -/
private theorem flatten_singletons {α : Type*} (ls : List α) :
    (ls.map (fun a => [a])).flatten=ls := by
  induction ls with
  | nil => rfl
  | cons a ls ih => simp [ih]

/-- With no remaining graph slots, the readout leaves are exactly the output-label projectors
with their decoded acceptance tests and single measurement records. -/
private theorem mbqcReadoutBase_leaves {n L : ℕ} (G : GraphWord n L)
    (E : Finset (Fin (2^n))) (F : PauliFrame n) :
    observedKrausLeaves 1 (mbqcReadoutTail G E [] F)=
      List.ofFn (fun y => (⟨Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y)),
        decide (mbqcFrameDecode F y ∈ E),0,0,1,[(2^n,y.val)]⟩ : ObservedKrausLeaf (2^(n+L)))) := by
  simp only [mbqcReadoutTail,observedKrausLeaves,List.map_singleton,
    ObservedKrausLeaf.prepend,Matrix.one_mul,Nat.zero_add,List.append_nil]
  have hf (f : Fin (2^n) → ObservedKrausLeaf (2^(n+L))) :
      (List.ofFn (fun y => [f y])).flatten=List.ofFn f := by
    simpa only [List.map_ofFn,Function.comp_def] using! flatten_singletons (List.ofFn f)
  exact hf _

/-- The readout-tail Kraus enumeration selects the history-and-output leaf at the tail-message
index multiplied by `2^n` plus `y.val`. -/
theorem mbqcReadoutTailLeaf_get {n L : ℕ} (G : GraphWord n L)
    (E : Finset (Fin (2^n))) (h : GraphHistory G) (y : Fin (2^n))
    (ts : List (Fin L)) (F : PauliFrame n) :
    (observedKrausLeaves 1 (mbqcReadoutTail G E ts F))[
      graphBitsIndex (graphTailMessage G h ts)*2^n+y.val]?=
        some (mbqcReadoutTailLeaf G E h y ts F) := by
  induction ts generalizing F with
  | nil =>
    rw [mbqcReadoutBase_leaves]
    simp [graphTailMessage,graphBitsIndex,mbqcReadoutTailLeaf]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      have hk : graphBitsIndex (graphTailMessage G h ts)*2^n+y.val <
          2^(graphSlotCount G ts)*2^n := by
        have hb := graphBitsIndex_lt (graphTailMessage G h ts)
        rw [graphTailMessage_length] at hb
        have hy := y.isLt
        have hp : 0 < 2^n := by positivity
        nlinarith
      have hm := graphMeasurementLeaf_get (graphPhysicalLabel n L (graphLayoutBefore G t i))
        (fun a => mbqcReadoutTail G E ts (graphWireFrame F i (boolEquivFin2.symm a)))
        (h.1 t) (graphBitsIndex (graphTailMessage G h ts)*2^n+y.val)
        (2^(graphSlotCount G ts)*2^n)
        (fun o => by rw [observedKrausLeaves_length,mbqcReadoutTail_leafCount]) hk _
        (by simpa using! ih (graphWireFrame F i (h.1 t)))
      have hmH := graphGateLeaf_get (graphPhysicalH n L (graphLayoutBefore G t i)) _ _ _ hm
      have hmP := graphGateLeaf_get (graphPhysicalPhase n L (graphLayoutBefore G t i)
        (if F.1 i then star z else z)) _ _ _ hmH
      have hmsg : graphTailMessage G h (t::ts)=h.1 t::graphTailMessage G h ts := by
        simp [graphTailMessage,graphWireAt,hg]
      rw [hmsg,graphBitsIndex_cons,graphTailMessage_length,add_mul]
      have hidx : (if h.1 t then 2^(graphSlotCount G ts) else 0)*2^n+
          graphBitsIndex (graphTailMessage G h ts)*2^n+y.val =
          (if h.1 t then 2^(graphSlotCount G ts)*2^n else 0)+
            (graphBitsIndex (graphTailMessage G h ts)*2^n+y.val) := by
        split_ifs <;> omega
      rw [hidx]
      simpa only [mbqcReadoutTail,mbqcReadoutTailLeaf,hg,graphFrameAdvance,
        graphPhysicalProjector] using! hmP
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hmsg : graphTailMessage G h (t::ts)=graphTailMessage G h ts := by
        simp [graphTailMessage,graphWireAt,hg]
      rw [hmsg]
      simpa only [mbqcReadoutTail,mbqcReadoutTailLeaf,hg,graphFrameAdvance] using!
        ih (graphCzFrame F i j)

/-- A full readout leaf is its recursive tail leaf with the fresh-qubit and graph-edge gates
prepended. -/
theorem mbqcReadoutLeaf_eq {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) :
    mbqcReadoutLeaf G E h y = graphPrependLeaf (graphFreshGates n L)
      (graphPrependLeaf (graphEdgeGates G)
        (mbqcReadoutTailLeaf G E h y (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))) := by
  have ht := mbqcReadoutTailLeaf_get G E h y (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  have he := graphPrependLeaf_get (graphFreshGates n L) _ _ _
    (graphPrependLeaf_get (graphEdgeGates G) _ _ _ ht)
  rw [mbqcReadoutLeaf,List.getD_eq_getElem?_getD]
  change (observedKrausLeaves 1 (graphPrepend _ (graphPrepend _ _)))[
    graphBitsIndex (graphTailMessage G h (List.ofFn (fun t : Fin L => t)))*2^n+y.val]?.getD _ = _
  rw [he]
  rfl

/-- A readout-tail leaf is the output projector times the raw tail operator, with acceptance
determined by the final decoded label. It makes no queries, uses two gates per counted slot
and one additional readout measurement, and appends the output to the raw record. -/
theorem mbqcReadoutTailLeaf_fields {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) (ts : List (Fin L)) (F : PauliFrame n) :
    (mbqcReadoutTailLeaf G E h y ts F).operator=
      Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y))*(mbqcRawTailLeaf G h ts F).operator ∧
    (mbqcReadoutTailLeaf G E h y ts F).accepted=
      decide (mbqcFrameDecode (ts.foldl (graphFrameAdvance G h) F) y ∈ E) ∧
    (mbqcReadoutTailLeaf G E h y ts F).queries=0 ∧
    (mbqcReadoutTailLeaf G E h y ts F).gates=2*graphSlotCount G ts ∧
    (mbqcReadoutTailLeaf G E h y ts F).measurements=graphSlotCount G ts+1 ∧
    (mbqcReadoutTailLeaf G E h y ts F).outcomes=(mbqcRawTailLeaf G h ts F).outcomes++[(2^n,y.val)] := by
  induction ts generalizing F with
  | nil => simp [mbqcReadoutTailLeaf,mbqcRawTailLeaf,graphSlotCount]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      obtain ⟨ho,ha,hq,hgates,hm,hout⟩ := ih (graphWireFrame F i (h.1 t))
      have hc : graphSlotCount G (t::ts)=graphSlotCount G ts+1 := by
        simp [graphSlotCount,graphWireAt,hg,Nat.add_comm]
      simp only [mbqcReadoutTailLeaf,mbqcRawTailLeaf,hg,graphFrameAdvance,
        ObservedKrausLeaf.prepend,ho,ha,hq,hgates,hm,hout,hc,List.foldl_cons,
        List.nil_append,Matrix.mul_assoc,Nat.add_zero,List.append_assoc]
      simp only [true_and,and_true]
      omega
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hc : graphSlotCount G (t::ts)=graphSlotCount G ts := by
        simp [graphSlotCount,graphWireAt,hg]
      simpa only [mbqcReadoutTailLeaf,mbqcRawTailLeaf,hg,graphFrameAdvance,hc,List.foldl_cons] using!
        ih (graphCzFrame F i j)

/-- Prepending gates to a Kraus leaf preserves its outcome record. -/
private theorem graphPrependLeaf_outcomes {D : ℕ} (Us : List (Operator D)) (leaf : ObservedKrausLeaf D) :
    (graphPrependLeaf Us leaf).outcomes=leaf.outcomes := by
  induction Us with
  | nil => rfl
  | cons U Us ih => simpa [graphPrependLeaf,ObservedKrausLeaf.prepend] using! ih

/-- The history-and-output index is in range, and its leaf is the output projector times the raw
leaf with the decoded acceptance test. It makes no queries, uses `2*L + 2*graphWireCount G`
gates and `graphWireCount G + 1` measurements, and appends the output record. -/
theorem mbqcReadoutLeaf_fields {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) :
    graphHistoryIndex G h*2^n+y.val < observedLeafCount (mbqcReadoutProgram G E) ∧
    (mbqcReadoutLeaf G E h y).operator =
      Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y))*(mbqcRawLeaf G h).operator ∧
    (mbqcReadoutLeaf G E h y).accepted=decide (mbqcFrameDecode (graphFinalFrame G h) y ∈ E) ∧
    (mbqcReadoutLeaf G E h y).queries=0 ∧
    (mbqcReadoutLeaf G E h y).gates=2*L+2*graphWireCount G ∧
    (mbqcReadoutLeaf G E h y).measurements=graphWireCount G+1 ∧
    (mbqcReadoutLeaf G E h y).outcomes=(mbqcRawLeaf G h).outcomes++[(2^n,y.val)] := by
  have hi : graphHistoryIndex G h*2^n+y.val < observedLeafCount (mbqcReadoutProgram G E) := by
    rw [mbqcReadoutProgram_leafCount]
    have hh := graphHistoryIndex_lt G h
    have hy := y.isLt
    have hp : 0 < 2^n := by positivity
    nlinarith
  refine ⟨hi,?_⟩
  have hc : graphSlotCount G (List.ofFn (fun t : Fin L => t))=graphWireCount G := by
    simp [graphSlotCount,List.map_ofFn,List.sum_ofFn,graphWireCount_eq_sum]
  obtain ⟨ho,ha,hq,hg,hm,hout⟩ := mbqcReadoutTailLeaf_fields G E h y
    (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  rw [hc] at hg hm
  simp only [mbqcReadoutLeaf_eq,mbqcRawLeaf_eq,graphPrependLeaf_operator,
    graphPrependLeaf_accepted,graphPrependLeaf_queries,graphPrependLeaf_gates,
    graphPrependLeaf_measurements,graphPrependLeaf_outcomes,ho,ha,hq,hg,hm,hout,
    graphFinalFrame,Matrix.mul_assoc,graphFreshGates,graphEdgeGates,List.length_ofFn]
  simp only [true_and,and_true]
  omega

/-- The finite index of a readout leaf corresponding to a graph history and a logical output
label. -/
def mbqcReadoutIndex {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (hy : GraphHistory G × Fin (2^n)) : Fin (observedLeafCount (mbqcReadoutProgram G E)) :=
  ⟨graphHistoryIndex G hy.1*2^n+hy.2.val,(mbqcReadoutLeaf_fields G E hy.1 hy.2).1⟩

/-- Graph histories paired with logical output labels are in bijection with the indices of all
readout leaves. -/
theorem mbqcReadoutIndex_bijective {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n))) :
    Function.Bijective (mbqcReadoutIndex G E) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,?_⟩
  · rintro ⟨h,y⟩ ⟨h',y'⟩ he
    have hv := congrArg Fin.val he
    change graphHistoryIndex G h*2^n+y.val=graphHistoryIndex G h'*2^n+y'.val at hv
    have hy := y.isLt
    have hy' := y'.isLt
    have hp : 0 < 2^n := by positivity
    have hi : graphHistoryIndex G h=graphHistoryIndex G h' := by nlinarith
    have hi' : y.val=y'.val := by rw [hi] at hv; omega
    exact Prod.ext (graphHistoryIndex_injective G hi) (Fin.ext hi')
  · simp only [Fintype.card_prod,Fintype.card_fin,graphHistory_card,mbqcReadoutProgram_leafCount]

/-- The observed leaf at `mbqcReadoutIndex G E (h,y)` is `mbqcReadoutLeaf G E h y`. -/
theorem mbqcReadoutLeaf_observedLeaf {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) :
    observedLeaf 1 (mbqcReadoutProgram G E) (mbqcReadoutIndex G E (h,y))=mbqcReadoutLeaf G E h y := by
  unfold observedLeaf mbqcReadoutLeaf
  rw [List.getD_eq_getElem _ _ (by
    rw [observedKrausLeaves_length]
    exact (mbqcReadoutLeaf_fields G E h y).1)]
  rfl

/-- Discard the non-output physical qubits according to the final graph layout and extract the
resulting logical operator. -/
def mbqcDiscard {n L : ℕ} (G : GraphWord n L) (B : Operator (2^(n+L))) : Operator (2^n) :=
  fun i j => graphDiscardReference n L 1 (graphLayoutFinal G) (TensorGate B (1 : Operator 1)) (i,0) (j,0)

/-- The raw logical branch is obtained by applying its physical Kraus operator to the embedded
input and then applying `mbqcDiscard`. -/
theorem mbqcRawBranch_discard {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G)
    (ρ : Operator (2^n)) :
    mbqcRawBranch G h ρ = mbqcDiscard G
      ((mbqcRawLeaf G h).operator*mbqcPhysicalInput G ρ*(mbqcRawLeaf G h).operatorᴴ) := by
  ext i j
  simp only [mbqcRawBranch,mbqcRawReference,mbqcPhysicalInput,mbqcDiscard,TensorGate,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]

/-- For a legal graph word, the trace mass of the physical projector for output `y` equals the
`y` diagonal entry after discarding non-output qubits. -/
theorem mbqcOutputLabel_mass {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (B : Operator (2^(n+L))) (y : Fin (2^n)) :
    Matrix.trace (Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y))*B*
      Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y)))=mbqcDiscard G B y y := by
  let lay := graphLayoutFinal G
  have hlay := (graph_layout_geometry G hlegal).1
  let coords := graphCoordinates lay hlay
  have hlabel (x : Reg n) (s : GraphSpectator lay → Bool) :
      mbqcOutputLabel G ((bitVecEquiv (n+L)) (coords.symm (x,s)))=(bitVecEquiv n) x := by
    have hc := congrArg Prod.fst (coords.apply_symm_apply (x,s))
    change (fun i => coords.symm (x,s) (lay i))=x at hc
    simp only [mbqcOutputLabel,Equiv.symm_apply_apply]
    exact congrArg (bitVecEquiv n) hc
  rw [mbqcDiscard,graphDiscardReference_coordinates n L 1 lay hlay]
  simp only [TensorGate,Matrix.kronecker_apply,Matrix.one_apply_eq,mul_one]
  simp only [Matrix.trace,Projector,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Finset.mem_filter,Finset.mem_univ,true_and,Matrix.diag_apply]
  rw [← (bitVecEquiv (n+L)).sum_comp,← coords.symm.sum_comp,Fintype.sum_prod_type]
  simp only [hlabel]
  rw [← (bitVecEquiv n).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,ite_mul,zero_mul,mul_ite,mul_zero,mul_one,one_mul]
  simp [coords]

/-- Embedding a density operator with `mbqcPhysicalInput` produces a density operator on the
physical register. -/
theorem mbqcPhysicalInput_density {n L : ℕ} (G : GraphWord n L) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) : IsDensityOperator (mbqcPhysicalInput G ρ) := by
  refine ⟨hρ.1.mul_mul_conjTranspose_same (graphInputFrame n L),?_⟩
  change Matrix.trace (graphInputFrame n L*ρ*(graphInputFrame n L)ᴴ)=1
  calc
    _ = Matrix.trace ((graphInputFrame n L)ᴴ*graphInputFrame n L*ρ) :=
      Matrix.trace_mul_cycle (graphInputFrame n L) ρ (graphInputFrame n L)ᴴ
    _ = 1 := by rw [graphInputFrame_isometry,Matrix.one_mul,hρ.2]

end Qatlib.Concepts.InstrumentCore.PatternCompile
