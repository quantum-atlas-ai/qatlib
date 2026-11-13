/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs

/-!
# Auxiliary laws for raw graph execution

This module constructs the recursive leaves of raw graph measurement tails and identifies them
with the leaves enumerated by the observed-circuit semantics. It proves exact counts and
resources and relates each raw operator to the corresponding operator with the final correction
applied.

The transfer and reference-system formulas retain the history-dependent Pauli frame, providing
the branch semantics needed for the measurement-based model [RaussendorfBriegel2000].

## Main statements

* `mbqcRawLeaf_resources`: exact gate, query, measurement, and message counts.
* `mbqcRawLeaf_correction`: the relation between raw and corrected branch operators.
* `mbqcRawReference_formula`: scaled framed-unitary conjugation with a reference system.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
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

/-- Construct the raw tail leaf for a fixed graph history, slot list, and initial Pauli frame by
following its recorded measurement outcomes. -/
def mbqcRawTailLeaf {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G) :
    List (Fin L) → PauliFrame n → ObservedKrausLeaf (2^(n+L))
  | [], _ => ⟨1,true,0,0,0,[]⟩
  | t::ts, F =>
    let rest := mbqcRawTailLeaf G h ts (graphFrameAdvance G h F t)
    match G t with
    | .inl (i,ζ) =>
      ((rest.prepend (graphPhysicalProjector n L (graphLayoutBefore G t i) (h.1 t))
        0 0 1 [(2,(boolEquivFin2 (h.1 t)).val)]).prepend
        (graphPhysicalH n L (graphLayoutBefore G t i)) 0 1 0 []).prepend
        (graphPhysicalPhase n L (graphLayoutBefore G t i)
          (if F.1 i then star ζ else ζ)) 0 1 0 []
    | .inr _ => rest

/-- The raw tail has `2^graphSlotCount G ts` leaves, independently of its initial Pauli frame. -/
theorem mbqcRawTail_leafCount {n L : ℕ} (G : GraphWord n L)
    (ts : List (Fin L)) (F : PauliFrame n) :
    observedLeafCount (mbqcRawTail G ts F) = 2^(graphSlotCount G ts) := by
  induction ts generalizing F with
  | nil => simp [mbqcRawTail, observedLeafCount, graphSlotCount]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      simp [mbqcRawTail, hg, observedLeafCount, ih, graphSlotCount, graphWireAt,
        pow_succ, pow_add, two_mul]
    | inr p => simp [mbqcRawTail, hg, ih, graphSlotCount, graphWireAt]

/-- The raw graph program has exactly `2^graphWireCount G` leaves. -/
theorem mbqcRawProgram_leafCount {n L : ℕ} (G : GraphWord n L) :
    observedLeafCount (mbqcRawProgram G) = 2^(graphWireCount G) := by
  have hc : graphSlotCount G (List.ofFn (fun t : Fin L => t)) = graphWireCount G := by
    simp [graphSlotCount, List.map_ofFn, List.sum_ofFn, graphWireCount_eq_sum]
  simp [mbqcRawProgram, graphPrepend_leafCount, mbqcRawTail_leafCount, hc]

/-- The Kraus-leaf enumeration of a raw tail selects `mbqcRawTailLeaf` at the index encoded by
the tail's history message. -/
theorem mbqcRawTailLeaf_get {n L : ℕ} (G : GraphWord n L)
    (h : GraphHistory G) (ts : List (Fin L)) (F : PauliFrame n) :
    (observedKrausLeaves 1 (mbqcRawTail G ts F))[graphBitsIndex (graphTailMessage G h ts)]?=
      some (mbqcRawTailLeaf G h ts F) := by
  induction ts generalizing F with
  | nil => rfl
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      have hm := graphMeasurementLeaf_get (graphPhysicalLabel n L (graphLayoutBefore G t i))
        (fun a => mbqcRawTail G ts (graphWireFrame F i (boolEquivFin2.symm a)))
        (h.1 t) (graphBitsIndex (graphTailMessage G h ts)) (2^(graphSlotCount G ts))
        (fun o => by rw [observedKrausLeaves_length, mbqcRawTail_leafCount])
        (by simpa [graphTailMessage_length] using! graphBitsIndex_lt (graphTailMessage G h ts))
        _ (by simpa using! ih (graphWireFrame F i (h.1 t)))
      have hmH := graphGateLeaf_get (graphPhysicalH n L (graphLayoutBefore G t i)) _ _ _ hm
      have hmP := graphGateLeaf_get (graphPhysicalPhase n L (graphLayoutBefore G t i)
        (if F.1 i then star ζ else ζ)) _ _ _ hmH
      have hmsg : graphTailMessage G h (t::ts) = h.1 t::graphTailMessage G h ts := by
        simp [graphTailMessage, graphWireAt, hg]
      rw [hmsg, graphBitsIndex_cons, graphTailMessage_length]
      simpa only [mbqcRawTail, mbqcRawTailLeaf, hg, graphFrameAdvance,
        graphPhysicalProjector] using! hmP
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hmsg : graphTailMessage G h (t::ts) = graphTailMessage G h ts := by
        simp [graphTailMessage, graphWireAt, hg]
      rw [hmsg]
      simpa only [mbqcRawTail, mbqcRawTailLeaf, hg, graphFrameAdvance] using!
        ih (graphCzFrame F i j)

/-- A raw program leaf is its full recursive tail leaf with the fresh-qubit and graph-edge gates
prepended. -/
theorem mbqcRawLeaf_eq {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G) :
    mbqcRawLeaf G h = graphPrependLeaf (graphFreshGates n L)
      (graphPrependLeaf (graphEdgeGates G)
        (mbqcRawTailLeaf G h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))) := by
  have ht := mbqcRawTailLeaf_get G h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  have he := graphPrependLeaf_get (graphFreshGates n L) _ _ _
    (graphPrependLeaf_get (graphEdgeGates G) _ _ _ ht)
  rw [mbqcRawLeaf, List.getD_eq_getElem?_getD]
  change ((observedKrausLeaves 1 (graphPrepend (graphFreshGates n L)
    (graphPrepend (graphEdgeGates G) _)))[graphHistoryIndex G h]?).getD _ = _
  change (observedKrausLeaves 1 (graphPrepend _ (graphPrepend _ _)))[graphBitsIndex (graphTailMessage G h (List.ofFn (fun t : Fin L => t)))]?.getD _ = _
  rw [he]
  rfl

/-- Every raw tail leaf accepts, makes no queries, and uses two gates and one measurement per
counted graph slot. -/
theorem mbqcRawTailLeaf_resources {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G)
    (ts : List (Fin L)) (F : PauliFrame n) :
    (mbqcRawTailLeaf G h ts F).accepted=true ∧
    (mbqcRawTailLeaf G h ts F).queries=0 ∧
    (mbqcRawTailLeaf G h ts F).gates=2*graphSlotCount G ts ∧
    (mbqcRawTailLeaf G h ts F).measurements=graphSlotCount G ts := by
  induction ts generalizing F with
  | nil => simp [mbqcRawTailLeaf, graphSlotCount]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,ζ⟩ := p
      obtain ⟨ha,hq,hgates,hm⟩ := ih (graphWireFrame F i (h.1 t))
      have hc : graphSlotCount G (t::ts)=graphSlotCount G ts+1 := by
        simp [graphSlotCount, graphWireAt, hg, Nat.add_comm]
      simp only [mbqcRawTailLeaf, hg, graphFrameAdvance, ObservedKrausLeaf.prepend,
        ha, hq, hgates, hm, hc, Nat.add_zero]
      exact ⟨trivial,trivial,by omega,trivial⟩
    | inr p =>
      obtain ⟨i,j⟩ := p
      have hc : graphSlotCount G (t::ts)=graphSlotCount G ts := by
        simp [graphSlotCount, graphWireAt, hg]
      simpa only [mbqcRawTailLeaf, hg, graphFrameAdvance, hc] using! ih (graphCzFrame F i j)

/-- Every raw graph leaf accepts and makes no queries, with `2*L + 2*graphWireCount G` gates and
`graphWireCount G` measurements and message bits. -/
theorem mbqcRawLeaf_resources {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G) :
    (mbqcRawLeaf G h).accepted=true ∧ (mbqcRawLeaf G h).queries=0 ∧
    (mbqcRawLeaf G h).gates=2*L+2*graphWireCount G ∧
    (mbqcRawLeaf G h).measurements=graphWireCount G ∧
    (graphMessage G h).length=graphWireCount G := by
  have hc : graphSlotCount G (List.ofFn (fun t : Fin L => t))=graphWireCount G := by
    simp [graphSlotCount,List.map_ofFn,List.sum_ofFn,graphWireCount_eq_sum]
  obtain ⟨ha,hq,hg,hm⟩ := mbqcRawTailLeaf_resources G h
    (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  rw [hc] at hg hm
  simp only [mbqcRawLeaf_eq, graphPrependLeaf_accepted, graphPrependLeaf_queries,
    graphPrependLeaf_gates, graphPrependLeaf_measurements, ha,hq,hg,hm,
    graphFreshGates,graphEdgeGates,List.length_ofFn,graphMessage_length]
  exact ⟨trivial,trivial,by omega,trivial,trivial⟩

/-- The corrected tail operator is the raw tail operator preceded by the correction gates for
the frame reached after processing the slots. -/
theorem mbqcRawTailLeaf_correction {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G)
    (ts : List (Fin L)) (F : PauliFrame n) :
    (graphTailLeaf true G h ts F).operator =
      graphGateProduct (graphCorrectionGates G (ts.foldl (graphFrameAdvance G h) F))*
        (mbqcRawTailLeaf G h ts F).operator := by
  induction ts generalizing F with
  | nil => simp [graphTailLeaf,graphPrependLeaf_operator,mbqcRawTailLeaf]
  | cons t ts ih =>
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      simp only [graphTailLeaf,mbqcRawTailLeaf,hg,if_true,graphFrameAdvance,
        ObservedKrausLeaf.prepend,List.foldl_cons,ih,Matrix.mul_assoc]
    | inr p =>
      obtain ⟨i,j⟩ := p
      simpa only [graphTailLeaf,mbqcRawTailLeaf,hg,if_true,graphFrameAdvance,
        List.foldl_cons] using! ih (graphCzFrame F i j)

/-- The corrected graph-program operator is the raw leaf operator preceded by the correction
gates for the final Pauli frame. -/
theorem mbqcRawLeaf_correction {n L : ℕ} (G : GraphWord n L) (h : GraphHistory G) :
    (graphProgramLeaf true G h).operator =
      graphGateProduct (graphCorrectionGates G (graphFinalFrame G h))*(mbqcRawLeaf G h).operator := by
  simp only [graphProgramLeaf_eq,if_true,mbqcRawLeaf_eq,graphPrependLeaf_operator,
    mbqcRawTailLeaf_correction,graphFinalFrame,Matrix.mul_assoc]

/-- The ordered graph product of a list of unitary operators is unitary. -/
private theorem graphGateProduct_unitary {D : ℕ} (Us : List (Operator D))
    (hUs : ∀ U ∈ Us, U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    graphGateProduct Us ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  induction Us with
  | nil => exact Submonoid.one_mem _
  | cons U Us ih =>
    exact Submonoid.mul_mem _ (ih (fun V hV => hUs V (List.mem_cons_of_mem U hV)))
      (hUs U List.mem_cons_self)

/-- For a legal graph word, the raw leaf applied to the input embedding is a row lift of the
logical tail with its final Pauli frame and history-dependent envelope. -/
theorem mbqcRawLeaf_columns {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (h : GraphHistory G) :
    let ts := List.ofFn (fun t : Fin L => t)
    let f₀ : Reg (n+L) → ℂ := fun _ => ((Real.sqrt 2 : ℂ)⁻¹)^L
    let f := graphTailEnvelope G h ts f₀
    let A := pauliFrameGateB (graphFinalFrame G h)*
      (graphLogicalTailB G h ts (zeroPauliFrame n)*graphInitialLogicalRows n)
    (mbqcRawLeaf G h).operator*graphInputFrame n L = graphRowLift (graphLayoutFinal G) f A := by
  intro ts f₀ f A
  have ht := graphTail_actual_transfer G hlegal h ts [] (by simp [ts])
    (zeroPauliFrame n) f₀ (by intro i z b; rfl) (by intro t ht z b; rfl)
    (graphInitialLogicalRows n)
  have hphys : (graphProgramLeaf true G h).operator*graphInputFrame n L=
      graphRowLift (graphLayoutFinal G) f
        (graphLogicalTailB G h ts (zeroPauliFrame n)*graphInitialLogicalRows n) := by
    have hleaf := ((preentangled_graph_actual_leaf_retiming n L G hlegal).2.2 h).1
    rw [← hleaf,graphProgramLeaf_eq]
    simp only [Bool.false_eq_true,if_false,graphPrependLeaf_operator,Matrix.mul_assoc]
    rw [graphFreshPreparation]
    exact ht.1
  let C := graphGateProduct (graphCorrectionGates G (graphFinalFrame G h))
  have hC : Cᴴ*C=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff').mp
        (graphGateProduct_unitary _ (graphCorrectionGates_unitary G _))
  have hF : (pauliFrameGate n (graphFinalFrame G h))ᴴ*
      pauliFrameGate n (graphFinalFrame G h)=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff').mp (pauliFrameGate_unitary n _)
  have hlift : C*graphRowLift (graphLayoutFinal G) f A=
      graphRowLift (graphLayoutFinal G) f
        (graphLogicalTailB G h ts (zeroPauliFrame n)*graphInitialLogicalRows n) := by
    rw [graphCorrection_rowLift G (graph_layout_geometry G hlegal).1 _ f ht.2.1 A]
    dsimp only [A]
    rw [graphPauliFrameB_eq,← Matrix.mul_assoc,← teleportRelabelGate_mul,hF,
      teleportRelabelGate_one,Matrix.one_mul]
  rw [mbqcRawLeaf_correction] at hphys
  have he : C*((mbqcRawLeaf G h).operator*graphInputFrame n L)=
      C*graphRowLift (graphLayoutFinal G) f A := by
    simpa only [C,Matrix.mul_assoc] using! hphys.trans hlift.symm
  have he' := congrArg (fun B => Cᴴ*B) he
  simpa only [← Matrix.mul_assoc,hC,Matrix.one_mul] using! he'

/-- For a legal graph word and any reference system, a raw branch is scaled conjugation by the
framed logical network matrix tensored with the reference identity. -/
theorem mbqcRawReference_formula {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (h : GraphHistory G) (R : ℕ)
    (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :
    mbqcRawReference G h R X=(1/2 : ℂ)^(graphWireCount G) •
      (TensorGate (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G))
        (1 : Operator R)*X*
        (TensorGate (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G))
          (1 : Operator R))ᴴ) := by
  let ts := List.ofFn (fun t : Fin L => t)
  let f₀ : Reg (n+L) → ℂ := fun _ => ((Real.sqrt 2 : ℂ)⁻¹)^L
  let f := graphTailEnvelope G h ts f₀
  let A := pauliFrameGateB (graphFinalFrame G h)*
    (graphLogicalTailB G h ts (zeroPauliFrame n)*graphInitialLogicalRows n)
  have ht := graphTail_actual_transfer G hlegal h ts [] (by simp [ts])
    (zeroPauliFrame n) f₀ (by intro i z b; rfl) (by intro t ht z b; rfl)
    (graphInitialLogicalRows n)
  have hphys := mbqcRawLeaf_columns G hlegal h
  have hmass : graphEnvelopeMass n f=(1/2 : ℂ)^(graphWireCount G) := by
    have he := ht.2.2
    have hcount : graphSlotCount G ts=graphWireCount G := by
      simp [ts,graphSlotCount,List.map_ofFn,List.sum_ofFn,graphWireCount_eq_sum]
    rw [hcount,graphEnvelopeMass_initial,mul_one] at he
    exact he
  obtain ⟨c,hc,he⟩ := graphLogicalTailB_correct n L G hlegal h ts (zeroPauliFrame n)
  have hzero : pauliFrameGateB (zeroPauliFrame n)=1 := by
    rw [graphPauliFrameB_eq,zeroPauliFrame_gate,teleportRelabelGate_one]
  rw [hzero,Matrix.mul_one] at he
  have hA : (fun u j => A ((bitVecEquiv n).symm u) j)=
      c • (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G)) := by
    have hB : pauliFrameGateB (graphFinalFrame G h)*graphLogicalTailB G h ts (zeroPauliFrame n)=
        c • relabelGate (bitVecEquiv n).symm
          (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G)) := by
      rw [he,graphPauliFrameB_eq,Matrix.mul_smul,← teleportRelabelGate_mul]
      simp only [ts,List.map_ofFn,Function.comp_def]
    ext u j
    change (pauliFrameGateB (graphFinalFrame G h)*
      (graphLogicalTailB G h ts (zeroPauliFrame n)*graphInitialLogicalRows n))
        ((bitVecEquiv n).symm u) j=_
    rw [← Matrix.mul_assoc,graphLogicalRows_init_mul,hB]
    simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
      Matrix.smul_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  have hk : TensorGate (mbqcRawLeaf G h).operator (1 : Operator R)*
      ((graphInputFrame n L) ⊗ₖ (1 : Operator R))=
        (graphRowLift (graphLayoutFinal G) f A) ⊗ₖ (1 : Operator R) := by
    rw [TensorGate,← Matrix.mul_kronecker_mul,Matrix.one_mul,hphys]
  unfold mbqcRawReference
  (try dsimp only)
  have hgroup : TensorGate (mbqcRawLeaf G h).operator (1 : Operator R)*
      (((graphInputFrame n L) ⊗ₖ (1 : Operator R))*X*
        ((graphInputFrame n L) ⊗ₖ (1 : Operator R))ᴴ)*
      (TensorGate (mbqcRawLeaf G h).operator (1 : Operator R))ᴴ=
      ((graphRowLift (graphLayoutFinal G) f A) ⊗ₖ (1 : Operator R))*X*
        ((graphRowLift (graphLayoutFinal G) f A) ⊗ₖ (1 : Operator R))ᴴ := by
    rw [← hk]
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hgroup,graphDiscardReference_rowLift n L (2^n) R (graphLayoutFinal G)
    (graph_layout_geometry G hlegal).1 f ht.2.1 A X,hmass,hA]
  have htensor : (c • (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G)))
      ⊗ₖ (1 : Operator R) = c • TensorGate
        (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G)) (1 : Operator R) := by
    ext p q
    simp only [Matrix.kroneckerMap,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,TensorGate]
    ring
  rw [htensor,graphConj_phase c hc]

end Qatlib.Concepts.InstrumentCore.PatternCompile
