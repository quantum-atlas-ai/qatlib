/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid


set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Actual finite constructor/output-word/readout composition. Dependent
continuations preserve complete paths and unnormalized quantum branches.
Known-state reset is an explicit complete Kraus operation with its outcomes
forgotten. Typed known gates and given input-query modes compile to the same
matrix word. Sequential reset/readout derives the IID Born product and its
joint law with the actual constructor, retaining every bad description path.

The model has one fixed finite dimension and finite output words in a common
basis. It does not prove an arbitrary external constructor has this normal
form, pad variable-width frames, truncate expected budgets, synthesize control
for an unprovided oracle, or implement the outer reconstruction/majority loop.
Known operations are explicit CP maps, not a complete primitive gate-cost
implementation. Original mathematical and complexity obligations remain. -/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Continue from each full classical record, preserving its unnormalized
quantum branch. The continuation is independent of hidden oracle parameters. -/
def bind {D R : ℕ} : (P : Program D R) → (Path P → Program D R) → Program D R
  | .halt, F => F ()
  | .query mode next, F => .query mode (bind next F)
  | .measure I next, F => .measure I (fun o => bind (next o) (fun p => F ⟨o,p⟩))
  | .support a next, F => .support a (fun o => bind (next o) (fun p => F ⟨o,p⟩))

/-- Construction for join Path in the output readout model. -/
def joinPath {D R : ℕ} : (P : Program D R) → (F : Path P → Program D R) →
    (p : Path P) → Path (F p) → Path (bind P F)
  | .halt, _, (), q => q
  | .query _ next, F, p, q => joinPath next F p q
  | .measure _ next, F, ⟨o,p⟩, q => ⟨o,joinPath (next o) (fun p => F ⟨o,p⟩) p q⟩
  | .support _ next, F, ⟨o,p⟩, q => ⟨o,joinPath (next o) (fun p => F ⟨o,p⟩) p q⟩

/-- Construction for split Path in the output readout model. -/
def splitPath {D R : ℕ} : (P : Program D R) → (F : Path P → Program D R) →
    Path (bind P F) → (p : Path P) × Path (F p)
  | .halt, _, q => ⟨(),q⟩
  | .query _ next, F, q => splitPath next F q
  | .measure _ next, F, ⟨o,q⟩ =>
    let pq := splitPath (next o) (fun p => F ⟨o,p⟩) q
    ⟨⟨o,pq.1⟩,pq.2⟩
  | .support _ next, F, ⟨o,q⟩ =>
    let pq := splitPath (next o) (fun p => F ⟨o,p⟩) q
    ⟨⟨o,pq.1⟩,pq.2⟩

/-- The finite protocol identity or bound `split_join` holds under exactly the displayed hypotheses. -/
theorem split_join {D R : ℕ} (P : Program D R) (F : Path P → Program D R)
    (p : Path P) (q : Path (F p)) :
    splitPath P F (joinPath P F p q)=⟨p,q⟩ := by
  induction P with
  | halt => cases p; rfl
  | query mode next ih => exact ih F p q
  | measure I next ih =>
    rcases p with ⟨o,p⟩
    simp only [joinPath,splitPath]
    rw [ih o (fun p => F ⟨o,p⟩) p q]
  | support a next ih =>
    rcases p with ⟨o,p⟩
    simp only [joinPath,splitPath]
    rw [ih o (fun p => F ⟨o,p⟩) p q]

/-- The finite protocol identity or bound `join_split` holds under exactly the displayed hypotheses. -/
theorem join_split {D R : ℕ} (P : Program D R) (F : Path P → Program D R)
    (q : Path (bind P F)) :
    joinPath P F (splitPath P F q).1 (splitPath P F q).2=q := by
  induction P with
  | halt => rfl
  | query mode next ih => exact ih F q
  | measure I next ih =>
    rcases q with ⟨o,q⟩
    dsimp only [splitPath,joinPath]
    exact congrArg (fun q' : Path (bind (next o) (fun p => F ⟨o,p⟩)) =>
      (⟨o,q'⟩ : Path (bind (.measure I next) F))) (ih o _ q)
  | support a next ih =>
    rcases q with ⟨o,q⟩
    dsimp only [splitPath,joinPath]
    exact congrArg (fun q' : Path (bind (next o) (fun p => F ⟨o,p⟩)) =>
      (⟨o,q'⟩ : Path (bind (.support a next) F))) (ih o _ q)

/-- Construction for bind Path Equiv in the output readout model. -/
def bindPathEquiv {D R : ℕ} (P : Program D R) (F : Path P → Program D R) :
    ((p : Path P) × Path (F p)) ≃ Path (bind P F) where
  toFun pq := joinPath P F pq.1 pq.2
  invFun := splitPath P F
  left_inv := by intro pq; exact split_join P F pq.1 pq.2
  right_inv := join_split P F

/-- The finite protocol map `pathMap_bind` preserves the stated branch semantics or positivity property. -/
theorem pathMap_bind {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (F : Path P → Program D R) (p : Path P) (q : Path (F p)) :
    pathMap O S (bind P F) (joinPath P F p q)=
      (pathMap O S (F p) q).comp (pathMap O S P p) := by
  induction P with
  | halt => cases p; rfl
  | query mode next ih =>
    change (pathMap O S (bind next F) (joinPath next F p q)).comp (O mode).map=_
    rw [ih]
    rfl
  | measure I next ih =>
    rcases p with ⟨o,p⟩
    change (pathMap O S (bind (next o) (fun p => F ⟨o,p⟩))
      (joinPath (next o) (fun p => F ⟨o,p⟩) p q)).comp (I.branch o)=_
    rw [ih o]
    rfl
  | support a next ih =>
    rcases p with ⟨o,p⟩
    change (pathMap O S (bind (next o) (fun p => F ⟨o,p⟩))
      (joinPath (next o) (fun p => F ⟨o,p⟩) p q)).comp _=_
    rw [ih o]
    rfl

/-- The finite protocol identity or bound `pathCharge_bind` holds under exactly the displayed hypotheses. -/
theorem pathCharge_bind {D R : ℕ} (P : Program D R) (F : Path P → Program D R)
    (p : Path P) (q : Path (F p)) :
    pathCharge (bind P F) (joinPath P F p q)=
      ((pathCharge P p).1+(pathCharge (F p) q).1,
       (pathCharge P p).2+(pathCharge (F p) q).2) := by
  induction P with
  | halt => cases p; simp [bind,joinPath,pathCharge]
  | query mode next ih =>
    simp only [bind,joinPath,pathCharge,ih]
    congr 1; omega
  | measure I next ih => rcases p with ⟨o,p⟩; exact ih o (fun p => F ⟨o,p⟩) p q
  | support a next ih =>
    rcases p with ⟨o,p⟩
    simp only [bind,joinPath,pathCharge,ih]
    congr 1; omega

/-- Construction for reset Kraus in the output readout model. -/
private def resetKraus {D : ℕ} (r k : Fin D) : Operator D :=
  fun i j => if i=r then if j=k then 1 else 0 else 0

/-- The finite protocol identity or bound `reset_complete` holds under exactly the displayed hypotheses. -/
private theorem reset_complete {D : ℕ} (r : Fin D) :
    (∑ k : Fin D,(resetKraus r k).conjTranspose*resetKraus r k)=1 := by
  ext i j
  simp [Matrix.sum_apply,resetKraus,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]

/-- Construction for reset Fine in the output readout model. -/
private def resetFine {D : ℕ} (r : Fin D) : Instrument (Fin D) D D :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus (resetKraus r) (reset_complete r)

/-- Kraus outcomes are erased internally, not revealed as extra algorithmic
information. The full constructor record stays in Program.bind's path. -/
def resetChannel {D : ℕ} (r : Fin D) : QuantumChannel D D := (resetFine r).forget

/-- Construction for reset Instrument in the output readout model. -/
def resetInstrument {D : ℕ} (r : Fin D) : Instrument (Fin 1) D D :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofBranches (fun _ => (resetChannel r).map)
    (fun _ => (resetChannel r).completelyPositive) (by
      intro ρ
      simpa only [Fin.sum_univ_one] using (resetChannel r).tracePreserving ρ)

/-- The finite protocol identity or bound `resetChannel_apply` holds under exactly the displayed hypotheses. -/
theorem resetChannel_apply {D : ℕ} (r : Fin D) (ρ : Operator D) :
    (resetChannel r).map ρ=(Matrix.trace ρ) • outerProduct (Qatlib.Foundations.PureStateMath.Ket r) := by
  ext i j
  by_cases hi : i=r <;> by_cases hj : j=r <;>
    simp [resetChannel,resetFine,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus_branch,
      Matrix.sum_apply,resetKraus,Matrix.mul_apply,Matrix.conjTranspose_apply,
      outerProduct,Qatlib.Foundations.PureStateMath.Ket,Matrix.trace,hi,hj]

/-- Exact complex branch factorization, including zero or subnormalized
constructor branches; no probabilistic independence is supplied as input. -/
theorem reset_follow_trace {D : ℕ} (r : Fin D) (ρ : Operator D)
    (L : Operator D →ₗ[ℂ] Operator D) :
    Matrix.trace (L ((resetChannel r).map ρ))=
      Matrix.trace ρ*Matrix.trace (L (outerProduct (Qatlib.Foundations.PureStateMath.Ket r))) := by
  rw [resetChannel_apply,map_smul,Matrix.trace_smul,smul_eq_mul]

/-- A returned word may use known gates and the given controlled input-query
modes. Its syntax has no hidden-matrix parameter. -/
inductive OutputGate (D : ℕ) where
  | known (U : Operator D) (hU : U∈Matrix.unitaryGroup (Fin D) ℂ)
  | query (mode : Bool)

/-- Construction for gate Matrix in the output readout model. -/
def gateMatrix {D : ℕ} (O : Bool → Operator D) : OutputGate D → Operator D
  | .known U _ => U
  | .query mode => O mode

/-- Construction for word Matrix in the output readout model. -/
def wordMatrix {D : ℕ} (O : Bool → Operator D) : List (OutputGate D) → Operator D
  | [] => 1
  | g::gs => wordMatrix O gs*gateMatrix O g

/-- Construction for word Queries in the output readout model. -/
def wordQueries {D : ℕ} : List (OutputGate D) → ℕ
  | [] => 0
  | .known _ _::gs => wordQueries gs
  | .query _::gs => wordQueries gs+1

/-- Construction for word Program in the output readout model. -/
def wordProgram {D : ℕ} (R : ℕ) : List (OutputGate D) → Program D R
  | [] => .halt
  | .known U hU::gs => .measure (unitaryInstrument U hU) (fun _ => wordProgram R gs)
  | .query mode::gs => .query mode (wordProgram R gs)

/-- Construction for word Path in the output readout model. -/
def wordPath {D : ℕ} (R : ℕ) : (gs : List (OutputGate D)) → Path (wordProgram R gs)
  | [] => ()
  | .known _ _::gs => ⟨0,wordPath R gs⟩
  | .query _::gs => wordPath R gs

/-- The finite protocol identity or bound `wordPath_unique` holds under exactly the displayed hypotheses. -/
theorem wordPath_unique {D : ℕ} (R : ℕ) (gs : List (OutputGate D))
    (p : Path (wordProgram R gs)) : p=wordPath R gs := by
  induction gs with
  | nil => cases p; rfl
  | cons g gs ih =>
    cases g with
    | known U hU =>
      rcases p with ⟨o,p⟩
      have ho : o=(0 : Fin 1) := Subsingleton.elim _ _
      subst o
      exact congrArg (Sigma.mk 0) (ih p)
    | query mode => exact ih p

/-- Construction for unitary Channel in the output readout model. -/
def unitaryChannel {D : ℕ} (U : Operator D) (hU : U∈Matrix.unitaryGroup (Fin D) ℂ) :
    QuantumChannel D D where
  map := conjBranch U
  completelyPositive := completelyPositive_conjBranch U
  tracePreserving := trace_conjBranch_unitary U hU

/-- The finite protocol identity or bound `wordProgram_map` holds under exactly the displayed hypotheses. -/
theorem wordProgram_map {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (gs : List (OutputGate D)) :
    pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S
      (wordProgram R gs) (wordPath R gs)=conjBranch (wordMatrix O gs) := by
  induction gs with
  | nil =>
    apply LinearMap.ext
    intro ρ
    simp [wordProgram,wordPath,pathMap,wordMatrix]
  | cons g gs ih =>
    cases g with
    | known U hU =>
      change (pathMap _ S (wordProgram R gs) (wordPath R gs)).comp (conjBranch U)=_
      rw [ih,conjBranch_comp]
      rfl
    | query mode =>
      change (pathMap _ S (wordProgram R gs) (wordPath R gs)).comp (conjBranch (O mode))=_
      rw [ih,conjBranch_comp]
      rfl

/-- The finite protocol identity or bound `wordProgram_charge` holds under exactly the displayed hypotheses. -/
theorem wordProgram_charge {D : ℕ} (R : ℕ) (gs : List (OutputGate D)) :
    pathCharge (wordProgram R gs) (wordPath R gs)=(wordQueries gs,0) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | known U hU => exact ih
    | query mode => simp only [wordProgram,wordPath,pathCharge,wordQueries,ih]

/-- The finite protocol identity or bound `wordMatrix_unitary` holds under exactly the displayed hypotheses. -/
theorem wordMatrix_unitary {D : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (gs : List (OutputGate D)) :
    wordMatrix O gs∈Matrix.unitaryGroup (Fin D) ℂ := by
  induction gs with
  | nil => exact (Matrix.unitaryGroup (Fin D) ℂ).one_mem
  | cons g gs ih =>
    apply (Matrix.unitaryGroup (Fin D) ℂ).mul_mem ih
    cases g with
    | known U hU => exact hU
    | query mode => exact hO mode

/-- Construction for basis Readout in the output readout model. -/
private def basisReadout {D : ℕ} (R : ℕ) : Program D R :=
  .measure projectiveInstrument (fun _ => .halt)

/-- Construction for readout Program in the output readout model. -/
def readoutProgram {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) : Program D R :=
  .measure (resetInstrument r) (fun _ => bind (wordProgram R gs) (fun _ => basisReadout R))

/-- Construction for readout Path in the output readout model. -/
def readoutPath {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) (b : Fin D) :
    Path (readoutProgram R r gs) :=
  ⟨0,joinPath (wordProgram R gs) (fun _ => basisReadout R) (wordPath R gs) ⟨b,()⟩⟩

/-- The finite protocol identity or bound `readoutProgram_map` holds under exactly the displayed hypotheses. -/
theorem readoutProgram_map {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (r : Fin D) (gs : List (OutputGate D)) (b : Fin D) :
    pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S
      (readoutProgram R r gs) (readoutPath R r gs b)=
      ((projectiveInstrument.branch b).comp (conjBranch (wordMatrix O gs))).comp (resetChannel r).map := by
  change (pathMap _ S (bind (wordProgram R gs) (fun _ => basisReadout R))
    (joinPath (wordProgram R gs) (fun _ => basisReadout R) (wordPath R gs) ⟨b,()⟩)).comp (resetChannel r).map=_
  rw [pathMap_bind,wordProgram_map]
  rfl

/-- The finite protocol identity or bound `readoutProgram_charge` holds under exactly the displayed hypotheses. -/
theorem readoutProgram_charge {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) (b : Fin D) :
    pathCharge (readoutProgram R r gs) (readoutPath R r gs b)=(wordQueries gs,0) := by
  change pathCharge (bind (wordProgram R gs) (fun _ => basisReadout R))
    (joinPath (wordProgram R gs) (fun _ => basisReadout R) (wordPath R gs) ⟨b,()⟩)=_
  rw [pathCharge_bind,wordProgram_charge]
  simp [basisReadout,pathCharge]

/-- The finite protocol identity or bound `measured_entry_trace` holds under exactly the displayed hypotheses. -/
private theorem measured_entry_trace {D : ℕ} (U : Operator D) (r b : Fin D) :
    Matrix.trace (projectiveInstrument.branch b (conjBranch U (outerProduct (Qatlib.Foundations.PureStateMath.Ket r))))=
      (Complex.normSq (U b r) : ℂ) := by
  change Matrix.trace (conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector ({b} : Finset (Fin D)))
    (conjBranch U (outerProduct (Qatlib.Foundations.PureStateMath.Ket r))))=_
  rw [conjBranch_outerProduct,conjBranch_projector_apply,Matrix.trace_diagonal]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,outerProduct,Matrix.of_apply]
  have he : (U *ᵥ Qatlib.Foundations.PureStateMath.Ket r) b=U b r := by simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  rw [he,Complex.normSq_eq_conj_mul_self]
  ring

/-- Born mass for the actual reset/word/measurement path. Every complex
unnormalized constructor residue is retained through its exact trace. -/
theorem readoutProgram_trace {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (r : Fin D) (gs : List (OutputGate D)) (b : Fin D) (ρ : Operator D) :
    Matrix.trace (pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S
      (readoutProgram R r gs) (readoutPath R r gs b) ρ)=
      Matrix.trace ρ*(Complex.normSq (wordMatrix O gs b r) : ℂ) := by
  rw [readoutProgram_map]
  change Matrix.trace (((projectiveInstrument.branch b).comp (conjBranch (wordMatrix O gs)))
    ((resetChannel r).map ρ))=_
  rw [reset_follow_trace]
  change Matrix.trace ρ*Matrix.trace (projectiveInstrument.branch b
    (conjBranch (wordMatrix O gs) (outerProduct (Qatlib.Foundations.PureStateMath.Ket r))))=_
  rw [measured_entry_trace]

/-- Construction for readout Outcome in the output readout model. -/
def readoutOutcome {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D))
    (p : Path (readoutProgram R r gs)) : Fin D :=
  (splitPath (wordProgram R gs) (fun _ => basisReadout R) p.2).2.1

/-- The finite protocol identity or bound `readoutOutcome_readoutPath` holds under exactly the displayed hypotheses. -/
theorem readoutOutcome_readoutPath {D : ℕ} (R : ℕ) (r : Fin D)
    (gs : List (OutputGate D)) (b : Fin D) :
    readoutOutcome R r gs (readoutPath R r gs b)=b := by
  unfold readoutOutcome readoutPath
  rw [split_join]

/-- The finite protocol identity or bound `readoutPath_readoutOutcome` holds under exactly the displayed hypotheses. -/
theorem readoutPath_readoutOutcome {D : ℕ} (R : ℕ) (r : Fin D)
    (gs : List (OutputGate D)) (p : Path (readoutProgram R r gs)) :
    readoutPath R r gs (readoutOutcome R r gs p)=p := by
  rcases p with ⟨o,p⟩
  have ho : o=(0 : Fin 1) := Subsingleton.elim _ _
  subst o
  have hh := join_split (wordProgram R gs) (fun _ => basisReadout R) p
  rcases he : splitPath (wordProgram R gs) (fun _ => basisReadout R) p with ⟨w,b,u⟩
  cases u
  simp only [he] at hh
  rw [wordPath_unique R gs w] at hh
  simpa only [readoutPath,readoutOutcome,he] using
    congrArg (fun q : Path (bind (wordProgram R gs) (fun _ => basisReadout R)) =>
      (⟨0,q⟩ : Path (readoutProgram R r gs))) hh

/-- Construction for readout Path Equiv in the output readout model. -/
def readoutPathEquiv {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) :
    Fin D ≃ Path (readoutProgram R r gs) where
  toFun := readoutPath R r gs
  invFun := readoutOutcome R r gs
  left_inv := readoutOutcome_readoutPath R r gs
  right_inv := readoutPath_readoutOutcome R r gs

/-- The constructor law is now the actual first program's law, not an
independently supplied random-description distribution. Bad paths remain. -/
theorem constructor_readout_trace {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (r : Path P → Fin D)
    (p : Path P) (b : Fin D) (ρ : Operator D) :
    Matrix.trace (pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => readoutProgram R (r p) (words p)))
      (joinPath P (fun p => readoutProgram R (r p) (words p)) p
        (readoutPath R (r p) (words p) b)) ρ)=
      Matrix.trace (pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S P p ρ)*
        (Complex.normSq (wordMatrix O (words p) b (r p)) : ℂ) := by
  rw [pathMap_bind]
  exact readoutProgram_trace O hO S (r p) (words p) b _

/-- Construction for sample Law in the output readout model. -/
def sampleLaw {D : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (r : Fin D)
    (gs : List (OutputGate D)) : FinDist (Fin D) where
  prob b := Complex.normSq (wordMatrix O gs b r)
  nonneg b := Complex.normSq_nonneg _
  sum_one := by
    have hh := sum_normSq_mulVec_of_mem_unitaryGroup (wordMatrix_unitary O hO gs) (Qatlib.Foundations.PureStateMath.Ket r)
    have he (b : Fin D) : (wordMatrix O gs *ᵥ Qatlib.Foundations.PureStateMath.Ket r) b=wordMatrix O gs b r := by
      simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
    simp_rw [he] at hh
    simpa [Qatlib.Foundations.PureStateMath.Ket] using hh

/-- Construction for repeat Readout in the output readout model. -/
def repeatReadout {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) : ℕ → Program D R
  | 0 => .halt
  | n+1 => bind (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)

/-- Construction for repeat Path in the output readout model. -/
def repeatPath {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) :
    (n : ℕ) → (Fin n → Fin D) → Path (repeatReadout R r gs n)
  | 0, _ => ()
  | n+1, ω => joinPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)
      (readoutPath R r gs (ω 0)) (repeatPath R r gs n (fun i => ω i.succ))

/-- This product is derived from sequential reset/word/readout CP maps.
No IID distribution or independence certificate is supplied. -/
theorem repeatReadout_trace {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (r : Fin D) (gs : List (OutputGate D)) (n : ℕ) (ω : Fin n → Fin D) (ρ : Operator D) :
    Matrix.trace (pathMap (fun mode => unitaryChannel (O mode) (hO mode)) S
      (repeatReadout R r gs n) (repeatPath R r gs n ω) ρ)=
      Matrix.trace ρ*∏ i : Fin n,((sampleLaw O hO r gs).prob (ω i) : ℂ) := by
  induction n generalizing ρ with
  | zero => simp [repeatReadout,repeatPath,pathMap]
  | succ n ih =>
    change Matrix.trace (pathMap _ S (bind (readoutProgram R r gs) (fun _ => repeatReadout R r gs n))
      (joinPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)
        (readoutPath R r gs (ω 0)) (repeatPath R r gs n (fun i => ω i.succ))) ρ)=_
    rw [pathMap_bind]
    change Matrix.trace (pathMap _ S (repeatReadout R r gs n)
      (repeatPath R r gs n (fun i => ω i.succ))
      (pathMap _ S (readoutProgram R r gs) (readoutPath R r gs (ω 0)) ρ))=_
    rw [ih,readoutProgram_trace,Fin.prod_univ_succ]
    simp only [sampleLaw,mul_assoc]

/-- The actual finite repeated protocol satisfies `repeatReadout_charge` without conditioning away failure records. -/
theorem repeatReadout_charge {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D))
    (n : ℕ) (ω : Fin n → Fin D) :
    pathCharge (repeatReadout R r gs n) (repeatPath R r gs n ω)=(n*wordQueries gs,0) := by
  induction n with
  | zero => simp [repeatReadout,repeatPath,pathCharge]
  | succ n ih =>
    change pathCharge (bind (readoutProgram R r gs) (fun _ => repeatReadout R r gs n))
      (joinPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)
        (readoutPath R r gs (ω 0)) (repeatPath R r gs n (fun i => ω i.succ)))=_
    rw [pathCharge_bind,readoutProgram_charge,ih]
    simp only [Nat.succ_mul,Nat.add_zero]
    congr 1
    omega

/-- Construction for repeat Outcome in the output readout model. -/
def repeatOutcome {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) :
    (n : ℕ) → Path (repeatReadout R r gs n) → (Fin n → Fin D)
  | 0, _ => Fin.elim0
  | n+1, p =>
    let pq := splitPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n) p
    Fin.cons (readoutOutcome R r gs pq.1) (repeatOutcome R r gs n pq.2)

/-- The actual finite repeated protocol satisfies `repeatOutcome_repeatPath` without conditioning away failure records. -/
theorem repeatOutcome_repeatPath {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D))
    (n : ℕ) (ω : Fin n → Fin D) :
    repeatOutcome R r gs n (repeatPath R r gs n ω)=ω := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [repeatOutcome,repeatPath,split_join,Fin.cons_zero,readoutOutcome_readoutPath]
    · simp only [repeatOutcome,repeatPath,split_join,Fin.cons_succ,ih]

/-- The actual finite repeated protocol satisfies `repeatPath_repeatOutcome` without conditioning away failure records. -/
theorem repeatPath_repeatOutcome {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D))
    (n : ℕ) (p : Path (repeatReadout R r gs n)) :
    repeatPath R r gs n (repeatOutcome R r gs n p)=p := by
  induction n with
  | zero => cases p; rfl
  | succ n ih =>
    change joinPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)
      (readoutPath R r gs (readoutOutcome R r gs
        (splitPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n) p).1))
      (repeatPath R r gs n (repeatOutcome R r gs n
        (splitPath (readoutProgram R r gs) (fun _ => repeatReadout R r gs n) p).2))=p
    rw [readoutPath_readoutOutcome,ih]
    exact join_split (readoutProgram R r gs) (fun _ => repeatReadout R r gs n) p

/-- Construction for repeat Path Equiv in the output readout model. -/
def repeatPathEquiv {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) (n : ℕ) :
    (Fin n → Fin D) ≃ Path (repeatReadout R r gs n) where
  toFun := repeatPath R r gs n
  invFun := repeatOutcome R r gs n
  left_inv := repeatOutcome_repeatPath R r gs n
  right_inv := repeatPath_repeatOutcome R r gs n

/-- The actual finite repeated protocol satisfies `repeatReadout_law` without conditioning away failure records. -/
theorem repeatReadout_law {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (r : Fin D) (gs : List (OutputGate D)) (n : ℕ) (ω : Fin n → Fin D)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (repeatReadout R r gs n) ρ hρ ht).prob (repeatPath R r gs n ω)=
      (sampleLaw O hO r gs).probOf ω := by
  change (Matrix.trace (pathMap _ S (repeatReadout R r gs n) (repeatPath R r gs n ω) ρ)).re=_
  rw [repeatReadout_trace]
  have he : (∏ i : Fin n,((sampleLaw O hO r gs).prob (ω i) : ℂ))=
      (((sampleLaw O hO r gs).probOf ω : ℝ) : ℂ) := by simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,ht,one_mul]

/-- Construction for constructor Readout Equiv in the output readout model. -/
def constructorReadoutEquiv {D R : ℕ} (P : Program D R)
    (words : Path P → List (OutputGate D)) (r : Path P → Fin D) (n : ℕ) :
    (Path P × (Fin n → Fin D)) ≃ Path (bind P (fun p => repeatReadout R (r p) (words p) n)) where
  toFun pq := joinPath P (fun p => repeatReadout R (r p) (words p) n) pq.1
    (repeatPath R (r pq.1) (words pq.1) n pq.2)
  invFun q :=
    let pq := splitPath P (fun p => repeatReadout R (r p) (words p) n) q
    (pq.1,repeatOutcome R (r pq.1) (words pq.1) n pq.2)
  left_inv := by
    intro pq
    dsimp only
    rw [split_join,repeatOutcome_repeatPath]
  right_inv := by
    intro q
    dsimp only
    rw [repeatPath_repeatOutcome]
    exact join_split P (fun p => repeatReadout R (r p) (words p) n) q

/-- Same-run actual constructor distribution and conditional IID Born word
samples, including every bad output record. -/
theorem constructor_repeat_law {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (r : Path P → Fin D)
    (n : ℕ) (p : Path P) (ω : Fin n → Fin D)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (r p) (words p) n)) ρ hρ ht).prob
      (constructorReadoutEquiv P words r n (p,ω))=
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p*
        (sampleLaw O hO (r p) (words p)).probOf ω := by
  change (Matrix.trace (pathMap _ S (bind P (fun p => repeatReadout R (r p) (words p) n))
    (joinPath P (fun p => repeatReadout R (r p) (words p) n) p
      (repeatPath R (r p) (words p) n ω)) ρ)).re=_
  rw [pathMap_bind]
  change (Matrix.trace (pathMap _ S (repeatReadout R (r p) (words p) n)
    (repeatPath R (r p) (words p) n ω) (pathMap _ S P p ρ))).re=_
  rw [repeatReadout_trace]
  have he : (∏ i : Fin n,((sampleLaw O hO (r p) (words p)).prob (ω i) : ℂ))=
      (((sampleLaw O hO (r p) (words p)).probOf ω : ℝ) : ℂ) := by simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rfl

/-- The finite protocol identity or bound `queryDepth_bind_le` holds under exactly the displayed hypotheses. -/
theorem queryDepth_bind_le {D R : ℕ} (P : Program D R) (F : Path P → Program D R)
    (q : ℕ) (hc : ∀ p,queryDepth (F p) ≤ q) :
    queryDepth (bind P F) ≤ queryDepth P+q := by
  induction P with
  | halt => simpa only [bind,queryDepth,Nat.zero_add] using hc ()
  | query mode next ih =>
    have hh := ih F hc
    change queryDepth (bind next F)+1 ≤ queryDepth next+1+q
    omega
  | measure I next ih =>
    apply Finset.sup_le
    intro o _
    have hh := ih o (fun p => F ⟨o,p⟩) (fun p => hc ⟨o,p⟩)
    have hn := Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ o)
    exact hh.trans (Nat.add_le_add_right hn q)
  | support a next ih =>
    apply Finset.sup_le
    intro o _
    have hh := ih o (fun p => F ⟨o,p⟩) (fun p => hc ⟨o,p⟩)
    have hn := Finset.le_sup (f := fun o => queryDepth (next o)) (Finset.mem_univ o)
    exact hh.trans (Nat.add_le_add_right hn q)

/-- The finite protocol identity or bound `wordProgram_depth` holds under exactly the displayed hypotheses. -/
theorem wordProgram_depth {D : ℕ} (R : ℕ) (gs : List (OutputGate D)) :
    queryDepth (wordProgram R gs) ≤ wordQueries gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | known U hU => exact Finset.sup_le (fun _ _ => ih)
    | query mode => exact Nat.add_le_add_right ih 1

/-- The finite protocol identity or bound `readoutProgram_depth` holds under exactly the displayed hypotheses. -/
theorem readoutProgram_depth {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) :
    queryDepth (readoutProgram R r gs) ≤ wordQueries gs := by
  apply Finset.sup_le
  intro _ _
  have hh := queryDepth_bind_le (wordProgram R gs) (fun _ => basisReadout R) 0
    (by intro p; simp [basisReadout,queryDepth])
  have hh' : queryDepth (bind (wordProgram R gs) (fun _ => basisReadout R)) ≤
      queryDepth (wordProgram R gs) := by simpa only [Nat.add_zero] using hh
  exact hh'.trans (wordProgram_depth R gs)

/-- The actual finite repeated protocol satisfies `repeatReadout_depth` without conditioning away failure records. -/
theorem repeatReadout_depth {D : ℕ} (R : ℕ) (r : Fin D) (gs : List (OutputGate D)) (n : ℕ) :
    queryDepth (repeatReadout R r gs n) ≤ n*wordQueries gs := by
  induction n with
  | zero => simp [repeatReadout,queryDepth]
  | succ n ih =>
    have hh := queryDepth_bind_le (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)
      (n*wordQueries gs) (fun _ => ih)
    have hr := readoutProgram_depth R r gs
    change queryDepth (bind (readoutProgram R r gs) (fun _ => repeatReadout R r gs n)) ≤ _
    calc
      _ ≤ queryDepth (readoutProgram R r gs)+n*wordQueries gs := hh
      _ ≤ wordQueries gs+n*wordQueries gs := Nat.add_le_add_right hr _
      _ = (n+1)*wordQueries gs := by rw [Nat.add_mul,Nat.one_mul]; omega

/-- The actual finite repeated protocol satisfies `constructor_repeat_charge` without conditioning away failure records. -/
theorem constructor_repeat_charge {D R : ℕ} (P : Program D R)
    (words : Path P → List (OutputGate D)) (r : Path P → Fin D) (n : ℕ)
    (p : Path P) (ω : Fin n → Fin D) :
    pathCharge (bind P (fun p => repeatReadout R (r p) (words p) n))
      (constructorReadoutEquiv P words r n (p,ω))=
      ((pathCharge P p).1+n*wordQueries (words p),(pathCharge P p).2) := by
  change pathCharge (bind P (fun p => repeatReadout R (r p) (words p) n))
    (joinPath P (fun p => repeatReadout R (r p) (words p) n) p
      (repeatPath R (r p) (words p) n ω))=_
  rw [pathCharge_bind,repeatReadout_charge]
  simp only [Nat.add_zero]

/-- The actual finite repeated protocol satisfies `constructor_repeat_support_cap` without conditioning away failure records. -/
theorem constructor_repeat_support_cap {D R : ℕ} (P : Program D R)
    (words : Path P → List (OutputGate D)) (r : Path P → Fin D) (n s : ℕ)
    (hc : ∀ p,(pathCharge P p).2 ≤ s) :
    ∀ q : Path (bind P (fun p => repeatReadout R (r p) (words p) n)),
      (pathCharge (bind P (fun p => repeatReadout R (r p) (words p) n)) q).2 ≤ s := by
  intro q
  obtain ⟨⟨p,ω⟩,rfl⟩ := (constructorReadoutEquiv P words r n).surjective q
  rw [constructor_repeat_charge]
  exact hc p

/-- The actual finite repeated protocol satisfies `constructor_repeat_depth` without conditioning away failure records. -/
theorem constructor_repeat_depth {D R : ℕ} (P : Program D R)
    (words : Path P → List (OutputGate D)) (r : Path P → Fin D) (n quse : ℕ)
    (hc : ∀ p,wordQueries (words p) ≤ quse) :
    queryDepth (bind P (fun p => repeatReadout R (r p) (words p) n)) ≤ queryDepth P+n*quse := by
  apply queryDepth_bind_le
  intro p
  exact (repeatReadout_depth R (r p) (words p) n).trans (Nat.mul_le_mul_left n (hc p))

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
