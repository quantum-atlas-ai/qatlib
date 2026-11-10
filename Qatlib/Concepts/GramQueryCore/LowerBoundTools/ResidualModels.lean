/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def sourceRectCert {R S : Type} (n : ℕ) (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (u : R → Fin n → QState (Fin m)) (v : S → Fin n → QState (Fin m)),
    (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k) * v s j k) ∧
    (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
    (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w)

def sourceRectValue {R S : Type} {n : ℕ} (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  sInf {b | ∃ w : ℝ, 0 ≤ w ∧ b = ENNReal.ofReal w ∧ sourceRectCert n A Z w}

def sourceUnfiltered {R S : Type} (A : Matrix R S ℂ) : ℝ≥0∞ :=
  sourceRectValue A (fun _ : Fin 1 => fun _ _ => 1)

def sourceRectLift {R S : Type} (A : Matrix R S ℂ) : Matrix (R ⊕ S) (R ⊕ S) ℂ :=
  fun r s => match r, s with
    | .inl r, .inr s => A r s
    | _, _ => 0

def sourceAlphabetDelta {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) : Fin n → Matrix X X ℂ :=
  fun j x y => if input x j = input y j then 0 else 1

def sourcePaddedSymbol {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) (j : Fin (n+1)) : Fin (q+1) :=
  if h : j.val < n then input x ⟨j.val, h⟩ else 0

def sourceAlphabetOracle {X W : Type} [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix ((Fin (n+1) × Fin (q+1)) × W) ((Fin (n+1) × Fin (q+1)) × W) ℂ :=
  permMatrix (fun p => ((p.1.1, p.1.2 + sourcePaddedSymbol input x p.1.1), p.2))

abbrev SourceWord (S : Type) := List (Matrix S S ℂ ⊕ Bool)

def sourceWordCalls {S : Type} (C : SourceWord S) : ℕ :=
  C.countP (fun s => match s with | .inl _ => false | .inr _ => true)

def sourceWordLegal {S : Type} [Fintype S] [DecidableEq S] (C : SourceWord S) : Prop :=
  ∀ s ∈ C, match s with | .inl U => U ∈ Matrix.unitaryGroup S ℂ | .inr _ => True

def sourceWordMatrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) : Matrix S S ℂ :=
  (C.map (fun s => match s with | .inl U => U | .inr adj => if adj then Oᴴ else O)).reverse.prod

abbrev SourceSpace (n q : ℕ) (H : Type) (r : ℕ) :=
  (Fin (n+1) × Fin (q+1)) × ((Bool × H) × Fin r)

def sourceClean {H : Type} [DecidableEq H] (n q r : ℕ) (hr : 0 < r)
    (tag : Bool) (ψ : QState H) : QState (SourceSpace n q H r) :=
  TensorState (Ket (0,0)) (TensorState (TensorState (Ket tag) ψ) (Ket ⟨0,hr⟩))

def sourceGarbageTarget {H : Type} (n q r : ℕ) (ψ : QState H)
    (ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r))) :
    QState (SourceSpace n q H r) :=
  fun p => ψ p.2.1.2 * ξ (p.1, (p.2.1.1, p.2.2))

def sourceCoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1-ε)}

def sourceNoncoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceGarbageTarget n q r (σ x) ξ p‖ ≥
      Real.sqrt (1-ε)}

def sourceQDelta {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (δ : ℝ) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Matrix X X ℂ // τ.PosSemidef ∧
      sourceUnfiltered (τ-σ) ≤ ENNReal.ofReal δ},
    sourceRectValue (ρ-τ.1) (sourceAlphabetDelta input)

def sourceQNoncoherentDelta {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (δ : ℝ) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Matrix X X ℂ // τ.PosSemidef},
    ⨅ S : {S : Matrix X X ℂ // S.PosSemidef ∧ ∀ x, S x x = 1},
      if sourceUnfiltered (τ.1-σ ⊙ S.1) ≤ ENNReal.ofReal δ then
        sourceRectValue (ρ-τ.1) (sourceAlphabetDelta input) else ⊤

def sourceAdversary {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n : ℕ} (Z : Fin n → Matrix X X ℂ) (f : X → E) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      (∀ x y, (Γ x y).im = 0) ∧ (∀ x y, f x = f y → Γ x y = 0) ∧
      ∀ j, ‖Γ ⊙ Z j‖ ≤ 1}, ENNReal.ofReal ‖Γ.1‖

def sourceFunctionQ {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q (Option E) r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (Ket none))
      (Finset.univ.filter (fun p => p.2.1.2 = some (f x))) ≥ 2/3}

def sourceTensor {R S U V : Type} (A : Matrix R S ℂ) (B : Matrix U V ℂ) :
    Matrix (R × U) (S × V) ℂ := fun r s => A r.1 s.1 * B r.2 s.2

def sourceFilterUnion {R S : Type} {n m : ℕ}
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix R S ℂ) :
    Fin (n+m) → Matrix R S ℂ := fun j => Sum.elim Y Z (finSumFinEquiv.symm j)

def sourceFilterTensor {R S U V : Type} {n m : ℕ}
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    Fin (n*m) → Matrix (R × U) (S × V) ℂ := fun j =>
  sourceTensor (Y (finProdFinEquiv.symm j).1) (Z (finProdFinEquiv.symm j).2)

def sourceDirectSum {R S U V : Type} (A : Matrix R S ℂ) (B : Matrix U V ℂ) :
    Matrix (R ⊕ U) (S ⊕ V) ℂ := Matrix.of (fun r s => match r,s with
  | .inl r, .inl s => A r s
  | .inr u, .inr v => B u v
  | _, _ => 0)

def sourceMergeTwo {R S : Type} {n : ℕ} (Z : Fin (n+2) → Matrix R S ℂ) :
    Fin (n+1) → Matrix R S ℂ := fun j =>
  if j.val=0 then Z 0+Z 1 else Z ⟨j.val+1,by omega⟩

def sourceSupports {R S : Type} {n : ℕ} (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) : Prop := ∀ r s, A r s ≠ 0 → ∃ j, Z j r s ≠ 0

def sourceAlpha (q : ℕ) : ℝ := Real.sqrt (1/2-Real.sqrt (q : ℝ)/(q+1))
def sourceMu (q : ℕ) (a : Fin (q+1)) : QState (Fin (q+1)) :=
  fun i => if i=a then (-sourceAlpha q : ℂ) else
    (Real.sqrt (1-(sourceAlpha q)^2)/Real.sqrt q : ℂ)
def sourceNu (q : ℕ) (a : Fin (q+1)) : QState (Fin (q+1)) :=
  fun i => if i=a then (Real.sqrt (1-(sourceAlpha q)^2) : ℂ) else
    (sourceAlpha q/Real.sqrt q : ℂ)

abbrev SourceGeometry (n q m : ℕ) (H : Type) :=
  (Bool × H) ⊕ (Fin n × (Fin (q+1) × Fin m))

def sourcePlus {n q m : ℕ} {H : Type} (ρ σ : QState H) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl (false,h) => (Real.sqrt 2 : ℂ)⁻¹*ρ h
    | .inl (true,h) => (Real.sqrt 2 : ℂ)⁻¹*σ h
    | .inr _ => 0
def sourceMinus {n q m : ℕ} {H : Type} (ρ σ : QState H) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl (false,h) => (Real.sqrt 2 : ℂ)⁻¹*ρ h
    | .inl (true,h) => -(Real.sqrt 2 : ℂ)⁻¹*σ h
    | .inr _ => 0

def sourceForbidden {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl h => ((ε/Real.sqrt W : ℝ) : ℂ)*
        sourceMinus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)
    | .inr (j,a,k) => -sourceMu q (input x j) a * u x j k

def sourceKeep {X H : Type} [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ := Matrix.of (fun p t =>
  match p,t with
    | .inl p,.inl t => if p=t then 1 else 0
    | .inr (j,a,k),.inr (l,b,h) => if j=l ∧ k=h then
        (if a=b then 1 else 0)-sourceMu q (input x j) a * star (sourceMu q (input x j) b)
        else 0
    | _,_ => 0)

def sourceComplement {X H : Type} [Fintype X] [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) :
    Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ :=
  if hp : ∃ P : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ,
      IsOrthogonalProjector P ∧ ∀ ψ : QState (SourceGeometry n q m H),
      P *ᵥ ψ = ψ ↔ ∀ x, (∑ i, star (sourceForbidden input ρ σ u W ε x i)*ψ i)=0 then
    Classical.choose hp
  else 0

def sourceFixed {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (v : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl h => sourcePlus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)
    | .inr (j,a,k) => (ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)*sourceNu q (input x j) a*v x j k

def sourceRowColumnDisjoint {R S : Type} (A B : Matrix R S ℂ) : Prop :=
  (∀ r s t, A r s ≠ 0 → B r t = 0) ∧ (∀ s r t, A r s ≠ 0 → B t s = 0)

def sourceRectDual {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  ⨆ M : {M : Matrix R S ℂ // ∀ j, ‖Z j ⊙ M‖ ≤ 1}, ENNReal.ofReal ‖A ⊙ M.1‖

def sourceHermitianLift {R S : Type} (A : Matrix R S ℂ) :
    Matrix (R ⊕ S) (R ⊕ S) ℂ := fun r s => match r,s with
  | .inl r, .inr s => A r s
  | .inr s, .inl r => star (A r s)
  | _, _ => 0

def sourceConjugate {R S : Type} (A : Matrix R S ℂ) : Matrix R S ℂ :=
  fun r s => star (A r s)

def sourceDualNorm {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  ⨆ B : {B : Matrix R S ℂ // sourceRectValue B Z ≤ 1},
    ENNReal.ofReal (∑ r, ∑ s, star (A r s) * B.1 r s).re

def sourcePhaseProjector {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (angles : H → ℝ) (Θ : ℝ) : Matrix H H ℂ :=
  V * Matrix.diagonal (fun h => if |angles h| ≤ Θ then 1 else 0) * Vᴴ

def sourceControlledU {H : Type} [DecidableEq H] (r : ℕ) (U : Matrix H H ℂ) :
    Matrix ((Bool × H) × Fin r) ((Bool × H) × Fin r) ℂ := fun p t =>
  if p.1.1=t.1.1 ∧ p.2=t.2 then
    if p.1.1 then U p.1.2 t.1.2 else if p.1.2=t.1.2 then 1 else 0
  else 0

def sourceLog {H : Type} [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) : Matrix H H ℂ :=
  if hs : ∃ (V : Matrix H H ℂ) (angles : H → ℝ),
      V ∈ Matrix.unitaryGroup H ℂ ∧ (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) ∧
      U = V * Matrix.diagonal (fun h => Complex.exp (-Complex.I * angles h)) * Vᴴ then
    let V := Classical.choose hs
    let angles := Classical.choose (Classical.choose_spec hs)
    V * Matrix.diagonal (fun h => (angles h : ℂ)) * Vᴴ
  else 0

def sourceValueQuery {q : ℕ} (a : Fin (q+1)) : Matrix (Fin (q+1)) (Fin (q+1)) ℂ :=
  permMatrix (fun t => t+a)

def sourceLogOracle {X W : Type} [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix ((Fin (n+1) × Fin (q+1)) × W) ((Fin (n+1) × Fin (q+1)) × W) ℂ :=
  fun p t => if p.1.1=t.1.1 ∧ p.2=t.2 then
    sourceLog (sourceValueQuery (sourcePaddedSymbol input x p.1.1)) p.1.2 t.1.2 else 0

def sourceVolterra {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (U : ℝ → Matrix H H ℂ) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
  ∀ t ∈ Set.Icc 0 T, U t = 1 + Matrix.of (fun i j =>
    ∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s * U s)) i j)

def sourceVolterraMatrix {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) : Matrix H H ℂ :=
  if h : ∃ U, sourceVolterra K T U then Classical.choose h T else 1

inductive SourceContinuousStep (H : Type) where
  | known : Matrix H H ℂ → SourceContinuousStep H
  | evolve : (ℝ → Matrix H H ℂ) → ℝ → Bool → SourceContinuousStep H

def sourceContinuousLegal {H : Type} [Fintype H] [DecidableEq H]
    (C : List (SourceContinuousStep H)) : Prop :=
  ∀ s ∈ C, match s with
    | .known U => U ∈ Matrix.unitaryGroup H ℂ
    | .evolve K T _ => 0 ≤ T ∧
        (∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T) ∧
        ∀ t ∈ Set.Icc 0 T, (K t).IsHermitian

def sourceContinuousTime {H : Type} (C : List (SourceContinuousStep H)) : ℝ :=
  (C.map (fun s => match s with | .known _ => 0 | .evolve _ T _ => T)).sum

def sourceContinuousMatrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (C : List (SourceContinuousStep H)) : Matrix H H ℂ :=
  (C.map (fun s => match s with
    | .known U => U
    | .evolve K T adj => sourceVolterraMatrix (fun t => K t + (if adj then -O else O)) T)).reverse.prod

def sourceContinuousCoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r))),
    b = ENNReal.ofReal (sourceContinuousTime C) ∧ sourceContinuousLegal C ∧
    ∀ x, (∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1-ε)}

def sourceContinuousNoncoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r))),
    b = ENNReal.ofReal (sourceContinuousTime C) ∧ sourceContinuousLegal C ∧
    ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceGarbageTarget n q r (σ x) ξ p‖ ≥
      Real.sqrt (1-ε)}

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
