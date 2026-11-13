/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Models for Gram witnesses and state conversion

Defines rectangular filtered Gram certificates and their optimization values, together with
alphabet query words and coherent and noncoherent conversion costs. Matrix constructions and
alphabet witness geometry provide common data for the state conversion framework of
[LeeEtAl2011].

The module also defines spectral cutoff and controlled matrices, a selected generator from
principal spectral data, and continuous query programs interpreted through a Volterra integral
equation.

## Main definitions

* `sourceRectCert`, `sourceRectValue`: bounded rectangular Gram factorizations and their value.
* `sourceCoherentQ`, `sourceNoncoherentQ`: discrete state conversion costs.
* `sourceQDelta`, `sourceQNoncoherentDelta`: approximate Gram optimization values.
* `sourceVolterra`, `sourceContinuousMatrix`: integral evolution and continuous program
  evaluation.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- A rectangular filtered Gram factorization with finite witness space and row and column
squared norm budgets bounded by `w`. -/
def sourceRectCert {R S : Type} (n : ℕ) (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (u : R → Fin n → QState (Fin m)) (v : S → Fin n → QState (Fin m)),
    (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k) * v s j k) ∧
    (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
    (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w)

/-- The infimum of nonnegative real budgets supporting a rectangular filtered Gram certificate,
valued in the extended nonnegative reals. -/
def sourceRectValue {R S : Type} {n : ℕ} (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  sInf {b | ∃ w : ℝ, 0 ≤ w ∧ b = ENNReal.ofReal w ∧ sourceRectCert n A Z w}

/-- The rectangular Gram factorization value with a single filter whose entries are all one. -/
def sourceUnfiltered {R S : Type} (A : Matrix R S ℂ) : ℝ≥0∞ :=
  sourceRectValue A (fun _ : Fin 1 => fun _ _ => 1)

/-- Embeds a rectangular matrix into the upper-right block of a square matrix on the sum of its
index types, with all other blocks zero. -/
def sourceRectLift {R S : Type} (A : Matrix R S ℂ) : Matrix (R ⊕ S) (R ⊕ S) ℂ :=
  fun r s => match r, s with
    | .inl r, .inr s => A r s
    | _, _ => 0

/-- The alphabet difference filters, equal to one exactly when the two inputs differ at the
selected coordinate. -/
def sourceAlphabetDelta {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) : Fin n → Matrix X X ℂ :=
  fun j x y => if input x j = input y j then 0 else 1

/-- The input symbol at an ordinary address, extended by zero at the extra padded address. -/
def sourcePaddedSymbol {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) (j : Fin (n+1)) : Fin (q+1) :=
  if h : j.val < n then input x ⟨j.val, h⟩ else 0

/-- The permutation matrix adding the padded input symbol to the answer register while
preserving the address and workspace. -/
def sourceAlphabetOracle {X W : Type} [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix ((Fin (n+1) × Fin (q+1)) × W) ((Fin (n+1) × Fin (q+1)) × W) ℂ :=
  permMatrix (fun p => ((p.1.1, p.1.2 + sourcePaddedSymbol input x p.1.1), p.2))

/-- A list of known matrix gates and Boolean-tagged forward or adjoint oracle calls. -/
abbrev SourceWord (S : Type) := List (Matrix S S ℂ ⊕ Bool)

/-- Counts the oracle letters in a source word, charging both forward and adjoint calls. -/
def sourceWordCalls {S : Type} (C : SourceWord S) : ℕ :=
  C.countP (fun s => match s with | .inl _ => false | .inr _ => true)

/-- The condition that every known matrix gate in a source word is unitary. -/
def sourceWordLegal {S : Type} [Fintype S] [DecidableEq S] (C : SourceWord S) : Prop :=
  ∀ s ∈ C, match s with | .inl U => U ∈ Matrix.unitaryGroup S ℂ | .inr _ => True

/-- Evaluates a source word in execution order, using `O` for forward calls and `Oᴴ` for adjoint
calls. -/
def sourceWordMatrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) : Matrix S S ℂ :=
  (C.map (fun s => match s with | .inl U => U | .inr adj => if adj then Oᴴ else O)).reverse.prod

/-- The padded source basis with address, alphabet answer, Boolean tag, payload, and finite
workspace registers. -/
abbrev SourceSpace (n q : ℕ) (H : Type) (r : ℕ) :=
  (Fin (n+1) × Fin (q+1)) × ((Bool × H) × Fin r)

/-- Embeds a payload state with a specified tag and zero address, answer, and workspace
registers. -/
def sourceClean {H : Type} [DecidableEq H] (n q r : ℕ) (hr : 0 < r)
    (tag : Bool) (ψ : QState H) : QState (SourceSpace n q H r) :=
  TensorState (Ket (0,0)) (TensorState (TensorState (Ket tag) ψ) (Ket ⟨0,hr⟩))

/-- Combines the target payload state with a separate state on the address, answer, tag, and
workspace registers. -/
def sourceGarbageTarget {H : Type} (n q r : ℕ) (ψ : QState H)
    (ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r))) :
    QState (SourceSpace n q H r) :=
  fun p => ψ p.2.1.2 * ξ (p.1, (p.2.1.1, p.2.2))

/-- The infimum of legal alphabet word call counts achieving real overlap at least `Real.sqrt
(1-ε)` with every clean tagged target. -/
def sourceCoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1-ε)}

/-- The infimum of legal alphabet word call counts achieving overlap magnitude at least
`Real.sqrt (1-ε)` with every target tensored with some normalized garbage state. -/
def sourceNoncoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceGarbageTarget n q r (σ x) ξ p‖ ≥
      Real.sqrt (1-ε)}

/-- The infimum of filtered values from `ρ` to positive semidefinite matrices whose unfiltered
difference from `σ` has value at most `δ`. -/
def sourceQDelta {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (δ : ℝ) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Matrix X X ℂ // τ.PosSemidef ∧
      sourceUnfiltered (τ-σ) ≤ ENNReal.ofReal δ},
    sourceRectValue (ρ-τ.1) (sourceAlphabetDelta input)

/-- The infimum of filtered values from `ρ` to positive semidefinite matrices within unfiltered
budget `δ` of `σ` multiplied entrywise by a positive semidefinite matrix with unit diagonal. -/
def sourceQNoncoherentDelta {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (δ : ℝ) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Matrix X X ℂ // τ.PosSemidef},
    ⨅ S : {S : Matrix X X ℂ // S.PosSemidef ∧ ∀ x, S x x = 1},
      if sourceUnfiltered (τ.1-σ ⊙ S.1) ≤ ENNReal.ofReal δ then
        sourceRectValue (ρ-τ.1) (sourceAlphabetDelta input) else ⊤

/-- The supremum of operator norms of real Hermitian adversary matrices vanishing on
equal-output pairs and satisfying each filtered operator norm constraint. -/
def sourceAdversary {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n : ℕ} (Z : Fin n → Matrix X X ℂ) (f : X → E) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      (∀ x y, (Γ x y).im = 0) ∧ (∀ x y, f x = f y → Γ x y = 0) ∧
      ∀ j, ‖Γ ⊙ Z j‖ ≤ 1}, ENNReal.ofReal ‖Γ.1‖

/-- The infimum of legal alphabet word call counts computing `f` with measurement probability at
least `2/3` on every input from a clean `none` payload. -/
def sourceFunctionQ {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q (Option E) r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (Ket none))
      (Finset.univ.filter (fun p => p.2.1.2 = some (f x))) ≥ 2/3}

/-- The tensor product of two rectangular matrices, indexed by products of their row and column
types. -/
def sourceTensor {R S U V : Type} (A : Matrix R S ℂ) (B : Matrix U V ℂ) :
    Matrix (R × U) (S × V) ℂ := fun r s => A r.1 s.1 * B r.2 s.2

/-- Concatenates two finite filter families using the equivalence between a finite sum and a sum
of finite types. -/
def sourceFilterUnion {R S : Type} {n m : ℕ}
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix R S ℂ) :
    Fin (n+m) → Matrix R S ℂ := fun j => Sum.elim Y Z (finSumFinEquiv.symm j)

/-- The family of pairwise tensor products of two finite filter families. -/
def sourceFilterTensor {R S U V : Type} {n m : ℕ}
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    Fin (n*m) → Matrix (R × U) (S × V) ℂ := fun j =>
  sourceTensor (Y (finProdFinEquiv.symm j).1) (Z (finProdFinEquiv.symm j).2)

/-- The block diagonal direct sum of two rectangular matrices, with zero off-diagonal blocks. -/
def sourceDirectSum {R S U V : Type} (A : Matrix R S ℂ) (B : Matrix U V ℂ) :
    Matrix (R ⊕ U) (S ⊕ V) ℂ := Matrix.of (fun r s => match r,s with
  | .inl r, .inl s => A r s
  | .inr u, .inr v => B u v
  | _, _ => 0)

/-- Merges the first two filters by addition and retains the remaining filters in order. -/
def sourceMergeTwo {R S : Type} {n : ℕ} (Z : Fin (n+2) → Matrix R S ℂ) :
    Fin (n+1) → Matrix R S ℂ := fun j =>
  if j.val=0 then Z 0+Z 1 else Z ⟨j.val+1,by omega⟩

/-- The condition that every nonzero entry of `A` is nonzero in at least one filter. -/
def sourceSupports {R S : Type} {n : ℕ} (A : Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ) : Prop := ∀ r s, A r s ≠ 0 → ∃ j, Z j r s ≠ 0

/-- The real alphabet parameter `Real.sqrt (1/2 - Real.sqrt q/(q+1))`. -/
def sourceAlpha (q : ℕ) : ℝ := Real.sqrt (1/2-Real.sqrt (q : ℝ)/(q+1))
/-- The alphabet vector with exceptional amplitude `-sourceAlpha q` at `a` and complementary
square root amplitude divided by `Real.sqrt q` elsewhere. -/
def sourceMu (q : ℕ) (a : Fin (q+1)) : QState (Fin (q+1)) :=
  fun i => if i=a then (-sourceAlpha q : ℂ) else
    (Real.sqrt (1-(sourceAlpha q)^2)/Real.sqrt q : ℂ)
/-- The alphabet vector with complementary square root amplitude at `a` and amplitude
`sourceAlpha q / Real.sqrt q` elsewhere. -/
def sourceNu (q : ℕ) (a : Fin (q+1)) : QState (Fin (q+1)) :=
  fun i => if i=a then (Real.sqrt (1-(sourceAlpha q)^2) : ℂ) else
    (sourceAlpha q/Real.sqrt q : ℂ)

/-- The sum of the tagged state sector and the query, alphabet, and witness sector. -/
abbrev SourceGeometry (n q m : ℕ) (H : Type) :=
  (Bool × H) ⊕ (Fin n × (Fin (q+1) × Fin m))

/-- The equally weighted sum of the input and output states in distinct Boolean-tagged state
sectors, with zero query-sector amplitudes. -/
def sourcePlus {n q m : ℕ} {H : Type} (ρ σ : QState H) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl (false,h) => (Real.sqrt 2 : ℂ)⁻¹*ρ h
    | .inl (true,h) => (Real.sqrt 2 : ℂ)⁻¹*σ h
    | .inr _ => 0
/-- The equally weighted difference of the input and output states in distinct Boolean-tagged
state sectors, with zero query-sector amplitudes. -/
def sourceMinus {n q m : ℕ} {H : Type} (ρ σ : QState H) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl (false,h) => (Real.sqrt 2 : ℂ)⁻¹*ρ h
    | .inl (true,h) => -(Real.sqrt 2 : ℂ)⁻¹*σ h
    | .inr _ => 0

/-- The forbidden vector formed from the scaled minus state and negative products of the
input-dependent `sourceMu` amplitudes with the first witness. -/
def sourceForbidden {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl h => ((ε/Real.sqrt W : ℝ) : ℂ)*
        sourceMinus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)
    | .inr (j,a,k) => -sourceMu q (input x j) a * u x j k

/-- The block matrix acting identically on the state sector and subtracting the rank-one
`sourceMu` matrix within each query and witness sector. -/
def sourceKeep {X H : Type} [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ := Matrix.of (fun p t =>
  match p,t with
    | .inl p,.inl t => if p=t then 1 else 0
    | .inr (j,a,k),.inr (l,b,h) => if j=l ∧ k=h then
        (if a=b then 1 else 0)-sourceMu q (input x j) a * star (sourceMu q (input x j) b)
        else 0
    | _,_ => 0)

/-- Chooses an orthogonal projector whose fixed space is orthogonal to all forbidden vectors
when one exists, and returns zero otherwise. -/
def sourceComplement {X H : Type} [Fintype X] [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) :
    Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ :=
  if hp : ∃ P : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ,
      IsOrthogonalProjector P ∧ ∀ ψ : QState (SourceGeometry n q m H),
      P *ᵥ ψ = ψ ↔ ∀ x, (∑ i, star (sourceForbidden input ρ σ u W ε x i)*ψ i)=0 then
    Classical.choose hp
  else 0

/-- The fixed-vector candidate formed from the plus state and scaled products of input-dependent
`sourceNu` amplitudes with the second witness. -/
def sourceFixed {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (v : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) : QState (SourceGeometry n q m H) :=
  fun p => match p with
    | .inl h => sourcePlus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)
    | .inr (j,a,k) => (ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)*sourceNu q (input x j) a*v x j k

/-- The condition that the nonzero entries of `A` share neither a row nor a column with nonzero
entries of `B`. -/
def sourceRowColumnDisjoint {R S : Type} (A B : Matrix R S ℂ) : Prop :=
  (∀ r s t, A r s ≠ 0 → B r t = 0) ∧ (∀ s r t, A r s ≠ 0 → B t s = 0)

/-- The supremum of `‖A ⊙ M‖` over matrices satisfying `‖Z j ⊙ M‖ ≤ 1` for every filter. -/
def sourceRectDual {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  ⨆ M : {M : Matrix R S ℂ // ∀ j, ‖Z j ⊙ M‖ ≤ 1}, ENNReal.ofReal ‖A ⊙ M.1‖

/-- The square block matrix with `A` in its upper-right block, its adjoint in the lower-left
block, and zero diagonal blocks. -/
def sourceHermitianLift {R S : Type} (A : Matrix R S ℂ) :
    Matrix (R ⊕ S) (R ⊕ S) ℂ := fun r s => match r,s with
  | .inl r, .inr s => A r s
  | .inr s, .inl r => star (A r s)
  | _, _ => 0

/-- The entrywise complex conjugate of a rectangular matrix. -/
def sourceConjugate {R S : Type} (A : Matrix R S ℂ) : Matrix R S ℂ :=
  fun r s => star (A r s)

/-- The supremum of the real entrywise inner product with `A` over matrices of rectangular
filtered value at most one. -/
def sourceDualNorm {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  ⨆ B : {B : Matrix R S ℂ // sourceRectValue B Z ≤ 1},
    ENNReal.ofReal (∑ r, ∑ s, star (A r s) * B.1 r s).re

/-- The spectral cutoff matrix `V * diagonal (if |angles h| ≤ Θ then 1 else 0) * Vᴴ`. -/
def sourcePhaseProjector {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (angles : H → ℝ) (Θ : ℝ) : Matrix H H ℂ :=
  V * Matrix.diagonal (fun h => if |angles h| ≤ Θ then 1 else 0) * Vᴴ

/-- The Boolean-controlled extension of `U`, acting trivially on a finite clock register and on
the false-control sector. -/
def sourceControlledU {H : Type} [DecidableEq H] (r : ℕ) (U : Matrix H H ℂ) :
    Matrix ((Bool × H) × Fin r) ((Bool × H) × Fin r) ℂ := fun p t =>
  if p.1.1=t.1.1 ∧ p.2=t.2 then
    if p.1.1 then U p.1.2 t.1.2 else if p.1.2=t.1.2 then 1 else 0
  else 0

/-- Selects the Hermitian generator from a unitary principal-angle representation `U = V *
diagonal (exp (-I*angles)) * Vᴴ`, returning zero if no such representation exists. -/
def sourceLog {H : Type} [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) : Matrix H H ℂ :=
  if hs : ∃ (V : Matrix H H ℂ) (angles : H → ℝ),
      V ∈ Matrix.unitaryGroup H ℂ ∧ (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) ∧
      U = V * Matrix.diagonal (fun h => Complex.exp (-Complex.I * angles h)) * Vᴴ then
    let V := Classical.choose hs
    let angles := Classical.choose (Classical.choose_spec hs)
    V * Matrix.diagonal (fun h => (angles h : ℂ)) * Vᴴ
  else 0

/-- The permutation matrix for addition by `a` on the finite alphabet. -/
def sourceValueQuery {q : ℕ} (a : Fin (q+1)) : Matrix (Fin (q+1)) (Fin (q+1)) ℂ :=
  permMatrix (fun t => t+a)

/-- The block matrix applying the selected generator of the value query at each padded input
address and preserving workspace. -/
def sourceLogOracle {X W : Type} [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix ((Fin (n+1) × Fin (q+1)) × W) ((Fin (n+1) × Fin (q+1)) × W) ℂ :=
  fun p t => if p.1.1=t.1.1 ∧ p.2=t.2 then
    sourceLog (sourceValueQuery (sourcePaddedSymbol input x p.1.1)) p.1.2 t.1.2 else 0

/-- The condition that `U` starts at the identity, is continuous on `[0, T]`, and satisfies the
Volterra equation with integrand `-I • (K s * U s)`. -/
def sourceVolterra {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (U : ℝ → Matrix H H ℂ) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
  ∀ t ∈ Set.Icc 0 T, U t = 1 + Matrix.of (fun i j =>
    ∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s * U s)) i j)

/-- The terminal matrix of a chosen Volterra evolution on `[0, T]` when one exists, and the
identity otherwise. -/
def sourceVolterraMatrix {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) : Matrix H H ℂ :=
  if h : ∃ U, sourceVolterra K T U then Classical.choose h T else 1

/-- A continuous query program step, consisting of a known matrix or evolution under a
time-dependent matrix for a duration and oracle direction. -/
inductive SourceContinuousStep (H : Type) where
  | known : Matrix H H ℂ → SourceContinuousStep H
  | evolve : (ℝ → Matrix H H ℂ) → ℝ → Bool → SourceContinuousStep H

/-- The condition that known gates are unitary and evolution steps have nonnegative duration and
entrywise integrable Hermitian driving matrices. -/
def sourceContinuousLegal {H : Type} [Fintype H] [DecidableEq H]
    (C : List (SourceContinuousStep H)) : Prop :=
  ∀ s ∈ C, match s with
    | .known U => U ∈ Matrix.unitaryGroup H ℂ
    | .evolve K T _ => 0 ≤ T ∧
        (∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T) ∧
        ∀ t ∈ Set.Icc 0 T, (K t).IsHermitian

/-- The sum of the evolution durations in a continuous program, with zero cost for known gates. -/
def sourceContinuousTime {H : Type} (C : List (SourceContinuousStep H)) : ℝ :=
  (C.map (fun s => match s with | .known _ => 0 | .evolve _ T _ => T)).sum

/-- Evaluates a continuous program by composing known matrices and selected Volterra evolutions
driven by `K t` plus the signed oracle matrix. -/
def sourceContinuousMatrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (C : List (SourceContinuousStep H)) : Matrix H H ℂ :=
  (C.map (fun s => match s with
    | .known U => U
    | .evolve K T adj => sourceVolterraMatrix (fun t => K t + (if adj then -O else O)) T)).reverse.prod

/-- The infimum of legal continuous program durations achieving real overlap at least `Real.sqrt
(1-ε)` with each clean tagged target under the logarithmic alphabet oracle. -/
def sourceContinuousCoherentQ {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r))),
    b = ENNReal.ofReal (sourceContinuousTime C) ∧ sourceContinuousLegal C ∧
    ∀ x, (∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1-ε)}

/-- The infimum of legal continuous program durations achieving overlap magnitude at least
`Real.sqrt (1-ε)` with each target and some normalized garbage state under the logarithmic
alphabet oracle. -/
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
