/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Span-program model for Reichardt, arXiv:0904.2759v1

This module fixes the paper's objects in Lean:

* `SpanProgram n` — Definition 2.1: target vector `|t⟩`, input vectors `|v_i⟩`
  indexed by `I = I_free ⊔ ⋃_{j,b} I_{j,b}`, in a finite-dimensional complex
  inner-product space `C^dim`.  The index set is re-indexed by `Fin idx`.
* `SpanProgram.fP` — Eq. (2.1), the function computed by the program.
* `SpanProgram.witnessSize` — Definition 2.3, Eqs. (2.5)–(2.6), with costs
  `s : Fin n → ℝ`; the cost operator `S` is represented by its squared diagonal
  action `∑_i s_{j(i)} |w_i|^2`, which is `‖S w‖²`.
* `SpanProgram.wsizeOn`, `wsize` — Eq. (2.7), the maximum over a domain.
* `advGeneral`, `advNonneg` — Definition 2.4, Eqs. (2.9)–(2.10), with costs.
* `advGeneralSDP`, `advNonnegSDP`, `advGeneralSDP2` — Eqs. (6.2), (6.5), (6.6).
* `vectorProgramValue` — Eq. (6.7), the vector-factorization form of Lemma 6.5.
* `queryComplexity`, `queryComplexityOneSided` — bounded-error and one-sided
  bounded-error query complexity in the frozen source word model
  (`sourceFunctionQ`), with the boolean alphabet `Fin 2`.
* `graphBiadj`, `graphAdjacency` — Definition 8.2, Eq. (8.4), and the weighted
  bipartite adjacency matrix `A_G`.
* `thresholdFun`, `intervalFun` — Definition A.1, Eqs. (A.1)–(A.2).
* `CompDomain`, `iterComp` — iterated composition `f^k` of Theorem 7.3.

The values of witness sizes and adversary bounds are `ℝ≥0∞`, so that infeasible
or unbounded cases stay explicit.  No mathematical result of the paper is
assumed here; everything below is a definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Papers.SpanProgReich09.MainResults

/-- Boolean strings of length `n`, the paper's `B^n` with `B = {0,1}`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- The `{0,1}`-to-`Fin 2` alphabet encoding used for the source query model. -/
def bitOfBool (b : Bool) : Fin 2 := if b then 1 else 0

/-! ## Definition 2.1: span programs -/

/-- Definition 2.1: a span program with target vector `target`, input vectors
`vec i`, and a label `none` for free inputs and `some (j,b)` for inputs labeled
by `(j,b)`.  The index set `I = I_free ⊔ ⋃_{j,b} I_{j,b}` is represented by
`Fin idx` and `label`. -/
structure SpanProgram (n : ℕ) where
  /-- Dimension of the inner-product space `V`. -/
  dim : ℕ
  /-- Number of input vectors. -/
  idx : ℕ
  /-- The target vector `|t⟩`. -/
  target : Fin dim → ℂ
  /-- The input vectors `|v_i⟩`. -/
  vec : Fin idx → Fin dim → ℂ
  /-- `none` for `I_free`, `some (j,b)` for `I_{j,b}`. -/
  label : Fin idx → Option (Fin n × Bool)

namespace SpanProgram

variable {n : ℕ}

/-- An input vector is free. -/
def IsFree (P : SpanProgram n) (i : Fin P.idx) : Prop := P.label i = none

/-- Eq. (2.3): `i ∈ I(x)`, i.e. the input vector is available on `x`. -/
def Available (P : SpanProgram n) (x : BitString n) (i : Fin P.idx) : Prop :=
  P.IsFree i ∨ ∃ (j : Fin n) (b : Bool), P.label i = some (j, b) ∧ x j = b

/-- Eq. (2.4): the diagonal of the available-index projection `Π(x)`. -/
def piCoeff (P : SpanProgram n) (x : BitString n) (i : Fin P.idx) : ℂ :=
  if P.Available x i then 1 else 0

/-- The linear combination `A Π(x) w` of available input vectors. -/
def combo (P : SpanProgram n) (x : BitString n) (w : Fin P.idx → ℂ) : Fin P.dim → ℂ :=
  fun r => ∑ i, P.piCoeff x i * w i * P.vec i r

/-- Eq. (2.1): `f_P(x) = 1` iff the target lies in the span of the available
input vectors. -/
def fP (P : SpanProgram n) (x : BitString n) : Bool :=
  if ∃ w : Fin P.idx → ℂ, P.combo x w = P.target then true else false

/-- Definition 2.3: the squared diagonal action of the cost operator `S`:
`‖S w‖² = ∑_i s_{j(i)} |w_i|²` on labeled inputs and zero on free inputs. -/
def costScale (P : SpanProgram n) (s : Fin n → ℝ) (i : Fin P.idx) : ℝ :=
  match P.label i with
  | none => 0
  | some (j, _) => s j

/-- The coordinate `(A† w')_i = ⟨v_i | w'⟩` of the adjoint applied to `w'`. -/
def dualCoord (P : SpanProgram n) (w' : Fin P.dim → ℂ) (i : Fin P.idx) : ℂ :=
  Inner (P.vec i) w'

/-- Eq. (2.5): feasible costs of a positive (true-input) witness. -/
def trueCostSet (P : SpanProgram n) (s : Fin n → ℝ) (x : BitString n) : Set ℝ≥0∞ :=
  {y | ∃ w : Fin P.idx → ℂ, P.combo x w = P.target ∧
      y = ENNReal.ofReal (∑ i, P.costScale s i * ‖w i‖ ^ 2)}

/-- Eq. (2.6): feasible costs of a negative (false-input) witness. -/
def falseCostSet (P : SpanProgram n) (s : Fin n → ℝ) (x : BitString n) : Set ℝ≥0∞ :=
  {y | ∃ w' : Fin P.dim → ℂ, Inner P.target w' = 1 ∧
      (∀ i, P.Available x i → P.dualCoord w' i = 0) ∧
      y = ENNReal.ofReal (∑ i, P.costScale s i * ‖P.dualCoord w' i‖ ^ 2)}

/-- Definition 2.3, Eqs. (2.5)–(2.6): `wsize_s(P,x)`. -/
def witnessSize (P : SpanProgram n) (s : Fin n → ℝ) (x : BitString n) : ℝ≥0∞ :=
  if P.fP x then sInf (P.trueCostSet s x) else sInf (P.falseCostSet s x)

/-- Eq. (2.7): witness size restricted to a domain of inputs. -/
def wsizeOn (P : SpanProgram n) (s : Fin n → ℝ) (D : Set (BitString n)) : ℝ≥0∞ :=
  ⨆ x : {x : BitString n // x ∈ D}, P.witnessSize s x.1

/-- Uniform costs `~1`. -/
def uniformCost (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The paper's `wsize_s(P)` with uniform costs on all of `B^n`. -/
def wsize (P : SpanProgram n) (s : Fin n → ℝ) : ℝ≥0∞ := P.wsizeOn s Set.univ

/-- The paper's `wsize(P)`, i.e. uniform costs on `B^n`. -/
def wsizeUniform (P : SpanProgram n) : ℝ≥0∞ := P.wsize (uniformCost n)

/-- Witness size restricted to a finite indexed domain via an input embedding. -/
def wsizeOnInput {X : Type} (P : SpanProgram n) (s : Fin n → ℝ)
    (input : X → BitString n) : ℝ≥0∞ := ⨆ x, P.witnessSize s (input x)

/-- `P` agrees with `f` on the indexed domain `input`. -/
def ComputesOn {X : Type} (P : SpanProgram n) (input : X → BitString n)
    (f : X → Bool) : Prop := ∀ x, P.fP (input x) = f x

/-- `P` computes the total boolean function `f` on `B^n`. -/
def Computes (P : SpanProgram n) (f : BitString n → Bool) : Prop := ∀ x, P.fP x = f x

/-- Definition 4.9: a strict span program has no free input vectors. -/
def Strict (P : SpanProgram n) : Prop := ∀ i, P.label i ≠ none

/-- A monotone span program has no `I_{j,0}`. -/
def Monotone (P : SpanProgram n) : Prop := ∀ (i : Fin P.idx) (j : Fin n), P.label i ≠ some (j, false)

/-- A span program is real when the target and input vectors have real
coordinates in the fixed basis. -/
def Real (P : SpanProgram n) : Prop :=
  (∀ r, ∃ a : ℝ, P.target r = (a : ℂ)) ∧ ∀ i r, ∃ a : ℝ, P.vec i r = (a : ℂ)

/-- Definition 5.1 with an explicit identification `e` of the zero-input set
`F_0 = {x : f_P(x) = 0}` with the computational basis of `V`. -/
def CanonicalWith (P : SpanProgram n)
    (e : {x : BitString n // P.fP x = false} ≃ Fin P.dim) : Prop :=
  P.Strict ∧
  (∀ r, P.target r = ∑ x : {x : BitString n // P.fP x = false}, if e x = r then 1 else 0) ∧
  (∀ (x : {x : BitString n // P.fP x = false}) (i : Fin P.idx),
    P.Available x.1 i → P.vec i (e x) = 0)

/-- Lemma 4.12: apply the linear map `M` to the target and all input vectors. -/
def applyLin (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ) : SpanProgram n where
  dim := P.dim
  idx := P.idx
  target := M *ᵥ P.target
  vec i := M *ᵥ P.vec i
  label := P.label

end SpanProgram

variable {n : ℕ}

/-! ## Definition 2.4: adversary bounds -/

/-- The filter matrix `Δ_j = ∑_{x,y : x_j ≠ y_j} |x⟩⟨y|` of Definition 2.4. -/
def delta {X : Type} {n : ℕ} (input : X → Fin n → Bool) (j : Fin n) : Matrix X X ℝ :=
  fun x y => if input x j = input y j then 0 else 1

/-- Feasibility for the adversary matrices of Definition 2.4: real symmetric,
zero on equal-output pairs, and `‖Γ ∘ Δ_j‖ ≤ s_j` for each `j`. -/
def AdversaryFeasible {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) (Γ : Matrix X X ℝ) : Prop :=
  Γᵀ = Γ ∧ (∀ x y, f x = f y → Γ x y = 0) ∧ ∀ j, ‖Γ ⊙ delta input j‖ ≤ s j

/-- Eq. (2.9): the nonnegative-weight adversary bound `Adv_s(f)`. -/
def advNonneg {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // AdversaryFeasible input f s Γ ∧ ∀ x y, 0 ≤ Γ x y},
    ENNReal.ofReal ‖Γ.1‖

/-- Eq. (2.10): the general adversary bound `Adv±_s(f)`. -/
def advGeneral {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // AdversaryFeasible input f s Γ}, ENNReal.ofReal ‖Γ.1‖

/-- The standard input family of a total function on `B^n`. -/
def totalInput {n : ℕ} : BitString n → Fin n → Bool := fun x j => x j

/-- Eq. (6.2): the SDP dual form of the general adversary bound, with
coordinates labeled by `D × [n]`. -/
def advGeneralSDP {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ Zs : {M : Matrix (X × Fin n) (X × Fin n) ℂ // M.PosSemidef ∧
      ∀ x y, f x ≠ f y →
        (∑ j : Fin n, if input x j ≠ input y j then (M (x, j) (y, j)).re else 0) = 1},
    ⨆ x, ENNReal.ofReal (∑ j, s j * (Zs.val (x, j) (x, j)).re)

/-- Eq. (6.5): the SDP form of the nonnegative-weight adversary bound. -/
def advNonnegSDP {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ Zs : {M : Fin n → Matrix X X ℂ //
      (∀ j, (M j).PosSemidef) ∧
      ∀ x y, f x ≠ f y →
        (1 : ℝ) ≤ ∑ j, if input x j ≠ input y j then (M j x y).re else 0},
    ⨆ x, ENNReal.ofReal (∑ j, s j * (Zs.val j x x).re)

/-- Eq. (6.6): the SDP form of the general adversary bound with separate
positive and negative PSD matrices. -/
def advGeneralSDP2 {X E : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ Zs : {M : (Fin n → Matrix X X ℂ) × (Fin n → Matrix X X ℂ) //
      (∀ j, (M.1 j).PosSemidef) ∧ (∀ j, (M.2 j).PosSemidef) ∧
      ∀ x y, f x ≠ f y →
        (∑ j, if input x j ≠ input y j then
          ((M.1 j x y).re - (M.2 j x y).re) else 0) = 1},
    ⨆ x, ENNReal.ofReal (∑ j, s j * ((Zs.val.1 j x x).re + (Zs.val.2 j x x).re))

/-- Eq. (6.7): the vector-factorization value of Lemma 6.5. -/
def vectorProgramValue {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (s : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ m : ℕ, ⨅ v : X → Fin n → Fin m → ℂ,
    if ∀ x y, f x = false → f y = true →
        (∑ j : Fin n, if input x j ≠ input y j then
          Inner (v x j) (v y j) else 0) = 1
    then ⨆ x, ENNReal.ofReal (∑ j, s j * ∑ k, ‖v x j k‖ ^ 2)
    else ⊤

/-! ## Query complexity in the frozen source word model -/

/-- Bounded-error (2/3) query complexity of a finite-domain boolean function,
using the frozen source word model with a one-coordinate encoding of the domain
into the alphabet `Fin (card X + 1)`.  This is the paper's `Q(f)`. -/
def queryComplexity (X : Type) [Fintype X] [DecidableEq X] (f : X → Bool) : ℝ≥0∞ :=
  sourceFunctionQ
    (n := 1) (q := Fintype.card X)
    (fun x (_ : Fin 1) => Fin.castLE (Nat.le_succ _) (Fintype.equivFin X x)) f

/-- One-sided bounded-error query complexity with certainty on false inputs,
Eq. (2.14) context and Theorem 3.1: false inputs are rejected with probability
one and true inputs are accepted with probability at least `2/3`. -/
def queryComplexityOneSided (X : Type) [Fintype X] [DecidableEq X]
    (f : X → Bool) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r)
      (C : SourceWord (SourceSpace 1 (Fintype.card X) (Option Bool) r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    (∀ x, f x = false →
      MeasureProb (sourceWordMatrix
        (sourceAlphabetOracle
          (fun y (_ : Fin 1) => Fin.castLE (Nat.le_succ _) (Fintype.equivFin X y)) x) C *ᵥ
        sourceClean 1 (Fintype.card X) r hr false (Ket none))
        (Finset.univ.filter (fun p => p.2.1.2 = some false)) = 1) ∧
    (∀ x, f x = true →
      MeasureProb (sourceWordMatrix
        (sourceAlphabetOracle
          (fun y (_ : Fin 1) => Fin.castLE (Nat.le_succ _) (Fintype.equivFin X y)) x) C *ᵥ
        sourceClean 1 (Fintype.card X) r hr false (Ket none))
        (Finset.univ.filter (fun p => p.2.1.2 = some true)) ≥ 2 / 3)}

/-! ## Definition 8.2: the weighted bipartite graph `G_P(x)` -/

/-- Eq. (8.4): the biadjacency matrix of `G_P(x)`, with row side
`V ⊕ I` and column side `{0} ⊕ I`.  The weight-one edges are deleted exactly on
the available indices `I(x)`. -/
def graphBiadj (P : SpanProgram n) (x : BitString n) :
    Matrix (Fin P.dim ⊕ Fin P.idx) (Unit ⊕ Fin P.idx) ℂ
  | Sum.inl r, Sum.inl _ => P.target r
  | Sum.inl r, Sum.inr i => P.vec i r
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr i' => if i = i' ∧ ¬ P.Available x i then 1 else 0

/-- The weighted bipartite adjacency matrix `A_G = [[0,B],[B†,0]]`. -/
def graphAdjacency (P : SpanProgram n) (x : BitString n) :
    Matrix ((Fin P.dim ⊕ Fin P.idx) ⊕ (Unit ⊕ Fin P.idx))
      ((Fin P.dim ⊕ Fin P.idx) ⊕ (Unit ⊕ Fin P.idx)) ℂ :=
  fun a b => match a, b with
    | Sum.inl t, Sum.inr c => graphBiadj P x t c
    | Sum.inr c, Sum.inl t => star (graphBiadj P x t c)
    | _, _ => 0

/-- General weighted bipartite adjacency built from an arbitrary biadjacency
matrix, as in Proposition 8.8. -/
def bipAdj {T U : Type} (B : Matrix T U ℂ) : Matrix (T ⊕ U) (T ⊕ U) ℂ :=
  fun a b => match a, b with
    | Sum.inl t, Sum.inr u => B t u
    | Sum.inr u, Sum.inl t => star (B t u)
    | _, _ => 0

/-- The output vertex `μ_0` inside `T ⊕ ({0} ⊕ I)`. -/
def outputVertex (P : SpanProgram n) : Sum (Fin P.dim ⊕ Fin P.idx) (Unit ⊕ Fin P.idx) :=
  Sum.inr (Sum.inl ())

/-! ## Appendix A: threshold and interval functions -/

/-- The Hamming weight of a boolean string. -/
def hammingWeight {n : ℕ} (x : BitString n) : ℕ :=
  (Finset.univ.filter (fun j => x j = true)).card

/-- Eq. (A.1): the Hamming-weight threshold function `T_l^n`. -/
def thresholdFun (n l : ℕ) (x : BitString n) : Bool := l ≤ hammingWeight x

/-- Eq. (A.2): the Hamming-weight interval function `I_{l,m}^n`. -/
def intervalFun (n l m : ℕ) (x : BitString n) : Bool :=
  l ≤ hammingWeight x ∧ hammingWeight x ≤ m

/-! ## Iterated composition (Theorem 7.3) -/

/-- The domain of the `k`-fold self-composition `f^k`: a complete `n`-ary tree
of depth `k` whose leaves are bits. -/
def CompDomain (n : ℕ) : ℕ → Type
  | 0 => Bool
  | k + 1 => Fin n → CompDomain n k

instance compDomainFintype (n k : ℕ) : Fintype (CompDomain n k) := by
  induction k with
  | zero => change Fintype Bool; infer_instance
  | succ k ih =>
      change Fintype (Fin n → CompDomain n k)
      haveI := ih
      infer_instance

instance compDomainDecidableEq (n k : ℕ) : DecidableEq (CompDomain n k) := by
  induction k with
  | zero => change DecidableEq Bool; infer_instance
  | succ k ih =>
      change DecidableEq (Fin n → CompDomain n k)
      haveI := ih
      infer_instance

/-- The `k`-fold self-composition `f^k` of a boolean function. -/
def iterComp {n : ℕ} (f : BitString n → Bool) : (k : ℕ) → CompDomain n k → Bool
  | 0, b => b
  | k + 1, x => f (fun j => iterComp f k (x j))

end Qatlib.Papers.SpanProgReich09.MainResults
