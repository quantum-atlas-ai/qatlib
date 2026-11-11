/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-layer model for arXiv:1104.4468 (Klauck–Špalek–de Wolf)

Fixed source: arXiv:1104.4468, "A strong direct product theorem for quantum query
complexity".  Page references below are to the arXiv PDF v1 (2011).

This module fixes the paper's notation at the level of the *shared* query model of
this library:

* inputs `input : X → Fin n → Fin (q+1)` are functions on a finite domain `X`
  (`D ⊆ Dⁿ` in the paper, with alphabet size `q+1`);
* a state-generation problem is a family of normalized target states, whose Gram
  matrix `σ(x,y) = ⟨σ_x | σ_y⟩` (Section 2.1) is `StateGenerationProblem.gram`;
* coherent and non-coherent query complexity use the counted `SourceWord` model of
  `QuantumAlgorithm.Concepts.GramQueryCore.LowerBoundTools` (`sourceWordCalls`,
  `sourceWordMatrix`, `sourceAlphabetOracle`, `sourceClean`), which is the library's
  general-alphabet version of the paper's query model;
* `Adv*` is Definition 3.1 (p.7), `Madv` is Definition 3.5 (p.8), and `γ₂` is
  Definition 2.3 (p.4), reused as `sourceUnfiltered`;
* `F(x,y) = δ_{f x, f y}` and `σ_f(x,y) = (-1)^{f x + f y}` are the two Gram
  matrices of Section 2 (p.4).

Everything here is a definition or an elementary structural lemma; no claim of the
paper is asserted in this file.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Foundations.PureStateMath
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.QDirectProd11.MainResults.Model

/-! ## 1. Inputs, k-fold products, XOR, and the two function Gram matrices -/

/-- The input of the `k`-fold product problem `f^{(k)}` (Section 1, p.2):
a `k`-tuple `x¹,…,xᵏ` of inputs, with the `k·n` coordinates re-indexed through
`finProdFinEquiv`. -/
def prodInput {X : Type} {n q k : ℕ} (input : X → Fin n → Fin (q+1)) :
    (Fin k → X) → Fin (k * n) → Fin (q+1) :=
  fun xs j => input (xs (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

/-- The `k`-fold product function `f^{(k)}(x¹,…,xᵏ) = (f x¹,…, f xᵏ)` (Section 1, p.2). -/
def kFoldFun {X E : Type} (f : X → E) (k : ℕ) : (Fin k → X) → (Fin k → E) :=
  fun xs l => f (xs l)

/-- The parity of `k` copies of a Boolean function, `⊕ ∘ f^{(k)}` (Section 2, p.4). -/
def xorFold {X : Type} (f : X → Bool) (k : ℕ) : (Fin k → X) → Bool :=
  fun xs => decide ((∑ l : Fin k, if f (xs l) then 1 else 0) % 2 = 1)

/-- The function-evaluation Gram matrix `F(x,y) = δ_{f x, f y}` (Section 2, p.4). -/
def funEvalGram {X E : Type} [DecidableEq E] (f : X → E) : Matrix X X ℂ :=
  fun x y => if f x = f y then 1 else 0

/-- The phase Gram matrix `σ_f(x,y) = (-1)^{f x + f y}` for a Boolean `f`
(Section 2, p.4): `1` on equal outputs and `-1` on different outputs. -/
def phaseGram {X : Type} (f : X → Bool) : Matrix X X ℂ :=
  fun x y => if f x = f y then 1 else -1

/-- The `k`-fold tensor power `σ^{⊗k}` of a Gram matrix, indexed by `k`-tuples:
`σ^{⊗k}(x,y) = ∏_{l} σ(x_l, y_l)` (Section 4, Theorem 4.1). -/
def gramTensorPower {X : Type} (σ : Matrix X X ℂ) (k : ℕ) :
    Matrix (Fin k → X) (Fin k → X) ℂ :=
  fun xs ys => ∏ l, σ (xs l) (ys l)

/-! ## 2. State-generation problems and their query complexities -/

/-- A state-generation problem as in Section 2.1 (p.5): a finite-dimensional
Hilbert space, a default state `init`, and normalized target states `target x`.
The problem is determined by its Gram matrix `gram`. -/
structure StateGenerationProblem (X : Type) where
  /-- Hilbert space of the target states. -/
  H : Type
  instFintype : Fintype H
  instDecidableEq : DecidableEq H
  /-- Default state `|0̄⟩` of the workspace register. -/
  init : QState H
  initNormalized : Normalized init
  /-- Target state `|σ_x⟩`. -/
  target : X → QState H
  targetNormalized : ∀ x, Normalized (target x)

attribute [instance] StateGenerationProblem.instFintype StateGenerationProblem.instDecidableEq

/-- The target Gram matrix `σ(x,y) = ⟨σ_x | σ_y⟩` (Section 2.1, p.5). -/
def StateGenerationProblem.gram {X : Type} (P : StateGenerationProblem X) : Matrix X X ℂ :=
  gramStateMatrix P.target

/-- Coherent quantum query complexity `Q^c_ε(σ)` (Section 2.1, p.5): the infimum over
counted legal query words `C` of the number of oracle calls such that, for every
input `x`, the final state has overlap at least `√(1-ε)` with the clean target
`|σ_x⟩ ⊗ |0̄⟩`.  The success condition is exactly the coherent output condition of
Section 2.1 and Claim 3.8. -/
def coherentQ {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (P : StateGenerationProblem X) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q P.H r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false P.init) p) *
        sourceClean n q r hr true (P.target x) p).re ≥ Real.sqrt (1 - ε)}

/-- The paper's `Q^c_ε(σ)` for a Gram matrix `σ`: the complexity of any state
generation problem realizing `σ` (all realizations have the same complexity by
Claim 3.8).  The infimum is `⊤` for a matrix that is not a Gram matrix. -/
def coherentQOfGram {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (σ : Matrix X X ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ P : {P : StateGenerationProblem X // P.gram = σ}, coherentQ input P.1 ε

/-- Non-coherent quantum query complexity of a function, `Q_ε(f)` (Section 2.1,
p.5, with the answer register read out): the infimum over counted legal query words
whose final state, on every input `x`, yields `f x` with probability at least
`1-ε`.  This is the function-evaluation specialization used throughout the paper. -/
def noncoherentFunctionQ {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q (Option E) r)),
    b = (sourceWordCalls C : ℝ≥0∞) ∧ sourceWordLegal C ∧
    ∀ x, MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (Ket (none : Option E)))
      (Finset.univ.filter (fun p => p.2.1.2 = some (f x))) ≥ 1 - ε}

/-! ## 3. Additive and multiplicative adversary values -/

/-- `γ₂(A)` of Definition 2.3 (p.4), in the library's rectangular-value form
(`sourceUnfiltered` is the unfiltered rectangular γ₂ value). -/
def gamma2 {X : Type} (A : Matrix X X ℂ) : ℝ≥0∞ :=
  sourceUnfiltered A

/-- The additive adversary `Adv*(σ)` of Definition 3.1 (p.7): the supremum of
`‖Γ ∘ (J-σ)‖` over Hermitian `Γ` with `I ± Γ ∘ (J-Δ_i) ⪰ 0` for all `i`. -/
def advStar {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      ∀ j, ((1 : Matrix X X ℂ) -
              Γ ⊙ (gramFilterAllOnes - sourceAlphabetDelta input j)).PosSemidef ∧
           ((1 : Matrix X X ℂ) +
              Γ ⊙ (gramFilterAllOnes - sourceAlphabetDelta input j)).PosSemidef},
    ENNReal.ofReal ‖Γ.1 ⊙ (gramFilterAllOnes - σ)‖

/-- The data of a multiplicative-adversary witness of Definition 3.5 (p.8):
a ratio bound `c > 1`, a positive definite matrix `Γ`, and a unit vector `v`. -/
structure MultiplicativeWitness (X : Type) where
  c : ℝ
  Γ : Matrix X X ℂ
  v : X → ℂ

/-- The linear form `v† (Γ ∘ σ) v = Tr((Γ∘σ) vv*)` appearing in the objective of
Definition 3.5 (p.8). -/
def gramQuadForm {X : Type} [Fintype X] (A : Matrix X X ℂ) (v : X → ℂ) : ℝ :=
  (∑ x, ∑ y, star (v x) * A x y * v y).re

/-- The multiplicative adversary `Madv(σ)` of Definition 3.5 (p.8):
`sup_{c>1, Γ≻0, ‖v‖=1} ln(Tr((Γ∘σ)vv*)) / ln c`, subject to
`c⁻¹Γ ⪯ Γ ∘ Δ_i ⪯ cΓ` for all `i`. -/
def madv {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨆ w : {w : MultiplicativeWitness X //
      1 < w.c ∧ w.Γ.PosDef ∧ (∑ x, ‖w.v x‖ ^ 2) = 1 ∧
      ∀ j, ((w.c)⁻¹ • w.Γ - w.Γ ⊙ sourceAlphabetDelta input j).PosSemidef ∧
           (w.Γ ⊙ sourceAlphabetDelta input j - w.c • w.Γ).PosSemidef},
    ENNReal.ofReal (Real.log (gramQuadForm (w.1.Γ ⊙ σ) w.1.v) / Real.log w.1.c)

/-- The paper's `d = γ₂(J-σ)⁻¹ Adv*(σ)` of Theorem 4.1 (p.14), read as a real
number through `ENNReal.toReal` (the product is finite for the problems of the paper). -/
def paperD {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (σ : Matrix X X ℂ) : ℝ :=
  (((gamma2 (gramFilterAllOnes - σ))⁻¹ * advStar input σ)).toReal

/-- Binary relative entropy `D(λ‖μ)` of Definition 2.2 (p.4).  Lean's
`Real.log 0 = 0` implements the paper's convention `0 ln 0 = 0`. -/
def binaryRelEntropy (lam mu : ℝ) : ℝ :=
  lam * Real.log (lam / mu) + (1 - lam) * Real.log ((1 - lam) / (1 - mu))

/-- `Pr` is the output distribution of a `T`-query algorithm for `f^{(k)}` whose
final measurement produces a `k`-tuple of Boolean outputs (Theorem 5.5, p.15).
The algorithm is a legal counted query word over the `k·n`-coordinate product
oracle, and `Pr xs o` is the probability of reading output tuple `o` on input
`xs`. -/
def IsTQueryOutputDistribution {X : Type} [Fintype X] [DecidableEq X]
    {n q k : ℕ} (input : X → Fin n → Fin (q+1)) (T : ℕ)
    (Pr : (Fin k → X) → (Fin k → Bool) → ℝ) : Prop :=
  ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace (k * n) q (Fin k → Bool) r)),
    sourceWordCalls C ≤ T ∧ sourceWordLegal C ∧
    ∀ xs o, Pr xs o = MeasureProb
      (sourceWordMatrix (sourceAlphabetOracle (prodInput (k := k) input) xs) C *ᵥ
        sourceClean (k * n) q r hr false (Ket (fun _ => false)))
      (Finset.univ.filter (fun p => p.2.1.2 = o))

end Qatlib.Papers.QDirectProd11.MainResults.Model
