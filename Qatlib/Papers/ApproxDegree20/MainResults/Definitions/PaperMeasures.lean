/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-layer measures for ABKRT 2020 (`ApproxDegree20`)

Source: arXiv:2010.12629v1, *Degree vs. Approximate Degree and Quantum
Implications of Huang's Sensitivity Theorem* (Aaronson, Ben-David, Kothari,
Rao, Tal).  This module fixes every measure that the paper's statements
mention but that the frozen library does not already provide.

Reuse from the frozen library:
* `QuantumAlgorithm.Concepts.QueryComplexity.DegreeMethod.exactDegree`
  (`deg`, Beals et al. 2001 §3.1) and `approxDegree` (`deg~`, the `1/3`
  version);
* `TriangleQuery.DegreeBounds.spectralSensitivity`
  (`λ`, paper Definition 7, page 6) and `sensAdjacency`.

New here:
* `hamDist`, `weight`, `flipBit` — Hamming-cube vocabulary;
* `hadamard`, `diagFun`, `posWeight` — the matrices `H`, `diag(g)`, `X` of
  Section 4 (pages 8–9);
* `fourierCoeff` — `ĝ` of Lemma 12 (page 9);
* `approxDegreeAt` — the paper's own `ε`-approximate degree convention
  `[1−2ε,1] / [−1,−1+2ε]` (Section 4.3, page 13), while the frozen
  `approxDegree` is the `1/3` version used in the introduction;
* `sensitivityAt`, `sensitivity`, `s0`, `s1`, `avgSensitivity` — paper §2.2 and
  Appendix A.3/A.4;
* `PBF` (partial Boolean function), `pSensAdj`, `pLambda`, and the partial
  variants of the sensitivity/adversary measures used in Appendix A
  (`K`, `Adv₁`, `Adv₁±`, `SWA₁`, `MM₁`, `GSA₁`);
* `colMax`, `gamma2` — Definition 21 (page 14);
* `ReadOnceFormula` — read-once De Morgan formulas of Section 6 (page 18).

Boundary: all measures are stated over an arbitrary finite coordinate type
`I`; the paper's `{0,1}^n` is recovered with `I = Fin n`.  Big-O statements in
the paper are rendered as explicit existential constants.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxDegree20.MainResults.Definitions

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds (spectralSensitivity sensAdjacency)
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## Hamming-cube vocabulary -/

/-- Hamming weight `|x|` of a Boolean string. -/
def weight (x : I → Bool) : ℕ := (Finset.univ.filter (fun i => x i)).card

/-- Hamming distance `|x ⊕ y|`. -/
def hamDist (x y : I → Bool) : ℕ := (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- Flip the `i`-th coordinate. -/
def flipBit (x : I → Bool) (i : I) : I → Bool := Function.update x i (!(x i))

/-- Maximum of `g` over a finite set, as an element of `ℝ`. -/
def maxOver {α : Type} (s : Finset α) (g : α → ℝ) : ℝ := sSup (g '' s)

/-! ## Section 4 matrices: `H`, `diag(·)`, `X`, and the Fourier transform -/

/-- Boolean inner product `⟨x,y⟩ = Σᵢ xᵢyᵢ` (as a natural number). -/
def boolInner (x y : I → Bool) : ℕ :=
  ∑ i, if x i ∧ y i then (1 : ℕ) else 0

/-- The Hadamard matrix `H` of page 8: `H_xy = (−1)^{⟨x,y⟩}·2^{−n/2}`. -/
def hadamard : Matrix (I → Bool) (I → Bool) ℝ :=
  fun x y => (-1 : ℝ) ^ boolInner x y / Real.sqrt ((2 : ℝ) ^ Fintype.card I)

/-- Diagonal matrix of a real function, `diag(g)`. -/
def diagFun (g : (I → Bool) → ℝ) : Matrix (I → Bool) (I → Bool) ℝ :=
  Matrix.diagonal g

/-- The diagonal matrix `X` with `X_xx = |x|` (page 8). -/
def posWeight : Matrix (I → Bool) (I → Bool) ℝ :=
  Matrix.diagonal (fun x => (weight x : ℝ))

/-- Fourier coefficient `ĝ(z) = 2^{−n} Σ_y (−1)^{⟨z,y⟩} g(y)` (Lemma 12, page 9). -/
def fourierCoeff (g : (I → Bool) → ℝ) (z : I → Bool) : ℝ :=
  (1 / (2 : ℝ) ^ Fintype.card I) * ∑ y, (-1 : ℝ) ^ boolInner z y * g y

/-- Pointwise XOR of Boolean strings. -/
def xorStr (x y : I → Bool) : I → Bool := fun i => x i ≠ y i

/-- The matrix `W_xy = |x| − |y|` of page 14. -/
def Wmat : Matrix (I → Bool) (I → Bool) ℝ := fun x y => (weight x : ℝ) - (weight y : ℝ)

/-- `R̃ = H diag(q) H` of Lemma 16/Lemma 20. -/
def Rq (q : (I → Bool) → ℝ) : Matrix (I → Bool) (I → Bool) ℝ :=
  hadamard * diagFun q * hadamard

/-- `R = H diag(g) H` for `g = 1 − 2f` (Lemma 11, page 8). -/
def Rmat (f : (I → Bool) → Bool) : Matrix (I → Bool) (I → Bool) ℝ :=
  Rq (fun x => 1 - 2 * (if f x then (1 : ℝ) else 0))

/-- The matrix `Bq` of Eq. (41), page 13: `(Bq)_xy = (q x − q y)/2` on hypercube
edges and `0` elsewhere. -/
def Bq (q : (I → Bool) → ℝ) : Matrix (I → Bool) (I → Bool) ℝ :=
  fun x y => if hamDist x y = 1 then (q x - q y) / 2 else 0

/-- Induced `1`-norm `‖A‖₁`: maximum absolute column sum (page 30). -/
def l1OpNorm {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  maxOver Finset.univ (fun j => ∑ i, |A i j|)

/-- Induced `∞`-norm `‖A‖∞`: maximum absolute row sum (page 30). -/
def linftyOpNorm {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  maxOver Finset.univ (fun i => ∑ j, |A i j|)

/-! ## The paper's `ε`-approximate degree (Section 4.3, page 13)

`deg~_ε(f)` is the least total degree of `q` with
`f(x)=1 ⇒ q(x) ∈ [1−2ε, 1]` and `f(x)=0 ⇒ q(x) ∈ [−1, −1+2ε]`.
Compare the frozen `approxDegree`, which is the `ε = 1/3` acceptance version. -/

/-- Paper's `ε`-approximate degree (page 13, §4.3). -/
noncomputable def approxDegreeAt (ε : ℝ) (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ x : I → Bool,
      (f x = true → 1 - 2 * ε ≤ boolEval p x ∧ boolEval p x ≤ 1) ∧
      (f x = false → -1 ≤ boolEval p x ∧ boolEval p x ≤ -1 + 2 * ε)})

/-! ## Sensitivity measures (paper §2.2, pages 6 and 32) -/

/-- Coordinates `i` for which flipping `x` at `i` changes `f`. -/
def sensitiveAt (f : (I → Bool) → Bool) (x : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => f (flipBit x i) ≠ f x)

/-- Vertex sensitivity `s_x(f)`. -/
def sensitivityAt (f : (I → Bool) → Bool) (x : I → Bool) : ℕ := (sensitiveAt f x).card

/-- Maximum sensitivity `s(f)`. -/
def sensitivity (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (fun x => sensitivityAt f x)

/-- One-sided sensitivity `s₀(f)`: maximum sensitivity over `0`-inputs. -/
def s0 (f : (I → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = false)).sup (fun x => sensitivityAt f x)

/-- One-sided sensitivity `s₁(f)`: maximum sensitivity over `1`-inputs. -/
def s1 (f : (I → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = true)).sup (fun x => sensitivityAt f x)

/-- Average sensitivity `E_x[s_x(f)]` of Lemma 35 (page 32). -/
def avgSensitivity (f : (I → Bool) → Bool) : ℝ :=
  (∑ x, (sensitivityAt f x : ℝ)) / (Fintype.card (I → Bool) : ℝ)

/-! ## Partial Boolean functions and their measures (Appendix A) -/

/-- A possibly partial Boolean function on the cube `I → Bool`.  The domain is
a finite set, as it is in the paper (a subset of the cube). -/
structure PBF (I : Type) where
  /-- the (finite) domain of definition -/
  dom : Finset (I → Bool)
  /-- the Boolean value on the domain -/
  fn : (I → Bool) → Bool

/-- Sensitivity-graph adjacency of a partial function: edges between domain
points at Hamming distance one on which the value changes. -/
def pSensAdj (F : PBF I) : Matrix (I → Bool) (I → Bool) ℝ :=
  fun x y =>
    if x ∈ F.dom ∧ y ∈ F.dom ∧ hamDist x y = 1 ∧ F.fn x ≠ F.fn y then 1 else 0

/-- **`λ(f)` for a partial function**: spectral norm of the sensitivity graph. -/
def pLambda (F : PBF I) : ℝ := ‖pSensAdj F‖

/-- Vertex sensitivity of a partial function (only domain neighbours count). -/
def pSensAt (F : PBF I) (x : I → Bool) : ℕ :=
  (Finset.univ.filter
    (fun i => flipBit x i ∈ F.dom ∧ F.fn (flipBit x i) ≠ F.fn x)).card

/-- Maximum sensitivity `s(f)` of a partial function. -/
def pSensitivity (F : PBF I) : ℕ := F.dom.sup (fun x => pSensAt F x)

/-- One-sided sensitivity `s₀(f)` of a partial function. -/
def pS0 (F : PBF I) : ℕ :=
  (F.dom.filter (fun x => F.fn x = false)).sup (fun x => pSensAt F x)

/-- One-sided sensitivity `s₁(f)` of a partial function. -/
def pS1 (F : PBF I) : ℕ :=
  (F.dom.filter (fun x => F.fn x = true)).sup (fun x => pSensAt F x)

/-- Average sensitivity `E_x[s_x(f)]` over the domain. -/
def pAvgSens (F : PBF I) : ℝ :=
  (∑ x ∈ F.dom, (pSensAt F x : ℝ)) / (F.dom.card : ℝ)

/-- Filtering a matrix by query direction `i`. -/
def dirFilter (i : I) (Γ : Matrix (I → Bool) (I → Bool) ℝ) :
    Matrix (I → Bool) (I → Bool) ℝ :=
  fun x y => if x i ≠ y i then Γ x y else 0

/-- Feasible single-bit spectral-adversary matrices (paper Definition in
Appendix A.1, page 25): nonnegative, supported on domain pairs with different
values at Hamming distance one, not all zero. -/
def IsSpectralAdversary (F : PBF I) (Γ : Matrix (I → Bool) (I → Bool) ℝ) : Prop :=
  (∀ x y, 0 ≤ Γ x y) ∧
  (∀ x y, (x ∉ F.dom ∨ y ∉ F.dom ∨ F.fn x = F.fn y) → Γ x y = 0) ∧
  (∀ x y, hamDist x y ≠ 1 → Γ x y = 0) ∧
  Γ ≠ 0

/-- `Adv₁(f)` in the spectral form `SA₁(f)` (page 25): maximum of
`‖Γ‖ / max_i ‖Γ ∘ D_i‖` over feasible adversary matrices. -/
def pAdv1 (F : PBF I) : ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (I → Bool) (I → Bool) ℝ,
    IsSpectralAdversary F Γ ∧
    r = ‖Γ‖ / (maxOver Finset.univ (fun i => ‖dirFilter i Γ‖))}

/-- `Adv₁±(f)`: the negative-entry relaxation (page 26). -/
def pAdv1Neg (F : PBF I) : ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (I → Bool) (I → Bool) ℝ,
    (∀ x y, (x ∉ F.dom ∨ y ∉ F.dom ∨ F.fn x = F.fn y) → Γ x y = 0) ∧
    (∀ x y, hamDist x y ≠ 1 → Γ x y = 0) ∧
    Γ ≠ 0 ∧
    r = ‖Γ‖ / (maxOver Finset.univ (fun i => ‖dirFilter i Γ‖))}

/-- Koutsoupias complexity `K(f)` (page 25): maximum spectral norm of the
Hamming-distance-one bipartite matrix between a set of `0`-inputs and a set of
`1`-inputs. -/
def pK (F : PBF I) : ℝ :=
  sSup {r : ℝ | ∃ A B : Finset (I → Bool),
    (∀ x ∈ A, x ∈ F.dom ∧ F.fn x = false) ∧
    (∀ y ∈ B, y ∈ F.dom ∧ F.fn y = true) ∧
    r = ‖(fun x y => if hamDist (x : I → Bool) y = 1 then (1 : ℝ) else 0 :
          Matrix A B ℝ)‖}

/-- `SWA₁(f)` (page 26): the strong weighted adversary value. -/
def pSWA1 (F : PBF I) : ℝ :=
  sSup {r : ℝ | ∃ w : (I → Bool) → (I → Bool) → ℝ,
    (∀ x y, 0 ≤ w x y) ∧
    (∀ x y, w x y = w y x) ∧
    (∀ x y, (x ∉ F.dom ∨ y ∉ F.dom ∨ F.fn x = F.fn y ∨ hamDist x y ≠ 1) →
      w x y = 0) ∧
    r = sInf {q : ℝ | ∃ x : I → Bool, ∃ i : I,
      0 < w x (flipBit x i) ∧
      q = Real.sqrt ((∑ y, w x y) * (∑ y, w (flipBit x i) y)) / w x (flipBit x i)}}

/-- `MM₁(f)` (page 26): the minimax adversary value. -/
def pMM1 (F : PBF I) : ℝ :=
  sInf {r : ℝ | ∃ w : (I → Bool) → I → ℝ,
    (∀ x, x ∈ F.dom → ∀ i, 0 ≤ w x i) ∧
    (∀ x, x ∉ F.dom → ∀ i, w x i = 0) ∧
    (∀ x y i, x ∈ F.dom → y ∈ F.dom → F.fn x ≠ F.fn y → hamDist x y = 1 →
      y = flipBit x i → 1 ≤ w x i * w y i) ∧
    r = maxOver F.dom (fun x => ∑ i, w x i)}

/-- `GSA₁(f)` (page 26): the semidefinite-program value. -/
def pGSA1 (F : PBF I) : ℝ :=
  sSup {r : ℝ | ∃ Z Δ : Matrix (I → Bool) (I → Bool) ℝ,
    (∀ x y, 0 ≤ Z x y) ∧
    (Δ = Matrix.diagonal (fun x => Δ x x)) ∧
    Matrix.trace Δ = 1 ∧
    (∀ x, x ∉ F.dom → Δ x x = 0) ∧
    (∀ x y, (x ∉ F.dom ∨ y ∉ F.dom) → Z x y = 0) ∧
    (∀ i, (Δ - Z ⊙ (fun x y => if x i ≠ y i then (1 : ℝ) else 0)).PosSemidef) ∧
    r = ∑ x, ∑ y, Z x y * pSensAdj F x y}

/-- Composition of partial Boolean functions (paper Appendix A.2):
`f ∘ g` on `n` blocks of `m` bits. -/
def compose {n m : ℕ} (F : PBF (Fin n)) (G : PBF (Fin m)) : PBF (Fin n × Fin m) where
  dom := Finset.univ.filter (fun x =>
    (∀ i, (fun j => x (i, j)) ∈ G.dom) ∧
    (fun i => G.fn (fun j => x (i, j))) ∈ F.dom)
  fn := fun x => F.fn (fun i => G.fn (fun j => x (i, j)))

/-! ## γ₂ norm (Definition 21, page 14) -/

/-- Maximum column `ℓ₂` norm `c(X)` (page 14). -/
def colMax {α β : Type} [Fintype α] [Fintype β] (M : Matrix α β ℝ) : ℝ :=
  maxOver Finset.univ (fun j => Real.sqrt (∑ i, (M i j) ^ 2))

/-- The γ₂ norm `γ₂(A) = min_{XᵀY = A} c(X)c(Y)` (Definition 21, page 14). -/
def gamma2 {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  sInf {r : ℝ | ∃ (γ : Type) (_ : Fintype γ) (_ : DecidableEq γ)
    (X : Matrix γ α ℝ) (Y : Matrix γ β ℝ),
    Xᵀ * Y = A ∧ r = @colMax γ α _ _ X * @colMax γ β _ _ Y}

/-! ## Read-once De Morgan formulas (Section 6, page 18) -/

/-- Read-once formulas over the De Morgan basis, with variable names `Var`.
The predicate `WellFormed` below records that the variable sets of the two
children of a conjunction are disjoint, i.e. every variable occurs once. -/
inductive ReadOnceFormula (Var : Type) : Type
  | var : Var → ReadOnceFormula Var
  | neg : ReadOnceFormula Var → ReadOnceFormula Var
  | conj : ReadOnceFormula Var → ReadOnceFormula Var → ReadOnceFormula Var

namespace ReadOnceFormula

variable {Var : Type} [DecidableEq Var]

/-- The set of variables occurring in the formula. -/
def supp : ReadOnceFormula Var → Finset Var
  | .var v => {v}
  | .neg f => f.supp
  | .conj f g => f.supp ∪ g.supp

/-- Every variable occurs exactly once (disjoint children at every `conj`). -/
def WellFormed : ReadOnceFormula Var → Prop
  | .var _ => True
  | .neg f => f.WellFormed
  | .conj f g => f.WellFormed ∧ g.WellFormed ∧ Disjoint f.supp g.supp

/-- Evaluation on a Boolean assignment (AND is `&&`, OR is obtained through
negation, NOT is `!`). -/
def eval (assign : Var → Bool) : ReadOnceFormula Var → Bool
  | .var v => assign v
  | .neg f => !(f.eval assign)
  | .conj f g => f.eval assign && g.eval assign

end ReadOnceFormula

end Qatlib.Papers.ApproxDegree20.MainResults.Definitions
