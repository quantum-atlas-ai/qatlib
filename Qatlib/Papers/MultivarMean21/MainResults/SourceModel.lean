/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared vocabulary for the paper layer of MultivarMean21

Fixed source: arXiv:2111.09787 (A. Cornelissen and S. Jerbi, *Near-Optimal Quantum
Algorithms for Multivariate Mean Estimation*, 2021).  Statements below quote the page
numbers of the fixed PDF (`2111.09787.pdf`, 2021-11 submission, 32 pages).

This module fixes the notation shared by every claim file of the `MainResults` block:

* `Vec d`, the `ℓp` norms of Definition 2.1 (p. 6), and the truncation `⟦x⟧_a^b`;
* `FinRV d`, the *finite* random variables of Definition 2.2 (p. 6): a finite sample set
  `Ω`, a probability mass function `P`, and the value map `X : Ω → ℝ^d`, together with
  the mean `FinRV.mean` and the covariance trace `Tr Σ = E‖X‖² − ‖E X‖²`;
* the grid `G` of Section 3.1 (p. 9), whose points are modelled by the uniform product
  distribution over `Fin d → Fin m`;
* `OracleBudget`, the query/experiment budget of the paper's input models
  (Definitions 2.5–2.7, pp. 6–7);
* `Estimator`, a query-bounded mean estimator interface, and `successProb`, the success
  probability of its (uniformly sampled) internal randomness;
* `SoftOLe`-style asymptotic vocabulary for the paper's `Õ`/`Õ(log²)` bounds.

## Boundary

The paper states its algorithms as quantum circuits acting on `H_G ⊗ H_Ω ⊗ H_aux` and
counts calls to the unitaries `U_P` (Definition 2.5) and `B_X` / `P_X`
(Definitions 2.6–2.7).  This paper layer deliberately does *not* rebuild the unitary
circuit model: `Estimator.cost` records the query/experiment budget that the paper's
algorithm achieves, and the guarantee is stated as a probability bound on the output law
of the estimator.  This is the same interface-level treatment used by other high-level
paper blocks of this repository; it keeps the source constants and the input-model
distinction (`B_X` versus `P_X` versus `U_P`) while leaving circuit synthesis to the
`Concepts`/`Foundations` layers.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MultivarMean21.MainResults

open scoped BigOperators

/-! ## Definition 2.1: norms and truncation (p. 6) -/

/-- A real `d`-vector, written as a function on `Fin d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The `ℓ∞` norm of Definition 2.1: `max_i |x_i|` (and `0` when `d = 0`). -/
noncomputable def linf {d : ℕ} (v : Vec d) : ℝ :=
  (Finset.univ : Finset (Fin d)).fold max 0 (fun i => |v i|)

/-- The `ℓ1` norm of Definition 2.1. -/
noncomputable def l1Nat {d : ℕ} (v : Vec d) : ℝ :=
  ∑ i, |v i|

/-- The `ℓ2` (Euclidean) norm of Definition 2.1. -/
noncomputable def l2Nat {d : ℕ} (v : Vec d) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

/-- The `ℓp` norm of Definition 2.1 for real `p ≥ 1`. -/
noncomputable def lpNat {d : ℕ} (p : ℝ) (v : Vec d) : ℝ :=
  (∑ i, |v i| ^ p) ^ (1 / p)

/-- The scalar truncation of Definition 2.1 (p. 6): keep `z` if `0 < z ≤ 1`, else `0`. -/
def truncScalar01 (z : ℝ) : ℝ :=
  if 0 < z ∧ z ≤ 1 then z else 0

/-- The paper's vector truncation `⟦x⟧_a^b` (above Definition 2.2, p. 6): keep `x` iff
`a < ‖x‖₂ ≤ b`, and output `0` otherwise. -/
noncomputable def truncVec {d : ℕ} (a b : ℝ) (x : Vec d) : Vec d :=
  if a < l2Nat x ∧ l2Nat x ≤ b then x else 0

/-- The `ℓ∞` estimation error `‖v − w‖∞`. -/
noncomputable def linfErr {d : ℕ} (v w : Vec d) : ℝ := linf (fun i => v i - w i)

/-- The `ℓ2` estimation error `‖v − w‖₂`. -/
noncomputable def l2Err {d : ℕ} (v w : Vec d) : ℝ := l2Nat (fun i => v i - w i)

/-- The `ℓ1` estimation error `‖v − w‖₁`. -/
noncomputable def l1Err {d : ℕ} (v w : Vec d) : ℝ := l1Nat (fun i => v i - w i)

/-- Uniform probability of a predicate over a finite seed set (the internal randomness of an
algorithm). -/
noncomputable def unifProb {S : Type} [Fintype S] (p : S → Prop) : ℝ :=
  letI := Classical.decPred p
  ∑ s, (Fintype.card S : ℝ)⁻¹ * if p s then 1 else 0

/-! ## Definition 2.2: finite random variables (p. 6) -/

/-- A *finite* random variable `X : Ω → ℝ^d` on a finite probability space, exactly as in
Definition 2.2: `Ω` is a finite sample set, `P` is a probability mass function, and
`X` is its value map. -/
structure FinRV (d : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  [decEq : DecidableEq Ω]
  /-- The probability mass function `P : Ω → [0,1]`. -/
  P : Ω → ℝ
  P_nonneg : ∀ ω, 0 ≤ P ω
  P_sum : ∑ ω, P ω = 1
  /-- The value map `X : Ω → ℝ^d`. -/
  X : Ω → Vec d

attribute [instance] FinRV.fintype FinRV.decEq

namespace FinRV

/-- The mean `μ = E[X]` of Definition 2.2. -/
noncomputable def mean {d : ℕ} (r : FinRV d) : Vec d :=
  fun i => ∑ ω, r.P ω * r.X ω i

/-- The covariance matrix of Definition 2.2, `Σ = E[X Xᵀ] − E[X] E[X]ᵀ`. -/
noncomputable def covMatrix {d : ℕ} (r : FinRV d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ ω, r.P ω * (r.X ω i * r.X ω j)) - r.mean i * r.mean j

/-- The covariance trace `Tr Σ = E‖X‖² − ‖E X‖²`. -/
noncomputable def trCov {d : ℕ} (r : FinRV d) : ℝ :=
  (∑ ω, r.P ω * ∑ i, (r.X ω i) ^ 2) - ∑ i, (r.mean i) ^ 2

/-- The spectral norm `‖Σ‖` of the covariance matrix: the supremum of `‖Σv‖₂` over unit
vectors `v` (Definition 2.1's induced `ℓ2` matrix norm). -/
noncomputable def covOpNorm {d : ℕ} (r : FinRV d) : ℝ :=
  sSup {t : ℝ | ∃ v : Vec d,
    l2Nat v = 1 ∧ t = l2Nat (fun i => ∑ j, r.covMatrix i j * v j)}

/-- `X` takes values in the box `[−B, B]^d` (the paper's `‖X‖₂ ≤ 1` case is `B = 1/4`
for the `[−1/4,1/4]^d` model of Section 4, p. 15). -/
def InBox {d : ℕ} (r : FinRV d) (B : ℝ) : Prop :=
  ∀ ω i, |r.X ω i| ≤ B

/-- The boundedness hypothesis `‖X(ω)‖₂ ≤ 1` of Section 3 (p. 9). -/
def BoundedL2 {d : ℕ} (r : FinRV d) : Prop :=
  ∀ ω, l2Nat (r.X ω) ≤ 1

/-- The second-moment hypothesis `E‖X‖₂² ≤ L2` of Section 3 (p. 9). -/
def secondMoment {d : ℕ} (r : FinRV d) : ℝ :=
  ∑ ω, r.P ω * (l2Nat (r.X ω)) ^ 2

/-- The expectation `E‖X‖₂` of the norm (the quantity written `E[‖X‖₂]` in Lemma 3.1). -/
noncomputable def expectedNorm {d : ℕ} (r : FinRV d) : ℝ :=
  ∑ ω, r.P ω * l2Nat (r.X ω)

/-- The mean of the univariate variable `⟦α⟨u,X⟩⟧_0^1` appearing in Proposition 3.2. -/
noncomputable def truncatedDirectionalMean {d : ℕ} (r : FinRV d) (α : ℝ) (u : Vec d) : ℝ :=
  ∑ ω, r.P ω * truncScalar01 (α * ∑ i, u i * r.X ω i)

/-- The expectation `E[|⟨u,X⟩|]` appearing in the second part of Lemma 3.1. -/
noncomputable def absDirectionalMean {d : ℕ} (r : FinRV d) (u : Vec d) : ℝ :=
  ∑ ω, r.P ω * |∑ i, u i * r.X ω i|

end FinRV

/-! ## The grid `G` of Section 3.1 (p. 9) -/

/-- The `j`-th point of the one-dimensional grid `{j/m − 1/2 + 1/(2m) : j = 0,…,m−1}`. -/
def gridCoord (m : ℕ) (j : Fin m) : ℝ :=
  (j : ℝ) / m - 1 / 2 + 1 / (2 * m)

/-- The uniform weight `1/m^d` of a grid point under `u ∼ G`. -/
def gridWeight (d m : ℕ) : ℝ := ((m : ℝ) ^ d)⁻¹

/-- The grid point indexed by `j : Fin d → Fin m`: its `i`-th coordinate is
`j_i/m − 1/2 + 1/(2m)`. -/
def gridPoint (d m : ℕ) (j : Fin d → Fin m) : Vec d := fun i => gridCoord m (j i)

/-- The probability of a predicate `p` under `u ∼ G`, i.e. the uniform distribution over the
grid `G` of Section 3.1 (p. 9). -/
noncomputable def gridProb (d m : ℕ) (p : Vec d → Prop) : ℝ :=
  letI := Classical.decPred p
  ∑ j : Fin d → Fin m, gridWeight d m * if p (gridPoint d m j) then 1 else 0

/-! ## Input-model budgets (Definitions 2.5–2.7, pp. 6–7) -/

/-- The query/experiment budget of an estimator: `experiments` calls to the probability
oracle `U_P` (Definition 2.5) and `queries` calls to the value oracle (`B_X` in the binary
model, Definition 2.6, or `P_X` in the phase model, Definition 2.7). -/
structure OracleBudget where
  experiments : ℕ
  queries : ℕ

/-- The parameters `(L₂, n, δ)` of the bounded multivariate estimator of Algorithm 1
(Theorem 3.3, p. 10). -/
structure BoundedParams where
  /-- The upper bound `L₂` on `E‖X‖₂`. -/
  L2 : ℝ
  /-- The number `n` of binary oracle queries. -/
  n : ℕ
  /-- The failure probability `δ`. -/
  δ : ℝ

/-- The parameters `(n, δ)` of the near-optimal estimators of Theorems 3.4 and 3.5. -/
structure SampleParams where
  /-- The number `n` of binary oracle queries. -/
  n : ℕ
  /-- The failure probability `δ`. -/
  δ : ℝ

/-- The parameters `(n, n', δ)` of the phase-oracle estimators of Theorems 4.3--4.5: `n` calls
to `U_P` and `n'` calls to `P_X`. -/
structure PhaseParams where
  /-- The number `n` of queries to the probability oracle `U_P`. -/
  n : ℕ
  /-- The number `n'` of queries to the phase oracle `P_X`. -/
  n' : ℕ
  /-- The failure probability `δ`. -/
  δ : ℝ

/-- A mean-estimation algorithm with a finite internal random seed.  `run r p s` is the
output on the finite random variable `r`, the numerical parameters `p`, and the internal
seed `s`; `cost p` is the oracle budget the algorithm uses at parameters `p`. -/
structure Estimator (d : ℕ) (Params : Type) where
  seed : Type
  [fintype : Fintype seed]
  [nonempty : Nonempty seed]
  run : FinRV d → Params → seed → Vec d
  cost : Params → OracleBudget

attribute [instance] Estimator.fintype Estimator.nonempty

namespace Estimator

/-- The success probability of an estimator on input `r` at parameters `p`, for the event
`good`: the uniform average of the indicator of `good` over the internal seed. -/
def successProb {d : ℕ} {Params : Type} (E : Estimator d Params) (r : FinRV d)
    (p : Params) (good : Vec d → Prop) : ℝ :=
  letI := Classical.decPred good
  ∑ s : E.seed, (Fintype.card E.seed : ℝ)⁻¹ * if good (E.run r p s) then 1 else 0

/-- The failure probability, `1 − successProb`. -/
def failProb {d : ℕ} {Params : Type} (E : Estimator d Params) (r : FinRV d)
    (p : Params) (good : Vec d → Prop) : ℝ :=
  1 - E.successProb r p good

end Estimator

/-! ## Asymptotic vocabulary (`Õ`) -/

/-- `cost = Õ(base · logᵉ(arg))`: up to a positive constant and extra polylogarithmic
factors in `arg`, `cost` is at most `base` times `e` explicit logarithmic factors. -/
def SoftOLePow (cost base arg : ℝ) (e : ℕ := 1) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, cost ≤ C * base * (Real.log (arg + 2)) ^ (k + e)

/-- `cost = Õ(base)` with the polylog taken in `arg`. -/
def SoftOLe (cost base arg : ℝ) : Prop := SoftOLePow cost base arg 1

/-- `cost = Õ(base · log²(arg))`: the two explicit logarithmic factors of the paper's
`Õ(… log²(1/ε))` bounds are kept. -/
def SoftOLeLogSq (cost base arg : ℝ) : Prop := SoftOLePow cost base arg 2

/-- `cost = Õ(base · log²(arg))` where the polylog is allowed in two separate positive
parameters `a` and `b` (e.g. the grid size `m` and `1/ε`). -/
def SoftOLeLogSq2 (cost base a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    cost ≤ C * base * (Real.log (a + 2)) ^ (k + 1) * (Real.log (b + 2)) ^ (k + 2)

/-- `cost = Õ(base)` where the polylog is allowed in two separate positive parameters. -/
def SoftOLe2 (cost base a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    cost ≤ C * base * (Real.log (a + 2)) ^ (k + 1) * (Real.log (b + 2)) ^ (k + 1)

/-- `cost = Õ(base)` where the polylog is allowed in three separate positive parameters
(typically the dimension `d` and the confidence `1/δ`, with `c = 2` a harmless filler). -/
def SoftOLeMulti (cost base a b c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    cost ≤ C * base * (Real.log (a + 2)) ^ (k + 1) * (Real.log (b + 2)) ^ (k + 1) *
      (Real.log (c + 2)) ^ (k + 1)

/-- `err ≥ Ω(scale)`: some positive absolute constant times `scale` bounds `err` from
below.  The constant is allowed to depend on the paper's fixed constants (`α`, `c`). -/
def BigOmegaGe (err scale : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ C * scale ≤ err

/-! ## Phase-encoding oracles (used by Proposition 3.2 and Lemmas 4.1–4.2) -/

/-- The squared `ℓ2` distance between two unit vectors in an auxiliary register
`Fin N → ℂ`.  The paper writes `‖|φ⟩ − |ψ⟩‖`; squaring keeps the statement in `ℝ`. -/
noncomputable def stateDistSq {N : ℕ} (φ ψ : Fin N → ℂ) : ℝ :=
  ∑ j, ‖φ j - ψ j‖ ^ 2

/-- The target phase state `θ ↦ e^{iθ}|0̃⟩` in an auxiliary register `Fin N → ℂ`. -/
noncomputable def targetPhaseState (N : ℕ) (θ : ℝ) : Fin N → ℂ :=
  fun j => if j.val = 0 then Complex.exp (Complex.I * θ) else 0

/-- A family of phase-encoding states produced by a directional oracle, with its oracle
budget.  `state u` is the auxiliary state prepared on grid point `u`. -/
structure PhaseEncoding (d : ℕ) where
  N : ℕ
  state : Vec d → Fin N → ℂ
  experiments : ℕ
  queries : ℕ

/-- A family of phase-encoding states indexed additionally by a sample `ω` of the random
variable, as in Lemma 4.1 (`L_{X,m,ε} : |u⟩|ω⟩|0̃⟩ ↦ |u⟩|ω⟩|φ_{u,ω}⟩`). -/
structure SamplePhaseEncoding (d : ℕ) (Ω : Type) where
  N : ℕ
  state : Ω → Vec d → Fin N → ℂ
  queries : ℕ

/-! ## Search_N ∘ Parity_M (Problem 1, p. 13) and bit-recovery algorithms -/

/-- Hamming weight of row `i` of a `N × M` Boolean matrix. -/
def rowWeight {N M : ℕ} (a : Fin N × Fin M → Bool) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j : Fin M => a (i, j))).card

/-- The target vector `b(A)` of Problem 1: `0` on rows of Hamming weight `⌊M/2⌋`, `1` on
rows of Hamming weight `⌊M/2⌋ + 1`. -/
noncomputable def bVector {N M : ℕ} (a : Fin N × Fin M → Bool) (i : Fin N) : ℝ :=
  if rowWeight a i = M / 2 then 0 else 1

/-- The input set `𝒜_{N,M}` of Problem 1 (p. 13): every row of `A` has Hamming weight
`⌊M/2⌋` or `⌊M/2⌋ + 1`, and exactly `⌊N/2⌋` rows have weight `⌊M/2⌋`. -/
def IsSearchParityInstance {N M : ℕ} (a : Fin N × Fin M → Bool) : Prop :=
  (∀ i, rowWeight a i = M / 2 ∨ rowWeight a i = M / 2 + 1) ∧
  (Finset.univ.filter (fun i : Fin N => rowWeight a i = M / 2)).card = N / 2

/-- A quantum algorithm for `Search_N ∘ Parity_M`: `run a s` is the output vector on the
oracle matrix `a`, with internal seed `s`; `queries` is its worst-case query count. -/
structure MatrixQueryAlgorithm (N M : ℕ) where
  seed : Type
  [fintype : Fintype seed]
  [nonempty : Nonempty seed]
  run : (Fin N × Fin M → Bool) → seed → Vec N
  queries : ℕ

attribute [instance] MatrixQueryAlgorithm.fintype MatrixQueryAlgorithm.nonempty

/-- A bit-recovery algorithm with oracle access to `b : Fin d → Bool` (through the
fractional phase oracle `F_ε` of Lemma 4.6, or its Hadamard variant of Lemma 4.8). -/
structure BitRecoveryAlgorithm (d : ℕ) where
  seed : Type
  [fintype : Fintype seed]
  [nonempty : Nonempty seed]
  run : (Fin d → Bool) → seed → (Fin d → Bool)
  queries : ℕ

attribute [instance] BitRecoveryAlgorithm.fintype BitRecoveryAlgorithm.nonempty

/-- The `ℓ1` distance between the bit vectors induced by two Boolean strings. -/
noncomputable def bitL1Dist {d : ℕ} (b b' : Fin d → Bool) : ℝ :=
  ∑ i, |(if b' i then (1 : ℝ) else 0) - (if b i then (1 : ℝ) else 0)|

/-- `‖H(b̃ − b)‖₁` for a `d × d` matrix `H`: the error measure of Lemma 4.8. -/
noncomputable def hadamardL1Dist {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b b' : Fin d → Bool) : ℝ :=
  ∑ i, |∑ j, H i j * ((if b' j then (1 : ℝ) else 0) - (if b j then (1 : ℝ) else 0))|

/-- A `d`-dimensional normalized Hadamard matrix (Lemma 4.8, p. 25): every entry is `±1/√d`
(encoded as `H i j ^ 2 = 1/d`) and `Hᵀ H = I`. -/
def IsHadamard {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, H i j ^ 2 = ((d : ℝ))⁻¹) ∧ H.transpose * H = 1

/-- The piecewise `ℓ1` lower-bound scale of Theorem 4.10 (p. 27):
`d` if `n' < d`, `max{d/√n, d²/n'}` if `n' ≥ d and n < d`, and
`max{d^{3/2}/n, d²/n'}` if `n' ≥ d and n ≥ d`. -/
noncomputable def l1LowerBound (d n n' : ℕ) : ℝ :=
  if n' < d then (d : ℝ)
  else if (n : ℝ) < (d : ℝ) then
    max ((d : ℝ) / Real.sqrt (n : ℝ)) ((d : ℝ) ^ 2 / (n' : ℝ))
  else
    max ((d : ℝ) ^ ((3 : ℝ) / 2) / (n : ℝ)) ((d : ℝ) ^ 2 / (n' : ℝ))

end Qatlib.Papers.MultivarMean21.MainResults
