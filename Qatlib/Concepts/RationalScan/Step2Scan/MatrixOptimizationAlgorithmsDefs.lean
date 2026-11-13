/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Definitions for matrix optimization algorithms

This module supplies the finite-dimensional SDP data, payoff and certificate formulas, sampling
laws, and resource ledgers used by the rational Step 2 development. It also records lifted
feasibility and rescaling conditions and the algebraic budgets used to express the algorithmic
framework of [BrandaoSvore2017].

## Main definitions

* `SdpInstance`: normalized Hermitian SDP data with a distinguished identity constraint.
* `Step2Loop`, `Step2LoopLegal`, and `step2Accepts`: sampled loop data and acceptance
  conditions.
* `dualCertificate` and `MixtureSamplingProcess`: averaged certificates and their mixture
  representations.
* `AlphaBisectionCorrect` and `Lemma2LiftFeasible`: bisection and lifted-problem specifications.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RationalScan.Step2Scan

set_option autoImplicit false

noncomputable section

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The normalized SDP instance conditions: positive dimensions and scale, Hermitian contraction
data, constraint bounds between one and `R`, and a distinguished identity constraint with
bound `R`. -/
def SdpInstance (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (j₀ : Fin m) (R : ℝ) : Prop :=
  0 < D ∧ 0 < m ∧ 0 < R ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i ∧ |b i| ≤ R) ∧
    A j₀ = 1 ∧ b j₀ = R

/-- The source precision parameter `δ/(28*R^2)`. -/
def sourceEps (δ R : ℝ) : ℝ := δ / (28 * R ^ 2)

/-- The distinguished-coordinate certificate offset `δ*α/(2*R)`. -/
def sourceOffset (δ α R : ℝ) : ℝ := δ * α / (2 * R)

/-- The natural ceiling of the source round budget `16*R*log D/(δ*ε)`. -/
def sourceRounds (D : ℕ) (R δ ε : ℝ) : ℕ :=
  Nat.ceil (16 * R * Real.log D / (δ * ε))

/-- The logarithm ratio `log x/log ξ`. -/
def sourceLogBase (ξ x : ℝ) : ℝ := Real.log x / Real.log ξ

/-- The logarithm ratio `log x/log (1+ξ)`. -/
def sourceLogOnePlus (ξ x : ℝ) : ℝ := Real.log x / Real.log (1 + ξ)

/-- The exponential tail `exp (-sourceLogBase ξ (n*m))`. -/
def sourceFailureTail (ξ n m : ℝ) : ℝ := Real.exp (-sourceLogBase ξ (n * m))

/-- The bound `actual ≤ soft*budget` together with the condition `1 ≤ soft`. -/
def SoftOWithin (actual budget soft : ℝ) : Prop :=
  1 ≤ soft ∧ actual ≤ soft * budget

/-- The round payoff obtained by scaling the weighted constraint sum minus `Cv` plus `2*α` times
identity by `1/(4*α)`. -/
def dualPayoff (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ)
    (y : ℕ → Fin m → ℝ) : ℕ → Operator D :=
  fun s => ((4 * α : ℝ))⁻¹ • ((∑ i, y s i • A i) - Cv + (2 * α) • (1 : Operator D))

/-- The average of the first `T` round vectors plus the distinguished-coordinate offset
`δ*α/(2*R)`. -/
def dualCertificate (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun j => (if j = j₀ then δ * α / (2 * R) else 0) + (∑ t ∈ Finset.range T, y t j) / T

/-- The coefficient-weighted objective `∑ i, yBar i*b i` of a certificate. -/
def certificateObjective (m : ℕ) (b : Fin m → ℝ) (yBar : Fin m → ℝ) : ℝ :=
  ∑ i, yBar i * b i

/-- The total mass of a dual certificate vector. -/
def dualSampleScale (m : ℕ) (yBar : Fin m → ℝ) : ℝ := ∑ i, yBar i

/-- The vector obtained by dividing each certificate coordinate by its total mass. -/
def dualSampleDist (m : ℕ) (yBar : Fin m → ℝ) : Fin m → ℝ :=
  fun i => yBar i / dualSampleScale m yBar

/-- The condition that a payoff is Hermitian and lies between zero and identity in the matrix
order. -/
def payoffUnitInterval (D : ℕ) (M : Operator D) : Prop :=
  M.IsHermitian ∧ (0 : Operator D) ≤ M ∧ M ≤ 1

/-- The exact objective width `α`. -/
def widthExact (α : ℝ) : ℝ := α

/-- The sampled objective width `α*(1+2*R*ε)`. -/
def widthSampled (α R ε : ℝ) : ℝ := α * (1 + 2 * R * ε)

/-- The additive width slack `2*R*ε*α`. -/
def widthBridgeSlack (α R ε : ℝ) : ℝ := 2 * R * ε * α

/-- The separation tolerance `2*α*ε`. -/
def separationSlack (α ε : ℝ) : ℝ := 2 * α * ε

/-- The separator threshold `3*α*ε`. -/
def noCheapSlack (α ε : ℝ) : ℝ := 3 * α * ε

/-- The objective threshold `α*(1-3*R*ε)` for the no-cheap-separator condition. -/
def noCheapWidth (α R ε : ℝ) : ℝ := α * (1 - 3 * R * ε)

/-- The condition that a finite vector is nonnegative and has total mass one. -/
def IsSamplingLaw (m : ℕ) (q : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1

/-- The sum of absolute coordinate differences between two finite real vectors. -/
def l1Dist {m : ℕ} (p q : Fin m → ℝ) : ℝ := ∑ i, |p i - q i|

/-- The normalized exponential law with scores combining constraint expectations and bounds at
the Step 2 index `k`. -/
def step2IdealLaw (D m : ℕ) (A : Fin m → Operator D) (b : Fin m → ℝ) (ρ : Operator D)
    (κ R : ℝ) (γ k : ℕ) : Fin m → ℝ :=
  fun i =>
    Real.exp (-(κ / (4 * R ^ 2)) *
      ((k : ℝ) * (Matrix.trace (A i * ρ)).re + ((γ - k : ℕ) : ℝ) * b i)) /
      (∑ j : Fin m,
        Real.exp (-(κ / (4 * R ^ 2)) *
          ((k : ℝ) * (Matrix.trace (A j * ρ)).re + ((γ - k : ℕ) : ℝ) * b j)))

/-- The natural ceiling of the Step 2 outer-loop budget `8*log m*R^2/κ^2`. -/
def step2Gamma (m : ℕ) (κ R : ℝ) : ℕ := Nat.ceil (8 / κ ^ 2 * Real.log m * R ^ 2)

/-- The natural floor of the mass-grid budget `α/κ`. -/
def step2GridMax (α κ : ℝ) : ℕ := Nat.floor (α / κ)

/-- The positive-indexed mass-grid value `κ*(N.val+1)`. -/
def step2Mass (κ : ℝ) {Nmax : ℕ} (N : Fin Nmax) : ℝ := κ * ((N : ℕ) + 1)

/-- The natural ceiling of the prescribed logarithmic draw budget divided by `τ^2`. -/
def step2SampleM (D m : ℕ) (R ξ τ : ℝ) : ℕ :=
  Nat.ceil (80 * sourceLogOnePlus ξ (8 * R ^ 2 * (D : ℝ) * (m : ℝ) / τ) / τ ^ 2)

/-- The natural ceiling of `80*sourceLogOnePlus ξ (D*m)/τ^2` for expectation samples. -/
def step2SampleL (D m : ℕ) (ξ τ : ℝ) : ℕ :=
  Nat.ceil (80 * sourceLogOnePlus ξ ((D : ℝ) * (m : ℝ)) / τ ^ 2)

/-- The finite collection of sampling laws, draws, and constraint and objective estimates
indexed by the Step 2 grid. -/
structure Step2Loop (m γ Nmax M : ℕ) where
  law : Fin γ → Fin m → ℝ
  draws : Fin γ → Fin Nmax → Fin M → Fin m
  estA : Fin γ → Fin Nmax → Fin m → ℝ
  estC : Fin γ → Fin Nmax → ℝ

/-- The conditions that loop laws are normalized and close to the ideal laws in `l1Dist`, and
that all recorded estimates have error at most `ν`. -/
def Step2LoopLegal (D m γ Nmax M : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (L : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  (∀ k : Fin γ, IsSamplingLaw m (L.law k)) ∧
    (∀ k : Fin γ,
      l1Dist (L.law k) (step2IdealLaw D m A b ρ κ R γ k) ≤ ν) ∧
    (∀ (k : Fin γ) (N : Fin Nmax) (i : Fin m),
      |L.estA k N i - (Matrix.trace (A i * ρ)).re| ≤ ν) ∧
    (∀ (k : Fin γ) (N : Fin Nmax),
      |L.estC k N - (Matrix.trace (Cv * ρ)).re| ≤ ν)

/-- The conjunction of the empirical separation and objective inequalities used to accept a Step
2 candidate. -/
def step2Accepts (m M : ℕ) (b : Fin m → ℝ) (estA : Fin m → ℝ) (estC : ℝ)
    (draws : Fin M → Fin m) (α R κ ν mass : ℝ) : Prop :=
  estC / mass - (κ + ν) ≤ (∑ j : Fin M, estA (draws j)) / (M : ℝ) ∧
    (∑ j : Fin M, b (draws j)) / (M : ℝ) ≤ α / mass + R * (κ + ν)

/-- The vector obtained by multiplying each sampling-law coordinate by the selected mass. -/
def step2RoundVector (m : ℕ) (mass : ℝ) (q : Fin m → ℝ) : Fin m → ℝ :=
  fun i => mass * q i

/-- The condition that every candidate in the Step 2 grid fails the acceptance predicate. -/
def Step2NoOutput (m γ Nmax M : ℕ) (b : Fin m → ℝ) (L : Step2Loop m γ Nmax M)
    (α R κ ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    ¬ step2Accepts m M b (L.estA k N) (L.estC k N) (L.draws k N) α R κ ν (step2Mass κ N)

/-- The event that empirical bound averages and estimated-observable averages are close to their
law-weighted means at every grid point. -/
def Step2GoodEvent (m γ Nmax M : ℕ) (b : Fin m → ℝ)
    (L : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    |(∑ i : Fin m, L.law k i * b i) -
      (∑ j : Fin M, b (L.draws k N j)) / (M : ℝ)| ≤ R * (κ + ν) ∧
    |(∑ j : Fin M, L.estA k N (L.draws k N j)) / (M : ℝ) -
      (∑ i : Fin m, L.law k i * L.estA k N i)| ≤ κ + ν

/-- The condition that every nonnegative vector meeting the separator threshold has objective at
least `noCheapWidth α R ε`. -/
def NoCheapSeparator (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (noCheapSlack α ε ≤
      (∑ i, z i * (Matrix.trace (A i * ρ)).re) - (Matrix.trace (Cv * ρ)).re) →
    noCheapWidth α R ε ≤ ∑ i, z i * b i

/-- The one-based row-major candidate index `k.val*Nmax+N.val+1`. -/
def step2PairIndex {γ Nmax : ℕ} (k : Fin γ) (N : Fin Nmax) : ℕ :=
  k.val * Nmax + N.val + 1

/-- The condition that the visited pair count fits the grid and determines Gibbs copies, law
draws, and state copies by the specified formulas. -/
def Step2SampleLedger (γ Nmax M L pairs gibbsCopies qDraws stateCopies : ℕ) : Prop :=
  pairs ≤ γ * Nmax ∧
    gibbsCopies = M * pairs ∧
    qDraws = M * pairs ∧
    stateCopies = (M + 1) * L * pairs

/-- The product weight of a table of `M` independent draws from the vector `q`. -/
def drawTableWeight (m M : ℕ) (q : Fin m → ℝ) (tab : Fin M → Fin m) : ℝ :=
  ∏ j : Fin M, q (tab j)

/-- The product weight of all draw entries across the Step 2 grid. -/
def loopDrawWeight (m γ Nmax M : ℕ) (q : Fin γ → Fin m → ℝ)
    (tab : Fin γ → Fin Nmax → Fin M → Fin m) : ℝ :=
  ∏ k : Fin γ, ∏ N : Fin Nmax, ∏ j : Fin M, q k (tab k N j)

/-- The sum of loop draw-table weights over the tables satisfying the specified event. -/
def loopEventProb (m γ Nmax M : ℕ) (q : Fin γ → Fin m → ℝ)
    (P : (Fin γ → Fin Nmax → Fin M → Fin m) → Prop) : ℝ :=
  ∑ tab : Fin γ → Fin Nmax → Fin M → Fin m,
    if P tab then loopDrawWeight m γ Nmax M q tab else 0

/-- The sum of finite outcome weights over the outcomes satisfying the specified event. -/
def eventProb {Ω : ℕ} (w : Fin Ω → ℝ) (P : Fin Ω → Prop) : ℝ :=
  ∑ ω : Fin Ω, if P ω then w ω else 0

/-- The condition that finite outcome weights are nonnegative and sum to one. -/
def IsProbLaw {Ω : ℕ} (w : Fin Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ w ω) ∧ (∑ ω : Fin Ω, w ω) = 1

/-- The product of the `q` weights along a table of `Q` draws. -/
def qDrawWeight (m Q : ℕ) (q : Fin m → ℝ) (tab : Fin Q → Fin m) : ℝ :=
  ∏ j : Fin Q, q (tab j)

/-- The total product weight of draw tables satisfying the specified event. -/
def qDrawEventProb (m Q : ℕ) (q : Fin m → ℝ) (P : (Fin Q → Fin m) → Prop) : ℝ :=
  ∑ tab : Fin Q → Fin m, if P tab then qDrawWeight m Q q tab else 0

/-- The payoff formed from the scaled empirical average of sampled constraint matrices, with the
same objective and identity shifts as `dualPayoff`. -/
def scaledSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α mass : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ •
    (mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv + (2 * α) • (1 : Operator D))

/-- The sparsification deviation threshold `1/(4*T)`. -/
def sparsifyDeviation (T : ℝ) : ℝ := 1 / (4 * T)

/-- The sparsification summand bound `mass/(2*α)`. -/
def sparsifySummandBound (mass α : ℝ) : ℝ := mass / (2 * α)

/-- The matrix tail expression `D*exp (-Q*δ^2/(8*lam^2))`. -/
def matrixHoeffdingTail (D Q : ℕ) (δ lam : ℝ) : ℝ :=
  (D : ℝ) * Real.exp (-(Q : ℝ) * δ ^ 2 / (8 * lam ^ 2))

/-- The real sample-budget expression `10^6*R^6*(log (n*m))^(2+ξ)/δ^4`. -/
def sparsifySamples (n m : ℕ) (R δ ξ : ℝ) : ℝ :=
  10 ^ 6 * R ^ 6 * (Real.log ((n : ℝ) * (m : ℝ))) ^ (2 + ξ) / δ ^ 4

/-- The Gibbs perturbation expression `2*(exp Δ-1)`. -/
def gibbsPerturbationBound (Δ : ℝ) : ℝ := 2 * (Real.exp Δ - 1)

/-- The condition that the trace norm distance between `ρ` and `ρHat` is at most `ε`. -/
def ApproxGibbsError (D : ℕ) (ρ ρHat : Operator D) (ε : ℝ) : Prop :=
  Matrix.traceNorm (ρ - ρHat) ≤ ε

/-- The positivity conditions on accuracy and failure parameters together with the four stated
copy, measurement, and oracle upper bounds. -/
def ExpectationEstimationBudget (n m s : ℕ) (h p_e copies meas copiesO oracle : ℝ) : Prop :=
  0 < h ∧ 0 < p_e ∧ p_e < 1 ∧
    copies ≤ 8 * Real.log (1 / p_e) / h ^ 2 ∧
    meas ≤ 8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (s : ℝ) / (p_e * h))) ^ 4 ∧
    copiesO ≤ 8 * Real.log ((m : ℝ) / p_e) / h ^ 2 ∧
    oracle ≤ 8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (m : ℝ) * (s : ℝ) / (p_e * h))) ^ 4

/-- The coordinatewise weighted sum of the component vectors. -/
def mixtureLaw (m T : ℕ) (w : Fin (T + 1) → ℝ) (comp : Fin (T + 1) → Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => ∑ u : Fin (T + 1), w u * comp u i

/-- The mixture weights obtained from the certificate offset and averaged round masses,
normalized by the total certificate mass. -/
def mixtureWeights (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin (T + 1) → ℝ :=
  fun u =>
    if u.val = 0 then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
    else (∑ i, y (u.val - 1) i) / (T : ℝ) / dualSampleScale m (dualCertificate m δ α R j₀ y T)

/-- The distinguished-coordinate point mass followed by the normalized round vectors. -/
def mixtureComponents (m : ℕ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin (T + 1) → Fin m → ℝ :=
  fun u i =>
    if u.val = 0 then (if i = j₀ then (1 : ℝ) else 0)
    else y (u.val - 1) i / (∑ j, y (u.val - 1) j)

/-- The conditions that a positive-mass certificate has the specified normalized distribution
and weighted mixture representation, with normalized weights and the stated component
conditions. -/
def MixtureSamplingProcess (m T : ℕ) (yBar p : Fin m → ℝ) (w : Fin (T + 1) → ℝ)
    (comp : Fin (T + 1) → Fin m → ℝ) : Prop :=
  0 < dualSampleScale m yBar ∧
    (∀ u, 0 ≤ w u) ∧ (∑ u : Fin (T + 1), w u) = 1 ∧
    (∀ u, IsSamplingLaw m (comp u) ∨
      (∀ i, 0 ≤ comp u i ∧ comp u i ≤ 1)) ∧
    p = dualSampleDist m yBar ∧
    mixtureLaw m T w comp = p

/-- The condition that each requested draw uses one selector draw and one component draw. -/
def MixtureSampleLedger (draws selectorDraws componentDraws : ℕ) : Prop :=
  selectorDraws = draws ∧ componentDraws = draws

/-- A positive semidefinite primal candidate satisfying all constraint bounds, the trace bound
`R`, and objective at least `(1-δ)*α`. -/
def LargerWitness (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (X : Operator D) (δ α R : ℝ) : Prop :=
  X.PosSemidef ∧
    (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
    (Matrix.trace X).re ≤ R ∧
    (1 - δ) * α ≤ (Matrix.trace (Cv * X)).re

/-- A positive scale and probability vector whose scaled coordinates form a feasible dual
certificate with objective at most `(1+δ)*α`. -/
def SampleOutput (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (p : Fin m → ℝ) (L : ℝ) (δ α : ℝ) : Prop :=
  0 < L ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
    (∀ i, 0 ≤ L * p i) ∧
    ((∑ i, (L * p i) • A i) - Cv).PosSemidef ∧
    (∑ i, (L * p i) * b i ≤ (1 + δ) * α)

/-- The lower and upper endpoint sequences, guesses, and Boolean responses of a finite bisection
run. -/
structure AlphaBisectionRun (K : ℕ) where
  lo : Fin (K + 1) → ℝ
  hi : Fin (K + 1) → ℝ
  guess : Fin K → ℝ
  answerLarger : Fin K → Bool

/-- The initial interval, response-dependent endpoint updates, and final optimum containment and
tolerance conditions for a positive-length bisection run. -/
def AlphaBisectionCorrect (K : ℕ) (B : AlphaBisectionRun K) (αmin αmax opt δ tol : ℝ) :
    Prop :=
  0 < K ∧ 0 < αmin ∧ αmin ≤ opt ∧ opt ≤ αmax ∧ 0 < δ ∧ 0 < tol ∧
    B.lo 0 = αmin ∧ B.hi 0 = αmax ∧
    (∀ k : Fin K, B.lo k.castSucc ≤ B.guess k ∧ B.guess k ≤ B.hi k.castSucc) ∧
    (∀ k : Fin K, B.answerLarger k = true →
      B.lo k.succ = (1 - δ) * B.guess k ∧ B.hi k.succ = B.hi k.castSucc) ∧
    (∀ k : Fin K, B.answerLarger k = false →
      B.hi k.succ = (1 + δ) * B.guess k ∧ B.lo k.succ = B.lo k.castSucc) ∧
    B.lo (Fin.last K) ≤ opt ∧ opt ≤ B.hi (Fin.last K) ∧
    B.hi (Fin.last K) - B.lo (Fin.last K) ≤ tol

/-- The objective on lifted dual coordinates, with coefficient `R+1` on the extra coordinate. -/
def lemma2LiftedObjective (m : ℕ) (b : Fin m → ℝ) (R : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  (∑ i : Fin m, b i * y i.castSucc) + (R + 1) * y (Fin.last m)

/-- The block-matrix slack for the lifted SDP, combining the original constraints with an
additional scalar block and coordinate. -/
def lemma2LiftedSlack (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (r : ℝ) (y : Fin (m + 1) → ℝ) : Operator (D + 1) :=
  Matrix.reindex (finSumFinEquiv (m := D) (n := 1)) (finSumFinEquiv (m := D) (n := 1))
    ((∑ i : Fin m, y i.castSucc •
        (Matrix.fromBlocks (A i) 0 0 (1 : Operator 1))) +
      y (Fin.last m) • (Matrix.fromBlocks (0 : Operator D) 0 0 (1 : Operator 1)) -
      Matrix.fromBlocks Cv 0 0 ((r : ℂ) • (1 : Operator 1)))

/-- The existence of a nonnegative dual vector with positive semidefinite slack, objective
exactly `opt`, and total mass at most `r`. -/
def Lemma2OptimalWitness (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (r opt : ℝ) : Prop :=
  ∃ z : Fin m → ℝ,
    (∀ i, 0 ≤ z i) ∧
      ((0 : Operator D) ≤ (∑ i, z i • A i) - Cv) ∧
      (∑ i, z i * b i = opt) ∧
      (∑ i, z i) ≤ r

/-- The condition that a nonnegative lifted vector has positive semidefinite lifted slack and
objective at most `optLift+δ/r`. -/
def Lemma2LiftFeasible (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (R r δ optLift : ℝ) (yLift : Fin (m + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ yLift i) ∧
    ((0 : Operator (D + 1)) ≤ lemma2LiftedSlack D m A Cv r yLift) ∧
    lemma2LiftedObjective m b R yLift ≤ optLift + δ / r

/-- The original-coordinate dual feasibility and objective bound `opt+δ` extracted from a lifted
vector. -/
def Lemma2Rescale (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (yLift : Fin (m + 1) → ℝ) (opt δ : ℝ) : Prop :=
  ((0 : Operator D) ≤ (∑ i : Fin m, yLift i.castSucc • A i) - Cv) ∧
    (∑ i : Fin m, yLift i.castSucc * b i ≤ opt + δ)

/-- The implication from an objective bound after division by `α` to the corresponding objective
bound scaled by `α`. -/
def alphaRescaleAccuracy (m : ℕ) (b sol : Fin m → ℝ) (α δ : ℝ) : Prop :=
  (∑ i, sol i * (b i / α) ≤ 1 + δ) → (∑ i, sol i * b i ≤ (1 + δ) * α)

/-- The runtime expression `(R^21/δ^11)*G_h*G_M + (R^13/δ^5)*T_Meas`. -/
def thm4TimeLedger (R δ G_h G_M T_Meas : ℝ) : ℝ :=
  (R ^ 21 / δ ^ 11) * G_h * G_M + (R ^ 13 / δ ^ 5) * T_Meas

/-- The scaled source-tail expression used as the total run failure budget. -/
def thm4FailureBudget (n m : ℕ) (R δ ξ cO : ℝ) : ℝ :=
  cO * ((R / δ) ^ 18 * ((n : ℝ) * (m : ℝ)) ^ 10 * sourceFailureTail ξ (n : ℝ) (m : ℝ))

/-- The Gibbs sampler call-budget expression `sqrt dim*β*spars/ε`. -/
def gibbsSamplerCallBudget (dim β spars ε : ℝ) : ℝ :=
  Real.sqrt dim * β * spars / ε

/-- The budget `sqrt m*R^2/δ` for `G_h`. -/
def cor5GhBudget (m : ℕ) (R δ : ℝ) : ℝ := Real.sqrt (m : ℝ) * R ^ 2 / δ

/-- The budget `sqrt n*s^2*R^9/δ^6` for `G_M`. -/
def cor5GmBudget (n : ℕ) (s R δ : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * s ^ 2 * R ^ 9 / δ ^ 6

/-- The runtime expression `n^12*m^12*s^2*R^32/δ^18`. -/
def cor5TimeLedger (n m : ℕ) (s R δ : ℝ) : ℝ :=
  (n : ℝ) ^ 12 * (m : ℝ) ^ 12 * s ^ 2 * R ^ 32 / δ ^ 18

/-- The condition that `s` is positive and every row of every input matrix has at most `s`
nonzero entries. -/
def SparseInputAccess (D m : ℕ) (A : Fin (m + 1) → Operator D) (s : ℕ) : Prop :=
  0 < s ∧ ∀ j : Fin (m + 1), ∀ k : Fin D,
    (Finset.univ.filter (fun l : Fin D => A j k l ≠ 0)).card ≤ s

/-- The condition that a nonnegative failure probability is bounded by `thm4FailureBudget`. -/
def RunFailureCharge (n m : ℕ) (R δ ξ cO : ℝ) (failProb : ℝ) : Prop :=
  0 ≤ failProb ∧ failProb ≤ thm4FailureBudget n m R δ ξ cO

end

end Qatlib.Concepts.RationalScan.Step2Scan
