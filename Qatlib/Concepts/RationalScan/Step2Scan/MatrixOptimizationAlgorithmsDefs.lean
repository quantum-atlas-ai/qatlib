/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Logic.Equiv.Fin.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RationalScan.Step2Scan

set_option autoImplicit false

noncomputable section

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

def SdpInstance (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (j₀ : Fin m) (R : ℝ) : Prop :=
  0 < D ∧ 0 < m ∧ 0 < R ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i ∧ |b i| ≤ R) ∧
    A j₀ = 1 ∧ b j₀ = R

def sourceEps (δ R : ℝ) : ℝ := δ / (28 * R ^ 2)

def sourceOffset (δ α R : ℝ) : ℝ := δ * α / (2 * R)

def sourceRounds (D : ℕ) (R δ ε : ℝ) : ℕ :=
  Nat.ceil (16 * R * Real.log D / (δ * ε))

def sourceLogBase (ξ x : ℝ) : ℝ := Real.log x / Real.log ξ

def sourceLogOnePlus (ξ x : ℝ) : ℝ := Real.log x / Real.log (1 + ξ)

def sourceFailureTail (ξ n m : ℝ) : ℝ := Real.exp (-sourceLogBase ξ (n * m))

def SoftOWithin (actual budget soft : ℝ) : Prop :=
  1 ≤ soft ∧ actual ≤ soft * budget

def dualPayoff (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ)
    (y : ℕ → Fin m → ℝ) : ℕ → Operator D :=
  fun s => ((4 * α : ℝ))⁻¹ • ((∑ i, y s i • A i) - Cv + (2 * α) • (1 : Operator D))

def dualCertificate (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun j => (if j = j₀ then δ * α / (2 * R) else 0) + (∑ t ∈ Finset.range T, y t j) / T

def certificateObjective (m : ℕ) (b : Fin m → ℝ) (yBar : Fin m → ℝ) : ℝ :=
  ∑ i, yBar i * b i

def dualSampleScale (m : ℕ) (yBar : Fin m → ℝ) : ℝ := ∑ i, yBar i

def dualSampleDist (m : ℕ) (yBar : Fin m → ℝ) : Fin m → ℝ :=
  fun i => yBar i / dualSampleScale m yBar

def payoffUnitInterval (D : ℕ) (M : Operator D) : Prop :=
  M.IsHermitian ∧ (0 : Operator D) ≤ M ∧ M ≤ 1

def widthExact (α : ℝ) : ℝ := α

def widthSampled (α R ε : ℝ) : ℝ := α * (1 + 2 * R * ε)

def widthBridgeSlack (α R ε : ℝ) : ℝ := 2 * R * ε * α

def separationSlack (α ε : ℝ) : ℝ := 2 * α * ε

def noCheapSlack (α ε : ℝ) : ℝ := 3 * α * ε

def noCheapWidth (α R ε : ℝ) : ℝ := α * (1 - 3 * R * ε)

def IsSamplingLaw (m : ℕ) (q : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1

def l1Dist {m : ℕ} (p q : Fin m → ℝ) : ℝ := ∑ i, |p i - q i|

def step2IdealLaw (D m : ℕ) (A : Fin m → Operator D) (b : Fin m → ℝ) (ρ : Operator D)
    (κ R : ℝ) (γ k : ℕ) : Fin m → ℝ :=
  fun i =>
    Real.exp (-(κ / (4 * R ^ 2)) *
      ((k : ℝ) * (Matrix.trace (A i * ρ)).re + ((γ - k : ℕ) : ℝ) * b i)) /
      (∑ j : Fin m,
        Real.exp (-(κ / (4 * R ^ 2)) *
          ((k : ℝ) * (Matrix.trace (A j * ρ)).re + ((γ - k : ℕ) : ℝ) * b j)))

def step2Gamma (m : ℕ) (κ R : ℝ) : ℕ := Nat.ceil (8 / κ ^ 2 * Real.log m * R ^ 2)

def step2GridMax (α κ : ℝ) : ℕ := Nat.floor (α / κ)

def step2Mass (κ : ℝ) {Nmax : ℕ} (N : Fin Nmax) : ℝ := κ * ((N : ℕ) + 1)

def step2SampleM (D m : ℕ) (R ξ τ : ℝ) : ℕ :=
  Nat.ceil (80 * sourceLogOnePlus ξ (8 * R ^ 2 * (D : ℝ) * (m : ℝ) / τ) / τ ^ 2)

def step2SampleL (D m : ℕ) (ξ τ : ℝ) : ℕ :=
  Nat.ceil (80 * sourceLogOnePlus ξ ((D : ℝ) * (m : ℝ)) / τ ^ 2)

structure Step2Loop (m γ Nmax M : ℕ) where
  law : Fin γ → Fin m → ℝ
  draws : Fin γ → Fin Nmax → Fin M → Fin m
  estA : Fin γ → Fin Nmax → Fin m → ℝ
  estC : Fin γ → Fin Nmax → ℝ

def Step2LoopLegal (D m γ Nmax M : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (L : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  (∀ k : Fin γ, IsSamplingLaw m (L.law k)) ∧
    (∀ k : Fin γ,
      l1Dist (L.law k) (step2IdealLaw D m A b ρ κ R γ k) ≤ ν) ∧
    (∀ (k : Fin γ) (N : Fin Nmax) (i : Fin m),
      |L.estA k N i - (Matrix.trace (A i * ρ)).re| ≤ ν) ∧
    (∀ (k : Fin γ) (N : Fin Nmax),
      |L.estC k N - (Matrix.trace (Cv * ρ)).re| ≤ ν)

def step2Accepts (m M : ℕ) (b : Fin m → ℝ) (estA : Fin m → ℝ) (estC : ℝ)
    (draws : Fin M → Fin m) (α R κ ν mass : ℝ) : Prop :=
  estC / mass - (κ + ν) ≤ (∑ j : Fin M, estA (draws j)) / (M : ℝ) ∧
    (∑ j : Fin M, b (draws j)) / (M : ℝ) ≤ α / mass + R * (κ + ν)

def step2RoundVector (m : ℕ) (mass : ℝ) (q : Fin m → ℝ) : Fin m → ℝ :=
  fun i => mass * q i

def Step2NoOutput (m γ Nmax M : ℕ) (b : Fin m → ℝ) (L : Step2Loop m γ Nmax M)
    (α R κ ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    ¬ step2Accepts m M b (L.estA k N) (L.estC k N) (L.draws k N) α R κ ν (step2Mass κ N)

def Step2GoodEvent (m γ Nmax M : ℕ) (b : Fin m → ℝ)
    (L : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    |(∑ i : Fin m, L.law k i * b i) -
      (∑ j : Fin M, b (L.draws k N j)) / (M : ℝ)| ≤ R * (κ + ν) ∧
    |(∑ j : Fin M, L.estA k N (L.draws k N j)) / (M : ℝ) -
      (∑ i : Fin m, L.law k i * L.estA k N i)| ≤ κ + ν

def NoCheapSeparator (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (noCheapSlack α ε ≤
      (∑ i, z i * (Matrix.trace (A i * ρ)).re) - (Matrix.trace (Cv * ρ)).re) →
    noCheapWidth α R ε ≤ ∑ i, z i * b i

def step2PairIndex {γ Nmax : ℕ} (k : Fin γ) (N : Fin Nmax) : ℕ :=
  k.val * Nmax + N.val + 1

def Step2SampleLedger (γ Nmax M L pairs gibbsCopies qDraws stateCopies : ℕ) : Prop :=
  pairs ≤ γ * Nmax ∧
    gibbsCopies = M * pairs ∧
    qDraws = M * pairs ∧
    stateCopies = (M + 1) * L * pairs

def drawTableWeight (m M : ℕ) (q : Fin m → ℝ) (tab : Fin M → Fin m) : ℝ :=
  ∏ j : Fin M, q (tab j)

def loopDrawWeight (m γ Nmax M : ℕ) (q : Fin γ → Fin m → ℝ)
    (tab : Fin γ → Fin Nmax → Fin M → Fin m) : ℝ :=
  ∏ k : Fin γ, ∏ N : Fin Nmax, ∏ j : Fin M, q k (tab k N j)

def loopEventProb (m γ Nmax M : ℕ) (q : Fin γ → Fin m → ℝ)
    (P : (Fin γ → Fin Nmax → Fin M → Fin m) → Prop) : ℝ :=
  ∑ tab : Fin γ → Fin Nmax → Fin M → Fin m,
    if P tab then loopDrawWeight m γ Nmax M q tab else 0

def eventProb {Ω : ℕ} (w : Fin Ω → ℝ) (P : Fin Ω → Prop) : ℝ :=
  ∑ ω : Fin Ω, if P ω then w ω else 0

def IsProbLaw {Ω : ℕ} (w : Fin Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ w ω) ∧ (∑ ω : Fin Ω, w ω) = 1

def qDrawWeight (m Q : ℕ) (q : Fin m → ℝ) (tab : Fin Q → Fin m) : ℝ :=
  ∏ j : Fin Q, q (tab j)

def qDrawEventProb (m Q : ℕ) (q : Fin m → ℝ) (P : (Fin Q → Fin m) → Prop) : ℝ :=
  ∑ tab : Fin Q → Fin m, if P tab then qDrawWeight m Q q tab else 0

def scaledSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α mass : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ •
    (mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv + (2 * α) • (1 : Operator D))

def sparsifyDeviation (T : ℝ) : ℝ := 1 / (4 * T)

def sparsifySummandBound (mass α : ℝ) : ℝ := mass / (2 * α)

def matrixHoeffdingTail (D Q : ℕ) (δ lam : ℝ) : ℝ :=
  (D : ℝ) * Real.exp (-(Q : ℝ) * δ ^ 2 / (8 * lam ^ 2))

def sparsifySamples (n m : ℕ) (R δ ξ : ℝ) : ℝ :=
  10 ^ 6 * R ^ 6 * (Real.log ((n : ℝ) * (m : ℝ))) ^ (2 + ξ) / δ ^ 4

def gibbsPerturbationBound (Δ : ℝ) : ℝ := 2 * (Real.exp Δ - 1)

def ApproxGibbsError (D : ℕ) (ρ ρHat : Operator D) (ε : ℝ) : Prop :=
  Matrix.traceNorm (ρ - ρHat) ≤ ε

def ExpectationEstimationBudget (n m s : ℕ) (h p_e copies meas copiesO oracle : ℝ) : Prop :=
  0 < h ∧ 0 < p_e ∧ p_e < 1 ∧
    copies ≤ 8 * Real.log (1 / p_e) / h ^ 2 ∧
    meas ≤ 8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (s : ℝ) / (p_e * h))) ^ 4 ∧
    copiesO ≤ 8 * Real.log ((m : ℝ) / p_e) / h ^ 2 ∧
    oracle ≤ 8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (m : ℝ) * (s : ℝ) / (p_e * h))) ^ 4

def mixtureLaw (m T : ℕ) (w : Fin (T + 1) → ℝ) (comp : Fin (T + 1) → Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => ∑ u : Fin (T + 1), w u * comp u i

def mixtureWeights (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin (T + 1) → ℝ :=
  fun u =>
    if u.val = 0 then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
    else (∑ i, y (u.val - 1) i) / (T : ℝ) / dualSampleScale m (dualCertificate m δ α R j₀ y T)

def mixtureComponents (m : ℕ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin (T + 1) → Fin m → ℝ :=
  fun u i =>
    if u.val = 0 then (if i = j₀ then (1 : ℝ) else 0)
    else y (u.val - 1) i / (∑ j, y (u.val - 1) j)

def MixtureSamplingProcess (m T : ℕ) (yBar p : Fin m → ℝ) (w : Fin (T + 1) → ℝ)
    (comp : Fin (T + 1) → Fin m → ℝ) : Prop :=
  0 < dualSampleScale m yBar ∧
    (∀ u, 0 ≤ w u) ∧ (∑ u : Fin (T + 1), w u) = 1 ∧
    (∀ u, IsSamplingLaw m (comp u) ∨
      (∀ i, 0 ≤ comp u i ∧ comp u i ≤ 1)) ∧
    p = dualSampleDist m yBar ∧
    mixtureLaw m T w comp = p

def MixtureSampleLedger (draws selectorDraws componentDraws : ℕ) : Prop :=
  selectorDraws = draws ∧ componentDraws = draws

def LargerWitness (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (X : Operator D) (δ α R : ℝ) : Prop :=
  X.PosSemidef ∧
    (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
    (Matrix.trace X).re ≤ R ∧
    (1 - δ) * α ≤ (Matrix.trace (Cv * X)).re

def SampleOutput (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (p : Fin m → ℝ) (L : ℝ) (δ α : ℝ) : Prop :=
  0 < L ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
    (∀ i, 0 ≤ L * p i) ∧
    ((∑ i, (L * p i) • A i) - Cv).PosSemidef ∧
    (∑ i, (L * p i) * b i ≤ (1 + δ) * α)

structure AlphaBisectionRun (K : ℕ) where
  lo : Fin (K + 1) → ℝ
  hi : Fin (K + 1) → ℝ
  guess : Fin K → ℝ
  answerLarger : Fin K → Bool

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

def lemma2LiftedObjective (m : ℕ) (b : Fin m → ℝ) (R : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  (∑ i : Fin m, b i * y i.castSucc) + (R + 1) * y (Fin.last m)

def lemma2LiftedSlack (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (r : ℝ) (y : Fin (m + 1) → ℝ) : Operator (D + 1) :=
  Matrix.reindex (finSumFinEquiv (m := D) (n := 1)) (finSumFinEquiv (m := D) (n := 1))
    ((∑ i : Fin m, y i.castSucc •
        (Matrix.fromBlocks (A i) 0 0 (1 : Operator 1))) +
      y (Fin.last m) • (Matrix.fromBlocks (0 : Operator D) 0 0 (1 : Operator 1)) -
      Matrix.fromBlocks Cv 0 0 ((r : ℂ) • (1 : Operator 1)))

def Lemma2OptimalWitness (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (r opt : ℝ) : Prop :=
  ∃ z : Fin m → ℝ,
    (∀ i, 0 ≤ z i) ∧
      ((0 : Operator D) ≤ (∑ i, z i • A i) - Cv) ∧
      (∑ i, z i * b i = opt) ∧
      (∑ i, z i) ≤ r

def Lemma2LiftFeasible (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (R r δ optLift : ℝ) (yLift : Fin (m + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ yLift i) ∧
    ((0 : Operator (D + 1)) ≤ lemma2LiftedSlack D m A Cv r yLift) ∧
    lemma2LiftedObjective m b R yLift ≤ optLift + δ / r

def Lemma2Rescale (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (yLift : Fin (m + 1) → ℝ) (opt δ : ℝ) : Prop :=
  ((0 : Operator D) ≤ (∑ i : Fin m, yLift i.castSucc • A i) - Cv) ∧
    (∑ i : Fin m, yLift i.castSucc * b i ≤ opt + δ)

def alphaRescaleAccuracy (m : ℕ) (b sol : Fin m → ℝ) (α δ : ℝ) : Prop :=
  (∑ i, sol i * (b i / α) ≤ 1 + δ) → (∑ i, sol i * b i ≤ (1 + δ) * α)

def thm4TimeLedger (R δ G_h G_M T_Meas : ℝ) : ℝ :=
  (R ^ 21 / δ ^ 11) * G_h * G_M + (R ^ 13 / δ ^ 5) * T_Meas

def thm4FailureBudget (n m : ℕ) (R δ ξ cO : ℝ) : ℝ :=
  cO * ((R / δ) ^ 18 * ((n : ℝ) * (m : ℝ)) ^ 10 * sourceFailureTail ξ (n : ℝ) (m : ℝ))

def gibbsSamplerCallBudget (dim β spars ε : ℝ) : ℝ :=
  Real.sqrt dim * β * spars / ε

def cor5GhBudget (m : ℕ) (R δ : ℝ) : ℝ := Real.sqrt (m : ℝ) * R ^ 2 / δ

def cor5GmBudget (n : ℕ) (s R δ : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * s ^ 2 * R ^ 9 / δ ^ 6

def cor5TimeLedger (n m : ℕ) (s R δ : ℝ) : ℝ :=
  (n : ℝ) ^ 12 * (m : ℝ) ^ 12 * s ^ 2 * R ^ 32 / δ ^ 18

def SparseInputAccess (D m : ℕ) (A : Fin (m + 1) → Operator D) (s : ℕ) : Prop :=
  0 < s ∧ ∀ j : Fin (m + 1), ∀ k : Fin D,
    (Finset.univ.filter (fun l : Fin D => A j k l ≠ 0)).card ≤ s

def RunFailureCharge (n m : ℕ) (R δ ξ cO : ℝ) (failProb : ℝ) : Prop :=
  0 ≤ failProb ∧ failProb ≤ thm4FailureBudget n m R δ ξ cO

end

end Qatlib.Concepts.RationalScan.Step2Scan
