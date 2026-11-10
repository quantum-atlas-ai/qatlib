/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.Quadrature

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Matrix Polynomial

open scoped Matrix.Norms.L2Operator

noncomputable def chebT (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (n : ℤ)

def chebRecursionIdentity : Prop :=
  ∀ n : ℕ, chebT (n + 2) = 2 * Polynomial.X * chebT (n + 1) - chebT n

noncomputable def chebWeight (x : ℝ) : ℝ := 1 / Real.sqrt (1 - x ^ 2)

def chebOrthogonality : Prop :=
  ∀ m n : ℕ, m ≠ n →
    ∫ x in (0 : ℝ)..Real.pi, Real.cos (m * x) * Real.cos (n * x) = 0

def chebTriangleRepresentation : Prop :=
  ∀ n : ℕ, ∀ θ : ℝ, (chebT n).eval (Real.cos θ) = Real.cos (n * θ)

noncomputable def chebNode (N : ℕ) (j : ℕ) : ℝ := Real.cos ((2 * j + 1) * Real.pi / (2 * N))

def chebNodeValues : Prop :=
  ∀ N j : ℕ, j < N → ∀ n : ℕ,
    (chebT n).eval (chebNode N j) = Real.cos (n * (2 * j + 1) * Real.pi / (2 * N))

def gaussLegendreComparison : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∃ node weight : Fin Q → ℝ,
    (∑ q, weight q = 2) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
      (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
        ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)

def gaussLegendreCellComparison : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ (a h : ℝ) (node weight : Fin Q → ℝ) (f : ℝ → ℝ),
    0 < h →
    (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in a..a + h, p.eval x =
        ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2)) →
    (∫ x in a..a + h,
        ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) =
      (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) →
    ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f →
    |(∫ k in a..a + h, f k) -
        ∑ q, (h / 2) * weight q * f (a + h * (node q + 1) / 2)| ≤
      ((Q.factorial : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
        (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv (2 * Q) f k|)

def scalarToSingularBridge : Prop :=
  ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (f g : ℝ → ℂ) (ε : ℝ),
    0 ≤ ε →
    (∀ i : Fin (Fintype.card I),
      ‖f (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) -
        g (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)‖ ≤ ε) →
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A f -
      Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A g‖ ≤ ε

def polynomialToSingularBridge : Prop :=
  ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (p q : Polynomial ℝ) (ε : ℝ),
    0 ≤ ε →
    (∀ i : Fin (Fintype.card I),
      |p.eval (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) -
        q.eval (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)| ≤ ε) →
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) -
      Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((q.eval x : ℝ) : ℂ))‖ ≤ ε

structure SpectralCertificate (D : ℕ) where

  values : Fin D → ℚ × ℚ

  gaps : Fin D → ℚ

  multiplicity : Fin D → ℕ

  bitTime : ℕ

  bitSpace : ℕ

def SpectralApproximationCorrect {D : ℕ} (A : Operator D)
    (cert : SpectralCertificate D) (ε : ℝ) : Prop :=
  A.IsHermitian → 0 < ε →
    ∃ (U : Operator D) (lam : Fin D → ℝ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        A = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ ∧
        (∀ i : Fin D, lam i ∈ Set.Icc ((cert.values i).1 : ℝ) ((cert.values i).2 : ℝ)) ∧
        (∀ i j : Fin D, (i : ℕ) < (j : ℕ) → (cert.values i).2 ≤ (cert.values j).1) ∧
        (∀ i j : Fin D, (i : ℕ) < (j : ℕ) → (cert.gaps i : ℝ) ≤ lam j - lam i) ∧
        ∑ i, cert.multiplicity i = D ∧
        cert.bitTime ≤ D ^ 3 * (Nat.ceil (1 / ε) + 1) ∧
        cert.bitSpace ≤ D ^ 2 * (Nat.ceil (1 / ε) + 1)

def ResolventCertificate {D : ℕ} (A : Operator D) (z : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ r ≤ ‖z • (1 : Operator D) - A‖

noncomputable def schurMultiplierMap {D : ℕ} (B : Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun X := B ⊙ X
  map_add' X Y := by
    ext i j
    simp [Matrix.hadamard, mul_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.hadamard, smul_eq_mul, mul_left_comm]

def SchurMultiplierBounded {D : ℕ} (B : Operator D) (M : ℝ) : Prop :=
  ∀ X Y : Operator D, ‖B ⊙ (X - Y)‖ ≤ M * ‖X - Y‖

def schurMultiplierBridge : Prop :=
  ∀ (D : ℕ) (A : Operator D) (z : ℂ) (r : ℝ),
    ResolventCertificate A z r →
      ∀ B : Operator D, (∀ i j, ‖B i j‖ ≤ 1 / r) →
        SchurMultiplierBounded B ((D : ℝ) / r)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
