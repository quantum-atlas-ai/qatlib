/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def bandIndexValid (m : ℕ) (x : ℝ) (k : ℕ) : Prop :=
  k < m ∧ (3 : ℝ)⁻¹^(k+1) ≤ abs x ∧ abs x < (3 : ℝ)⁻¹^k

def bandRowsLegal {I : Type} (m : ℕ) (k : I → ℕ)
    (ξ : ℕ → I → QState (Fin 2)) (δ : ℕ → ℝ) : Prop :=
  0 < m ∧ (∀ u, k u < m) ∧
  (∀ j : Fin m, 0 ≤ δ (j.val+1) ∧ δ (j.val+1) ≤ 1/3) ∧
  (∀ u, ξ m u=(fun b =>  if b=0 then 1 else 0)) ∧
  (∀ j : Fin m, ∀ u, Normalized (ξ (j.val+1) u)) ∧
  (∀ j : Fin m, ∀ u, j.val+1 < k u → ‖ξ (j.val+1) u 0‖ ≤ δ (j.val+1)) ∧
  (∀ j : Fin m, ∀ u, k u+1 ≤ j.val+1 → ‖ξ (j.val+1) u 1‖ ≤ δ (j.val+1))

def stopCoefficient {I : Type} (ξ : ℕ → I → QState (Fin 2)) (j : ℕ) (u : I) : ℂ :=
  if j=0 then 0 else ξ j u 0*∏ l : Fin (j-1), ξ (l.val+1) u 1

def weightedBandState {I : Type} [Fintype I] (m : ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) : QState (Fin m × I) :=
  fun p =>  γ p.2*ζ (p.1.val+1) p.2*((3 : ℝ)^(p.1.val+1)/(3 : ℝ)^m)
def nearBandState {I : Type} [Fintype I] (m : ℕ) (k : I → ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) : QState (Fin m × I) :=
  fun p =>  if p.1.val+1=k p.2 ∨ p.1.val+1=k p.2+1 then
    weightedBandState m γ ζ p else 0
def singleBandProbability {I : Type} [Fintype I] (m : ℕ) (k : I → ℕ) (γ : I → ℂ) : ℝ :=
  ∑ u, ‖γ u‖^2*(9 : ℝ)^(k u+1)/(9 : ℝ)^m
def inverseBandProbability {I : Type} [Fintype I]
    (m : ℕ) (σ : I → ℝ) (γ : I → ℂ) : ℝ :=
  ∑ u, ‖γ u‖^2/((3 : ℝ)^m*σ u)^2
def bandLeakage {I : Type} [Fintype I] (m : ℕ) (k : I → ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) (weighted : Bool) : ℝ :=
  ∑ u, ‖γ u‖^2*∑ j : Fin m,
    if j.val+1≠k u ∧ j.val+1≠k u+1 then
      ‖ζ (j.val+1) u‖^2*(9 : ℝ)^(if weighted then j.val+1 else k u)/(9 : ℝ)^m else 0
def bandPotentialProbability {I : Type} [Fintype I] (m : ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) (j : ℕ) : ℝ :=
  ∑ u, ‖γ u‖^2*∑ h : Fin m,
    ‖ζ (h.val+1) u‖^2*(if j < h.val+1 then 1 else (9 : ℝ)^(h.val+1)/(9 : ℝ)^m)
def thresholdSum {I : Type} [Fintype I] (m l : ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) : ℝ :=
  ∑ j : Fin l, bandPotentialProbability m γ ζ (m-l+j.val+1)*
    (9 : ℝ)^(j.val+1)
def nearStop {I : Type} (k : I → ℕ) (ζ : ℕ → I → ℂ) (j : ℕ) (u : I) : ℂ :=
  if j=k u ∨ j=k u+1 then ζ j u else 0

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
