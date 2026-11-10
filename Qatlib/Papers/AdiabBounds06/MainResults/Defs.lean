/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

def IsProj (P : Matrix (Fin n) (Fin n) ℂ) : Prop := P * P = P ∧ Pᴴ = P

def orthCompl (P : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := 1 - P

def realGenerator (τ : ℝ) (H : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    ℝ → Matrix (Fin n) (Fin n) ℂ :=
  fun u => (Complex.I * (τ : ℂ)) • H u

def Uτ (τ : ℝ) (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  orderedEvolution (realGenerator τ H) 0 s

def HτA (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  H s + (Complex.I / (τ : ℂ)) • (Pdot s * P s - P s * Pdot s)

def adiGenerator (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    ℝ → Matrix (Fin n) (Fin n) ℂ :=
  fun u => (Complex.I * (τ : ℂ)) • H u - (Pdot u * P u - P u * Pdot u)

def UτA (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  orderedEvolution (adiGenerator τ H P Pdot) 0 s

def Pt (τ : ℝ) (H : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (P0 : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Uτ τ H s * P0 * (Uτ τ H s)ᴴ

def waveOperator (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (UτA τ H P Pdot s)ᴴ * Uτ τ H s

def adjoinEv (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (X : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (UτA τ H P Pdot s)ᴴ * X s * UτA τ H P Pdot s

def applyMat (A : Matrix (Fin n) (Fin n) ℂ) (ψ : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (A *ᵥ (ψ : Fin n → ℂ))

def transitionProb (U Q : Matrix (Fin n) (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  (inner ℂ (applyMat U ψ) (applyMat Q (applyMat U ψ))).re

def commutator (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

theorem IsProj.orthCompl_isProj {P : Matrix (Fin n) (Fin n) ℂ} (h : IsProj P) :
    IsProj (orthCompl P) := by
  obtain ⟨hPP, hPstar⟩ := h
  show (1 - P) * (1 - P) = 1 - P ∧ (1 - P)ᴴ = 1 - P
  refine ⟨?_, ?_⟩
  · rw [mul_sub, mul_one, sub_mul, one_mul, hPP]
    abel
  · rw [conjTranspose_sub, conjTranspose_one, hPstar]

theorem mul_orthCompl {P : Matrix (Fin n) (Fin n) ℂ} (h : IsProj P) :
    P * orthCompl P = 0 ∧ orthCompl P * P = 0 := by
  obtain ⟨hPP, _⟩ := h
  show P * (1 - P) = 0 ∧ (1 - P) * P = 0
  constructor
  · rw [mul_sub, mul_one, hPP]
    exact sub_self _
  · rw [sub_mul, one_mul, hPP]
    exact sub_self _

theorem orthCompl_mul_self {P : Matrix (Fin n) (Fin n) ℂ} (h : IsProj P) :
    orthCompl P * orthCompl P = orthCompl P :=
  (IsProj.orthCompl_isProj h).1

theorem Pdot_eq_offdiag
    (P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hProj : ∀ s, P s * P s = P s)
    (hder : ∀ s, HasDerivAt P (Pdot s) s) (s : ℝ) :
    Pdot s = Pdot s * P s + P s * Pdot s := by
  have hmul : HasDerivAt (fun t => P t * P t)
      (Pdot s * P s + P s * Pdot s) s :=
    (hder s).mul (hder s)
  have hconst : (fun t => P t * P t) = P := funext hProj
  rw [hconst] at hmul
  exact (hmul.unique (hder s)).symm

theorem Pdot_sandwich_eq_zero
    (P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hProj : ∀ s, P s * P s = P s)
    (hder : ∀ s, HasDerivAt P (Pdot s) s) (s : ℝ) :
    P s * Pdot s * P s = 0 := by
  have hoff := Pdot_eq_offdiag P Pdot hProj hder s

  have h1 : P s * Pdot s = P s * Pdot s * P s + P s * Pdot s := by
    have h' : P s * (P s * Pdot s) = P s * Pdot s := by
      rw [← mul_assoc, hProj s]
    have h'' : P s * (Pdot s * P s) = P s * Pdot s * P s := by
      rw [← mul_assoc]
    calc P s * Pdot s = P s * (Pdot s * P s + P s * Pdot s) := by rw [← hoff]
      _ = P s * (Pdot s * P s) + P s * (P s * Pdot s) := by rw [mul_add]
      _ = P s * Pdot s * P s + P s * Pdot s := by rw [h'', h']
  have h2 : P s * Pdot s * P s = 0 := by
    have := congrArg (fun X => X - P s * Pdot s) h1
    simpa using! this.symm
  exact h2

end Qatlib.Papers.AdiabBounds06.MainResults
