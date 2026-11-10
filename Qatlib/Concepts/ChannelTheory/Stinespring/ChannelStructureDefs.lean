/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ChannelTheory.Stinespring

set_option autoImplicit false

open Matrix
open scoped Classical ComplexOrder BigOperators

variable {D E F : ℕ}

noncomputable def matrixUnit (i j : Fin D) : Operator D := Matrix.single i j 1

noncomputable def ChoiMatrix (T : Operator D →ₗ[ℂ] Operator E) :
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  fun x y => T (matrixUnit x.1 y.1) x.2 y.2

def KrausForm (T : Operator D →ₗ[ℂ] Operator E) {n : ℕ}
    (K : Fin n → Matrix (Fin E) (Fin D) ℂ) : Prop :=
  ∀ A : Operator D, T A = ∑ k, K k * A * (K k).conjTranspose

def KrausComplete {n : ℕ} (K : Fin n → Matrix (Fin E) (Fin D) ℂ) : Prop :=
  ∑ k, (K k).conjTranspose * K k = 1

noncomputable def krausMap {n : ℕ} (K : Fin n → Matrix (Fin E) (Fin D) ℂ) :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ k, conjBranch (K k)

noncomputable def refIsometryImage {env : ℕ} (V : Matrix (Fin E × Fin env) (Fin D) ℂ)
    (R : ℕ) (X : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) :
    Matrix (Fin R × (Fin E × Fin env)) (Fin R × (Fin E × Fin env)) ℂ :=
  fun x y => ∑ i, ∑ j, V x.2 i * X (x.1, i) (y.1, j) * star (V y.2 j)

noncomputable def traceOutEnv {R env : ℕ}
    (Y : Matrix (Fin R × (Fin E × Fin env)) (Fin R × (Fin E × Fin env)) ℂ) :
    Matrix (Fin R × Fin E) (Fin R × Fin E) ℂ :=
  fun u v => ∑ e : Fin env, Y (u.1, (u.2, e)) (v.1, (v.2, e))

def StinespringDilation (T : Operator D →ₗ[ℂ] Operator E) (env : ℕ)
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) : Prop :=
  V.conjTranspose * V = 1 ∧
  ∀ (R : ℕ) (X : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ),
    traceOutEnv (refIsometryImage V R X) = ChannelAmplification T R X

noncomputable def envPad {env dOut : ℕ} (_h : env ≤ dOut) (w : Fin E × Fin env → ℂ) :
    Fin E × Fin dOut → ℂ :=
  fun x => if hx : x.2.val < env then w (x.1, ⟨x.2.val, hx⟩) else 0

def CleanEnvUnitaryCompletion {env : ℕ} (V : Matrix (Fin E × Fin env) (Fin D) ℂ) : Prop :=
  ∃ (dIn dOut : ℕ) (e0 : Fin dIn) (U : Matrix (Fin E × Fin dOut) (Fin D × Fin dIn) ℂ),
    ∃ (_hdim : D * dIn = E * dOut) (henv : env ≤ dOut),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      ∀ ψ : Fin D → ℂ,
        U *ᵥ (fun x : Fin D × Fin dIn => if x.2 = e0 then ψ x.1 else 0)
          = envPad henv (V *ᵥ ψ)

noncomputable def EffectStat (E : Operator D) (ρ : Operator D) : ℝ :=
  (Matrix.trace (E * ρ)).re

noncomputable def normSqVec {S : Type} [Fintype S] (w : S → ℂ) : ℝ := ∑ s, ‖w s‖ ^ 2

noncomputable def refLeft {S : Type} [Fintype S] (A : Matrix S S ℂ) (R : ℕ) :
    Matrix (Fin R × S) (Fin R × S) ℂ :=
  fun x y => if x.1 = y.1 then A x.2 y.2 else 0

def NaimarkDilation {O : Type} [Fintype O] (Λ : POVM O (Fin D)) (m : ℕ)
    (V : Matrix (Fin D × Fin m) (Fin D) ℂ)
    (P : O → Matrix (Fin D × Fin m) (Fin D × Fin m) ℂ) : Prop :=
  V.conjTranspose * V = 1 ∧
  (∀ o : O, (P o).conjTranspose = P o ∧ P o * P o = P o) ∧
  (∀ o p : O, o ≠ p → P o * P p = 0) ∧
  (∑ o, P o = 1) ∧
  (∀ o : O, V.conjTranspose * P o * V = (Λ.mats o).mat)

def IsUnitaryMatrix (A : Operator D) : Prop :=
  A.conjTranspose * A = 1 ∧ A * A.conjTranspose = 1

def IsUnitaryRep {G : Type} [Group G] (U : G → Operator D) : Prop :=
  (∀ g : G, IsUnitaryMatrix (U g)) ∧ U 1 = 1 ∧ ∀ g h : G, U (g * h) = U g * U h

noncomputable def FamilyTwirl {J : Type} [Fintype J] (U : J → Operator D) :
    Operator D →ₗ[ℂ] Operator D :=
  ((Fintype.card J : ℂ)⁻¹) • ∑ j, conjBranch (U j)

noncomputable def pauliFourFamily : Fin 4 → Operator 2 := ![1, pauliX, pauliY, pauliZ]

@[reducible] noncomputable def operatorMeasurableSpace : MeasurableSpace (Operator D) :=
  @MeasurableSpace.pi (Fin D) (fun _ => Fin D → ℂ)
    (fun _ => @MeasurableSpace.pi (Fin D) (fun _ => ℂ) (fun _ => Complex.measurableSpace))

attribute [local instance] operatorMeasurableSpace

structure HaarUnitaryMeasure (D : ℕ) where

  μ : MeasureTheory.Measure (Matrix (Fin D) (Fin D) ℂ)

  isProb : MeasureTheory.IsProbabilityMeasure μ

  supportedOnUnitary : μ {A : Operator D | IsUnitaryMatrix A}ᶜ = 0

  leftInvariant : ∀ W : Operator D, IsUnitaryMatrix W →
    MeasureTheory.Measure.map (fun A => W * A) μ = μ

  rightInvariant : ∀ W : Operator D, IsUnitaryMatrix W →
    MeasureTheory.Measure.map (fun A => A * W) μ = μ

noncomputable def HaarTwirl {D : ℕ} (H : HaarUnitaryMeasure D) (ρ : Operator D) :
    Operator D :=
  fun i j => MeasureTheory.integral H.μ fun A : Operator D => (A * ρ * A.conjTranspose) i j

def HaarProjectionFormula {D : ℕ} (H : HaarUnitaryMeasure D) : Prop :=
  ∀ (ρ : Operator D) (i j : Fin D),
    HaarTwirl H ρ i j
      = MeasureTheory.integral H.μ
          fun A : Operator D => HaarTwirl H (A * ρ * A.conjTranspose) i j

noncomputable def ChannelAmplificationFn (T : Operator D → Operator E) (r : ℕ)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix (Fin r × Fin E) (Fin r × Fin E) ℂ :=
  fun x y => T (fun i j => A (x.1, i) (y.1, j)) x.2 y.2

def CPTPFunction (T : Operator D → Operator E) : Prop :=
  (∀ (r : ℕ) (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ),
    A.PosSemidef → (ChannelAmplificationFn T r A).PosSemidef) ∧
  (∀ A : Operator D, Matrix.trace (T A) = Matrix.trace A)

def QubitTwoDesignMoments (f : Fin 24 → Operator 2) : Prop :=
  (∀ i : Fin 24, IsUnitaryMatrix (f i)) ∧
  (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
    (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re) / 24 = (Matrix.trace A).re / 2) ∧
  (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
    A.IsHermitian → B.IsHermitian →
      (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re *
        (Matrix.trace (B * (f i)ᴴ * Pp * f i)).re) / 24 =
        ((Matrix.trace A).re * (Matrix.trace B).re + (Matrix.trace (A * B)).re) / 6)

def QubitSecondMomentUnboundaried {J : Type} [Fintype J] (prob : J → ℝ)
    (Uf : J → Operator 2) : Prop :=
  ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
    (∑ j, prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
      (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re) =
      ((Matrix.trace A).re * (Matrix.trace B).re + (Matrix.trace (A * B)).re) / 6

end Qatlib.Concepts.ChannelTheory.Stinespring
