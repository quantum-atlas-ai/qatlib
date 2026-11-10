/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

set_option autoImplicit false


namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix
open scoped Classical

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

abbrev PauliLabel (ι : Type*) := (ι → ZMod 2) × (ι → ZMod 2)

def pauliSyndrome (c : CssData ι κX κZ) (e : PauliLabel ι) : (κX → ZMod 2) × (κZ → ZMod 2) :=
  (c.hX *ᵥ e.2, c.hZ *ᵥ e.1)

def syndromeDist (η η' : (κX → ZMod 2) × (κZ → ZMod 2)) : ℕ :=
  bitWeight (η.1 + η'.1) + bitWeight (η.2 + η'.2)

noncomputable def IsStabilizerLabel (c : CssData ι κX κZ) (e : PauliLabel ι) : Prop :=
  e.1 ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
    e.2 ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)

structure RecoveryProgram (c : CssData ι κX κZ) where

  corr : (κX → ZMod 2) × (κZ → ZMod 2) → PauliLabel ι

  decodeTime : (κX → ZMod 2) × (κZ → ZMod 2) → ℕ

def residualFromObserved {c : CssData ι κX κZ} (prog : RecoveryProgram c) (e : PauliLabel ι)
    (ηobs : (κX → ZMod 2) × (κZ → ZMod 2)) : PauliLabel ι :=
  (e.1 + (prog.corr ηobs).1, e.2 + (prog.corr ηobs).2)

def residualLabel {c : CssData ι κX κZ} (prog : RecoveryProgram c) (e : PauliLabel ι) :
    PauliLabel ι :=
  residualFromObserved prog e (pauliSyndrome c e)

def CorrectsUpTo {c : CssData ι κX κZ} (prog : RecoveryProgram c) (t : ℕ) : Prop :=
  ∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
    IsStabilizerLabel c (residualLabel prog e)

def CorrectsSingleShotNoisyUpTo {c : CssData ι κX κZ} (prog : RecoveryProgram c)
    (t s : ℕ) : Prop :=
  ∀ (e : PauliLabel ι) (ηobs : (κX → ZMod 2) × (κZ → ZMod 2)),
    pauliWeight e.1 e.2 ≤ t →
    syndromeDist (pauliSyndrome c e) ηobs ≤ s →
    IsStabilizerLabel c (residualFromObserved prog e ηobs)

def MinimumWeightSound {c : CssData ι κX κZ} (prog : RecoveryProgram c) : Prop :=
  ∀ (η : (κX → ZMod 2) × (κZ → ZMod 2)) (e : PauliLabel ι),
    pauliSyndrome c e = η →
    pauliWeight (prog.corr η).1 (prog.corr η).2 ≤ pauliWeight e.1 e.2

noncomputable def coeffInner (u v : (ι → ZMod 2) → ℂ) : ℂ := ∑ i, star (u i) * v i

structure CssEncoding (c : CssData ι κX κZ) (K : ℕ) where

  enc : (Fin K → ZMod 2) → (ι → ZMod 2) → ℂ

  mem_codespace : ∀ b : Fin K → ZMod 2, enc b ∈ cssCodespace c

  orthonormal : ∀ b b' : Fin K → ZMod 2,
    coeffInner (enc b) (enc b') = if b = b' then 1 else 0

  spans : ∀ v : (ι → ZMod 2) → ℂ,
    v ∈ cssCodespace c → v ∈ Submodule.span ℂ (Set.range enc)

noncomputable def vecNormSq (ψ : (ι → ZMod 2) → ℂ) : ℝ := ∑ i, (ψ i).normSq

noncomputable def syndromeOutcomeMass (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (ψ : (ι → ZMod 2) → ℂ) : ℝ :=
  vecNormSq (cssSyndromeProjector c η *ᵥ ψ)

noncomputable def densityOf (ψ : (ι → ZMod 2) → ℂ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  fun i j => ψ i * star (ψ j)

noncomputable def recoveryChannel (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (ρ : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
    (fun P R => R * (P * ρ * P) * Matrix.conjTranspose R)
      (cssSyndromeProjector c η)
      (cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2)

noncomputable def LogicalReferencePreserved (c : CssData ι κX κZ) (e : PauliLabel ι) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] (M : Matrix (ι → ZMod 2) ρ ℂ),
    (∀ r : ρ, (fun q => M q r) ∈ cssCodespace c) →
    (cssPauliX e.1 * cssPauliZ e.2) * M = M

structure RecoveryCost where

  gates : ℕ

  measurements : ℕ

  classicalTime : ℕ

def syndromeMeasurements (_c : CssData ι κX κZ) : ℕ := Fintype.card (κX ⊕ κZ)

def syndromeExtractionGates (c : CssData ι κX κZ) : ℕ :=
  (∑ i : κX, bitWeight (c.hX i)) + (∑ j : κZ, bitWeight (c.hZ j))

def correctionGates (e : PauliLabel ι) : ℕ := pauliWeight e.1 e.2

def recoveryCost (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : RecoveryCost :=
  { gates := syndromeExtractionGates c + correctionGates (prog.corr η)
    measurements := syndromeMeasurements c
    classicalTime := prog.decodeTime η }

def decodeTimeBound (c : CssData ι κX κZ) (prog : RecoveryProgram c) : ℕ :=
  Finset.univ.sup fun η : (κX → ZMod 2) × (κZ → ZMod 2) => prog.decodeTime η

structure RecoveryReceipt (c : CssData ι κX κZ) (prog : RecoveryProgram c) where

  η : (κX → ZMod 2) × (κZ → ZMod 2)

  applied : PauliLabel ι

  cost : RecoveryCost

def RecoveryReceipt.Realizes {c : CssData ι κX κZ} {prog : RecoveryProgram c}
    (r : RecoveryReceipt c prog) (e : PauliLabel ι) : Prop :=
  r.η = pauliSyndrome c e ∧ r.applied = prog.corr r.η ∧
    r.cost = recoveryCost c prog r.η

structure CssFamily where

  N : ℕ → ℕ

  mX : ℕ → ℕ

  mZ : ℕ → ℕ

  code : (n : ℕ) → CssData (Fin (N n)) (Fin (mX n)) (Fin (mZ n))

def CssFamily.IsLdpc (f : CssFamily) (w inc a : ℕ) : Prop :=
  ∀ n, 0 < n →
    (f.code n).checkWeight ≤ w ∧ (f.code n).qubitIncidence ≤ inc ∧
      f.mX n + f.mZ n ≤ a * f.N n

noncomputable def CssFamily.DistanceAtLeast (f : CssFamily) (d : ℕ → ℕ) : Prop :=
  ∀ n, 0 < n → (d n : ℕ∞) ≤ cssDistance (f.code n)

noncomputable def CssFamily.SoundnessAtLeast (f : CssFamily) (σ : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → cssHasSoundnessAtLeast (f.code n) (σ n)

noncomputable def CssFamily.IsGood (f : CssFamily) : Prop :=
  ∃ (d : ℕ → ℕ) (C : ℕ) (r : ℚ), 0 < C ∧ 0 < r ∧
    f.DistanceAtLeast d ∧ (∀ n, 0 < n → f.N n ≤ C * d n) ∧
      (∀ n, 0 < n → r ≤ (f.code n).rate)

def trivialFamily : CssFamily where
  N := fun n => n
  mX := fun _ => 1
  mZ := fun _ => 1
  code := fun n =>
    { hX := 0
      hZ := 0
      hcompat := by exact Matrix.zero_mul _ }

noncomputable def iidSyndromeLaw (c : CssData ι κX κZ)
    (ηtrue ηobs : (κX → ZMod 2) × (κZ → ZMod 2)) (p : ℝ) : ℝ :=
  p ^ syndromeDist ηtrue ηobs *
    (1 - p) ^ (syndromeMeasurements c - syndromeDist ηtrue ηobs)

noncomputable def noisyFailureMass {c : CssData ι κX κZ} (prog : RecoveryProgram c)
    (e : PauliLabel ι) (p : ℝ) : ℝ :=
  ∑ ηobs : (κX → ZMod 2) × (κZ → ZMod 2),
    if IsStabilizerLabel c (residualFromObserved prog e ηobs) then 0
    else iidSyndromeLaw c (pauliSyndrome c e) ηobs p

def LocalStochasticNoiseLaw {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (p : ℝ) : Prop :=
  (∀ F, 0 ≤ pp F) ∧ (∑ F ∈ Finset.univ, pp F = 1) ∧
    ∀ S ⊆ Finset.univ,
      ∑ F ∈ Finset.univ.filter (fun F => S ⊆ F), pp F ≤ p ^ S.card

def AdversarialFaultBudget {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (a : ℕ) : Prop :=
  (∀ F, 0 ≤ pp F) ∧ (∑ F ∈ Finset.univ, pp F = 1) ∧
    ∀ F, 0 < pp F → F.card ≤ a

noncomputable def gadgetFailureProb {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (t : ℕ) : ℝ :=
  ∑ F ∈ Finset.univ.filter (fun F : Finset (Fin ζ) => t < F.card), pp F

inductive GadgetKind where

  | syndromeRound

  | gate

  | prep

  | measure

structure GadgetSpec (c : CssData ι κX κZ) where

  kind : GadgetKind

  locations : ℕ

  space : ℕ

  time : ℕ

  ideal : PauliLabel ι

  residual : Finset (Fin locations) → PauliLabel ι

noncomputable def GadgetSpec.IsIdealCorrect {c : CssData ι κX κZ} (g : GadgetSpec c) : Prop :=
  IsStabilizerLabel c g.ideal ∧ g.residual ∅ = g.ideal

def GadgetSpec.IsFaultTolerantAt {c : CssData ι κX κZ} (g : GadgetSpec c) (t : ℕ) : Prop :=
  ∀ F : Finset (Fin g.locations), F.card ≤ t →
    pauliWeight (g.residual F).1 (g.residual F).2 ≤ t

def GadgetSpec.spaceTime {c : CssData ι κX κZ} (g : GadgetSpec c) : ℕ :=
  g.space * g.time

noncomputable def GadgetSpec.failureMass {c : CssData ι κX κZ} (g : GadgetSpec c)
    (t : ℕ) (p : ℝ) : ℝ :=
  (g.locations.choose (t + 1) : ℝ) * p ^ (t + 1)

noncomputable def composedFailureMass {c : CssData ι κX κZ}
    (gs : List (GadgetSpec c)) (t : ℕ) (p : ℝ) : ℝ :=
  (gs.map fun g => g.failureMass t p).sum

noncomputable def composedErrWindow {c : CssData ι κX κZ} (gs : List (GadgetSpec c))
    (ζ t : ℕ) (p : ℝ) : ℝ :=
  (gs.length : ℝ) * (ζ.choose (t + 1) : ℝ) * p ^ (t + 1)

def cumulativeSpaceTime {c : CssData ι κX κZ} (gs : List (GadgetSpec c)) : ℕ :=
  (gs.map fun g => g.space * g.time).sum

def peakSpace {c : CssData ι κX κZ} (gs : List (GadgetSpec c)) : ℕ :=
  (gs.map fun g => g.space).foldr max 0

structure FtRealization where

  N : ℕ

  mX : ℕ

  mZ : ℕ

  code : CssData (Fin N) (Fin mX) (Fin mZ)

  prog : RecoveryProgram code

  t : ℕ

  ζ : ℕ

  gadgets : List (GadgetSpec code)

  pTh : ℝ

  ε : ℝ

  budget : ℕ

  peak : ℕ

end Qatlib.Concepts.CodingDecoding.CssTesters
