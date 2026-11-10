/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OperatorAccess.EncodedAccess
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.QSingValue19.Implementation

open Matrix Qatlib SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

structure EffectAccess (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ) where

  unitary : Matrix (Reg n) (Reg n) ℂ

  unitary_mem : unitary ∈ Matrix.unitaryGroup (Reg n) ℂ

  eigenvalues : Reg n → ℝ

  eigenvalues_nonneg : ∀ j, 0 ≤ eigenvalues j

  spectral : E = unitary * Matrix.diagonal (fun j => (eigenvalues j : ℂ)) * unitaryᴴ

  word : List (ReflectionGate (n+(n+1)))

  word_legal : reflectionLegal word

  word_length : word.length ≤ 128*(n+1)^2*4^n

  word_queries : QueryCount (reflectionCompile word) = 0

  word_gates : GateCount (reflectionCompile word) = word.length

  word_action : ∀ ψ : QState (Reg n),
    Run 1 (reflectionCompile word) (knownFrameEmbed n ψ) = knownFrameEmbed n (unitary *ᵥ ψ)

noncomputable def effectAccess (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) : EffectAccess n E := by
  have hH : E.IsHermitian := hE.isHermitian
  let V : Matrix (Reg n) (Reg n) ℂ := hH.eigenvectorUnitary
  have hV : V ∈ Matrix.unitaryGroup (Reg n) ℂ := hH.eigenvectorUnitary.2
  have hex := known_unitary_actual_clean_local_synthesis n V hV
  let gs : List (ReflectionGate (n+(n+1))) := Classical.choose hex
  have hspec := Classical.choose_spec hex
  refine
    { unitary := V
      unitary_mem := hV
      eigenvalues := hH.eigenvalues
      eigenvalues_nonneg := fun j => hE.eigenvalues_nonneg j
      spectral := hH.spectral_theorem
      word := gs
      word_legal := hspec.1
      word_length := hspec.2.1
      word_queries := hspec.2.2.1
      word_gates := hspec.2.2.2.1
      word_action := hspec.2.2.2.2 }

noncomputable def spectrumMantissa (b : ℕ) (x : ℝ) : ℕ := Nat.floor (x * (2 : ℝ)^b)

def effectSpectrumBits (n b : ℕ) : ℕ := (b+1) * Fintype.card (Reg n)

noncomputable def prepareFiniteDigit {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
  rationalWeightPrepare w k

noncomputable def prepareIdeal {n : ℕ} (w : Option (Fin n) → ℚ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
  idealWeightPrepare w

noncomputable def prepareTarget {n : ℕ} (w : Option (Fin n) → ℚ) :
    QState (Option (Fin n)) :=
  rationalWeightTarget w

end Qatlib.Papers.QSingValue19.Implementation
