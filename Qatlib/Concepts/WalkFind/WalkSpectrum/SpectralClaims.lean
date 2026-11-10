/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkTypeTransportQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonFullSpectrumQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonPhaseAsymptoticQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.NormalSpectralPerturbationQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkUnitaryQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkStartFixedQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

def Lemma1Statement : Prop :=
  Qatlib.Concepts.WalkFind.WalkSpectrum.WalkTypeTransport

theorem lemma1 : Lemma1Statement :=
  Qatlib.Concepts.WalkFind.WalkSpectrum.walkTypeTransport_answer

def Lemma2Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.WalkUnitary ∧
    Qatlib.Concepts.WalkFind.UniqueCollision.WalkStartFixed ∧
    Qatlib.Concepts.WalkFind.SearchAlgorithm.JohnsonFullSpectrumContract ∧
    Qatlib.Concepts.WalkFind.SearchAlgorithm.JohnsonPhaseAsymptoticContract

theorem lemma2 : Lemma2Statement :=
  ⟨Qatlib.Concepts.WalkFind.UniqueCollision.walkUnitary,
    Qatlib.Concepts.WalkFind.UniqueCollision.walkStartFixed,
    Qatlib.Concepts.WalkFind.WalkSpectrum.johnsonFullSpectrum_answer,
    Qatlib.Concepts.WalkFind.WalkSpectrum.johnsonPhaseAsymptotic_answer⟩

def Theorem6Statement : Prop :=
  ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ),
    A ∈ Matrix.unitaryGroup (Fin m) ℂ →
    B ∈ Matrix.unitaryGroup (Fin m) ℂ →
      ∃ (E F G : Matrix (Fin m) (Fin m) ℂ)
        (eigenA eigenB eigenAB : Fin m → ℂ) (σ : Fin m → Fin m),
        E ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
        F ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
        G ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
        A * E = E * Matrix.diagonal eigenA ∧
        B * F = F * Matrix.diagonal eigenB ∧
        (A * B) * G = G * Matrix.diagonal eigenAB ∧
        ∀ j : Fin m,
          ‖eigenB j - eigenAB (σ j)‖ ≤
            Real.sqrt (∑ i : Fin m, ‖eigenA i - (1 : ℂ)‖ ^ 2)

theorem theorem6 : Theorem6Statement := by
  intro m A B hA hB
  obtain ⟨E, F, G, eigenA, eigenB, eigenAB, σ, hE, hF, hG, hAE, hBF, hABG, hsum⟩ :=
    Qatlib.Concepts.WalkFind.WalkSpectrum.normalSpectralPerturbation_answer.2.2
      m A B hA hB
  refine ⟨E, F, G, eigenA, eigenB, eigenAB, σ, hE, hF, hG, hAE, hBF, hABG, ?_⟩
  intro j
  calc ‖eigenB j - eigenAB (σ j)‖
      = Real.sqrt (‖eigenB j - eigenAB (σ j)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i : Fin m, ‖eigenB i - eigenAB (σ i)‖ ^ 2) :=
        Real.sqrt_le_sqrt
          (Finset.single_le_sum (fun i _ => sq_nonneg ‖eigenB i - eigenAB (σ i)‖)
            (Finset.mem_univ j))
    _ ≤ Real.sqrt (∑ i : Fin m, ‖eigenA i - (1 : ℂ)‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum

def Theorem7Statement : Prop :=
  ∀ (m n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin m) (Fin n) ℂ),
    U ∈ Matrix.unitaryGroup (Fin m) ℂ →
      Qatlib.Concepts.WalkFind.SearchAlgorithm.frobeniusSq (U * C) =
        Qatlib.Concepts.WalkFind.SearchAlgorithm.frobeniusSq C

theorem theorem7 : Theorem7Statement :=
  fun m n U C hU =>
    Qatlib.Concepts.WalkFind.WalkSpectrum.normalSpectralPerturbation_answer.1
      m n U C hU

def Theorem8Statement : Prop :=
  ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) ℂ),
    C.conjTranspose * C = C * C.conjTranspose →
    D.conjTranspose * D = D * D.conjTranspose →
      ∃ (E F : Matrix (Fin n) (Fin n) ℂ)
        (eigenC eigenD : Fin n → ℂ) (σ : Equiv.Perm (Fin n)),
        E ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        F ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        C * E = E * Matrix.diagonal eigenC ∧
        D * F = F * Matrix.diagonal eigenD ∧
        (∑ i : Fin n, ‖eigenC i - eigenD (σ i)‖ ^ 2) ≤
          Qatlib.Concepts.WalkFind.SearchAlgorithm.frobeniusSq (C - D)

theorem theorem8 : Theorem8Statement :=
  fun n C D hC hD =>
    Qatlib.Concepts.WalkFind.WalkSpectrum.normalSpectralPerturbation_answer.2.1
      n C D hC hD

def Claim1Statement : Prop :=
  ∀ (k N r : ℕ) (i j : Fin (2 * k + 1)),
    Qatlib.Concepts.WalkFind.UniqueCollision.jwStep1 k N r i j =
      if (Qatlib.Concepts.WalkFind.UniqueCollision.jwPsiCoord k i).1 =
          (Qatlib.Concepts.WalkFind.UniqueCollision.jwPsiCoord k j).1 then
        Qatlib.Concepts.WalkFind.UniqueCollision.jwD2
          ((k - (Qatlib.Concepts.WalkFind.UniqueCollision.jwPsiCoord k j).1 : ℝ) /
            (N - r))
          (Qatlib.Concepts.WalkFind.UniqueCollision.jwPsiCoord k i).2
          (Qatlib.Concepts.WalkFind.UniqueCollision.jwPsiCoord k j).2
      else 0

theorem claim1 : Claim1Statement :=
  Qatlib.Concepts.WalkFind.WalkSpectrum.jwStep1_entry_types

end Qatlib.Concepts.WalkFind.WalkSpectrum
