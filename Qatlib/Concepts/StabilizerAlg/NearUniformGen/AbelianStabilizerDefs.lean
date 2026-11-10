/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.CompositeMeasurementNearUniformQuan
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.NearUniformGenerationSubgoalQuan
import Qatlib.Concepts.HspRecovery.AbelianSampling.MeasuredGenerationSubgoalQuan
import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasis
set_option warningAsError false
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.StabilizerAlg.NearUniformGen

set_option autoImplicit false

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

open Qatlib
open scoped BigOperators Classical

structure AspRecordKernel (Ω G : Type*) [Fintype Ω] [DecidableEq Ω]
    [Fintype G] [DecidableEq G] where

  branchLaw : FinDist Ω

  conditional : Ω → FinDist G

namespace AspRecordKernel

variable {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype G] [DecidableEq G]

def joint (k : AspRecordKernel Ω G) (V : Ω) (y : G) : ℝ :=
  k.branchLaw.prob V * (k.conditional V).prob y

def marginal (k : AspRecordKernel Ω G) : FinDist G where
  prob y := ∑ V, k.joint V y
  nonneg y := by
    refine Finset.sum_nonneg fun V _ => ?_
    exact mul_nonneg (k.branchLaw.nonneg V) ((k.conditional V).nonneg y)
  sum_one := by
    have hswap : (∑ y : G, ∑ V : Ω, k.branchLaw.prob V * (k.conditional V).prob y)
        = ∑ V : Ω, ∑ y : G, k.branchLaw.prob V * (k.conditional V).prob y :=
      Finset.sum_comm
    have hmul (V : Ω) :
        (∑ y : G, k.branchLaw.prob V * (k.conditional V).prob y)
          = k.branchLaw.prob V * ∑ y : G, (k.conditional V).prob y := by
      rw [Finset.mul_sum]
    calc
      ∑ y : G, ∑ V : Ω, k.branchLaw.prob V * (k.conditional V).prob y
          = ∑ V : Ω, ∑ y : G, k.branchLaw.prob V * (k.conditional V).prob y := hswap
      _ = ∑ V : Ω, k.branchLaw.prob V * ∑ y : G, (k.conditional V).prob y := by
          refine Finset.sum_congr rfl fun V _ => hmul V
      _ = ∑ V : Ω, k.branchLaw.prob V * 1 := by
          refine Finset.sum_congr rfl fun V _ => ?_
          rw [(k.conditional V).sum_one, mul_one]
      _ = ∑ V : Ω, k.branchLaw.prob V := by
          refine Finset.sum_congr rfl fun V _ => mul_one _
      _ = 1 := k.branchLaw.sum_one

theorem marginal_total_mass (k : AspRecordKernel Ω G) :
    (∑ y : G, ∑ V : Ω, k.branchLaw.prob V * (k.conditional V).prob y) = 1 := by
  have h := k.marginal.sum_one
  simpa [AspRecordKernel.marginal, AspRecordKernel.joint] using h

def jointLaw (k : AspRecordKernel Ω G) : FinDist (Ω × G) where
  prob p := k.joint p.1 p.2
  nonneg p := mul_nonneg (k.branchLaw.nonneg p.1) ((k.conditional p.1).nonneg p.2)
  sum_one := by
    calc
      ∑ p : Ω × G, k.joint p.1 p.2
          = ∑ V : Ω, ∑ y : G, k.joint V y := by
            rw [Fintype.sum_prod_type]
      _ = ∑ y : G, ∑ V : Ω, k.joint V y := Finset.sum_comm
      _ = 1 := by simpa [AspRecordKernel.joint] using k.marginal_total_mass

end AspRecordKernel

noncomputable def aspUniformBranchLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinDist Ω where
  prob _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    have hcard : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact mul_inv_cancel₀ (ne_of_gt hcard)

noncomputable def aspUniformGroupBranchLaw (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) : FinDist ↥H :=
  aspUniformBranchLaw ↥H

noncomputable def aspOrbitBranchLaw (E : Type) [AddCommGroup E] [Fintype E]
    [DecidableEq E] : FinDist (AddChar E ℂ) :=
  Qatlib.Concepts.HspRecovery.AbelianSampling.fourierBornDist E

theorem aspCharacterGroup_card (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E] :
    Fintype.card (AddChar E ℂ) = Fintype.card E :=
  AddChar.card_eq

theorem aspOrbitBranchLaw_uniform (E : Type) [AddCommGroup E] [Fintype E]
    [DecidableEq E] (χ : AddChar E ℂ) :
    (aspOrbitBranchLaw E).prob χ = (Fintype.card E : ℝ)⁻¹ :=
  Qatlib.Concepts.HspRecovery.AbelianSampling.fourierBornDist_apply E χ

def aspMeasuresWithError {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype G]
    [DecidableEq G] (k : AspRecordKernel Ω G) (F : Ω → G) (ε : ℝ) : Prop :=
  ∀ V, 1 - ε ≤ (k.conditional V).prob (F V)

def aspProductRecordLaw {G : Type*} [Fintype G] [DecidableEq G] (μ : FinDist G)
    (l : ℕ) : FinDist (Fin l → G) where
  prob ω := μ.probOf ω
  nonneg ω := Finset.prod_nonneg fun i _ => μ.nonneg (ω i)
  sum_one := FinDist.sum_probOf μ l

noncomputable def aspPointConditional {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype G]
    [DecidableEq G] (F : Ω → G) : Ω → FinDist G := fun V =>
  { prob := fun y => if y = F V then (1 : ℝ) else 0
    nonneg := by
      intro y
      by_cases h : y = F V <;> simp [h]
    sum_one := by
      rw [Finset.sum_ite_eq']
      simp }

noncomputable def aspUniformLaw (G : Type*) [Fintype G] [Nonempty G] : FinDist G where
  prob _ := (Fintype.card G : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    have hcard : (0 : ℝ) < (Fintype.card G : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact mul_inv_cancel₀ (ne_of_gt hcard)

noncomputable def finDistMix {G : Type*} [Fintype G] [DecidableEq G] (μ ν : FinDist G)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) : FinDist G where
  prob x := w * μ.prob x + (1 - w) * ν.prob x
  nonneg x := by
    refine add_nonneg (mul_nonneg hw (μ.nonneg x)) ?_
    have : 0 ≤ 1 - w := by linarith
    exact mul_nonneg this (ν.nonneg x)
  sum_one := by
    have hμ : ∑ x, μ.prob x = 1 := μ.sum_one
    have hν : ∑ x, ν.prob x = 1 := ν.sum_one
    calc
      ∑ x, (w * μ.prob x + (1 - w) * ν.prob x)
          = (w * ∑ x, μ.prob x) + ((1 - w) * ∑ x, ν.prob x) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = w * 1 + (1 - w) * 1 := by rw [hμ, hν]
      _ = 1 := by ring

noncomputable def aspBoundedErrorConditional {Ω G : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype G] [DecidableEq G] [Nonempty G] (F : Ω → G) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) : Ω → FinDist G :=
  fun V =>
    finDistMix (aspPointConditional F V) (aspUniformLaw G) (1 - ε) (by linarith) (by linarith)

structure AspBisectionState where

  level : ℕ

  bits : ℕ

  bits_lt : bits < 2 ^ level

  queries : ℕ

  queries_eq_level : queries = level

namespace AspBisectionState

variable {s : AspBisectionState}

noncomputable def lower (s : AspBisectionState) : ℝ := (s.bits : ℝ) / 2 ^ s.level

noncomputable def width (s : AspBisectionState) : ℝ := 1 / 2 ^ s.level

noncomputable def mid (s : AspBisectionState) : ℝ := s.lower + s.width / 2

def step (s : AspBisectionState) (b : Bool) : AspBisectionState where
  level := s.level + 1
  bits := 2 * s.bits + b.toNat
  bits_lt := by
    have h := s.bits_lt
    simp only [Nat.pow_succ]
    by_cases hb : b = true
    · simp [hb]
      omega
    · have hb' : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd rfl hb
      simp [hb']
      omega
  queries := s.queries + 1
  queries_eq_level := by
    have h := s.queries_eq_level
    omega

end AspBisectionState

def aspBisectionInitial : AspBisectionState where
  level := 0
  bits := 0
  bits_lt := by simp
  queries := 0
  queries_eq_level := rfl

def aspBisectionStateAt : (ℕ → Bool) → ℕ → AspBisectionState
  | _, 0 => aspBisectionInitial
  | o, k + 1 => (aspBisectionStateAt o k).step (o k)

def aspBisectionAux : (ℕ → Bool) → ℕ → AspBisectionState → AspBisectionState
  | _, 0, s => s
  | o, n + 1, s => aspBisectionAux o n (s.step (o s.level))

def aspBisectionRun (l : ℕ) (o : ℕ → Bool) : AspBisectionState :=
  aspBisectionStateAt o (l + 2)

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
