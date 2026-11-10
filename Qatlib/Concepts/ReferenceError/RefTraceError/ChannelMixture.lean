/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ReferenceError.RefTraceError.MixedStateChannels
import Qatlib.Foundations.PureStateMath.MixedState
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ReferenceError.RefTraceError

open scoped ComplexOrder
open Matrix

noncomputable def ChannelMixture {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (d : FinDist J) (U : J → Matrix I I ℂ) : Matrix I I ℂ → Matrix I I ℂ :=
  fun ρ => ∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)

theorem channelMixture_apply {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (d : FinDist J) (U : J → Matrix I I ℂ) (ρ : Matrix I I ℂ) (a b : I) :
    ChannelMixture d U ρ a b = ∑ j, (d.prob j : ℂ) * (U j * ρ * (U j)ᴴ) a b := by
  simp only [ChannelMixture, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem channelMixture_add {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (d : FinDist J) (U : J → Matrix I I ℂ) (ρ σ : Matrix I I ℂ) :
    ChannelMixture d U (ρ + σ) = ChannelMixture d U ρ + ChannelMixture d U σ := by
  show ∑ j, (d.prob j : ℂ) • (U j * (ρ + σ) * (U j)ᴴ)
      = (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ))
        + ∑ j, (d.prob j : ℂ) • (U j * σ * (U j)ᴴ)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem channelMixture_smul {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (d : FinDist J) (U : J → Matrix I I ℂ) (c : ℂ) (ρ : Matrix I I ℂ) :
    ChannelMixture d U (c • ρ) = c • ChannelMixture d U ρ := by
  show ∑ j, (d.prob j : ℂ) • (U j * (c • ρ) * (U j)ᴴ)
      = c • ∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [mul_smul_comm, smul_mul_assoc, smul_comm]

theorem trace_channelMixture {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Matrix (Fin D) (Fin D) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ChannelMixture d U ρ) = Matrix.trace ρ := by
  have hU' : ∀ j, (U j)ᴴ * U j = 1 := fun j => by
    have h := (Matrix.mem_unitaryGroup_iff').mp (hU j)
    rwa [Matrix.star_eq_conjTranspose] at h
  have htr : ∀ j, Matrix.trace (U j * ρ * (U j)ᴴ) = Matrix.trace ρ := fun j => by
    calc Matrix.trace (U j * ρ * (U j)ᴴ)
        = Matrix.trace ((U j)ᴴ * (U j * ρ)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((U j)ᴴ * U j) * ρ) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ρ := by rw [hU' j, Matrix.one_mul]
  calc Matrix.trace (ChannelMixture d U ρ)
      = ∑ j, (d.prob j : ℂ) * Matrix.trace (U j * ρ * (U j)ᴴ) := by
        show Matrix.trace (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) = _
        rw [Matrix.trace_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Matrix.trace_smul, smul_eq_mul]
    _ = ∑ j, (d.prob j : ℂ) * Matrix.trace ρ :=
        Finset.sum_congr rfl fun j _ => by rw [htr j]
    _ = (∑ j, (d.prob j : ℂ)) * Matrix.trace ρ := (Finset.sum_mul _ _ _).symm
    _ = Matrix.trace ρ := by
        rw [← Complex.ofReal_sum, d.sum_one, Complex.ofReal_one, one_mul]

theorem channelMixture_maps_density {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Matrix (Fin D) (Fin D) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (ChannelMixture d U ρ) := by
  refine ⟨?_, ?_⟩
  · show (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)).PosSemidef
    refine Matrix.posSemidef_sum Finset.univ fun j _ => ?_
    exact Matrix.PosSemidef.smul (hρ.1.mul_mul_conjTranspose_same (U j))
      (RCLike.ofReal_nonneg.mpr (d.nonneg j))
  · rw [trace_channelMixture d U hU ρ]
    exact hρ.2

end Qatlib.Concepts.ReferenceError.RefTraceError
