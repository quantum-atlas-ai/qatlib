/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.KrausCompile.BornMoments.BornReadout
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open scoped ComplexOrder Classical

namespace Qatlib.Concepts.KrausCompile.Sequential

structure Stage (d : ℕ) where
  n : ℕ
  K : Fin n → Operator d
  complete : ∑ i, (K i).conjTranspose * K i = 1
  w : Fin n → ℝ

def Hist {d : ℕ} : List (Stage d) → Type
  | [] => PUnit
  | s :: ss => Fin s.n × Hist ss

noncomputable instance histFintype {d : ℕ} (ss : List (Stage d)) : Fintype (Hist ss) := by
  induction ss with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons s ss ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin s.n × Hist ss))

noncomputable def pathKraus {d : ℕ} : (ss : List (Stage d)) → Hist ss → Operator d
  | [], _ => 1
  | s :: ss, h => pathKraus ss h.2 * s.K h.1

noncomputable def pathWeight {d : ℕ} : (ss : List (Stage d)) → Hist ss → ℝ
  | [], _ => 1
  | s :: ss, h => pathWeight ss h.2 * s.w h.1

def HasZeroWeight {d : ℕ} : (ss : List (Stage d)) → Hist ss → Prop
  | [], _ => False
  | s :: ss, h => s.w h.1 = 0 ∨ HasZeroWeight ss h.2

theorem pathWeight_zero {d : ℕ} (ss : List (Stage d)) (h : Hist ss)
    (hz : HasZeroWeight ss h) : pathWeight ss h = 0 := by
  induction ss with
  | nil => exact False.elim hz
  | cons s ss ih =>
      rcases hz with hz | hz
      · simp only [pathWeight, hz, mul_zero]
      · simp only [pathWeight, ih h.2 hz, zero_mul]

theorem pathKraus_complete {d : ℕ} (ss : List (Stage d)) :
    ∑ h : Hist ss, (pathKraus ss h).conjTranspose * pathKraus ss h = 1 := by
  induction ss with
  | nil => simp [Hist, pathKraus]
  | cons s ss ih =>
      change (∑ h : Fin s.n × Hist ss,
        (pathKraus ss h.2 * s.K h.1).conjTranspose * (pathKraus ss h.2 * s.K h.1)) = 1
      rw [Fintype.sum_prod_type]
      have hinner (i : Fin s.n) :
          (∑ h : Hist ss, (pathKraus ss h * s.K i).conjTranspose * (pathKraus ss h * s.K i)) =
            (s.K i).conjTranspose * s.K i := by
        calc
          _ = (s.K i).conjTranspose *
              (∑ h : Hist ss, (pathKraus ss h).conjTranspose * pathKraus ss h) * s.K i := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro h _
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = _ := by rw [ih]; simp
      simp_rw [hinner]
      exact s.complete

noncomputable def jointInstrument {d : ℕ} (ss : List (Stage d)) : Instrument (Hist ss) d d :=
  Instrument.ofKraus (pathKraus ss) (pathKraus_complete ss)

theorem jointInstrument_cons_branch {d : ℕ} (s : Stage d) (ss : List (Stage d))
    (h : Hist (s :: ss)) (ρ : Operator d) :
    (jointInstrument (s :: ss)).branch h ρ =
      ((Instrument.ofKraus s.K s.complete).seq (jointInstrument ss)).branch h ρ := by
  change (pathKraus ss h.2 * s.K h.1) * ρ * (pathKraus ss h.2 * s.K h.1).conjTranspose =
    pathKraus ss h.2 * (s.K h.1 * ρ * (s.K h.1).conjTranspose) * (pathKraus ss h.2).conjTranspose
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

noncomputable def weightedLinear {d : ℕ} (s : Stage d) : Operator d →ₗ[ℂ] Operator d :=
  ∑ i, (s.w i : ℂ) • conjBranch (s.K i)

noncomputable def composedWeighted {d : ℕ} : List (Stage d) → (Operator d →ₗ[ℂ] Operator d)
  | [] => LinearMap.id
  | s :: ss => (composedWeighted ss).comp (weightedLinear s)

theorem weightedPath_eq_composed {d : ℕ} (ss : List (Stage d)) (ρ : Operator d) :
    (∑ h : Hist ss, (pathWeight ss h : ℂ) •
      (pathKraus ss h * ρ * (pathKraus ss h).conjTranspose)) = composedWeighted ss ρ := by
  induction ss generalizing ρ with
  | nil => simp [Hist, pathKraus, pathWeight, composedWeighted]
  | cons s ss ih =>
      change (∑ h : Fin s.n × Hist ss, ((pathWeight ss h.2 * s.w h.1 : ℝ) : ℂ) •
        ((pathKraus ss h.2 * s.K h.1) * ρ * (pathKraus ss h.2 * s.K h.1).conjTranspose)) =
          composedWeighted ss (weightedLinear s ρ)
      rw [Fintype.sum_prod_type]
      simp only [weightedLinear, LinearMap.sum_apply, LinearMap.smul_apply,
        conjBranch_apply, map_sum, map_smul]
      simp_rw [← ih]
      simp only [Finset.smul_sum, smul_smul, Complex.ofReal_mul,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro h _
      rw [mul_comm (pathWeight ss h : ℂ) (s.w i : ℂ)]

noncomputable def finalJointLaw {d : ℕ} (ss : List (Stage d)) {O : Type} [Fintype O]
    (J : Instrument O d d) {ρ : Operator d} (hρ : IsDensityOperator ρ) : PMF (Hist ss × O) :=
  instrumentPMF ((jointInstrument ss).seq J) hρ

noncomputable def finalValue {d : ℕ} (ss : List (Stage d)) {O : Type}
    (v : O → ℝ) (x : Hist ss × O) : ℝ := pathWeight ss x.1 * v x.2

theorem finalValue_zero {d : ℕ} (ss : List (Stage d)) {O : Type} (v : O → ℝ)
    (h : Hist ss) (o : O) (hz : HasZeroWeight ss h) : finalValue ss v (h,o) = 0 := by
  change pathWeight ss h * v o = 0
  rw [pathWeight_zero ss h hz, zero_mul]

theorem final_weighted_readout {d : ℕ} (ss : List (Stage d)) {O : Type} [Fintype O]
    (J : Instrument O d d) (v : O → ℝ) {ρ : Operator d} (hρ : IsDensityOperator ρ) :
    (∑ x : Hist ss × O, (finalJointLaw ss J hρ x).toReal * finalValue ss v x) =
      ∑ o : O, v o * (Matrix.trace (J.branch o (composedWeighted ss ρ))).re := by
  have hmass (h : Hist ss) (o : O) : (finalJointLaw ss J hρ (h,o)).toReal =
      (Matrix.trace (J.branch o (pathKraus ss h * ρ * (pathKraus ss h).conjTranspose))).re := by
    rw [finalJointLaw, instrumentPMF_apply,
      ENNReal.toReal_ofReal (instrumentProb_nonneg _ hρ.1 (h,o))]
    rfl
  rw [Fintype.sum_prod_type]
  simp only [hmass, finalValue]
  rw [← weightedPath_eq_composed ss ρ]
  simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_comm, mul_assoc]

noncomputable def spectralReadout {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : Instrument (Fin d) d d :=
  measuredInstrument V.conjTranspose (by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hV))

theorem spectralReadout_branch {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (j : Fin d) (A : Operator d) :
    (spectralReadout V hV).branch j A =
      (Projector ({j} : Finset (Fin d)) * V.conjTranspose) * A *
        (Projector ({j} : Finset (Fin d)) * V.conjTranspose).conjTranspose := by
  change ((conjBranch (Projector ({j} : Finset (Fin d)))).comp (conjBranch V.conjTranspose)) A = _
  rw [conjBranch_comp, conjBranch_apply]

theorem spectralReadout_mass {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (j : Fin d) (A : Operator d) :
    (Matrix.trace ((spectralReadout V hV).branch j A)).re =
      ((V.conjTranspose * A * V) j j).re := by
  change instrumentProb projectiveInstrument (conjBranch V.conjTranspose A) j = _
  rw [instrumentProb_projective, conjBranch_apply, Matrix.conjTranspose_conjTranspose]

theorem spectralReadout_mean {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) (A : Operator d) :
    (∑ j : Fin d, eig j * (Matrix.trace ((spectralReadout V hV).branch j A)).re) =
      (A * Qatlib.Concepts.KrausCompile.BornMoments.observable V eig).trace.re := by
  rw [Qatlib.Concepts.KrausCompile.BornMoments.trace_observable]
  apply Finset.sum_congr rfl
  intro j _
  rw [spectralReadout_mass]
  ring

theorem final_observable_expectation {d : ℕ} (ss : List (Stage d)) (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ)
    {ρ : Operator d} (hρ : IsDensityOperator ρ) :
    (∑ x : Hist ss × Fin d, (finalJointLaw ss (spectralReadout V hV) hρ x).toReal *
      finalValue ss eig x) =
      (composedWeighted ss ρ *
        Qatlib.Concepts.KrausCompile.BornMoments.observable V eig).trace.re := by
  rw [final_weighted_readout]
  exact spectralReadout_mean V hV eig (composedWeighted ss ρ)

end Qatlib.Concepts.KrausCompile.Sequential
