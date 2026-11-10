/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Mathlib.Analysis.Matrix.Order
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.KrausCompile.BornMoments
open Matrix
open MeasureTheory
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open scoped BigOperators ComplexOrder

def observable {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) (eig : Fin d → ℝ) : Operator d :=
  V * diagonal (fun j => (eig j : ℂ)) * V.conjTranspose

def rotatedBranch {d s : ℕ} (K : Fin s → Operator d) (ρ V : Operator d)
    (i : Fin s) : Operator d := V.conjTranspose * (K i * ρ * (K i).conjTranspose) * V

def bornMass {d s : ℕ} (K : Fin s → Operator d) (ρ V : Operator d)
    (z : Fin s × Fin d) : ℝ := (rotatedBranch K ρ V z.1 z.2 z.2).re

theorem bornMass_nonneg {d s : ℕ} (K : Fin s → Operator d) (ρ V : Operator d)
    (hρ : ρ.PosSemidef) (z : Fin s × Fin d) : 0 ≤ bornMass K ρ V z := by
  have h := (hρ.mul_mul_conjTranspose_same (K z.1)).conjTranspose_mul_mul_same V
  exact (Complex.nonneg_iff.mp (h.diag_nonneg (i := z.2))).1

theorem rotatedBranch_trace {d s : ℕ} (K : Fin s → Operator d) (ρ V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (i : Fin s) :
    (rotatedBranch K ρ V i).trace = (K i * ρ * (K i).conjTranspose).trace := by
  have hVV : V * V.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  unfold rotatedBranch
  rw [Matrix.trace_mul_cycle, hVV, one_mul]

theorem bornMass_sum {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : ∑ z, bornMass K ρ V z = 1 := by
  have htp := tracePreserving_of_krausComplete (krausForm_krausMap K) hK ρ
  have hsum : (∑ i, (K i * ρ * (K i).conjTranspose).trace) = 1 := by
    simpa only [krausMap, LinearMap.sum_apply, conjBranch_apply, Matrix.trace_sum, hρ] using htp
  rw [Fintype.sum_prod_type]
  change (∑ i, ∑ j, (rotatedBranch K ρ V i j j).re) = 1
  have hrow (i : Fin s) : (∑ j, (rotatedBranch K ρ V i j j).re) =
      (K i * ρ * (K i).conjTranspose).trace.re := by
    rw [← Complex.re_sum]
    exact congrArg Complex.re (rotatedBranch_trace K ρ V hV i)
  simp_rw [hrow]
  rw [← Complex.re_sum, hsum]
  rfl

def bornLaw {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : FinDist (Fin s × Fin d) where
  prob := bornMass K ρ V
  nonneg := bornMass_nonneg K ρ V hρ
  sum_one := bornMass_sum K hK ρ V htρ hV

def bornPMF {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : PMF (Fin s × Fin d) :=
  toPMF (bornLaw K hK ρ V hρ htρ hV)

theorem bornPMF_mass {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (z : Fin s × Fin d) :
    (bornPMF K hK ρ V hρ htρ hV z).toReal = bornMass K ρ V z := by
  exact ENNReal.toReal_ofReal (bornMass_nonneg K ρ V hρ z)

theorem trace_observable {d : ℕ} (A V : Operator d) (eig : Fin d → ℝ) :
    (A * observable V eig).trace.re = ∑ j, ((V.conjTranspose * A * V) j j).re * eig j := by
  unfold observable
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

def readout {d s : ℕ} (w : Fin s → ℝ) (eig : Fin d → ℝ) (z : Fin s × Fin d) : ℝ :=
  w z.1 * eig z.2

theorem readout_mean {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : Fin s → ℝ) (eig : Fin d → ℝ) :
    (bornLaw K hK ρ V hρ htρ hV).expect (readout w eig) =
      ∑ i, w i * (K i * ρ * (K i).conjTranspose * observable V eig).trace.re := by
  unfold FinDist.expect bornLaw
  rw [Fintype.sum_prod_type]
  simp_rw [trace_observable, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp [bornMass, rotatedBranch, readout]
  ring

theorem observable_sq {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) :
    observable V eig ^ 2 = observable V (fun j => eig j ^ 2) := by
  have hVV : V.conjTranspose * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  let D := diagonal (fun j => (eig j : ℂ))
  change (V * D * V.conjTranspose) ^ 2 = _
  calc
    (V * D * V.conjTranspose) ^ 2 = V * D * (V.conjTranspose * V) * D * V.conjTranspose := by
      simp only [pow_two, mul_assoc]
    _ = V * (D * D) * V.conjTranspose := by rw [hVV]; simp only [mul_one, mul_assoc]
    _ = observable V (fun j => eig j ^ 2) := by
      simp only [D, Matrix.diagonal_mul_diagonal, observable, pow_two, Complex.ofReal_mul]

theorem readout_second {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : Fin s → ℝ) (eig : Fin d → ℝ) :
    (bornLaw K hK ρ V hρ htρ hV).expect (fun z => readout w eig z ^ 2) =
      ∑ i, w i ^ 2 * (K i * ρ * (K i).conjTranspose * observable V eig ^ 2).trace.re := by
  have hshot : (fun z => readout w eig z ^ 2) =
      readout (fun i => w i ^ 2) (fun j => eig j ^ 2) := by
    funext z
    simp only [readout, mul_pow]
  rw [hshot, readout_mean, observable_sq V hV eig]

theorem readout_variance {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : Fin s → ℝ) (eig : Fin d → ℝ) :
    (bornLaw K hK ρ V hρ htρ hV).variance (readout w eig) =
      (∑ i, w i ^ 2 * (K i * ρ * (K i).conjTranspose * observable V eig ^ 2).trace.re) -
        (∑ i, w i * (K i * ρ * (K i).conjTranspose * observable V eig).trace.re) ^ 2 := by
  rw [FinDist.variance_eq_expect_sq_sub, readout_second, readout_mean]

theorem hermitian_readout_exists {d : ℕ} (O : Operator d) (hO : O.IsHermitian) :
    ∃ V : Operator d, V ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      ∃ eig : Fin d → ℝ, O = observable V eig := by
  refine ⟨hO.eigenvectorUnitary, (hO.eigenvectorUnitary).property, hO.eigenvalues, ?_⟩
  have h := hO.spectral_theorem
  simpa only [Unitary.conjStarAlgAut_apply, observable] using! h

theorem readout_variance_nonneg {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : Fin s → ℝ) (eig : Fin d → ℝ) :
    0 ≤ (bornLaw K hK ρ V hρ htρ hV).variance (readout w eig) := by
  exact Finset.sum_nonneg (fun z _ =>
    mul_nonneg (bornMass_nonneg K ρ V hρ z) (sq_nonneg _))

theorem bornPMF_integral {d s : ℕ}
    [MeasurableSpace (Fin s × Fin d)] [MeasurableSingletonClass (Fin s × Fin d)]
    (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (f : Fin s × Fin d → ℝ) :
    ∫ z, f z ∂(bornPMF K hK ρ V hρ htρ hV).toMeasure =
      (bornLaw K hK ρ V hρ htρ hV).expect f := by
  rw [PMF.integral_eq_sum]
  simp only [bornPMF_mass, smul_eq_mul, FinDist.expect, bornLaw]

theorem bornPMF_centered_integral {d s : ℕ}
    [MeasurableSpace (Fin s × Fin d)] [MeasurableSingletonClass (Fin s × Fin d)]
    (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ V : Operator d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (w : Fin s → ℝ) (eig : Fin d → ℝ) :
    ∫ z, (readout w eig z - (bornLaw K hK ρ V hρ htρ hV).expect (readout w eig)) ^ 2
      ∂(bornPMF K hK ρ V hρ htρ hV).toMeasure =
        (bornLaw K hK ρ V hρ htρ hV).variance (readout w eig) := by
  exact bornPMF_integral K hK ρ V hρ htρ hV _

end Qatlib.Concepts.KrausCompile.BornMoments
