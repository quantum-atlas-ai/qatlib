/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.PhysicalRounding
import Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# Finite hybrid state selection

Constructs finite pushforward laws for selecting the lower-energy state from a fixed candidate
and a sampled candidate. Rounded product candidates and selected outputs are positive
semidefinite with trace one when their inputs are physical, and the expected selected energy is
bounded by any convex combination of candidate energies. See [CrostaSaubanereHuber2026].

## Main statements

* `idealLaw_energy`: identifies expected output energy with the expected pointwise minimum.
* `output_density`: proves physicality of either selected candidate.
* `ideal_expected_convex`: gives the convex-combination energy bound.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

/-- The pushforward of a finite probability distribution along `f`, obtained by summing masses
over each fiber. -/
noncomputable def push {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]
    (q : FinDist Ω) (f : Ω → Λ) : FinDist Λ where
  prob y := ∑ x, if f x=y then q.prob x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split; exact q.nonneg x; exact le_rfl)
  sum_one := by
    rw [Finset.sum_comm]
    simpa using q.sum_one

/-- Expectation under a finite pushforward equals expectation of the function composed with the
pushforward map. -/
theorem push_expect {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]
    (q : FinDist Ω) (f : Ω → Λ) (g : Λ → ℝ) :
    (push q f).expect g=q.expect (fun x => g (f x)) := by
  simp only [FinDist.expect,push,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Pointwise domination of real functions implies domination of their expectations under a
finite probability distribution. -/
theorem expect_mono {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω)
    (f g : Ω → ℝ) (h : ∀ x,f x≤g x) : q.expect f≤q.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (q.nonneg x))

/-- The product density matrix formed from the physically rounded vectors associated with `ρ`
and sample matrix `R ω`. -/
noncomputable def productCandidate {n : ℕ} {Ω : Type*}
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram.MomentIndex n → ℝ) (ω : Ω) :
    Matrix (Reg n) (Reg n) ℂ := productState (physicalRound n ρ hρ htr (R ω))

/-- Every rounded product candidate from a positive semidefinite trace-one input is positive
semidefinite and has trace one. -/
theorem productCandidate_density {n : ℕ} {Ω : Type*}
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Ω → Fin 3 → Fin 2×Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram.MomentIndex n → ℝ) (ω : Ω) :
    (productCandidate ρ hρ htr R ω).PosSemidef ∧ (productCandidate ρ hρ htr R ω).trace=1 :=
  physical_round_density n ρ hρ htr (R ω)

/-- The Boolean selector that chooses the fixed candidate when its energy is no larger than the
sampled candidate's energy. -/
noncomputable def idealChoice {n : ℕ} {Ω : Type*} (H : Matrix (Reg n) (Reg n) ℂ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (ω : Ω) : Bool :=
  if energy H ρ≤energy H (σ ω) then true else false

/-- The candidate selected by a sample and Boolean flag: `ρ` for true and `σ out.1` for false. -/
def outputDensity {n : ℕ} {Ω : Type*} (ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (out : Ω×Bool) : Matrix (Reg n) (Reg n) ℂ :=
  if out.2 then ρ else σ out.1

/-- The finite pushforward law retaining the original sample together with its ideal
energy-comparison flag. -/
noncomputable def idealLaw {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω)
    (H : Matrix (Reg n) (Reg n) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) : FinDist (Ω×Bool) :=
  push q (fun ω => (ω,idealChoice H ρ σ ω))

/-- Selecting between a positive semidefinite trace-one fixed candidate and a family of such
candidates always yields a positive semidefinite trace-one matrix. -/
theorem output_density {n : ℕ} {Ω : Type*} (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (σ : Ω → Matrix (Reg n) (Reg n) ℂ)
    (hσ : ∀ ω,(σ ω).PosSemidef ∧ (σ ω).trace=1) (out : Ω×Bool) :
    (outputDensity ρ σ out).PosSemidef ∧ (outputDensity ρ σ out).trace=1 := by
  cases h : out.2
  · simpa only [outputDensity,h,Bool.false_eq_true,ite_false] using hσ out.1
  · simpa only [outputDensity,h,ite_true] using And.intro hρ htr

/-- The ideal selector returns a candidate whose energy is the minimum of the fixed and sampled
energies. -/
theorem ideal_energy {n : ℕ} {Ω : Type*} (H : Matrix (Reg n) (Reg n) ℂ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (ω : Ω) :
    energy H (outputDensity ρ σ (ω,idealChoice H ρ σ ω))=min (energy H ρ) (energy H (σ ω)) := by
  by_cases h : energy H ρ≤energy H (σ ω)
  · simp only [idealChoice,h,ite_true,outputDensity,min_eq_left h]
  · simp only [idealChoice,h,ite_false,outputDensity,Bool.false_eq_true,min_eq_right (le_of_not_ge h)]

/-- The expected energy under the ideal output law equals the expectation of the pointwise
minimum of the two candidate energies. -/
theorem idealLaw_energy {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω)
    (H : Matrix (Reg n) (Reg n) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) :
    (idealLaw q H ρ σ).expect (fun out => energy H (outputDensity ρ σ out))=
      q.expect (fun ω => min (energy H ρ) (energy H (σ ω))) := by
  rw [idealLaw,push_expect]
  simp_rw [ideal_energy]

/-- The real-weighted matrix combination `p • ρ + (1 - p) • σ`. -/
noncomputable def mixture {n : ℕ} (p : ℝ) (ρ σ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n) (Reg n) ℂ := p • ρ+(1-p) • σ

/-- For `p ∈ [0,1]`, a mixture of two positive semidefinite trace-one matrices is positive
semidefinite with trace one. -/
theorem mixture_density {n : ℕ} (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (ρ σ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htrρ : ρ.trace=1)
    (hσ : σ.PosSemidef) (htrσ : σ.trace=1) :
    (mixture p ρ σ).PosSemidef ∧ (mixture p ρ σ).trace=1 := by
  refine ⟨(hρ.smul hp0).add (hσ.smul (by linarith : 0≤1-p)),?_⟩
  simp only [mixture,Matrix.trace_add,Matrix.trace_smul,htrρ,htrσ,Complex.real_smul,mul_one]
  push_cast
  ring

/-- The energy of the matrix mixture is `p * energy H ρ + (1 - p) * energy H σ`. -/
theorem mixture_energy {n : ℕ} (H ρ σ : Matrix (Reg n) (Reg n) ℂ) (p : ℝ) :
    energy H (mixture p ρ σ)=p*energy H ρ+(1-p)*energy H σ := by
  simp [mixture,energy,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]

/-- For `p ∈ [0,1]`, the minimum of `x` and `y` is at most `p * x + (1 - p) * y`. -/
theorem min_le_mixture (x y p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    min x y≤p*x+(1-p)*y := by
  rcases le_total x y with h|h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith

/-- For `p ∈ [0,1]`, the expected ideal-output energy is at most `p` times the fixed energy plus
`1 - p` times the expected sampled energy. -/
theorem ideal_expected_convex {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω)
    (H : Matrix (Reg n) (Reg n) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (idealLaw q H ρ σ).expect (fun out => energy H (outputDensity ρ σ out))≤
      p*energy H ρ+(1-p)*q.expect (fun ω => energy H (σ ω)) := by
  rw [idealLaw_energy]
  have h := expect_mono q _ _ (fun ω => min_le_mixture (energy H ρ) (energy H (σ ω)) p hp0 hp1)
  convert h using 1
  simp only [FinDist.expect,mul_add,Finset.sum_add_distrib]
  rw [show (∑ ω,q.prob ω*(p*energy H ρ))=p*energy H ρ from by
    rw [← Finset.sum_mul,q.sum_one,one_mul]]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring
end Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
