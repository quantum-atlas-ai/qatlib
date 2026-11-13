/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid

/-!
# Pauli readout and rational energy scores

`finDensity` transfers register-indexed matrices to the finite operator representation used by
the Pauli measurement channel. `readoutLaw` is its Born outcome distribution, while `wordValueQ`
and `energyScoreQ` give rational scores whose real expectations recover Pauli correlations and
quantum Max Cut energy.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `pair_readout_mean`: the Pauli pair score has the prescribed correlation as its mean.
* `energyScoreQ_unbiased`: the rational energy score is unbiased.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.PauliReadout
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds

/-- The register matrix `ρ` relabelled as an operator on `Fin (2^n)`. -/
noncomputable def finDensity (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) : Operator (2^n) :=
  relabelGate (bitVecEquiv n) ρ

/-- Relabelling a positive semidefinite register matrix of trace one gives a density operator. -/
theorem finDensity_physical (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    IsDensityOperator (finDensity n ρ) := by
  refine ⟨(Matrix.posSemidef_submatrix_equiv _).mpr hρ,?_⟩
  change (∑ x,ρ ((bitVecEquiv n).symm x) ((bitVecEquiv n).symm x))=1
  exact (Equiv.sum_comp (bitVecEquiv n).symm (fun x => ρ x x)).trans htr

/-- The finite Born distribution of local randomized Pauli readouts of the density matrix `ρ`. -/
noncomputable def readoutLaw (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    FinDist (Fin n → Fin 3×Bool) := tensorPauliLaw n (finDensity n ρ) (finDensity_physical n ρ hρ htr)

/-- The Pauli word with axis `a` at sites `i` and `j` and identity at all other sites. -/
def pairWord {n : ℕ} (i j : Fin n) (a : Fin 3) : Fin n → Option (Fin 3) :=
  fun h => if h=i ∨ h=j then some a else none

/-- The tensor matrix of `pairWord i j a` is the relabelled register operator `pairPauli i j a`. -/
theorem pairWord_matrix {n : ℕ} (i j : Fin n) (a : Fin 3) :
    tensorPauliWord n (pairWord i j a)=relabelGate (bitVecEquiv n) (pairPauli i j a) := by
  apply congrArg (relabelGate (bitVecEquiv n))
  ext x y
  change (∏ h,tensorPauliWordFactor (pairWord i j a h)
    (boolEquivFin2 (x h)) (boolEquivFin2 (y h))) =
    ∏ h,(if h=i ∨ h=j then pauliMatrix a else (1 : Operator 2))
      (boolEquivFin2 (x h)) (boolEquivFin2 (y h))
  apply Finset.prod_congr rfl
  intro h _
  dsimp only [pairWord]
  split <;> rfl

/-- Simultaneously relabelling two square matrices by an equivalence preserves the trace of
their product. -/
theorem relabel_trace_product {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I≃J) (A B : Matrix I I ℂ) :
    ((relabelGate e A)*(relabelGate e B)).trace=(A*B).trace := by
  change (A.submatrix e.symm e.symm*B.submatrix e.symm e.symm).trace= _
  rw [Matrix.submatrix_mul_equiv]
  exact Equiv.sum_comp e.symm (fun x => (A*B) x x)

/-- The mean tensor Pauli score for `pairWord i j a` under `readoutLaw` equals the correlation
`corr ρ i j a`. -/
theorem pair_readout_mean {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (a : Fin 3) :
    (readoutLaw n ρ hρ htr).expect (tensorPauliValue (pairWord i j a))=corr ρ i j a := by
  rw [readoutLaw,tensorPauliValue_mean,pairWord_matrix,finDensity,relabel_trace_product]
  rfl

/-- The rational local Pauli score: one for an identity factor, the signed value three for a
matching measured axis, and zero otherwise. -/
def localValueQ : Option (Fin 3) → (Fin 3×Bool) → ℚ
  | none,_ => 1
  | some a,o => if o.1=a then 3*(if o.2 then 1 else -1) else 0

/-- The rational score of a Pauli word, obtained by multiplying its local scores over all sites. -/
def wordValueQ {n : ℕ} (w : Fin n → Option (Fin 3)) (o : Fin n → Fin 3×Bool) : ℚ :=
  ∏ i,localValueQ (w i) (o i)

/-- Casting the rational word score to the reals gives `tensorPauliValue`. -/
theorem wordValueQ_real {n : ℕ} (w : Fin n → Option (Fin 3)) (o : Fin n → Fin 3×Bool) :
    (wordValueQ w o:ℝ)=tensorPauliValue w o := by
  simp only [wordValueQ,Rat.cast_prod,tensorPauliValue]
  apply Finset.prod_congr rfl
  intro i _
  cases h : w i with
  | none => norm_num [h,localValueQ,tensorPauliLocalValue]
  | some a =>
    by_cases ha : (o i).1=a
    · cases hb : (o i).2 <;> norm_num [h,localValueQ,tensorPauliLocalValue,ha,hb]
    · norm_num [h,localValueQ,tensorPauliLocalValue,ha]

/-- The rational quantum Max Cut energy score formed from weighted pair-word scores with
prefactor −1/4. -/
def energyScoreQ {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n) (w : E → ℚ)
    (o : Fin n → Fin 3×Bool) : ℚ :=
  -(1/4:ℚ)*∑ e,w e*(1-∑ a : Fin 3,wordValueQ (pairWord (ends e).1 (ends e).2 a) o)

/-- Casting `energyScoreQ` to the reals gives the weighted expression in tensor Pauli scores
with prefactor −1/4. -/
theorem energyScoreQ_real {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n) (w : E → ℚ)
    (o : Fin n → Fin 3×Bool) : (energyScoreQ ends w o:ℝ)=
      -(1/4:ℝ)*∑ e,(w e:ℝ)*(1-∑ a : Fin 3,tensorPauliValue (pairWord (ends e).1 (ends e).2 a) o) := by
  simp only [energyScoreQ,Rat.cast_mul,Rat.cast_sum,Rat.cast_sub,Rat.cast_one,Rat.cast_neg,Rat.cast_div]
  norm_num only
  simp_rw [wordValueQ_real]

/-- Finite expectation commutes with multiplication by a real constant. -/
theorem expect_scale {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω) (c : ℝ) (f : Ω → ℝ) :
    q.expect (fun ω => c*f ω)=c*q.expect f := by
  simp only [FinDist.expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Finite expectation commutes with a finite sum of real-valued functions. -/
theorem expect_sum {Ω E : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype E] (q : FinDist Ω) (f : E → Ω → ℝ) :
    q.expect (fun ω => ∑ e,f e ω)=∑ e,q.expect (f e) := by
  simp only [FinDist.expect,Finset.mul_sum]
  exact Finset.sum_comm

/-- The expectation of a difference is the difference of the expectations. -/
theorem expect_sub {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (q : FinDist Ω) (f g : Ω → ℝ) :
    q.expect (fun ω => f ω-g ω)=q.expect f-q.expect g := by
  simp only [FinDist.expect,mul_sub,Finset.sum_sub_distrib]

/-- The expected rational Pauli energy score equals the quantum Max Cut energy of `ρ`, with
rational edge weights cast to the reals. This supplies the energy readout used in
[CrostaSaubanereHuber2026]. -/
theorem energyScoreQ_unbiased {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℚ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (readoutLaw n ρ hρ htr).expect (fun o => (energyScoreQ ends w o:ℝ))=
      energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ := by
  simp_rw [energyScoreQ_real]
  rw [expect_scale,expect_sum]
  simp_rw [expect_scale,expect_sub,FinDist.expect_const,expect_sum,pair_readout_mean]
  rw [qmc_energy_sum]
  simp_rw [energy_smul,energy_edge ρ htr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fin.sum_univ_three]
  ring
end Qatlib.Papers.RydbergMaxCut26.MainResults.PauliReadout
