/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 12 (noisy QSP ensemble average)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Appendix B,
Theorem 12 (Eqs. (B2)–(B15)).

Main result `theorem12_ensemble_mean` is the *signal-matrix* form of Eq. (B13):
for independent phase errors `e_j` with even laws,
the ensemble average of the noisy QSP signal product `∏_j e^{-i(φ_j+e_j)Z}·R`
equals `(∏_j E cos e_j) • ∏_j e^{-iφ_j Z}·R`.  The product `∏_j` is the ordered
matrix product `matProd`, since matrix multiplication is not commutative.

`theorem12_average_block` assembles the operator form (B3)/(B15): the top-left
block of the ensemble-averaged circuit is `(∏_j E cos e_j)·P(A)`.  The two
hypotheses are exactly the paper's two inputs: Lemma 11 (each sample circuit is a
block-encoding of the noisy reduction `Pe(ω)`) and the matrix lift of (B13) to the
qubitized operator `Pe(ω)(A)` (the qubitization identity of [4, Thm 17]); the
assembly itself (the linearity of block extraction under expectation, Eq. (B15))
is proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Theorem 12 (arXiv:2601.20073v1 p.10, Eq. (B13), signal-matrix form).**
Let `e_j` be independent phase errors with even laws.  Then the ensemble mean of
the noisy QSP signal product is `(∏_j E cos e_j)` times the ideal product. -/
theorem theorem12_ensemble_mean {d : ℕ} (μs : Fin d → FinDist Ω)
    (φ : Fin d → ℝ) (e : Fin d → Ω → ℝ) (hEven : ∀ j, IsEvenNoise (μs j) (e j))
    (R : Matrix (Fin 2) (Fin 2) ℂ) :
    matExpect (prodLaw μs) (fun ω => matProd d (fun j => zRot (φ j + e j (ω j)) * R))
      = (∏ j, (μs j).expect (fun x => Real.cos (e j x))) •
          matProd d (fun j => zRot (φ j) * R) := by
  rw [matExpect_prod_indep d μs (fun j x => zRot (φ j + e j x) * R)]
  have hstep : ∀ j, matExpect (μs j) (fun x => zRot (φ j + e j x) * R)
      = ((μs j).expect (fun x => Real.cos (e j x))) • (zRot (φ j) * R) := by
    intro j
    rw [matExpect_mul_const, matExpect_zRot (hEven j), Matrix.smul_mul]
  simp only [hstep]
  exact matProd_smul d (fun j => (μs j).expect (fun x => Real.cos (e j x)))
    (fun j => zRot (φ j) * R)

/-- Top-left block extraction commutes with the ensemble expectation
(linearity used in Eq. (B15)). -/
theorem matExpect_block {S Rb : Type*} (μ : FinDist Ω) (r0 : Rb)
    (U : Ω → Matrix (S × Rb) (S × Rb) ℂ) :
    matExpect μ (fun ω => fun i j => U ω (i, r0) (j, r0))
      = fun i j => (matExpect μ U) (i, r0) (j, r0) := by
  ext i j
  rfl

/-- **Theorem 12 (arXiv:2601.20073v1 p.10, Eq. (B3)/(B15), operator form).**
Assume each noisy QSP sample `U ω` is a block-encoding of the noisy reduction
`Pe ω` (Lemma 11), and that the ensemble mean of the reductions equals
`(∏_j E cos e_j) • P` (the matrix lift of Eq. (B13) through qubitization).
Then the top-left block of the averaged circuit is `(∏_j E cos e_j) • P`. -/
theorem theorem12_average_block {S Rb : Type*} [Fintype S] [Fintype Rb]
    [DecidableEq S] [DecidableEq Rb] {d : ℕ} (μs : Fin d → FinDist Ω)
    (r0 : Rb) (U : (Fin d → Ω) → Matrix (S × Rb) (S × Rb) ℂ)
    (Pe : (Fin d → Ω) → Matrix S S ℂ) (P : Matrix S S ℂ)
    (e : Fin d → Ω → ℝ)
    (hblock : ∀ ω i j, U ω (i, r0) (j, r0) = Pe ω i j)
    (hmean : matExpect (prodLaw μs) Pe
      = (∏ j, (μs j).expect (fun x => Real.cos (e j x))) • P) :
    matExpect (prodLaw μs) (fun ω => fun i j => U ω (i, r0) (j, r0))
      = (∏ j, (μs j).expect (fun x => Real.cos (e j x))) • P := by
  rw [matExpect_block]
  funext i j
  have h1 : (matExpect (prodLaw μs) U) (i, r0) (j, r0)
      = matExpect (prodLaw μs) Pe i j := by
    simp only [matExpect, cexpect, hblock]
  rw [h1, hmean]

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
