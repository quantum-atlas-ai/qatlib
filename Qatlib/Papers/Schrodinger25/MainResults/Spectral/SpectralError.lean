/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — spectral discretisation + truncation error (Theorem 2.1)

Fixed paper version: arXiv:2505.00370.  Source statement: Theorem 2.1, p. 12–13,
eqs. (2.24)–(2.26).

The paper proves the total error estimate

  `‖w(T,p) − w_h(T,p)‖_{L²((−L,R))} ≲ ε ‖u_I‖`                     (2.25)

by adding the two error sources produced by the algorithm of Section 2:

* the **domain truncation** error `w − w_trunc`, controlled by the boundary
  trace/boundary mass estimates of Section 5 (Lemmas 5.1–5.5; see
  `MainResults.Truncation`), and
* the **spectral (Fourier collocation) discretisation** error
  `w_trunc − w_h`, controlled by the aliasing estimate (2.23)

  `‖ψ − P_h ψ‖_{L²((−L,R))} ≲ ((R+L)/N_p)^r ‖ψ^{(r)}‖_{L²((−L,R))} = (π/μ_max)^r ‖ψ^{(r)}‖_{L²((−L,R))}`,

  which is `≲ ε` precisely under the mesh condition (2.24)
  `(Δp)^{-1} ≃ μ_max ≃ π(1/ε)^{1/r} ‖ψ^{(r)}‖_{L²((−L,R))}^{1/r}`.

This module formalises the final (genuinely mathematical) step of that proof:
the combination of the two `ε`-level estimates into a single `ε`-level bound
for the total error, in the squared `L²` norm over `(−L,R)`.  The two
sub-estimates are hypotheses here because the Fourier-aliasing estimate and the
truncation energy estimate require analysis infrastructure that the paper-layer
model does not formalise (see the sorry-annotated theorems of
`MainResults.Truncation`); the combination step is proved in full.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset MeasureTheory

namespace Qatlib.Papers.Schrodinger25.MainResults.Spectral

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Squared `L²` norm over `(a,b)` of an `ι`-indexed complex-valued function of
`p`: `∫_a^b ‖f(p)‖² dp`.  This is the squared norm appearing in (2.25). -/
def L2Sq (a b : ℝ) (f : ℝ → ι → ℂ) : ℝ := ∫ p in a..b, vecNormSq (f p)

/-- Triangle inequality for the squared Euclidean norm:
`‖f + g‖² ≤ 2‖f‖² + 2‖g‖²`.  Used to add the two error sources. -/
theorem vecNormSq_add_le (f g : ι → ℂ) :
    vecNormSq (fun j => f j + g j) ≤ 2 * vecNormSq f + 2 * vecNormSq g := by
  unfold vecNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ‖f j + g j‖ ≤ ‖f j‖ + ‖g j‖ := norm_add_le _ _
  have h3 : ‖f j + g j‖ ^ 2 ≤ (‖f j‖ + ‖g j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2 : (‖f j‖ + ‖g j‖) ^ 2 ≤ 2 * ‖f j‖ ^ 2 + 2 * ‖g j‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f j‖ - ‖g j‖), norm_nonneg (f j), norm_nonneg (g j)]
  linarith

/-- **Theorem 2.1** (p. 12–13, (2.24)–(2.26)), combination step.

Let `w` be the exact solution of (2.4), `wmid` the solution of the
domain-truncated problem and `wh` the continuous reconstruction (2.26) of the
Fourier-collocation solution `W_h`.  Suppose both error sources are at the
`ε`-level in squared `L²((−L,R))`-norm:

* `∫ ‖w − wmid‖² ≤ ε² ‖u_I‖²`  (truncation, Section 5), and
* `∫ ‖wmid − wh‖² ≤ ε² ‖u_I‖²`  (aliasing under the mesh condition (2.24)).

Then the total error obeys the paper's estimate (2.25) with an absolute
constant: `∫ ‖w − wh‖² ≤ 4 ε² ‖u_I‖²`, i.e. `‖w − w_h‖_{L²((−L,R))} ≤ 2ε‖u_I‖`.

The hypotheses `hmid1`/`hmid2` are exactly the estimates established in the
paper by (2.23) and by the boundary estimates of Lemma 5.2/5.3 for the
truncated problem; the arithmetic fact `(x+y)² ≤ 2x² + 2y²` and the
monotonicity of the integral are proved here. -/
theorem theorem_two_one_discrete_error
    (a b : ℝ) (hab : a ≤ b)
    (w wmid wh : ℝ → ι → ℂ) (uI : ι → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hAint : IntervalIntegrable (fun p => vecNormSq (fun j => w p j - wmid p j)) volume a b)
    (hBint : IntervalIntegrable (fun p => vecNormSq (fun j => wmid p j - wh p j)) volume a b)
    (hCint : IntervalIntegrable (fun p => vecNormSq (fun j => w p j - wh p j)) volume a b)
    (hmid1 : L2Sq a b (fun p j => w p j - wmid p j) ≤ ε ^ 2 * vecNormSq uI)
    (hmid2 : L2Sq a b (fun p j => wmid p j - wh p j) ≤ ε ^ 2 * vecNormSq uI) :
    L2Sq a b (fun p j => w p j - wh p j) ≤ 4 * ε ^ 2 * vecNormSq uI := by
  have hpt : ∀ p, vecNormSq (fun j => w p j - wh p j)
      ≤ 2 * vecNormSq (fun j => w p j - wmid p j)
        + 2 * vecNormSq (fun j => wmid p j - wh p j) := by
    intro p
    have heq : (fun j => w p j - wh p j)
        = (fun j => (w p j - wmid p j) + (wmid p j - wh p j)) := by
      funext j
      ring
    rw [heq]
    exact vecNormSq_add_le _ _
  have hsumInt : IntervalIntegrable
      (fun p => 2 * vecNormSq (fun j => w p j - wmid p j)
        + 2 * vecNormSq (fun j => wmid p j - wh p j)) volume a b :=
    (hAint.const_mul 2).add (hBint.const_mul 2)
  calc L2Sq a b (fun p j => w p j - wh p j)
      ≤ ∫ p in a..b, (2 * vecNormSq (fun j => w p j - wmid p j)
          + 2 * vecNormSq (fun j => wmid p j - wh p j)) := by
        unfold L2Sq
        exact intervalIntegral.integral_mono_on hab hCint hsumInt fun p _ => hpt p
    _ = 2 * L2Sq a b (fun p j => w p j - wmid p j)
          + 2 * L2Sq a b (fun p j => wmid p j - wh p j) := by
        unfold L2Sq
        rw [intervalIntegral.integral_add (hAint.const_mul 2) (hBint.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (ε ^ 2 * vecNormSq uI) + 2 * (ε ^ 2 * vecNormSq uI) := by
        linarith [hmid1, hmid2]
    _ = 4 * ε ^ 2 * vecNormSq uI := by ring

end Qatlib.Papers.Schrodinger25.MainResults.Spectral
