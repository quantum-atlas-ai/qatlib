/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# PersistentHom22.MainResults.PhaseReadout

Paper-layer Lean for **PersistentHom22** = *Quantum Persistent Homology*
(Ameneyro-Maroulas-Siopsis, arXiv:2202.12965).


Source anchors (arXiv PDF pages):

* Eq. (21), p.8: the measurement distribution over the readout register
  `P(p) = (1/N) sum_lambda g_lambda(p)`, with
  `g_lambda(p) = (1/M^2) sin^2(pi l lambda) / sin^2(pi (l lambda - p)/M)`.
  This is the modulus-squared of the amplitude of Eq. (C12), pp.16-17.
* Eq. (C13), p.17: at the peak `p = l`,
  `P(l) = beta_k^{eps,eps'}/N + (1/(M^2 N)) sum_{lambda != 1}
     sin^2(pi l lambda) / sin^2(pi l (lambda-1)/M)`.
* Eq. (C14), p.17: `beta_k^{eps,eps'} = N P(l)`.

This file uses an arbitrary finite list `eig : ι -> R`; `hβ` identifies `beta`
with the cardinality of its `lambda = 1` fibre.  Instantiating that list from a
Dirac operator or identifying this cardinality with a Betti number is separate work.

`readoutKernel` is the displayed quotient interpreted using Lean's total division,
including value `0` when its denominator is zero.  No analytic continuation at a
resonance, normalization theorem or readout circuit is supplied.  `peakKernel` is a
separate function that assigns `1` at `lambda = 1`; no equality identifies its sum
with `readoutProbability`.  The results below prove finite-sum algebra and a restricted
limit under exact off-peak numerator vanishing, rather than the general source C14 claim.
-/

set_option autoImplicit false
noncomputable section

open Classical
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace Qatlib.Papers.PersistentHom22.MainResults

/-- The raw quotient displayed in Eq. (21), p.8, with total division.
It has value `0` at a zero denominator; no resonant continuation is applied. -/
def readoutKernel (M l : ℕ) (lam : ℝ) (p : ℕ) : ℝ :=
  (1 / (M : ℝ) ^ 2) * (Real.sin (Real.pi * (l : ℝ) * lam)) ^ 2 /
    (Real.sin (Real.pi * ((l : ℝ) * lam - (p : ℝ)) / (M : ℝ))) ^ 2

/-- The finite average of raw quotients suggested by Eq. (21), p.8.
Its name does not assert normalization or an identification with a measurement law. -/
def readoutProbability {ι : Type*} [Fintype ι] (eig : ι → ℝ) (M l p : ℕ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ i, readoutKernel M l (eig i) p

/-- The off-peak (`lambda != 1`) summand of Eq. (C13), p.17, at `p = l`:
`(1/M^2) sin^2(pi l lambda) / sin^2(pi l (lambda - 1)/M)`. -/
def offPeakKernel (M l : ℕ) (lam : ℝ) : ℝ :=
  (1 / (M : ℝ) ^ 2) * (Real.sin (Real.pi * (l : ℝ) * lam)) ^ 2 /
    (Real.sin (Real.pi * (l : ℝ) * (lam - 1) / (M : ℝ))) ^ 2

/-- A separately patched function suggested by Eq. (C13), p.17: it assigns `1`
at `lambda = 1` and uses the raw off-peak quotient elsewhere.  No analytic-continuation
or equality-to-readout theorem is encoded by this definition. -/
def peakKernel (M l : ℕ) (lam : ℝ) : ℝ :=
  if lam = 1 then 1 else offPeakKernel M l lam

/-- The raw quotient is nonnegative because its numerator and denominator are squares. -/
lemma readoutKernel_nonneg (M l : ℕ) (lam : ℝ) (p : ℕ) : 0 ≤ readoutKernel M l lam p := by
  unfold readoutKernel
  have h1 : (0 : ℝ) ≤ 1 / (M : ℝ) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
  have h2 : (0 : ℝ) ≤ (Real.sin (Real.pi * (l : ℝ) * lam)) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ (Real.sin (Real.pi * ((l : ℝ) * lam - (p : ℝ)) / (M : ℝ))) ^ 2 :=
    sq_nonneg _
  exact div_nonneg (mul_nonneg h1 h2) h3

/-- A finite average of the nonnegative raw quotients is nonnegative. -/
lemma readoutProbability_nonneg {ι : Type*} [Fintype ι] (eig : ι → ℝ) (M l p : ℕ) :
    0 ≤ readoutProbability eig M l p := by
  unfold readoutProbability
  have h1 : (0 : ℝ) ≤ 1 / (Fintype.card ι : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have h2 : (0 : ℝ) ≤ ∑ i, readoutKernel M l (eig i) p :=
    Finset.sum_nonneg (fun i _ => readoutKernel_nonneg M l (eig i) p)
  exact mul_nonneg h1 h2

/-- At `p = l`, the readout kernel equals the off-peak summand (Eq. (C13), p.17). -/
lemma readoutKernel_at_peak (M l : ℕ) (lam : ℝ) :
    readoutKernel M l lam l = offPeakKernel M l lam := by
  unfold readoutKernel offPeakKernel
  rw [show (l : ℝ) * lam - (l : ℝ) = (l : ℝ) * (lam - 1) by ring]
  simp only [mul_assoc]

/-- **Eq. (C13) additive core** (p.17).  Splitting the eigenvalue sum at the
`lambda = 1` fibre: if that fibre has `beta` elements, the total peak sum equals
`beta` plus the off-peak sum.  This is the combinatorial content of
`P(l) = beta/N + (1/(M^2 N)) sum_{lambda != 1} ...`. -/
theorem peakSum_eq {ι : Type*} [Fintype ι] (eig : ι → ℝ) (M l β : ℕ)
    (hβ : Fintype.card {i // eig i = 1} = β) :
    (∑ i, peakKernel M l (eig i)) =
      (β : ℝ) + ∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1), offPeakKernel M l (eig i) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => eig i = 1)]
  have h1 : (∑ i ∈ Finset.univ.filter (fun i => eig i = 1), peakKernel M l (eig i)) = (β : ℝ) := by
    have hterm : ∀ i ∈ Finset.univ.filter (fun i => eig i = 1), peakKernel M l (eig i) = (1 : ℝ) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      simp [peakKernel, hi.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (Finset.univ.filter (fun i => eig i = 1)).card = β := by
      rw [← Fintype.card_subtype (fun i => eig i = 1)]
      exact hβ
    exact_mod_cast hc
  have h2 : (∑ i ∈ Finset.univ.filter (fun i => ¬ eig i = 1), peakKernel M l (eig i))
      = ∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1), offPeakKernel M l (eig i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    simp [peakKernel, hi.2]
  rw [h1, h2]

/-- Finite-sum algebra for the separately patched `peakKernel`, suggested by
Eq. (C13), p.17.  This statement does not identify the sum with `readoutProbability`. -/
theorem readout_at_peak_C13 {ι : Type*} [Fintype ι] (eig : ι → ℝ) (M l β : ℕ)
    (hβ : Fintype.card {i // eig i = 1} = β)
    (hN : (Fintype.card ι : ℝ) ≠ 0) (hM : (M : ℝ) ≠ 0) :
    (1 / (Fintype.card ι : ℝ)) * (∑ i, peakKernel M l (eig i)) =
      (β : ℝ) / (Fintype.card ι : ℝ) +
        (1 / ((Fintype.card ι : ℝ) * (M : ℝ) ^ 2)) *
          ∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1),
            (Real.sin (Real.pi * (l : ℝ) * (eig i))) ^ 2 /
              (Real.sin (Real.pi * (l : ℝ) * (eig i - 1) / (M : ℝ))) ^ 2 := by
  rw [peakSum_eq eig M l β hβ]
  have hS : (∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1), offPeakKernel M l (eig i))
      = (1 / (M : ℝ) ^ 2) *
          ∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1),
            (Real.sin (Real.pi * (l : ℝ) * (eig i))) ^ 2 /
              (Real.sin (Real.pi * (l : ℝ) * (eig i - 1) / (M : ℝ))) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [offPeakKernel, mul_div_assoc]
  rw [hS]
  field_simp

/-- Exact finite-sum identity under vanishing off-peak numerators, suggested by
Eq. (C14), p.17.  The normalized sum of the separately patched `peakKernel` recovers
the size of the `lambda = 1` fibre.  No circuit or measurement-law bridge is asserted. -/
theorem betti_readout_of_integer_spectrum {ι : Type*} [Fintype ι] (eig : ι → ℝ) (M l β : ℕ)
    (hβ : Fintype.card {i // eig i = 1} = β)
    (hint : ∀ i, eig i ≠ 1 → Real.sin (Real.pi * (l : ℝ) * (eig i)) = 0)
    (hN : (Fintype.card ι : ℝ) ≠ 0) :
    (Fintype.card ι : ℝ) * ((1 / (Fintype.card ι : ℝ)) * ∑ i, peakKernel M l (eig i))
      = (β : ℝ) := by
  rw [peakSum_eq eig M l β hβ]
  have hzero : (∑ i ∈ Finset.univ.filter (fun i => eig i ≠ 1), offPeakKernel M l (eig i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    simp [offPeakKernel, hint i hi.2]
  rw [hzero, add_zero]
  field_simp

/-- **Eq. (C14)** under exact off-peak numerator vanishing.  For fixed `l`,
increasing `M` alone does not remove general spectral tails: a single eigenvalue
`1/2` at `l = 1` contributes a term tending to `4 / pi^2`.  The integer-spectrum
condition makes every tail zero and gives the claimed limit uniformly in `M`. -/
theorem betti_readout_limit {ι : Type*} [Fintype ι] (eig : ι → ℝ) (l β : ℕ)
    (hβ : Fintype.card {i // eig i = 1} = β)
    (hint : ∀ i, eig i ≠ 1 → Real.sin (Real.pi * (l : ℝ) * (eig i)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      |(Fintype.card ι : ℝ) *
          ((1 / (Fintype.card ι : ℝ)) * ∑ i, peakKernel M l (eig i)) - (β : ℝ)| < ε := by
  intro ε hε
  refine ⟨0, fun M _ => ?_⟩
  by_cases hN : (Fintype.card ι : ℝ) ≠ 0
  · rw [betti_readout_of_integer_spectrum eig M l β hβ hint hN]
    simpa using hε
  · have hc : Fintype.card ι = 0 := by exact_mod_cast not_ne_iff.mp hN
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    have hb : β = 0 := by simpa using hβ.symm
    simp [hb, hε]

end Qatlib.Papers.PersistentHom22.MainResults
