/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

@[expose] public section


/-!
# Lemma 12 — estimating the kernel entries is as hard as DLP

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020), Lemma 12, p. 15–16.

If a polynomial-time algorithm computes the kernel entry
`K₀(y,y') = ⟨φ(y)|φ(y')⟩` on arbitrary inputs up to `0.01` additive error, then
`DLP(p,g)` is solvable in polynomial time.  The source proof decides a promise
problem: for `y = g^x` with `x` either in the first `(p-1)/16` log-values or in
the next `(p-1)/16`, the two cases give kernel value `0` and at least `1/16`
against the point `y' = g^((p+1)/2)`.

The interval geometry (kernel entry = normalised intersection size of the two
feature intervals) is proved here, together with the zero case.  The reduction
itself (Lemma 5 of the source, promise-DLP to DLP) lies outside the interval
identities proved in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset DlogWorld
open scoped BigOperators

namespace DlogWorld

variable {W : DlogWorld}

/-- The kernel entry `K₀(y,y') = ⟨φ(y)|φ(y')⟩` of the `k`-th feature map. -/
def kernelEntry (k : ℕ) (t t' : ZMod W.N) : ℝ :=
  W.euclidInner (W.phiVec k t) (W.phiVec k t')

/-- Sum of two indicator products. -/
theorem sum_indicator_sq {α : Type} [Fintype α] [DecidableEq α]
    (B A : Finset α) (c : ℝ) :
    (∑ u, (if u ∈ B then c else 0) * (if u ∈ A then c else 0)) =
      c ^ 2 * ((B ∩ A).card : ℝ) := by
  have h : ∀ u, (if u ∈ B then c else 0) * (if u ∈ A then c else 0) =
      (if u ∈ B ∩ A then c ^ 2 else 0) := by
    intro u
    by_cases hb : u ∈ B <;> by_cases ha : u ∈ A <;>
      simp [hb, ha, Finset.mem_inter, sq]
  calc (∑ u, (if u ∈ B then c else 0) * (if u ∈ A then c else 0))
      = ∑ u, (if u ∈ B ∩ A then c ^ 2 else 0) := Finset.sum_congr rfl (fun u _ => h u)
    _ = ∑ u ∈ B ∩ A, c ^ 2 := by
        rw [← Finset.sum_filter]
        congr 1
        ext u
        simp
    _ = c ^ 2 * ((B ∩ A).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The squared coefficient `((√L)⁻¹)² = 1/L` of the feature state. -/
theorem phi_coeff_sq (L : ℕ) (hL : 0 < L) :
    ((Real.sqrt ((L : ℕ) : ℝ))⁻¹) ^ 2 = (((L : ℕ) : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- **Kernel entry = normalised interval overlap.**  This is the geometric
identity underlying Lemma 12: `K₀(y,y')` is the fraction of the `2^k` log-values
on which the two feature states overlap. -/
theorem kernelEntry_eq_card_div (k : ℕ) (t t' : ZMod W.N) :
    W.kernelEntry k t t' =
      (((cyclicInterval W.N t (2 ^ k) ∩ cyclicInterval W.N t' (2 ^ k)).card : ℝ)) /
        (((2 ^ k : ℕ)) : ℝ) := by
  unfold kernelEntry euclidInner phiVec
  rw [sum_indicator_sq]
  have h2k : (0 : ℝ) < (((2 ^ k : ℕ)) : ℝ) := by positivity
  rw [phi_coeff_sq _ (by positivity), div_eq_inv_mul]

/-- **Lemma 12, case 1 (source p. 16).**  Disjoint feature intervals give kernel
entry `0`, and hence an estimator of additive accuracy less than `1/16` reports
`0`. -/
theorem kernelEntry_eq_zero_of_disjoint {k : ℕ} {t t' : ZMod W.N}
    (h : cyclicInterval W.N t (2 ^ k) ∩ cyclicInterval W.N t' (2 ^ k) = ∅) :
    W.kernelEntry k t t' = 0 := by
  rw [kernelEntry_eq_card_div, h]
  simp

/-- **Lemma 12, case 2 (source p. 16).**  An intersection of `c` log-values gives
kernel entry `c / 2^k`, so an estimator of additive accuracy less than
`c/2^k` reports a positive value; the source uses `c ≥ p/16` and `2^k = p/8`. -/
theorem kernelEntry_eq_of_inter_card {k c : ℕ} {t t' : ZMod W.N}
    (h : (cyclicInterval W.N t (2 ^ k) ∩ cyclicInterval W.N t' (2 ^ k)).card = c) :
    W.kernelEntry k t t' = ((c : ℝ)) / (((2 ^ k : ℕ)) : ℝ) := by
  rw [kernelEntry_eq_card_div, h]

/-- A polynomial-time algorithm that estimates `K₀(y,y')` on log-index inputs
`(y,y')` up to `0.01` additive error, where the indices are encoded by the
canonical codes of the corresponding group elements. -/
def KernelEstimator (W : DlogWorld) (k : ℕ) : Prop :=
  ∃ g : ℕ → ℕ,
    PolyComputes g ∧
      ∀ y y' : ZMod W.N,
        |(g (Nat.pair (W.codeOf (W.logEquiv.symm y)) (W.codeOf (W.logEquiv.symm y'))) : ℝ) -
            W.kernelEntry k y y'| ≤ 1 / 100

end DlogWorld

end Qatlib.Papers.SupervSpeedup20.MainResults
