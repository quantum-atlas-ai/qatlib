/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonlinearDE20.PolynomialStep.Polynomial
public import Mathlib.Tactic

@[expose] public section

/-!
# Symmetrized two-environment monomial interaction

The printed supplement of [LloydEtAl2020] writes the interaction of the monomial `x 1 * x 1 * x 2`
with a duplicated second index in its second term. This module records the corrected
symmetrization, in which both terms carry the conjugated monomial on the first environment copy
and the second term reverses the ket order, and proves that its contraction with two bra and two
ket amplitudes is exactly `conj (x 1)^2 * x 2` at `i = 2`, `j = 1` and zero elsewhere.

The first environment index `p` enumerates bra-side amplitudes and the second environment index
`q` enumerates ket-side amplitudes.

## Main statements

* `symmetrized_monomial_contraction`: the symmetrized two-environment interaction contracts to
  `conj (x 1)^2 * x 2` for target indices `i = 2`, `j = 1`, and to zero otherwise.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Monomial

/-- The symmetrized two-environment interaction for the monomial `x 1 * x 1 * x 2` with target
indices `i` and `j`. The second term reverses the ket order, which is the correction of the
duplicated index in the printed source [LloydEtAl2020]. -/
def symmetrizedTwoEnv (i j : Fin 3) (p q : Fin 2 → Fin 3) : ℂ :=
  (1/2) * ((if i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![2,0] then 1 else 0) +
    (if i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![0,2] then 1 else 0))

/-- A finite sum vanishes off two points and equals the sum of the two remaining values. -/
private lemma sum_two_points {α : Type} [Fintype α] [DecidableEq α] (a b : α) {g : α → ℂ}
    (hab : a ≠ b) (hzero : ∀ y : α, y ≠ a → y ≠ b → g y = 0) :
    (∑ y : α, g y) = g a + g b := by
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset α))]
  · rw [Finset.sum_pair hab]
  · intro y _ hy
    exact hzero y (fun h => hy (by simp [h])) (fun h => hy (by simp [h]))

/-- The symmetrized interaction contracts the two bra and two ket amplitudes to
`conj (x 1)^2 * x 2` at the target indices `i = 2`, `j = 1`, and to zero otherwise; this is the
corrected form of the printed two-environment interaction [LloydEtAl2020]. -/
theorem symmetrized_monomial_contraction (x : Fin 3 → ℂ) (h0 : x 0 = 1) (i j : Fin 3) :
    (∑ p : Fin 2 → Fin 3, ∑ q : Fin 2 → Fin 3,
      (∏ k : Fin 2, star (x (p k))) * symmetrizedTwoEnv i j p q * (∏ k : Fin 2, x (q k))) =
      (if i = 2 ∧ j = 1 then star (x 1) ^ 2 * x 2 else 0) := by
  split_ifs with hcon
  · obtain ⟨rfl, rfl⟩ := hcon
    have houter : ∀ p : Fin 2 → Fin 3, p ≠ ![1,1] →
        (∑ q : Fin 2 → Fin 3,
          (∏ k : Fin 2, star (x (p k))) * symmetrizedTwoEnv 2 1 p q *
            (∏ k : Fin 2, x (q k))) = 0 := by
      intro p hp
      apply Finset.sum_eq_zero
      intro q _
      have h1 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ p = ![1,1] ∧ q = ![2,0]) :=
        fun h => hp h.2.2.1
      have h2 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ p = ![1,1] ∧ q = ![0,2]) :=
        fun h => hp h.2.2.1
      have hs : symmetrizedTwoEnv 2 1 p q = 0 := by
        unfold symmetrizedTwoEnv
        by_cases hc1 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ p = ![1,1] ∧ q = ![2,0])
        · exact absurd hc1 h1
        · by_cases hc2 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ p = ![1,1] ∧ q = ![0,2])
          · exact absurd hc2 h2
          · simp_all
      rw [hs]
      ring
    rw [Finset.sum_eq_single ![1,1] (fun p _ hp => houter p hp)
      (fun h => absurd (Finset.mem_univ _) h)]
    have htwo := sum_two_points (![2,0] : Fin 2 → Fin 3) ![0,2] (by decide)
      (g := fun q => (∏ k : Fin 2, star (x (![1,1] k))) * symmetrizedTwoEnv 2 1 ![1,1] q *
        (∏ k : Fin 2, x (q k)))
      (by
        intro q hq1 hq2
        have h1 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
            q = ![2,0]) := fun h => hq1 h.2.2.2
        have h2 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
            q = ![0,2]) := fun h => hq2 h.2.2.2
        have hs : symmetrizedTwoEnv 2 1 ![1,1] q = 0 := by
          unfold symmetrizedTwoEnv
          by_cases hc1 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧
              (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧ q = ![2,0])
          · exact absurd hc1 h1
          · by_cases hc2 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧
                (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧ q = ![0,2])
            · exact absurd hc2 h2
            · simp_all
        rw [hs]
        ring)
    have hA : (∏ k : Fin 2, star (x (![1,1] k))) = star (x 1) * star (x 1) := by
      simp [Fin.prod_univ_two]
    have hB : (∏ k : Fin 2, x (![2,0] k)) = x 2 * x 0 := by
      simp [Fin.prod_univ_two]
    have hC : (∏ k : Fin 2, x (![0,2] k)) = x 0 * x 2 := by
      simp [Fin.prod_univ_two]
    have hq1 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
        (![2,0] : Fin 2 → Fin 3) = ![2,0]) := by decide
    have hq2 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
        (![2,0] : Fin 2 → Fin 3) = ![0,2]) := by decide
    have hq3 : ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
        (![0,2] : Fin 2 → Fin 3) = ![0,2]) := by decide
    have hq4 : ¬ ((2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 ∧ (![1,1] : Fin 2 → Fin 3) = ![1,1] ∧
        (![0,2] : Fin 2 → Fin 3) = ![2,0]) := by decide
    have e1 : symmetrizedTwoEnv 2 1 ![1,1] ![2,0] = 1/2 := by
      unfold symmetrizedTwoEnv
      simp_all
    have e2 : symmetrizedTwoEnv 2 1 ![1,1] ![0,2] = 1/2 := by
      unfold symmetrizedTwoEnv
      simp_all
    rw [htwo, hA, hB, hC, e1, e2, h0]
    ring
  · have hzero : ∀ (p q : Fin 2 → Fin 3),
        (∏ k : Fin 2, star (x (p k))) * symmetrizedTwoEnv i j p q *
          (∏ k : Fin 2, x (q k)) = 0 := by
      intro p q
      have h1 : ¬ (i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![2,0]) := fun h => hcon ⟨h.1, h.2.1⟩
      have h2 : ¬ (i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![0,2]) := fun h => hcon ⟨h.1, h.2.1⟩
      have hs : symmetrizedTwoEnv i j p q = 0 := by
        unfold symmetrizedTwoEnv
        by_cases hc1 : (i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![2,0])
        · exact absurd hc1 h1
        · by_cases hc2 : (i = 2 ∧ j = 1 ∧ p = ![1,1] ∧ q = ![0,2])
          · exact absurd hc2 h2
          · simp [hc1, hc2]
      rw [hs]
      ring
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro q _
    exact hzero p q

end Qatlib.Papers.NonlinearDE20.AffineLift.Monomial
