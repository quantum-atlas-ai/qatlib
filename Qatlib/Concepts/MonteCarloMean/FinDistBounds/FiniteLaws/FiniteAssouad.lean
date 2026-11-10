/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FinitePinsker

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteAssouad
open FiniteInformationDivergence
open scoped BigOperators Classical
noncomputable section

abbrev Cube (m : ℕ) := Fin m → Bool

def flipAt {m : ℕ} (i : Fin m) (theta : Cube m) : Cube m :=
  Function.update theta i (!theta i)

@[simp] theorem flipAt_self {m : ℕ} (i : Fin m) (theta : Cube m) :
    flipAt i theta i = !theta i := by simp [flipAt]

@[simp] theorem flipAt_twice {m : ℕ} (i : Fin m) (theta : Cube m) :
    flipAt i (flipAt i theta) = theta := by
  funext j
  by_cases h : j=i
  · subst j; simp [flipAt]
  · simp [flipAt, h]

def flipEquiv {m : ℕ} (i : Fin m) : Cube m ≃ Cube m where
  toFun := flipAt i
  invFun := flipAt i
  left_inv := flipAt_twice i
  right_inv := flipAt_twice i

variable {X : Type} [Fintype X] [DecidableEq X]

def coordinateRisk {m n : ℕ} (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (decode : (Fin n → X) → Cube m) (theta : Cube m) (i : Fin m) : ℝ :=
  (P theta).probEvent (fun w => decode w i ≠ theta i)

theorem paired_error {m n : ℕ} (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (decode : (Fin n → X) → Cube m) (theta : Cube m) (i : Fin m) :
    coordinateRisk P decode theta i + coordinateRisk P decode (flipAt i theta) i =
      errorSum (records (P theta) n) (records (P (flipAt i theta)) n)
        (fun w => decide (decode w i ≠ theta i)) := by
  unfold coordinateRisk Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent errorSum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  cases ht : theta i <;> cases hd : decode w i <;>
    simp [flipAt_self, ht, hd, records,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]

theorem coordinate_pair_lower {m n : ℕ} (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (hpos : ∀ theta x, 0 < (P theta).prob x) (kappa : ℝ)
    (hkl : ∀ theta (i : Fin m), kl (P theta) (P (flipAt i theta)) ≤ kappa)
    (decode : (Fin n → X) → Cube m) (theta : Cube m) (i : Fin m) :
    1-Real.sqrt ((n : ℝ)*kappa/2) ≤
      coordinateRisk P decode theta i + coordinateRisk P decode (flipAt i theta) i := by
  rw [paired_error]
  have h := FinitePinsker.records_testing (P theta) (P (flipAt i theta))
    (hpos theta) (hpos _) n (fun w => decide (decode w i ≠ theta i))
  have hs : Real.sqrt ((n : ℝ)*kl (P theta) (P (flipAt i theta))/2) ≤
      Real.sqrt ((n : ℝ)*kappa/2) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hkl theta i) (Nat.cast_nonneg _)) (by norm_num)
  linarith

theorem average_hamming_lower {m n : ℕ} (P : Cube m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (hpos : ∀ theta x, 0 < (P theta).prob x) (kappa : ℝ)
    (hkl : ∀ theta (i : Fin m), kl (P theta) (P (flipAt i theta)) ≤ kappa)
    (decode : (Fin n → X) → Cube m) :
    (m : ℝ)/2*(1-Real.sqrt ((n : ℝ)*kappa/2)) ≤
      (∑ theta : Cube m, ∑ i, coordinateRisk P decode theta i) /
        (Fintype.card (Cube m) : ℝ) := by
  have hi (i : Fin m) :
      (Fintype.card (Cube m) : ℝ)*(1-Real.sqrt ((n : ℝ)*kappa/2)) ≤
        2*∑ theta : Cube m, coordinateRisk P decode theta i := by
    have hs := Finset.sum_le_sum (fun theta (_ : theta ∈ (Finset.univ : Finset (Cube m))) =>
      coordinate_pair_lower P hpos kappa hkl decode theta i)
    have he : (∑ theta : Cube m, coordinateRisk P decode (flipAt i theta) i) =
        ∑ theta : Cube m, coordinateRisk P decode theta i :=
      (flipEquiv i).sum_comp (fun theta => coordinateRisk P decode theta i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_add_distrib, he] at hs
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum] at hs
  rw [Finset.sum_comm] at hs
  have hc : 0 < (Fintype.card (Cube m) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Cube m))
  apply (le_div_iff₀ hc).mpr
  nlinarith

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteAssouad
