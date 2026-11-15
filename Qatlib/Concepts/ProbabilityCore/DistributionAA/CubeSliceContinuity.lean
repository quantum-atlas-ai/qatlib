/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceCoupling

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Bounds the expectation difference between adjacent slices for a bounded degree-`d` cube
function. -/
theorem cube_slice_adjacent_expectation_bound {n d k : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) (hk0 : 0 < k) (hk : k ≤ n) :
    |cubeExpect n (sliceWeight n k) f-cubeExpect n (sliceWeight n (k-1)) f| ≤
      4*(d : ℝ)^2/(n : ℝ) := by
  let Δ := cubeExpect n (sliceWeight n k) f-cubeExpect n (sliceWeight n (k-1)) f
  have hDown (x : Fin n → Bool) : |∑ i : Fin n, if x i then f x-f (cubeFlip x i) else 0| ≤ 2*(d : ℝ)^2 := by
    have h := cube_flip_sum_le_two hb hd x (Finset.univ.filter fun i => x i=true)
    simpa only [Finset.sum_filter] using h
  have hUp (x : Fin n → Bool) : |∑ i : Fin n, if x i=false then f (cubeFlip x i)-f x else 0| ≤ 2*(d : ℝ)^2 := by
    have h := cube_flip_sum_le_two hb hd x (Finset.univ.filter fun i => x i=false)
    have he : (∑ i : Fin n, if x i=false then f (cubeFlip x i)-f x else 0) =
        -(∑ i ∈ Finset.univ.filter (fun i => x i=false), (f x-f (cubeFlip x i))) := by
      rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [he,abs_neg]
    exact h
  have hl := cube_expect_abs_le (sliceWeight_cubeWeight n k hk) _ _ hDown
  rw [cube_slice_difference_down n k hk0 hk, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at hl
  have hu := cube_expect_abs_le (sliceWeight_cubeWeight n (k-1) (by omega)) _ _ hUp
  rw [cube_slice_difference_up n k hk0 hk, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n-k+1))] at hu
  change (k : ℝ)*|Δ| ≤ _ at hl
  change (n-k+1 : ℕ)*|Δ| ≤ _ at hu
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hk0 hk)
  have hsum : (k : ℝ)+(n-k+1 : ℕ) = (n : ℝ)+1 := by exact_mod_cast (show k+(n-k+1)=n+1 by omega)
  have hbound : (n : ℝ)*|Δ| ≤ 4*(d : ℝ)^2 := by
    have ha : 0 ≤ |Δ| := abs_nonneg _
    have he : ((k : ℝ)+(n-k+1 : ℕ))*|Δ| = ((n : ℝ)+1)*|Δ| := by rw [hsum]
    nlinarith only [hl,hu,ha,he]
  apply (le_div_iff₀ hnr).2
  nlinarith only [hbound]

/-- Gives a Lipschitz bound for slice expectations in terms of the distance between slice
indices. -/
theorem cube_slice_expectation_lipschitz {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (t u : ℕ) (ht : t ≤ n) (hu : u ≤ n) :
    |cubeExpect n (sliceWeight n t) f-cubeExpect n (sliceWeight n u) f| ≤
      (4*(d : ℝ)^2/(n : ℝ))*|(t : ℝ)-(u : ℝ)| := by
  let F := fun k => cubeExpect n (sliceWeight n k) f
  have hordered (t u : ℕ) (ht : t ≤ n) (hu : u ≤ t) :
      |F t-F u| ≤ (4*(d : ℝ)^2/(n : ℝ))*|(t : ℝ)-(u : ℝ)| := by
    have hs := Finset.sum_range_sub (fun j => F (u+j)) (t-u)
    have htu : u+(t-u)=t := by omega
    simp only [Nat.add_zero,htu] at hs
    rw [← hs]
    calc
      _ ≤ ∑ j ∈ Finset.range (t-u), |F (u+(j+1))-F (u+j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range (t-u), 4*(d : ℝ)^2/(n : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.1 hj
        have hkj : u+(j+1) ≤ n := by omega
        have he := cube_slice_adjacent_expectation_bound hb hd (show 0 < u+(j+1) by omega) hkj
        have hk : u+(j+1)-1 = u+j := by omega
        simpa only [hk] using he
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        rw [Nat.cast_sub hu,
            abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hu) : 0 ≤ (t : ℝ)-(u : ℝ))]
        ring
  rcases le_total u t with h | h
  · exact hordered t u ht h
  · have he := hordered u t hu h
    simpa only [abs_sub_comm] using he

end Qatlib.Concepts.ProbabilityCore.DistributionAA
