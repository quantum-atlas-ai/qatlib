/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCellAutomata96.MainResults.PathCounting
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact lattice propagator recurrences

This module defines the two-component lattice evolution and explicit binomial-sum amplitudes in
light-cone coordinates. It proves their recurrences, identifies them with evolution from
localized initial states, and derives reflection, translation, and path-sum formulas. See
[Meyer1996a].

## Main statements

* `caEvolve_amp`: If `u + v = t`, evolution from the localized component-one state at `lcCell u
  v` equals the explicit amplitude vector.
* `caEvolve_left_amp`: For `u + v = t`, evolution from the localized component-zero state has
  components `ampE θ v u` and `ampO θ v u`.
* `fullEvenAmp_eq_ampE`: Adding the straight-path boundary contribution to the even path sum
  gives `ampE` for all light-cone coordinates.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The nearest-neighbor update block with nonzero second column `(i * sin θ, cos θ)`. -/
def caBlockA (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, I * (Real.sin θ : ℂ); 0, (Real.cos θ : ℂ)]

/-- The nearest-neighbor update block with nonzero first column `(cos θ, i * sin θ)`. -/
def caBlockB (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), 0; I * (Real.sin θ : ℂ), 0]

/-- One lattice update, combining `caBlockA` on the left neighbor and `caBlockB` on the right
neighbor. -/
def caStep (θ : ℝ) (ψ : ℤ → Fin 2 → ℂ) : ℤ → Fin 2 → ℂ :=
  fun x => (caBlockA θ).mulVec (ψ (x - 1)) + (caBlockB θ).mulVec (ψ (x + 1))

/-- Iterate the lattice update for a natural number of time steps. -/
def caEvolve (θ : ℝ) : ℕ → (ℤ → Fin 2 → ℂ) → (ℤ → Fin 2 → ℂ)
  | 0, ψ => ψ
  | n + 1, ψ => caStep θ (caEvolve θ n ψ)

/-- The state localized at the origin in component one. -/
def caPsi0 : ℤ → Fin 2 → ℂ := fun x i => if x = 0 ∧ i = 1 then 1 else 0

/-- The integer lattice position `u - v` associated with natural light-cone coordinates. -/
def lcCell (u v : ℕ) : ℤ := (u : ℤ) - (v : ℤ)

/-- The light-cone update from the two predecessor coordinates, omitting terms across a zero
boundary. -/
def lcStep (θ : ℝ) (F : ℕ → ℕ → Fin 2 → ℂ) : ℕ → ℕ → Fin 2 → ℂ :=
  fun u v =>
    (if u = 0 then 0 else (caBlockA θ).mulVec (F (u - 1) v)) +
      (if v = 0 then 0 else (caBlockB θ).mulVec (F u (v - 1)))

/-- Iterate the light-cone update for a natural number of steps. -/
def lcEvolve (θ : ℝ) : ℕ → (ℕ → ℕ → Fin 2 → ℂ) → (ℕ → ℕ → Fin 2 → ℂ)
  | 0, F => F
  | n + 1, F => lcStep θ (lcEvolve θ n F)

/-- The pullback of `caPsi0` along the position map `lcCell`. -/
def lcPsi0 : ℕ → ℕ → Fin 2 → ℂ := fun u v i => caPsi0 (lcCell u v) i

/-- The action of `caBlockA` uses only component one and yields `(i * sin θ * z 1, cos θ * z
1)`. -/
theorem caBlockA_mulVec (θ : ℝ) (z : Fin 2 → ℂ) :
    (caBlockA θ).mulVec z =
      ![I * (Real.sin θ : ℂ) * z 1, (Real.cos θ : ℂ) * z 1] := by
  ext i
  fin_cases i <;>
    simp [caBlockA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The action of `caBlockB` uses only component zero and yields `(cos θ * z 0, i * sin θ * z
0)`. -/
theorem caBlockB_mulVec (θ : ℝ) (z : Fin 2 → ℂ) :
    (caBlockB θ).mulVec z =
      ![(Real.cos θ : ℂ) * z 0, I * (Real.sin θ : ℂ) * z 0] := by
  ext i
  fin_cases i <;>
    simp [caBlockB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The finite binomial sum for the odd component, set to zero when `u = 0`. -/
def ampO (θ : ℝ) (u v : ℕ) : ℂ :=
  if u = 0 then 0 else
    ∑ j ∈ Finset.range (min (u - 1) v + 1),
      (Nat.choose (u - 1) j : ℂ) * (Nat.choose v j : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) *
          (Real.cos θ : ℂ) ^ (u + v - (2 * j + 1))

/-- The finite binomial sum for the even component, with the straight-path value on the boundary
`v = 0`. -/
def ampE (θ : ℝ) (u v : ℕ) : ℂ :=
  if v = 0 then (Real.cos θ : ℂ) ^ (u + v) else
    ∑ k ∈ Finset.range (min u v),
      (Nat.choose u (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) *
          (Real.cos θ : ℂ) ^ (u + v - 2 * (k + 1))

/-- The two-component vector formed from `ampO` and `ampE`. -/
def ampVec (θ : ℝ) (u v : ℕ) : Fin 2 → ℂ := ![ampO θ u v, ampE θ u v]

/-- A finite sum with vanishing zeroth term equals the sum over the shifted range. -/
lemma sum_range_shift (f : ℕ → ℂ) (m : ℕ) (h0 : f 0 = 0) :
    (∑ j ∈ Finset.range (m + 1), f j) = ∑ k ∈ Finset.range m, f (k + 1) := by
  rw [Finset.sum_range_succ']
  simp [h0]

/-- On the boundary `v = 0`, the even amplitude is `cos θ` raised to `u`. -/
theorem ampE_zero_right (θ : ℝ) (u : ℕ) : ampE θ u 0 = (Real.cos θ : ℂ) ^ u := by
  simp [ampE]

/-- On the boundary `u = 0` with `v ≥ 1`, the even amplitude vanishes. -/
theorem ampE_zero_left (θ : ℝ) (v : ℕ) (hv : 1 ≤ v) : ampE θ 0 v = 0 := by
  unfold ampE
  rw [if_neg (by omega), Nat.zero_min, Finset.range_zero, Finset.sum_empty]

/-- For `u ≥ 1` and `v = 0`, the odd amplitude is `i * sin θ * cos θ^(u - 1)`. -/
theorem ampO_zero_right (θ : ℝ) (u : ℕ) (hu : 1 ≤ u) :
    ampO θ u 0 = I * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ (u - 1) := by
  unfold ampO
  rw [if_neg (by omega), Nat.min_zero, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj0
    have hj : j ≠ 0 := hj0
    simp [Nat.choose_eq_zero_of_lt (show 0 < j by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The odd amplitude vanishes whenever `u = 0`. -/
theorem ampO_zero_left (θ : ℝ) (v : ℕ) : ampO θ 0 v = 0 := by
  simp [ampO]

/-- The odd amplitude vanishes at the light-cone origin. -/
theorem ampO_zero_zero (θ : ℝ) : ampO θ 0 0 = 0 := by
  simp [ampO]

/-- At positive light-cone coordinates, the odd amplitude satisfies the recurrence combining the
preceding odd amplitude with the other preceding even amplitude. See [Meyer1996a]. -/
theorem ampO_rec (θ : ℝ) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ampO θ u v =
      (Real.cos θ : ℂ) * ampO θ u (v - 1) + (I * (Real.sin θ : ℂ)) * ampE θ (u - 1) v := by
  have hu0 : ¬ (u = 0) := by omega
  have hv0 : ¬ (v = 0) := by omega
  unfold ampO ampE
  rw [if_neg hu0, if_neg hu0, if_neg hv0, Finset.mul_sum, Finset.mul_sum]
  set n : ℕ := min (u - 1) v with hn

  set F1 : ℕ → ℂ := fun j =>
    (Real.cos θ : ℂ) * ((Nat.choose (u - 1) j : ℂ) * (Nat.choose (v - 1) j : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) * (Real.cos θ : ℂ) ^ (u + (v - 1) - (2 * j + 1)))
    with hF1
  set F2 : ℕ → ℂ := fun k =>
    (I * (Real.sin θ : ℂ)) * ((Nat.choose (u - 1) (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) * (Real.cos θ : ℂ) ^ ((u - 1) + v - 2 * (k + 1)))
    with hF2
  set G : ℕ → ℂ := fun j =>
    (if j = 0 then 0 else (Nat.choose (u - 1) j : ℂ) * (Nat.choose (v - 1) (j - 1) : ℂ)) *
      (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) * (Real.cos θ : ℂ) ^ (u + v - (2 * j + 1))
    with hG
  set L : ℕ → ℂ := fun j =>
    (Nat.choose (u - 1) j : ℂ) * (Nat.choose v j : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) * (Real.cos θ : ℂ) ^ (u + v - (2 * j + 1))
    with hL
  have hEqL : (∑ j ∈ Finset.range (min (u - 1) v + 1),
      (Nat.choose (u - 1) j : ℂ) * (Nat.choose v j : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) *
          (Real.cos θ : ℂ) ^ (u + v - (2 * j + 1))) = ∑ j ∈ Finset.range (n + 1), L j := by
    rw [hL, hn]

  have hmn : min (u - 1) (v - 1) + 1 ≤ n + 1 := by omega
  have hR1 : (∑ j ∈ Finset.range (min (u - 1) (v - 1) + 1),
      (Real.cos θ : ℂ) * ((Nat.choose (u - 1) j : ℂ) * (Nat.choose (v - 1) j : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * j + 1) *
          (Real.cos θ : ℂ) ^ (u + (v - 1) - (2 * j + 1)))) =
      ∑ j ∈ Finset.range (n + 1), F1 j := by
    rw [hF1]
    refine Finset.sum_subset (Finset.range_subset_range.mpr hmn) ?_
    intro j hj hmem
    have hgt : min (u - 1) (v - 1) < j := by
      have h' : ¬ (j < min (u - 1) (v - 1) + 1) :=
        fun hlt => hmem (Finset.mem_range.mpr hlt)
      omega
    have hjv : j = v := by
      have hjn : j ≤ min (u - 1) v := by
        have h' : j < n + 1 := by simpa [Finset.mem_range] using hj
        omega
      have hlev : j ≤ v := le_trans hjn (Nat.min_le_right _ _)
      by_cases hc : u - 1 ≤ v - 1
      · rw [Nat.min_eq_left hc] at hgt
        have hm : min (u - 1) v = u - 1 := by
          apply Nat.min_eq_left
          omega
        omega
      · have hvu : v - 1 ≤ u - 1 := by omega
        rw [Nat.min_eq_right hvu] at hgt
        omega
    rw [hjv]
    simp [Nat.choose_eq_zero_of_lt (show v - 1 < v by omega)]

  have hR2 : (∑ k ∈ Finset.range n,
      (I * (Real.sin θ : ℂ)) * ((Nat.choose (u - 1) (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) *
          (Real.cos θ : ℂ) ^ ((u - 1) + v - 2 * (k + 1)))) =
      ∑ j ∈ Finset.range (n + 1), G j := by
    have hpt : ∀ k : ℕ, F2 k = G (k + 1) := by
      intro k
      rw [hF2, hG]
      have hk1 : k + 1 - 1 = k := by omega
      have hexp1 : (u - 1) + v - 2 * (k + 1) = (u + v - (2 * (k + 1) + 1)) := by omega
      simp only [hk1]
      rw [if_neg (by omega), hexp1]
      have hp : (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1) + 1) =
          (I * (Real.sin θ : ℂ)) * (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) := by
        rw [pow_succ']
      rw [hp]
      ring
    calc (∑ k ∈ Finset.range n, F2 k) = ∑ k ∈ Finset.range n, G (k + 1) := by
          apply Finset.sum_congr rfl; intro k _; exact hpt k
      _ = ∑ j ∈ Finset.range (n + 1), G j := by
          rw [sum_range_shift G n]
          rw [hG]; simp
  rw [hEqL, hR1, hR2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by simpa [Finset.mem_range] using hj
  simp only [hL, hF1, hG]
  have hju : j ≤ u - 1 := le_trans hjle (Nat.min_le_left _ _)
  have hjv : j ≤ v := le_trans hjle (Nat.min_le_right _ _)
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, pow_one,
      if_true, zero_mul, add_zero, Nat.mul_zero, Nat.zero_add]
    have hexp : u + v - 1 = (u + (v - 1) - 1) + 1 := by omega
    rw [hexp, pow_succ']
    ring
  · rw [if_neg (by omega)]
    have hpascal : Nat.choose v j = Nat.choose (v - 1) (j - 1) + Nat.choose (v - 1) j := by
      have h := Nat.choose_succ_succ (v - 1) (j - 1)
      simp only [Nat.succ_eq_add_one, show v - 1 + 1 = v by omega,
        show j - 1 + 1 = j by omega] at h
      exact h
    rw [hpascal]
    push_cast
    by_cases hcase : 2 * j + 1 ≤ u + (v - 1)
    · have hB : u + v - (2 * j + 1) = (u + (v - 1) - (2 * j + 1)) + 1 := by omega
      rw [hB, pow_succ']
      ring
    · have hzero : Nat.choose (v - 1) j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hzero]
      have hexp : u + v - (2 * j + 1) = 0 := by omega
      have hexp2 : u + (v - 1) - (2 * j + 1) = 0 := by omega
      rw [hexp, hexp2]
      simp

/-- At positive light-cone coordinates, the even amplitude satisfies the recurrence combining
the preceding even amplitude with the other preceding odd amplitude. See [Meyer1996a]. -/
theorem ampE_rec (θ : ℝ) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ampE θ u v =
      (Real.cos θ : ℂ) * ampE θ (u - 1) v + (I * (Real.sin θ : ℂ)) * ampO θ u (v - 1) := by
  have hv0 : ¬ (v = 0) := by omega
  have hu0 : ¬ (u = 0) := by omega
  unfold ampE ampO
  rw [if_neg hv0, if_neg hv0, if_neg hu0, Finset.mul_sum, Finset.mul_sum]
  set n : ℕ := min u v with hn
  set F1 : ℕ → ℂ := fun k =>
    (Real.cos θ : ℂ) * ((Nat.choose (u - 1) (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) * (Real.cos θ : ℂ) ^ ((u - 1) + v - 2 * (k + 1)))
    with hF1
  set F2 : ℕ → ℂ := fun k =>
    (Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) * (Real.cos θ : ℂ) ^ (u + v - 2 * (k + 1))
    with hF2
  set L : ℕ → ℂ := fun k =>
    (Nat.choose u (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
      (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) * (Real.cos θ : ℂ) ^ (u + v - 2 * (k + 1))
    with hL
  have hEqL : (∑ k ∈ Finset.range (min u v),
      (Nat.choose u (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) *
          (Real.cos θ : ℂ) ^ (u + v - 2 * (k + 1))) = ∑ k ∈ Finset.range n, L k := by
    rw [hL, hn]
  have hmn : min (u - 1) v ≤ n := by omega
  have hR1 : (∑ k ∈ Finset.range (min (u - 1) v),
      (Real.cos θ : ℂ) * ((Nat.choose (u - 1) (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * (k + 1)) *
          (Real.cos θ : ℂ) ^ ((u - 1) + v - 2 * (k + 1)))) =
      ∑ k ∈ Finset.range n, F1 k := by
    rw [hF1]
    refine Finset.sum_subset (Finset.range_subset_range.mpr hmn) ?_
    intro k hk hmem
    have hge : min (u - 1) v ≤ k := by
      have h' : ¬ (k < min (u - 1) v) := fun hlt => hmem (Finset.mem_range.mpr hlt)
      omega
    have hkl : k < n := by simpa [Finset.mem_range] using hk
    have hku : k = u - 1 := by
      by_cases h : u ≤ v
      · have hmin : min (u - 1) v = u - 1 := by
          apply Nat.min_eq_left; omega
        have hn' : n = u := by rw [hn]; exact Nat.min_eq_left h
        omega
      · have hmin : min (u - 1) v = v := by
          apply Nat.min_eq_right; omega
        have hn' : n = v := by rw [hn]; exact Nat.min_eq_right (by omega)
        omega
    rw [hku]
    simp [show u - 1 + 1 = u by omega,
      Nat.choose_eq_zero_of_lt (show u - 1 < u by omega)]
  have hne2 : min (u - 1) (v - 1) + 1 = n := by
    by_cases h : u ≤ v
    · have h1 : min u v = u := Nat.min_eq_left h
      have h2 : min (u - 1) (v - 1) = u - 1 := Nat.min_eq_left (by omega)
      simp [hn, h1, h2]
      omega
    · have h1 : min u v = v := Nat.min_eq_right (by omega)
      have h2 : min (u - 1) (v - 1) = v - 1 := Nat.min_eq_right (by omega)
      simp [hn, h1, h2]
      omega
  have hR2 : (∑ k ∈ Finset.range (min (u - 1) (v - 1) + 1),
      (I * (Real.sin θ : ℂ)) * ((Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
        (I * (Real.sin θ : ℂ)) ^ (2 * k + 1) *
          (Real.cos θ : ℂ) ^ (u + (v - 1) - (2 * k + 1)))) =
      ∑ k ∈ Finset.range n, F2 k := by
    have hpt2 : ∀ k : ℕ,
        (I * (Real.sin θ : ℂ)) * ((Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
          (I * (Real.sin θ : ℂ)) ^ (2 * k + 1) *
            (Real.cos θ : ℂ) ^ (u + (v - 1) - (2 * k + 1))) =
        (Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
          (I * (Real.sin θ : ℂ)) ^ (2 * k + 2) *
            (Real.cos θ : ℂ) ^ (u + v - 2 * k - 2) := by
      intro k
      have he : u + (v - 1) - (2 * k + 1) = u + v - 2 * k - 2 := by omega
      have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
      rw [he, h2, pow_succ']
      ring
    have hpt3 : ∀ k : ℕ, F2 k =
        (Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
          (I * (Real.sin θ : ℂ)) ^ (2 * k + 2) *
            (Real.cos θ : ℂ) ^ (u + v - 2 * k - 2) := by
      intro k
      simp only [hF2]
      have hs : 2 * (k + 1) = 2 * k + 2 := by omega
      have hc : u + v - (2 * k + 2) = u + v - 2 * k - 2 := by omega
      rw [hs, hc]
    calc (∑ k ∈ Finset.range (min (u - 1) (v - 1) + 1),
        (I * (Real.sin θ : ℂ)) * ((Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
          (I * (Real.sin θ : ℂ)) ^ (2 * k + 1) *
            (Real.cos θ : ℂ) ^ (u + (v - 1) - (2 * k + 1))))
        = ∑ k ∈ Finset.range (min (u - 1) (v - 1) + 1),
            (Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
              (I * (Real.sin θ : ℂ)) ^ (2 * k + 2) *
                (Real.cos θ : ℂ) ^ (u + v - 2 * k - 2) := by
          apply Finset.sum_congr rfl
          intro k _
          exact hpt2 k
      _ = ∑ k ∈ Finset.range n,
            (Nat.choose (u - 1) k : ℂ) * (Nat.choose (v - 1) k : ℂ) *
              (I * (Real.sin θ : ℂ)) ^ (2 * k + 2) *
                (Real.cos θ : ℂ) ^ (u + v - 2 * k - 2) := by rw [hne2]
      _ = ∑ k ∈ Finset.range n, F2 k := by
          apply Finset.sum_congr rfl
          intro k _
          exact (hpt3 k).symm
  rw [hEqL, hR1, hR2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjmin : j < min u v := by
    have h' : j < n := by simpa [Finset.mem_range] using hj
    simpa [hn] using h'
  have hju : j + 1 ≤ u := by
    have := Nat.min_le_left (a := u) (b := v); omega
  have hjv : j + 1 ≤ v := by
    have := Nat.min_le_right (a := u) (b := v); omega
  simp only [hL, hF1, hF2]
  have hpascal : Nat.choose u (j + 1) = Nat.choose (u - 1) j + Nat.choose (u - 1) (j + 1) := by
    have h := Nat.choose_succ_succ (u - 1) j
    simp only [Nat.succ_eq_add_one, show u - 1 + 1 = u by omega] at h
    exact h
  rw [hpascal]
  push_cast
  by_cases hcase : 2 * (j + 1) ≤ u + v - 1
  · have hB : u + v - 2 * (j + 1) = ((u - 1) + v - 2 * (j + 1)) + 1 := by omega
    rw [hB, pow_succ']
    ring
  · have hzero : Nat.choose (u - 1) (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero]
    have hexp : u + v - 2 * (j + 1) = 0 := by omega
    have hexp2 : (u - 1) + v - 2 * (j + 1) = 0 := by omega
    rw [hexp, hexp2]
    simp

/-- Away from the light-cone origin, applying the light-cone recurrence to the explicit
amplitudes reproduces them. See [Meyer1996a]. -/
theorem lcStep_ampVec (θ : ℝ) (u v : ℕ) (h : 0 < u + v) :
    lcStep θ (ampVec θ) u v = ampVec θ u v := by
  ext i
  fin_cases i
  · simp only [lcStep, ampVec, caBlockA_mulVec, caBlockB_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases hu0 : u = 0
    · subst hu0
      have hvne : ¬ v = 0 := by omega
      simp [ampO, hvne]
    by_cases hv0 : v = 0
    · subst hv0
      have hu1 : 1 ≤ u := by omega
      rw [ampE_zero_right, ampO_zero_right θ u hu1]
      simp [hu0, mul_assoc]
    · have hu1 : 1 ≤ u := by omega
      have hv1 : 1 ≤ v := by omega
      simp only [hu0, hv0, if_false]
      rw [ampO_rec θ u v hu1 hv1]
      simp
      ring
  · simp only [lcStep, ampVec, caBlockA_mulVec, caBlockB_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases hu0 : u = 0
    · subst hu0
      have hvne : ¬ v = 0 := by omega
      simp [ampE, ampO, hvne]
    by_cases hv0 : v = 0
    · subst hv0
      have hu1 : 1 ≤ u := by omega
      have hpow : (Real.cos θ : ℂ) ^ u = (Real.cos θ) * (Real.cos θ) ^ (u - 1) := by
        conv_lhs => rw [show u = (u - 1) + 1 by omega]
        rw [pow_succ']
      rw [ampE_zero_right θ u, ampE_zero_right θ (u - 1), ampO_zero_right θ u hu1]
      simp only [Nat.add_zero]
      rw [hpow]
      simp [hu0]
    · have hu1 : 1 ≤ u := by omega
      have hv1 : 1 ≤ v := by omega
      simp only [hu0, hv0, if_false]
      rw [ampE_rec θ u v hu1 hv1]
      simp

/-- Decreasing a positive left light-cone coordinate by one decreases its lattice position by
one. -/
lemma lcCell_pred_left (u v : ℕ) (hu : 1 ≤ u) :
    lcCell (u - 1) v = lcCell u v - 1 := by
  unfold lcCell
  have hcast : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by
    have := Nat.cast_sub hu (R := ℤ)
    simpa using this
  rw [hcast]
  ring

/-- Decreasing a positive right light-cone coordinate by one increases its lattice position by
one. -/
lemma lcCell_pred_right (u v : ℕ) (hv : 1 ≤ v) :
    lcCell u (v - 1) = lcCell u v + 1 := by
  unfold lcCell
  have hcast : ((v - 1 : ℕ) : ℤ) = (v : ℤ) - 1 := by
    have := Nat.cast_sub hv (R := ℤ)
    simpa using this
  rw [hcast]
  ring

/-- Evolution from `caPsi0` vanishes strictly to the right of the time-`t` light cone. See
[Meyer1996a]. -/
theorem caEvolve_gt (θ : ℝ) :
    ∀ (t : ℕ) (y : ℤ), (t : ℤ) < y → caEvolve θ t caPsi0 y = 0 := by
  intro t
  induction t with
  | zero =>
    intro y hy
    ext i
    fin_cases i <;> simp [caEvolve, caPsi0, show y ≠ 0 by omega]
  | succ t ih =>
    intro y hy
    have hy1 : (t : ℤ) < y - 1 := by omega
    have hy2 : (t : ℤ) < y + 1 := by omega
    show caStep θ (caEvolve θ t caPsi0) y = 0
    simp only [caStep]
    rw [ih (y - 1) hy1, ih (y + 1) hy2]
    ext i
    fin_cases i <;> simp [caBlockA_mulVec, caBlockB_mulVec]

/-- Evolution from `caPsi0` vanishes strictly to the left of the time-`t` light cone. See
[Meyer1996a]. -/
theorem caEvolve_lt (θ : ℝ) :
    ∀ (t : ℕ) (y : ℤ), y < -((t : ℤ)) → caEvolve θ t caPsi0 y = 0 := by
  intro t
  induction t with
  | zero =>
    intro y hy
    ext i
    fin_cases i <;> simp [caEvolve, caPsi0, show y ≠ 0 by omega]
  | succ t ih =>
    intro y hy
    have hy1 : y - 1 < -((t : ℤ)) := by omega
    have hy2 : y + 1 < -((t : ℤ)) := by omega
    show caStep θ (caEvolve θ t caPsi0) y = 0
    simp only [caStep]
    rw [ih (y - 1) hy1, ih (y + 1) hy2]
    ext i
    fin_cases i <;> simp [caBlockA_mulVec, caBlockB_mulVec]

/-- If `u + v = t`, evolution from the localized component-one state at `lcCell u v` equals the
explicit amplitude vector. See [Meyer1996a]. -/
theorem caEvolve_amp (θ : ℝ) :
    ∀ (t u v : ℕ), u + v = t →
      caEvolve θ t caPsi0 (lcCell u v) = ampVec θ u v := by
  intro t
  induction t with
  | zero =>
    intro u v huv
    have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst hu
    subst hv
    ext i
    fin_cases i <;> simp [caEvolve, caPsi0, lcCell, ampVec, ampO, ampE]
  | succ t ih =>
    intro u v huv
    show caStep θ (caEvolve θ t caPsi0) (lcCell u v) = ampVec θ u v
    simp only [caStep]
    rcases Nat.eq_zero_or_pos u with rfl | hu1
    · have hv : v = t + 1 := by omega
      have hv1 : 1 ≤ v := by omega
      have hlt : lcCell 0 v - 1 < -((t : ℤ)) := by
        unfold lcCell
        push_cast
        omega
      have h2 : lcCell 0 v + 1 = lcCell 0 (v - 1) := by
        rw [lcCell_pred_right 0 v hv1]
      have hsupp := caEvolve_lt θ t (lcCell 0 v - 1) hlt
      have e2 : 0 + (v - 1) = t := by omega
      rw [hsupp, h2, ih 0 (v - 1) e2]
      ext i
      fin_cases i <;>
        simp [caBlockA_mulVec, caBlockB_mulVec, ampVec, ampO_zero_left, ampE_zero_left,
          show 1 ≤ v by omega]
    · rcases Nat.eq_zero_or_pos v with rfl | hv1
      · have hgt : (t : ℤ) < lcCell u 0 + 1 := by
          unfold lcCell
          push_cast
          omega
        have h1 : lcCell u 0 - 1 = lcCell (u - 1) 0 := by
          rw [lcCell_pred_left u 0 hu1]
        have hsupp := caEvolve_gt θ t (lcCell u 0 + 1) hgt
        have e1 : (u - 1) + 0 = t := by omega
        rw [h1, ih (u - 1) 0 e1, hsupp]
        have hpow : Complex.cos (θ : ℂ) ^ u = Complex.cos (θ : ℂ) * Complex.cos (θ : ℂ) ^ (u - 1) := by
          conv_lhs => rw [show u = (u - 1) + 1 by omega]
          rw [pow_succ']
        ext i
        fin_cases i
        · simp [caBlockA_mulVec, caBlockB_mulVec, ampVec, ampE_zero_right,
            ampO_zero_right θ u hu1]
        · simp [caBlockA_mulVec, caBlockB_mulVec, ampVec, ampE_zero_right]
          rw [← hpow]
      · have h1 : lcCell u v - 1 = lcCell (u - 1) v := by
          rw [lcCell_pred_left u v hu1]
        have h2 : lcCell u v + 1 = lcCell u (v - 1) := by
          rw [lcCell_pred_right u v hv1]
        have e1 : (u - 1) + v = t := by omega
        have e2 : u + (v - 1) = t := by omega
        rw [h1, h2, ih (u - 1) v e1, ih u (v - 1) e2]
        have hstep := lcStep_ampVec θ u v (by omega)
        simp only [lcStep, if_neg (by omega : ¬ u = 0), if_neg (by omega : ¬ v = 0)] at hstep
        exact hstep

/-- The two-by-two matrix interchanging the two components. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Swapping components intertwines `caBlockA` with `caBlockB`. -/
theorem swap2_mul_caBlockA (θ : ℝ) :
    swap2 * caBlockA θ = caBlockB θ * swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2, caBlockA, caBlockB]

/-- Swapping components intertwines `caBlockB` with `caBlockA`. -/
theorem swap2_mul_caBlockB (θ : ℝ) :
    swap2 * caBlockB θ = caBlockA θ * swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2, caBlockA, caBlockB]

/-- The state localized at the origin in component zero. -/
def caPsi0L : ℤ → Fin 2 → ℂ := fun x i => if x = 0 ∧ i = 0 then 1 else 0

/-- The localized component-zero state is the reflected and component-swapped localized
component-one state. -/
theorem caPsi0L_eq (x : ℤ) : caPsi0L x = swap2.mulVec (caPsi0 (-x)) := by
  ext i
  fin_cases i <;>
    by_cases hx : x = 0 <;>
      simp [caPsi0L, caPsi0, swap2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx]

/-- Evolution from the component-zero initial state is obtained by reflecting and swapping the
evolution from the component-one initial state. See [Meyer1996a]. -/
theorem caEvolve_mirror (θ : ℝ) (t : ℕ) (x : ℤ) :
    caEvolve θ t caPsi0L x = swap2.mulVec (caEvolve θ t caPsi0 (-x)) := by
  have hA : ∀ w : Fin 2 → ℂ,
      swap2.mulVec ((caBlockA θ).mulVec w) = (caBlockB θ).mulVec (swap2.mulVec w) := by
    intro w
    rw [Matrix.mulVec_mulVec, swap2_mul_caBlockA θ, ← Matrix.mulVec_mulVec]
  have hB : ∀ w : Fin 2 → ℂ,
      swap2.mulVec ((caBlockB θ).mulVec w) = (caBlockA θ).mulVec (swap2.mulVec w) := by
    intro w
    rw [Matrix.mulVec_mulVec, swap2_mul_caBlockB θ, ← Matrix.mulVec_mulVec]
  induction t generalizing x with
  | zero => simp [caEvolve, caPsi0L_eq]
  | succ t ih =>
    show caStep θ (caEvolve θ t caPsi0L) x =
      swap2.mulVec (caStep θ (caEvolve θ t caPsi0) (-x))
    simp only [caStep, Matrix.mulVec_add]
    rw [ih (x - 1), ih (x + 1)]
    simp only [hA, hB]
    rw [show -(x - 1) = -x + 1 by ring, show -(x + 1) = -x - 1 by ring]
    rw [add_comm]

/-- For `u + v = t`, evolution from the localized component-zero state has components `ampE θ v
u` and `ampO θ v u`. See [Meyer1996a]. -/
theorem caEvolve_left_amp (θ : ℝ) (t u v : ℕ) (h : u + v = t) :
    caEvolve θ t caPsi0L (lcCell u v) = ![ampE θ v u, ampO θ v u] := by
  rw [caEvolve_mirror]
  have hneg : -(lcCell u v) = lcCell v u := by
    unfold lcCell
    push_cast
    ring
  rw [hneg, caEvolve_amp θ t v u (by omega)]
  ext i
  fin_cases i <;>
    simp [ampVec, swap2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Lattice evolution commutes with translation of the initial state by any integer. See
[Meyer1996a]. -/
theorem caEvolve_translate (θ : ℝ) (t : ℕ) (k : ℤ) (ψ : ℤ → Fin 2 → ℂ) :
    caEvolve θ t (fun x => ψ (x - k)) = fun x => caEvolve θ t ψ (x - k) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    show caStep θ (caEvolve θ t (fun x => ψ (x - k))) x =
      caStep θ (caEvolve θ t ψ) (x - k)
    rw [ih]
    simp only [caStep]
    rw [show x - k - 1 = x - 1 - k by ring,
      show x - k + 1 = x + 1 - k by ring]

/-- The explicit amplitude vector gives evolution from a translated component-one initial state
at the correspondingly translated light-cone position. See [Meyer1996a]. -/
theorem caEvolve_amp_translate (θ : ℝ) (t u v : ℕ) (h : u + v = t) (k : ℤ) :
    caEvolve θ t (fun x => caPsi0 (x - k)) (lcCell u v + k) = ampVec θ u v := by
  rw [caEvolve_translate θ t k caPsi0]
  change caEvolve θ t caPsi0 (lcCell u v + k - k) = ampVec θ u v
  rw [show lcCell u v + k - k = lcCell u v by ring, caEvolve_amp θ t u v h]

/-- The swapped explicit amplitudes give evolution from a translated component-zero initial
state at the correspondingly translated light-cone position. See [Meyer1996a]. -/
theorem caEvolve_left_amp_translate (θ : ℝ) (t u v : ℕ) (h : u + v = t) (k : ℤ) :
    caEvolve θ t (fun x => caPsi0L (x - k)) (lcCell u v + k) =
      ![ampE θ v u, ampO θ v u] := by
  rw [caEvolve_translate θ t k caPsi0L]
  change caEvolve θ t caPsi0L (lcCell u v + k - k) = ![ampE θ v u, ampO θ v u]
  rw [show lcCell u v + k - k = lcCell u v by ring, caEvolve_left_amp θ t u v h]

/-- For `u ≥ 1`, the odd recurrence amplitude equals the odd path sum. See [Meyer1996a]. -/
theorem ampO_eq_pathSumOdd (θ : ℝ) (u v : ℕ) (hu : 1 ≤ u) :
    ampO θ u v = pathSumOdd θ u v := by
  unfold ampO pathSumOdd
  rw [if_neg (by omega : ¬ u = 0)]
  have hmin : min (u - 1) v + 1 = min u (v + 1) := by
    rcases lt_or_ge v u with h | h
    · rw [Nat.min_eq_right (by omega : v ≤ u - 1), Nat.min_eq_right (by omega : v + 1 ≤ u)]
    · rw [Nat.min_eq_left (by omega : u - 1 ≤ v), Nat.min_eq_left (by omega : u ≤ v + 1)]
      omega
  rw [hmin]
  apply Finset.sum_congr rfl
  intro k _
  simp only [oddAmp]
  simp only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  ring

/-- For `v ≥ 1`, the even recurrence amplitude equals the even path sum. See [Meyer1996a]. -/
theorem ampE_eq_pathSumEven (θ : ℝ) (u v : ℕ) (hv : 1 ≤ v) :
    ampE θ u v = pathSumEven θ u v := by
  unfold ampE pathSumEven
  rw [if_neg (by omega : ¬ v = 0)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [evenAmp]
  have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [h1]
  ring

/-- Adding the straight-path boundary contribution to the even path sum gives `ampE` for all
light-cone coordinates. See [Meyer1996a]. -/
theorem fullEvenAmp_eq_ampE (θ : ℝ) (u v : ℕ) :
    fullEvenAmp θ u v = ampE θ u v := by
  by_cases hv : v = 0
  · subst hv
    simp [fullEvenAmp, ampE, pathSumEven]
  · rw [fullEvenAmp, ampE_eq_pathSumEven θ u v (by omega)]
    simp [hv]

end Qatlib.Papers.QCellAutomata96.MainResults
