/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.CubeFourier
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

noncomputable def contCoeffByWeight (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  Real.cos (2 * t / n) ^ k

noncomputable def contDist (n : ℕ) (t : ℝ) (x : Cube n) : ℝ :=
  uniformMass n * ∑ S, contCoeffByWeight n t S.card * chi S x

lemma cos_two_t_at_odd_multiple {n k : ℕ} (hn : 0 < n) (hk : Odd k) :
    Real.cos (2 * ((k : ℝ) * (Real.pi / 4) * n) / n) = 0 := by
  obtain ⟨m, hm⟩ := hk
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have harg : 2 * ((k : ℝ) * (Real.pi / 4) * n) / (n : ℝ) = (k : ℝ) * Real.pi / 2 := by
    field_simp
    ring
  rw [harg]
  have hkπ : (k : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi + Real.pi / 2 := by
    rw [hm]
    push_cast
    ring
  rw [hkπ, Real.cos_add]
  simp [Real.sin_nat_mul_pi]

lemma contCoeff_eq_zero_at_odd_multiple {n k : ℕ} (hn : 0 < n) (hk : Odd k)
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    contCoeffByWeight n ((k : ℝ) * (Real.pi / 4) * n) S.card = 0 := by
  have hcos := cos_two_t_at_odd_multiple hn hk
  rw [contCoeffByWeight, hcos]
  exact zero_pow (Finset.card_ne_zero.mpr hS)

theorem contDist_uniform_at_odd_multiple {n k : ℕ} (hn : 0 < n) (hk : Odd k)
    (x : Cube n) :
    contDist n ((k : ℝ) * (Real.pi / 4) * n) x = uniformMass n := by
  classical
  have hsum : (∑ S, contCoeffByWeight n ((k : ℝ) * (Real.pi / 4) * n) S.card * chi S x) = 1 := by
    have hsingle := Finset.sum_eq_single
      (s := Finset.univ)
      (f := fun S : Finset (Fin n) =>
        contCoeffByWeight n ((k : ℝ) * (Real.pi / 4) * n) S.card * chi S x)
      (∅ : Finset (Fin n))
      (fun S _ hS => by
        change contCoeffByWeight n ((k : ℝ) * (Real.pi / 4) * n) S.card * chi S x = 0
        rw [contCoeff_eq_zero_at_odd_multiple hn hk
          (Finset.nonempty_iff_ne_empty.mpr hS), zero_mul])
      (fun hmem => absurd (Finset.mem_univ _) hmem)
    rw [hsingle]
    simp [contCoeffByWeight, chi, cubeChar]
  rw [contDist, hsum, mul_one]

theorem continuousWalk_zero_instantaneous_mixing {n k : ℕ} (hn : 0 < n) (hk : Odd k) :
    tvDist (contDist n ((k : ℝ) * (Real.pi / 4) * n)) = 0 := by
  classical
  have huniform : ∀ x : Cube n,
      contDist n ((k : ℝ) * (Real.pi / 4) * n) x - uniformMass n = 0 := by
    intro x
    rw [contDist_uniform_at_odd_multiple hn hk x, sub_self]
  rw [tvDist]
  simp only [huniform, abs_zero, Finset.sum_const_zero, mul_zero]

end Qatlib.Papers.HypercubeWalk01.MainResults
