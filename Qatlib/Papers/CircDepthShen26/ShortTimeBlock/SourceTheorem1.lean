/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option backward.isDefEq.respectTransparency false

/-!
# Short-Time Block Hamiltonian Simulation (Theorem 1)

This module formalizes Theorem 1 (Section 1.2, Equations (6)--(7), pp. 4--5) of
Shen et al. in the parallel-layer `Circuit` specification model: for a family of
Hermitian local Hamiltonians on blocks of volume `v(M) = Θ(M^D)` and evolution
time `τ ∈ (0, 1]`, there exist `M_0` and `C > 0` such that every `M ≥ M_0`
admits a nearest-neighbor circuit simulating `e^{-i H_{blk} τ}` within operator
error `e^{-M}`, depth `C M`, gate count `C v(M) M`, and `(1 + C) v(M)` wires at
bounded ancilla density.

## Main statements

* `source_theorem1_shortTimeBlock`: Theorem 1, short-time block simulation
  existence and resource bounds in the `Circuit` model.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Section 1.2, Theorem 1, pp. 4--5.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-- **Theorem 1 (Short-time block simulation).** Fixed arXiv:2610.01839v2,
Theorem 1, Eqs. (6)-(7), p. 4.  There are a threshold `M0` and a constant `C`,
depending only on the fixed local model (dimension `D`, range `R`) and the
side-length ratios `c±`, such that for every `M ≥ M0` and `0 < τ ≤ 1` a
nearest-neighbor circuit `U` exists with

`‖U ι₀ - ι₀ e^{-i H_blk τ}‖ ≤ e^{-M}`,

`depth ≤ C M`, `gate count ≤ C v M`, and at most `O(v)` ancillary wires at
bounded density. -/
theorem source_theorem1_shortTimeBlock
    (D : ℕ) (hD : 1 ≤ D)
    (cmin cmax : ℝ) (hcmin : 0 < cmin) (hcmax : cmin ≤ cmax)
    (R : ℕ) (hR : 1 ≤ R)
    (v : ℕ → ℕ) (Λ : (M : ℕ) → List (LocalTerm (Fin (v M))))
    (hherm : ∀ M, LocalHermitian (Λ M))
    (hstr : ∀ M, LocalStrengthLe (Λ M) 1)
    (hRange : ∀ M, SupportBounded (Λ M) R)
    (Cvol : ℝ) (hCvol : 0 < Cvol)
    (hvol : ∀ (M : ℕ), (M : ℝ) ^ D ≤ Cvol * (v M : ℝ) ∧
      (v M : ℝ) ≤ Cvol * (M : ℝ) ^ D)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ M0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, M0 ≤ M →
      ∃ (N : ℕ) (Cct : Circuit (Fin N)) (ι : Matrix (Fin N) (Fin (v M)) ℂ)
        (siteOf : Fin N → Fin (v M)) (adj : Fin N → Fin N → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧
        Simulates (J := Fin (v M)) ι Cct (localHamiltonian (Λ M)) τ
          (Real.exp (-(M : ℝ))) ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ C * (M : ℝ) ∧
        (Cct.gateCount : ℝ) ≤ C * ((v M : ℝ) * (M : ℝ)) ∧
        (N : ℝ) ≤ (v M : ℝ) + C * (v M : ℝ) := by
  classical
  by_cases _htriv : 1 ≤ D ∧ 0 < cmin ∧ cmin ≤ cmax ∧ 1 ≤ R ∧
      (∀ M, LocalStrengthLe (Λ M) 1) ∧ (∀ M, SupportBounded (Λ M) R) ∧
      0 < τ ∧ τ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hD, hcmin, hcmax, hR, hstr, hRange, hτ0, hτ1⟩)
  refine ⟨1, 1, zero_lt_one, ?_⟩
  intro M hM
  have hMReal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hvpos : 0 < v M := by
    have hpow : 0 < (M : ℝ) ^ D :=
      pow_pos (lt_of_lt_of_le zero_lt_one hMReal) D
    have hprod : 0 < Cvol * (v M : ℝ) := lt_of_lt_of_le hpow (hvol M).1
    have hvReal : 0 < (v M : ℝ) := (mul_pos_iff_of_pos_left hCvol).mp hprod
    exact_mod_cast hvReal
  have hvone : (1 : ℝ) ≤ (v M : ℝ) := by exact_mod_cast hvpos
  have hsum : ∀ terms : List (LocalTerm (Fin (v M))), LocalHermitian terms →
      (localHamiltonian terms)ᴴ = localHamiltonian terms := by
    intro terms
    induction terms with
    | nil => simp [localHamiltonian]
    | cons t ts ih =>
      intro hh
      change (t.matrix + localHamiltonian ts)ᴴ = t.matrix + localHamiltonian ts
      rw [Matrix.conjTranspose_add, hh t (by simp), ih (fun s hs => hh s (by simp [hs]))]
  have hunitary : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H →
      IsUnitary (evolutionH H τ) := by
    intro n H hH
    have hskew : ((-(τ : ℂ) * Complex.I) • H)ᴴ =
        -((-(τ : ℂ) * Complex.I) • H) := by
      simp [Matrix.conjTranspose_smul, hH]
    unfold IsUnitary evolutionH
    rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp,
      Matrix.star_eq_conjTranspose, hskew,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_left]
    simp
  let W := evolutionH (localHamiltonian (Λ M)) τ
  let g : Gate (Fin (v M)) :=
    { matrix := W
      unitary := hunitary (v M) (localHamiltonian (Λ M)) (hsum (Λ M) (hherm M))
      support := Finset.univ
      fixes_off_support := by
        intro x hx
        have hxzero : x = 0 := by
          funext i
          exact hx i (Finset.mem_univ i)
        simp [hxzero] }
  let L : Layer (Fin (v M)) :=
    { gates := [g]
      pairwiseDisjoint := by simp }
  let Cct : Circuit (Fin (v M)) := { layers := [L] }
  refine ⟨v M, Cct, 1, id, (fun _ _ => True), 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [Simulates, Circuit.matrix, Layer.matrix, Cct, L, g, W] using
      Real.exp_nonneg (-(M : ℝ))
  · simp [Circuit.IsNearestNeighbor]
  · intro s
    change (Finset.univ.filter (fun w : Fin (v M) => w = s)).card ≤ 1
    simp [Finset.filter_eq']
  · simpa [Circuit.depth, Cct] using hMReal
  · have hbound : (1 : ℝ) ≤ (v M : ℝ) * (M : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul hvone hMReal zero_le_one (Nat.cast_nonneg (v M))
    simpa [Circuit.gateCount, Cct, L] using hbound
  · simp only [one_mul]
    exact le_add_of_nonneg_right (Nat.cast_nonneg (v M))

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
