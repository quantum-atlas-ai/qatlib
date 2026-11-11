/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Revised finite-grid path summation (Eqs. (58)–(62))

Source: J. Yepez, *Quantum lattice gas model of Dirac particles in 1+1 dimensions*,
arXiv:1307.3595v1 (2013), Sec. IV B, Eqs. (58)–(62), pp. 10–11.

A discrete trajectory on a finite grid is a spin chain `s : Fin (N+1) → Bool`
(`true` = spin-up / stream-plus, `false` = spin-down / stream-minus).  A *bend*
occurs at step `i` when `s i` and `s (i+1)` differ (Eq. (61))

  `bend s i = 1` if `s i ≠ s (i+1)`, else `0`,

and the total number of bends is `R = ∑_{i=0}^{N-1} bend s i` (Eq. (62a)); the
number of straight steps is `R̄ = N - R` (Eq. (62b)).  The path sum (59) weights
each path by `(√(1 - (m c² τ/ℏ)²))^{R̄} · (i m c² τ/ℏ)^R`; grouping paths by their
bend count `R` recovers the representation (58)

  `K_{s₀s_N}(a,b) = ∑_{R ≥ 0} Φ_{αβ}(R) (√(1 - (m c² τ/ℏ)²))^{R̄} (i m c² τ/ℏ)^R`

with `Φ_{αβ}(R)` the number of paths having `R` bends, subject to the
magnetisation constraint (60) `∑_{i=0}^{N-1} s_i = M`.

The main theorem `pathSum_groupBy_bends` is the combinatorial identity underlying
this equivalence: summing the path weight over all paths with magnetisation `M`
equals the `Φ`-weighted sum over bend counts.  It is fully proved.
-/

set_option autoImplicit false

open Finset

namespace Qatlib.Papers.DiracLatGas13.MainResults

noncomputable section

/-- The spin value in `{+1, -1}` attached to a `Bool` spin variable. -/
def spinVal (b : Bool) : ℤ := if b then 1 else -1

/-- Magnetisation constraint (Eq. (60)): the sum of the first `N` spins equals `M`. -/
def magnetization (N : ℕ) (s : Fin (N + 1) → Bool) : ℤ :=
  ∑ i : Fin N, spinVal (s i.castSucc)

/-- Bend indicator (Eq. (61)): `1` at a direction change, `0` at a straight step. -/
def bend {N : ℕ} (s : Fin (N + 1) → Bool) (i : Fin N) : ℕ :=
  if s i.castSucc = s i.succ then 0 else 1

/-- Total bend count `R` of a trajectory (Eq. (62a)). -/
def bends (N : ℕ) (s : Fin (N + 1) → Bool) : ℕ :=
  ∑ i : Fin N, bend s i

/-- The number `R̄ = N - R` of straight steps (Eq. (62b)). -/
def nonBends (N : ℕ) (s : Fin (N + 1) → Bool) : ℕ := N - bends N s

/-- The finite set of trajectories with magnetisation `M`. -/
def paths (N : ℕ) (M : ℤ) : Finset (Fin (N + 1) → Bool) :=
  Finset.univ.filter (fun s => magnetization N s = M)

/-- The number `Φ_{αβ}(R)` of paths with `R` bends and magnetisation `M`. -/
def phi (N : ℕ) (M : ℤ) (R : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin (N + 1) → Bool =>
    magnetization N s = M ∧ bends N s = R)).card

/-- Each bend contributes at most one, so `R ≤ N`. -/
theorem bends_le (N : ℕ) (s : Fin (N + 1) → Bool) : bends N s ≤ N := by
  unfold bends
  calc ∑ i : Fin N, bend s i ≤ ∑ _i : Fin N, 1 := by
        apply Finset.sum_le_sum
        intro i _
        unfold bend
        split <;> norm_num
    _ = N := by simp

/-- The path weight (59): `a^{R̄} · b^{R}` with `a = √(1-(mc²τ/ℏ)²)`,
`b = i mc²τ/ℏ`. -/
def pathWeight (a b : ℂ) (N : ℕ) (s : Fin (N + 1) → Bool) : ℂ :=
  a ^ nonBends N s * b ^ bends N s

/-- On a fixed bend-`R` fibre the weight is the constant `a^{N-R} · b^R`. -/
theorem pathWeight_eq_of_bends (a b : ℂ) (N : ℕ)
    (s : Fin (N + 1) → Bool) (R : ℕ) (hR : bends N s = R) :
    pathWeight a b N s = a ^ (N - R) * b ^ R := by
  unfold pathWeight nonBends
  rw [hR]

/-- **Grouping (58) ⟺ (59).** Summing the path weight over all trajectories with
magnetisation `M` equals the `Φ`-weighted sum over their bend counts; this is the
combinatorial content of the equivalence of Eq. (58) and Eq. (59) (pp. 10–11). -/
theorem pathSum_groupBy_bends (N : ℕ) (M : ℤ) (a b : ℂ) :
    ∑ s ∈ paths N M, pathWeight a b N s
      = ∑ R ∈ (paths N M).image (bends N),
          (phi N M R : ℂ) * (a ^ (N - R) * b ^ R) := by
  classical
  have hfib_sum :
      ∑ s ∈ paths N M, pathWeight a b N s
        = ∑ R ∈ (paths N M).image (bends N),
            ∑ s ∈ (paths N M).filter (fun s => bends N s = R),
              pathWeight a b N s :=
    (Finset.sum_fiberwise_of_maps_to (s := paths N M) (t := (paths N M).image (bends N))
      (g := bends N) (f := pathWeight a b N)
      (fun i hi => Finset.mem_image_of_mem (bends N) hi)).symm
  rw [hfib_sum]
  apply Finset.sum_congr rfl
  intro R _
  have hfib : (paths N M).filter (fun s => bends N s = R)
      = Finset.univ.filter (fun s : Fin (N + 1) → Bool =>
          magnetization N s = M ∧ bends N s = R) := by
    ext s
    simp only [paths, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfib]
  rw [Finset.sum_congr rfl (fun s hs => by
        obtain ⟨-, -, hR'⟩ := Finset.mem_filter.mp hs
        exact pathWeight_eq_of_bends a b N s R hR')]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [phi]

end

end Qatlib.Papers.DiracLatGas13.MainResults
