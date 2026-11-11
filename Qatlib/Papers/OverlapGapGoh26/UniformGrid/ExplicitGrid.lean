/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Explicit grids for one-half Hölder paths

`uniformGrid` and `gridResolution` provide an explicit mesh for families of paths with a common
one-half Hölder bound. The approximation and cardinality estimates supply the deterministic
discretization step used for the energy paths associated with [GohMuller2026].

## Main statements

* `uniform_holder_grid`: the chosen mesh approximates every path on the specified data set.
* `uniform_holder_grid_card`: the mesh cardinality is bounded explicitly by the Hölder constant
  and tolerance.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.Grid

/-- The finite set of mesh points `j / n` for `j : Fin (n + 1)`. -/
def uniformGrid (n : ℕ) : Finset ℝ :=
  Finset.univ.image (fun j : Fin (n+1) => (j:ℝ)/(n:ℝ))

/-- The uniform grid contains at most `n + 1` points. -/
theorem uniformGrid_card (n : ℕ) : (uniformGrid n).card≤n+1 := by
  simpa only [uniformGrid,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_image_le (s:=Finset.univ) (f:=fun j : Fin (n+1) => (j:ℝ)/(n:ℝ)))

/-- For positive `n`, every point of `uniformGrid n` lies in `[0, 1]`. -/
theorem uniformGrid_mem {n : ℕ} (hn : 0<n) (σ : ℝ) (hσ : σ∈uniformGrid n) :
    σ∈Set.Icc (0:ℝ) 1 := by
  obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hσ
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_one hn').mpr
    exact_mod_cast (show j.val≤n by omega)

/-- For positive `n`, every point of `[0, 1]` is within `1 / n` of a point of `uniformGrid n`. -/
theorem uniformGrid_cover {n : ℕ} (hn : 0<n) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    ∃ σ∈uniformGrid n, |τ-σ|≤1/(n:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  let k : ℕ := Nat.floor (τ*(n:ℝ))
  have hklo : (k:ℝ)≤τ*(n:ℝ) := Nat.floor_le (mul_nonneg hτ.1 hn'.le)
  have hkhi : τ*(n:ℝ)<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkn : k≤n := by
    have h : (k:ℝ)≤n := hklo.trans (by nlinarith [hτ.2])
    exact_mod_cast h
  let j : Fin (n+1) := ⟨k,by omega⟩
  refine ⟨(j:ℝ)/(n:ℝ),Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
  have hlow : (k:ℝ)/(n:ℝ)≤τ := (div_le_iff₀ hn').mpr hklo
  have hupp : τ<((k:ℝ)+1)/(n:ℝ) := (lt_div_iff₀ hn').mpr hkhi
  change |τ-(k:ℝ)/(n:ℝ)|≤1/(n:ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  rw [add_div] at hupp
  linarith

/-- The positive mesh resolution `ceil ((2 * H / ε)^2) + 1`. -/
def gridResolution (H ε : ℝ) : ℕ := Nat.ceil ((2*H/ε)^2)+1

/-- The chosen grid resolution is positive for every `H` and `ε`. -/
theorem gridResolution_pos (H ε : ℝ) : 0<gridResolution H ε := by unfold gridResolution; omega

/-- For nonnegative `H` and positive `ε`, the Hölder error at the chosen mesh size is at most `ε
/ 2`. -/
theorem holder_mesh_bound (H ε : ℝ) (hH : 0≤H) (hε : 0<ε) :
    H*Real.sqrt (1/(gridResolution H ε:ℝ))≤ε/2 := by
  let n := gridResolution H ε
  have hn : (0:ℝ)<n := by exact_mod_cast gridResolution_pos H ε
  have hc : (2*H/ε)^2≤(n:ℝ) := by
    have h := Nat.le_ceil ((2*H/ε)^2)
    dsimp [n,gridResolution]
    push_cast
    linarith
  have he : (2*H/ε)^2=4*H^2/ε^2 := by ring
  rw [he] at hc
  have hb : 4*H^2≤(n:ℝ)*ε^2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  have hs : (H*Real.sqrt (1/(n:ℝ)))^2=H^2/(n:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    ring
  have hsq : (H*Real.sqrt (1/(n:ℝ)))^2≤(ε/2)^2 := by
    rw [hs]
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hpos : 0≤H*Real.sqrt (1/(n:ℝ)) := by positivity
  nlinarith

/-- A family with common one-half Hölder constant `H` on `D` is uniformly approximated to within
positive `ε` by the chosen grid. -/
theorem uniform_holder_grid {Ω : Type} (F : Ω → ℝ → ℝ) (D : Set Ω)
    (H ε : ℝ) (hH : 0≤H) (hε : 0<ε)
    (hmod : ∀ w∈D,∀ τ∈Set.Icc (0:ℝ) 1,∀ σ∈Set.Icc (0:ℝ) 1,
      |F w τ-F w σ|≤H*Real.sqrt |τ-σ|) :
    ∀ w∈D,∀ τ∈Set.Icc (0:ℝ) 1,∃ σ∈uniformGrid (gridResolution H ε),|F w τ-F w σ|<ε := by
  intro w hw τ hτ
  obtain ⟨σ,hσ,hclose⟩ := uniformGrid_cover (gridResolution_pos H ε) τ hτ
  refine ⟨σ,hσ,?_⟩
  have hσ' := uniformGrid_mem (gridResolution_pos H ε) σ hσ
  calc
    _ ≤ H*Real.sqrt |τ-σ| := hmod w hw τ hτ σ hσ'
    _ ≤ H*Real.sqrt (1/(gridResolution H ε:ℝ)) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hclose) hH
    _ ≤ ε/2 := holder_mesh_bound H ε hH hε
    _ < ε := by linarith

/-- The cardinality of the chosen uniform grid, viewed as a real number, is at most `(2 * H /
ε)^2 + 3`. -/
theorem uniform_holder_grid_card (H ε : ℝ) :
    ((uniformGrid (gridResolution H ε)).card:ℝ)≤(2*H/ε)^2+3 := by
  have hc := uniformGrid_card (gridResolution H ε)
  have hc' : ((uniformGrid (gridResolution H ε)).card:ℝ)≤(gridResolution H ε:ℝ)+1 := by
    exact_mod_cast hc
  have hceil := Nat.ceil_lt_add_one (show 0≤(2*H/ε)^2 by positivity)
  dsimp [gridResolution] at hc' ⊢
  push_cast at hc'
  linarith

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.Grid
