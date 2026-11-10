/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphModelMath.SrgQuotient.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
namespace Qatlib.Foundations.GraphModelMath.SrgQuotient
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)

omit [DecidableEq V] in

theorem sum_near {n k l m : ℕ} (h : G.IsSRGWith n k l m) (a : ℝ) :
    (∑ v : V, if G.Adj v w then a else 0) = k * a := by
  have he : Finset.univ.filter (fun v => G.Adj v w) = G.neighborFinset w := by
    ext v; simp [G.adj_comm]
  rw [← Finset.sum_filter, Finset.sum_const, he,
    SimpleGraph.card_neighborFinset_eq_degree, h.regular.degree_eq]
  simp

theorem sum_far {n k l m : ℕ} (h : G.IsSRGWith n k l m) (a : ℝ) :
    (∑ v : V, if v ≠ w ∧ ¬ G.Adj v w then a else 0) = ((n-k-1 : ℕ) : ℝ) * a := by
  simpa only [SimpleGraph.compl_adj] using sum_near Gᶜ w h.compl a

omit [Fintype V] in

theorem embed_mass_point (z : Fin 3 → ℂ) (v : V) :
    ‖embed G w z v‖ ^ 2 =
      (if v = w then ‖z 0‖^2 else 0) +
      (if G.Adj v w then ‖z 1‖^2 else 0) +
      (if v ≠ w ∧ ¬G.Adj v w then ‖z 2‖^2 else 0) := by
  by_cases hv : v = w
  · subst v; simp [embed, marked, near, far]
  · by_cases ha : G.Adj v w <;> simp [embed, marked, near, far, hv, ha]

theorem embed_norm_sq {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (z : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 (embed G w z) : EuclideanSpace ℂ V)‖^2 =
      ‖z 0‖^2 + k * ‖z 1‖^2 + ((n-k-1 : ℕ) : ℝ) * ‖z 2‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [embed_mass_point, Finset.sum_add_distrib]
  rw [sum_near G w h, sum_far G w h]
  simp

noncomputable def unscale (k b : ℕ) (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![z 0, z 1 / (Real.sqrt k : ℂ), z 2 / (Real.sqrt b : ℂ)]

noncomputable def normalizedEmbed (k b : ℕ) (z : Fin 3 → ℂ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (embed G w (unscale k b z))

theorem normalized_isometry {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n-k-1) (z : Fin 3 → ℂ) :
    ‖normalizedEmbed G w k (n-k-1) z‖ = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hbr : (0 : ℝ) < (n-k-1 : ℕ) := by exact_mod_cast hb
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalizedEmbed, embed_norm_sq G w h, EuclideanSpace.norm_sq_eq]
  change ‖z 0‖^2 + (k : ℝ) * ‖z 1 / (Real.sqrt k : ℂ)‖^2 +
    ((n-k-1 : ℕ) : ℝ) * ‖z 2 / (Real.sqrt (n-k-1 : ℕ) : ℂ)‖^2 =
    ∑ i : Fin 3, ‖z i‖^2
  simp [Fin.sum_univ_succ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hkr.le,
    Real.sq_sqrt hbr.le]
  field_simp [ne_of_gt hkr, ne_of_gt hbr]
  ring
end Qatlib.Foundations.GraphModelMath.SrgQuotient
