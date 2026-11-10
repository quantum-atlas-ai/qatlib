/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphModelMath.SrgQuotient.Hamiltonian
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.NoGlobalSym14.NativeReduction
open Matrix
open Qatlib.Foundations.GraphModelMath.SrgQuotient
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)

theorem actual_srg_reduction {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n-k-1) (gamma : ℝ) (z : Fin 3 → ℂ) :
    ‖normalizedEmbed G w k (n-k-1) z‖ = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ ∧
    hamiltonian G w gamma *ᵥ (normalizedEmbed G w k (n-k-1) z).ofLp =
      (normalizedEmbed G w k (n-k-1)
        (normalHamiltonian k (n-k-1) l m gamma *ᵥ z)).ofLp ∧
    (normalizedEmbed G w k (n-k-1) z).ofLp w = z 0 ∧
    (hamiltonian G w gamma).IsHermitian :=
  ⟨normalized_isometry G w h hk hb z,
    normalized_hamiltonian G w h hk hb gamma z,
    normalized_marked_amplitude G w k (n-k-1) z,
    hamiltonian_hermitian G w gamma⟩

theorem uniform_initial_norm {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hn : 0 < n) (hk : 0 < k) (hb : 0 < n-k-1) :
    ‖normalizedEmbed G w k (n-k-1) (uniformCoeffs n k (n-k-1))‖ = 1 := by
  rw [actual_uniform G w hk hb]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp [h.card, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hnr.le, ne_of_gt hnr]

theorem actual_power_marked {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (hk : 0 < k) (hb : 0 < n-k-1) (gamma : ℝ) (p : ℕ) (z : Fin 3 → ℂ) :
    (hamiltonian G w gamma ^ p *ᵥ (normalizedEmbed G w k (n-k-1) z).ofLp) w =
      (normalHamiltonian k (n-k-1) l m gamma ^ p *ᵥ z) 0 := by
  rw [normalized_power G w h hk hb, normalized_marked_amplitude]
end Qatlib.Papers.NoGlobalSym14.NativeReduction
