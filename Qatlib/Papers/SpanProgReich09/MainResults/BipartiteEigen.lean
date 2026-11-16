/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.BipEigen.Core
public import Qatlib.Papers.SpanProgReich09.MainResults.Section8.SpectralModel

@[expose] public section


/-! # Both directions of the source Proposition 8.8

These specialize the shared finite-matrix algebra to the pinned paper's actual predicates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Papers.SpanProgReich09.MainResults.Section8

namespace Qatlib.Papers.SpanProgReich09.MainResults

/-- The pinned bipartite adjacency has the shared rectangular block action. -/
theorem bipAction {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (u : T → ℂ) (v : U → ℂ) :
    bipAdj B *ᵥ Sum.elim u v = Sum.elim (B *ᵥ v) (Bᴴ *ᵥ u) := by
  exact Qatlib.Foundations.PureStateMath.BipEigen.bipAction B u v

/-- Proposition 8.8 gives the sign pair and both actual squared eigenvectors. -/
theorem prop88Forward {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (ρ : ℝ) (hρ : ρ ≠ 0) (u : T → ℂ) (v : U → ℂ)
    (heig : IsEigenvector (bipAdj B) ρ (Sum.elim u v)) :
    IsEigenvector (bipAdj B) (-ρ) (Sum.elim u (fun i => -v i)) ∧
      IsEigenvector (B * Bᴴ) (ρ ^ 2) u ∧ IsEigenvector (Bᴴ * B) (ρ ^ 2) v := by
  exact Qatlib.Foundations.PureStateMath.BipEigen.prop88Forward B ρ hρ u v heig

/-- Proposition 8.8 recovers both signs from a positive squared eigenvalue. -/
theorem prop88Converse {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (lam : ℝ) (hlam : 0 < lam)
    (φ : T → ℂ) (heig : IsEigenvector (B * Bᴴ) lam φ) :
    IsEigenvector (Bᴴ * B) lam (Bᴴ *ᵥ φ) ∧
      IsEigenvector (bipAdj B) (Real.sqrt lam)
        (Sum.elim φ (fun i => (1 / Real.sqrt lam) * (Bᴴ *ᵥ φ) i)) ∧
      IsEigenvector (bipAdj B) (-Real.sqrt lam)
        (Sum.elim φ (fun i => -(1 / Real.sqrt lam) * (Bᴴ *ᵥ φ) i)) := by
  have hsrc :
      IsEigenvector (Bᴴ * B) lam (Bᴴ *ᵥ φ) ∧
        IsEigenvector (bipAdj B) (Real.sqrt lam)
          (Sum.elim φ (fun i => (1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i)) ∧
        IsEigenvector (bipAdj B) (-Real.sqrt lam)
          (Sum.elim φ (fun i => -(1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i)) :=
    Qatlib.Foundations.PureStateMath.BipEigen.prop88Converse B lam hlam φ heig
  simpa only [Complex.ofReal_div, Complex.ofReal_one] using hsrc


end Qatlib.Papers.SpanProgReich09.MainResults
