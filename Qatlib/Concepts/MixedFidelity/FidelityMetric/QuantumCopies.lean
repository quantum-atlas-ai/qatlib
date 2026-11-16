/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.PhyslibBridge
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section


set_option autoImplicit false
set_option warningAsError true
/-! # Fidelity of actual mixed tensor powers

The existing public matrix tensor identity is transported to bundled Physlib
states. A proved coordinate equivalence connects its actual pi-product `npow`
carrier to binary products; the empty tensor power is handled explicitly.
-/

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators

/-- Root fidelity multiplies on products of bundled states in finite coordinates. -/
private theorem fidelity_prod_fin {D E : ℕ} (ρ σ : MState (Fin D))
    (τ ω : MState (Fin E)) :
    MState.fidelity (ρ.prod τ) (σ.prod ω) = MState.fidelity ρ σ * MState.fidelity τ ω := by
  have h := (g1 D σ.m ρ.m ⟨σ.psd, σ.tr'⟩ ⟨ρ.psd, ρ.tr'⟩).2.2.2.2.2.2.2.2
    E ω.m τ.m ⟨ω.psd, ω.tr'⟩ ⟨τ.psd, τ.tr'⟩
  simp only [MState.fidelity_eq_traceNorm_sqrt_mul_sqrt, mstate_sqrt_mat]
  exact h

/-- Root fidelity multiplies on products of arbitrary finite mixed states. -/
theorem fidelity_prod {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (ρ σ : MState d) (τ ω : MState e) :
    MState.fidelity (ρ.prod τ) (σ.prod ω) = MState.fidelity ρ σ * MState.fidelity τ ω := by
  let f := (Fintype.equivFin d).symm
  let g := (Fintype.equivFin e).symm
  have h := fidelity_prod_fin (ρ.relabel f) (σ.relabel f) (τ.relabel g) (ω.relabel g)
  have hp (a : MState d) (b : MState e) :
      (a.relabel f).prod (b.relabel g) = (a.prod b).relabel (f.prodCongr g) := rfl
  simpa only [hp, fidelity_relabel] using h

/-- Splitting off the first tensor factor identifies the actual Physlib copy state. -/
theorem npow_succ_relabel {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (n : ℕ) :
    (ρ.npow (n+1)).relabel (Fin.consEquiv (fun _ : Fin (n+1) => d)) =
      ρ.prod (ρ.npow n) := by
  ext x y
  change (∏ i : Fin (n+1), ρ.m ((Fin.consEquiv (fun _ : Fin (n+1) => d)) x i)
    ((Fin.consEquiv (fun _ : Fin (n+1) => d)) y i)) =
      ρ.m x.1 y.1 * ∏ i : Fin n, ρ.m (x.2 i) (y.2 i)
  simp [Fin.prod_univ_succ, Fin.consEquiv]

/-- The root fidelity of actual mixed-state tensor powers is the single-copy power. -/
theorem fidelity_npow {d : Type*} [Fintype d] [DecidableEq d]
    (ρ σ : MState d) (n : ℕ) :
    MState.fidelity (ρ.npow n) (σ.npow n) = MState.fidelity ρ σ ^ n := by
  induction n with
  | zero =>
    have h : ρ.npow 0 = σ.npow 0 := by
      ext x y
      change (∏ i : Fin 0, ρ.m (x i) (y i)) = ∏ i : Fin 0, σ.m (x i) (y i)
      simp
    rw [h, MState.fidelity_self_eq_one, pow_zero]
  | succ n ih =>
    rw [← fidelity_relabel (ρ.npow (n+1)) (σ.npow (n+1))
      (Fin.consEquiv (fun _ : Fin (n+1) => d)), npow_succ_relabel, npow_succ_relabel,
      fidelity_prod, ih, pow_succ, mul_comm]

end Qatlib.Concepts.MixedFidelity.FidelityMetric
