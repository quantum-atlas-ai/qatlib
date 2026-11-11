/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# TimeDilation — Proposition 1 and Corollary 1 (arXiv:2303.01471v1, Appendix A.3)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1.
PDF pages 19–20; equations (A.24)–(A.32).

* `source_time_dilation` is Proposition 1 (A.26)–(A.28): reparametrising the
  time variable `t ↦ τ(t)` multiplies both Hamiltonian coefficients by `τ̇`
  (equivalently shifts `φ, χ` by `log τ̇`).
* `source_corollary1_three_parameter` is Corollary 1 (A.32): with
  `φ_t = α_t − γ_t`, `χ_t = α_t + β_t + γ_t`, the dilated parameters are
  `α̃ = α∘τ + log τ̇`, `β̃ = β∘τ`, `γ̃ = γ∘τ`, and the ideal scaling
  condition (A.25) is preserved if and only if `τ̇ > 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.TimeDilation

open Qatlib.Papers.QHamDescent23.MainResults

/-- Scalar rearrangement behind Proposition 1: a real rescaling `r` of the
time derivative factors through the two QHD coefficients. -/
theorem qhd_dilate_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K F : E →L[ℂ] E) (a b : ℝ → ℝ) (r : ℝ) (t : ℝ) (x : E) :
    r • ((-Complex.I) • qhdHamiltonian a b K F t x)
      = (-Complex.I) • qhdHamiltonian (fun s => r * a s) (fun s => r * b s) K F t x := by
  rw [qhdHamiltonian_apply, qhdHamiltonian_apply, smul_comm r (-Complex.I)]
  congr 1
  rw [smul_add]
  congr 1
  · rw [← smul_assoc r (a t : ℂ) (K x), Algebra.smul_def, Complex.ofReal_mul]; rfl
  · rw [← smul_assoc r (b t : ℂ) (F x), Algebra.smul_def, Complex.ofReal_mul]; rfl

/-- Source Proposition 1 (Time dilation), arXiv:2303.01471v1, p.19–20,
equations (A.26)–(A.28). If `Ψ` solves `i d/dt |Ψ_t⟩ = H(t)|Ψ_t⟩` for the
QHD Hamiltonian `H(t) = a_t K + b_t F`, and `τ` is a smooth reparametrisation
with derivative `τ̇`, then `t ↦ Ψ(τ(t))` solves the Schrödinger equation for
the dilated Hamiltonian whose coefficients are `a(τ t)·τ̇(t)` and
`b(τ t)·τ̇(t)` — i.e. `e^{φ_{τ t}+log τ̇}` and `e^{χ_{τ t}+log τ̇}` in (A.28). -/
theorem source_time_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K F : E →L[ℂ] E) (a b : ℝ → ℝ) (τ τ' : ℝ → ℝ)
    (hτ : ∀ t, HasDerivAt τ (τ' t) t)
    (Ψ : ℝ → E) (hΨ : Schrodinger (qhdHamiltonian a b K F) Ψ) :
    ∀ t, HasDerivAt (fun s => Ψ (τ s))
      ((-Complex.I) • qhdHamiltonian (fun s => τ' s * a (τ s))
        (fun s => τ' s * b (τ s)) K F t (Ψ (τ t))) t := by
  intro t
  have h := HasDerivAt.scomp (h := τ) (x := t) (hΨ (τ t)) (hτ t)
  have hval :
      (τ' t) • ((-Complex.I) • qhdHamiltonian a b K F (τ t) (Ψ (τ t)))
        = (-Complex.I) • qhdHamiltonian (fun s => τ' s * a (τ s))
            (fun s => τ' s * b (τ s)) K F t (Ψ (τ t)) := by
    convert! qhd_dilate_scalar K F (fun s => a (τ s)) (fun s => b (τ s))
      (τ' t) t (Ψ (τ t)) using 1
  rw [hval] at h
  convert! h using 1

/-! ### Corollary 1: three-parameter rescaling -/

/-- Source Corollary 1, arXiv:2303.01471v1, p.20, equations (A.32a)–(A.32c)
and the invariance of the ideal scaling condition (A.25).

With `φ_t = α_t − γ_t` and `χ_t = α_t + β_t + γ_t` as in (A.24), the
time-dilated Hamiltonian of Proposition 1 is again a three-parameter QHD
Hamiltonian with
`α̃_t = α_{τ t} + log τ̇(t)`, `β̃_t = β_{τ t}`, `γ̃_t = γ_{τ t}`.
The two displayed identities record that `φ̃ = α̃ − γ̃` and
`χ̃ = α̃ + β̃ + γ̃`; the two `HasDerivAt` conjuncts record that the
time-dilated parameters have derivatives `β̇_{τ t}·τ̇(t)` and `γ̇_{τ t}·τ̇(t)`.
Finally `α,β,γ` satisfy (A.25) if and only if the dilated parameters do,
because `τ̇ > 0` is a positive factor on both sides of `β̇ ≤ e^{α}` and
`γ̇ = e^{α}`. The hypothesis `hτsurj` is the paper's standing reading of
`t ↦ τ(t)` as a reparametrisation of the whole time horizon (so that every
dilated time is attained); it is what makes the converse direction of the
`iff` meaningful. -/
theorem source_corollary1_three_parameter
    (α β γ β' γ' τ τ' : ℝ → ℝ)
    (hβ : ∀ t, HasDerivAt β (β' t) t)
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hτ : ∀ t, HasDerivAt τ (τ' t) t)
    (hτpos : ∀ t, 0 < τ' t)
    (hτsurj : Function.Surjective τ) :
    (∀ t, (α (τ t) - γ (τ t)) + Real.log (τ' t)
        = (α (τ t) + Real.log (τ' t)) - γ (τ t)) ∧
    (∀ t, (α (τ t) + β (τ t) + γ (τ t)) + Real.log (τ' t)
        = (α (τ t) + Real.log (τ' t)) + β (τ t) + γ (τ t)) ∧
    (∀ t, HasDerivAt (fun s => β (τ s)) (β' (τ t) * τ' t) t) ∧
    (∀ t, HasDerivAt (fun s => γ (τ s)) (γ' (τ t) * τ' t) t) ∧
    (IdealScaling α β γ β' γ' ↔
      IdealScaling (fun t => α (τ t) + Real.log (τ' t))
        (fun t => β (τ t)) (fun t => γ (τ t))
        (fun t => β' (τ t) * τ' t) (fun t => γ' (τ t) * τ' t)) := by
  refine ⟨fun t => by ring, fun t => by ring, ?_, ?_, ?_⟩
  · intro t
    convert! (hβ (τ t)).comp t (hτ t) using 1
  · intro t
    convert! (hγ (τ t)).comp t (hτ t) using 1
  · constructor
    · intro h t
      obtain ⟨hle, heq⟩ := h (τ t)
      have ht := hτpos t
      change β' (τ t) * τ' t ≤ Real.exp (α (τ t) + Real.log (τ' t)) ∧
        γ' (τ t) * τ' t = Real.exp (α (τ t) + Real.log (τ' t))
      have hexp : Real.exp (α (τ t) + Real.log (τ' t)) = τ' t * Real.exp (α (τ t)) := by
        rw [Real.exp_add, Real.exp_log ht, mul_comm]
      refine ⟨?_, ?_⟩
      · calc β' (τ t) * τ' t ≤ Real.exp (α (τ t)) * τ' t :=
              mul_le_mul_of_nonneg_right hle (le_of_lt ht)
          _ = Real.exp (α (τ t) + Real.log (τ' t)) := by rw [hexp]; ring
      · rw [heq, hexp]; ring
    · intro h s
      obtain ⟨t, rfl⟩ := hτsurj s
      obtain ⟨hle, heq⟩ := h t
      simp only at hle heq
      have ht := hτpos t
      have hexp : Real.exp (α (τ t) + Real.log (τ' t)) = Real.exp (α (τ t)) * τ' t := by
        rw [Real.exp_add, Real.exp_log ht]
      refine ⟨?_, ?_⟩
      · have h1 : β' (τ t) * τ' t ≤ Real.exp (α (τ t)) * τ' t := by
          rw [hexp] at hle
          simpa [mul_comm] using hle
        exact (mul_le_mul_iff_left₀ ht).mp h1
      · have h1 : γ' (τ t) * τ' t = Real.exp (α (τ t)) * τ' t := by
          rw [hexp] at heq
          simpa [mul_comm] using heq
        exact (mul_left_inj' (ne_of_gt ht)).mp h1

end Qatlib.Papers.QHamDescent23.MainResults.TimeDilation
