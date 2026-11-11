/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc

set_option backward.isDefEq.respectTransparency false

/-!
# Eqs. (13)-(14): the walk eigenphases and the QSP target function

Source: G. H. Low and I. L. Chuang, *Optimal Hamiltonian Simulation by Quantum
Signal Processing*, arXiv:1606.02685v2 (2016-12-20), p. 4, Eqs. (13)-(14).

The Childs walk built from the sparse frame has eigenvalues
`Ŵ|λ±⟩ = e^{iθ_{λ±}}|λ±⟩` with Eq. (13)

`θ_{λ±} = ±arcsin(λ/(‖Ĥ‖max d)) + (1∓1)π/2`,

so the walk itself carries the *nonlinear* phase `±arcsin s` and the two
branches evolve in opposite directions.  The source's observation (p. 4) is
that this is harmless: with the target function of Eq. (14),

`h(θ) = -τ sin θ`  (so `h(θ_{λ±}) = -λ t`),

both branches land on the *same* phase `e^{-iλt}`, because the extra `(1∓1)π/2`
in Eq. (13) is invisible to `sin` and `sin(±arcsin s) = s`.  This is precisely
why uncomputing with `T̂†` after applying the QSP transform of `h` returns the
desired evolution `e^{-iλt}` independently of the `±` branch.

This module proves

* the eigenphase formulas of Eq. (13) as real angles `θ₊ = arcsin s`,
  `θ₋ = π - arcsin s`, their identification with the frozen eigenvalues
  `e^{i arcsin s}` and `-e^{-i arcsin s}`, and the fact that the two walk
  phases are *opposite*;
* Eq. (14): `h(θ₊) = h(θ₋) = -τs`, hence the QSP-transformed phase is the
  same evolution phase on both branches;
* the bridge to the actual walk: the frozen `sparseWalkEigenphasesRestricted`
  supplies the unitary `Ŵ = iS(2LL† - 1)`, the two eigenstates and their
  eigenphases, and the two conclusions above apply to those eigenstates.

The frame normalization `|c·ev| ≤ 1` is the hypothesis under which `arcsin` is
evaluated; it is what the frozen eigenphase formula `arcsin(c·ev)` already
presupposes (and what its Lowc proof derives internally from
`‖(c:ℂ) • H‖ ≤ 1` together with the normalized eigenvector).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamSimQSP17.SparseWalk

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Eq. (14): the QSP target function `h(θ) = -τ sin θ`, with
`τ = t d ‖Ĥ‖max`. -/
def simulationTarget (τ θ : ℝ) : ℝ := -τ * Real.sin θ

/-- Eq. (13), `+` branch: `θ₊ = +arcsin s + (1-1)π/2 = arcsin s`. -/
abbrev walkPhasePlus (s : ℝ) : ℝ := Real.arcsin s

/-- Eq. (13), `-` branch: `θ₋ = -arcsin s + (1+1)π/2 = π - arcsin s`. -/
abbrev walkPhaseMinus (s : ℝ) : ℝ := Real.pi - Real.arcsin s

/-- The `+` eigenphase has sine `s`; the `(1∓1)π/2` term of Eq. (13) does not
affect `sin`. -/
theorem sin_walkPhasePlus {s : ℝ} (hs : |s| ≤ 1) : Real.sin (walkPhasePlus s) = s := by
  rw [walkPhasePlus]
  exact Real.sin_arcsin (by linarith [neg_abs_le s]) (by linarith [le_abs_self s])

/-- The `-` eigenphase has the same sine `s` (`sin(π - x) = sin x`). -/
theorem sin_walkPhaseMinus {s : ℝ} (hs : |s| ≤ 1) : Real.sin (walkPhaseMinus s) = s := by
  have h := sin_walkPhasePlus hs
  rw [walkPhaseMinus, Real.sin_pi_sub]
  exact h

/-- The two walk eigenphase factors of Eq. (13) are *opposite*:
`e^{iθ₋} = -e^{-iθ₊}`.  This is the "phases in opposite directions" of p. 4
that makes plain (untransformed) walk iteration fail. -/
theorem walkPhaseFactor_opposite (s : ℝ) :
    Complex.exp (Complex.I * ((walkPhaseMinus s : ℝ) : ℂ))
      = -Complex.exp (Complex.I * -((walkPhasePlus s : ℝ) : ℂ)) := by
  have hsplit : Complex.I * ((walkPhaseMinus s : ℝ) : ℂ)
      = Real.pi * Complex.I + Complex.I * -((walkPhasePlus s : ℝ) : ℂ) := by
    rw [walkPhaseMinus, walkPhasePlus]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **Eq. (14), `+` branch:** `h(θ₊) = -τ s`. -/
theorem simulationTarget_walkPhasePlus {τ s : ℝ} (hs : |s| ≤ 1) :
    simulationTarget τ (walkPhasePlus s) = -(τ * s) := by
  rw [simulationTarget, sin_walkPhasePlus hs]
  ring

/-- **Eq. (14), `-` branch:** `h(θ₋) = -τ s` as well. -/
theorem simulationTarget_walkPhaseMinus {τ s : ℝ} (hs : |s| ≤ 1) :
    simulationTarget τ (walkPhaseMinus s) = -(τ * s) := by
  rw [simulationTarget, sin_walkPhaseMinus hs]
  ring

/-- **Eq. (14): `h(θ_{λ+}) = h(θ_{λ-})`.**  The target function is blind to the
branch index. -/
theorem simulationTarget_branch_independent (τ s : ℝ) (hs : |s| ≤ 1) :
    simulationTarget τ (walkPhasePlus s) = simulationTarget τ (walkPhaseMinus s) := by
  rw [simulationTarget_walkPhasePlus hs, simulationTarget_walkPhaseMinus hs]

/-- **Eq. (14): `h(θ_{λ±}) = -λt`.**  With `s = c·ev` and `τ·c = t` both walk
branches are mapped to the evolution phase `e^{-iλt}`. -/
theorem simulationTarget_eq_evolutionPhase (τ c ev t : ℝ) (hs : |c * ev| ≤ 1)
    (ht : τ * c = t) :
    simulationTarget τ (walkPhasePlus (c * ev)) = -(t * ev) ∧
      simulationTarget τ (walkPhaseMinus (c * ev)) = -(t * ev) := by
  have hval : τ * (c * ev) = t * ev := by rw [← mul_assoc, ht]
  rw [simulationTarget_walkPhasePlus hs, simulationTarget_walkPhaseMinus hs, hval]
  exact ⟨rfl, rfl⟩

/-- **Eq. (14), as a phase factor:** the QSP transform of `h(θ) = -τ sin θ`
applied to either walk eigenphase is the *same* evolution phase `e^{-iλt}`, so
both walk eigenstates are corrected by the same factor and uncomputing with
`T̂†` restores the eigenbasis of `Ĥ`. -/
theorem targetPhase_eq_evolutionPhase (τ c ev t : ℝ) (hs : |c * ev| ≤ 1)
    (ht : τ * c = t) :
    Complex.exp (Complex.I * ((simulationTarget τ (walkPhasePlus (c * ev)) : ℝ) : ℂ))
        = Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ))) ∧
      Complex.exp (Complex.I * ((simulationTarget τ (walkPhaseMinus (c * ev)) : ℝ) : ℂ))
        = Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ))) := by
  obtain ⟨hp, hm⟩ := simulationTarget_eq_evolutionPhase τ c ev t hs ht
  constructor
  · rw [hp, show Complex.I * ((-(t * ev) : ℝ) : ℂ)
        = -(Complex.I * ((t * ev : ℝ) : ℂ)) by push_cast; ring]
  · rw [hm, show Complex.I * ((-(t * ev) : ℝ) : ℂ)
        = -(Complex.I * ((t * ev : ℝ) : ℂ)) by push_cast; ring]

/-! ## Bridge to the frozen walk -/

/-- **Eqs. (13)-(14) on the actual walk.**  For the frozen Childs walk
`Ŵ = iS(2LL† - 1)` built from the sparse frame (`L†R = cH`, `S` a self-adjoint
unitary involution exchanging the frames), every normalized real eigenpair
`Hψ = ev·ψ` has two walk eigenstates whose eigenphase factors are
`e^{iθ₊}` and `e^{iθ₋}` of Eq. (13), and the QSP target `h(θ) = -τ sin θ`
evaluated at either of them is the evolution phase `e^{-iλt}`.

The walk eigenphase factors themselves differ (`e^{iθ₋} = -e^{-iθ₊}`), which is
exactly the obstruction that Eq. (14) removes. -/
theorem sparseWalk_targetPhase
    (hSW : Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestricted)
    (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (H : Matrix I I ℂ) (c τ t : ℝ) (hc : 0 < c) (hH : ‖(c : ℂ) • H‖ ≤ 1)
    (L R : Matrix W I ℂ) (S : Matrix W W ℂ)
    (hL : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L)
    (hR : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R)
    (hLR : L.conjTranspose * R = (c : ℂ) • H)
    (hS : S ∈ Matrix.unitaryGroup W ℂ) (hSsym : S.conjTranspose = S) (hS2 : S * S = 1)
    (hSL : S * L = R)
    (ψ : I → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (ev : ℝ) (hev : H *ᵥ ψ = (ev : ℂ) • ψ)
    (hs : |c * ev| ≤ 1) (ht : τ * c = t) :
    ∃ (wp wm : W → ℂ) (V : Matrix W W ℂ),
      V ∈ Matrix.unitaryGroup W ℂ ∧
      V *ᵥ wp = Complex.exp (Complex.I * ((walkPhasePlus (c * ev) : ℝ) : ℂ)) • wp ∧
      V *ᵥ wm = Complex.exp (Complex.I * ((walkPhaseMinus (c * ev) : ℝ) : ℂ)) • wm ∧
      Complex.exp (Complex.I * ((simulationTarget τ (walkPhasePlus (c * ev)) : ℝ) : ℂ))
          = Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ))) ∧
      Complex.exp (Complex.I * ((simulationTarget τ (walkPhaseMinus (c * ev)) : ℝ) : ℂ))
          = Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ))) := by
  obtain ⟨wp, wm, ap, am, hwp, hwm, horth, ⟨V, hV, hVdef, hVp, hVm⟩, hsplit⟩ :=
    hSW I W H c hc hH L R S hL hR hLR hS hSsym hS2 hSL ψ hψ ev hev
  refine ⟨wp, wm, V, hV, ?_, ?_, ?_⟩
  · exact hVp
  · rw [hVm, ← walkPhaseFactor_opposite (c * ev)]
  · exact targetPhase_eq_evolutionPhase τ c ev t hs ht

end Qatlib.Papers.HamSimQSP17.SparseWalk
