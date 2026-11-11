/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Papers.HamSimQSP17.SparseWalk.EigenphaseTarget

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 applied on the walk: the compiled word carries `e^{-iλt}` on both branches

Source: G. H. Low and I. L. Chuang, *Optimal Hamiltonian Simulation by Quantum
Signal Processing*, arXiv:1606.02685v2 (2016-12-20), pp. 3-4.

The source's simulation pipeline has two halves that are proved separately.

* Theorem 2 (p. 3) compiles an `ε`-Fourier approximation of `e^{ih}` into a
  source word of length `N` whose projection `⟨+|V̂|+⟩` is within `8ε` of
  `e^{ih(θ)}` for every angle `θ` of the covered range (Eq. (8); the frozen
  `lcSourceCompilation` is the repository's compiled form of it).
* Eqs. (13)-(14) (p. 4) give the angles at which the walk must be evaluated:
  the eigenstates `|λ±⟩` of `Ŵ` carry eigenphases `θ_{λ±}`, and the target
  function `h(θ) = -τ sin θ` satisfies `h(θ_{λ±}) = -λt` on *both* branches.

This module joins the two: instantiate Theorem 2 at `h(θ) = -τ sin θ` and
evaluate its guarantee at the walk eigenphases. The result is that a single
compiled source word, applied at either eigenphase, produces the evolution
phase `e^{-iλt}` to within `8ε` — the mechanism by which the paper's
Hamiltonian simulation is exact in the `±` branch after uncomputing with `T̂†`.

Scope. This is the *frame-level, per-eigenpair* statement of the simulation:
the eigenphases come from the frozen restricted walk (isometric frames with
`L†R = cH`, `S` exchanging them), and the compilation guarantee is the frozen
source-word compiler. The sector covered is `0 ≤ c·ev` (eigenvalues `λ ≥ 0`);
the sector `λ < 0` is the reflection `θ ↦ -θ` of the same argument, which the
odd target and the symmetric eigenphase pair make identical, and is left out
of this statement rather than assumed away. The general sparse-oracle
embedding, the operator-level trace distance over arbitrary superpositions and
the resource counts of Theorem 3 remain outside this module.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamSimQSP17.SparseWalk

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.QspSimulation.Achievability (lcSourceCompilation)
open Qatlib.Concepts.QsvtCore.PhaseExistence (lcPlusAmp realEval)

/-- The target of Eq. (14) is odd, as Theorem 2 requires of `h`. -/
theorem simulationTarget_odd (τ : ℝ) : ∀ θ : ℝ, simulationTarget τ (-θ) = -simulationTarget τ θ := by
  intro θ
  simp only [simulationTarget, Real.sin_neg]
  ring

/-- The `+` walk eigenphase of Eq. (13) lies in the compiled angle range
`[0, 2π]` in the sector `0 ≤ c·ev` of positive eigenvalues. -/
theorem walkPhasePlus_mem (s : ℝ) (hs0 : 0 ≤ s) (_hs : s ≤ 1) :
    walkPhasePlus s ∈ Set.Icc 0 (2 * Real.pi) := by
  have h0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have h1 : Real.arcsin s ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  have hpi : Real.pi / 2 ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
  exact ⟨h0, by simpa [walkPhasePlus] using le_trans h1 hpi⟩

/-- The `-` walk eigenphase of Eq. (13) lies in the compiled angle range
`[0, 2π]` in the sector `0 ≤ c·ev` of positive eigenvalues. -/
theorem walkPhaseMinus_mem (s : ℝ) (hs0 : 0 ≤ s) (_hs : s ≤ 1) :
    walkPhaseMinus s ∈ Set.Icc 0 (2 * Real.pi) := by
  have h0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have h1 : Real.arcsin s ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  constructor
  · have : Real.arcsin s ≤ Real.pi := by nlinarith [Real.pi_pos]
    simp only [walkPhaseMinus]
    linarith
  · simp only [walkPhaseMinus]
    linarith [Real.pi_pos]

/-- **Theorem 2 at `h(θ) = -τ sin θ`, evaluated at the walk eigenphases.**
Given an `ε`-Fourier approximation of `e^{-iτ sin θ}` (the Jacobi–Anger pair of
Eqs. (15)-(17) is one), the frozen compiler produces a source word of length
`N` whose projection is within `8ε` of the evolution phase `e^{-iλt}` at *both*
walk eigenphases of Eq. (13), with `s = c·ev` and `τ·c = t`. -/
theorem compiledWord_at_walkEigenphases
    (N : ℕ) (A Qt : Polynomial ℝ) (ε τ t c ev : ℝ)
    (hN : Even N) (hp : 0 < N) (hε : 0 < ε) (hε16 : ε ≤ 1 / 16)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (N : WithBot ℕ)) (hQtdeg : Qt.degree < (N : WithBot ℕ))
    (happrox : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) *
        realEval Qt (Real.cos (θ / 2) : ℂ) - Complex.exp (Complex.I * (simulationTarget τ θ : ℂ))‖
        ≤ ε)
    (hs : |c * ev| ≤ 1) (hs0 : 0 ≤ c * ev) (ht : τ * c = t) :
    ∃ phis : List ℝ, phis.length = N ∧
      ‖lcPlusAmp phis (walkPhasePlus (c * ev))
          - Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ)))‖ ≤ 8 * ε ∧
      ‖lcPlusAmp phis (walkPhaseMinus (c * ev))
          - Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ)))‖ ≤ 8 * ε := by
  have hs1 : c * ev ≤ 1 := (abs_le.mp hs).2
  obtain ⟨phis, hlen, hamp⟩ :=
    lcSourceCompilation N (simulationTarget τ) A Qt ε hN hp (simulationTarget_odd τ)
      hAeven hQtodd hAdeg hQtdeg hε hε16 happrox
  obtain ⟨hplus, hminus⟩ := targetPhase_eq_evolutionPhase τ c ev t hs ht
  refine ⟨phis, hlen, ?_, ?_⟩
  · have := hamp (walkPhasePlus (c * ev)) (walkPhasePlus_mem (c * ev) hs0 hs1)
    rw [hplus] at this
    exact this
  · have := hamp (walkPhaseMinus (c * ev)) (walkPhaseMinus_mem (c * ev) hs0 hs1)
    rw [hminus] at this
    exact this

/-- **The simulation pipeline on the actual walk, per eigenpair.**  For the
frozen Childs walk of the sparse frame and an `ε`-Jacobi–Anger pair for
`h(θ) = -τ sin θ`, there is a source word of length `N` such that, on *each*
walk eigenstate of Eq. (13), the projection `⟨+|V̂|+⟩` realises the evolution
phase `e^{-iλt}` to within `8ε`.  Both branches therefore carry the same
phase, which is what makes uncomputing with `T̂†` return `e^{-iλt}|λ⟩`. -/
theorem sparseWalk_compiledEvolutionPhase
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
    (N : ℕ) (A Qt : Polynomial ℝ) (ε : ℝ)
    (hN : Even N) (hp : 0 < N) (hε : 0 < ε) (hε16 : ε ≤ 1 / 16)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (N : WithBot ℕ)) (hQtdeg : Qt.degree < (N : WithBot ℕ))
    (happrox : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) *
        realEval Qt (Real.cos (θ / 2) : ℂ) - Complex.exp (Complex.I * (simulationTarget τ θ : ℂ))‖
        ≤ ε)
    (hs : |c * ev| ≤ 1) (hs0 : 0 ≤ c * ev) (ht : τ * c = t) :
    ∃ (wp wm : W → ℂ) (V : Matrix W W ℂ) (phis : List ℝ),
      V ∈ Matrix.unitaryGroup W ℂ ∧ phis.length = N ∧
      V *ᵥ wp = Complex.exp (Complex.I * ((walkPhasePlus (c * ev) : ℝ) : ℂ)) • wp ∧
      V *ᵥ wm = Complex.exp (Complex.I * ((walkPhaseMinus (c * ev) : ℝ) : ℂ)) • wm ∧
      ‖lcPlusAmp phis (walkPhasePlus (c * ev))
          - Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ)))‖ ≤ 8 * ε ∧
      ‖lcPlusAmp phis (walkPhaseMinus (c * ev))
          - Complex.exp (-(Complex.I * ((t * ev : ℝ) : ℂ)))‖ ≤ 8 * ε := by
  obtain ⟨wp, wm, V, hV, hVp, hVm, _⟩ :=
    sparseWalk_targetPhase hSW I W H c τ t hc hH L R S hL hR hLR hS hSsym hS2 hSL
      ψ hψ ev hev hs ht
  obtain ⟨phis, hlen, hp, hm⟩ :=
    compiledWord_at_walkEigenphases N A Qt ε τ t c ev hN hp hε hε16 hAeven hQtodd
      hAdeg hQtdeg happrox hs hs0 ht
  exact ⟨wp, wm, V, phis, hV, hlen, hVp, hVm, hp, hm⟩

end Qatlib.Papers.HamSimQSP17.SparseWalk
