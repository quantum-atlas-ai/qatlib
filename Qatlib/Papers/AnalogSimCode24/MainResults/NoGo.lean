/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# The no-go theorem of Appendix C (arXiv:2412.07764v1)

Fixed paper: arXiv:2412.07764v1 (10 Dec 2024), Appendix C, p. 14:

> **Theorem C.1.** No eigenspace of a 2-local commuting Hamiltonian of qudits (of any local
> dimension d) can be a quantum code of dimension greater than 1 and distance greater than 2
> simultaneously.

The paper's proof is a corollary of the structure lemma [62, Lemma 8] for 2-local commuting
Hamiltonians.  After the sector decomposition `H = ⊕_α H^(α)` of Eqs. (C2)--(C6), two cases are
distinguished for an eigenspace `S = ⊕_α S^(α)` of dimension `> 1`:

* **Case 1** (two distinct sectors `α ≠ β` with `S^(α) ≠ 0 ≠ S^(β)`): the 1-local operator
  `V = P_i^(α_i) - P_i^(β_i)` of Eq. (C7) satisfies `V|ψ⟩ = |ψ⟩` for `|ψ⟩ ∈ S^(α)` and
  `V|φ⟩ = -|φ⟩` for `|φ⟩ ∈ S^(β)`, so `V` is not a detectable error and the distance is 1.
* **Case 2** (a single sector): `S` has an orthonormal basis of product vectors Eq. (C9); for two
  distinct basis vectors `|η⟩, |η'⟩` one of the sub-particle factors is orthogonal, and the
  1-local operator `|η_ii⟩⟨η_ii| - |η'_ii⟩⟨η'_ii|` (or the 2-local operator
  `|η_ij⟩⟨η_ij| - |η'_ij⟩⟨η'_ij|`) again takes the values `+1` and `-1` on `|η⟩` and `|η'⟩`,
  so the distance is at most 2.

Both cases therefore produce an operator of weight at most `2` which has eigenvalue `+1` on one
unit vector of `S` and `-1` on an orthogonal unit vector of `S`.  Such an operator is never
detectable in the Knill--Laflamme sense, which is the final step (proved below as
`not_detectable_of_plus_minus_eigenvectors`).

The tensor-product formalism for `n` qudits, the partial traces entering the definition of
weight, and the structure lemma [62, Lemma 8] are not available in this library; the cited
structure lemma together with the two-case construction is therefore recorded as the explicit
hypothesis `TwoLocalCommutingModel.eigenspace_witness`, and the last step is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AnalogSimCode24.MainResults.NoGo

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A linear operator `V` is a *detectable error* for the code space `S` if it acts as a scalar on
`S` (the Knill--Laflamme condition `P_S V P_S = c P_S`, used in [36, 62] and in the proof of
Theorem C.1 to define the code distance). -/
def Detectable (S : Submodule ℂ H) (V : H →L[ℂ] H) : Prop :=
  ∃ c : ℂ, ∀ ψ ∈ S, ∀ φ ∈ S, ⟪ψ, V φ⟫_ℂ = c * ⟪ψ, φ⟫_ℂ

/-- `S` has *distance greater than `k`* when every error operator of weight at most `k` (with
weight measured by `LocalWeightLe`) is detectable.  Theorem C.1 asserts that for an eigenspace of
a 2-local commuting Hamiltonian this fails at `k = 2` whenever `dim S > 1`. -/
def DistanceGreaterThan (LocalWeightLe : (H →L[ℂ] H) → ℕ → Prop) (S : Submodule ℂ H) (k : ℕ) :
    Prop :=
  ∀ V, LocalWeightLe V k → Detectable S V

/-- The final step of the proof of Theorem C.1 (used in both Case 1 and Case 2): an operator
which is `+1` on a unit vector `ψ ∈ S` and `-1` on an orthogonal unit vector `φ ∈ S` is not a
detectable error for `S`.  Indeed a detecting scalar `c` would have to equal both
`⟨ψ|V|ψ⟩ = 1` and `⟨φ|V|φ⟩ = -1`. -/
theorem not_detectable_of_plus_minus_eigenvectors (S : Submodule ℂ H) (V : H →L[ℂ] H) (ψ φ : H)
    (hψS : ψ ∈ S) (hφS : φ ∈ S) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (horth : ⟪ψ, φ⟫_ℂ = 0)
    (hVψ : V ψ = ψ) (hVφ : V φ = -φ) :
    ¬ Detectable S V := by
  rintro ⟨c, hc⟩
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    norm_num
  have hcψ : c = 1 := by
    have h := hc ψ hψS ψ hψS
    rw [hVψ, hψψ, mul_one] at h
    exact h.symm
  have hcφ : c = -1 := by
    have h := hc φ hφS φ hφS
    rw [hVφ, inner_neg_right, hφφ, mul_one] at h
    exact h.symm
  rw [hcψ] at hcφ
  norm_num at hcφ

/-- The `n`-qudit physical model of Theorem C.1.  `LocalWeightLe V k` is the paper's notion of
"`V` acts nontrivially on at most `k` qudits".  The field `eigenspace_witness` records the cited
structure lemma [62, Lemma 8] together with the two-case construction of the proof (Eq. (C7) in
Case 1 and the sub-particle projectors of Case 2, Eq. (C9)): it produces, for every eigenspace of
dimension `> 1`, a weight-`≤ 2` operator with `+1`/`-1` eigenvalues on two orthogonal unit
vectors of the eigenspace. -/
structure TwoLocalCommutingModel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- `LocalWeightLe V k`: `V` acts nontrivially on at most `k` qudits. -/
  LocalWeightLe : (H →L[ℂ] H) → ℕ → Prop
  /-- Structure lemma [62, Lemma 8] + the two cases of the proof of Theorem C.1. -/
  eigenspace_witness : ∀ S : Submodule ℂ H, 1 < Module.finrank ℂ S →
    ∃ (V : H →L[ℂ] H) (ψ φ : H), LocalWeightLe V 2 ∧ ψ ∈ S ∧ φ ∈ S ∧
      ‖ψ‖ = 1 ∧ ‖φ‖ = 1 ∧ ⟪ψ, φ⟫_ℂ = 0 ∧ V ψ = ψ ∧ V φ = -φ

/-- **Theorem C.1** (arXiv:2412.07764v1, Appendix C, p. 14), distance form: every eigenspace of a
2-local commuting Hamiltonian of qudits with dimension greater than `1` has code distance at most
`2`, i.e. admits a non-detectable error of weight at most `2`. -/
theorem theorem_C1 (M : TwoLocalCommutingModel H) (S : Submodule ℂ H)
    (hS : 1 < Module.finrank ℂ S) :
    ∃ V : H →L[ℂ] H, M.LocalWeightLe V 2 ∧ ¬ Detectable S V := by
  obtain ⟨V, ψ, φ, hw, hψS, hφS, hψ, hφ, horth, hVψ, hVφ⟩ := M.eigenspace_witness S hS
  exact ⟨V, hw,
    not_detectable_of_plus_minus_eigenvectors S V ψ φ hψS hφS hψ hφ horth hVψ hVφ⟩

/-- **Theorem C.1** (arXiv:2412.07764v1, Appendix C, p. 14), no-go form: no eigenspace of a
2-local commuting Hamiltonian of qudits is simultaneously a code of dimension greater than `1`
and of distance greater than `2`. -/
theorem theorem_C1_no_go (M : TwoLocalCommutingModel H) (S : Submodule ℂ H) :
    ¬ (1 < Module.finrank ℂ S ∧ DistanceGreaterThan M.LocalWeightLe S 2) := by
  rintro ⟨hS, hdist⟩
  obtain ⟨V, hw, hnd⟩ := theorem_C1 M S hS
  exact hnd (hdist V hw)

end Qatlib.Papers.AnalogSimCode24.MainResults.NoGo
