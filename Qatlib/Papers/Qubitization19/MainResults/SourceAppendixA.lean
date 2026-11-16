/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
public import Qatlib.Papers.Qubitization19.LCUConsumers.SourceLCU
public import Qatlib.Papers.Qubitization19.MainResults.SourceDefinitions

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SignalPrimitive.LCUConsumers

open Qatlib.Papers.Qubitization19.LCUConsumers

open Qatlib.Papers.Qubitization19.MainResults

namespace Qatlib.Papers.Qubitization19.MainResults

section

/-- Fixed arXiv:1610.06546v3, Eq. (35) (PDF p.17): a normal matrix satisfies
`Ĥ Ĥ† = Ĥ† Ĥ`. (Mathlib's `Matrix.IsNormal` is not available in this
environment, so the defining commutation is stated directly.) -/
def IsNormalMatrix {I : Type*} [Fintype I]
    (H : Matrix I I ℂ) : Prop :=
  H * Hᴴ = Hᴴ * H

/-- Fixed arXiv:1610.06546v3, Eq. (36) (PDF p.17): normal-operator eigenbranch
decomposition. For a normal signal operator `Ĥ` encoded in standard form by `V`
at scale one, and any normalized eigenvector `ψ` with eigenvalue
`λ e^{iθ}` (`0 ≤ λ < 1`), the encoded state `V (|G⟩ ⊗ ψ)` splits into the fiber
component `λ e^{iθ} |G⟩ ⊗ ψ` plus an orthogonal unit vector `φ⊥` with amplitude
`√(1 − λ²)`. This is the exact analogue of the Hermitian eigenbranch of Eq. (4)
for normal operators. The strict bound `λ < 1` is part of the statement: at
`λ = 1` the orthogonal remnant vanishes and cannot be a unit vector, so the
Gram–Schmidt normalization of Eq. (36) degenerates. -/
def NormalEigenbranchDecomposition : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (lam θ : ℝ) (ψ : I → ℂ),
      IsNormalMatrix H → IsBlockEncoding V j₀ H 1 →
      Inner ψ ψ = 1 →
      H *ᵥ ψ = (Complex.exp (Complex.I * (θ : ℂ)) * (lam : ℂ)) • ψ →
      0 ≤ lam → lam < 1 →
      ∃ (φperp : J × I → ℂ),
        V *ᵥ TensorState (Ket j₀) ψ =
          (Complex.exp (Complex.I * (θ : ℂ)) * (lam : ℂ)) •
              TensorState (Ket j₀) ψ +
            ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) • φperp ∧
        Inner φperp φperp = 1 ∧
        Inner (TensorState (Ket j₀) ψ) φperp = 0

/-- Fixed arXiv:1610.06546v3, Eq. (37) (PDF p.17): the phased phase gate
`Ẑ_c = e^{ic} |G⟩⟨G| + e^{−ic} (I − |G⟩⟨G|)` acting on the ancilla fiber
`j₀`, i.e. `e^{ic(2|G⟩⟨G| − I)}`. -/
noncomputable def normalPhaseGate {J I : Type*} [DecidableEq J] [DecidableEq I] (j₀ : J) (c : ℝ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.diagonal (fun p : J × I =>
    if p.1 = j₀ then Complex.exp (Complex.I * (c : ℂ))
    else Complex.exp (-(Complex.I * (c : ℂ))))

/-- Fixed arXiv:1610.06546v3, Eq. (37) (PDF p.17): the phased iterate
`Ŵ^±_φ = Ẑ_{φ−π/2} (2|G⟩⟨G| − I) Û^± Ẑ_{−φ+π/2}` for the `+` sign, with
`Û^+ = V`. The `−` sign is the same expression with `Vᴴ` (see
`normalIterateDagger`). -/
noncomputable def normalIterate {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (φ : ℝ) : Matrix (J × I) (J × I) ℂ :=
  normalPhaseGate j₀ (φ - Real.pi / 2) * FiberReflection j₀ * V *
    normalPhaseGate j₀ (-φ + Real.pi / 2)

/-- Fixed arXiv:1610.06546v3, Eq. (37) (PDF p.17): the `−` phased iterate
`Ŵ^-_φ`, using `Û^- = Vᴴ`. -/
noncomputable def normalIterateDagger {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (φ : ℝ) : Matrix (J × I) (J × I) ℂ :=
  normalPhaseGate j₀ (φ - Real.pi / 2) * FiberReflection j₀ * Vᴴ *
    normalPhaseGate j₀ (-φ + Real.pi / 2)

/-- Fixed arXiv:1610.06546v3, Eq. (38) (PDF p.17): the Gram–Schmidt state
`|G⊥±_λ⟩ = (λ e^{±iθ_λ} − Ŵ_{π/2,±})|G_λ⟩ / √(1 − λ²)` associated with the
`+` iterate. -/
noncomputable def normalGperpPlus {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (lam θ : ℝ) (G : J × I → ℂ) : J × I → ℂ :=
  (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ))⁻¹ •
    ((Complex.exp (Complex.I * (θ : ℂ)) * (lam : ℂ)) • G -
      normalIterate V j₀ (Real.pi / 2) *ᵥ G)

/-- Fixed arXiv:1610.06546v3, Eq. (40) (PDF p.17): the 2×2 representation
`[[λ e^{iθ_λ}, −i e^{−iφ}√(1−λ²)], [−i e^{iφ}√(1−λ²), λ e^{−iθ_λ}]]` of the
`+` phased iterate in the Gram–Schmidt basis of Eq. (38). -/
noncomputable def normalIterateBlock (lam φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(lam : ℂ) * Complex.exp (Complex.I * (θ : ℂ)),
     -Complex.I * Complex.exp (-(Complex.I * (φ : ℂ))) *
       ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ);
     -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
       ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ),
     (lam : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))]

/-- Fixed arXiv:1610.06546v3, Eq. (40) (PDF p.17): the phased iterate has the
displayed 2×2 matrix elements between the states of Eq. (38), for an
eigenbranch of a normal operator. The matrix elements are stated through the
inner product; the `+` iterate maps the `+` Gram–Schmidt basis to the `−` one,
so `GperpPlus` and `GperpMinus` are both quantified. -/
def NormalPhasedIterateForm : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (lam φ θ : ℝ) (G : J × I → ℂ),
      IsNormalMatrix H → IsBlockEncoding V j₀ H 1 →
      Inner G G = 1 →
      Inner G (V *ᵥ G) = Complex.exp (Complex.I * (θ : ℂ)) * (lam : ℂ) →
      Inner G (Vᴴ *ᵥ G) = Complex.exp (-(Complex.I * (θ : ℂ))) * (lam : ℂ) →
      0 ≤ lam → lam < 1 →
      ∃ (GperpPlus GperpMinus : J × I → ℂ),
        Inner GperpPlus GperpPlus = 1 ∧
        Inner GperpMinus GperpMinus = 1 ∧
        Inner G GperpPlus = 0 ∧ Inner G GperpMinus = 0 ∧
        Inner G (normalIterate V j₀ φ *ᵥ G) =
          (lam : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∧
        Inner GperpMinus (normalIterate V j₀ φ *ᵥ GperpPlus) =
          (lam : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ))) ∧
        Inner GperpPlus (normalIterate V j₀ φ *ᵥ G) =
          -Complex.I * Complex.exp (-(Complex.I * (φ : ℂ))) *
            ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) ∧
        Inner G (normalIterate V j₀ φ *ᵥ GperpMinus) =
          -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
            ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)

/-- Fixed arXiv:1610.06546v3, Appendix A.1 (PDF p.18, Eq. (42) and its
discussion): the Hermitian specialization of normal qubitization. For a
Hermitian `Ĥ` (`θ_λ = 0`), the frozen walk `QubitizationWalk` of the paper's
Lemma 8 has projected eigenvalue `2x² − 1` on an eigenbranch `Ĥψ = xψ`, which is
the squared iterate's diagonal entry `λ = 2x² − 1` of Eq. (40). This is exactly
the frozen theorem `qubitization_amplifies_fiber` of
`PhaseEstimation/Qubitization/Qubitization.lean:316`. -/
theorem appendixA_hermitian_amplification {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (A : Matrix I I ℂ) (hV : IsBlockEncoding V j₀ A 1) (hA : Aᴴ = A)
    (ψ : QState I) (x : ℝ) (hx : A *ᵥ ψ = ((x : ℝ) : ℂ) • ψ) :
    FiberProjector j₀ *ᵥ
        (Qatlib.Concepts.AmplitudeCore.InvFreePhase.QubitizationWalk V j₀ *ᵥ
          TensorState (Ket j₀) ψ) =
      (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • TensorState (Ket j₀) ψ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.qubitization_amplifies_fiber
    V j₀ A hV hA ψ x hx

/-- Local alias for the frozen conjugate-linearity rule of `Inner` on
`QState` (`PhaseEstimation.inner_smul_left`); the same root name is used by
Mathlib's abstract inner-product lemmas. -/
theorem appInner_smul_left {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (ψ φ : QState I) :
    Inner (c • ψ) φ = (starRingEnd ℂ) c * Inner ψ φ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left c ψ φ

/-- Local alias for the frozen linearity rule of `Inner` on `QState`
(`PhaseEstimation.inner_smul_right`). -/
theorem appInner_smul_right {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (ψ φ : QState I) :
    Inner ψ (c • φ) = c * Inner ψ φ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right c ψ φ

/-- Local alias for the frozen left-subtraction rule of `Inner` on `QState`
(`PhaseEstimation.inner_sub_left`). -/
theorem appInner_sub_left {I : Type*} [Fintype I] [DecidableEq I]
    (ψ φ χ : QState I) :
    Inner (ψ - φ) χ = Inner ψ χ - Inner φ χ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left ψ φ χ

/-- Local alias for the frozen right-subtraction rule of `Inner` on `QState`
(`PhaseEstimation.inner_sub_right`). -/
theorem appInner_sub_right {I : Type*} [Fintype I] [DecidableEq I]
    (ψ φ χ : QState I) :
    Inner ψ (φ - χ) = Inner ψ φ - Inner ψ χ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right ψ φ χ

/-- Local alias for the frozen self-adjointness of the fiber projector inside
`Inner` (`PhaseEstimation.inner_fiberProjector_left`), used in the proof of
Eq. (36). -/
theorem appInner_fiberProjector_left {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (χ φ : QState (J × I)) :
    Inner (FiberProjector j₀ *ᵥ χ) φ = Inner χ (FiberProjector j₀ *ᵥ φ) :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_fiberProjector_left j₀ χ φ

/-- Fixed arXiv:1610.06546v3, Eq. (36) (PDF p.17): normal-operator eigenbranch
decomposition.

Paper version: arXiv:1610.06546v3. Source: Appendix A, Eq. (36), PDF p.17.
Key proof steps in the paper: (i) polar-decompose the normal `Ĥ` as
`Ĥ = Ĥ_U Ĥ_H` with commuting unitary and positive-semidefinite factors
(Eq. (35)), so eigenvalues are `λ e^{iθ_λ}` with `λ ≥ 0`;
(ii) the standard-form corner `⟨G|⊗I V |G⟩⊗I = Ĥ` gives
`V|G⟩|λ⟩ = λ e^{iθ_λ}|G⟩|λ⟩ + √(1 − |λ|²)|G⊥_λ⟩` (Eq. (36));
(iii) `|G⊥_λ⟩` is normalized because `V` is unitary and the fiber component has
norm `λ²`.

Proof: write `c = λ e^{iθ_λ}` and `g = |G⟩ ⊗ ψ`. The frozen fiber calculus gives
`Π (V g) = c g` (`fiberProjector_mul_mul_corner` plus
`fiberEmbed_mulVec_tensorState_ket`), hence `⟨g|V g⟩ = c` and `⟨V g|g⟩ = c̄` by
`inner_fiberProjector_left`, while unitarity gives `⟨V g|V g⟩ = ⟨g|g⟩ = 1`
(`inner_applyGate`). The state `φ = V g − c g` then satisfies `⟨g|φ⟩ = 0` and
`⟨φ|φ⟩ = 1 − λ²`, so `φ⊥ = (√(1−λ²))⁻¹ φ` is the required normalized
orthogonal vector; `λ < 1` makes the inverse well defined. -/
theorem appendixA_normal_eigenbranch : NormalEigenbranchDecomposition := by
  intro J I _ _ _ _ H V j₀ lam θ ψ _hH hV hψ hψeig hlam0 hlam1
  obtain ⟨hVun, -, hcorner⟩ := hV
  have hcornH : BlockCorner V j₀ = H := by simpa using hcorner
  set c : ℂ := Complex.exp (Complex.I * (θ : ℂ)) * (lam : ℂ) with hcdef
  set g : QState (J × I) := TensorState (Ket j₀) ψ with hgdef
  set phi : QState (J × I) := V *ᵥ g - c • g with hφdef
  -- `ψ` is normalized and so is the fiber state `g`.
  have hψn : Normalized ψ := (normalized_iff_inner_self ψ).mpr hψ
  have hgn : Normalized g := by
    rw [hgdef]
    exact normalized_tensorState (normalized_ket j₀) hψn
  have hgg : Inner g g = 1 := (normalized_iff_inner_self g).mp hgn
  -- The fiber projector fixes `g`.
  have hPfix : FiberProjector j₀ *ᵥ g = g := by
    rw [hgdef]
    exact fiberProjector_mulVec_tensorState_ket j₀ ψ
  -- `c` has norm `lam` and `c * conj c = lam²`.
  have hc_norm : ‖c‖ = lam := by
    rw [hcdef, Complex.norm_mul]
    rw [show ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 from by
      rw [mul_comm (Complex.I) ((θ : ℂ))]
      exact Complex.norm_exp_ofReal_mul_I θ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0, one_mul]
  have hc_normSq : Complex.normSq c = lam ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hc_norm]
  have hcc : c * (starRingEnd ℂ) c = ((lam ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, hc_normSq]
  have hcc_comm : (starRingEnd ℂ) c * c = ((lam ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, hcc]
  -- `V` maps the fiber state `g` to `c g` in the fiber and `phi` outside it.
  have hPVg : FiberProjector j₀ *ᵥ (V *ᵥ g) = c • g := by
    rw [show V *ᵥ g = V *ᵥ (FiberProjector j₀ *ᵥ g) by rw [hPfix]]
    rw [show FiberProjector j₀ *ᵥ (V *ᵥ (FiberProjector j₀ *ᵥ g))
          = (FiberProjector j₀ * (V * FiberProjector j₀)) *ᵥ g by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    rw [fiberProjector_mul_mul_corner, hcornH, hgdef,
      fiberEmbed_mulVec_tensorState_ket, hψeig, tensorState_smul_ket_right,
      ← hgdef]
  have hVg : V *ᵥ g = c • g + phi := by
    rw [hφdef]
    abel
  -- Inner products of `g`, `V g` and `phi`.
  have hVgg : Inner (V *ᵥ g) (V *ᵥ g) = 1 := by
    have h := inner_applyGate hVun g g
    simpa [ApplyGate, hgg] using h
  have hVg_g : Inner (V *ᵥ g) g = (starRingEnd ℂ) c := by
    have h := appInner_fiberProjector_left j₀ (V *ᵥ g) g
    rw [hPVg, hPfix] at h
    rw [appInner_smul_left, hgg, mul_one] at h
    exact h.symm
  have hg_Vg : Inner g (V *ᵥ g) = c := by
    have h := appInner_fiberProjector_left j₀ g (V *ᵥ g)
    rw [hPfix, hPVg] at h
    rw [appInner_smul_right, hgg, mul_one] at h
    exact h
  have hφφ : Inner phi phi = ((1 - lam ^ 2 : ℝ) : ℂ) := by
    rw [hφdef]
    simp only [appInner_sub_left, appInner_sub_right, appInner_smul_right,
      appInner_smul_left]
    rw [hVgg, hVg_g, hg_Vg, hgg]
    simp only [mul_one]
    rw [sub_self, mul_zero, sub_zero, hcc_comm]
    push_cast
    ring
  have hgφ : Inner g phi = 0 := by
    rw [hφdef, appInner_sub_right, hg_Vg, appInner_smul_right, hgg, mul_one,
      sub_self]
  -- The Gram–Schmidt normalization constant.
  have h1m : 0 < 1 - lam := by linarith
  have h1p : 0 < 1 + lam := by linarith
  have hpos : 0 < 1 - lam ^ 2 := by nlinarith [mul_pos h1m h1p]
  have hy : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.mpr hpos
  have hy2c : (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) *
      ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) = ((1 - lam ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hpos)]
  have hyne : ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hy.ne'
  have hstar_inv : (starRingEnd ℂ) (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ))⁻¹
      = (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.starRingEnd_ofReal,
      Complex.ofReal_inv]
  refine ⟨(((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ))⁻¹ • phi, ?_, ?_, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hyne, one_smul, hVg]
  · rw [appInner_smul_left, appInner_smul_right, hφφ, hstar_inv, ← hy2c,
      ← mul_assoc, ← mul_inv]
    rw [inv_mul_cancel₀ (mul_ne_zero hyne hyne)]
  · rw [appInner_smul_right, hgφ, mul_zero]

end

end Qatlib.Papers.Qubitization19.MainResults
