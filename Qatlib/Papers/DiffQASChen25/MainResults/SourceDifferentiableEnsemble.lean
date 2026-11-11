/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option backward.isDefEq.respectTransparency false

/-!
# §V — the differentiable ensemble of DiffQAS-QT

Chen, Liu, Chen, Huang, Chang and Huang, *Differentiable Quantum Architecture
Search in Quantum-Enhanced Neural Network Parameter Generation*, fixed
arXiv:2505.09653v1 (PDF SHA-256
`f4c2826106aa16ea779151a598c5a2357c823e9e162f1138b937c121234b54c6`),
§V p.3–4.

This module formalises the source's differentiable-ensemble construction:

* the candidate design space `Π i, Bᵢ` with `N = Π i |Bᵢ|` (p.3–4);
* for a single VQC/QNN layer, the three design dimensions *Hadamard on/off*
  (2), *entangling layer Ent/Cyc* (2) and *rotation Rx/Ry/Rz* (3), giving
  `2 × 2 × 3 = 12` candidates (p.4);
* Eq. (5), `f_C = Σ_{j=1..N} w_j f_{C_j}` (p.4), and Eq. (6),
  `output = Σ_j w_j VQC_j(Θ_j)` (p.4);
* the structural-weight count `N × M` for `M` stacked ensemble layers (p.4);
* Eq. (7), the shared-parameter specialisation
  `output = Σ_j w_j VQC_j(Θ)` (p.4);
* the automatic-differentiation statement `∇_{w_j} L(f_C)`: the Fréchet
  derivative of the task loss through the ensemble is the derivative of `L` at
  the ensemble output composed with the ensemble linear map (p.4).

Boundary: this is the source's *architecture-search* layer. It records the
ensemble as a weighted sum of abstract candidate outputs `f_{C_j}` and treats
`VQC_j(Θ)` as the candidates' outputs; it does not model a concrete gate set,
the Quantum-Train parameter-generation map, or the training loop. No `sorry`,
no extra axiom, no `unsafe`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiffQASChen25.MainResults.SourceDifferentiableEnsemble

open scoped BigOperators

/-! ## The candidate design space of §V -/

/-- §V p.4: the first design dimension, "whether to apply Hadamard gates at
initialization" (`Bool`: `true` = applied, `false` = not applied). -/
abbrev HadamardChoice := Bool

/-- §V p.4: the second design dimension, "which entangling layer to use (two
choices are provided)": the `Ent` and `Cyc` configurations of Figure 3. -/
abbrev EntangleChoice := Fin 2

/-- §V p.4: the third design dimension, "the type of rotation gates to be
applied (`Rx`, `Ry`, or `Rz`)". -/
abbrev RotationChoice := Fin 3

/-- §V p.4: a single-layer VQC/QNN architecture candidate, an element of the
product `{Hadamard on/off} × {Ent, Cyc} × {Rx, Ry, Rz}`. -/
abbrev SingleLayerCandidate := HadamardChoice × EntangleChoice × RotationChoice

/-- §V p.4: "This results in `2 × 2 × 3 = 12` total architecture candidates for a
single-layer VQC or QNN". -/
theorem singleLayerCandidate_card : Fintype.card SingleLayerCandidate = 12 := by
  simp [SingleLayerCandidate, HadamardChoice, EntangleChoice, RotationChoice]

/-- §V p.3–4: for a circuit `C` built from modular components `S₁, …, Sₙ`, where
`Sᵢ` is instantiated from the candidate set `Bᵢ`, the design space is the
dependent product `Π i, Bᵢ` and "the total design space for `C` includes
`N = |B₁| × |B₂| × ⋯ × |Bₙ|` unique circuit configurations". -/
theorem candidateDesignSpace_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Type*) [∀ i, Fintype (B i)] :
    Fintype.card (∀ i, B i) = ∏ i, Fintype.card (B i) :=
  Fintype.card_pi

/-- §V p.4: "If `M` such layers are employed, the total number of structural
weights increases to `N × M`": one weight per candidate per ensemble layer. -/
theorem stackedWeightCard (N M : ℕ) : Fintype.card (Fin M × Fin N) = M * N := by
  simp [Fintype.card_prod, Nat.mul_comm]

/-- §V p.4, restated for the single-layer case: the DiffQAS block sums over
exactly the 12 candidates of Figure 3. -/
theorem singleLayerCandidate_sum_card :
    (Finset.univ : Finset SingleLayerCandidate).card = 12 := by
  rw [Finset.card_univ, singleLayerCandidate_card]

/-! ## Eq. (5) — the ensemble function -/

section Ensemble

variable {ι : Type*} [Fintype ι] {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- §V Eq. (5), p.4: "we define an ensemble function `f_C` as a weighted
combination over all `N` candidates,
`f_C = Σ_{j=1}^{N} w_j f_{C_j}`", where `w_j` are the learnable structural
weights and `f_{C_j}` the candidate outputs. -/
def ensemble (f : ι → E) (w : ι → ℝ) : E :=
  ∑ j, w j • f j

/-- §V Eq. (5), spelled out: the ensemble is the explicit weighted sum. -/
theorem ensemble_eq_sum (f : ι → E) (w : ι → ℝ) :
    ensemble f w = ∑ j, w j • f j := rfl

/-- §V Eq. (5) as a linear map in the structural weights `w`.  Linearity in `w`
is exactly what makes `∇_{w_j} L(f_C)` accessible to automatic
differentiation: the candidates `f_{C_j}` enter only as fixed vectors. -/
def ensembleLinear (f : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun w := ∑ j, w j • f j
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

/-- The linear map of Eq. (5) is the ensemble function. -/
theorem ensembleLinear_apply (f : ι → E) (w : ι → ℝ) :
    ensembleLinear f w = ensemble f w := rfl

/-- §V Eq. (5): the ensemble is additive in the weights. -/
theorem ensemble_add (f : ι → E) (w w' : ι → ℝ) :
    ensemble f (w + w') = ensemble f w + ensemble f w' := by
  simp only [ensemble, Pi.add_apply, add_smul, Finset.sum_add_distrib]

end Ensemble

/-! ## Eq. (5) under automatic differentiation -/

section Derivative

variable {ι : Type*} [Fintype ι] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- §V p.4: the ensemble map is linear in the structural weights, so its
Fréchet derivative at any weight vector is the ensemble linear map itself. -/
theorem hasFDerivAt_ensemble (f : ι → E) (w : ι → ℝ) :
    HasFDerivAt (fun w => ensemble f w)
      (ensembleLinear f).toContinuousLinearMap w := by
  exact (ensembleLinear f).toContinuousLinearMap.hasFDerivAt (x := w)

/-- §V p.4: "By leveraging automatic differentiation, we compute gradients with
respect to the structural weights `w_j`, i.e. `∇_{w_j} L(f_C)`".  Through the
chain rule the derivative of the task loss `L` at the ensemble output factors
as `DL(f_C) ∘ (ensemble linear map)`. -/
theorem hasFDerivAt_loss_ensemble (f : ι → E) (L : E → ℝ) (w : ι → ℝ)
    (hL : DifferentiableAt ℝ L (ensemble f w)) :
    HasFDerivAt (fun w => L (ensemble f w))
      ((fderiv ℝ L (ensemble f w)).comp
        (ensembleLinear f).toContinuousLinearMap) w := by
  simpa only [Function.comp_def] using
    hL.hasFDerivAt.comp w (hasFDerivAt_ensemble f w)

/-- §V p.4: the structural-weight gradient `∇_w L(f_C)` as a Fréchet derivative:
the derivative of `L` at the ensemble output composed with the ensemble linear
map.  This is the exact object that automatic differentiation computes for the
shared task loss `L(f_C)`. -/
theorem fderiv_loss_ensemble (f : ι → E) (L : E → ℝ) (w : ι → ℝ)
    (hL : DifferentiableAt ℝ L (ensemble f w)) :
    fderiv ℝ (fun w => L (ensemble f w)) w
      = (fderiv ℝ L (ensemble f w)).comp
          (ensembleLinear f).toContinuousLinearMap :=
  (hasFDerivAt_loss_ensemble f L w hL).fderiv

end Derivative

/-! ## Eq. (7) — the shared-parameter ensemble -/

section SharedParameter

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Θ : Type*}

/-- §V Eq. (7), p.4: "a single parameter vector `Θ` is used across all circuit
variants", so the DiffQAS block output "simplifies to
`output = Σ_j w_j VQC_j(Θ)`". -/
def sharedEnsemble (VQC : ι → Θ → E) (w : ι → ℝ) (θ : Θ) : E :=
  ∑ j, w j • VQC j θ

/-- §V Eq. (7) is the shared-parameter specialisation of Eq. (5): at a fixed
parameter value `θ` the candidates are `f_{C_j} = VQC_j(θ)`. -/
theorem sharedEnsemble_eq_ensemble (VQC : ι → Θ → E) (w : ι → ℝ) (θ : Θ) :
    sharedEnsemble VQC w θ = ensemble (fun j => VQC j θ) w := rfl

/-- §V p.4: under the shared-parameter strategy the ensemble output is again
linear in the structural weights, and its structural-weight derivative is the
corresponding ensemble linear map. -/
theorem hasFDerivAt_sharedEnsemble (VQC : ι → Θ → E) (θ : Θ) (w : ι → ℝ) :
    HasFDerivAt (fun w => sharedEnsemble VQC w θ)
      (ensembleLinear (fun j => VQC j θ)).toContinuousLinearMap w := by
  simpa only [sharedEnsemble_eq_ensemble] using
    hasFDerivAt_ensemble (fun j => VQC j θ) w

/-- §V p.4 (Eq. (6) / Eq. (7)): with distinct per-candidate parameter sets
`Θ_j`, the DiffQAS block output is `Σ_j w_j VQC_j(Θ_j)`; this is Eq. (5) with
candidate output `f_{C_j} = VQC_j(Θ_j)`. -/
theorem distinctParameterEnsemble_eq_ensemble (VQC : ι → Θ → E)
    (param : ι → Θ) (w : ι → ℝ) :
    (∑ j, w j • VQC j (param j)) = ensemble (fun j => VQC j (param j)) w := rfl

end SharedParameter

end Qatlib.Papers.DiffQASChen25.MainResults.SourceDifferentiableEnsemble
