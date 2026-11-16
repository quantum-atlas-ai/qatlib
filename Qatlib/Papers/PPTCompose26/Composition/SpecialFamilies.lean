/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Solution
public import Qatlib.Foundations.PPTMatrix.OperatorCones.TensorMaps

@[expose] public section


/-!
# Special PPT Families, Conic Closures, and Trace-Replacement / Pinching Channels

This module formalizes structural strengthenings of the PPT composition bound:

1. **Two-Sided Ideal Closure of Entanglement-Breaking Maps**:
   - `IsEntanglementBreaking.comp_isCompletelyPositive`: Pre-composing an entanglement-breaking
     map with any completely positive map preserves the entanglement-breaking property.
   - Combined with `IsEntanglementBreaking.comp_of_isCompletelyPositive` (`AtLeast.lean`),
     entanglement-breaking maps form a two-sided ideal in the semigroup of completely positive maps.
   - `ebIndex_eq_one_of_isEntanglementBreaking` and `ebIndex_eq_one_iff`: A linear map has
     entanglement-breaking index `1` if and only if it is entanglement breaking.

2. **Diagonal Pinching / Diagonal Schur Multipliers (`ebIndex = 1`)**:
   - `diagPinchMap w`: The weighted diagonal pinching (diagonal Hadamard–Schur multiplier) map
     `Δ_w(X)_{a,b} = w_a X_{a,a}` for `a = b` and `0` for `a ≠ b`.
   - `choi_diagPinchMap_eq_sum_kronecker`: The Choi matrix of `diagPinchMap w` decomposes
     explicitly as `∑ k : Fin d, ((w k : ℂ) • |k⟩⟨k|) ⊗ |k⟩⟨k|`.
   - `isEntanglementBreaking_diagPinchMap`, `isPPTMap_diagPinchMap`, and
     `ebIndex_diagPinchMap_eq_one`: For any nonnegative weights `w : Fin d → ℝ` (`∀ k, 0 ≤ w k`),
     `diagPinchMap w` is PPT and entanglement breaking in a single step (`ebIndex = 1`),
     sharpening the general `2(d-1)` bound to `1` on the entire diagonal Schur-multiplier cone.

3. **Linearity and Functoriality of `refMap` and Transposition**:
   - `refMap_add`, `refMap_add_eq`, `refMap_smul`, `refMap_smul_eq`: Linearity of reference system extension.
   - `transposeMap_comp_add`, `transposeMap_comp_smul`: Linearity and scalar multiplication behavior of transposition.

4. **Conic and Convex Closures of CP, CC, PPT, Separable, and EB Cones**:
   - Conic addition and scaling: `IsCompletelyPositive.add`, `smul_of_nonneg`; `IsCompletelyCopositive.add`, `smul_of_nonneg`;
     `IsPPTMap.add`, `smul_of_nonneg`; `IsSeparable.smul_of_nonneg`; `IsEntanglementBreaking.add`, `smul_of_nonneg`.
   - Explicit convex combinations: `IsCompletelyPositive.convex_combination`, `IsCompletelyCopositive.convex_combination`,
     `IsPPTMap.convex_combination`, `IsEntanglementBreaking.convex_combination`.

5. **Trace-Replacement and Rank-1 State Preparation Channels (`ebIndex = 1`)**:
   - `traceReplaceMap σ`: The replacement channel `X ↦ Tr(X) • σ`.
   - `partialTraceSys`: Bipartite subsystem partial trace.
   - `choi_traceReplaceMap`: Explicit Choi matrix `1 ⊗ₖ σ`.
   - `isEntanglementBreaking_traceReplaceMap`, `isPPTMap_traceReplaceMap_of_posSemidef`,
     `ebIndex_traceReplaceMap_of_posSemidef_eq_one`.
   - Specialization to pure state preparation: `ebIndex_traceReplaceMap_pureState_eq_one`.

6. **Depolarizing Convex Mixtures and Arbitrary-Basis Pinching Maps**:
   - `depolarizeMix p Φ σ`: Convex combination `(1 - p) • Φ + p • traceReplaceMap σ`.
   - `isPPTMap_depolarizeMix`, `isPPTMap_depolarizeMix_one`.
   - `isEntanglementBreaking_depolarizeMix`, `isEntanglementBreaking_depolarizeMix_one`.
   - `basisPinchMap U V w`: General measurement-and-prepare pinching channel.
   - `isEntanglementBreaking_basisPinchMap`, `ebIndex_basisPinchMap_eq_one`.

7. **Measure-and-Prepare Channels, Transpose-Depolarizing Family, Finite-Sum Conic Closures, and Surrounded Chains**:
   - Finite sums: `IsCompletelyPositive.sum`, `IsPPTMap.sum`, `IsEntanglementBreaking.sum`, etc.
   - `measurePrepareMap K σ`: General Kraus measurement and state preparation channel.
   - `transposeDepolarizeMix p σ`: Transpose-depolarizing mixture.
   - `compose_ppt_maps_surrounded_entanglementBreaking`: Composition of PPT maps surrounded by pre/post CP channels.

8. **Schmidt-Number Conic/Convex Closure, Reference-Limited Separability, and Heterogeneous Interleaved PPT-CP Composition**:
   - `isSeparable_iff_hasSchmidtNumberLE_one`: Equivalence between bipartite separability and Schmidt number at most 1.
   - `HasSchmidtNumberLE.smul_of_nonneg`, `HasSchmidtNumberLE.convex_combination`, `HasSchmidtNumberLE.sum_smul_of_nonneg`:
     Conic scaling, binary convex/conic combinations, and nonnegative-weighted finite sums preserve Schmidt-number upper bounds.
   - `hasSchmidtNumberLE_refMap_comp_ppt_maps` & `schmidtNumber_refMap_comp_ppt_maps_le`:
     Quantitative intermediate $2j$-step Schmidt-number descent bound $\max(\min(k, d) - j, 1)$.
   - `isSeparable_refMap_comp_ppt_maps_of_hasSchmidtNumberLE`:
     Separability collapse when initial Schmidt number $s \le j + 1$.
   - `isSeparable_refMap_comp_ppt_maps_of_ref_le`:
     Reference-dimension-limited composition bound: only $2(k - 1)$ PPT maps suffice on $M_d(\mathbb{C})$
     for any $k$-dimensional reference ($k \ge 1$), collapsing before the full $2(d - 1)$ Choi bound whenever $k < d$.
   - `compose_heterogeneous_ppt_interleaved_entanglementBreaking` & `compose_heterogeneous_ppt_interleaved_post_entanglementBreaking`:
     Entanglement breaking for $2(d - 1)$ heterogeneous interleaved PPT-CP pairs and optional post-processing CP channel.

9. **Peres–Horodecki Criterion, CP Chain Ideal Absorption, and All-Power Monotonicity**:
   - `partialTransposeRef_kronecker`, `partialTransposeRef_sum`, `IsSeparable.partialTransposeRef`,
     `IsSeparable.posSemidef_partialTransposeRef`: Peres–Horodecki criterion for bipartite separability.
   - `IsEntanglementBreaking.isCompletelyCopositive`, `IsEntanglementBreaking.isPPTMap`:
     Universal cone inclusion showing every entanglement-breaking map is PPT.
   - `isEntanglementBreaking_compList_of_mem`, `isEntanglementBreaking_ofFn_of_exists`,
     `ebIndex_compList_of_mem_eq_one`, `ebIndex_ofFn_of_exists_eq_one`: Arbitrary-length CP chain ideal absorption.
   - `IsCompletelyPositive.pow`, `IsPPTMap.pow`, `IsEntanglementBreaking.pow_of_le`,
     `isEntanglementBreaking_pow_of_le`, `ebIndex_pow_of_le_eq_one`: Power closure and universal
     all-power entanglement-breaking threshold for all exponents $M \ge 2(d-1)$.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators

noncomputable section

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n p q : Type*}

/-! ## Section 1: Two-Sided Ideal Closure and `ebIndex = 1` Characterization -/

/-- Pre-composing an entanglement-breaking map with a completely positive map yields an
entanglement-breaking map. Together with `IsEntanglementBreaking.comp_of_isCompletelyPositive`,
this shows that entanglement-breaking maps form a two-sided ideal among completely positive maps. -/
theorem IsEntanglementBreaking.comp_isCompletelyPositive
    {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ} {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΨ : IsEntanglementBreaking Ψ) (hΦ : IsCompletelyPositive Φ) :
    IsEntanglementBreaking (Ψ ∘ₗ Φ) := by
  refine ⟨hΨ.1.comp hΦ, fun k X hX => ?_⟩
  rw [refMap_comp, LinearMap.comp_apply]
  exact hΨ.2 k (refMap (Fin k) Φ X) (hΦ k X hX)

/-- Sandwiching an entanglement-breaking map between two arbitrary completely positive maps
preserves the entanglement-breaking property. -/
theorem IsEntanglementBreaking.sandwich_isCompletelyPositive [Finite p]
    {Φ₁ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    {Φ₂ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ}
    (hΦ₁ : IsCompletelyPositive Φ₁)
    (hΨ : IsEntanglementBreaking Ψ)
    (hΦ₂ : IsCompletelyPositive Φ₂) :
    IsEntanglementBreaking (Φ₂ ∘ₗ Ψ ∘ₗ Φ₁) := by
  simpa only [LinearMap.comp_assoc] using IsEntanglementBreaking.comp_isCompletelyPositive
    (IsEntanglementBreaking.comp_of_isCompletelyPositive hΨ hΦ₂) hΦ₁

/-- Every entanglement-breaking map has entanglement-breaking index `1`. -/
theorem ebIndex_eq_one_of_isEntanglementBreaking
    {T : Module.End ℂ (Matrix n n ℂ)} (hT : IsEntanglementBreaking T) :
    ebIndex T = 1 := by
  apply le_antisymm
  · unfold ebIndex
    refine iInf_le_of_le 1 (iInf_le_of_le le_rfl (iInf_le_of_le ?_ ?_))
    · rw [pow_one]
      exact hT
    · simp
  · unfold ebIndex
    refine le_iInf fun m => le_iInf fun hm => le_iInf fun _ => ?_
    exact_mod_cast hm

/-- A map on `Matrix n n ℂ` has entanglement-breaking index `1` if and only if it is
entanglement breaking. -/
theorem ebIndex_eq_one_iff (T : Module.End ℂ (Matrix n n ℂ)) :
    ebIndex T = 1 ↔ IsEntanglementBreaking T := by
  constructor
  · intro h
    by_contra hnot
    have hge2 : (2 : ℕ∞) ≤ ebIndex T := by
      unfold ebIndex
      refine le_iInf fun m => le_iInf fun hm => le_iInf fun hm_eb => ?_
      have hm_ne_one : m ≠ 1 := by
        intro hm1
        subst hm1
        rw [pow_one] at hm_eb
        exact hnot hm_eb
      have hm2 : 2 ≤ m := by omega
      exact_mod_cast hm2
    rw [h] at hge2
    exact absurd hge2 (by decide)
  · exact ebIndex_eq_one_of_isEntanglementBreaking

/-! ## Section 2: Weighted Diagonal Pinching Maps (`ebIndex = 1`) -/

/-- Weighted diagonal pinching map `Δ_w(X)_{a,b} = if a = b then w_a * X_{a,a} else 0`,
which coincides with the diagonal Hadamard–Schur multiplier `X ↦ diag(w) ⊙ X`. -/
def diagPinchMap {d : ℕ} (w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := Matrix.of fun a b => if a = b then (w a : ℂ) * X a a else 0
  map_add' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- Establishes `diagPinchMap_apply`: `diagPinchMap w X a b = if a = b then (w a : ℂ) * X a a else 0`, for the stated parameters. -/
@[simp]
theorem diagPinchMap_apply {d : ℕ} (w : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    diagPinchMap w X a b = if a = b then (w a : ℂ) * X a a else 0 :=
  rfl

/-- Diagonal pinching is invariant under post-composition with matrix transposition. -/
theorem transposeMap_comp_diagPinchMap {d : ℕ} (w : Fin d → ℝ) :
    transposeMap (Fin d) ∘ₗ diagPinchMap w = diagPinchMap w := by
  refine LinearMap.ext fun X => ?_
  ext a b
  simp only [LinearMap.comp_apply, transposeMap_apply, Matrix.transpose_apply, diagPinchMap_apply]
  by_cases h : a = b
  · subst h
    simp
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

/-- Explicit rank-1 product decomposition of the Choi matrix of `diagPinchMap w`. -/
theorem choi_diagPinchMap_eq_sum_kronecker {d : ℕ} (w : Fin d → ℝ) :
    refMap (Fin d) (diagPinchMap w) (pureState (omegaVec d)) =
      ∑ k : Fin d, ((w k : ℂ) • pureState (Pi.single k (1 : ℂ))) ⊗ₖ
        pureState (Pi.single k (1 : ℂ)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [refMap_apply, diagPinchMap_apply, block_apply, pureState,
    Matrix.vecMulVec_apply, omegaVec, Pi.star_apply, RCLike.star_def,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b <;> by_cases hia : i = a <;> by_cases hja : j = a <;>
      simp [hab, hia, hja, Pi.single_apply, eq_comm]
  · intro k _ hka
    have hak : a ≠ k := Ne.symm hka
    simp [Pi.single_eq_of_ne hak]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- For nonnegative weights `w`, the Choi matrix of `diagPinchMap w` is separable. -/
theorem isSeparable_choi_diagPinchMap {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsSeparable (refMap (Fin d) (diagPinchMap w) (pureState (omegaVec d))) := by
  rw [choi_diagPinchMap_eq_sum_kronecker]
  refine isSeparable_sum_kronecker _ _ (fun k => ?_) (fun k => ?_)
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr (hw k))
  · exact Matrix.posSemidef_vecMulVec_self_star _

/-- **1-Step Entanglement Breaking for Nonnegative Diagonal Pinching Maps:**
For any nonnegative weights `w : Fin d → ℝ`, `diagPinchMap w` is entanglement breaking. -/
theorem isEntanglementBreaking_diagPinchMap {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsEntanglementBreaking (diagPinchMap w) :=
  (isEntanglementBreaking_iff_choi (diagPinchMap w)).mpr (isSeparable_choi_diagPinchMap w hw)

/-- For nonnegative weights `w : Fin d → ℝ`, `diagPinchMap w` is a PPT map. -/
theorem isPPTMap_diagPinchMap {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsPPTMap (diagPinchMap w) := by
  have hEB := isEntanglementBreaking_diagPinchMap w hw
  refine ⟨hEB.1, ?_⟩
  unfold IsCompletelyCopositive
  rw [transposeMap_comp_diagPinchMap]
  exact hEB.1

/-- For nonnegative weights `w : Fin d → ℝ`, `diagPinchMap w` is PPT and has
entanglement-breaking index equal to `1`. -/
theorem ebIndex_diagPinchMap_eq_one {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsPPTMap (diagPinchMap w) ∧ ebIndex (diagPinchMap w) = 1 :=
  ⟨isPPTMap_diagPinchMap w hw,
    ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_diagPinchMap w hw)⟩

/-! ## Section 3: Basic Linearity and Functoriality of `refMap` and Transposition -/

/-- `refMap κ` preserves addition of linear maps on any input matrix. -/
theorem refMap_add (κ : Type*) (Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (Φ₁ + Φ₂) X = refMap κ Φ₁ X + refMap κ Φ₂ X := by
  ext x y
  rfl

/-- `refMap κ` preserves addition of linear maps as linear operators. -/
@[simp]
theorem refMap_add_eq (κ : Type*) (Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    refMap κ (Φ₁ + Φ₂) = refMap κ Φ₁ + refMap κ Φ₂ := by
  refine LinearMap.ext fun X => ?_
  ext x y
  rfl

/-- `refMap κ` preserves complex scalar multiplication on any input matrix. -/
theorem refMap_smul (κ : Type*) (c : ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (c • Φ) X = c • refMap κ Φ X := by
  ext x y
  rfl

/-- `refMap κ` preserves complex scalar multiplication as linear operators. -/
@[simp]
theorem refMap_smul_eq (κ : Type*) (c : ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    refMap κ (c • Φ) = c • refMap κ Φ := by
  refine LinearMap.ext fun X => ?_
  ext x y
  rfl

/-- Transposition distributes over addition of linear maps. -/
theorem transposeMap_comp_add (Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    transposeMap p ∘ₗ (Φ₁ + Φ₂) = (transposeMap p ∘ₗ Φ₁) + (transposeMap p ∘ₗ Φ₂) := by
  refine LinearMap.ext fun X => ?_
  ext a b
  rfl

/-- Transposition commutes with complex scalar multiplication of linear maps. -/
theorem transposeMap_comp_smul (c : ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    transposeMap p ∘ₗ (c • Φ) = c • (transposeMap p ∘ₗ Φ) := by
  refine LinearMap.ext fun X => ?_
  ext a b
  rfl

/-! ## Section 4: Conic and Convex Closure Properties -/

/-- Completely positive maps are closed under addition. -/
theorem IsCompletelyPositive.add {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsCompletelyPositive Φ₁) (hΦ₂ : IsCompletelyPositive Φ₂) :
    IsCompletelyPositive (Φ₁ + Φ₂) := by
  intro k X hX
  rw [refMap_add]
  exact (hΦ₁ k X hX).add (hΦ₂ k X hX)

/-- Scaling a completely positive map by a nonnegative complex scalar preserves complete positivity. -/
theorem IsCompletelyPositive.smul_c_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsCompletelyPositive Φ) (c : ℂ) (hc : 0 ≤ c) :
    IsCompletelyPositive (c • Φ) := by
  intro k X hX
  rw [refMap_smul]
  exact (hΦ k X hX).smul hc

/-- Completely positive maps are closed under nonnegative real scaling. -/
theorem IsCompletelyPositive.smul_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsCompletelyPositive Φ) (c : ℝ) (hc : 0 ≤ c) :
    IsCompletelyPositive ((c : ℂ) • Φ) :=
  IsCompletelyPositive.smul_c_of_nonneg hΦ (c : ℂ) (Complex.zero_le_real.mpr hc)

/-- Completely copositive maps are closed under addition. -/
theorem IsCompletelyCopositive.add {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsCompletelyCopositive Φ₁) (hΦ₂ : IsCompletelyCopositive Φ₂) :
    IsCompletelyCopositive (Φ₁ + Φ₂) := by
  unfold IsCompletelyCopositive at hΦ₁ hΦ₂ ⊢
  rw [transposeMap_comp_add]
  exact IsCompletelyPositive.add hΦ₁ hΦ₂

/-- Scaling a completely copositive map by a nonnegative complex scalar preserves complete copositivity. -/
theorem IsCompletelyCopositive.smul_c_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsCompletelyCopositive Φ) (c : ℂ) (hc : 0 ≤ c) :
    IsCompletelyCopositive (c • Φ) := by
  unfold IsCompletelyCopositive at hΦ ⊢
  rw [transposeMap_comp_smul]
  exact IsCompletelyPositive.smul_c_of_nonneg hΦ c hc

/-- Completely copositive maps are closed under nonnegative real scaling. -/
theorem IsCompletelyCopositive.smul_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsCompletelyCopositive Φ) (c : ℝ) (hc : 0 ≤ c) :
    IsCompletelyCopositive ((c : ℂ) • Φ) :=
  IsCompletelyCopositive.smul_c_of_nonneg hΦ (c : ℂ) (Complex.zero_le_real.mpr hc)

/-- PPT maps are closed under addition. -/
theorem IsPPTMap.add {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsPPTMap Φ₁) (hΦ₂ : IsPPTMap Φ₂) :
    IsPPTMap (Φ₁ + Φ₂) :=
  ⟨IsCompletelyPositive.add hΦ₁.1 hΦ₂.1, IsCompletelyCopositive.add hΦ₁.2 hΦ₂.2⟩

/-- PPT maps are closed under nonnegative complex scalar multiplication. -/
theorem IsPPTMap.smul_c_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsPPTMap Φ) (c : ℂ) (hc : 0 ≤ c) :
    IsPPTMap (c • Φ) :=
  ⟨IsCompletelyPositive.smul_c_of_nonneg hΦ.1 c hc,
    IsCompletelyCopositive.smul_c_of_nonneg hΦ.2 c hc⟩

/-- PPT maps are closed under nonnegative real scalar multiplication. -/
theorem IsPPTMap.smul_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsPPTMap Φ) (c : ℝ) (hc : 0 ≤ c) :
    IsPPTMap ((c : ℂ) • Φ) :=
  ⟨IsCompletelyPositive.smul_of_nonneg hΦ.1 c hc,
    IsCompletelyCopositive.smul_of_nonneg hΦ.2 c hc⟩

/-- Scaling a separable operator by a nonnegative complex scalar preserves separability. -/
theorem IsSeparable.smul_c_of_nonneg {κ n : Type*}
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : IsSeparable X)
    (c : ℂ) (hc : 0 ≤ c) : IsSeparable (c • X) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := hX
  refine ⟨N, fun j => c • A j, B, fun j => (hA j).smul hc, hB, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Matrix.smul_kronecker c (A j) (B j)).symm

/-- Scaling a separable operator by a nonnegative real scalar preserves separability.
This complements `IsSeparable.add` to establish that separable operators form a convex cone. -/
theorem IsSeparable.smul_of_nonneg {κ n : Type*}
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : IsSeparable X)
    (c : ℝ) (hc : 0 ≤ c) : IsSeparable ((c : ℂ) • X) :=
  IsSeparable.smul_c_of_nonneg hX (c : ℂ) (Complex.zero_le_real.mpr hc)

/-- Entanglement-breaking maps are closed under addition. -/
theorem IsEntanglementBreaking.add {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsEntanglementBreaking Φ₁) (hΦ₂ : IsEntanglementBreaking Φ₂) :
    IsEntanglementBreaking (Φ₁ + Φ₂) := by
  refine ⟨IsCompletelyPositive.add hΦ₁.1 hΦ₂.1, fun k X hX => ?_⟩
  rw [refMap_add]
  exact (hΦ₁.2 k X hX).add (hΦ₂.2 k X hX)

/-- Entanglement-breaking maps are closed under nonnegative complex scalar multiplication. -/
theorem IsEntanglementBreaking.smul_c_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsEntanglementBreaking Φ) (c : ℂ) (hc : 0 ≤ c) :
    IsEntanglementBreaking (c • Φ) := by
  refine ⟨IsCompletelyPositive.smul_c_of_nonneg hΦ.1 c hc, fun k X hX => ?_⟩
  rw [refMap_smul]
  exact IsSeparable.smul_c_of_nonneg (hΦ.2 k X hX) c hc

/-- Entanglement-breaking maps are closed under nonnegative real scalar multiplication. -/
theorem IsEntanglementBreaking.smul_of_nonneg {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsEntanglementBreaking Φ) (c : ℝ) (hc : 0 ≤ c) :
    IsEntanglementBreaking ((c : ℂ) • Φ) :=
  IsEntanglementBreaking.smul_c_of_nonneg hΦ (c : ℂ) (Complex.zero_le_real.mpr hc)

/-- Convex combinations of completely positive maps are completely positive. -/
theorem IsCompletelyPositive.convex_combination {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsCompletelyPositive Φ₁) (hΦ₂ : IsCompletelyPositive Φ₂)
    (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) :
    IsCompletelyPositive ((p₁ : ℂ) • Φ₁ + (p₂ : ℂ) • Φ₂) :=
  IsCompletelyPositive.add (IsCompletelyPositive.smul_of_nonneg hΦ₁ p₁ hp₁)
    (IsCompletelyPositive.smul_of_nonneg hΦ₂ p₂ hp₂)

/-- Convex combinations of completely copositive maps are completely copositive. -/
theorem IsCompletelyCopositive.convex_combination {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsCompletelyCopositive Φ₁) (hΦ₂ : IsCompletelyCopositive Φ₂)
    (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) :
    IsCompletelyCopositive ((p₁ : ℂ) • Φ₁ + (p₂ : ℂ) • Φ₂) :=
  IsCompletelyCopositive.add (IsCompletelyCopositive.smul_of_nonneg hΦ₁ p₁ hp₁)
    (IsCompletelyCopositive.smul_of_nonneg hΦ₂ p₂ hp₂)

/-- Convex combinations of PPT maps are PPT maps. -/
theorem IsPPTMap.convex_combination {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsPPTMap Φ₁) (hΦ₂ : IsPPTMap Φ₂)
    (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) :
    IsPPTMap ((p₁ : ℂ) • Φ₁ + (p₂ : ℂ) • Φ₂) :=
  IsPPTMap.add (IsPPTMap.smul_of_nonneg hΦ₁ p₁ hp₁)
    (IsPPTMap.smul_of_nonneg hΦ₂ p₂ hp₂)

/-- Convex combinations of entanglement-breaking maps are entanglement breaking. -/
theorem IsEntanglementBreaking.convex_combination {Φ₁ Φ₂ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ₁ : IsEntanglementBreaking Φ₁) (hΦ₂ : IsEntanglementBreaking Φ₂)
    (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) :
    IsEntanglementBreaking ((p₁ : ℂ) • Φ₁ + (p₂ : ℂ) • Φ₂) :=
  IsEntanglementBreaking.add (IsEntanglementBreaking.smul_of_nonneg hΦ₁ p₁ hp₁)
    (IsEntanglementBreaking.smul_of_nonneg hΦ₂ p₂ hp₂)

/-! ## Section 5: Trace-Replacement and Rank-1 State Preparation Channels (`ebIndex = 1`) -/

/-- The trace-replacement map `X ↦ (Matrix.trace X) • σ` which replaces any input matrix `X`
with the fixed target state / operator `σ` scaled by `Tr(X)`. -/
def traceReplaceMap {n : Type*} [Fintype n] (σ : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := Matrix.trace X • σ
  map_add' X Y := by
    simp only [Matrix.trace_add, add_smul]
  map_smul' c X := by
    rw [Matrix.trace_smul, smul_smul]
    rfl

/-- Establishes `traceReplaceMap_apply`: `traceReplaceMap σ X = Matrix.trace X • σ`, for the stated parameters. -/
@[simp]
theorem traceReplaceMap_apply {n : Type*} [Fintype n] (σ : Matrix n n ℂ) (X : Matrix n n ℂ) :
    traceReplaceMap σ X = Matrix.trace X • σ :=
  rfl

/-- Transposition intertwines trace-replacement maps: `t ∘ (traceReplaceMap σ) = traceReplaceMap σᵀ`. -/
theorem transposeMap_comp_traceReplaceMap {n : Type*} [Fintype n] (σ : Matrix n n ℂ) :
    transposeMap n ∘ₗ traceReplaceMap σ = traceReplaceMap (σᵀ) := by
  refine LinearMap.ext fun X => ?_
  ext a b
  simp only [LinearMap.comp_apply, transposeMap_apply, traceReplaceMap_apply,
    Matrix.transpose_apply, Matrix.smul_apply]

/-- The partial trace over the second subsystem `n`:
`(partialTraceSys X)_{i, j} = Tr(X_{i, j})`. -/
def partialTraceSys {κ n : Type*} [Fintype n] (X : Matrix (κ × n) (κ × n) ℂ) : Matrix κ κ ℂ :=
  Matrix.of fun i j => Matrix.trace (block X i j)

/-- Establishes `partialTraceSys_apply`: `partialTraceSys X i j = Matrix.trace (block X i j)`, for the stated parameters. -/
@[simp]
theorem partialTraceSys_apply {κ n : Type*} [Fintype n] (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) :
    partialTraceSys X i j = Matrix.trace (block X i j) :=
  rfl

/-- Action of `(id_κ ⊗ (traceReplaceMap σ))` on any bipartite matrix `X`:
it evaluates to `Tr_B(X) ⊗ σ`. -/
theorem refMap_traceReplaceMap {κ n : Type*} [Fintype n] (σ : Matrix n n ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (traceReplaceMap σ) X = partialTraceSys X ⊗ₖ σ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [refMap_apply, traceReplaceMap_apply, partialTraceSys_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]

/-- The partial trace of the maximally entangled state `|ω⟩⟨ω|` on `ℂ^d ⊗ ℂ^d`
is the identity matrix `1`. -/
theorem partialTraceSys_pureState_omegaVec (d : ℕ) :
    partialTraceSys (pureState (omegaVec d)) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  simp only [partialTraceSys_apply, Matrix.trace, Matrix.diag_apply, block_apply,
    pureState, Matrix.vecMulVec_apply, omegaVec, Pi.star_apply, RCLike.star_def,
    Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  · intro x _ hxi
    have hix : i ≠ x := Ne.symm hxi
    simp [hix]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The Choi matrix of `traceReplaceMap σ` decomposes explicitly as `1 ⊗ₖ σ`. -/
theorem choi_traceReplaceMap {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) :
    refMap (Fin d) (traceReplaceMap σ) (pureState (omegaVec d)) =
      (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ σ := by
  rw [refMap_traceReplaceMap, partialTraceSys_pureState_omegaVec]

/-- If `σ` is positive semidefinite, the Choi matrix of `traceReplaceMap σ` is separable. -/
theorem isSeparable_choi_traceReplaceMap {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) :
    IsSeparable (refMap (Fin d) (traceReplaceMap σ) (pureState (omegaVec d))) := by
  rw [choi_traceReplaceMap]
  exact IsSeparable.kronecker Matrix.PosSemidef.one hσ

/-- For any positive semidefinite target state `σ`, `traceReplaceMap σ` is entanglement breaking. -/
theorem isEntanglementBreaking_traceReplaceMap {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) :
    IsEntanglementBreaking (traceReplaceMap σ) :=
  (isEntanglementBreaking_iff_choi (traceReplaceMap σ)).mpr
    (isSeparable_choi_traceReplaceMap σ hσ)

/-- If `σ` and its transpose `σᵀ` are both positive semidefinite,
then `traceReplaceMap σ` is a PPT map. -/
theorem isPPTMap_traceReplaceMap {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) (hσT : σᵀ.PosSemidef) :
    IsPPTMap (traceReplaceMap σ) := by
  have hEB : IsEntanglementBreaking (traceReplaceMap σ) :=
    isEntanglementBreaking_traceReplaceMap σ hσ
  refine ⟨hEB.1, ?_⟩
  unfold IsCompletelyCopositive
  rw [transposeMap_comp_traceReplaceMap]
  exact (isEntanglementBreaking_traceReplaceMap (σᵀ) hσT).1

/-- Every positive semidefinite state `σ` satisfies `σᵀ.PosSemidef`,
so `traceReplaceMap σ` is unconditionally a PPT map for any positive semidefinite `σ`. -/
theorem isPPTMap_traceReplaceMap_of_posSemidef {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) :
    IsPPTMap (traceReplaceMap σ) :=
  isPPTMap_traceReplaceMap σ hσ hσ.transpose

/-- If `σ` and `σᵀ` are positive semidefinite, then `traceReplaceMap σ` is PPT
and has entanglement-breaking index equal to `1`. -/
theorem ebIndex_traceReplaceMap_eq_one {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) (hσT : σᵀ.PosSemidef) :
    IsPPTMap (traceReplaceMap σ) ∧ ebIndex (traceReplaceMap σ) = 1 :=
  ⟨isPPTMap_traceReplaceMap σ hσ hσT,
    ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_traceReplaceMap σ hσ)⟩

/-- Single-step entanglement breaking for trace-replacement maps on any positive semidefinite `σ`. -/
theorem ebIndex_traceReplaceMap_of_posSemidef_eq_one {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) :
    IsPPTMap (traceReplaceMap σ) ∧ ebIndex (traceReplaceMap σ) = 1 :=
  ⟨isPPTMap_traceReplaceMap_of_posSemidef σ hσ,
    ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_traceReplaceMap σ hσ)⟩

/-- Pure state preparation channel `X ↦ Tr(X) • |ψ⟩⟨ψ|` is a PPT map. -/
theorem isPPTMap_traceReplaceMap_pureState {d : ℕ} (ψ : Fin d → ℂ) :
    IsPPTMap (traceReplaceMap (pureState ψ)) :=
  isPPTMap_traceReplaceMap_of_posSemidef (pureState ψ)
    (Matrix.posSemidef_vecMulVec_self_star ψ)

/-- Every rank-1 pure state preparation channel is PPT and breaks entanglement in a single step (`ebIndex = 1`). -/
theorem ebIndex_traceReplaceMap_pureState_eq_one {d : ℕ} (ψ : Fin d → ℂ) :
    IsPPTMap (traceReplaceMap (pureState ψ)) ∧ ebIndex (traceReplaceMap (pureState ψ)) = 1 :=
  ebIndex_traceReplaceMap_of_posSemidef_eq_one (pureState ψ)
    (Matrix.posSemidef_vecMulVec_self_star ψ)

/-! ## Section 6: Depolarizing Convex Mixtures and Arbitrary-Basis Pinching Maps -/

/-- Pre-composition of an entanglement-breaking map with a completely positive map is
entanglement breaking (alias for `IsEntanglementBreaking.comp_isCompletelyPositive`). -/
theorem isEntanglementBreaking_comp_right
    {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ} {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΨ : IsEntanglementBreaking Ψ) (hΦ : IsCompletelyPositive Φ) :
    IsEntanglementBreaking (Ψ ∘ₗ Φ) :=
  IsEntanglementBreaking.comp_isCompletelyPositive hΨ hΦ

/-- Post-composition of an entanglement-breaking map with a completely positive map is
entanglement breaking (alias for `IsEntanglementBreaking.comp_of_isCompletelyPositive`). -/
theorem isEntanglementBreaking_comp_left [Finite n]
    {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΨ : IsCompletelyPositive Ψ) (hΦ : IsEntanglementBreaking Φ) :
    IsEntanglementBreaking (Ψ ∘ₗ Φ) :=
  IsEntanglementBreaking.comp_of_isCompletelyPositive hΦ hΨ

/-- Depolarizing convex mixture / replacement channel:
`depolarizeMix p Φ σ = (1 - p) • Φ + p • traceReplaceMap σ`. -/
def depolarizeMix {n : Type*} [Fintype n] (p : ℝ) (Φ : Module.End ℂ (Matrix n n ℂ))
    (σ : Matrix n n ℂ) : Module.End ℂ (Matrix n n ℂ) :=
  ((1 - p : ℝ) : ℂ) • Φ + (p : ℂ) • traceReplaceMap σ

/-- Establishes `depolarizeMix_apply`: `depolarizeMix p Φ σ X = ((1 - p : ℝ) : ℂ) • Φ X + (p : ℂ) • traceReplaceMap σ X`, for the stated parameters. -/
@[simp]
theorem depolarizeMix_apply {n : Type*} [Fintype n] (p : ℝ)
    (Φ : Module.End ℂ (Matrix n n ℂ)) (σ : Matrix n n ℂ) (X : Matrix n n ℂ) :
    depolarizeMix p Φ σ X = ((1 - p : ℝ) : ℂ) • Φ X + (p : ℂ) • traceReplaceMap σ X :=
  rfl

/-- Depolarizing convex mixtures preserve PPT maps when `0 ≤ p ≤ 1` and `σ, σᵀ` are positive semidefinite. -/
theorem isPPTMap_depolarizeMix {d : ℕ} {p : ℝ}
    {Φ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)} {σ : Matrix (Fin d) (Fin d) ℂ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hΦ : IsPPTMap Φ)
    (hσ : σ.PosSemidef) (hσT : σᵀ.PosSemidef) :
    IsPPTMap (depolarizeMix p Φ σ) :=
  IsPPTMap.convex_combination hΦ (isPPTMap_traceReplaceMap σ hσ hσT)
    (1 - p) p (by linarith) hp0

/-- For the identity / maximally mixed operator `σ = 1`, the standard depolarizing channel mixture
preserves PPT maps for any `0 ≤ p ≤ 1`. -/
theorem isPPTMap_depolarizeMix_one {d : ℕ} {p : ℝ}
    {Φ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hΦ : IsPPTMap Φ) :
    IsPPTMap (depolarizeMix p Φ (1 : Matrix (Fin d) (Fin d) ℂ)) :=
  isPPTMap_depolarizeMix hp0 hp1 hΦ Matrix.PosSemidef.one Matrix.PosSemidef.one.transpose

/-- Depolarizing convex mixtures preserve entanglement-breaking maps when `0 ≤ p ≤ 1` and `σ.PosSemidef`. -/
theorem isEntanglementBreaking_depolarizeMix {d : ℕ} {p : ℝ}
    {Φ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)} {σ : Matrix (Fin d) (Fin d) ℂ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hΦ : IsEntanglementBreaking Φ)
    (hσ : σ.PosSemidef) :
    IsEntanglementBreaking (depolarizeMix p Φ σ) :=
  IsEntanglementBreaking.convex_combination hΦ
    (isEntanglementBreaking_traceReplaceMap σ hσ)
    (1 - p) p (by linarith) hp0

/-- Standard depolarizing mixture with `σ = 1` preserves entanglement breaking for any `0 ≤ p ≤ 1`. -/
theorem isEntanglementBreaking_depolarizeMix_one {d : ℕ} {p : ℝ}
    {Φ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hΦ : IsEntanglementBreaking Φ) :
    IsEntanglementBreaking (depolarizeMix p Φ (1 : Matrix (Fin d) (Fin d) ℂ)) :=
  isEntanglementBreaking_depolarizeMix hp0 hp1 hΦ Matrix.PosSemidef.one

/-- Arbitrary-basis pinching / measurement-and-prepare map:
`basisPinchMap U V w = (congruenceMap U ∘ₗ diagPinchMap w) ∘ₗ congruenceMap V`. -/
def basisPinchMap {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) (w : Fin d → ℝ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  (congruenceMap U ∘ₗ diagPinchMap w) ∘ₗ congruenceMap V

/-- Any arbitrary-basis pinching map with nonnegative weights is entanglement breaking. -/
theorem isEntanglementBreaking_basisPinchMap {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsEntanglementBreaking (basisPinchMap U V w) := by
  have hDiag : IsEntanglementBreaking (diagPinchMap w) :=
    isEntanglementBreaking_diagPinchMap w hw
  have hU : IsCompletelyPositive (congruenceMap U) :=
    isCompletelyPositive_congruenceMap U
  have hV : IsCompletelyPositive (congruenceMap V) :=
    isCompletelyPositive_congruenceMap V
  have hLeft : IsEntanglementBreaking (congruenceMap U ∘ₗ diagPinchMap w) :=
    isEntanglementBreaking_comp_left hU hDiag
  exact isEntanglementBreaking_comp_right hLeft hV

/-- Any arbitrary-basis pinching map with nonnegative weights has entanglement-breaking index `1`. -/
theorem ebIndex_basisPinchMap_eq_one {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ebIndex (basisPinchMap U V w) = 1 :=
  ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_basisPinchMap U V w hw)

/-! ## Section 7: Finite-Sum Conic Closure, Measure-and-Prepare Channels, Transpose-Depolarizing Family, and Surrounded PPT Composition Chains -/

/-- Completely positive maps are closed under the zero map. -/
theorem IsCompletelyPositive.zero :
    IsCompletelyPositive (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :=
  isCompletelyPositive_zero

/-- Completely copositive maps are closed under the zero map. -/
theorem IsCompletelyCopositive.zero :
    IsCompletelyCopositive (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) := by
  unfold IsCompletelyCopositive
  rw [LinearMap.comp_zero]
  exact isCompletelyPositive_zero

/-- PPT maps are closed under the zero map. -/
theorem IsPPTMap.zero :
    IsPPTMap (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :=
  isPPTMap_zero

/-- Entanglement-breaking maps are closed under the zero map. -/
theorem IsEntanglementBreaking.zero :
    IsEntanglementBreaking (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :=
  isEntanglementBreaking_zero

/-- Finite sums of completely positive maps are completely positive. -/
theorem IsCompletelyPositive.sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsCompletelyPositive (Φ i)) :
    IsCompletelyPositive (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsCompletelyPositive.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsCompletelyPositive.add (hΦ a (Finset.mem_insert_self a s))
      (ih fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

/-- Nonnegative-weighted finite sums of completely positive maps are completely positive. -/
theorem IsCompletelyPositive.sum_smul_of_nonneg {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsCompletelyPositive (Φ i)) :
    IsCompletelyPositive (∑ i ∈ s, (w i : ℂ) • Φ i) :=
  IsCompletelyPositive.sum s (fun i => (w i : ℂ) • Φ i) fun i hi =>
    IsCompletelyPositive.smul_of_nonneg (hΦ i hi) (w i) (hw i hi)

/-- Finite sums of completely copositive maps are completely copositive. -/
theorem IsCompletelyCopositive.sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsCompletelyCopositive (Φ i)) :
    IsCompletelyCopositive (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsCompletelyCopositive.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsCompletelyCopositive.add (hΦ a (Finset.mem_insert_self a s))
      (ih fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

/-- Nonnegative-weighted finite sums of completely copositive maps are completely copositive. -/
theorem IsCompletelyCopositive.sum_smul_of_nonneg {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsCompletelyCopositive (Φ i)) :
    IsCompletelyCopositive (∑ i ∈ s, (w i : ℂ) • Φ i) :=
  IsCompletelyCopositive.sum s (fun i => (w i : ℂ) • Φ i) fun i hi =>
    IsCompletelyCopositive.smul_of_nonneg (hΦ i hi) (w i) (hw i hi)

/-- Finite sums of PPT maps are PPT maps. -/
theorem IsPPTMap.sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsPPTMap (Φ i)) :
    IsPPTMap (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsPPTMap.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsPPTMap.add (hΦ a (Finset.mem_insert_self a s))
      (ih fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

/-- Nonnegative-weighted finite sums of PPT maps are PPT maps. -/
theorem IsPPTMap.sum_smul_of_nonneg {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsPPTMap (Φ i)) :
    IsPPTMap (∑ i ∈ s, (w i : ℂ) • Φ i) :=
  IsPPTMap.sum s (fun i => (w i : ℂ) • Φ i) fun i hi =>
    IsPPTMap.smul_of_nonneg (hΦ i hi) (w i) (hw i hi)

/-- Finite sums of entanglement-breaking maps are entanglement breaking. -/
theorem IsEntanglementBreaking.sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsEntanglementBreaking (Φ i)) :
    IsEntanglementBreaking (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsEntanglementBreaking.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsEntanglementBreaking.add (hΦ a (Finset.mem_insert_self a s))
      (ih fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

/-- Nonnegative-weighted finite sums of entanglement-breaking maps are entanglement breaking. -/
theorem IsEntanglementBreaking.sum_smul_of_nonneg {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (Φ : ι → Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΦ : ∀ i ∈ s, IsEntanglementBreaking (Φ i)) :
    IsEntanglementBreaking (∑ i ∈ s, (w i : ℂ) • Φ i) :=
  IsEntanglementBreaking.sum s (fun i => (w i : ℂ) • Φ i) fun i hi =>
    IsEntanglementBreaking.smul_of_nonneg (hΦ i hi) (w i) (hw i hi)

/-- General rank-1 / operator Measure-and-Prepare (Kraus-Replacement) channels:
`measurePrepareMap K σ = ∑ i : Fin k, (traceReplaceMap (σ i)) ∘ₗ (congruenceMap (K i))`.
For an input matrix `X`, each term evaluates to `Tr(K i * X * (K i)ᴴ) • σ i`. -/
def measurePrepareMap {n : Type*} [Fintype n] {k : ℕ}
    (K : Fin k → Matrix n n ℂ) (σ : Fin k → Matrix n n ℂ) :
    Module.End ℂ (Matrix n n ℂ) :=
  ∑ i : Fin k, (traceReplaceMap (σ i)) ∘ₗ (congruenceMap (K i))

/-- Establishes `measurePrepareMap_apply`: `measurePrepareMap K σ X = ∑ i : Fin k, Matrix.trace (K i * X * (K i)ᴴ) • σ i`, for the stated parameters. -/
@[simp]
theorem measurePrepareMap_apply {n : Type*} [Fintype n] {k : ℕ}
    (K : Fin k → Matrix n n ℂ) (σ : Fin k → Matrix n n ℂ) (X : Matrix n n ℂ) :
    measurePrepareMap K σ X =
      ∑ i : Fin k, Matrix.trace (K i * X * (K i)ᴴ) • σ i := by
  simp only [measurePrepareMap, LinearMap.sum_apply, LinearMap.comp_apply,
    traceReplaceMap_apply, congruenceMap_apply]

/-- If each target state `σ i` is positive semidefinite, then `measurePrepareMap K σ`
is entanglement breaking. -/
theorem isEntanglementBreaking_measurePrepareMap {d : ℕ} {k : ℕ}
    (K : Fin k → Matrix (Fin d) (Fin d) ℂ) (σ : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).PosSemidef) :
    IsEntanglementBreaking (measurePrepareMap K σ) := by
  unfold measurePrepareMap
  refine IsEntanglementBreaking.sum Finset.univ _ fun i _ => ?_
  exact IsEntanglementBreaking.comp_isCompletelyPositive
    (isEntanglementBreaking_traceReplaceMap (σ i) (hσ i))
    (isCompletelyPositive_congruenceMap (K i))

/-- Alias for `isEntanglementBreaking_measurePrepareMap`. -/
abbrev measurePrepareMap_entanglementBreaking := @isEntanglementBreaking_measurePrepareMap

/-- For any positive semidefinite target states `σ`, `measurePrepareMap K σ` has
entanglement-breaking index equal to `1`. -/
theorem ebIndex_measurePrepareMap_eq_one {d : ℕ} {k : ℕ}
    (K : Fin k → Matrix (Fin d) (Fin d) ℂ) (σ : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).PosSemidef) :
    ebIndex (measurePrepareMap K σ) = 1 :=
  ebIndex_eq_one_of_isEntanglementBreaking
    (isEntanglementBreaking_measurePrepareMap K σ hσ)

/-- Alias for `ebIndex_measurePrepareMap_eq_one`. -/
abbrev measurePrepareMap_ebIndex := @ebIndex_measurePrepareMap_eq_one

/-- If each `σ i` and `(σ i)ᵀ` are positive semidefinite, then `measurePrepareMap K σ`
is a PPT map. -/
theorem isPPTMap_measurePrepareMap {d : ℕ} {k : ℕ}
    (K : Fin k → Matrix (Fin d) (Fin d) ℂ) (σ : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).PosSemidef) (hσT : ∀ i, (σ i)ᵀ.PosSemidef) :
    IsPPTMap (measurePrepareMap K σ) := by
  unfold measurePrepareMap
  refine IsPPTMap.sum Finset.univ _ fun i _ => ?_
  exact IsPPTMap.comp_isCompletelyPositive (isPPTMap_traceReplaceMap (σ i) (hσ i) (hσT i))
    (isCompletelyPositive_congruenceMap (K i))

/-- Alias for `isPPTMap_measurePrepareMap`. -/
abbrev measurePrepareMap_isPPTMap := @isPPTMap_measurePrepareMap

/-- Positive semidefinite target states unconditionally yield a PPT measure-and-prepare map. -/
theorem isPPTMap_measurePrepareMap_of_posSemidef {d : ℕ} {k : ℕ}
    (K : Fin k → Matrix (Fin d) (Fin d) ℂ) (σ : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).PosSemidef) :
    IsPPTMap (measurePrepareMap K σ) :=
  isPPTMap_measurePrepareMap K σ hσ fun i => (hσ i).transpose

/-- Werner–Holevo / Transpose-Depolarizing mixture:
`transposeDepolarizeMix p σ = ((1 - p : ℝ) : ℂ) • transposeMap (Fin d) + (p : ℂ) • traceReplaceMap σ`. -/
def transposeDepolarizeMix {d : ℕ} (p : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  ((1 - p : ℝ) : ℂ) • transposeMap (Fin d) + (p : ℂ) • traceReplaceMap σ

/-- Establishes `transposeDepolarizeMix_apply`: `transposeDepolarizeMix p σ X = ((1 - p : ℝ) : ℂ) • Xᵀ + (p : ℂ) • Matrix.trace X • σ`, for the stated parameters. -/
@[simp]
theorem transposeDepolarizeMix_apply {d : ℕ} (p : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    transposeDepolarizeMix p σ X =
      ((1 - p : ℝ) : ℂ) • Xᵀ + (p : ℂ) • Matrix.trace X • σ :=
  rfl

/-- Transposition intertwines the transpose-depolarizing mixture and the standard depolarizing mixture:
`t ∘ₗ (transposeDepolarizeMix p σ) = depolarizeMix p id (σᵀ)`. -/
theorem transposeMap_comp_transposeDepolarizeMix {d : ℕ} (p : ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    transposeMap (Fin d) ∘ₗ transposeDepolarizeMix p σ =
      depolarizeMix p LinearMap.id (σᵀ) := by
  refine LinearMap.ext fun X => ?_
  ext a b
  simp only [LinearMap.comp_apply, transposeMap_apply, transposeDepolarizeMix_apply,
    depolarizeMix_apply, LinearMap.id_apply, traceReplaceMap_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply]

/-- The transpose-depolarizing mixture is completely copositive for `0 ≤ p ≤ 1`
whenever `σᵀ.PosSemidef`. -/
theorem isCompletelyCopositive_transposeDepolarizeMix {d : ℕ} {p : ℝ}
    {σ : Matrix (Fin d) (Fin d) ℂ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hσT : σᵀ.PosSemidef) :
    IsCompletelyCopositive (transposeDepolarizeMix p σ) := by
  unfold IsCompletelyCopositive
  rw [transposeMap_comp_transposeDepolarizeMix]
  exact IsCompletelyPositive.convex_combination
    isCompletelyPositive_id
    (isEntanglementBreaking_traceReplaceMap (σᵀ) hσT).1
    (1 - p) p (by linarith) hp0

/-- Standard Werner–Holevo transpose-depolarizing mixture with `σ = 1`
is completely copositive for all `0 ≤ p ≤ 1`. -/
theorem isCompletelyCopositive_transposeDepolarizeMix_one {d : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsCompletelyCopositive (transposeDepolarizeMix p (1 : Matrix (Fin d) (Fin d) ℂ)) :=
  isCompletelyCopositive_transposeDepolarizeMix hp0 hp1
    Matrix.PosSemidef.one.transpose

/-- **Surrounded PPT Composition Chains:**
For any dimension `d ≥ 2`, any sequence of `2(d-1)` PPT maps `Φ_0, …, Φ_{2(d-1)-1}`,
and any pre- and post-processing completely positive maps `Ψ_pre` and `Ψ_post`,
the surrounded composition `(Ψ_post ∘ₗ compList (List.ofFn Φ)) ∘ₗ Ψ_pre` is entanglement breaking. -/
theorem compose_ppt_maps_surrounded_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (Ψ_post Ψ_pre : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hpost : IsCompletelyPositive Ψ_post) (hpre : IsCompletelyPositive Ψ_pre) :
    IsEntanglementBreaking ((Ψ_post ∘ₗ compList (List.ofFn Φ)) ∘ₗ Ψ_pre) := by
  have hEB : IsEntanglementBreaking (compList (List.ofFn Φ)) :=
    compose_ppt_maps_entanglementBreaking d hd Φ hΦ
  exact IsEntanglementBreaking.comp_isCompletelyPositive
    (IsEntanglementBreaking.comp_of_isCompletelyPositive hEB hpost) hpre

/-- Associativity variant for surrounded PPT composition chains. -/
theorem compose_ppt_maps_surrounded_entanglementBreaking' (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (Ψ_post Ψ_pre : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hpost : IsCompletelyPositive Ψ_post) (hpre : IsCompletelyPositive Ψ_pre) :
    IsEntanglementBreaking (Ψ_post ∘ₗ compList (List.ofFn Φ) ∘ₗ Ψ_pre) := by
  rw [← LinearMap.comp_assoc]
  exact compose_ppt_maps_surrounded_entanglementBreaking d hd Φ hΦ Ψ_post Ψ_pre hpost hpre

/-! ## Section 8: Schmidt-Number Conic/Convex Closure, Reference-Dimension-Limited Separability Bounds, and Heterogeneous Interleaved PPT-CP Composition -/

/-! ### Section 8.1: Separability ↔ Schmidt Number ≤ 1 and Conic/Convex Closure of `HasSchmidtNumberLE` -/

/-- A bipartite operator is separable if and only if its Schmidt number is at most one:
`IsSeparable X ↔ HasSchmidtNumberLE 1 X`.
This unites `IsSeparable.hasSchmidtNumberLE_one` from `Reduction.lean` and
`IsSeparable.of_hasSchmidtNumberLE_one` from `SchmidtFacts.lean`. -/
theorem isSeparable_iff_hasSchmidtNumberLE_one [Fintype κ] [Fintype n]
    {X : Matrix (κ × n) (κ × n) ℂ} :
    IsSeparable X ↔ HasSchmidtNumberLE 1 X :=
  ⟨IsSeparable.hasSchmidtNumberLE_one, IsSeparable.of_hasSchmidtNumberLE_one⟩

/-- Scaling an operator by a nonnegative real scalar preserves any Schmidt-number upper bound:
if `HasSchmidtNumberLE s X` and `0 ≤ c`, then `HasSchmidtNumberLE s ((c : ℂ) • X)`.
Proven via reference-system conjugation `HasSchmidtNumberLE.refConj` with `L = √c • 1`. -/
theorem HasSchmidtNumberLE.smul_of_nonneg [Fintype κ] [Fintype n] [DecidableEq n]
    {s : ℕ} {X : Matrix (κ × n) (κ × n) ℂ} (hX : HasSchmidtNumberLE s X)
    (c : ℝ) (hc : 0 ≤ c) :
    HasSchmidtNumberLE s ((c : ℂ) • X) := by
  classical
  let r : ℂ := (Real.sqrt c : ℂ)
  have hr : r * r = (c : ℂ) := by
    dsimp [r]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hconj : (star r : ℂ) = r := Complex.conj_ofReal (Real.sqrt c)
  let L : Matrix κ κ ℂ := r • (1 : Matrix κ κ ℂ)
  have hL : (L ⊗ₖ (1 : Matrix n n ℂ)) = r • (1 : Matrix (κ × n) (κ × n) ℂ) := by
    dsimp [L]
    rw [Matrix.smul_kronecker, one_kronecker_one]
  have h_eq : (L ⊗ₖ (1 : Matrix n n ℂ)) * X * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ = (c : ℂ) • X := by
    rw [hL, conjTranspose_smul, conjTranspose_one, hconj, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hr]
  have h_conj := HasSchmidtNumberLE.refConj L hX
  rwa [h_eq] at h_conj

/-- Conic and convex combinations of operators with Schmidt number bounded by `s` preserve
the Schmidt number bound: for `a, b ≥ 0`, `HasSchmidtNumberLE s ((a : ℂ) • X + (b : ℂ) • Y)`. -/
theorem HasSchmidtNumberLE.convex_combination [Fintype κ] [Fintype n] [DecidableEq n]
    {s : ℕ} {X Y : Matrix (κ × n) (κ × n) ℂ}
    (hX : HasSchmidtNumberLE s X) (hY : HasSchmidtNumberLE s Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSchmidtNumberLE s ((a : ℂ) • X + (b : ℂ) • Y) :=
  (HasSchmidtNumberLE.smul_of_nonneg hX a ha).add
    (HasSchmidtNumberLE.smul_of_nonneg hY b hb)

/-- Nonnegative-weighted finite sums of operators with Schmidt number bounded by `s`
preserve the Schmidt number bound. -/
theorem HasSchmidtNumberLE.sum_smul_of_nonneg {ι : Type*} [Fintype κ] [Fintype n] [DecidableEq n]
    (t : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i)
    {s : ℕ} (X : ι → Matrix (κ × n) (κ × n) ℂ)
    (hX : ∀ i ∈ t, HasSchmidtNumberLE s (X i)) :
    HasSchmidtNumberLE s (∑ i ∈ t, (w i : ℂ) • X i) :=
  HasSchmidtNumberLE.sum t fun i hi => HasSchmidtNumberLE.smul_of_nonneg (hX i hi) (w i) (hw i hi)

/-! ### Section 8.2: Intermediate 2j-Step Schmidt-Number Bound & Reference-Limited Early Separability Collapse -/

/-- Quantitative intermediate `2j`-step Schmidt-number bound for compositions of `2j` PPT maps
acting on any bipartite positive semidefinite state:
`HasSchmidtNumberLE (max (min k d - j) 1) (refMap (Fin k) (compList (List.ofFn Φ)) X)`. -/
theorem hasSchmidtNumberLE_refMap_comp_ppt_maps (d j k : ℕ)
    (Φ : Fin (2 * j) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hX : X.PosSemidef) :
    HasSchmidtNumberLE (max (min k d - j) 1) (refMap (Fin k) (compList (List.ofFn Φ)) X) := by
  have hCard : HasSchmidtNumberLE (min k d) X := by
    simpa only [Fintype.card_fin] using hasSchmidtNumberLE_min_card hX
  refine hasSchmidtNumberLE_refMap_compList j (List.ofFn Φ) (by simp) (fun φ hφ => ?_) hCard
  rcases List.mem_ofFn.mp hφ with ⟨i, rfl⟩
  exact hΦ i

/-- Companion `schmidtNumber` inequality for intermediate `2j`-step PPT compositions:
`schmidtNumber (refMap (Fin k) (compList (List.ofFn Φ)) X) ≤ max (min k d - j) 1`. -/
theorem schmidtNumber_refMap_comp_ppt_maps_le (d j k : ℕ)
    (Φ : Fin (2 * j) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hX : X.PosSemidef) :
    schmidtNumber (refMap (Fin k) (compList (List.ofFn Φ)) X) ≤ max (min k d - j) 1 :=
  schmidtNumber_le (hasSchmidtNumberLE_refMap_comp_ppt_maps d j k Φ hΦ X hX)

/-- If an initial bipartite state has Schmidt number bounded by `s ≤ j + 1`, then composing
`2 * j` PPT maps collapses the state to separability (`IsSeparable`). -/
theorem isSeparable_refMap_comp_ppt_maps_of_hasSchmidtNumberLE (d j k : ℕ)
    (Φ : Fin (2 * j) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    {s : ℕ} {X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ}
    (hX : HasSchmidtNumberLE s X) (hs : s ≤ j + 1) :
    IsSeparable (refMap (Fin k) (compList (List.ofFn Φ)) X) := by
  have hSN := hasSchmidtNumberLE_refMap_compList j (List.ofFn Φ) (by simp) (fun φ hφ => ?_) hX
  · have h1 : max (s - j) 1 = 1 := by omega
    rw [h1] at hSN
    exact IsSeparable.of_hasSchmidtNumberLE_one hSN
  · rcases List.mem_ofFn.mp hφ with ⟨i, rfl⟩
    exact hΦ i

/-- **Reference-Dimension-Limited Composition Bound:**
For any reference dimension `k ≥ 1` and system dimension `d`, only `2 * (k - 1)` PPT maps
on `M_d(ℂ)` suffice to make `refMap (Fin k) (compList (List.ofFn Φ)) X` separable for every
positive semidefinite bipartite state `X`. -/
theorem isSeparable_refMap_comp_ppt_maps_of_ref_le (k d : ℕ) (hk : 1 ≤ k)
    (Φ : Fin (2 * (k - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hX : X.PosSemidef) :
    IsSeparable (refMap (Fin k) (compList (List.ofFn Φ)) X) := by
  have hCard : HasSchmidtNumberLE (min k d) X := by
    simpa only [Fintype.card_fin] using hasSchmidtNumberLE_min_card hX
  refine isSeparable_refMap_comp_ppt_maps_of_hasSchmidtNumberLE d (k - 1) k Φ hΦ hCard ?_
  omega

/-! ### Section 8.3: General Heterogeneous Interleaved PPT-CP Composition -/

/-- **Heterogeneous Interleaved PPT-CP Composition:**
For any dimension `d ≥ 2`, composing `2 * (d - 1)` distinct PPT maps `Φ i` each interleaved
with an arbitrary completely positive map `S i` yields an entanglement-breaking map. -/
theorem compose_heterogeneous_ppt_interleaved_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (S : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hS : ∀ i, IsCompletelyPositive (S i)) :
    IsEntanglementBreaking (compList (List.ofFn fun i => Φ i ∘ₗ S i)) := by
  refine compose_ppt_maps_entanglementBreaking d hd (fun i => Φ i ∘ₗ S i) (fun i => ?_)
  exact IsPPTMap.comp_isCompletelyPositive (hΦ i) (hS i)

/-- Heterogeneous interleaved PPT-CP composition with an additional completely positive
post-processing channel `Ψ_post`. -/
theorem compose_heterogeneous_ppt_interleaved_post_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i))
    (S : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hS : ∀ i, IsCompletelyPositive (S i))
    (Ψ_post : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hpost : IsCompletelyPositive Ψ_post) :
    IsEntanglementBreaking (Ψ_post ∘ₗ compList (List.ofFn fun i => Φ i ∘ₗ S i)) :=
  IsEntanglementBreaking.comp_of_isCompletelyPositive
    (compose_heterogeneous_ppt_interleaved_entanglementBreaking d hd Φ hΦ S hS) hpost

/-! ## Section 9: Peres–Horodecki Separability Criterion, CP Chain Ideal Absorption, and All-Power Monotonicity -/

/-! ### Subsection 9.1: Peres–Horodecki Criterion (`IsSeparable → PPT`) & Universal `EB ⊆ PPT` Cone Inclusion -/

-- Note: `partialTransposeRef_kronecker`, `partialTransposeRef_sum`, and
-- `IsSeparable.posSemidef_partialTransposeRef` are established in `NonTrivial.lean`
-- and are in scope in namespace `Qatlib.Foundations.PPTMatrix.OperatorCones`.

/-- **Peres–Horodecki Separability Criterion (Reference Partial Transpose Separability):**
The reference partial transpose of any separable bipartite operator is separable. -/
theorem IsSeparable.partialTransposeRef {X : Matrix (κ × n) (κ × n) ℂ}
    (hX : IsSeparable X) : IsSeparable (partialTransposeRef X) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := hX
  refine ⟨N, fun i => (A i)ᵀ, B, fun i => (hA i).transpose, hB, ?_⟩
  rw [partialTransposeRef_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialTransposeRef_kronecker]

/-- Establishes `IsEntanglementBreaking.isCompletelyCopositive`: `IsCompletelyCopositive Φ`, for the stated parameters. -/
theorem IsEntanglementBreaking.isCompletelyCopositive [Finite p]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsEntanglementBreaking Φ) :
    IsCompletelyCopositive Φ := fun k X hX => by
  have hPosΓ := IsSeparable.posSemidef_partialTransposeRef (hΦ.2 k X hX)
  rw [partialTransposeRef_refMap] at hPosΓ
  exact Matrix.posSemidef_transpose_iff.mp hPosΓ

/-- Establishes `IsEntanglementBreaking.isPPTMap`: `IsPPTMap Φ`, for the stated parameters. -/
theorem IsEntanglementBreaking.isPPTMap [Finite p]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsEntanglementBreaking Φ) :
    IsPPTMap Φ :=
  ⟨hΦ.1, IsEntanglementBreaking.isCompletelyCopositive hΦ⟩

/-! ### Subsection 9.2: Arbitrary-Length CP Chain Ideal Absorption -/

/-- **Arbitrary-Length CP Chain Ideal Absorption:**
For any finite type `n` and any list `L` of completely positive maps on `Matrix n n ℂ`,
if at least one channel `ψ ∈ L` is entanglement breaking, then the full composite
channel `compList L` is entanglement breaking. -/
theorem isEntanglementBreaking_compList_of_mem [Finite n]
    (L : List (Module.End ℂ (Matrix n n ℂ)))
    (hCP : ∀ φ ∈ L, IsCompletelyPositive φ)
    (hEB : ∃ ψ ∈ L, IsEntanglementBreaking ψ) :
    IsEntanglementBreaking (compList L) := by
  obtain ⟨ψ, hψ_mem, hψ_eb⟩ := hEB
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hψ_mem
  rw [compList_append, compList_cons]
  have hCP_s : ∀ φ ∈ s, IsCompletelyPositive φ := fun φ hφ =>
    hCP φ (List.mem_append_left _ hφ)
  have hCP_t : ∀ φ ∈ t, IsCompletelyPositive φ := fun φ hφ =>
    hCP φ (List.mem_append_right _ (List.mem_cons_of_mem ψ hφ))
  have hCP_comp_s := isCompletelyPositive_compList s hCP_s
  have hCP_comp_t := isCompletelyPositive_compList t hCP_t
  exact IsEntanglementBreaking.comp_isCompletelyPositive
    (IsEntanglementBreaking.comp_of_isCompletelyPositive hψ_eb hCP_comp_t) hCP_comp_s

/-- Indexed `Fin N` version of ideal absorption: if all channels `Φ i` in an arbitrary
chain of length `N` are completely positive and at least one channel `Φ i₀` is entanglement
breaking, then the composite channel `compList (List.ofFn Φ)` is entanglement breaking. -/
theorem isEntanglementBreaking_ofFn_of_exists [Finite n] {N : ℕ}
    (Φ : Fin N → Module.End ℂ (Matrix n n ℂ))
    (hCP : ∀ i, IsCompletelyPositive (Φ i))
    (hEB : ∃ i₀ : Fin N, IsEntanglementBreaking (Φ i₀)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  refine isEntanglementBreaking_compList_of_mem (List.ofFn Φ) ?_ ?_
  · intro φ hφ
    rw [List.mem_ofFn] at hφ
    obtain ⟨i, rfl⟩ := hφ
    exact hCP i
  · obtain ⟨i₀, hi₀⟩ := hEB
    refine ⟨Φ i₀, ?_, hi₀⟩
    exact List.mem_ofFn.mpr ⟨i₀, rfl⟩

/-- The entanglement-breaking index of any list composition of CP channels containing
at least one entanglement-breaking channel collapses to `1`. -/
theorem ebIndex_compList_of_mem_eq_one [Finite n]
    (L : List (Module.End ℂ (Matrix n n ℂ)))
    (hCP : ∀ φ ∈ L, IsCompletelyPositive φ)
    (hEB : ∃ ψ ∈ L, IsEntanglementBreaking ψ) :
    ebIndex (compList L) = 1 :=
  ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_compList_of_mem L hCP hEB)

/-- The entanglement-breaking index of an indexed CP chain containing at least one
entanglement-breaking channel collapses to `1`. -/
theorem ebIndex_ofFn_of_exists_eq_one [Finite n] {N : ℕ}
    (Φ : Fin N → Module.End ℂ (Matrix n n ℂ))
    (hCP : ∀ i, IsCompletelyPositive (Φ i))
    (hEB : ∃ i₀ : Fin N, IsEntanglementBreaking (Φ i₀)) :
    ebIndex (compList (List.ofFn Φ)) = 1 :=
  ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_ofFn_of_exists Φ hCP hEB)

/-! ### Subsection 9.3: Power Closure & Universal All-Power Threshold -/

/-- Powers of completely positive maps are completely positive: for any `m : ℕ`,
if `T` is completely positive then `T ^ m` is completely positive. -/
theorem IsCompletelyPositive.pow {T : Module.End ℂ (Matrix n n ℂ)}
    (hT : IsCompletelyPositive T) (m : ℕ) :
    IsCompletelyPositive (T ^ m) := by
  rw [← compList_replicate T m]
  exact isCompletelyPositive_compList (List.replicate m T) fun φ hφ => by
    obtain rfl := List.eq_of_mem_replicate hφ
    exact hT

/-- Powers of PPT maps with exponent `m ≥ 1` are PPT maps:
if `T` is a PPT map and `1 ≤ m`, then `T ^ m` is a PPT map. -/
theorem IsPPTMap.pow {T : Module.End ℂ (Matrix n n ℂ)}
    (hT : IsPPTMap T) {m : ℕ} (hm : 1 ≤ m) :
    IsPPTMap (T ^ m) := by
  induction m, hm using Nat.le_induction with
  | base =>
      rw [pow_one]
      exact hT
  | succ k hk ih =>
      rw [pow_succ, Module.End.mul_eq_comp]
      exact ih.comp hT

/-- Power absorption in the CP semigroup: if `T` is completely positive and `T ^ m` is
entanglement breaking, then `T ^ M` is entanglement breaking for all `M ≥ m`. -/
theorem IsEntanglementBreaking.pow_of_le [Finite n] {T : Module.End ℂ (Matrix n n ℂ)}
    (hCP : IsCompletelyPositive T) {m M : ℕ}
    (hm : IsEntanglementBreaking (T ^ m)) (h : m ≤ M) :
    IsEntanglementBreaking (T ^ M) := by
  have hM : M = (M - m) + m := by omega
  rw [hM, pow_add, Module.End.mul_eq_comp]
  exact IsEntanglementBreaking.comp_of_isCompletelyPositive hm (IsCompletelyPositive.pow hCP (M - m))

/-- **Universal All-Power Entanglement-Breaking Threshold:**
For any dimension `d ≥ 2`, any PPT map `T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)`,
and **any** exponent `M : ℕ` with `2 * (d - 1) ≤ M` (both even and odd `M`!),
the power `T ^ M` is entanglement breaking. -/
theorem isEntanglementBreaking_pow_of_le (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (hT : IsPPTMap T)
    (M : ℕ) (hM : 2 * (d - 1) ≤ M) :
    IsEntanglementBreaking (T ^ M) := by
  have h_base : IsEntanglementBreaking (T ^ (2 * (d - 1))) :=
    isEntanglementBreaking_pow hT (d - 1) (by rw [Fintype.card_fin]; omega)
  exact IsEntanglementBreaking.pow_of_le hT.1 h_base hM

/-- For any dimension `d ≥ 2`, any PPT map `T`, and any exponent `M ≥ 2 * (d - 1)`,
the entanglement-breaking index of `T ^ M` is exactly `1`. -/
theorem ebIndex_pow_of_le_eq_one (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (hT : IsPPTMap T)
    (M : ℕ) (hM : 2 * (d - 1) ≤ M) :
    ebIndex (T ^ M) = 1 :=
  ebIndex_eq_one_of_isEntanglementBreaking (isEntanglementBreaking_pow_of_le d hd T hT M hM)

end Qatlib.Papers.PPTCompose26.Composition
