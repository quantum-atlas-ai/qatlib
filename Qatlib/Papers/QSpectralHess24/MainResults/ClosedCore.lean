/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSpectralHess24.MainResults.Core.OracleModel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! An arithmetic basis-permutation oracle and finite Gaussian test-family energy bounds. No gradient or Hessian estimation algorithm is asserted. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Classical ComplexOrder

namespace Qatlib.Papers.QSpectralHess24.MainResults.ClosedCore
open Qatlib.Papers.QSpectralHess24.MainResults.Core
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

/-! Mathematical identities for the source model. -/

/-- **Lemma 2.3 (arXiv:2407.03833v2, p.10, Equation (2.1)).**
For values `a, b, c` in a finite additive value register, the map
`|a⟩|b⟩ ↦ |a⟩|b + a c⟩` is implemented by a unitary. Here `mulC` is the function
`a ↦ a * c` for the fixed constant `c` of the lemma (`c` is absorbed into `mulC`,
since the paper only needs one fixed `c`). The proof exhibits the permutation matrix
of the bijection `(a, b) ↦ (a, b + mulC a)` and uses that permutation matrices are
unitary.

Original proof: the paper observes that `(a, b) ↦ (a, b + ac)` is a bijection of the
finite value set and hence a permutation, implemented by a permutation matrix
(Equations (2.1)–(2.3)); the inverse map subtracts `ac`. -/
theorem arithmeticOracle {β : Type} [Fintype β] [DecidableEq β] [AddGroup β]
    (mulC : β → β) :
    ∃ U : Matrix (β × β) (β × β) ℂ,
      U ∈ Matrix.unitaryGroup (β × β) ℂ ∧
        ∀ a b : β, U *ᵥ (Pi.single (a, b) (1 : ℂ)) =
          Pi.single (a, b + mulC a) (1 : ℂ) := by
  let σ : Equiv.Perm (β × β) :=
    { toFun := fun p => (p.1, p.2 + mulC p.1)
      invFun := fun p => (p.1, p.2 - mulC p.1)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  refine ⟨basisPermMatrix σ, basisPermMatrix_mem_unitaryGroup σ, ?_⟩
  intro a b
  change basisPermMatrix σ *ᵥ Pi.single (a, b) (1 : ℂ) = Pi.single (σ (a, b)) 1
  exact basisPermMatrix_mulVec_single σ (a, b)

/-! ## Proposition 2.5: binary oracle versus phase oracle -/

/-! Mathematical identities for the source model. -/

/-- The Gaussian test function `f_{j,k}(x) = ε x_j x_k e^{−c‖x‖²/2}` of Lemma 6.4. -/
noncomputable def gaussianFamily {d : ℕ} (ε c : ℝ) (j k : Fin d) (x : Fin d → ℝ) : ℝ :=
  ε * x j * x k * Real.exp (-(c * ∑ i, (x i) ^ 2) / 2)

/-- The `d²` members of the test family, indexed by the pair `(j,k)`. -/
noncomputable def gaussianFamilyIndex (d : ℕ) : Type := Fin d × Fin d

instance (d : ℕ) : Fintype (gaussianFamilyIndex d) := by
  unfold gaussianFamilyIndex; infer_instance

instance (d : ℕ) : DecidableEq (gaussianFamilyIndex d) := by
  unfold gaussianFamilyIndex; infer_instance

/-- **Lemma 6.4 (arXiv:2407.03833v2, p.29).**
Let `d ∈ ℕ`, `ε, c ∈ ℝ₊` and `f_*(x) = 0`, `f_{j,k}(x) = ε x_j x_k e^{−c‖x‖²/2}`.
The family `𝓕 = {f_{j,k} : j,k ∈ [d]}` has `d²` members and for all `x ∈ ℝ^d`,
`Σ_{j,k ∈ [d]} |f_{j,k}(x) − f_*(x)|² ≤ 4ε²/(e²c²)`.

Original proof: `Σ_{j,k} (ε x_j x_k e^{−c‖x‖²/2})² = ε² (Σ_i x_i²)² e^{−c‖x‖²}`, and
with `z := c‖x‖²` one has `z² e^{−z} ≤ 4/e²` (from `z e^{−z} ≤ 1/e` applied to
`z/2`), giving the bound.

**Status.** Fully proved: `gaussianFamily_sum_sq_le` proves the numerical bound and
`gaussianFamilyIndex_card` the cardinality `d²`. -/
theorem gaussianFamily_index_card (d : ℕ) : Fintype.card (gaussianFamilyIndex d) = d ^ 2 := by
  change Fintype.card (Fin d × Fin d) = d ^ 2
  rw [Fintype.card_prod, Fintype.card_fin, sq]

/-- The squared-exponential identity behind Lemma 6.4:
`Σ_{j,k} f_{j,k}(x)^2 = ε² (Σ_i x_i²)² e^{−c Σ_i x_i²}`. -/
theorem gaussianFamily_sum_sq_eq {d : ℕ} (ε c : ℝ) (x : Fin d → ℝ) :
    ∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2 =
      ε ^ 2 * (∑ i, (x i) ^ 2) ^ 2 * Real.exp (-(c * ∑ i, (x i) ^ 2)) := by
  have hexp_sq : ∀ t : ℝ, (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    intro t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hterm : ∀ j k : Fin d,
      (gaussianFamily ε c j k x) ^ 2 =
        ε ^ 2 * (x j) ^ 2 * (x k) ^ 2 * Real.exp (-(c * ∑ i, (x i) ^ 2)) := by
    intro j k
    unfold gaussianFamily
    simp only [mul_pow, hexp_sq]
    rw [show 2 * (-(c * ∑ i, (x i) ^ 2) / 2) = -(c * ∑ i, (x i) ^ 2) from by ring]
  have hprod : (∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2) =
      ∑ j : Fin d, ∑ k : Fin d, (gaussianFamily ε c j k x) ^ 2 := by
    change (∑ p : Fin d × Fin d, (gaussianFamily ε c p.1 p.2 x) ^ 2) = _
    rw [Fintype.sum_prod_type]
  rw [hprod]
  simp only [hterm]
  set E : ℝ := Real.exp (-(c * ∑ i, (x i) ^ 2)) with hE
  set T : ℝ := ∑ k : Fin d, (x k) ^ 2 with hT
  have hstepA : ∀ j : Fin d, (∑ k : Fin d, ε ^ 2 * (x j) ^ 2 * (x k) ^ 2 * E) =
      ∑ k : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * (x k) ^ 2 := by
    intro j
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hstepB : ∀ j : Fin d, (∑ k : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * (x k) ^ 2) =
      (ε ^ 2 * (x j) ^ 2 * E) * T := by
    intro j
    rw [Finset.mul_sum]
  have hstepC : (∑ j : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * T) = ε ^ 2 * E * T * T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTT : (∑ i : Fin d, (x i) ^ 2) ^ 2 = T * T := by
    rw [sq, ← hT]
  rw [hTT]
  simp only [hstepA, hstepB, hstepC]
  ring

/-- **Lemma 6.4, numerical bound.** For `c > 0` and `ε ≥ 0`,
`Σ_{j,k} |f_{j,k}(x) − f_*(x)|² ≤ 4ε²/(e²c²)` with `f_* = 0`. -/
theorem gaussianFamily_sum_sq_le {d : ℕ} (ε c : ℝ) (hc : 0 < c) (_hε : 0 ≤ ε)
    (x : Fin d → ℝ) :
    ∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2 ≤
      4 * ε ^ 2 / (Real.exp 1) ^ 2 / c ^ 2 := by
  rw [gaussianFamily_sum_sq_eq]
  set S : ℝ := ∑ i, (x i) ^ 2 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  -- the scalar inequality `z² e^{−z} ≤ 4/e²` for `z = c S`
  have hexp_sq : ∀ t : ℝ, (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    intro t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hbase : (c * S / 2) * Real.exp (-(c * S / 2)) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one (c * S / 2)
  have hbase2 : c * S * Real.exp (-(c * S / 2)) ≤ 2 * Real.exp (-1) := by
    nlinarith [Real.exp_pos (-(c * S / 2))]
  have hsquare : (c * S * Real.exp (-(c * S / 2))) ^ 2 ≤ (2 * Real.exp (-1)) ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self
      (mul_nonneg (mul_nonneg (le_of_lt hc) hSnn) (le_of_lt (Real.exp_pos _))) hbase2
  have hlhs : (c * S * Real.exp (-(c * S / 2))) ^ 2 = (c * S) ^ 2 * Real.exp (-(c * S)) := by
    simp only [mul_pow, hexp_sq]
    rw [show 2 * (-(c * S / 2)) = -(c * S) from by ring]
  have hrhs : (2 * Real.exp (-1)) ^ 2 = 4 * ((Real.exp 1)⁻¹) ^ 2 := by
    rw [mul_pow, Real.exp_neg]
    ring
  rw [hlhs, hrhs] at hsquare
  -- divide by `c ^ 2`
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hfin : (c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2 ≤
      4 * ((Real.exp 1)⁻¹) ^ 2 / c ^ 2 :=
    div_le_div_of_nonneg_right hsquare (le_of_lt hc2)
  have hconv : ε ^ 2 * S ^ 2 * Real.exp (-(c * S)) =
      ε ^ 2 * ((c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2) := by
    field_simp
  rw [hconv]
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hstep : ε ^ 2 * ((c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2) ≤
      ε ^ 2 * (4 * ((Real.exp 1)⁻¹) ^ 2 / c ^ 2) :=
    mul_le_mul_of_nonneg_left hfin hε2
  refine hstep.trans (le_of_eq ?_)
  rw [inv_pow]
  field_simp

end Qatlib.Papers.QSpectralHess24.MainResults.ClosedCore
