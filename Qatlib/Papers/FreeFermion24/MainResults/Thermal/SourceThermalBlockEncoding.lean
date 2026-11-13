/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceThermalBlockEncoding

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.Thermal

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding (BlockCorner)
open Qatlib.Foundations.PureStateMath (TensorGate tensorGate_apply tensorGate_unitary)

private def twoLevel (m : ℕ) (j₀ j₁ : Fin (2 ^ m)) (c t : ℝ) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun a b =>
    if a = j₀ then
      (if b = j₀ then (c : ℂ) else 0) + (if b = j₁ then (t : ℂ) else 0)
    else if a = j₁ then
      (if b = j₀ then (t : ℂ) else 0) - (if b = j₁ then (c : ℂ) else 0)
    else if a = b then 1 else 0

private lemma twoLevel_mul_apply (m : ℕ) (j₀ j₁ : Fin (2 ^ m))
    (c t : ℝ) (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (a b : Fin (2 ^ m)) :
    (twoLevel m j₀ j₁ c t * M) a b =
      if a = j₀ then (c : ℂ) * M j₀ b + (t : ℂ) * M j₁ b
      else if a = j₁ then (t : ℂ) * M j₀ b - (c : ℂ) * M j₁ b
      else M a b := by
  by_cases ha₀ : a = j₀
  · subst a
    simp [Matrix.mul_apply, twoLevel, add_mul, ite_mul, Finset.sum_add_distrib]
  · by_cases ha₁ : a = j₁
    · subst a
      simp [Matrix.mul_apply, twoLevel, ha₀, ite_mul, sub_mul, Finset.sum_sub_distrib]
    · simp [Matrix.mul_apply, twoLevel, ha₀, ha₁, ite_mul]

private lemma twoLevel_unitary (m : ℕ) (j₀ j₁ : Fin (2 ^ m)) (h₀₁ : j₀ ≠ j₁)
    (c t : ℝ) (hct : c ^ 2 + t ^ 2 = 1) :
    twoLevel m j₀ j₁ c t ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
  have hstar : (twoLevel m j₀ j₁ c t)ᴴ = twoLevel m j₀ j₁ c t := by
    ext a b
    by_cases ha₀ : a = j₀ <;> by_cases ha₁ : a = j₁ <;>
      by_cases hb₀ : b = j₀ <;> by_cases hb₁ : b = j₁ <;>
      simp_all [twoLevel, Matrix.conjTranspose_apply, eq_comm]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hstar]
  have hct' : (c : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by exact_mod_cast hct
  ext a b
  rw [twoLevel_mul_apply]
  by_cases ha₀ : a = j₀ <;> by_cases ha₁ : a = j₁ <;>
    by_cases hb₀ : b = j₀ <;> by_cases hb₁ : b = j₁ <;>
    simp_all [twoLevel, Matrix.one_apply, eq_comm, pow_two] <;> ring_nf at hct' ⊢
  all_goals assumption

private lemma diagonal_dilation (m N : ℕ) (j₀ j₁ : Fin (2 ^ m)) (h₀₁ : j₀ ≠ j₁)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) :
    ∃ D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ,
      D ∈ Matrix.unitaryGroup (Fin (2 ^ m) × Fin N) ℂ ∧
      BlockCorner D j₀ = Matrix.diagonal (fun i => (c i : ℂ)) := by
  let R := fun i => twoLevel m j₀ j₁ (c i) (Real.sqrt (1 - c i ^ 2))
  have hR : ∀ i, R i ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    intro i
    apply twoLevel_unitary m j₀ j₁ h₀₁
    rw [Real.sq_sqrt (by nlinarith [(hc i).1, (hc i).2])]
    ring
  let D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ :=
    fun a b => if a.2 = b.2 then R a.2 a.1 b.1 else 0
  refine ⟨D, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, D]
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, eq_comm] using
        congrFun (congrFun ((Matrix.mem_unitaryGroup_iff.mp (hR i))) a) b
    · simp [hij, eq_comm]
  · ext i j
    by_cases hij : i = j <;>
      simp [BlockCorner, D, R, twoLevel, h₀₁, hij]

private lemma corner_conjugate (m N : ℕ)
    (D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ)
    (V W : Matrix (Fin N) (Fin N) ℂ) (j₀ : Fin (2 ^ m)) :
    BlockCorner (TensorGate 1 V * D * TensorGate 1 W) j₀ =
      V * BlockCorner D j₀ * W := by
  ext i j
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply, ite_mul, mul_ite]

/-- The logarithmic factor `log^{5/2}(16 s^9 β^8/(ε_PA^2 ε_p(h)^2))` of Theorem 16
(arXiv:2409.04550, Eq. (D3)/(D4)); the `max … 1` makes it total for degenerate
parameters. -/
def thm16LogFactor (s : ℕ) (β εPA εp : ℝ) : ℝ :=
  Real.rpow (Real.log (max (16 * (s : ℝ) ^ 9 * β ^ 8 / (εPA ^ 2 * εp ^ 2)) 1))
    (5 / 2 : ℝ)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem9_blockEncoding_thermalM`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem9_blockEncoding_thermalM_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (β ε : ℝ) (na : ℕ)
    (hβpos : 0 < β) (hε : 0 < ε)
    (hβ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ)) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (thermalMQuarter h β) 1 ε,
      B.m = n + 5 ∧
      PolyOverEps B.cost.oracleCalls n ε ∧
      AncillaShape B.cost.ancillaryQubits n na ε ∧
      GateShape B.cost.gates n ε ∧
      ClassicalShape B.cost.classicalTime n ε

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem16_thermalM_resources`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem16_thermalM_resources_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (β εPA εp δc : ℝ) (na : ℕ)
    (hβ : 0 < β) (hεPA : 0 < εPA) (hεp : 0 ≤ εp) (hδ : 0 < δc) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (thermalMQuarter h β) 1 (εPA + εp + δc),
      B.m = n + 5 ∧
      (if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
          ThetaBound B.cost.oracleCalls
            (β ^ 4 * (s : ℝ) ^ 4 / εPA ^ 2) (β ^ 4 * (s : ℝ) ^ 4 / εPA ^ 2)
        else
          ThetaBound B.cost.oracleCalls
            (β ^ 2 * (s : ℝ) ^ 2 / εPA) (β ^ 2 * (s : ℝ) ^ 2 / εPA)) ∧
      BigO B.cost.ancillaryQubits
        ((s : ℝ) * (n : ℝ) + (na : ℝ) + thm16LogFactor s β εPA εp) ∧
      BigO B.cost.gates
        ((n : ℝ) + ((n : ℝ) + 4) * β ^ 4 * (s : ℝ) ^ 4 / εPA +
          thm16LogFactor s β εPA εp) ∧
      PolyTwo B.cost.classicalTime (β ^ 4 * (s : ℝ) ^ 4 / εPA) (Real.log (1 / δc))

end Qatlib.Papers.FreeFermion24.MainResults.Thermal
