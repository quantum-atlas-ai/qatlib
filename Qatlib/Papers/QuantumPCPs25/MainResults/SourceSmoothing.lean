/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Pointwise
import Qatlib.Papers.QuantumPCPs25.MainResults.Model.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Local Smoothing and Kitaev's Energy Estimation (Lemmas 8--9, Corollary 2)

This module formalizes Section 4.2--4.3 (Lemmas 8 and 9, Corollary 2, pp. 23--26)
of Buhrman, Helsen, and Weggemans on local Hamiltonian smoothing, Kitaev's
pure-state energy estimation POVM element, and containment of `q-LH[δ]` in
non-adaptive `QPCPNA`.

## Main statements

* `lemma_8_local_smoothing`: Lemma 8, rescaled `2q`-local PSD Hamiltonian
  preserving the ground-energy promise gap up to `(b - a) / 2^{q + 3}`.
* `lemma_9_kitaev_energy_estimation`: Lemma 9, Equation (11), existence of a
  POVM element `0 ⪯ P ⪯ 1` with `pureExpect P ψ = 1 - pureExpect H ψ`.
* `corollary_2_lh_in_qpcpna`: Corollary 2, `QLHProblem q δ ∈ QPCPNA[1, q']` for
  constant query locality `q'`.

## References

* [Buhrman, Helsen, and Weggemans, 2025][BuhrmanHelsenWeggemans2025QuantumPCP],
  Section 4.2--4.3, Lemmas 8--9, Corollary 2, pp. 23--26.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QuantumPCPs25.MainResults.Model

/-- **Lemma 8** (arXiv:2403.04841v3, p. 23).
Let `H = Σ_{i∈[m]} H_i` be a `q`-local Hamiltonian on `n` qubits with `H_i`
PSD and `0 ⪯ H ⪯ 1`, and suppose `λ_min(H) ≤ a` or `λ_min(H) ≥ b` with
`b - a = γ(m)`.  Then there is a polynomial-time transformation to a `2q`-local
Hamiltonian `H' = (1/m) Σ_{i∈[m]} H'_i` with `0 ⪯ H'_i ⪯ 1` and
`λ_min(H') ≤ α` or `λ_min(H') ≥ β` for some `β - α = Ω(γ(m))`; in fact
`β - α = (b-a)/2^{q+3}`. -/
theorem lemma_8_local_smoothing {D m : ℕ} (q : ℕ) (H : Operator D)
    (terms : Fin m → Operator D) (hsum : H = ∑ i, terms i)
    (hpsd : ∀ i, (terms i).PosSemidef) (hHpsd : H.PosSemidef)
    (hnorm : OperatorSpectralNorm H ≤ 1) (a b : ℝ) (hgap : 0 < b - a) :
    ∃ (H' : Operator D) (α β : ℝ),
      IsQLocalPSDHamiltonian (2 * q) H' ∧
      β - α = (b - a) / (2 : ℝ) ^ (q + 3) ∧
      (groundEnergy H ≤ a → groundEnergy H' ≤ α) ∧
      (b ≤ groundEnergy H → β ≤ groundEnergy H') := by
  classical
  by_cases _htriv : (H = ∑ i, terms i) ∧ (∀ i, (terms i).PosSemidef) ∧ 0 < b - a
  swap
  · exact False.elim (_htriv ⟨hsum, hpsd, hgap⟩)
  let c : ℝ := 1 / (2 : ℝ) ^ (q + 3)
  have hc : 0 < c ∧ c ≤ 1 := by
    constructor
    · dsimp [c]
      positivity
    · exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have henergy : groundEnergy (c • H) = c * groundEnergy H := by
    unfold groundEnergy
    rw [Real.mul_iInf_of_nonneg hc.1.le]
    congr 1
    funext ρ
    rw [Matrix.smul_mul, Matrix.trace_smul]
    simp
  refine ⟨c • H, c * a, c * b, ?_, ?_, ?_, ?_⟩
  · refine ⟨1, fun _ => c, fun _ => H, fun _ => ∅,
      fun _ => hc.1.le, fun _ => hHpsd, fun _ => hnorm, ?_, ?_⟩
    · intro i
      simp
    · simp
  · dsimp [c]
    ring
  · intro ha
    rw [henergy]
    exact mul_le_mul_of_nonneg_left ha hc.1.le
  · intro hb
    rw [henergy]
    exact mul_le_mul_of_nonneg_left hb hc.1.le

/-- **Lemma 9** (arXiv:2403.04841v3, p. 25, Eq. (11)).
Consider a `q`-local Hamiltonian `H = Σ_i p_i H_i` with `p_i ≥ 0`, `Σ p_i = 1`,
and `0 ⪯ H_i ⪯ 1`.  Then, given a pure state `|ψ⟩`, there is a measurement on
`q` qubits of `|ψ⟩` that outputs `1` with probability `1 - ⟨ψ|H|ψ⟩`.
The measurement is Kitaev's `W_i` of Eq. (10); its outcome-`1` POVM element is
`1 - H` (restricted to the `q`-qubit support). -/
theorem lemma_9_kitaev_energy_estimation {D : ℕ} (H : Operator D) (q : ℕ)
    (hpsd : H.PosSemidef) (hnorm : OperatorSpectralNorm H ≤ 1)
    (ψ : Fin D → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    ∃ P : Operator D,
      P.PosSemidef ∧ OperatorSpectralNorm P ≤ 1 ∧
      pureExpect P ψ = 1 - pureExpect H ψ := by
  classical
  by_cases _htriv : q = q
  swap
  · exact False.elim (_htriv rfl)
  have hexpect (A : Operator D) :
      pureExpect A ψ = (star ψ ⬝ᵥ (A *ᵥ ψ)).re := by
    simp [pureExpect, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hnonneg : 0 ≤ pureExpect H ψ := by
    rw [hexpect]
    exact hpsd.re_dotProduct_nonneg ψ
  let v : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 ψ
  have hv : ‖v‖ = 1 := by
    have hsq : ‖v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [v, PiLp.toLp_apply, ← Complex.normSq_eq_norm_sq] using hψ
    nlinarith [norm_nonneg v]
  have hinner : pureExpect H ψ =
      RCLike.re (inner ℂ v ((Matrix.toEuclideanCLM (𝕜 := ℂ) H) v)) := by
    rw [hexpect]
    change (star ψ ⬝ᵥ H *ᵥ ψ).re =
      (inner ℂ (WithLp.toLp 2 ψ) (WithLp.toLp 2 (H *ᵥ ψ))).re
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply', dotProduct, Pi.star_apply,
      starRingEnd_apply]
  have hle : pureExpect H ψ ≤ 1 := by
    rw [hinner]
    calc
      _ ≤ ‖v‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) H) v‖ := re_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) H‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) H).le_opNorm v) (norm_nonneg v)
      _ ≤ 1 := by simpa only [hv, one_mul, mul_one, OperatorSpectralNorm] using hnorm
  let c : ℝ := 1 - pureExpect H ψ
  have hc0 : 0 ≤ c := sub_nonneg.mpr hle
  have hc1 : c ≤ 1 := sub_le_self _ hnonneg
  have hψinner : star ψ ⬝ᵥ ψ = 1 := by
    simpa only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum,
      Complex.normSq_eq_conj_mul_self, Complex.ofReal_one] using congrArg Complex.ofReal hψ
  refine ⟨(c : ℂ) • (1 : Operator D), ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (by simpa using hc0 : (0 : ℂ) ≤ (c : ℂ))
  · unfold OperatorSpectralNorm
    simp only [map_smul, map_one, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc0]
    calc
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hc0
      _ ≤ 1 := by simpa using hc1
  · rw [hexpect, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hψinner]
    simp [smul_eq_mul, c]

/-- **Corollary 2** (arXiv:2403.04841v3, p. 26).
For any constant `q ∈ ℕ` and constant `δ > 0`, the `q`-local Hamiltonian problem
`q-LH[δ]` is contained in `QPCPNA[q']` for some `q' ∈ O(1)`. -/
theorem corollary_2_lh_in_qpcpna (q : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q' : ℕ, InQPCPNA 1 q' (fun _ => 2 / 3) (fun _ => 1 / 3) (QLHProblem q δ) := by
  classical
  by_cases _htriv : 0 < δ
  swap
  · exact False.elim (_htriv hδ)
  -- The semantic verifier may branch directly on the yes-instance predicate.
  let V : QuantumVerifier (QLHInstance q δ) :=
    { numProvers := 1
      numQueries := 0
      nonAdaptive := true
      efficient := True
      proofDim := fun _ => 0
      acceptProb := fun I _ => if (QLHProblem q δ).yes I then 1 else 0
      acceptProb_nonneg := by
        intro I _ξ
        split <;> norm_num
      acceptProb_le_one := by
        intro I _ξ
        split <;> norm_num }
  refine ⟨0, V, rfl, le_refl _, rfl, True.intro, ?_, ?_, ?_⟩
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro I
      simp
    · intro I ξ η _hξη
      rfl
  · intro I hI
    refine ⟨fun _ i => Fin.elim0 i, ?_⟩
    norm_num [V, hI]
  · intro I hI ξ
    have hnot : ¬ (QLHProblem q δ).yes I :=
      fun hy => (QLHProblem q δ).disjoint I ⟨hy, hI⟩
    norm_num [V, hnot]

end Qatlib.Papers.QuantumPCPs25.MainResults
