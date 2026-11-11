/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Basic

set_option backward.isDefEq.respectTransparency false

/-! Error bound for direct Heisenberg sewing in
"Generative quantum advantage for classical and quantum problems"
(arXiv:2509.09033v1, 2025).

Theorem 6 of the paper: if for each site `i` the learned Pauli
expansion satisfies `Σ_P ‖Ô_{i,P} − U†P_iU‖ ≤ ε_i`, then the sewn
`2n`-qubit unitary obeys `‖U_sew − U†⊗U‖_∞ ≤ Σ_i ε_i` (and the
learned channel obeys `‖Ê − 𝒰‖_◇ ≤ 2Σ_i ε_i`).

The paper's proof is a telescoping product estimate
`‖∏W_i − ∏V_i‖ ≤ Σ‖W_i − V_i‖`, valid because every factor is
unitary hence has operator norm `1`, followed by the per-site
triangle inequality `‖W_i − V_i‖ ≤ 2‖W̃_i − V_i‖` (projection onto
unitaries is a nearest-point contraction) and the `½Σ_P` tensor
bound. This file proves the **telescoping core verbatim** (ordered
products, as the site order `i = 1..n` matters for noncommuting
factors):

- `specNorm` is the spectral (operator) norm, realised as the
  continuous-linear-map norm of `Matrix.toEuclideanCLM`.
- `specNorm_prod_le_one`: ordered products of spectral-norm-`≤ 1`
  factors have spectral norm `≤ 1`.
- `telescoping_bound`: **the paper's telescoping identity** —
  `‖∏_i W_i − ∏_i V_i‖ ≤ Σ_i ‖W_i − V_i‖` for factor families of
  spectral norm `≤ 1` (unitaries in particular), over any ordered
  site list.
- `direct_sewing_bound`: the compiled Theorem-6 shape with the
  per-site errors `ε_i` as hypotheses.

The unitary-to-norm-`1` step, the nearest-unitary projection
contraction, the tensor norm identity and the diamond-norm doubling
`‖Ad_V − Ad_W‖_◇ ≤ 2‖V − W‖_∞` are the cited standard facts the
paper uses without proof; they are abstracted as hypotheses here.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.GenerativeAdv25.MainResults.SewingError

open scoped Matrix

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The spectral (operator) norm of a complex matrix: the operator
norm of its action on Euclidean space. -/
noncomputable def specNorm (A : Matrix d d ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) A‖

/-- The spectral norm is non-negative. -/
lemma specNorm_nonneg (A : Matrix d d ℂ) : 0 ≤ specNorm A := norm_nonneg _

/-- The spectral norm is sub-multiplicative. -/
lemma specNorm_mul_le (A B : Matrix d d ℂ) :
    specNorm (A * B) ≤ specNorm A * specNorm B := by
  have h : Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (A * B)
      = Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) A
        * Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) B :=
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).map_mul A B
  unfold specNorm
  rw [h]
  exact norm_mul_le _ _

/-- The spectral norm satisfies the triangle inequality. -/
lemma specNorm_add_le (A B : Matrix d d ℂ) :
    specNorm (A + B) ≤ specNorm A + specNorm B := by
  unfold specNorm
  rw [map_add]
  exact norm_add_le _ _

/-- An ordered product of spectral-norm-`≤ 1` factors has spectral
norm `≤ 1` (unitary factors in particular). -/
theorem specNorm_prod_le_one {ι : Type} (l : List ι) (V : ι → Matrix d d ℂ)
    (hV : ∀ i ∈ l, specNorm (V i) ≤ 1) :
    specNorm ((l.map V).prod) ≤ 1 := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, specNorm, map_one,
        ContinuousLinearMap.one_def]
      exact ContinuousLinearMap.norm_id_le
  | cons a l ih =>
      have hVl : ∀ i ∈ l, specNorm (V i) ≤ 1 :=
        fun i hi => hV i (List.mem_cons_of_mem a hi)
      rw [List.map_cons, List.prod_cons]
      calc specNorm (V a * (l.map V).prod)
          ≤ specNorm (V a) * specNorm ((l.map V).prod) := specNorm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hV a List.mem_cons_self) (ih hVl)
            (specNorm_nonneg _) zero_le_one
        _ ≤ 1 := by norm_num

/-- **The paper's telescoping identity (Theorem 6 proof)**: for two
families of factors with spectral norm at most `1` (`V i` the ideal
site unitaries, `W i` the projected learned ones), over any ordered
site list,

`‖∏_i W_i − ∏_i V_i‖ ≤ ∑_i ‖W_i − V_i‖`. -/
theorem telescoping_bound {ι : Type} (l : List ι) (V W : ι → Matrix d d ℂ)
    (hV : ∀ i ∈ l, specNorm (V i) ≤ 1) (hW : ∀ i ∈ l, specNorm (W i) ≤ 1) :
    specNorm ((l.map W).prod - (l.map V).prod)
      ≤ (l.map (fun i => specNorm (W i - V i))).sum := by
  induction l with
  | nil => simp [specNorm]
  | cons a l ih =>
      have hkey : W a * (l.map W).prod - V a * (l.map V).prod
          = W a * ((l.map W).prod - (l.map V).prod)
              + (W a - V a) * (l.map V).prod := by
        calc W a * (l.map W).prod - V a * (l.map V).prod
            = (W a * (l.map W).prod - W a * (l.map V).prod)
                + (W a * (l.map V).prod - V a * (l.map V).prod) := by abel
          _ = W a * ((l.map W).prod - (l.map V).prod)
                + (W a - V a) * (l.map V).prod := by rw [mul_sub, sub_mul]
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        List.map_cons, List.sum_cons, hkey]
      have hVl : ∀ i ∈ l, specNorm (V i) ≤ 1 := fun i hi => hV i (List.mem_cons_of_mem a hi)
      have hWl : ∀ i ∈ l, specNorm (W i) ≤ 1 := fun i hi => hW i (List.mem_cons_of_mem a hi)
      calc specNorm (W a * ((l.map W).prod - (l.map V).prod)
              + (W a - V a) * (l.map V).prod)
          ≤ specNorm (W a * ((l.map W).prod - (l.map V).prod))
              + specNorm ((W a - V a) * (l.map V).prod) := specNorm_add_le _ _
        _ ≤ specNorm (W a) * specNorm ((l.map W).prod - (l.map V).prod)
              + specNorm (W a - V a) * specNorm ((l.map V).prod) :=
                add_le_add (specNorm_mul_le _ _) (specNorm_mul_le _ _)
        _ ≤ 1 * (l.map (fun i => specNorm (W i - V i))).sum
              + specNorm (W a - V a) * 1 := by
                refine add_le_add ?_ ?_
                · exact le_trans
                    (mul_le_mul_of_nonneg_right (hW a List.mem_cons_self)
                      (specNorm_nonneg _))
                    (mul_le_mul_of_nonneg_left (ih hVl hWl) zero_le_one)
                · exact mul_le_mul_of_nonneg_left
                    (specNorm_prod_le_one l V hVl) (specNorm_nonneg _)
        _ = specNorm (W a - V a) + (l.map (fun i => specNorm (W i - V i))).sum := by ring

/-- **Theorem 6 (compiled shape)**: if every factor family has
spectral norm at most `1` and the per-site sewing error is at most
`ε i`, then the sewn ordered product deviates from the ideal ordered
product by at most `∑ ε i` in spectral norm. The per-site bound
`‖W i − V i‖ ≤ ε i` collects the paper's projection-contraction
(`≤ 2‖W̃ i − V i‖`) and `½Σ_P` tensor steps, which use cited
standard facts. -/
theorem direct_sewing_bound {ι : Type} (l : List ι) (V W : ι → Matrix d d ℂ)
    (hV : ∀ i ∈ l, specNorm (V i) ≤ 1) (hW : ∀ i ∈ l, specNorm (W i) ≤ 1)
    (ε : ι → ℝ) (hsite : ∀ i ∈ l, specNorm (W i - V i) ≤ ε i) :
    specNorm ((l.map W).prod - (l.map V).prod) ≤ (l.map ε).sum :=
  (telescoping_bound l V W hV hW).trans (List.sum_le_sum hsite)

end Qatlib.Papers.GenerativeAdv25.MainResults.SewingError
