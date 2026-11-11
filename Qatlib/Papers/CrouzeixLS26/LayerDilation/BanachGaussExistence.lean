/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.BanachPolynomial
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule

set_option backward.isDefEq.respectTransparency false

/-!
# Banach Gauss Existence

G19: one actual positive Gauss rule has finite-vector polynomial exactness and uniform-approximation stability for every real Banach space.
-/
open Qatlib.Foundations.OpCalculus.ContourCalc


set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib.Concepts.LchsSimulation.Quadrature Set MeasureTheory
open scoped BigOperators

/-- G19: one actual positive Gauss rule has finite-vector polynomial exactness
and uniform-approximation stability for every real Banach space. -/
theorem banach_gauss_stability (Q : ℕ) (a h : ℝ) (hQ : 1 ≤ Q) (hh : 0 < h) :
    ∃ node weight : Fin Q → ℝ,
      (∀ q, node q ∈ Icc a (a + h)) ∧ (∀ q, 0 < weight q) ∧
      (∑ q, weight q) = h ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (K : ℕ) (c : Fin (K + 1) → E), K ≤ 2 * Q - 1 →
        (∫ t in a..a + h, finiteVectorPolynomial K c t) =
          ∑ q, weight q • finiteVectorPolynomial K c (node q)) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (f : ℝ → E) (K : ℕ) (c : Fin (K + 1) → E) (ε : ℝ),
        IntervalIntegrable f volume a (a + h) → K ≤ 2 * Q - 1 → 0 ≤ ε →
        (∀ t ∈ Icc a (a + h), ‖f t - finiteVectorPolynomial K c t‖ ≤ ε) →
        ‖(∫ t in a..a + h, f t) - ∑ q, weight q • f (node q)‖ ≤ 2 * h * ε) := by
  obtain ⟨node₀, weight₀, hnode₀, _, hweight₀, hexact₀, _⟩ :=
    gauss_legendre_rule_exists Q hQ
  let node : Fin Q → ℝ := fun q => a + h * (node₀ q + 1) / 2
  let weight : Fin Q → ℝ := fun q => (h / 2) * weight₀ q
  have hnode : ∀ q, node q ∈ Icc a (a + h) := by
    intro q
    have hn := hnode₀ q
    have hlo : 0 < h * (node₀ q + 1) :=
      mul_pos hh (by linarith [hn.1])
    have hhi : 0 < h * (1 - node₀ q) :=
      mul_pos hh (by linarith [hn.2])
    dsimp [node]
    constructor <;> nlinarith
  have hweight : ∀ q, 0 < weight q := by
    intro q
    exact mul_pos (div_pos hh (by norm_num)) (hweight₀ q)
  have hsum : (∑ q, weight q) = h := by
    dsimp [weight]
    rw [← Finset.mul_sum, gauss_rule_weight_sum Q node₀ weight₀ hexact₀]
    ring
  have hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      (∫ t in a..a + h, p.eval t) = ∑ q, weight q * p.eval (node q) := by
    intro p hp
    exact gauss_cell_rule_affine_exact Q a h node₀ weight₀ hexact₀ p hp
  have hvector : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (K : ℕ) (c : Fin (K + 1) → E), K ≤ 2 * Q - 1 →
      (∫ t in a..a + h, finiteVectorPolynomial K c t) =
        ∑ q, weight q • finiteVectorPolynomial K c (node q) := by
    intro E _ _ _ K c hK
    exact finiteVectorPolynomial_rule_exact Q a h node weight hexact K c hK
  refine ⟨node, weight, hnode, hweight, hsum, hvector, ?_⟩
  intro E _ _ _ f K c ε hf hK hε hbound
  exact positive_rule_banach_error_le Q a h node weight f (finiteVectorPolynomial K c) ε
    hh hnode (fun q => (hweight q).le) hsum hf
    ((finiteVectorPolynomial_continuous K c).intervalIntegrable a (a + h))
    (hvector E K c hK) hε hbound

end Qatlib.Papers.CrouzeixLS26.LayerDilation
