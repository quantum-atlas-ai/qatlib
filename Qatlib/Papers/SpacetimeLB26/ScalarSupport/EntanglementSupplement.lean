/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement

/-! # Scalar support retained from the original SpacetimeLB26 contribution

This file proves conditional arithmetic or abstract combinatorial implications. Its
hypotheses must be read literally: final overlap, survival, contraction, code existence,
distance or threshold fields are not constructions of the corresponding physical objects.
The paper metadata records these interfaces as partial support, separately from the
new native Bell and adaptive erasure producers. Fixed source: arXiv2608.26272v1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement

open Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement

open scoped BigOperators
open Finset

/-! ## Lemma 3 — Bell-state witness -/

/-! ## Lemma 4 — singlet fraction from Schmidt number -/

/-! ## Lemma 5 — entanglement contraction for `m` noisy qubits -/

/-! A concrete boundary of Lemma 5: when the contraction parameter is one,
the named one-step inequality forces the revised functional to vanish. -/
/-- Unit contraction parameter forces the next scalar entanglement value to be nonpositive. -/
theorem entanglement_contraction_kappa_one
    (m : ℕ) (_hm : 1 ≤ m) (Echi_before Echi_after : ℝ)
    (_hbefore : 0 ≤ Echi_before)
    (hRef19 : Echi_after ≤ (1 - (1 : ℝ) ^ (m : ℝ)) * Echi_before) :
    Echi_after ≤ 0 := by
  norm_num at hRef19
  exact hRef19

/-! A finite constant-width corollary of the iterated contraction interface. -/

/-- If every one of `S` successive steps has the same noisy width `m`, then the
iterated contraction bound is the finite geometric estimate
`E S ≤ (1 − κ^m)^S E 0`.  This is a scalar corollary of the supplied per-step
inequality; it does not construct a channel or identify the functional with a
physical entanglement measure. -/
theorem entanglement_contraction_constant_width
    (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (m S : ℕ) (E : ℕ → ℝ) (hE0 : 0 ≤ E 0)
    (hstep : ∀ i : ℕ, E (i + 1) ≤ (1 - κ ^ (m : ℝ)) * E i) :
    E S ≤ (1 - κ ^ (m : ℝ)) ^ S * E 0 := by
  have hiter := entanglement_contraction_iterated κ hκ0 hκ1
    (fun _ : ℕ => m) E hE0 (by
      intro i
      simpa using hstep i) S
  simpa [Finset.prod_const] using hiter

/-! ## Lemma 10 — complete erasure and the reference -/

/-- The scalar contraction multiplier belongs to the unit interval. -/
theorem entanglement_contraction_factor_mem_Icc
    (m : ℕ) (κN : ℝ) (hκ0 : 0 < κN) (hκ1 : κN ≤ 1) :
    1 - κN ^ (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpow_nonneg : 0 ≤ κN ^ (m : ℝ) :=
    (Real.rpow_pos_of_pos hκ0 _).le
  have hpow_le : κN ^ (m : ℝ) ≤ 1 :=
    Real.rpow_le_one hκ0.le hκ1 (by positivity)
  constructor <;> linarith


end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement
