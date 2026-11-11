/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma3.MQSPInversion
import Qatlib.Papers.QSPIto26.MainResults.Lemma4.MQSPDegreeEquality

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 — `P` is a nonzero Laurent polynomial

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 5 (Appendix A, p. 12), Eq. (36).

Lemma 5. If `(P,Q)` is constructible by m-variable M-QSP in `n` steps, then `P ≠ 0`.

The composition below is complete: it uses Lemma 3 (c004, fully proved) for the
antisymmetry `Q(a^{-1}) = -Q(a)`, the `SU(2)` determinant identity
`P · P^* + Q · Q^* = 1` (fully proved in the Lemma 4 module), and Lemma 4 (c005)
through its interface form. The only external hypothesis is the lex-leading-monomial
degree fact `deg_{a_j}(X · X^*) = 2 deg_{a_j} X` for `X ≠ 0`, the same interface
hypothesis as Lemma 4.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma5

open Qatlib.Papers.QSPIto26.MainResults.Core

/-- Interface version of Lemma 5. Assuming the lex-leading-monomial degree fact
(Eqs. (31)--(32), the interface hypothesis of Lemma 4), the polynomial `P` of a
constructible pair is nonzero: if `P = 0` then Lemma 4 forces every `deg_{a_j} Q`
to vanish, so `Q` is a constant; Lemma 3 makes that constant odd under `a ↦ a^{-1}`,
hence zero; the determinant identity then reads `0 = 1`. -/
theorem lemma5_nonzero {m n : ℕ} (P Q : MLaurent m) (h : Constructible n P Q)
    (hlead : ∀ (X : MLaurent m) (j : Fin m), X ≠ 0 →
      degVar j (X * starOp X) = 2 * degVar j X) :
    P ≠ 0 := by
  intro h0
  subst h0
  have hid := Lemma4.det_identity 0 Q h
  -- Lemma 4 (interface): every `a_j`-degree of `Q` vanishes
  have h4 : ∀ j : Fin m, degVar j Q = 0 := by
    intro j
    have hj := Lemma4.lemma4_degree_eq 0 Q h hlead j
    rw [Lemma4.degVar_zero] at hj
    exact hj.symm
  -- hence the support of `Q` is contained in `{0}` and `Q` is a constant
  have hsupp : Q.coeff.support ⊆ {0} := by
    intro k hk
    refine Finset.mem_singleton.mpr (funext fun j => ?_)
    have hkj : Int.natAbs (k j) ≤ degVar j Q :=
      Finset.le_sup (f := fun x => Int.natAbs (x j)) hk
    rw [h4 j] at hkj
    simpa using hkj
  have hQ : Q = C' (Q.coeff 0) := by
    apply AddMonoidAlgebra.coeff_injective
    simpa only [C', AddMonoidAlgebra.coeff_single] using
      (Finsupp.support_subset_singleton.mp hsupp)
  -- Lemma 3: `Q(a^{-1}) = -Q(a)`, so the constant satisfies `c = -c`
  obtain ⟨_, h3⟩ := Lemma3.lemma3_inversion 0 Q h
  rw [hQ, Lemma3.substInv_C'] at h3
  have hcong := congrArg (fun X : MLaurent m => X.coeff (0 : ExpVec m)) h3
  simp [C', AddMonoidAlgebra.coeff_neg] at hcong
  have h0e : (2 : ℂ) * Q.coeff 0 = 0 := by linear_combination hcong
  have hQ0 : Q.coeff 0 = 0 := by
    rcases mul_eq_zero.mp h0e with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  have hC0 : C' (Q.coeff 0) = (0 : MLaurent m) := by
    rw [hQ0]
    apply AddMonoidAlgebra.coeff_injective
    simp [C']
  -- `Q = 0` turns the determinant identity into `0 = 1`
  have hQz : Q = (0 : MLaurent m) := hQ.trans hC0
  rw [hQz] at hid
  simp at hid

end Qatlib.Papers.QSPIto26.MainResults.Lemma5
