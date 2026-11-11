/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 and Corollary 8 of arXiv:1705.01843v4

These are the two numerical lemmas that turn multiplicative approximations of
the traces `Tr(I/4 · e^{-H})` and `Tr((I+A/2)/4 · e^{-H})` into an additive
approximation of `Tr(A e^{-H}) / Tr(e^{-H})`.  Both are proved here outright;
they do not depend on any quantum-circuit model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound

/-- **Lemma 7** (arXiv:1705.01843v4, p. 8).  Let `0 ≤ θ ≤ 1` and let
`α, α̃, Z, Z̃ > 0` satisfy `|α - α̃| ≤ α θ / 3` and `|Z - Z̃| ≤ Z θ / 3`.
Then `|α/Z - α̃/Z̃| ≤ θ · α/Z`.

Proof route (paper): `Z̃ ≥ (2/3) Z`, and
`α/Z - α̃/Z̃ = (α(Z̃-Z) + Z(α-α̃))/(Z Z̃)`, whose numerator is bounded by
`2 α Z θ/3`; dividing by `Z Z̃ ≥ (2/3) Z²` gives the claim. -/
theorem ratio_error {θ α αt Z Zt : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hα : 0 < α) (hZ : 0 < Z)
    (hA : |α - αt| ≤ α * θ / 3) (hZε : |Z - Zt| ≤ Z * θ / 3) :
    |α / Z - αt / Zt| ≤ θ * (α / Z) := by
  have hZt_lb : (2 / 3) * Z ≤ Zt := by
    have h1 : Z - Zt ≤ Z * θ / 3 := (abs_le.mp hZε).2
    nlinarith
  have hZt : 0 < Zt := by nlinarith
  have hkey : α / Z - αt / Zt = (α * Zt - αt * Z) / (Z * Zt) := by
    rw [div_sub_div _ _ hZ.ne' hZt.ne']
    ring_nf
  rw [hkey, abs_div]
  have hden : 0 < Z * Zt := mul_pos hZ hZt
  rw [abs_of_pos hden, div_le_iff₀ hden]
  have hrhs : θ * (α / Z) * (Z * Zt) = θ * α * Zt := by
    field_simp
  rw [hrhs]
  have hnum : |α * Zt - αt * Z| ≤ α * (Z * θ / 3) + Z * (α * θ / 3) := by
    have e : α * Zt - αt * Z = α * (Zt - Z) + Z * (α - αt) := by ring
    rw [e]
    calc |α * (Zt - Z) + Z * (α - αt)|
        ≤ |α * (Zt - Z)| + |Z * (α - αt)| := abs_add_le _ _
      _ = α * |Zt - Z| + Z * |α - αt| := by
          rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hZ]
      _ = α * |Z - Zt| + Z * |α - αt| := by rw [abs_sub_comm Zt Z]
      _ ≤ α * (Z * θ / 3) + Z * (α * θ / 3) := by
          gcongr
  have hαθ : 0 ≤ α * θ := mul_nonneg hα.le hθ0
  have hmul : α * θ * ((2 / 3) * Z) ≤ α * θ * Zt :=
    mul_le_mul_of_nonneg_left hZt_lb hαθ
  nlinarith [hnum, hmul]

/-- **Corollary 8**, scalar form (arXiv:1705.01843v4, p. 9).  Suppose
`P = Tr((I + A/2)/4 · e^{-H})`, `Q = Tr(I/4 · e^{-H})`, so that
`Tr(A e^{-H})/Tr(e^{-H}) = 2P/Q - 2`; and suppose `|Tr(A e^{-H})/Tr(e^{-H})| ≤ 1`,
which follows from `‖A‖ ≤ 1` and positive semidefiniteness of `e^{-H}`.
Multiplicative `θ/9`-approximations `P̃, Q̃` of `P, Q` then yield the additive
`θ`-estimate `2P̃/Q̃ - 2` of the ratio.

Proof route: apply Lemma 7 with `θ/3` to `(P, Q, P̃, Q̃)` (the hypothesis is
`θ/9 = (θ/3)/3`), then use `P/Q = 1 + ratio/2 ≤ 3/2`. -/
theorem cor8_scalar {θ P Q Phat Qhat ratio : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hQ : 0 < Q) (hP : 0 < P)
    (hratio : ratio = 2 * P / Q - 2) (hratio_abs : |ratio| ≤ 1)
    (hPhat : |P - Phat| ≤ P * (θ / 9)) (hQhat : |Q - Qhat| ≤ Q * (θ / 9)) :
    |2 * Phat / Qhat - 2 - ratio| ≤ θ := by
  have hθ3 : 0 ≤ θ / 3 := by linarith
  have hθ3' : θ / 3 ≤ 1 := by linarith
  have hP' : |P - Phat| ≤ P * (θ / 3) / 3 := by nlinarith
  have hQ' : |Q - Qhat| ≤ Q * (θ / 3) / 3 := by nlinarith
  have h := ratio_error (θ := θ / 3) (α := P) (αt := Phat) (Z := Q) (Zt := Qhat)
    hθ3 hθ3' hP hQ hP' hQ'
  have hratio2 : P / Q = (ratio + 2) / 2 := by
    rw [hratio]
    field_simp
    ring
  have hPQ : P / Q ≤ 3 / 2 := by
    have h1 : ratio ≤ 1 := (abs_le.mp hratio_abs).2
    rw [hratio2]
    linarith
  have e : 2 * Phat / Qhat - 2 - ratio = 2 * (Phat / Qhat - P / Q) := by
    rw [hratio2]
    field_simp
    ring
  rw [e, abs_mul]
  have h' : |Phat / Qhat - P / Q| ≤ (θ / 3) * (P / Q) := by
    rwa [abs_sub_comm] at h
  have h2 : (2 : ℝ) * |Phat / Qhat - P / Q| ≤ 2 * ((θ / 3) * (P / Q)) := by
    linarith [h']
  have h3 : (θ / 3) * (P / Q) ≤ θ / 2 := by nlinarith [hPQ, hθ0]
  nlinarith [h2, h3]

/-- **Corollary 8**, trace form (arXiv:1705.01843v4, p. 9).  Here `Z = Tr(e^{-H})`,
`W = Tr(A e^{-H})`, `Qhat` approximates `Tr(I/4 · e^{-H}) = Z/4` and `Phat`
approximates `Tr((I+A/2)/4 · e^{-H}) = (Z + W/2)/4`, each multiplicatively with
error `θ/9`.  The hypothesis `|W| ≤ Z` is exactly the consequence of `‖A‖ ≤ 1`
used in the paper.  Then `2 Phat/Qhat - 2` is an additive `θ`-approximation of
`Tr(A e^{-H})/Tr(e^{-H}) = W/Z`. -/
theorem cor8_trace_ratio {θ Z W Qhat Phat : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hZ : 0 < Z) (hW : |W| ≤ Z)
    (hQ : |Z / 4 - Qhat| ≤ (Z / 4) * (θ / 9))
    (hP : |(Z + W / 2) / 4 - Phat| ≤ ((Z + W / 2) / 4) * (θ / 9)) :
    |2 * Phat / Qhat - 2 - W / Z| ≤ θ := by
  have hPpos : 0 < (Z + W / 2) / 4 := by
    have h1 : -Z ≤ W := (abs_le.mp hW).1
    linarith
  have hQpos : 0 < Z / 4 := by linarith
  have hratio_abs : |W / Z| ≤ 1 := by
    rw [abs_div, abs_of_pos hZ]
    rw [div_le_one hZ]
    exact hW
  have hr : W / Z = 2 * ((Z + W / 2) / 4) / (Z / 4) - 2 := by
    field_simp
    ring
  exact cor8_scalar hθ0 hθ1 hQpos hPpos hr hratio_abs hP hQ

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
