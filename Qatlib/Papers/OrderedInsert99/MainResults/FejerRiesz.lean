/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorUniquenessTran
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators
open Polynomial

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

theorem fejer_riesz_factorization (M : ℕ) (q : Fin (M + 1) → ℂ)
    (htop : q ⟨M, Nat.lt_succ_self M⟩ ≠ 0)
    (him : (q ⟨0, Nat.succ_pos M⟩).im = 0)
    (hnonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (complexLaurentEval q z).re) :
    ∃ p : Fin (M + 1) → ℂ,
      (laurentCoefficientPolynomial p).natDegree = M ∧
      (∀ z : ℂ, ‖z‖ = 1 → complexLaurentEval q z =
        (laurentCoefficientPolynomial p).eval z *
          star ((laurentCoefficientPolynomial p).eval ((star z)⁻¹))) := by
  have ha : complexLaurentNonnegative q := ⟨him, hnonneg⟩

  obtain ⟨p, _hdeg, heval, _hcoeff, _hpsd, _htr, hroots⟩ :=
    laurentCircleSpectralFactor (M + 1) q ha

  have htop' : q ⟨(M + 1) - 1, by omega⟩ ≠ 0 := by
    have hfin : (⟨(M + 1) - 1, by omega⟩ : Fin (M + 1)) = ⟨M, Nat.lt_succ_self M⟩ := by
      apply Fin.ext
      simp
    simpa [hfin] using! htop

  have hp0 : laurentCoefficientPolynomial p ≠ 0 := by
    intro hP
    have hzero : ∀ z : ℂ, ‖z‖ = 1 → complexLaurentEval q z = 0 := by
      intro z hz
      rw [heval z hz, hP]
      simp
    have hq0 : q = fun _ => (0 : ℂ) := by
      funext i
      refine complexLaurent_coeff_eq_of_eval_eq q (fun _ => (0 : ℂ)) ?_ i
      intro z hz
      rw [hzero z hz]
      simp [complexLaurentEval, complexLaurentCoefficient]
    exact htop (by rw [hq0])
  have hroots' : ∀ z : ℂ, (laurentCoefficientPolynomial p).eval z = 0 → ‖z‖ ≤ 1 :=
    hroots hp0

  obtain ⟨hd, -, -, -⟩ :=
    laurentCircleFactorUniqueness (M + 1) q p p ha htop' heval heval hroots' hroots'
  refine ⟨p, hd, ?_⟩
  intro z hz
  have hzstar : star z = z⁻¹ := by
    have h1 : z * star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
      norm_num
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  have hzinv : (star z)⁻¹ = z := by
    rw [hzstar, inv_inv]
  rw [heval z hz, hzinv]

  have hsq : ((‖(laurentCoefficientPolynomial p).eval z‖ ^ 2 : ℝ) : ℂ) =
      (laurentCoefficientPolynomial p).eval z * star ((laurentCoefficientPolynomial p).eval z) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsq]

end Qatlib.Papers.OrderedInsert99.MainResults
