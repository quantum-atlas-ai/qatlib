/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorUniquenessStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentFactorUniqueness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped Classical BigOperators ComplexOrder

private theorem circle_factor_actual_degree (n : ℕ) [NeZero n] (a p : Fin n → ℂ)
    (htop : a ⟨n-1,by have := NeZero.pos n; omega⟩≠0)
    (hc : ∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z=
      ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ)) :
    (laurentCoefficientPolynomial p).natDegree=n-1 ∧
      (laurentCoefficientPolynomial p).eval 0≠0 := by
  let top : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  have hcoeff := gramOuter_positive_coeff_of_circle_factor a p hc top
  rw [gramOuter_highest_trace] at hcoeff
  have hprod : star (p 0)*p top≠0 := by rw [hcoeff]; exact htop
  have hp0 : p 0≠0 := by intro h; apply hprod; simp [h]
  have hpt : p top≠0 := by intro h; apply hprod; simp [h]
  have hc0 : (laurentCoefficientPolynomial p).coeff 0=p 0 := by
    rw [laurentCoefficientPolynomial_coeff,dif_pos (NeZero.pos n)]
    rfl
  have hct : (laurentCoefficientPolynomial p).coeff (n-1)=p top := by
    rw [laurentCoefficientPolynomial_coeff,dif_pos (by have := NeZero.pos n; omega)]
  refine ⟨le_antisymm (laurentCoefficientPolynomial_degree p)
    (Polynomial.le_natDegree_of_ne_zero (by rwa [hct])),?_⟩
  rw [← Polynomial.coeff_zero_eq_eval_zero,hc0]
  exact hp0

theorem laurentCircleFactorUniqueness : LaurentCircleFactorUniqueness := by
  intro n _ a p q _ htop hP hQ hPr hQr
  obtain ⟨hPd,hPc⟩ := circle_factor_actual_degree n a p htop hP
  obtain ⟨hQd,hQc⟩ := circle_factor_actual_degree n a q htop hQ
  have hnorm (z : ℂ) (hz : ‖z‖=1) :
      ‖(laurentCoefficientPolynomial p).eval z‖=‖(laurentCoefficientPolynomial q).eval z‖ := by
    have he := (hP z hz).symm.trans (hQ z hz)
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective he)
  obtain ⟨u,hu,he⟩ := closed_disk_polynomial_phase_unique (laurentCoefficientPolynomial p)
    (laurentCoefficientPolynomial q) (hQd.trans hPd.symm) hPc hQc hPr hQr hnorm
  refine ⟨hPd,hQd,u,hu,?_⟩
  intro i
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff i.val) he
  simp only [coeff_C_mul,laurentCoefficientPolynomial_coeff,dif_pos i.isLt] at hc
  exact hc

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
