/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCayleyTransport
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped Classical BigOperators ComplexOrder

theorem laurentCircleSpectralFactor : LaurentCircleSpectralFactor := by
  intro n a ha
  by_cases hn : 0<n
  · obtain ⟨P,hPd,hPc,hPr⟩ := complex_laurent_circle_factor_polynomial a ha
    let p : Fin n → ℂ := fun i => P.coeff i.val
    have hp : laurentCoefficientPolynomial p=P := by
      ext k
      rw [laurentCoefficientPolynomial_coeff]
      split_ifs with hk
      · rfl
      · exact (coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<k)).symm
    have hc (z : ℂ) (hz : ‖z‖=1) : complexLaurentEval a z=
        ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ) := by
      rw [hp]
      exact hPc z hz
    have hcoeff := gramOuter_coeff_of_circle_factor a p hc
    refine ⟨p,laurentCoefficientPolynomial_degree p,hc,hcoeff,gramOuter_posSemidef p,?_,?_⟩
    · have he := congrArg Complex.re (hcoeff 0)
      simpa only [genTrace_zero,gramOuter_trace,Complex.ofReal_re] using he
    · simpa only [hp] using hPr
  · have hn0 : n=0 := by omega
    subst n
    refine ⟨fun _ => 0,by simp [laurentCoefficientPolynomial],?_,?_,gramOuter_posSemidef _,?_,?_⟩
    · intro z _
      norm_num [complexLaurentEval,laurentCoefficientPolynomial]
    · intro j
      rw [genTrace_eq_zero_of_natAbs_ge _ j (Nat.zero_le _)]
      simp [complexLaurentCoefficient]
    · simp [complexLaurentCoefficient]
    · simp [laurentCoefficientPolynomial]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
