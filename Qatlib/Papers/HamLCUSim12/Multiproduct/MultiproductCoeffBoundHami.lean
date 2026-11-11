/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffClosedFormHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductLogEstimates
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundStat

/-!
# Multiproduct coefficient estimates from analytic inputs

This module proves `multiproductCoeffBound` using the scalar maximum property and factorial
lower bound. The auxiliary results `multiproduct_exp_node_gt` and `multiproduct_coefficient_log`
establish terminal-node separation and a logarithmic estimate for the first k coefficients. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `multiproductCoeffBound`: Establishes the first-k multiproduct coefficient bound from
  `EtaMaxProperty`, `FactorialLowerBound`, and the terminal-node separation hypothesis.
* `multiproduct_coefficient_log`: Under terminal-node separation and q < k, the coefficient has
  positive absolute value, and its logarithm plus the two factorial logarithms is bounded by 2
  log 2 + (2k + 2) log(q + 1) − 2γ(k + 1).

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

/-- For k ≥ 1, the inequality 2k² ≤ exp(2γ(k + 1)) implies k < exp(γ(k + 1)). -/
theorem multiproduct_exp_node_gt (k : ℕ) (hk : 1 ≤ k) (γ : ℝ)
    (hc : 2*(k : ℝ)^2 ≤ Real.exp (2*γ*((k+1 : ℕ) : ℝ))) :
    (k : ℝ) < Real.exp (γ*((k+1 : ℕ) : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsq : Real.exp (γ*((k+1 : ℕ) : ℝ))^2 =
      Real.exp (2*γ*((k+1 : ℕ) : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hN := Real.exp_pos (γ*((k+1 : ℕ) : ℝ))
  nlinarith [sq_pos_of_pos hkR]

/-- Under terminal-node separation and q < k, the coefficient has positive absolute value, and
its logarithm plus the two factorial logarithms is bounded by 2 log 2 + (2k + 2) log(q + 1)
− 2γ(k + 1). -/
theorem multiproduct_coefficient_log (k : ℕ) (hk : 1 ≤ k) (γ : ℝ)
    (hc : 2*(k : ℝ)^2 ≤ Real.exp (2*γ*((k+1 : ℕ) : ℝ)))
    (q : Fin (k+1)) (hq : q.val < k) :
    0 < |mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q| ∧
    Real.log |mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q| +
      Real.log ((k+q.val+1).factorial : ℝ) + Real.log ((k-q.val-1).factorial : ℝ) ≤
      2*Real.log 2 + (2*(k : ℝ)+2)*Real.log (q.val+1 : ℝ) -
        2*γ*((k+1 : ℕ) : ℝ) := by
  let N := Real.exp (γ*((k+1 : ℕ) : ℝ))
  let p : ℝ := q.val+1
  let D := N^2-p^2
  have hp : 0 < p := by dsimp [p]; positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpK : p ≤ k := by dsimp [p]; exact_mod_cast (by omega : q.val+1 ≤ k)
  have hN : (k : ℝ) < N := multiproduct_exp_node_gt k hk γ hc
  have hNs : 0 < N := Real.exp_pos _
  have hsq : N^2 = Real.exp (2*γ*((k+1 : ℕ) : ℝ)) := by
    dsimp [N]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hDhalf : N^2/2 ≤ D := by dsimp [D]; rw [← hsq] at hc; nlinarith
  have hd : NodesDistinct k N := by
    intro j hj
    have hjK : (j.val+1 : ℝ) ≤ k := by exact_mod_cast (by omega : j.val+1 ≤ k)
    linarith
  have he := multiproductCoeffClosedForm k hk N hNs hd q hq
  have hf1 : 0 < ((k+q.val+1).factorial : ℝ) := by positivity
  have hf2 : 0 < ((k-q.val-1).factorial : ℝ) := by positivity
  have heabs := congrArg abs he
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow] at heabs
  have hpd : |p^2-N^2| = D := by rw [abs_of_neg (by dsimp [D] at hD; linarith)]; dsimp [D]; ring
  change |mCoeff k N q| *|p^2-N^2| *
      (|((k+q.val+1).factorial : ℝ)| *|((k-q.val-1).factorial : ℝ)|) =
      1*|2| *|p| ^(2*(k+1)) at heabs
  rw [hpd, abs_of_pos hf1, abs_of_pos hf2, abs_of_pos hp] at heabs
  norm_num at heabs
  have hC : 0 < |mCoeff k N q| := by
    have hpw : 0 < 2*p^(2*(k+1)) := by positivity
    by_contra hnot
    have hz : |mCoeff k N q| = 0 := le_antisymm (not_lt.mp hnot) (abs_nonneg _)
    rw [hz] at heabs
    norm_num at heabs
    linarith
  have hlog := congrArg Real.log heabs
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hC.ne' hD.ne',
    Real.log_mul hf1.ne' hf2.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hlD := Real.log_le_log (by positivity : 0 < N^2/2) hDhalf
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlD
  have hlN : Real.log N = γ*((k+1 : ℕ) : ℝ) := Real.log_exp _
  rw [hlN] at hlD
  push_cast at hlog
  norm_num at hlD
  constructor
  · exact hC
  · dsimp [p] at hlog
    dsimp [N] at hlog
    push_cast at hlog ⊢
    nlinarith

/-- Establishes the first-k multiproduct coefficient bound from `EtaMaxProperty`,
`FactorialLowerBound`, and the terminal-node separation hypothesis. See [ChildsWiebe2012]. -/
theorem multiproductCoeffBound : MultiproductCoeffBound := by
  intro k hk γ η hγ hη hE hF hc q hq
  let K : ℝ := k
  let p : ℝ := q.val+1
  let C := |mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q|
  let B := Real.sqrt 2 * K^((3 : ℝ)/2) * Real.exp (2*K*(1+Real.log η/2-γ))
  have hK : 0 < K := by dsimp [K]; exact_mod_cast (by omega : 0 < k)
  have hK1 : 1 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hp : 0 < p := by dsimp [p]; positivity
  have hpK : p ≤ K := by dsimp [p, K]; exact_mod_cast (by omega : q.val+1 ≤ k)
  have hη0 : 0 < η := by linarith
  have hC := multiproduct_coefficient_log k hk γ hc q hq
  have hCp : 0 < C := hC.1
  have hcl := hC.2
  have hB : 0 < B := by dsimp [B]; positivity
  have hlB : Real.log B = Real.log (Real.sqrt 2) + (3/2 : ℝ)*Real.log K +
      2*K*(1+Real.log η/2-γ) := by
    dsimp [B]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hK, Real.log_exp]
  change C ≤ B
  apply (Real.log_le_log_iff hCp hB).mp
  rw [hlB]
  have hplus : ((k+q.val+1 : ℕ) : ℝ) = K+p := by dsimp [K,p]; push_cast; ring
  have hminus : ((k-q.val-1 : ℕ) : ℝ) = K-p := by
    dsimp [K,p]
    rw [Nat.cast_sub (by omega : 1 ≤ k-q.val), Nat.cast_sub (by omega : q.val ≤ k)]
    push_cast
    ring
  have hcast : ((k+1 : ℕ) : ℝ) = K+1 := by dsimp [K]; push_cast; ring
  change Real.log C + _ + _ ≤ 2*Real.log 2 + (2*K+2)*Real.log p - _ at hcl
  rw [hcast] at hcl
  rcases lt_or_eq_of_le hpK with hi | he
  · have hmn : 0 < k-q.val-1 := by
      have hiN : q.val+1 < k := by dsimp [K,p] at hi; exact_mod_cast hi
      omega
    have hf1 := multiproduct_factorial_log_lower hF (k+q.val+1) (by omega)
    have hf2 := multiproduct_factorial_log_lower hF (k-q.val-1) hmn
    rw [hplus] at hf1
    rw [hminus] at hf2
    have hKP : 0 < K+p := by linarith
    have hKM : 0 < K-p := by linarith
    rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hKP.ne'] at hf1
    rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hKM.ne'] at hf2
    have hr := multiproduct_eta_log_ratio η K p hη0 hE hK hp hi
    have hpL := Real.log_le_log hp hpK
    have hiN : q.val+1 < k := by dsimp [K,p] at hi; exact_mod_cast hi
    have hp1 : p ≤ K-1 := by dsimp [p,K]; exact_mod_cast (by omega : q.val+1 ≤ k-1)
    have hprod : K ≤ (K+p)*(K-p) := by nlinarith
    have hlprod := Real.log_le_log hK hprod
    rw [Real.log_mul hKP.ne' hKM.ne'] at hlprod
    have hconst := multiproduct_interior_log_constant
    nlinarith
  · have heN : q.val+1 = k := by dsimp [K,p] at he; exact_mod_cast he
    have hmn : k-q.val-1 = 0 := by omega
    have hf1 := multiproduct_factorial_log_lower hF (k+q.val+1) (by omega)
    rw [hplus, he] at hf1
    rw [he, hmn, Nat.factorial_zero, Nat.cast_one, Real.log_one] at hcl
    have he2 : K+K = 2*K := by ring
    rw [he2, show 2*Real.pi*(2*K)=4*Real.pi*K by ring,
      Real.log_mul (by positivity : 4*Real.pi ≠ 0) hK.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hK.ne'] at hf1
    have hr := mul_le_mul_of_nonneg_left (multiproduct_eta_log_lower η hη) hK.le
    have hconst := multiproduct_endpoint_log_constant
    nlinarith

end Qatlib.Papers.HamLCUSim12.Multiproduct
