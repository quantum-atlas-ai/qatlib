/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLawAnsw
import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecoveryAnsw
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.PerturbedProgression
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Matrix
open scoped Classical BigOperators

theorem dlog_good_fiber_rotation (p q r k : ℕ) (hp : 1 < p) (hpq : p < q)
    (c d : Fin q) (j : ℤ) :
    let θ := dlogT p q r c d - (j : ℝ)*(q : ℝ)
    let s := (centeredResidue (q : ℤ) ((c.val*(p-1) : ℤ)) : ℝ)
    let a := fun b : Fin (p-1) => (((r*b.val+k)%(p-1) : ℕ) : ℝ)
    let C := ((p-1 : ℕ) : ℝ)-1
    let W := C/2*θ/(q : ℝ) + (k : ℝ)*(dlogCprime p q c : ℝ)/((p-1 : ℕ) : ℝ) + s/(2*(q : ℝ))
    (∑ b : Fin (p-1), Complex.exp (2*Real.pi*Complex.I*
        (a b*c.val + (b.val : ℝ)*d.val)/(q : ℝ))) =
      Complex.exp (2*Real.pi*Complex.I*(W : ℂ)) *
        ∑ b : Fin (p-1), Complex.exp (Complex.I *
          ((2*Real.pi*θ/(q : ℝ)*((b.val : ℝ)-C/2) +
            2*Real.pi*(a b/((p-1 : ℕ) : ℝ)-1/2)*s/(q : ℝ) : ℝ) : ℂ)) := by
  (try dsimp only)
  let P : ℝ := ((p-1 : ℕ) : ℝ)
  let s : ℝ := (centeredResidue (q : ℤ) ((c.val*(p-1) : ℤ)) : ℝ)
  let θ := dlogT p q r c d - (j : ℝ)*(q : ℝ)
  let W := (P-1)/2*θ/(q : ℝ) + (k : ℝ)*(dlogCprime p q c : ℝ)/P + s/(2*(q : ℝ))
  have hP : 0 < P := by dsimp [P]; exact_mod_cast (by omega : 0 < p-1)
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (dlog_cprime_integrality p q c)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hi
  have hc : (c.val : ℝ) = ((dlogCprime p q c : ℝ)*(q : ℝ)+s)/P := by
    apply (eq_div_iff hP.ne').mpr
    dsimp [P, s]
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    linarith
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  let z : ℕ := (r*b.val+k)/(p-1)
  let a : ℝ := (((r*b.val+k)%(p-1) : ℕ) : ℝ)
  let n : ℤ := (b.val : ℤ)*j - (z : ℤ)*dlogCprime p q c
  let B := θ/(q : ℝ)*((b.val : ℝ)-(P-1)/2)
  let A := (a/P-1/2)*s/(q : ℝ)
  have ha : a = (r : ℝ)*(b.val : ℝ)+(k : ℝ)-P*(z : ℝ) := by
    have he := Nat.mod_add_div (r*b.val+k) (p-1)
    have hr : a+P*(z : ℝ) = (r : ℝ)*(b.val : ℝ)+(k : ℝ) := by
      dsimp [a, P, z]
      exact_mod_cast he
    linarith
  have he : (a*(c.val : ℝ)+(b.val : ℝ)*(d.val : ℝ))/(q : ℝ) = W+B+A+(n : ℝ) := by
    dsimp only [W, B, A, θ, n]
    have ht : dlogT p q r c d = (d.val : ℝ) + (r : ℝ)*(dlogCprime p q c : ℝ)*(q : ℝ)/P :=
      dlogT_cprime_formula p q r hp c d
    rw [ht, hc, ha]
    push_cast
    field_simp
    ring
  have harg : (2*Real.pi*Complex.I*(a*(c.val : ℝ)+(b.val : ℝ)*(d.val : ℝ))/(q : ℝ) : ℂ) =
      2*Real.pi*Complex.I*(W : ℂ) + Complex.I*((2*Real.pi*B+2*Real.pi*A : ℝ) : ℂ) +
        2*Real.pi*Complex.I*(n : ℝ) := by
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) he
    push_cast at hcast
    push_cast
    linear_combination (2*Real.pi*Complex.I)*hcast
  change Complex.exp (2*Real.pi*Complex.I*(a*(c.val : ℝ)+(b.val : ℝ)*(d.val : ℝ))/(q : ℝ)) = _
  rw [harg, Complex.exp_add, Complex.exp_add, exp_two_pi_I_int, mul_one]
  congr 1
  congr 1
  dsimp [A, B, P, W, θ, s, a]
  push_cast
  ring

theorem dlog_good_state_probability_strong (p q r : ℕ) [NeZero p] (g x : ZMod p)
    (hp : 3 ≤ p) (hprime : Nat.Prime p) (hx0 : x ≠ 0) (hpq : p < q) (ho : orderOf g = p-1) (hx : x = g ^ r)
    (c d : Fin q) (k : ℕ) (hk : k < p-1) (hgood : dlogGoodPair p q r c d) :
    1/(16*(q : ℝ)^2) ≤ BornProb (dlogTwoDimState p q g x) (c, d, g ^ k) := by
  obtain ⟨⟨j, hj⟩, hs⟩ := hgood
  let P := p-1
  let θ := dlogT p q r c d - (j : ℝ)*(q : ℝ)
  let s : ℝ := (centeredResidue (q : ℤ) ((c.val*(p-1) : ℤ)) : ℝ)
  let a := fun b : Fin P => (((r*b.val+k)%P : ℕ) : ℝ)
  let W := ((P : ℝ)-1)/2*θ/(q : ℝ) + (k : ℝ)*(dlogCprime p q c : ℝ)/(P : ℝ) + s/(2*(q : ℝ))
  have hP : 0 < P := by dsimp [P]; omega
  have hq : 0 < q := by omega
  have hqa : (0 : ℝ) < q := by exact_mod_cast hq
  have hPa : (0 : ℝ) < P := by exact_mod_cast hP
  have hNq : P ≤ q := by dsimp [P]; omega
  have hs' : |s| ≤ (q : ℝ)/12 := by simpa only [s, dlogSmallResidue, Int.cast_abs] using! hs
  have ha (b : Fin P) : 0 ≤ a b ∧ a b ≤ (P : ℝ) := by
    constructor
    · exact Nat.cast_nonneg _
    · have h := Nat.mod_lt (r*b.val+k) hP
      dsimp only [a]
      exact_mod_cast h.le
  have hproject := perturbed_progression_norm_lower P q hP hNq θ s hj hs' a ha
  have hrotate := dlog_good_fiber_rotation p q r k (by omega) hpq c d j
  have hsum : (P : ℝ)/4 ≤ ‖∑ b : Fin P, Complex.exp (2*Real.pi*Complex.I*
      (a b*c.val+(b.val : ℝ)*d.val)/(q : ℝ))‖ := by
    rw [hrotate, norm_mul, norm_exp_two_pi_I, one_mul]
    exact hproject
  rw [(dlogTwoDimSamplingLaw p q g x hprime hp hx0 hpq ho r hx).2.2 c d k hk]
  rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, mul_pow,
      mul_pow]
  have hsq : ((P : ℝ)/4)^2 ≤
      ‖∑ b : Fin P, Complex.exp (2*Real.pi*Complex.I*(a b*c.val+(b.val : ℝ)*d.val)/(q : ℝ))‖^2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hsum
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (P : ℝ)⁻¹^2 * (q : ℝ)⁻¹^2)
  convert! hmul using 1
  all_goals field_simp
  all_goals ring

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
