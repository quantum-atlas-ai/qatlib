/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleyAnalysis

/-!
# Endpoint error for the same decoded integer execution

The exact coefficient is only required to be continuous on the unit interval
with the stated Lipschitz bound. Each step is compared separately. The
initial approximation is arbitrary; its error is added, not assumed zero.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open Set
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `grid_step_error` guarantee for the `CayleyError` construction; the complete source hypotheses are retained. -/
private theorem grid_step_error {q k : ℝ → ℍ} (D : ℕ) (hD : 0<D) (j : ℕ) (hj : j<D)
    (hk : ContinuousOn k (Icc 0 1)) (hp : ∀ t ∈ Icc 0 1, (k t).re=0)
    (hq : ∀ t ∈ Icc 0 1, HasDerivWithinAt q (q t*k t) (Icc 0 1) t)
    (hn : ∀ t ∈ Icc 0 1, ‖q t‖=1) (K M e : ℝ)
    (hK : ∀ t ∈ Icc 0 1, ‖k t‖ ≤ K)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, ‖k t-k s‖ ≤ M*|t-s|)
    (v : ℍ) (hv : v.re=0) (he : ‖v-k ((j : ℝ)/D)‖ ≤ e) :
    ‖q ((j : ℝ)/D)*cayleyFactor v (1/(D : ℝ))-q (((j+1 : ℕ) : ℝ)/D)‖ ≤
      M*(1/(D : ℝ))^2/2+e*(1/(D : ℝ))+(K+e)^3*(1/(D : ℝ))^3/12 := by
  have hd : (0 : ℝ)<D := by exact_mod_cast hD
  let tau : ℝ := (j : ℝ)/D
  let h : ℝ := 1/(D : ℝ)
  have hh : 0 ≤ h := (one_div_pos.mpr hd).le
  have ht0 : 0 ≤ tau := div_nonneg (Nat.cast_nonneg j) hd.le
  have hnext : tau+h=((j+1 : ℕ) : ℝ)/D := by dsimp [tau,h]; push_cast; ring
  have ht1 : tau+h ≤ 1 := by
    rw [hnext]
    apply (div_le_one hd).mpr
    exact_mod_cast Nat.succ_le_of_lt hj
  have htau : tau ∈ Icc (0 : ℝ) 1 := ⟨ht0,by linarith⟩
  have hmap : MapsTo (fun u : ℝ => tau+u) (Icc 0 h) (Icc 0 1) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hkc : ContinuousOn (fun u : ℝ => k (tau+u)) (Icc 0 h) :=
    hk.comp (continuous_const.add continuous_id).continuousOn hmap
  have hqd : ∀ u ∈ Icc 0 h, HasDerivWithinAt (fun z : ℝ => q (tau+z))
      (q (tau+u)*k (tau+u)) (Icc 0 h) u := by
    intro u hu
    have ht : HasDerivWithinAt (fun z : ℝ => tau+z) 1 (Icc 0 h) u := by
      simpa using ((hasDerivAt_id u).const_add tau).hasDerivWithinAt
    simpa only [Function.comp_def,one_smul] using (hq (tau+u) (hmap hu)).scomp u ht hmap
  have hvb : ‖v‖ ≤ K+e := by
    have h := (norm_le_norm_sub_add v (k tau)).trans (add_le_add he (hK tau htau))
    linarith
  have hfreeze : ∀ u ∈ Icc 0 h, ‖v-k (tau+u)‖ ≤ M*u+e := by
    intro u hu
    have hvar : ‖k tau-k (tau+u)‖ ≤ M*u := by
      rw [norm_sub_rev]
      simpa only [add_sub_cancel_left,abs_of_nonneg hu.1] using hlip tau htau (tau+u) (hmap hu)
    calc
      _ ≤ ‖v-k tau‖+‖k tau-k (tau+u)‖ := by
        simpa only [dist_eq_norm] using dist_triangle v (k tau) (k (tau+u))
      _ ≤ e+M*u := add_le_add he hvar
      _ = M*u+e := by ring
  have hstep := cayleyStep_error hh hkc (fun u hu => hp (tau+u) (hmap hu)) hqd
    (fun u hu => hn (tau+u) (hmap hu)) v hv hvb hfreeze
  simpa only [add_zero,hnext] using hstep

/-- All D,p satisfying the oracle contracts approximate the same exact curve.
The initial value is allowed to be a non-unit rational approximation. -/
theorem cayleyIntegerRun_error {q k : ℝ → ℍ} (D p : ℕ) (hD : 0<D)
    (a : ℕ → Fin 3 → ℤ) (hk : ContinuousOn k (Icc 0 1))
    (hp : ∀ t ∈ Icc 0 1, (k t).re=0)
    (hq : ∀ t ∈ Icc 0 1, HasDerivWithinAt q (q t*k t) (Icc 0 1) t)
    (hn : ∀ t ∈ Icc 0 1, ‖q t‖=1) (K M : ℝ)
    (hK : ∀ t ∈ Icc 0 1, ‖k t‖ ≤ K)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, ‖k t-k s‖ ≤ M*|t-s|)
    (horacle : ∀ j < D, ‖dyadicCoefficient p (a j)-k ((j : ℝ)/D)‖ ≤ (2^p : ℝ)⁻¹)
    (initial : ℍ) (delta0 : ℝ) (hinitial : ‖initial-q 0‖ ≤ delta0) :
    ‖initial*decodeCayleyState (cayleyIntegerRun D p a D)-q 1‖ ≤
      delta0+M/(2*(D : ℝ))+(2^p : ℝ)⁻¹+(K+(2^p : ℝ)⁻¹)^3/(12*(D : ℝ)^2) := by
  have hd : (0 : ℝ)<D := by exact_mod_cast hD
  let h : ℝ := 1/(D : ℝ)
  let e : ℝ := (2^p : ℝ)⁻¹
  let budget : ℝ := M*h^2/2+e*h+(K+e)^3*h^3/12
  have hprefix : ∀ n ≤ D, ‖initial*realCayleyRun D p a n-q ((n : ℝ)/D)‖ ≤ delta0+(n : ℝ)*budget := by
    intro n
    induction n with
    | zero => intro hn; simpa only [realCayleyRun,mul_one,Nat.cast_zero,zero_div,zero_mul,add_zero] using hinitial
    | succ n ih =>
      intro hnle
      have hnd : n<D := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnle
      have hprev := ih (Nat.le_of_succ_le hnle)
      have hstep := grid_step_error D hD n hnd hk hp hq hn K M e hK hlip
        (dyadicCoefficient p (a n)) (dyadicCoefficient_re p (a n)) (horacle n hnd)
      let v := dyadicCoefficient p (a n)
      let factor := cayleyFactor v h
      have hf : ‖factor‖=1 := cayleyFactor_unit v (dyadicCoefficient_re p (a n)) h
      calc
        _ = ‖(initial*realCayleyRun D p a n)*factor-q (((n+1 : ℕ) : ℝ)/D)‖ := by
          rw [realCayleyRun,mul_assoc]
        _ ≤ ‖(initial*realCayleyRun D p a n)*factor-q ((n : ℝ)/D)*factor‖+
            ‖q ((n : ℝ)/D)*factor-q (((n+1 : ℕ) : ℝ)/D)‖ := by
          simpa only [dist_eq_norm] using dist_triangle ((initial*realCayleyRun D p a n)*factor)
            (q ((n : ℝ)/D)*factor) (q (((n+1 : ℕ) : ℝ)/D))
        _ = ‖initial*realCayleyRun D p a n-q ((n : ℝ)/D)‖+
            ‖q ((n : ℝ)/D)*factor-q (((n+1 : ℕ) : ℝ)/D)‖ := by rw [← sub_mul,norm_mul,hf,mul_one]
        _ ≤ (delta0+(n : ℝ)*budget)+budget := add_le_add hprev hstep
        _ = delta0+((n+1 : ℕ) : ℝ)*budget := by push_cast; ring
  rw [decodeCayleyIntegerRun D p hD]
  have hfinal := hprefix D (le_refl D)
  rw [div_self hd.ne'] at hfinal
  calc
    _ ≤ delta0+(D : ℝ)*budget := hfinal
    _ = _ := by
      dsimp [budget,h,e]
      field_simp [hd.ne']
      ring

/-- Original `cayleyOracleExecution_error` guarantee for the `CayleyError` construction; the complete source hypotheses are retained. -/
theorem cayleyOracleExecution_error {q k : ℝ → ℍ} (D p : ℕ) (hD : 0<D)
    (oracle : ℚ × ℕ → Fin 3 → ℤ) (hk : ContinuousOn k (Icc 0 1))
    (hp : ∀ t ∈ Icc 0 1, (k t).re=0)
    (hq : ∀ t ∈ Icc 0 1, HasDerivWithinAt q (q t*k t) (Icc 0 1) t)
    (hn : ∀ t ∈ Icc 0 1, ‖q t‖=1) (K M : ℝ)
    (hK : ∀ t ∈ Icc 0 1, ‖k t‖ ≤ K)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, ‖k t-k s‖ ≤ M*|t-s|)
    (horacle : ∀ j < D, ‖dyadicCoefficient p (oracle ((j : ℚ)/(D : ℚ),p))-k ((j : ℝ)/D)‖ ≤ (2^p : ℝ)⁻¹)
    (initial : ℍ) (delta0 : ℝ) (hinitial : ‖initial-q 0‖ ≤ delta0) :
    ‖initial*decodeCayleyState (cayleyOracleExecution D p oracle)-q 1‖ ≤
      delta0+M/(2*(D : ℝ))+(2^p : ℝ)⁻¹+(K+(2^p : ℝ)⁻¹)^3/(12*(D : ℝ)^2) := by
  rw [cayleyOracleExecution_eq]
  exact cayleyIntegerRun_error D p hD _ hk hp hq hn K M hK hlip horacle initial delta0 hinitial

end Qatlib.Concepts.EffectiveGauge.RationalFlow
