/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Gauge
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# Conditional correctness of the actual horizontal-coordinate ODE

Initial unit norm and Hopf compatibility are propagated using the actual
source derivative and one-sided solution derivatives on a finite interval.
This module does not construct the ODE solution or a periodic lift.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

-- The pinned quaternion API needs this local real-linearity adapter.
/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Definition of horizontal Coefficient in the Hopf Atlas construction. -/
def horizontalCoefficient (s ds : ℍ) : ℍ := (-1/2 : ℝ) • (s*ds)
/-- Definition of commutator in the Hopf Atlas construction. -/
def commutator (a b : ℍ) : ℍ := a*b-b*a

/-- The square of a purely imaginary unit quaternion is negative one. -/
theorem source_square (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1) : s*s = -1 := by
  have h := Quaternion.sq_eq_neg_normSq.mpr hr
  rw [(normSq_eq_one_iff _).mpr hn] at h
  simpa only [pow_two, Quaternion.coe_one] using h

/-- The derivative of a differentiable curve of purely imaginary unit quaternions anticommutes
with the curve value at each time. -/
theorem source_tangent {s ds : ℝ → ℍ} (hs : ∀ t, HasDerivAt s (ds t) t)
    (hr : ∀ t, (s t).re=0) (hn : ∀ t, ‖s t‖=1) (t : ℝ) :
    s t*ds t+ds t*s t=0 := by
  have heq : (fun u => s u*s u) = fun _ => (-1 : ℍ) :=
    funext fun u => source_square (s u) (hr u) (hn u)
  have hd := (hs t).mul (hs t)
  change HasDerivAt (fun u => s u*s u) (ds t*s t+s t*ds t) t at hd
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (-1 : ℍ))
  simpa only [add_comm] using hz

/-- If `s` and `ds` anticommute, the transport coefficient `-s * ds / 2` is purely imaginary. -/
theorem horizontal_re (s ds : ℍ) (ht : s*ds+ds*s=0) :
    (horizontalCoefficient s ds).re = 0 := by
  have h : (s*ds).re+(ds*s).re=0 := by
    simpa only [Quaternion.re_add, Quaternion.re_zero] using congrArg (fun q : ℍ => q.re) ht
  have heq : (s*ds).re=(ds*s).re := by simp only [Quaternion.re_mul]; ring
  rw [← heq] at h
  have hz : (s*ds).re=0 := by linarith
  change (-1/2 : ℝ) * (s*ds).re = 0
  rw [hz, mul_zero]

/-- If `s` squares to negative one and anticommutes with `ds`, its commutator with the
horizontal coefficient equals `ds`. -/
theorem horizontal_commutator (s ds : ℍ) (hu : s*s = -1) (ht : s*ds+ds*s=0) :
    commutator s (horizontalCoefficient s ds)=ds := by
  have hv : ds*s=-(s*ds) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using ht)
  calc
    _ = (-1/2 : ℝ) • ((s*s)*ds-s*(ds*s)) := by
      simp [commutator, horizontalCoefficient, smul_sub, mul_assoc]
    _ = ds := by
      simp only [hv, mul_neg, ← mul_assoc, hu, neg_one_mul]
      ext <;> simp <;> ring

/-- For a unit spin, the norm of the horizontal coefficient is half the norm of the spin
derivative. -/
theorem horizontal_norm (s ds : ℍ) (hu : ‖s‖=1) :
    ‖horizontalCoefficient s ds‖ = (1/2 : ℝ)*‖ds‖ := by
  simp [horizontalCoefficient, norm_smul, norm_mul, hu]

/-- The real inner product of `q` with `q * k` equals the squared norm of `q` times the real
coordinate of `k`. -/
theorem inner_self_mul (q k : ℍ) : inner ℝ q (q*k)=Quaternion.normSq q*k.re := by
  simp [Quaternion.inner_def, Quaternion.normSq_def']
  ring

/-- If a quaternion curve has derivative `v` at `t`, its squared norm has derivative twice the
real inner product of `q t` with `v`. -/
theorem normSq_hasDerivAt {q : ℝ → ℍ} {v : ℍ} {t : ℝ} (hq : HasDerivAt q v t) :
    HasDerivAt (fun u => Quaternion.normSq (q u)) (2*inner ℝ (q t) v) t := by
  simpa only [Quaternion.normSq_eq_norm_mul_self, pow_two] using hq.norm_sq

/-- Right transport by a purely imaginary coefficient makes the squared norm derivative zero at
the transport point. -/
theorem transport_normSq_derivative {q : ℝ → ℍ} {k : ℍ} {t : ℝ}
    (hq : HasDerivAt q (q t*k) t) (hk : k.re=0) :
    HasDerivAt (fun u => Quaternion.normSq (q u)) 0 t := by
  simpa [inner_self_mul, hk] using normSq_hasDerivAt hq

/-- Under right transport by a purely imaginary coefficient `k`, the derivative of the Hopf
image is its commutator with `k`. -/
theorem transport_hopf_derivative {q : ℝ → ℍ} {k : ℍ} {t : ℝ}
    (hq : HasDerivAt q (q t*k) t) (hk : k.re=0) :
    HasDerivAt (fun u => hopf (q u)) (commutator (hopf (q t)) k) t := by
  have hstar : star k = -k := by ext <;> simp [hk]
  apply ((hq.star.mul_const iAxis).mul hq).congr_deriv
  simp only [star_mul, hstar, hopf, commutator]
  noncomm_ring

/-- The norm of the quaternion commutator is bounded by twice the product of the two quaternion
norms. -/
theorem norm_commutator (a b : ℍ) : ‖commutator a b‖ ≤ 2*‖b‖*‖a‖ := by
  calc
    _ ≤ ‖a*b‖+‖b*a‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, norm_mul]; ring

/-- The derivative of a differentiable curve with identically zero real coordinate is purely
imaginary at every time. -/
theorem source_derivative_re {s ds : ℝ → ℍ} (hs : ∀ t, HasDerivAt s (ds t) t)
    (hr : ∀ t, (s t).re=0) (t : ℝ) : (ds t).re=0 := by
  have heq : (fun u => star (s u)) = fun u => -s u := by
    funext u
    ext <;> simp [hr u]
  have hd := (hs t).star
  rw [heq] at hd
  have h := hd.unique (hs t).neg
  have hreal := congrArg (fun q : ℍ => q.re) h
  simp only [Quaternion.re_star, Quaternion.re_neg] at hreal
  linarith

/-- For a curve with within-set derivative given by right multiplication by a purely imaginary
coefficient, the squared norm has zero derivative within that set. -/
theorem normSq_within {q : ℝ → ℍ} {k : ℍ} {t : ℝ} {S : Set ℝ}
    (hq : HasDerivWithinAt q (q t*k) S t) (hk : k.re=0) :
    HasDerivWithinAt (fun u => Quaternion.normSq (q u)) 0 S t := by
  simpa only [Quaternion.normSq_eq_norm_mul_self, pow_two, inner_self_mul,
    hk, mul_zero] using hq.norm_sq

/-- For a curve with within-set derivative given by right multiplication by a purely imaginary
coefficient, its Hopf image has within-set derivative given by the commutator with that
coefficient. -/
theorem hopf_within {q : ℝ → ℍ} {k : ℍ} {t : ℝ} {S : Set ℝ}
    (hq : HasDerivWithinAt q (q t*k) S t) (hk : k.re=0) :
    HasDerivWithinAt (fun u => hopf (q u)) (commutator (hopf (q t)) k) S t := by
  have hstar : star k = -k := by ext <;> simp [hk]
  apply ((hq.star.mul_const iAxis).mul hq).congr_deriv
  simp only [star_mul, hstar, hopf, commutator]
  noncomm_ring

/-- The quaternion Hopf map is continuous on the whole quaternion space. -/
theorem continuous_hopf : Continuous hopf :=
  (continuous_star.mul continuous_const).mul continuous_id

/-- A curve continuous on a closed interval, starting at a unit quaternion and solving the right
transport equation with purely imaginary coefficient in the right-sided sense before the final
time, has unit norm throughout the interval. -/
theorem unit_transport {q k : ℝ → ℍ} {a b : ℝ}
    (hc : ContinuousOn q (Set.Icc a b))
    (hq : ∀ t ∈ Set.Ico a b, HasDerivWithinAt q (q t*k t) (Set.Ici t) t)
    (hk : ∀ t ∈ Set.Ico a b, (k t).re=0) (h0 : ‖q a‖=1) :
    ∀ t ∈ Set.Icc a b, ‖q t‖=1 := by
  have hf : ContinuousOn (fun t => Quaternion.normSq (q t)-1) (Set.Icc a b) :=
    (Quaternion.continuous_normSq.comp_continuousOn hc).sub continuousOn_const
  have hd : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (fun u => Quaternion.normSq (q u)-1) 0 (Set.Ici t) t := by
    intro t ht
    simpa using (normSq_within (hq t ht) (hk t ht)).sub_const 1
  have ha : Quaternion.normSq (q a)-1=0 := by
    rw [(normSq_eq_one_iff _).mpr h0]
    ring
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := 0)
    hf hd ha (by intro t ht; simp)
  intro t ht
  exact (normSq_eq_one_iff _).mp (sub_eq_zero.mp (hz t ht))

/-- A differentiable curve of purely imaginary unit spins with bounded speed is lifted by
horizontal transport throughout the closed interval. The transporting curve must be continuous
there, satisfy the right-sided equation before the final time, and start at a unit quaternion
over the initial spin. -/
theorem horizontal_transport {s ds q : ℝ → ℍ} {a b M : ℝ}
    (hs : ∀ t, HasDerivAt s (ds t) t) (hr : ∀ t, (s t).re=0) (hn : ∀ t, ‖s t‖=1)
    (hb : ∀ t ∈ Set.Ico a b, ‖ds t‖ ≤ M)
    (hc : ContinuousOn q (Set.Icc a b))
    (hq : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt q (q t*horizontalCoefficient (s t) (ds t)) (Set.Ici t) t)
    (h0 : ‖q a‖=1) (hcompat : hopf (q a)=s a) :
    ∀ t ∈ Set.Icc a b, ‖q t‖=1 ∧ hopf (q t)=s t := by
  let k := fun t => horizontalCoefficient (s t) (ds t)
  let d := fun t => hopf (q t)-s t
  have hk : ∀ t ∈ Set.Ico a b, (k t).re=0 := by
    intro t _
    exact horizontal_re _ _ (source_tangent hs hr hn t)
  have hnq := unit_transport hc hq hk h0
  have hcont : ContinuousOn d (Set.Icc a b) :=
    (continuous_hopf.comp_continuousOn hc).sub
      (continuous_iff_continuousAt.mpr (fun t => (hs t).continuousAt)).continuousOn
  have hder : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt d (commutator (d t) (k t)) (Set.Ici t) t := by
    intro t ht
    have hsk : ds t=commutator (s t) (k t) :=
      (horizontal_commutator _ _ (source_square _ (hr t) (hn t)) (source_tangent hs hr hn t)).symm
    have hs0 : HasDerivWithinAt s (commutator (s t) (k t)) (Set.Ici t) t := by
      rw [← hsk]
      exact (hs t).hasDerivWithinAt
    have hd := (hopf_within (hq t ht) (hk t ht)).sub hs0
    convert hd using 1
    dsimp [d]
    unfold commutator
    noncomm_ring
  have hbound : ∀ t ∈ Set.Ico a b, ‖commutator (d t) (k t)‖ ≤ M*‖d t‖ := by
    intro t ht
    have hkbound : ‖k t‖ ≤ M/2 := by
      rw [horizontal_norm _ _ (hn t)]
      linarith [hb t ht]
    exact (norm_commutator (d t) (k t)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hcont hder (by simp [d, hcompat]) hbound
  intro t ht
  exact ⟨hnq t ht, sub_eq_zero.mp (hzero t ht)⟩

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
