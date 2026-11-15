/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStabilityStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Foundations.ComplexGeometry.PhaseRecovery

/-- Under the stated small-error and normalization assumptions, bounds the upper triangulation
gap by the prescribed rational function of `S`. -/
private theorem triangulation_upper_gap {S t H : ℝ} (hS0 : 0 ≤ S) (hS1 : S ≤ 2/5)
    (ht0 : 0 ≤ t) (htS : t ≤ S/4) (hH : 0 < H) (hHsq : H^2=(1-t)^2+S) :
    1-(1-3*t/2)/H ≤ (5*S/8)/(1+S/4) := by
  have ht1 : t ≤ 1/10 := by linarith only [htS,hS1]
  have hSsq : S^2 ≤ 4/25 := by nlinarith only [hS0,hS1]
  have hSt : S*t ≤ 1/25 := by
    have h := mul_le_mul hS1 ht1 ht0 (by norm_num : (0 : ℝ) ≤ 2/5)
    nlinarith only [h]
  let Q := 1/4+43*S/64-9*S^2/64-(5/16+15*S/32)*t
  have hQ : 0 ≤ Q := by dsimp [Q]; nlinarith only [hS0,hSsq,ht1,hSt]
  have hprod := mul_nonneg (show 0 ≤ S-4*t by linarith only [htS]) hQ
  have he : ((1-3*t/2)*(1+S/4))^2-(H*(1-3*S/8))^2=(S-4*t)*Q := by
    simp only [mul_pow,hHsq]
    dsimp [Q]
    ring
  have hraw : H*(1-3*S/8) ≤ (1-3*t/2)*(1+S/4) := by
    have h0 : 0 ≤ H*(1-3*S/8) := mul_nonneg hH.le (by linarith only [hS1])
    have h1 : 0 ≤ (1-3*t/2)*(1+S/4) := mul_nonneg (by linarith only [ht1]) (by linarith only [hS0])
    nlinarith only [he,hprod,h0,h1]
  apply (le_div_iff₀ (show 0 < 1+S/4 by linarith only [hS0])).2
  apply (mul_le_mul_iff_left₀ hH).1
  have he' : ((1-(1-3*t/2)/H)*(1+S/4))*H=H*(1+S/4)-(1-3*t/2)*(1+S/4) := by
    field_simp
  rw [he']
  nlinarith only [hraw]

/-- The stated scale-error assumptions bound the normalized scale gap by three quarters of `S`. -/
private theorem triangulation_scale_gap {S t D : ℝ} (hS0 : 0 ≤ S) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1/10) (htS : t ≤ S/4) (hD : 9/10 ≤ D)
    (herr : |D^2-1| ≤ S-2*t+t^2) :
    (|1-D|+3*t/2)/D ≤ 3*S/4 := by
  have hDs : 0 < D+1 := by linarith only [hD]
  have hEq : |1-D| * (D+1)=|D^2-1| := by
    rw [← abs_of_pos hDs,← abs_mul]
    have he : (1-D)*(D+1)=-(D^2-1) := by ring
    rw [he,abs_neg]
  have htSq : t^2 ≤ t/10 := by nlinarith only [ht0,ht1]
  have hdLower :=
      mul_le_mul_of_nonneg_left (show 19/10 ≤ D+1 by linarith only [hD]) (abs_nonneg (1-D))
  rw [hEq] at hdLower
  have hg : |1-D| ≤ 10*S/19-t := by nlinarith only [hdLower,herr,htSq]
  apply (div_le_iff₀ (show 0 < D by linarith only [hD])).2
  have hmult := mul_le_mul_of_nonneg_left hD (show 0 ≤ 3*S/4 by positivity)
  nlinarith only [hg,htS,hmult,hS0]

/-- For two points on the upper unit semicircle with ordered first coordinates, bounds their
squared distance by twice the first-coordinate difference. -/
private theorem triangulation_hemisphere_ordered {u v x y : ℝ}
    (hu : u ∈ Set.Icc (-1) 1) (hx : x ∈ Set.Icc (-1) 1)
    (hv : 0 ≤ v) (hy : 0 ≤ y) (huv : u^2+v^2=1) (hxy : x^2+y^2=1) (hux : u ≤ x) :
    (x-u)^2+(y-v)^2 ≤ 2*(x-u) := by
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ 1+u by linarith only [hu.1])
    (show 0 ≤ 1-x by linarith only [hx.2])) (sub_nonneg.2 hux)
  have hV : v^2=1-u^2 := by linarith only [huv]
  have hY : y^2=1-x^2 := by linarith only [hxy]
  have he : (v*y)^2-((1+u)*(1-x))^2=2*(1+u)*(1-x)*(x-u) := by
    simp only [mul_pow]
    rw [hV,hY]
    ring
  have hroot : (1+u)*(1-x) ≤ v*y := by
    have h0 : 0 ≤ (1+u)*(1-x) := mul_nonneg (by linarith only [hu.1]) (by linarith only [hx.2])
    have h1 : 0 ≤ v*y := mul_nonneg hv hy
    nlinarith only [he,hp,h0,h1]
  nlinarith only [hroot,huv,hxy]

/-- The squared distance between two points on the upper unit semicircle is at most twice their
absolute first-coordinate difference. -/
private theorem triangulation_hemisphere {u v x y : ℝ}
    (hu : u ∈ Set.Icc (-1) 1) (hx : x ∈ Set.Icc (-1) 1)
    (hv : 0 ≤ v) (hy : 0 ≤ y) (huv : u^2+v^2=1) (hxy : x^2+y^2=1) :
    (x-u)^2+(y-v)^2 ≤ 2*|x-u| := by
  by_cases h : u ≤ x
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact triangulation_hemisphere_ordered hu hx hv hy huv hxy h
  · have he := triangulation_hemisphere_ordered hx hu hy hv hxy huv (lt_of_not_ge h).le
    rw [abs_of_nonpos (by linarith only [h])]
    nlinarith only [he]

/-- Clipping a real number through cosine of arccosine does not increase its distance to a point
in the unit interval centered at zero. -/
private theorem triangulation_cosine_clipping (x u : ℝ) (hu : u ∈ Set.Icc (-1) 1) :
    |Real.cos (Real.arccos x)-u| ≤ |x-u| := by
  by_cases hx1 : 1 ≤ x
  · rw [Real.arccos_eq_zero.2 hx1,Real.cos_zero,
      abs_of_nonneg (by linarith only [hu.2]),abs_of_nonneg (by linarith only [hu.2,hx1])]
    linarith only [hx1]
  · by_cases hx0 : x ≤ -1
    · rw [Real.arccos_eq_pi.2 hx0,Real.cos_pi,
        abs_of_nonpos (by linarith only [hu.1]),abs_of_nonpos (by linarith only [hu.1,hx0])]
      linarith only [hx0]
    · rw [Real.cos_arccos (by linarith only [hx0]) (by linarith only [hx1])]

/-- Bounds the wrong-side first-coordinate gap by the prescribed `S` term plus one ninth of the
squared second coordinate. -/
private theorem triangulation_wrong_gap {u v x S t D H : ℝ}
    (hu : u ∈ Set.Icc 0 1) (huv : u^2+v^2=1) (hS0 : 0 ≤ S) (hS1 : S ≤ 2/5)
    (ht0 : 0 ≤ t) (htS : t ≤ S/4) (hD : 9/10 ≤ D) (hDH : D ≤ H)
    (hHsq : H^2=(1-t)^2+S) (hx : u-3*t/2 ≤ D*x) :
    u-x ≤ (5*S/8)/(1+S/4)+v^2/9 := by
  have hDp : 0 < D := by linarith only [hD]
  have hHp : 0 < H := lt_of_lt_of_le hDp hDH
  have ht1 : t ≤ 1/10 := by linarith only [htS,hS1]
  have hUp : 0 ≤ 1-u := by linarith only [hu.2]
  have hU : 1-u ≤ v^2 := by nlinarith only [hu.1,hu.2,huv]
  have hcross := mul_le_mul_of_nonneg_left (show 1-D ≤ 1/10 by linarith only [hD]) hUp
  have hraw : D*(u-x) ≤ D-1+3*t/2+v^2/10 := by nlinarith only [hx,hcross,hU]
  have hdiv : D*(1-(1-3*t/2)/D+v^2/(10*D))=D-1+3*t/2+v^2/10 := by field_simp; ring
  have hdelta : u-x ≤ 1-(1-3*t/2)/D+v^2/(10*D) := by
    apply (mul_le_mul_iff_right₀ hDp).1
    rw [hdiv]
    exact hraw
  have hmono := div_le_div_of_nonneg_left (show 0 ≤ 1-3*t/2 by linarith only [ht1]) hDp hDH
  have hV : v^2/(10*D) ≤ v^2/9 := by
    apply (div_le_iff₀ (show 0 < 10*D by positivity)).2
    have hh := mul_nonneg (sq_nonneg v) (show 0 ≤ D-9/10 by linarith only [hD])
    nlinarith only [hh]
  have hgap := triangulation_upper_gap hS0 hS1 ht0 htS hHp hHsq
  linarith only [hdelta,hmono,hV,hgap]

/-- Under the stated error bounds, the squared distance between points on opposite semicircles
is at most the square of the product of 1.37 and `q`. -/
private theorem triangulation_opposite_hemispheres {u v x y S t D H q : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hx : x ∈ Set.Icc 0 1) (hv : 0 ≤ v) (hy : 0 ≤ y)
    (huv : u^2+v^2=1) (hxy : x^2+y^2=1)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 2/5) (ht0 : 0 ≤ t) (htS : t ≤ S/4)
    (hvSmall : v ≤ 3*t/2) (hD : 9/10 ≤ D) (hDH : D ≤ H)
    (hHsq : H^2=(1-t)^2+S) (hraw : x < u → u-3*t/2 ≤ D*x)
    (hq0 : 0 ≤ q) (hqsq : q^2=S) (hq1 : q ≤ 16/25) :
    (x-u)^2+(y+v)^2 ≤ (137/100*q)^2 := by
  have ht1 : t ≤ 1/10 := by linarith only [htS,hS1]
  by_cases hux : u ≤ x
  · have hyv : y ≤ v := by nlinarith only [huv,hxy,hu.1,hx.1,hux,hv,hy]
    have hdot1 := mul_nonneg hu.1 (sub_nonneg.2 hux)
    have hdot2 := mul_nonneg hv (sub_nonneg.2 hyv)
    have hc : (x-u)^2+(y+v)^2 ≤ 4*v^2 := by nlinarith only [hdot1,hdot2,huv,hxy]
    have hvsq : v^2 ≤ 9*t^2/4 := by nlinarith only [hv,hvSmall,ht0]
    have htSq : t^2 ≤ S/40 := by
      have h := mul_le_mul htS ht1 ht0 (by positivity : (0 : ℝ) ≤ S/4)
      nlinarith only [h]
    nlinarith only [hc,hvsq,htSq,hqsq,hS0]
  · have hdelta0 : 0 ≤ u-x := by linarith only [hux]
    have hdelta := triangulation_wrong_gap hu huv hS0 hS1 ht0 htS hD hDH hHsq
      (hraw (lt_of_not_ge hux))
    have hvS : v ≤ 3*S/8 := by linarith only [hvSmall,htS]
    have hvSq : v^2 ≤ 9*S^2/64 := by nlinarith only [hvS,hv,hS0]
    have hvs : v^2/9 ≤ S/160 := by
      have hs := mul_nonneg hS0 (show 0 ≤ 2/5-S by linarith only [hS1])
      nlinarith only [hvSq,hs]
    have hYS : y^2 ≤ v^2+2*(u-x) := by
      have hm := mul_le_mul_of_nonneg_left (show u+x ≤ 2 by linarith only [hu.2,hx.2]) hdelta0
      nlinarith only [hm,huv,hxy]
    have hch : (x-u)^2+(y+v)^2 ≤ 2*v^2+2*(u-x)+2*v*y := by
      have hm := mul_le_mul_of_nonneg_left hu.2 hdelta0
      nlinarith only [hm,huv,hxy]
    by_cases hq : q ≤ 14/25
    · have hgap : (5*S/8)/(1+S/4) ≤ 5*S/8 := by
        apply (div_le_iff₀ (show 0 < 1+S/4 by positivity)).2
        nlinarith only [sq_nonneg S]
      have hd : u-x ≤ 16*S/25 := by linarith only [hdelta,hgap,hvs,hS0]
      have hvq : v ≤ 21*q/100 := by
        have hm := mul_le_mul_of_nonneg_left hq hq0
        nlinarith only [hm,hqsq,hvS]
      have hvqSq : v^2 ≤ (21*q/100)^2 := by nlinarith only [hvq,hv,hq0]
      have hyq : y ≤ 29*q/25 := by nlinarith only [hYS,hd,hvqSq,hqsq,hy,hq0]
      have hprod := mul_le_mul hvq hyq hy (by positivity : (0 : ℝ) ≤ 21*q/100)
      nlinarith only [hch,hd,hvqSq,hprod,hqsq,hS0]
    · have hS : 4/19 ≤ S := by nlinarith only [hq,hq0,hqsq]
      have hgap : (5*S/8)/(1+S/4) ≤ 19*S/32 := by
        apply (div_le_iff₀ (show 0 < 1+S/4 by positivity)).2
        have hm := mul_nonneg hS0 (show 0 ≤ S-4/19 by linarith only [hS])
        nlinarith only [hm]
      have hd : u-x ≤ 3*S/5 := by linarith only [hdelta,hgap,hvs]
      have hvq : v ≤ 6*q/25 := by
        have hm := mul_le_mul_of_nonneg_left hq1 hq0
        nlinarith only [hm,hqsq,hvS]
      have hvqSq : v^2 ≤ (6*q/25)^2 := by nlinarith only [hvq,hv,hq0]
      have hyq : y ≤ 113*q/100 := by nlinarith only [hYS,hd,hvqSq,hqsq,hy,hq0]
      have hprod := mul_le_mul hvq hyq hy (by positivity : (0 : ℝ) ≤ 6*q/25)
      nlinarith only [hch,hd,hvqSq,hprod,hqsq,hS0]

/-- A real number and its cosine-arccosine clipping have nonnegative product. -/
private theorem triangulation_clipping_sign (z : ℝ) :
    0 ≤ z*Real.cos (Real.arccos z) := by
  by_cases hz1 : 1 ≤ z
  · rw [Real.arccos_eq_zero.2 hz1,Real.cos_zero,mul_one]
    linarith only [hz1]
  · by_cases hz0 : z ≤ -1
    · rw [Real.arccos_eq_pi.2 hz0,Real.cos_pi]
      nlinarith only [hz0]
    · rw [Real.cos_arccos (by linarith only [hz0]) (by linarith only [hz1])]
      exact mul_self_nonneg z

/-- If the absolute clipped value is smaller than that of a point in the unit interval centered
at zero, clipping leaves the original value unchanged. -/
private theorem triangulation_clipping_inside {z u : ℝ}
    (hu : |u| ≤ 1) (hx : |Real.cos (Real.arccos z)| < |u|) :
    Real.cos (Real.arccos z)=z := by
  have hz1 : z < 1 := by
    by_contra h
    rw [Real.arccos_eq_zero.2 (le_of_not_gt h),Real.cos_zero,abs_one] at hx
    linarith only [hx,hu]
  have hz0 : -1 < z := by
    by_contra h
    rw [Real.arccos_eq_pi.2 (le_of_not_gt h),Real.cos_pi,abs_neg,abs_one] at hx
    linarith only [hx,hu]
  exact Real.cos_arccos hz0.le hz1.le

/-- The reconstructed point on the upper unit semicircle has squared error at most the square of
the product of 1.37 and `q` under the stated perturbation assumptions. -/
private theorem triangulation_circle_error {u v z D H S t q : ℝ}
    (hu : u ∈ Set.Icc (-1) 1) (huv : u^2+v^2=1)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 2/5) (ht0 : 0 ≤ t) (htS : t ≤ S/4)
    (hD : 9/10 ≤ D) (hDH : D ≤ H) (hHsq : H^2=(1-t)^2+S)
    (hDerr : |D^2-1| ≤ S-2*t+t^2) (hz : |D*z-u| ≤ 3*t/2)
    (hvWrong : v < 0 → |v| ≤ 3*t/2) (hq0 : 0 ≤ q) (hqsq : q^2=S) (hq1 : q ≤ 16/25) :
    (Real.cos (Real.arccos z)-u)^2+(Real.sin (Real.arccos z)-v)^2 ≤ (137/100*q)^2 := by
  let x := Real.cos (Real.arccos z)
  let y := Real.sin (Real.arccos z)
  have hx : x ∈ Set.Icc (-1) 1 := ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hy : 0 ≤ y := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hxy : x^2+y^2=1 := by simp [x,y]
  have ht1 : t ≤ 1/10 := by linarith only [htS,hS1]
  have hDp : 0 < D := by linarith only [hD]
  change (x-u)^2+(y-v)^2 ≤ _
  by_cases hv : 0 ≤ v
  · have hclip := triangulation_cosine_clipping z u hu
    have hraw : |z-u| ≤ (|1-D|+3*t/2)/D := by
      have he : z-u=((D*z-u)+(1-D)*u)/D := by field_simp; ring
      rw [he,abs_div,abs_of_pos hDp]
      apply (div_le_div_iff_of_pos_right hDp).2
      have hh := abs_add_le (D*z-u) ((1-D)*u)
      have hm := mul_le_mul_of_nonneg_left (abs_le.2 hu) (abs_nonneg (1-D))
      rw [abs_mul] at hh
      nlinarith only [hh,hm,hz]
    have hgap := triangulation_scale_gap hS0 ht0 ht1 htS hD hDerr
    have hbound := triangulation_hemisphere hu hx hv hy huv hxy
    dsimp [x] at hbound ⊢
    nlinarith only [hbound,hclip,hraw,hgap,hqsq,hS0]
  · have hvlt : v < 0 := lt_of_not_ge hv
    have hvSmall := hvWrong hvlt
    have hUs : |u| ≥ 97/100 := by
      have hv1 : |v| ≤ 3/20 := by linarith only [hvSmall,ht1]
      have hvsq : v^2 ≤ (3/20)^2 := by nlinarith only [sq_abs v,abs_nonneg v,hv1]
      nlinarith only [huv,sq_abs u,abs_nonneg u,hvsq]
    have hzerr := abs_le.1 hz
    have htz : 3*t/2 ≤ 3/20 := by linarith only [ht1]
    have huz : 0 < u*z := by
      by_cases hu0 : 0 ≤ u
      · have huP : 0 < u := by rw [abs_of_nonneg hu0] at hUs; linarith only [hUs]
        have hzP : 0 < z := by nlinarith only [hzerr.1,hUs,abs_of_nonneg hu0,htz,hDp]
        exact mul_pos huP hzP
      · have huP : u < 0 := lt_of_not_ge hu0
        have hzP : z < 0 := by rw [abs_of_neg huP] at hUs; nlinarith only [hzerr.2,hUs,htz,hDp]
        exact mul_pos_of_neg_of_neg huP hzP
    have hzx := triangulation_clipping_sign z
    have hux : 0 ≤ u*x := by
      dsimp [x]
      by_cases hu0 : 0 ≤ u
      · have hzP : 0 < z := by nlinarith only [huz,hu0]
        have hx0 : 0 ≤ Real.cos (Real.arccos z) := by nlinarith only [hzx,hzP]
        exact mul_nonneg hu0 hx0
      · have hzP : z < 0 := by nlinarith only [huz,lt_of_not_ge hu0]
        have hx0 : Real.cos (Real.arccos z) ≤ 0 := by nlinarith only [hzx,hzP]
        exact mul_nonneg_of_nonpos_of_nonpos (lt_of_not_ge hu0).le hx0
    have habsprod : |x| * |u|=x*u := by rw [← abs_mul,abs_of_nonneg (by nlinarith only [hux])]
    have hxx : (|x|-|u|)^2=(x-u)^2 := by nlinarith only [sq_abs x,sq_abs u,habsprod]
    have hc := triangulation_opposite_hemispheres
      (show |u| ∈ Set.Icc 0 1 from ⟨abs_nonneg _,abs_le.2 hu⟩)
      (show |x| ∈ Set.Icc 0 1 from ⟨abs_nonneg _,abs_le.2 hx⟩)
      (abs_nonneg v) hy (by simpa only [sq_abs] using huv)
      (by simpa only [sq_abs] using hxy) hS0 hS1 ht0 htS hvSmall hD hDH hHsq
      (by
        intro hxu
        have hxe : x=z := triangulation_clipping_inside (abs_le.2 hu) hxu
        have hh := abs_sub_abs_le_abs_sub u (D*z)
        rw [abs_mul,abs_of_pos hDp] at hh
        rw [hxe]
        have hz' : |u-D*z| ≤ 3*t/2 := by simpa only [abs_sub_comm] using hz
        linarith only [hh,hz']) hq0 hqsq hq1
    rw [hxx,abs_of_neg hvlt] at hc
    nlinarith only [hc]

/-- The signed arccosine reconstruction has squared error at most 1.37 squared times the square
of the sum of the two normalization errors. -/
private theorem triangulation_normalized {mu nu U V u v z K : ℝ}
    (hm0 : 0 ≤ mu) (hn0 : 0 ≤ nu) (hm1 : mu^2 ≤ 1/10) (hn1 : nu^2 ≤ 1/10)
    (hU : |U-1| ≤ mu^2) (hV : |V-1| ≤ nu^2)
    (hu : u ∈ Set.Icc (-1) 1) (huv : u^2+v^2=1)
    (hz : |Real.sqrt (U*V)*z-u| ≤ 3*(mu*nu)/2)
    (hK : |K-v| ≤ 3*(mu*nu)/2) :
    (Real.cos ((if K < 0 then -1 else 1)*Real.arccos z)-u)^2
      +(Real.sin ((if K < 0 then -1 else 1)*Real.arccos z)-v)^2
      ≤ (137/100*(mu+nu))^2 := by
  let D := Real.sqrt (U*V)
  let H := Real.sqrt ((1+mu^2)*(1+nu^2))
  let t := mu*nu
  let S := (mu+nu)^2
  let sg : ℝ := if K < 0 then -1 else 1
  have hUb := abs_le.1 hU
  have hVb := abs_le.1 hV
  have hU0 : 9/10 ≤ U := by linarith only [hUb.1,hm1]
  have hV0 : 9/10 ≤ V := by linarith only [hVb.1,hn1]
  have hUpos : 0 < U := by linarith only [hU0]
  have hVpos : 0 < V := by linarith only [hV0]
  have hDsq : D^2=U*V := Real.sq_sqrt (mul_pos hUpos hVpos).le
  have hD0 : 9/10 ≤ D := by
    have hh := mul_le_mul hU0 hV0 (by norm_num : (0 : ℝ) ≤ 9/10) hUpos.le
    have h := Real.sqrt_nonneg (U*V)
    change 0 ≤ D at h
    nlinarith only [hh,hDsq,h]
  have hupper : U*V ≤ (1+mu^2)*(1+nu^2) := mul_le_mul
    (by linarith only [hUb.2]) (by linarith only [hVb.2]) hVpos.le (by positivity)
  have hlower : (1-mu^2)*(1-nu^2) ≤ U*V := mul_le_mul
    (by linarith only [hUb.1]) (by linarith only [hVb.1])
    (by linarith only [hn1]) hUpos.le
  have hHsq : H^2=(1-t)^2+S := by
    dsimp [H]
    rw [Real.sq_sqrt (by positivity)]
    dsimp [t,S]
    ring
  have hDH : D ≤ H := by
    have h := Real.sqrt_nonneg ((1+mu^2)*(1+nu^2))
    change 0 ≤ H at h
    dsimp [t,S] at hHsq
    nlinarith only [hupper,hDsq,hHsq,h,hD0]
  have hDerr : |D^2-1| ≤ S-2*t+t^2 := by
    apply abs_le.2
    dsimp [S,t]
    constructor <;> nlinarith only [hupper,hlower,hDsq]
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS1 : S ≤ 2/5 := by dsimp [S]; nlinarith only [hm1,hn1,sq_nonneg (mu-nu)]
  have ht0 : 0 ≤ t := mul_nonneg hm0 hn0
  have htS : t ≤ S/4 := by dsimp [t,S]; nlinarith only [sq_nonneg (mu-nu)]
  have hq0 : 0 ≤ mu+nu := add_nonneg hm0 hn0
  have hq1 : mu+nu ≤ 16/25 := by dsimp [S] at hS1; nlinarith only [hS1,hq0]
  have hsg : sg^2=1 := by dsimp [sg]; split_ifs <;> norm_num
  have hsgAbs : |sg*v|=|v| := by dsimp [sg]; split_ifs <;> simp
  have hvWrong : sg*v < 0 → |sg*v| ≤ 3*t/2 := by
    intro hv
    have hKb := abs_le.1 hK
    rw [hsgAbs]
    dsimp [sg] at hv
    split_ifs at hv with h
    · have hv0 : 0 ≤ v := by linarith only [hv]
      rw [abs_of_nonneg hv0]
      dsimp [t]
      linarith only [h,hKb.1]
    · have hv0 : v < 0 := by simpa only [one_mul] using hv
      rw [abs_of_neg hv0]
      dsimp [t]
      linarith only [h,hKb.2]
  have hcircle := triangulation_circle_error hu
    (show u^2+(sg*v)^2=1 by rw [mul_pow,hsg,one_mul]; exact huv)
    hS0 hS1 ht0 htS hD0 hDH hHsq hDerr hz hvWrong hq0 rfl hq1
  have he :
      (Real.cos (sg*Real.arccos z)-u)^2+(Real.sin (sg*Real.arccos z)-v)^2=
        (Real.cos (Real.arccos z)-u)^2+(Real.sin (Real.arccos z)-sg*v)^2 := by
    dsimp [sg]
    split_ifs <;> simp only [neg_one_mul,one_mul,Real.cos_neg,Real.sin_neg]
    all_goals ring
  change (Real.cos (sg*Real.arccos z)-u)^2+(Real.sin (sg*Real.arccos z)-v)^2 ≤ _
  rw [he]
  exact hcircle

/-- Three squared-distance measurement errors bound the resulting normalized residual error by
the stated scale-dependent quantity. -/
private theorem triangulation_residual {r b eps R C A w : ℝ}
    (hr : 0 < r) (hb : 0 < b)
    (hR : |R-r^2| ≤ eps*b^2) (hC : |C-b^2| ≤ eps*b^2)
    (hA : |A-(r^2+b^2-2*r*b*w)| ≤ eps*b^2) :
    |(R+C-A)/(2*r*b)-w| ≤ 3*eps*b/(2*r) := by
  have he : (R+C-A)/(2*r*b)-w=
      ((R-r^2)+(C-b^2)-(A-(r^2+b^2-2*r*b*w)))/(2*r*b) := by field_simp; ring
  rw [he,abs_div,abs_of_pos (by positivity : (0 : ℝ) < 2*r*b)]
  have hnum : |(R-r^2)+(C-b^2)-(A-(r^2+b^2-2*r*b*w))| ≤ 3*eps*b^2 := by
    have h1 := abs_add_le ((R-r^2)+(C-b^2)) (-(A-(r^2+b^2-2*r*b*w)))
    rw [abs_neg,← sub_eq_add_neg] at h1
    have h2 := abs_add_le (R-r^2) (C-b^2)
    linarith only [h1,h2,hR,hC,hA]
  calc
    _ ≤ (3*eps*b^2)/(2*r*b) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 3*eps*b/(2*r) := by field_simp

/-- The phase reconstructed from perturbed squared-distance data is within the stated complex
norm bound of the true phase. -/
private theorem triangulation_phase_estimate {r b eps phi R C S T : ℝ}
    (hr : 0 < r) (hb : 0 < b) (heps : 0 < eps) (heps1 : eps ≤ 1/10)
    (hdomain : eps*b^2 ≤ r^2/10)
    (hR : |R-r^2| ≤ eps*b^2) (hC : |C-b^2| ≤ eps*b^2)
    (hS : |S-(r^2+b^2-2*r*b*Real.cos phi)| ≤ eps*b^2)
    (hT : |T-(r^2+b^2-2*r*b*Real.sin phi)| ≤ eps*b^2) :
    ‖Complex.exp (((if R+C-T < 0 then -1 else 1)*Real.arccos ((R+C-S)/(2*Real.sqrt (R*C))))*Complex.I)
        -Complex.exp (phi*Complex.I)‖ ≤ 137/100*Real.sqrt eps*(b/r+1) := by
  let mu := Real.sqrt eps*b/r
  let nu := Real.sqrt eps
  let U := R/r^2
  let V := C/b^2
  let K := (R+C-T)/(2*r*b)
  let z := (R+C-S)/(2*Real.sqrt (R*C))
  have hmusq : mu^2=eps*b^2/r^2 := by
    dsimp [mu]
    rw [div_pow,mul_pow,Real.sq_sqrt heps.le]
  have hnusq : nu^2=eps := Real.sq_sqrt heps.le
  have hmunu : mu*nu=eps*b/r := by
    dsimp [mu,nu]
    have hs := Real.sq_sqrt heps.le
    field_simp
    nlinarith only [hs]
  have hm1 : mu^2 ≤ 1/10 := by
    rw [hmusq]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).2
    linarith only [hdomain]
  have hn1 : nu^2 ≤ 1/10 := by rw [hnusq]; exact heps1
  have hU : |U-1| ≤ mu^2 := by
    rw [hmusq]
    have hEq : U-1=(R-r^2)/r^2 := by dsimp [U]; field_simp
    rw [hEq,abs_div,abs_of_pos (sq_pos_of_pos hr)]
    exact div_le_div_of_nonneg_right hR (sq_nonneg r)
  have hV : |V-1| ≤ nu^2 := by
    rw [hnusq]
    have hEq : V-1=(C-b^2)/b^2 := by dsimp [V]; field_simp
    rw [hEq,abs_div,abs_of_pos (sq_pos_of_pos hb)]
    apply (div_le_iff₀ (sq_pos_of_pos hb)).2
    exact hC
  have hRb := abs_le.1 hR
  have hCb := abs_le.1 hC
  have hR0 : 0 < R := by nlinarith only [hRb.1,hdomain,sq_pos_of_pos hr]
  have hC0 : 0 < C := by
    have hh := mul_le_mul_of_nonneg_right heps1 (sq_nonneg b)
    nlinarith only [hCb.1,hh,sq_pos_of_pos hb]
  have hroot : 0 < Real.sqrt (R*C) := Real.sqrt_pos.2 (mul_pos hR0 hC0)
  have hRC : R*C=(r*b)^2*(U*V) := by dsimp [U,V]; field_simp
  have hscale : Real.sqrt (R*C)=r*b*Real.sqrt (U*V) := by
    rw [hRC,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_pos hr hb).le]
  have hzEq : Real.sqrt (U*V)*z=(R+C-S)/(2*r*b) := by
    dsimp [z]
    rw [hscale]
    have huvp : 0 < Real.sqrt (U*V) := by
      apply (mul_pos_iff_of_pos_left (mul_pos hr hb)).1
      rwa [← hscale]
    field_simp
  have hz : |Real.sqrt (U*V)*z-Real.cos phi| ≤ 3*(mu*nu)/2 := by
    rw [hzEq,hmunu]
    have hh := triangulation_residual hr hb hR hC hS
    convert hh using 1
    ring
  have hK : |K-Real.sin phi| ≤ 3*(mu*nu)/2 := by
    rw [hmunu]
    have hh := triangulation_residual hr hb hR hC hT
    convert hh using 1
    ring
  have hcircle := triangulation_normalized (show 0 ≤ mu by dsimp [mu]; positivity)
    (Real.sqrt_nonneg eps) hm1 hn1 hU hV
    ⟨Real.neg_one_le_cos phi,Real.cos_le_one phi⟩
    (by nlinarith only [Real.sin_sq_add_cos_sq phi]) hz hK
  have hsg : (if K < 0 then (-1 : ℝ) else 1)=(if R+C-T < 0 then -1 else 1) := by
    dsimp [K]
    simp only [div_neg_iff,show 0 < 2*r*b by positivity,not_lt_of_ge (show 0 ≤ 2*r*b by positivity),
      and_true,and_false,false_or]
  rw [hsg] at hcircle
  let angle := (if R+C-T < 0 then (-1 : ℝ) else 1)*Real.arccos z
  have hnorm : ‖Complex.exp (angle*Complex.I)-Complex.exp (phi*Complex.I)‖^2=
      (Real.cos angle-Real.cos phi)^2+(Real.sin angle-Real.sin phi)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,pow_two]
  have hq : mu+nu=Real.sqrt eps*(b/r+1) := by dsimp [mu,nu]; ring
  have hcsg : (if R+C-T < 0 then (-1 : ℂ) else 1)*↑(Real.arccos z)=(angle : ℂ) := by
    dsimp [angle]
    split_ifs <;> simp
  change ‖Complex.exp (((if R+C-T < 0 then (-1 : ℂ) else 1)*↑(Real.arccos z))*Complex.I)
    -Complex.exp (phi*Complex.I)‖ ≤ _
  rw [hcsg]
  change (Real.cos angle-Real.cos phi)^2+(Real.sin angle-Real.sin phi)^2 ≤ _ at hcircle
  rw [← hnorm,hq] at hcircle
  have hbound0 : 0 ≤ 137/100*Real.sqrt eps*(b/r+1) := by positivity
  have hnorm0 := norm_nonneg (Complex.exp (angle*Complex.I)-Complex.exp (phi*Complex.I))
  nlinarith only [hcircle,hbound0,hnorm0]

/-- Establishes `TriangulationStability` for reconstructing a phase from the prescribed
perturbed measurements. -/
theorem triangulationStability : TriangulationStability := by
  intro r c theta tau lam eps R S T C tau' hr hc hlam heps heps1 hdomain hR hS hT hC
  let b := lam*c
  let angle : ℝ := (if R+C-T < 0 then -1 else 1)*Real.arccos ((R+C-S)/(2*Real.sqrt (R*C)))
  have hb : 0 < b := mul_pos hlam hc
  have hb2 : b^2=lam^2*c^2 := mul_pow lam c 2
  have hcross : 2*r*b=2*lam*r*c := by dsimp [b]; ring
  have hphase := triangulation_phase_estimate hr hb heps heps1
    (by simpa only [hb2,mul_assoc] using hdomain)
    (by simpa only [hb2,mul_assoc] using hR)
    (by simpa only [hb2,mul_assoc] using hC)
    (phi := theta-tau)
    (by simpa only [hb2,hcross,mul_assoc] using hS)
    (by simpa only [hb2,hcross,mul_assoc] using hT)
  have hcsg : (if R+C-T < 0 then (-1 : ℂ) else 1)*
      ↑(Real.arccos ((R+C-S)/(2*Real.sqrt (R*C))))=(angle : ℂ) := by
    dsimp [angle]
    split_ifs <;> simp
  rw [hcsg] at hphase
  let E := fun a : ℝ => Complex.exp (a*Complex.I)
  have hEadd (a d : ℝ) : E (a+d)=E a*E d := by
    dsimp [E]
    rw [Complex.ofReal_add,add_mul,Complex.exp_add]
  have hEnorm (a : ℝ) : ‖E a‖=1 := Complex.norm_exp_ofReal_mul_I a
  have hEtheta : E tau*E (theta-tau)=E theta := by rw [← hEadd]; congr 1; ring
  have hsplit : E (tau'+angle)-E theta=
      (E tau'-E tau)*E angle+E tau*(E angle-E (theta-tau)) := by
    rw [hEadd]
    calc
      _ = E tau'*E angle-E tau*E (theta-tau) := by rw [hEtheta]
      _ = _ := by ring
  have hbound : ‖E (tau'+angle)-E theta‖ ≤ ‖E tau'-E tau‖+137/100*Real.sqrt eps*(b/r+1) := by
    rw [hsplit]
    calc
      _ ≤ ‖(E tau'-E tau)*E angle‖+‖E tau*(E angle-E (theta-tau))‖ := norm_add_le _ _
      _ = ‖E tau'-E tau‖+‖E angle-E (theta-tau)‖ := by rw [norm_mul,norm_mul,hEnorm,hEnorm,mul_one,one_mul]
      _ ≤ _ := add_le_add le_rfl hphase
  have hfactor : Real.sqrt (lam^2*c^2/r^2)=b/r := by
    have he : lam^2*c^2/r^2=(b/r)^2 := by rw [div_pow,hb2]
    rw [he,Real.sqrt_sq (div_pos hb hr).le]
  rw [hfactor]
  have hcast : ((tau'+angle : ℝ) : ℂ) = (tau' : ℂ)+
      (if R+C-T < 0 then (-1 : ℂ) else 1)*↑(Real.arccos ((R+C-S)/(2*Real.sqrt (R*C)))) := by
    rw [Complex.ofReal_add,hcsg]
  rw [← hcast]
  change ‖E (tau'+angle)-E theta‖ ≤ ‖E tau'-E tau‖+1.37*Real.sqrt eps*(b/r+1)
  convert hbound using 1
  norm_num

end Qatlib.Foundations.ComplexGeometry.PhaseRecovery
