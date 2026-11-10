/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformMixerSpectrum
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.AffineGap
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.RankOneSeparation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator Topology
open Filter
open Qatlib.Papers.ProjectorQAOA26.StageStability
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem cost_mixer_norm_le (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R) :
    ‖costOperator E-uniformMixer‖ ≤ R+1 := by
  have hd : ‖costOperator E‖ ≤ R := by
    apply opNorm_diagonal_le (by linarith)
    intro i
    have he0 : 0≤E i := by
      by_cases hi : i=zero
      · subst i; rw [hzero]
      · linarith [(hE i hi).1]
    have heR : E i≤R := by
      by_cases hi : i=zero
      · subst i; rw [hzero]; linarith
      · exact (hE i hi).2
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he0] using! heR
  have hm : ‖uniformMixer (I := I)‖ ≤ 1 :=
    opNorm_one_sub_rankOne_le_one uniformReference_normalized
  exact (norm_sub_le _ _).trans (add_le_add hd hm)

theorem spectralGap_small_time (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (s : ℝ) (hs : 0≤ s) (hsmall : s≤1/(4*(R+1))) :
    1/2 ≤ spectralGap E hL s := by
  have hw := spectralGap_lipschitz E hL s 0
  rw [spectralGap_zero,sub_zero,abs_of_nonneg hs] at hw
  have hn := cost_mixer_norm_le E zero hzero R hR hE
  have hn' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2)) hs
  have hb := (le_div_iff₀ (by positivity : (0:ℝ)<4*(R+1))).mp hsmall
  have ha := neg_abs_le (spectralGap E hL s-1)
  nlinarith

theorem spectralGap_positive_time (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (hL : 2≤Fintype.card I)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    s*(1/(2*Real.sqrt (Fintype.card I:ℝ))) ≤ spectralGap E hL s := by
  rw [actual_spectralGap_rankOne E hL s hs]
  apply mul_le_mul_of_nonneg_left _ hs.le
  exact rankOne_gap_lower E zero hzero hE hL ((1-s)/s) (div_pos (by linarith) hs)

theorem spectralGap_global_lower_interior (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (s : ℝ) (hs : s∈Set.Ico (0:ℝ) 1) :
    1/(8*(R+1)*Real.sqrt (Fintype.card I:ℝ)) ≤ spectralGap E hL s := by
  have hcard : (1:ℝ)≤Fintype.card I := by exact_mod_cast (show 1≤Fintype.card I by omega)
  have hsqrt : 1≤Real.sqrt (Fintype.card I:ℝ) := Real.one_le_sqrt.mpr hcard
  have hsqpos : 0<Real.sqrt (Fintype.card I:ℝ) := by linarith
  by_cases hsmall : s≤1/(4*(R+1))
  · have hh := spectralGap_small_time E zero hzero R hR hE hL s hs.1 hsmall
    have hc : 1/(8*(R+1)*Real.sqrt (Fintype.card I:ℝ))≤1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (show 0≤R+1 by linarith) (show 0≤Real.sqrt (Fintype.card I:ℝ)-1 by linarith)]
    exact hc.trans hh
  · have hslarge : 1/(4*(R+1))≤ s := (lt_of_not_ge hsmall).le
    have hspos : 0<s := lt_of_lt_of_le (by positivity) hslarge
    have hh := spectralGap_positive_time E zero hzero (fun i hi => (hE i hi).1) hL s hspos hs.2
    calc _ = (1/(4*(R+1)))*(1/(2*Real.sqrt (Fintype.card I:ℝ))) := by field_simp;ring
         _ ≤ s*(1/(2*Real.sqrt (Fintype.card I:ℝ))) :=
           mul_le_mul_of_nonneg_right hslarge (by positivity)
         _ ≤ spectralGap E hL s := hh

theorem spectralGap_global_lower (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) :
    1/(8*(R+1)*Real.sqrt (Fintype.card I:ℝ)) ≤ spectralGap E hL s := by
  by_cases hs1 : s<1
  · exact spectralGap_global_lower_interior E zero hzero R hR hE hL s ⟨hs.1,hs1⟩
  · have he : s=1 := by linarith [hs.2]
    subst s
    have ht : Tendsto (spectralGap E hL) (𝓝[<] (1:ℝ)) (𝓝 (spectralGap E hL 1)) :=
      (spectralGap_continuous E hL).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with t ht
    exact spectralGap_global_lower_interior E zero hzero R hR hE hL t ⟨ht.1.le,ht.2⟩

theorem minimumGap_global_lower (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) :
    1/(8*(R+1)*Real.sqrt (Fintype.card I:ℝ)) ≤ minimumGap E hL :=
  spectralGap_global_lower E zero hzero R hR hE hL (gapMinimizer E hL) (gapMinimizer_mem E hL)

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
