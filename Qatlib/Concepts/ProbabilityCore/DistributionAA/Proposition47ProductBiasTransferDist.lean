/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition47ProductBiasTransferStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma37BiasGadgetDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma46BiasContinuityDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeGadgetDegree
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeBiasTransferBounds
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDegenerateVariance

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the product-bias AA transfer result of Proposition 4.7. -/
theorem proposition47ProductBiasTransfer : Proposition47ProductBiasTransfer := by
  intro p q hp0 hp1 hq0 hq1 S hAA D hD n d v hv hv1 f hb hd hvar
  change v ≤ cubeVar n (muWeight q n) f at hvar
  let a := min (min p (1-p)) (min q (1-q))
  have ha : 0 < a := lt_min (lt_min hp0 (sub_pos.2 hp1)) (lt_min hq0 (sub_pos.2 hq1))
  have hd0 : 0 < d := by
    by_contra hd0
    have he : d=0 := by omega
    subst d
    rw [cube_degree_zero_variance (muWeight_cubeWeight hq0.le hq1.le n) hd] at hvar
    linarith only [hv,hvar]
  let m := biasGadgetSize a D v d
  obtain ⟨g,hg0,hg1⟩ := lemma37BiasGadget p q hp0 hp1 hq0.le hq1.le m
  let r := cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)
  have hr : r ∈ Set.Icc 0 1 := cube_expect_range (muWeight_cubeWeight hp0.le hp1.le m)
    (fun z => by cases g z <;> simp)
  have hAtom : (2 : ℝ)^(-(min p (1-p)*(m : ℝ))) ≤ (2 : ℝ)^(-(a*(m : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg m))
  have hqr : |q-r| ≤ (2 : ℝ)^(-(a*(m : ℝ))) := by
    rw [abs_sub_comm,abs_of_nonneg (show 0 ≤ r-q by exact sub_nonneg.2 hg0)]
    exact (show r-q ≤ (2 : ℝ)^(-(min p (1-p)*(m : ℝ))) by linarith only [hg1]).trans hAtom
  have herror := cube_bias_gadget_error ha hv hv1 hd0 hD
  have hcont := lemma46BiasContinuity n d f hb hd q r hq0.le hq1.le hr.1 hr.2
  have hδ : 16*(d : ℝ)^2*|q-r| ≤ 16*(d : ℝ)^2*(2 : ℝ)^(-(a*(m : ℝ))) :=
    mul_le_mul_of_nonneg_left hqr (by positivity)
  have hvr : v/2 ≤ cubeVar n (muWeight r n) f := by
    have he := (abs_le.1 hcont.1).2
    have ht : 16*(d : ℝ)^2*|q-r| ≤ v/2 := hδ.trans herror.2
    linarith only [he,ht,hvar]
  let F := fun z : Fin (n*m) → Bool => f (cubeBlockMap g z)
  have hFb (z) : F z ∈ Set.Icc (0 : ℝ) 1 := hb _
  have hFd : CubeDegreeLE (d*m) F := cube_block_degree hd g
  have hFv : v/2 ≤ cubeVar (n*m) (muWeight p (n*m)) F := by
    rw [cube_block_variance hp0.le hp1.le g f]
    exact hvr
  obtain ⟨e,he⟩ := hAA (n*m) (d*m) (v/2) (by positivity) (by linarith) F hFb hFd hFv
  let i := (finProdFinEquiv.symm e).1
  let j := (finProdFinEquiv.symm e).2
  have heij : finProdFinEquiv (i,j)=e := finProdFinEquiv.apply_symm_apply e
  have hInf := cube_block_influence hp0.le hp1.le g f i j
  rw [heij] at hInf
  have hi := he.trans hInf
  have hgap := (abs_le.1 (hcont.2 i)).1
  have hε : 16*(d : ℝ)^2*|q-r| ≤ (v/(d : ℝ))^D := hδ.trans herror.1
  refine ⟨i, ?_⟩
  change S (v/2) (d*m)-(v/(d : ℝ))^D ≤ cubeInf n (muWeight q n) f i
  change S (v/2) (d*m) ≤ cubeInf n (muWeight r n) f i at hi
  linarith only [hi,hgap,hε]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
