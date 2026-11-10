/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.Lemma3
import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.SpectralGapProof
set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.Connectivity

open Finset
open Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
open Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem abs_apply_le_l2norm {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    |x i| ≤ l2norm x := by
  have h1 : (x i) ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  have h2 : |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs (x i)).symm
  rw [h2]
  exact Real.sqrt_le_sqrt h1

theorem corollary4_disconnected (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (k : ℕ) (s t : V) (h : ¬ G.Reachable s t) :
    (walkQ G d ^ k) (t, t) (s, s) = 0 := by
  rw [walkQ_pow_apply_diag]
  apply walkM_pow_apply_eq_zero G d s _ k t h
  intro v hv
  exact basisVec_apply_of_ne (fun hvs => hv (hvs ▸ SimpleGraph.Reachable.rfl))

theorem corollary4_connected (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (s t : V) (hconn : G.Reachable s t)
    (hgap : SpectralGap G d s) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
      Real.log (2 * (Fintype.card V : ℝ)) ≤ (k : ℝ)) :
    1 / (2 * (Fintype.card V : ℝ)) < (walkQ G d ^ k) (t, t) (s, s) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hnpos : (0 : ℝ) < n := by
    have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    rw [hn_def]
    exact_mod_cast h
  have hε : (0 : ℝ) < 1 / (2 * n) := by positivity

  have hk' : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
      Real.log (1 / (1 / (2 * (Fintype.card V : ℝ)))) ≤ (k : ℝ) := by
    rw [one_div, one_div, inv_inv]
    exact hk
  have hmix := lemma3_mixing G hreg hd hε s hgap k hk'

  have hdec : (walkQ G d ^ k) (t, t) (s, s) =
      ((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) t + uniformOn G s t := by
    rw [walkQ_pow_apply_diag]
    have h : (walkM G d ^ k) *ᵥ basisVec s =
        (walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s) + uniformOn G s := by
      rw [Matrix.mulVec_sub, walkM_pow_mulVec_uniformOn G hreg, sub_add_cancel]
    rw [h, Pi.add_apply]

  have hsmall : |((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) t| < 1 / (2 * n) := by
    have h1 : |((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) t| ≤
        l2norm ((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) :=
      abs_apply_le_l2norm _ t
    have h2 : l2norm ((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) =
        l2norm (lemma3State G d k s) := by
      rw [lemma3State_eq_diagLift, l2norm_diagLift]
      congr 1
      rw [Matrix.mulVec_sub, walkM_pow_mulVec_uniformOn G hreg]
    rw [h2] at h1
    exact lt_of_le_of_lt h1 hmix
  have hlower : -((1 : ℝ) / (2 * n)) <
      ((walkM G d ^ k) *ᵥ (basisVec s - uniformOn G s)) t := (abs_lt.mp hsmall).1

  have huniform : uniformOn G s t = 1 / (compSize G s : ℝ) := by
    simp [uniformOn, hconn]
  have hcomp_le : (compSize G s : ℝ) ≤ n := by
    have h : compSize G s ≤ Fintype.card V := Finset.card_le_univ _
    rw [hn_def]
    exact_mod_cast h
  have hcomp_pos : (0 : ℝ) < (compSize G s : ℝ) := compSize_pos G s
  have hinv : 1 / n ≤ 1 / (compSize G s : ℝ) :=
    one_div_le_one_div_of_le hcomp_pos hcomp_le
  have hn_ne : n ≠ 0 := ne_of_gt hnpos
  have hone : 2 * (1 / (2 * n)) = 1 / n := by
    field_simp
  have h2 : 2 * (1 / (2 * n)) ≤ 1 / (compSize G s : ℝ) := by
    rw [hone]
    exact hinv
  rw [hdec, huniform]
  linarith

theorem corollary4_overlap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (s t : V) (hconn : G.Reachable s t)
    (hgap : SpectralGap G d s) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
      Real.log (2 * (Fintype.card V : ℝ)) ≤ (k : ℝ)) :
    1 / (4 * (Fintype.card V : ℝ) ^ 2) < ((walkQ G d ^ k) (t, t) (s, s)) ^ 2 := by
  classical
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    exact_mod_cast h
  have hge := corollary4_connected G hreg hd s t hconn hgap k hk
  have hhalf : (0 : ℝ) < 1 / (2 * (Fintype.card V : ℝ)) := by positivity
  have hsq : (1 / (2 * (Fintype.card V : ℝ))) ^ 2 <
      ((walkQ G d ^ k) (t, t) (s, s)) ^ 2 := by
    have hprod : (0 : ℝ) <
        (((walkQ G d ^ k) (t, t) (s, s)) - 1 / (2 * (Fintype.card V : ℝ))) *
          (((walkQ G d ^ k) (t, t) (s, s)) + 1 / (2 * (Fintype.card V : ℝ))) :=
      mul_pos (sub_pos.mpr hge) (by linarith)
    nlinarith [hprod]
  have heq : (1 / (2 * (Fintype.card V : ℝ))) ^ 2 =
      1 / (4 * (Fintype.card V : ℝ) ^ 2) := by
    field_simp
    ring
  linarith

theorem corollary4_connected_uncond (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (s t : V) (hconn : G.Reachable s t) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
      Real.log (2 * (Fintype.card V : ℝ)) ≤ (k : ℝ)) :
    1 / (2 * (Fintype.card V : ℝ)) < (walkQ G d ^ k) (t, t) (s, s) :=
  corollary4_connected G hreg hd s t hconn (spectralGap_of_regular G hreg hd s) k hk

theorem corollary4_overlap_uncond (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (s t : V) (hconn : G.Reachable s t) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
      Real.log (2 * (Fintype.card V : ℝ)) ≤ (k : ℝ)) :
    1 / (4 * (Fintype.card V : ℝ) ^ 2) < ((walkQ G d ^ k) (t, t) (s, s)) ^ 2 :=
  corollary4_overlap G hreg hd s t hconn (spectralGap_of_regular G hreg hd s) k hk

end

end Qatlib.Papers.QWalkConnect98.MainResults.Connectivity
