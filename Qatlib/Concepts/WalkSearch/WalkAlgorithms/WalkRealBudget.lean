/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.CorrectedWalkBounds
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem walk_root_window (n r a b : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (hb : 0 < b)
    (hl : n^a ≤ r^b) (hu : (r-1)^b < n^a) :
    (n : ℝ)^(a / b : ℝ) ≤ r ∧ (r : ℝ) ≤ (n : ℝ)^(a / b : ℝ)+1 := by
  have root (x : ℕ) : ((x : ℝ)^b)^(1 / b : ℝ) = x := by
    rw [← Real.rpow_natCast_mul (by positivity) b]
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [mul_one_div_cancel hbR, Real.rpow_one]
  have nroot : ((n : ℝ)^a)^(1 / b : ℝ) = (n : ℝ)^(a / b : ℝ) := by
    rw [← Real.rpow_natCast_mul (by positivity) a]
    congr 1
    ring
  constructor
  · have h := Real.rpow_le_rpow (by positivity) (show (n : ℝ)^a ≤ (r : ℝ)^b by exact_mod_cast hl)
      (show (0 : ℝ) ≤ 1 / b by positivity)
    simpa only [root, nroot] using h
  · have h := Real.rpow_le_rpow (by positivity)
      (show ((r-1 : ℕ) : ℝ)^b ≤ (n : ℝ)^a by exact_mod_cast hu.le)
      (show (0 : ℝ) ≤ 1 / b by positivity)
    rw [root, nroot, Nat.cast_sub hr, Nat.cast_one] at h
    linarith

theorem walk_inner_bound (r r' : ℕ) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hl : r^2 ≤ r'^3) (hu : (r'-1)^3 < r^2) :
    ((r'+(r/r')*Nat.sqrt r' : ℕ) : ℝ) ≤ 3*(r : ℝ)^(2/3 : ℝ) := by
  obtain ⟨hlo,hhi⟩ := walk_root_window r r' 2 3 hr hr' (by decide) hl hu
  norm_num only [Nat.cast_ofNat] at hlo hhi
  let A := (r : ℝ)^(2/3 : ℝ)
  have hA : 1 ≤ A := Real.one_le_rpow (by exact_mod_cast hr) (by norm_num)
  have hA3 : A^3 = (r : ℝ)^2 := by
    dsimp [A]
    rw [← Real.rpow_mul_natCast (by positivity) (2/3 : ℝ) 3]
    norm_num [Real.rpow_natCast]
  let D : ℝ := (r/r' : ℕ)
  let S : ℝ := Nat.sqrt r'
  have hD : 0 ≤ D := by positivity
  have hS : 0 ≤ S := by positivity
  have hDS : 0 ≤ D*S := mul_nonneg hD hS
  have hdr : D*(r' : ℝ) ≤ r := by dsimp [D]; exact_mod_cast Nat.div_mul_le_self r r'
  have hs2 : S^2 ≤ (r' : ℝ) := by dsimp [S]; exact_mod_cast Nat.sqrt_le' r'
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ D*(r' : ℝ)) hdr 2
  have hp := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ D^2*(r' : ℝ) by positivity)
  have hprod : (D*S)^2*(r' : ℝ) ≤ (r : ℝ)^2 := by nlinarith only [hh,hp]
  have hprodA := mul_le_mul_of_nonneg_left hlo (sq_nonneg (D*S))
  have hsquare : (D*S)^2 ≤ A^2 := by
    apply (mul_le_mul_iff_left₀ (by linarith : 0 < A)).mp
    nlinarith only [hprod,hprodA,hA3]
  have hds := (sq_le_sq₀ hDS (by linarith : 0 ≤ A)).mp hsquare
  push_cast
  change (r' : ℝ)+D*S ≤ 3*A
  change (r' : ℝ) ≤ A+1 at hhi
  linarith

theorem walk_sqrt_succ (n : ℕ) (hn : 0 < n) :
    ((Nat.sqrt (n+1)+1 : ℕ) : ℝ) ≤ 3*(n : ℝ)^(1/2 : ℝ) := by
  have hs : (Nat.sqrt (n+1) : ℝ)^2 ≤ (n : ℝ)+1 := by
    exact_mod_cast Nat.sqrt_le' (n+1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ)^(1/2 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have he : ((n : ℝ)^(1/2 : ℝ))^2 = n := by
    rw [← Real.rpow_mul_natCast (by positivity) (1/2 : ℝ) 2]
    norm_num
  have hsq : (Nat.sqrt (n+1) : ℝ)^2 ≤ (2*(n : ℝ)^(1/2 : ℝ))^2 := by nlinarith
  have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  push_cast
  linarith

theorem walk_real_budget (n r r' : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hl : n^3 ≤ r^5) (hu : (r-1)^5 < n^3)
    (hl' : r^2 ≤ r'^3) (hu' : (r'-1)^3 < r^2)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover)
    (hk : 1 ≤ kcs.κ) :
    ((kcs.κ*(Nat.log 2 (n+1)+2)*(r*r+(n/r)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r)) +
      sgs.κ*(Nat.log 2 (n+1)+2)*4*(Nat.sqrt (n+1)+1)+3 : ℕ) : ℝ) ≤
      (2^16 : ℕ)*(walkKappa kcs ncs sgs)^3*((Nat.log 2 n+2 : ℕ)^3)*
        (n : ℝ)^(13/10 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let L : ℝ := (Nat.log 2 n+2 : ℕ)
  let K : ℝ := walkKappa kcs ncs sgs
  have hL : 2 ≤ L := by dsimp [L]; exact_mod_cast (show 2 ≤ Nat.log 2 n+2 by omega)
  have hkK : (kcs.κ : ℝ) ≤ K := by
    dsimp [K,walkKappa]; exact_mod_cast (le_max_left kcs.κ (max ncs.κ sgs.κ))
  have hnK : (ncs.κ : ℝ) ≤ K := by
    dsimp [K,walkKappa]; exact_mod_cast ((le_max_left ncs.κ sgs.κ).trans (le_max_right kcs.κ _))
  have hsK : (sgs.κ : ℝ) ≤ K := by
    dsimp [K,walkKappa]; exact_mod_cast ((le_max_right ncs.κ sgs.κ).trans (le_max_right kcs.κ _))
  have hK : 1 ≤ K := (show (1 : ℝ) ≤ kcs.κ by exact_mod_cast hk).trans hkK
  have hlog : ((Nat.log 2 (n+1)+2 : ℕ) : ℝ) ≤ 2*L := by
    dsimp [L]
    exact_mod_cast corrected_log_succ_le n hn
  have hrn : r ≤ n := by
    by_contra h
    have hh : n ≤ r-1 := by omega
    have hh' := Nat.pow_le_pow_left hh 5
    have hp := Nat.pow_le_pow_right hn (by decide : 3 ≤ 5)
    omega
  have hlogr : ((Nat.log 2 (r+1)+2 : ℕ) : ℝ) ≤ 2*L := by
    have hh := Nat.add_le_add_right (Nat.log_mono_right (b:=2) (by omega : r+1 ≤ n+1)) 2
    exact (show ((Nat.log 2 (r+1)+2 : ℕ) : ℝ) ≤ (Nat.log 2 (n+1)+2 : ℕ) by exact_mod_cast hh).trans hlog
  obtain ⟨hroot,hrhi⟩ := walk_root_window n r 3 5 hn hr (by decide) hl hu
  norm_num only [Nat.cast_ofNat] at hroot hrhi
  have powone (e : ℝ) (he : 0 ≤ e) : 1 ≤ (n : ℝ)^e := Real.one_le_rpow hnR he
  have hr2 : (r : ℝ) ≤ 2*(n : ℝ)^(3/5 : ℝ) := by linarith [powone (3/5) (by norm_num)]
  have hrr : (r : ℝ)^2 ≤ 4*(n : ℝ)^(6/5 : ℝ) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hr2 2
    have he : ((n : ℝ)^(3/5 : ℝ))^2 = (n : ℝ)^(6/5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hn0.le (3/5 : ℝ) 2]; norm_num
    simpa only [mul_pow,he,show (2 : ℝ)^2 = 4 by norm_num] using hh
  have hdiv : ((n/r : ℕ) : ℝ) ≤ (n : ℝ)^(2/5 : ℝ) := by
    have hh := corrected_cast_div_le n r hr
    have hd : (n : ℝ)/(r : ℝ) ≤ (n : ℝ)/(n : ℝ)^(3/5 : ℝ) :=
      div_le_div_of_nonneg_left hn0.le (Real.rpow_pos_of_pos hn0 _) hroot
    have he : (n : ℝ)/(n : ℝ)^(3/5 : ℝ) = (n : ℝ)^(2/5 : ℝ) := by
      have hh := Real.rpow_sub hn0 (1 : ℝ) (3/5 : ℝ)
      norm_num at hh
      exact hh.symm
    exact hh.trans (hd.trans_eq he)
  have hrpow : (r : ℝ)^(2/3 : ℝ) ≤ 4*(n : ℝ)^(2/5 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity) hr2 (by norm_num : (0 : ℝ) ≤ 2/3)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le] at hh
    have htwo : (2 : ℝ)^(2/3 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2/3 : ℝ) ≤ 1)
    norm_num only [show (3/5 : ℝ)*(2/3) = 2/5 by norm_num] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg hn0.le (2/5 : ℝ)])
  have hinner : ((r'+(r/r')*Nat.sqrt r' : ℕ) : ℝ) ≤ 12*(n : ℝ)^(2/5 : ℝ) :=
    (walk_inner_bound r r' hr hr' hl' hu').trans (by linarith)
  have hsqrt : (Nat.sqrt r : ℝ) ≤ 2*(n : ℝ)^(3/10 : ℝ) := by
    have hs : (Nat.sqrt r : ℝ)^2 ≤ r := by exact_mod_cast Nat.sqrt_le' r
    have he : ((n : ℝ)^(3/10 : ℝ))^2 = (n : ℝ)^(3/5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hn0.le (3/10 : ℝ) 2]; norm_num
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [Real.rpow_nonneg hn0.le (3/5 : ℝ)]
  have hsr : ((Nat.sqrt r*r : ℕ) : ℝ) ≤ 4*(n : ℝ)^(9/10 : ℝ) := by
    have hh := mul_le_mul hsqrt hr2 (by positivity) (by positivity)
    have he : (2*(n : ℝ)^(3/10 : ℝ))*(2*(n : ℝ)^(3/5 : ℝ)) = 4*(n : ℝ)^(9/10 : ℝ) := by
      rw [show (9/10 : ℝ) = 3/10+3/5 by norm_num, Real.rpow_add hn0]; ring
    simpa only [Nat.cast_mul,he] using hh
  have hss := walk_sqrt_succ n hn
  have hcc : (cCOf kcs ncs n r r' 4 : ℝ) ≤ 600*K^2*L^2*(n : ℝ)^(9/10 : ℝ) := by
    have hi : (kcs.κ : ℝ)*(Nat.log 2 (r+1)+2 : ℕ)*((r'+(r/r')*Nat.sqrt r' : ℕ) : ℝ) ≤
        24*K*L*(n : ℝ)^(2/5 : ℝ) := by
      calc _ ≤ K*(2*L)*(12*(n : ℝ)^(2/5 : ℝ)) := by gcongr
           _ = _ := by ring
    have hpad : 4*((kcs.κ : ℝ)*(Nat.log 2 (r+1)+2 : ℕ)*((r'+(r/r')*Nat.sqrt r' : ℕ) : ℝ))+3 ≤
        100*K*L*(n : ℝ)^(2/5 : ℝ) := by
      have hKL : 1 ≤ K*L := by nlinarith
      have hp : 1 ≤ K*L*(n : ℝ)^(2/5 : ℝ) :=
          one_le_mul_of_one_le_of_one_le hKL (powone _ (by norm_num))
      linarith
    have hh : (ncs.κ : ℝ)*(Nat.log 2 (n+1)+2 : ℕ)*
      (4*((kcs.κ : ℝ)*(Nat.log 2 (r+1)+2 : ℕ)*((r'+(r/r')*Nat.sqrt r' : ℕ) : ℝ))+3)*
      ((Nat.sqrt (n+1)+1 : ℕ) : ℝ) ≤
        K*(2*L)*(100*K*L*(n : ℝ)^(2/5 : ℝ))*(3*(n : ℝ)^(1/2 : ℝ)) := by gcongr
    have he : K*(2*L)*(100*K*L*(n : ℝ)^(2/5 : ℝ))*(3*(n : ℝ)^(1/2 : ℝ)) =
        600*K^2*L^2*(n : ℝ)^(9/10 : ℝ) := by
      rw [show (9/10 : ℝ) = 2/5+1/2 by norm_num, Real.rpow_add hn0]; ring
    simpa only [cCOf,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,he] using hh
  have hKL : 1 ≤ K^2*L^2 := by nlinarith [sq_nonneg (K*L-1)]
  have hsum : (cCOf kcs ncs n r r' 4+Nat.sqrt r*r : ℕ) ≤
      (604 : ℝ)*K^2*L^2*(n : ℝ)^(9/10 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hKL (show 0 ≤ 4*(n : ℝ)^(9/10 : ℝ) by positivity)
    push_cast at hsr ⊢
    nlinarith only [hcc,hsr,hh]
  have hprod : ((n/r : ℕ) : ℝ)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r : ℕ) ≤
      604*K^2*L^2*(n : ℝ)^(13/10 : ℝ) := by
    have hh := mul_le_mul hdiv hsum (by positivity) (by positivity)
    have he : (n : ℝ)^(2/5 : ℝ)*(604*K^2*L^2*(n : ℝ)^(9/10 : ℝ)) =
        604*K^2*L^2*(n : ℝ)^(13/10 : ℝ) := by
      rw [show (13/10 : ℝ) = 2/5+9/10 by norm_num, Real.rpow_add hn0]; ring
    simpa only [he] using hh
  have hexp : (n : ℝ)^(6/5 : ℝ) ≤ (n : ℝ)^(13/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hsetup : ((r*r : ℕ) : ℝ) ≤ 4*K^2*L^2*(n : ℝ)^(13/10 : ℝ) := by
    rw [Nat.cast_mul,← pow_two]
    exact hrr.trans (by gcongr; nlinarith)
  have hout : ((kcs.κ*(Nat.log 2 (n+1)+2)*(r*r+(n/r)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r)) : ℕ) : ℝ) ≤
      1216*K^3*L^3*(n : ℝ)^(13/10 : ℝ) := by
    have hh : (kcs.κ : ℝ)*(Nat.log 2 (n+1)+2 : ℕ)*
        ((r*r : ℕ)+(n/r : ℕ)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r : ℕ) : ℕ) ≤
        K*(2*L)*(608*K^2*L^2*(n : ℝ)^(13/10 : ℝ)) := by
      have hadd : ((r*r : ℕ)+(n/r : ℕ)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r : ℕ) : ℕ) ≤
          (608 : ℝ)*K^2*L^2*(n : ℝ)^(13/10 : ℝ) := by
        push_cast at hsetup hprod ⊢
        linarith
      push_cast at hlog hadd ⊢
      gcongr
    push_cast at hh ⊢
    nlinarith only [hh]
  have hgrover : ((sgs.κ*(Nat.log 2 (n+1)+2)*4*(Nat.sqrt (n+1)+1) : ℕ) : ℝ) ≤
      24*K^3*L^3*(n : ℝ)^(13/10 : ℝ) := by
    have hp : (n : ℝ)^(1/2 : ℝ) ≤ (n : ℝ)^(13/10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    calc _ ≤ K*(2*L)*4*(3*(n : ℝ)^(1/2 : ℝ)) := by push_cast at hlog hss ⊢; gcongr
         _ ≤ 24*K^3*L^3*(n : ℝ)^(13/10 : ℝ) := by
           have hK3 : K ≤ K^3 := by nlinarith [sq_nonneg (K-1)]
           have hL3 : L ≤ L^3 := by nlinarith [sq_nonneg (L-1)]
           calc _ = 24*K*L*(n : ℝ)^(1/2 : ℝ) := by ring
                _ ≤ _ := by gcongr
  have hunit : 1 ≤ K^3*L^3*(n : ℝ)^(13/10 : ℝ) := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le <;> exact one_le_pow₀ (by linarith)
    · exact powone _ (by norm_num)
  have hfinal : ((kcs.κ*(Nat.log 2 (n+1)+2)*(r*r+(n/r)*(cCOf kcs ncs n r r' 4+Nat.sqrt r*r)) +
      sgs.κ*(Nat.log 2 (n+1)+2)*4*(Nat.sqrt (n+1)+1)+3 : ℕ) : ℝ) ≤
      65536*K^3*L^3*(n : ℝ)^(13/10 : ℝ) := by
    push_cast at hout hgrover ⊢
    nlinarith only [hout,hgrover,hunit]
  simpa only [K,L,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,show (2 : ℝ)^16 = 65536 by norm_num] using hfinal

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
