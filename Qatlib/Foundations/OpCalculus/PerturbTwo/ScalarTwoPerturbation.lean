/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional


/-! The finite-dimensional perturbation lemma from Lorist--Schwenninger,
https://arxiv.org/html/2608.03841v2. The recurrence is proved by taking its
bounded sequence's infimum, avoiding an infinite telescoping sum. Norm
attainment and the complex-to-real adjoint bridge are derived here. Actual
polynomial double-layer-potential data are a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.PerturbTwo

/-- A bounded-below sequence cannot follow an expanding negative affine orbit. -/
theorem recurrence_lower_bound (κ C : ℝ) (m : ℕ → ℝ) (hκ : 1<κ)
    (hb : BddBelow (Set.range m)) (hstep : ∀ n,-C≤κ*m n-m (n+1)) :
    -C/(κ-1)≤m 0 := by
  let a := sInf (Set.range m)
  have ha (n : ℕ) : a≤m n := csInf_le hb (Set.mem_range_self n)
  have hκ0 : 0<κ := by linarith
  have hinf : (a-C)/κ≤a := by
    apply le_csInf (Set.range_nonempty m)
    rintro _ ⟨n,rfl⟩
    apply (div_le_iff₀ hκ0).mpr
    linarith [ha (n+1),hstep n]
  have hrec := (div_le_iff₀ hκ0).mp hinf
  have hleft : -C/(κ-1)≤a := by
    apply (div_le_iff₀ (by linarith : 0<κ-1)).mpr
    nlinarith
  exact hleft.trans (ha 0)

/-- The two scalar estimates in the perturbation argument force kappa<=2. -/
theorem sharp_two_of_scalar_receipts (κ U m : ℝ) (hκ : 1<κ) (hU : 0≤U)
    (hlower : -U/(κ-1)^2≤κ*m)
    (hupper : U≤2*κ^2-κ*m-κ^3) : κ≤2 := by
  by_contra h
  have hk2 : 2<κ := lt_of_not_ge h
  have hden : 1≤(κ-1)^2 := by nlinarith
  have hdiv : U/(κ-1)^2≤U := (div_le_iff₀ (by positivity : 0<(κ-1)^2)).mpr (by nlinarith)
  have hkpos : 0<κ^2 := sq_pos_of_pos (by linarith)
  have hneg : κ^2*(2-κ)<0 := mul_neg_of_pos_of_neg hkpos (by linarith)
  have hmlow : -U≤κ*m := by
    calc
      -U ≤ -(U/(κ-1)^2) := neg_le_neg hdiv
      _ ≤ κ*m := by simpa only [neg_div] using hlower
  nlinarith

end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
open ContinuousLinearMap
open scoped InnerProduct
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Actual rectangular contraction powers, not an arbitrary moment sequence. -/
private theorem contraction_adjoint_pow (Q : K →L[ℝ] K) (hQ : ‖Q‖≤1) (n : ℕ) : ‖Q†^n‖≤1 := by
  induction n with
  | zero =>
    change ‖ContinuousLinearMap.id ℝ K‖ ≤ 1
    exact norm_id_le
  | succ n ih =>
    rw [pow_succ]
    calc
      _ ≤ ‖Q†^n‖*‖Q†‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul ih (by simpa only [adjoint.norm_map] using hQ) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- The identity or estimate `adjoint_pow` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem adjoint_pow (T : H →L[ℝ] H) (n : ℕ) : (T^n)†=T†^n := by
  change star (T^n)=star T^n
  exact star_pow _ _

/-- Maximum-norm vectors satisfy the top singular-vector equation. -/
theorem norm_attaining_equation (T : H →L[ℝ] H) (x : H)
    (hx : ‖x‖=1) (hTx : ‖T x‖=‖T‖) : (T†) (T x)=‖T‖^2 • x := by
  have hb : ‖(T†) (T x)‖≤‖T‖^2 := by
    calc
      _ ≤ ‖T†‖*‖T x‖ := le_opNorm _ _
      _ = _ := by rw [adjoint.norm_map,hTx]; ring
  have hi : inner ℝ ((T†) (T x)) x=‖T‖^2 := by
    rw [adjoint_inner_left,real_inner_self_eq_norm_sq,hTx]
  have hs : ‖(T†) (T x)-‖T‖^2 • x‖^2=0 := by
    have hbsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hs0 := sq_nonneg ‖(T†) (T x)-‖T‖^2 • x‖
    rw [norm_sub_sq_real,real_inner_smul_right,hi,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _),hx] at hs0 ⊢
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

/-- Construction for perturbation in the scalar two perturbation model. -/
def perturbation (T : H →L[ℝ] H) (Q : K →L[ℝ] K) (V : H →L[ℝ] K) (n : ℕ) : H →L[ℝ] H :=
  (2 : ℝ) • (V† ∘L (Q†^n) ∘L V)-T†^n

/-- Construction for discrepancy in the scalar two perturbation model. -/
def discrepancy (T : H →L[ℝ] H) (Q : K →L[ℝ] K) (V : H →L[ℝ] K) (x : H) : K :=
  (Q†) (V (T x))-‖T‖ • V x

/-- The identity or estimate `perturbation_step_vector` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem perturbation_step_vector (T : H →L[ℝ] H) (Q : K →L[ℝ] K)
    (V : H →L[ℝ] K) (x : H) (heig : (T†) (T x)=‖T‖^2 • x) (n : ℕ) :
    ‖T‖ • perturbation T Q V n x-perturbation T Q V (n+1) (T x)=
      (‖T‖*(‖T‖-1)) • (T†^n) x-(2 : ℝ) • (V†) ((Q†^n) (discrepancy T Q V x)) := by
  simp only [perturbation,discrepancy,sub_apply,smul_apply,comp_apply,pow_succ,
    ContinuousLinearMap.mul_apply,heig,map_sub,map_smul]
  module

/-- The identity or estimate `inner_power` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem inner_power (T : H →L[ℝ] H) (n : ℕ) (x y : H) :
    inner ℝ x ((T^n) y)=inner ℝ ((T†^n) x) y := by
  rw [← adjoint_inner_left,adjoint_pow]

/-- Commutation is used here; uniform boundedness alone does not suffice. -/
theorem perturbation_scalar_step (T : H →L[ℝ] H) (Q : K →L[ℝ] K)
    (V : H →L[ℝ] K) (x : H) (heig : (T†) (T x)=‖T‖^2 • x)
    (hcomm : ∀ n,Commute (perturbation T Q V n) T) (n : ℕ) :
    ‖T‖*inner ℝ x (perturbation T Q V n ((T^n) x))-
      inner ℝ x (perturbation T Q V (n+1) ((T^(n+1)) x))=
      (‖T‖*(‖T‖-1))*‖(T†^n) x‖^2-
        2*inner ℝ ((T†^n) x) ((V†) ((Q†^n) (discrepancy T Q V x))) := by
  have hc (j : ℕ) : ∀ y,perturbation T Q V j ((T^n) y)=(T^n) (perturbation T Q V j y) := by
    intro y
    exact congrArg (fun A : H →L[ℝ] H => A y) ((hcomm j).pow_right n).eq
  rw [pow_succ,ContinuousLinearMap.mul_apply,hc n,hc (n+1),← real_inner_smul_right,← inner_sub_right,← map_smul,← map_sub,
    perturbation_step_vector T Q V x heig n,inner_power]
  rw [inner_sub_right,real_inner_smul_right]
  simp only [two_smul,inner_add_right,real_inner_self_eq_norm_sq]
  ring

end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
open ContinuousLinearMap
open scoped InnerProduct
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The identity or estimate `isometry_norm_le` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem isometry_norm_le (V : H →L[ℝ] K) (hV : ∀ y,‖V y‖=‖y‖) : ‖V‖≤1 := by
  apply opNorm_le_bound _ (by norm_num)
  intro y
  simp only [hV,one_mul,le_refl]

/-- The identity or estimate `moment_contraction` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem moment_contraction (Q : K →L[ℝ] K) (V : H →L[ℝ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖) (n : ℕ) : ‖V† ∘L (Q†^n) ∘L V‖≤1 := by
  have hv := isometry_norm_le V hV
  have hv' : ‖V†‖≤1 := by simpa only [adjoint.norm_map] using hv
  calc
    _ ≤ ‖V†‖*(‖Q†^n‖*‖V‖) := (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(1*1) := by gcongr; exact contraction_adjoint_pow Q hQ n
    _ = 1 := by norm_num

/-- The identity or estimate `powers_bounded` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem powers_bounded (T : H →L[ℝ] H) (Q : K →L[ℝ] K) (V : H →L[ℝ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖) (C : ℝ)
    (hE : ∀ n,‖perturbation T Q V n‖≤C) (n : ℕ) : ‖T^n‖≤2+C := by
  have heq : T†^n=(2 : ℝ) • (V† ∘L (Q†^n) ∘L V)-perturbation T Q V n := by
    unfold perturbation
    module
  rw [← adjoint.norm_map (T^n),adjoint_pow,heq]
  calc
    _ ≤ ‖(2 : ℝ) • (V† ∘L (Q†^n) ∘L V)‖+‖perturbation T Q V n‖ := norm_sub_le _ _
    _ ≤ 2*1+C := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      have hB := moment_contraction Q V hQ hV n
      linarith [hE n]
    _ = _ := by ring

/-- The identity or estimate `discrepancy_step_lower` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem discrepancy_step_lower (T : H →L[ℝ] H) (Q : K →L[ℝ] K)
    (V : H →L[ℝ] K) (x : H) (heig : (T†) (T x)=‖T‖^2 • x)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖) (hκ : 1<‖T‖)
    (hcomm : ∀ n,Commute (perturbation T Q V n) T) (n : ℕ) :
    -‖discrepancy T Q V x‖^2/(‖T‖*(‖T‖-1))≤
      ‖T‖*inner ℝ x (perturbation T Q V n ((T^n) x))-
        inner ℝ x (perturbation T Q V (n+1) ((T^(n+1)) x)) := by
  rw [perturbation_scalar_step T Q V x heig hcomm n]
  let z := (T†^n) x
  let u := discrepancy T Q V x
  let w := (V†) ((Q†^n) u)
  have ha : 0<‖T‖*(‖T‖-1) := mul_pos (by linarith) (by linarith)
  have hw : ‖w‖≤‖u‖ := by
    have hv : ‖V†‖≤1 := by simpa only [adjoint.norm_map] using isometry_norm_le V hV
    calc
      _ ≤ ‖V†‖*‖(Q†^n) u‖ := le_opNorm _ _
      _ ≤ ‖V†‖*(‖Q†^n‖*‖u‖) := mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
      _ ≤ 1*(1*‖u‖) := by gcongr; exact contraction_adjoint_pow Q hQ n
      _ = _ := by ring
  have hi : inner ℝ z w≤‖z‖*‖u‖ := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  change -‖u‖^2/(‖T‖*(‖T‖-1))≤(‖T‖*(‖T‖-1))*‖z‖^2-2*inner ℝ z w
  apply (div_le_iff₀ ha).mpr
  nlinarith [sq_nonneg ((‖T‖*(‖T‖-1))*‖z‖-‖u‖)]

end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
open ContinuousLinearMap
open scoped InnerProduct
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The identity or estimate `discrepancy_upper` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem discrepancy_upper (T : H →L[ℝ] H) (Q : K →L[ℝ] K)
    (V : H →L[ℝ] K) (x : H) (hx : ‖x‖=1) (hTx : ‖T x‖=‖T‖)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖) :
    ‖discrepancy T Q V x‖^2≤2*‖T‖^2-
      ‖T‖*inner ℝ x (perturbation T Q V 1 (T x))-‖T‖^3 := by
  let v := (Q†) (V (T x))
  have heig := norm_attaining_equation T x hx hTx
  have hv : ‖v‖≤‖T‖ := by
    calc
      _ ≤ ‖Q†‖*‖V (T x)‖ := le_opNorm _ _
      _ ≤ 1*‖V (T x)‖ := mul_le_mul_of_nonneg_right (by simpa only [adjoint.norm_map] using hQ) (norm_nonneg _)
      _ = _ := by rw [hV,hTx,one_mul]
  have he : perturbation T Q V 1 (T x)=(2 : ℝ) • (V†) v-‖T‖^2 • x := by
    simp only [perturbation,pow_one,sub_apply,smul_apply,comp_apply,heig]
    rfl
  have hm : inner ℝ x (perturbation T Q V 1 (T x))=2*inner ℝ (V x) v-‖T‖^2 := by
    rw [he,inner_sub_right]
    simp only [two_smul,inner_add_right,adjoint_inner_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hx]
    ring
  have hs : ‖discrepancy T Q V x‖^2=‖v‖^2-2*(‖T‖*inner ℝ (V x) v)+‖T‖^2 := by
    rw [discrepancy,norm_sub_sq_real,real_inner_smul_right,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hV,hx,real_inner_comm]
    dsimp [v]
    ring
  have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hm' := congrArg (fun a : ℝ => ‖T‖*a) hm
  nlinarith

/-- The actual perturbation lemma for a norm-attaining real Hilbert operator.
The finite-dimensional norm-attainment step and complex restriction are separate. -/
theorem perturbation_norm_le_two_of_attainment
    (T : H →L[ℝ] H) (Q : K →L[ℝ] K) (V : H →L[ℝ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖)
    (C : ℝ) (hE : ∀ n,‖perturbation T Q V n‖≤C)
    (hcomm : ∀ n,Commute (perturbation T Q V n) T)
    (x : H) (hx : ‖x‖=1) (hTx : ‖T x‖=‖T‖) : ‖T‖≤2 := by
  by_cases hκ : ‖T‖≤1
  · linarith
  have hκ1 : 1<‖T‖ := lt_of_not_ge hκ
  have heig := norm_attaining_equation T x hx hTx
  let m : ℕ → ℝ := fun n => inner ℝ x (perturbation T Q V (n+1) ((T^(n+1)) x))
  have hC : 0≤C := (norm_nonneg _).trans (hE 0)
  have hb : BddBelow (Set.range m) := by
    refine ⟨-(C*(2+C)),?_⟩
    rintro _ ⟨n,rfl⟩
    have hh : |m n|≤C*(2+C) := by
      calc
        _ ≤ ‖x‖*‖perturbation T Q V (n+1) ((T^(n+1)) x)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x‖*(‖perturbation T Q V (n+1)‖*(‖T^(n+1)‖*‖x‖)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
          exact (le_opNorm (perturbation T Q V (n+1)) ((T^(n+1)) x)).trans
            (mul_le_mul_of_nonneg_left (le_opNorm (T^(n+1)) x) (norm_nonneg _))
        _ ≤ 1*(C*((2+C)*1)) := by
          rw [hx]
          gcongr
          exact hE (n+1)
          exact powers_bounded T Q V hQ hV C hE (n+1)
        _ = _ := by ring
    exact (abs_le.mp hh).1
  have hstep : ∀ n,-(‖discrepancy T Q V x‖^2/(‖T‖*(‖T‖-1)))≤‖T‖*m n-m (n+1) := by
    intro n
    simpa only [m,neg_div,Nat.add_assoc] using discrepancy_step_lower T Q V x heig hQ hV hκ1 hcomm (n+1)
  have hl := recurrence_lower_bound ‖T‖ (‖discrepancy T Q V x‖^2/(‖T‖*(‖T‖-1))) m hκ1 hb hstep
  have hlower : -‖discrepancy T Q V x‖^2/(‖T‖-1)^2≤‖T‖*m 0 := by
    have hk0 : 0<‖T‖ := by linarith
    have heq : -‖discrepancy T Q V x‖^2/(‖T‖-1)^2=
        ‖T‖*(-(‖discrepancy T Q V x‖^2/(‖T‖*(‖T‖-1)))/(‖T‖-1)) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hl hk0.le
  apply sharp_two_of_scalar_receipts ‖T‖ (‖discrepancy T Q V x‖^2) (m 0) hκ1 (sq_nonneg _) hlower
  simpa only [m,Nat.zero_add,pow_one] using discrepancy_upper T Q V x hx hTx hQ hV

end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
open ContinuousLinearMap
open scoped InnerProduct
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Finite-dimensional attainment is derived from the actual compact sphere. -/
theorem exists_norm_attainment [FiniteDimensional ℝ H] [Nontrivial H] (T : H →L[ℝ] H) :
    ∃ x : H,‖x‖=1 ∧ ‖T x‖=‖T‖ := by
  obtain ⟨x,hx,hmax⟩ := (isCompact_sphere (0 : H) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num)) T.continuous.norm.continuousOn
  have hx' : ‖x‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  refine ⟨x,hx',le_antisymm ?_ ?_⟩
  · simpa only [hx',mul_one] using le_opNorm T x
  · apply opNorm_le_of_unit_norm (norm_nonneg _)
    intro y hy
    exact hmax (by simpa only [Metric.mem_sphere,dist_zero_right] using hy)

/-- The perturbation lemma in finite dimension; no two-norm hypothesis. -/
theorem perturbation_norm_le_two [FiniteDimensional ℝ H]
    (T : H →L[ℝ] H) (Q : K →L[ℝ] K) (V : H →L[ℝ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖)
    (C : ℝ) (hE : ∀ n,‖perturbation T Q V n‖≤C)
    (hcomm : ∀ n,Commute (perturbation T Q V n) T) : ‖T‖≤2 := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    have ht : T=0 := Subsingleton.elim _ _
    simp only [ht,norm_zero]; norm_num
  | inr h =>
    obtain ⟨x,hx,hTx⟩ := exists_norm_attainment T
    exact perturbation_norm_le_two_of_attainment T Q V hQ hV C hE hcomm x hx hTx

end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
section Complex
open ContinuousLinearMap
open scoped InnerProduct
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
/-- Typeclass instance for real H in the scalar two perturbation model. -/
local instance realH : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
/-- Typeclass instance for real K in the scalar two perturbation model. -/
local instance realK : InnerProductSpace ℝ K := InnerProductSpace.complexToReal

/-- The complex defects are the actual adjoint-power expressions. -/
def complexPerturbation (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K) (n : ℕ) : H →L[ℂ] H :=
  (2 : ℝ) • (V† ∘L (Q†^n) ∘L V)-T†^n

/-- The identity or estimate `adjoint_restrict_real` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem adjoint_restrict_real (A : H →L[ℂ] K) :
    (A.restrictScalars ℝ)†=(A†).restrictScalars ℝ := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  change (inner ℂ ((A†) x) y).re=(inner ℂ x (A y)).re
  rw [adjoint_inner_left]

omit [CompleteSpace H] in
/-- The identity or estimate `pow_restrict_real` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem pow_restrict_real (T : H →L[ℂ] H) (n : ℕ) :
    (T.restrictScalars ℝ)^n=(T^n).restrictScalars ℝ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [pow_succ,ContinuousLinearMap.mul_apply,coe_restrictScalars']
    exact congrArg (fun A : H →L[ℝ] H => A (T x)) ih

/-- The identity or estimate `perturbation_restrict_real` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem perturbation_restrict_real (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K) (n : ℕ) :
    perturbation (T.restrictScalars ℝ) (Q.restrictScalars ℝ) (V.restrictScalars ℝ) n=
      (complexPerturbation T Q V n).restrictScalars ℝ := by
  unfold perturbation
  rw [adjoint_restrict_real,adjoint_restrict_real,adjoint_restrict_real,pow_restrict_real,pow_restrict_real]
  ext x
  rfl

/-- Finite complex input, possibly infinite dilation space: sharp two follows
from actual bounded commuting defects, with no sharp-norm premise. -/
theorem complex_perturbation_norm_le_two [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖)
    (C : ℝ) (hE : ∀ n,‖complexPerturbation T Q V n‖≤C)
    (hcomm : ∀ n,Commute (complexPerturbation T Q V n) T) : ‖T‖≤2 := by
  have hq : ‖Q.restrictScalars ℝ‖≤1 := by simpa only [norm_restrictScalars] using hQ
  have hv : ∀ y,‖(V.restrictScalars ℝ) y‖=‖y‖ := hV
  have he : ∀ n,‖perturbation (T.restrictScalars ℝ) (Q.restrictScalars ℝ) (V.restrictScalars ℝ) n‖≤C := by
    intro n
    rw [perturbation_restrict_real,norm_restrictScalars]
    exact hE n
  have hc : ∀ n,Commute (perturbation (T.restrictScalars ℝ) (Q.restrictScalars ℝ) (V.restrictScalars ℝ) n)
      (T.restrictScalars ℝ) := by
    intro n
    change _ * _ = _ * _
    rw [perturbation_restrict_real]
    ext x
    exact congrArg (fun A : H →L[ℂ] H => A x) (hcomm n).eq
  have hh := perturbation_norm_le_two (T.restrictScalars ℝ) (Q.restrictScalars ℝ)
    (V.restrictScalars ℝ) hq hv C he hc
  simpa only [norm_restrictScalars] using hh

end Complex
end Qatlib.Foundations.OpCalculus.PerturbTwo

namespace Qatlib.Foundations.OpCalculus.PerturbTwo
open ContinuousLinearMap Matrix
open scoped InnerProduct Matrix.Norms.L2Operator
variable {I K : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual Matrix L2 norm, with the normalized matrix's actual dilation data.
This is not yet the production of those data from W(A) and a polynomial. -/
theorem matrix_norm_le_two_mul_of_dilation
    (T : Matrix I I ℂ) (M : ℝ) (hM : 0<M)
    (Q : K →L[ℂ] K) (V : EuclideanSpace ℂ I →L[ℂ] K)
    (hQ : ‖Q‖≤1) (hV : ∀ y,‖V y‖=‖y‖) (C : ℝ)
    (hE : ∀ n,‖complexPerturbation (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (M⁻¹ • T)) Q V n‖≤C)
    (hcomm : ∀ n,Commute (complexPerturbation (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (M⁻¹ • T)) Q V n)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (M⁻¹ • T))) : ‖T‖≤2*M := by
  have hh := complex_perturbation_norm_le_two (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (M⁻¹ • T)) Q V hQ hV C hE hcomm
  change ‖M⁻¹ • T‖≤2 at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hM)] at hh
  calc
    _ = M*(M⁻¹*‖T‖) := by field_simp
    _ ≤ M*2 := mul_le_mul_of_nonneg_left hh hM.le
    _ = _ := by ring

end Qatlib.Foundations.OpCalculus.PerturbTwo
