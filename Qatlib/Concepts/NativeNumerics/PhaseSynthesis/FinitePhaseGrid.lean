/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.PhaseGeometry.Phase Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def coeffMass (p : Polynomial ℂ) : ℝ := ∑ i ∈ p.support, ‖p.coeff i‖

theorem coeffMass_nonneg (p : Polynomial ℂ) : 0 ≤ coeffMass p :=
    Finset.sum_nonneg (fun _i _ => norm_nonneg _)

theorem coeffMass_expand (p : Polynomial ℂ) (s : Finset ℕ) (hs : p.support ⊆ s) :
    coeffMass p = ∑ i ∈ s, ‖p.coeff i‖ := by
  apply Finset.sum_subset hs
  intro i hi hn
  have he : p.coeff i = 0 := by simpa only [Polynomial.mem_support_iff,not_not] using hn
  simp [he]

theorem coeffMass_range (p : Polynomial ℂ) (n : ℕ) (hn : p.natDegree < n) :
    coeffMass p = ∑ i ∈ Finset.range n, ‖p.coeff i‖ := coeffMass_expand p _ (Polynomial.supp_subset_range hn)

@[simp] theorem coeffMass_zero : coeffMass (0:Polynomial ℂ) = 0 := by simp [coeffMass]

@[simp] theorem coeffMass_C (z : ℂ) : coeffMass (C z) = ‖z‖ := by
  rw [coeffMass_range (C z) 1 (by simp)]
  simp

@[simp] theorem coeffMass_neg (p : Polynomial ℂ) : coeffMass (-p) = coeffMass p := by
  simp [coeffMass]

theorem coeffMass_add_le (p q : Polynomial ℂ) : coeffMass (p+q) ≤ coeffMass p+coeffMass q := by
  rw [coeffMass_expand (p+q) (p.support ∪ q.support) Polynomial.support_add,
    coeffMass_expand p (p.support ∪ q.support) Finset.subset_union_left,
    coeffMass_expand q (p.support ∪ q.support) Finset.subset_union_right,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by rw [Polynomial.coeff_add]; exact norm_add_le _ _)

theorem coeffMass_sub_le (p q : Polynomial ℂ) : coeffMass (p-q) ≤ coeffMass p+coeffMass q := by
  simpa only [sub_eq_add_neg,coeffMass_neg] using coeffMass_add_le p (-q)

theorem coeffMass_C_mul (z : ℂ) (p : Polynomial ℂ) : coeffMass (C z*p) = ‖z‖*coeffMass p := by
  have hs : (C z*p).support ⊆ p.support := by
    intro i hi
    apply Polynomial.mem_support_iff.mpr
    intro he
    have hz : (C z*p).coeff i = 0 := by rw [Polynomial.coeff_C_mul,he,mul_zero]
    exact (Polynomial.mem_support_iff.mp hi) hz
  rw [coeffMass_expand (C z*p) p.support hs]
  simp only [Polynomial.coeff_C_mul,norm_mul,coeffMass,Finset.mul_sum]

theorem coeffMass_X_mul (p : Polynomial ℂ) : coeffMass (X*p) = coeffMass p := by
  have hd : (X*p).natDegree < p.natDegree+2 := by
    have h := Polynomial.natDegree_mul_le (p:= (X:Polynomial ℂ)) (q:=p)
    simp only [Polynomial.natDegree_X] at h
    omega
  rw [coeffMass_range (X*p) (p.natDegree+2) hd,Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul,Polynomial.coeff_X_mul_zero,norm_zero,add_zero]
  exact (coeffMass_range p (p.natDegree+1) (by omega)).symm

theorem coeffMass_response_step (P Q : Polynomial ℂ) :
    coeffMass (X*P+(1-X^2)*Q)+coeffMass (P-X*Q) ≤ 3*(coeffMass P+coeffMass Q) := by
  have he : (1-X^2)*Q = Q-X*(X*Q) := by ring
  rw [he]
  have hp := (coeffMass_add_le (X*P) (Q-X*(X*Q))).trans
    (add_le_add le_rfl (coeffMass_sub_le Q (X*(X*Q))))
  have hq := coeffMass_sub_le P (X*Q)
  simp only [coeffMass_X_mul] at hp hq
  have hn := coeffMass_nonneg P
  linarith

theorem coeffMass_response_phase_step (z : ℂ) (P Q : Polynomial ℂ) (hz : ‖z‖ = 1) :
    coeffMass (C z*(X*P+(1-X^2)*Q))+coeffMass (C (star z)*(P-X*Q)) ≤ 3*(coeffMass P+coeffMass Q) := by
  simpa only [coeffMass_C_mul,norm_star,hz,one_mul] using coeffMass_response_step P Q

theorem phase_norm_one (z : ℂ) (hz : IsPhase z) : ‖z‖ = 1 := by
  have hs := Qatlib.Concepts.TrotterFormula.SuzukiFourth.IsPhase.normSq hz
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg z]

theorem response_packet_mass (base : ℂ) (zs : List ℂ) (hb : IsPhase base) (hz : ∀ z ∈ zs,IsPhase z) :
    coeffMass (responseP base zs)+coeffMass (responseQ base zs) ≤ (3:ℝ)^zs.length := by
  induction zs with
  | nil => simp [phase_norm_one base hb]
  | cons z zs ih =>
    have ht : ∀ w ∈ zs,IsPhase w := fun w hw => hz w (List.mem_cons_of_mem z hw)
    have hhead := phase_norm_one z (hz z List.mem_cons_self)
    rw [responseP_cons,responseQ_cons]
    exact (coeffMass_response_phase_step z _ _ hhead).trans
      ((mul_le_mul_of_nonneg_left (ih ht) (by norm_num)).trans_eq (by simp [pow_succ]; ring))

theorem response_step_coeff_defect (z w : ℂ) (P Q R S : Polynomial ℂ) (hz : ‖z‖ = 1) :
    coeffMass (C z*(X*P+(1-X^2)*Q)-C w*(X*R+(1-X^2)*S))+
    coeffMass (C (star z)*(P-X*Q)-C (star w)*(R-X*S)) ≤
      3*(coeffMass (P-R)+coeffMass (Q-S))+3*‖z-w‖*(coeffMass R+coeffMass S) := by
  have heP : C z*(X*P+(1-X^2)*Q)-C w*(X*R+(1-X^2)*S) =
      C z*(X*(P-R)+(1-X^2)*(Q-S))+C (z-w)*(X*R+(1-X^2)*S) := by rw [Polynomial.C_sub]; ring
  have heQ : C (star z)*(P-X*Q)-C (star w)*(R-X*S) =
      C (star z)*((P-R)-X*(Q-S))+C (star (z-w))*(R-X*S) := by rw [star_sub,Polynomial.C_sub]; ring
  rw [heP,heQ]
  have hp := coeffMass_add_le (C z*(X*(P-R)+(1-X^2)*(Q-S))) (C (z-w)*(X*R+(1-X^2)*S))
  have hq := coeffMass_add_le (C (star z)*((P-R)-X*(Q-S))) (C (star (z-w))*(R-X*S))
  have hd := coeffMass_response_phase_step z (P-R) (Q-S) hz
  have hr := mul_le_mul_of_nonneg_left (coeffMass_response_step R S) (norm_nonneg (z-w))
  simp only [coeffMass_C_mul,norm_star,hz,one_mul] at hp hq
  simp only [coeffMass_C_mul,norm_star,hz,one_mul] at hd
  nlinarith

theorem response_packet_coeff_defect (base other : ℂ) (zs ws : List ℂ) (delta : ℝ)
    (hlen : zs.length = ws.length) (_hb : IsPhase base) (ho : IsPhase other)
    (hz : ∀ z ∈ zs,IsPhase z) (hw : ∀ w ∈ ws,IsPhase w) (hd : 0 ≤ delta)
    (hbase : ‖base-other‖ ≤ delta) (hs : ∀ i < zs.length,‖zs.getD i 1-ws.getD i 1‖ ≤ delta) :
    coeffMass (responseP base zs-responseP other ws)+coeffMass (responseQ base zs-responseQ other ws) ≤
      ((zs.length+1:ℕ):ℝ)*(3:ℝ)^zs.length*delta := by
  induction zs generalizing ws with
  | nil =>
    have hw0 : ws = [] := by cases ws <;> simp_all
    subst ws
    simpa only [responseP_nil,responseQ_nil,← Polynomial.C_sub,sub_self,coeffMass_zero,
      coeffMass_C,add_zero,List.length_nil,Nat.cast_add,Nat.cast_zero,Nat.cast_one,pow_zero,zero_add,mul_one,one_mul] using hbase
  | cons z zs ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      have hlen' : zs.length = ws.length := by simpa using hlen
      have hz' : ∀ a ∈ zs,IsPhase a := fun a ha => hz a (List.mem_cons_of_mem z ha)
      have hw' : ∀ a ∈ ws,IsPhase a := fun a ha => hw a (List.mem_cons_of_mem w ha)
      have hzw : ‖z-w‖ ≤ delta := by simpa using hs 0 (by simp)
      have htail : ∀ i < zs.length,‖zs.getD i 1-ws.getD i 1‖ ≤ delta := by
        intro i hi
        simpa using hs (i+1) (by simp; omega)
      have hi := ih ws hlen' hz' hw' htail
      have hm := response_packet_mass other ws ho hw'
      rw [responseP_cons,responseP_cons,responseQ_cons,responseQ_cons]
      have hh := response_step_coeff_defect z w (responseP base zs) (responseQ base zs)
        (responseP other ws) (responseQ other ws) (phase_norm_one z (hz z List.mem_cons_self))
      rw [← hlen'] at hm
      have hfirst := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 3)
      have hsecond : 3*‖z-w‖*(coeffMass (responseP other ws)+coeffMass (responseQ other ws)) ≤
          3*delta*(3:ℝ)^zs.length := by
        have hn :=
            add_nonneg (coeffMass_nonneg (responseP other ws))
            (coeffMass_nonneg (responseQ other ws))
        gcongr
      exact (hh.trans (add_le_add hfirst hsecond)).trans_eq
          (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one,pow_succ]; ring)

def phaseConstant (d : ℕ) : ℕ := (d+1)*3^d

theorem response_coefficients_derived_lipschitz : ∀ (d : ℕ) (base other : ℂ) (zs ws : List ℂ) (delta : ℝ),
  zs.length=d → ws.length=d → IsPhase base → IsPhase other →
  (∀ z ∈ zs,IsPhase z) → (∀ w ∈ ws,IsPhase w) → 0 ≤ delta →
  ‖base-other‖ ≤ delta → (∀ i < d, ‖zs.getD i 1-ws.getD i 1‖ ≤ delta) →
  (∑ i ∈ Finset.range (d+1), ‖(responseP base zs).coeff i-(responseP other ws).coeff i‖) ≤
    (phaseConstant d:ℝ)*delta := by
  intro d base other zs ws delta hzs hws hb ho hz hw hd hbase hs
  have hj :=
      response_packet_coeff_defect base other zs ws delta (hzs.trans hws.symm) hb ho hz hw hd hbase
      (by simpa only [hzs] using hs)
  have hp : (responseP base zs-responseP other ws).natDegree < d+1 := by
    have h1 := (response_degree base zs).1
    have h2 := (response_degree other ws).1
    rw [hzs] at h1
    rw [hws] at h2
    have h := Polynomial.natDegree_sub_le (responseP base zs) (responseP other ws)
    omega
  rw [coeffMass_range _ (d+1) hp] at hj
  simp only [Polynomial.coeff_sub] at hj
  have hq := coeffMass_nonneg (responseQ base zs-responseQ other ws)
  have he : ((zs.length+1:ℕ):ℝ)*(3:ℝ)^zs.length*delta = (phaseConstant d:ℝ)*delta := by
    rw [hzs]
    simp [phaseConstant,Nat.cast_mul,Nat.cast_pow]
  rw [he] at hj
  linarith

def phaseTableLoop (z : GaussianRat) : ℕ → GaussianRat → List GaussianRat × ℕ
  | 0,_ => ([],0)
  | 1,a => ([a],0)
  | n+2,a => let r := phaseTableLoop z (n+1) (gmul a z); (a::r.1,r.2+1)
def phaseTable (z : GaussianRat) (N : ℕ) := phaseTableLoop z N gone

theorem phaseTableLoop_spec (z : GaussianRat) (N : ℕ) (a : GaussianRat) :
    (phaseTableLoop z N a).1.length = N ∧ (phaseTableLoop z N a).2 = N-1 ∧
    ∀ j < N,gaussianRatComplex ((phaseTableLoop z N a).1.getD j gone) =
      gaussianRatComplex a*(gaussianRatComplex z)^j := by
  induction N using Nat.strong_induction_on generalizing a with
  | h N ih =>
    cases N with
    | zero => simp [phaseTableLoop]
    | succ N =>
      cases N with
      | zero =>
        refine ⟨rfl,rfl,?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        simp [phaseTableLoop,hj0]
      | succ N =>
        have ht := ih (N+1) (by omega) (gmul a z)
        simp only [phaseTableLoop,List.length_cons,ht.1,ht.2.1]
        refine ⟨True.intro,by omega,?_⟩
        intro j hj
        cases j with
        | zero => simp [pow_zero]
        | succ j =>
          rw [List.getD_cons_succ,ht.2.2 j (by omega),complex_gmul,pow_succ]
          ring

theorem phaseTable_spec (z : GaussianRat) (N : ℕ) :
    (phaseTable z N).1.length = N ∧ (phaseTable z N).2 = N-1 ∧
    ∀ j < N,gaussianRatComplex ((phaseTable z N).1.getD j gone) = (gaussianRatComplex z)^j := by
  simpa only [phaseTable,complex_gone,one_mul] using phaseTableLoop_spec z N gone

theorem phase_power_error (z w : ℂ) (eta : ℝ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (he : ‖z-w‖ ≤ eta) (j : ℕ) : ‖z^j-w^j‖ ≤ (j:ℝ)*eta := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd : z^(j+1)-w^(j+1) = z^j*(z-w)+(z^j-w^j)*w := by rw [pow_succ,pow_succ]; ring
    rw [hd]
    calc
      _ ≤ ‖z^j*(z-w)‖+‖(z^j-w^j)*w‖ := norm_add_le _ _
      _ = ‖z-w‖+‖z^j-w^j‖ := by simp [norm_pow,hz,hw]
      _ ≤ eta+(j:ℝ)*eta := add_le_add he ih
      _ = _ := by push_cast; ring

theorem phase_angle_representative (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 2*Real.pi ∧ Complex.exp ((t:ℂ)*Complex.I) = v := by
  have he : Complex.exp ((Complex.arg v:ℂ)*Complex.I) = v := by
    simpa only [hv,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I v
  by_cases harg : Complex.arg v < 0
  · refine ⟨Complex.arg v+2*Real.pi,?_,?_,?_⟩
    · linarith [Complex.neg_pi_lt_arg v,Real.pi_pos]
    · linarith
    · rw [Complex.ofReal_add,add_mul,Complex.exp_add]
      rw [show (((2*Real.pi:ℝ):ℂ)*Complex.I) = 2*(Real.pi:ℂ)*Complex.I by push_cast; ring,
        Complex.exp_two_pi_mul_I,he,mul_one]
  · exact ⟨Complex.arg v,le_of_not_gt harg,(Complex.arg_le_pi v).trans_lt (by linarith [Real.pi_pos]),he⟩

theorem phase_ideal_grid_cover (N : ℕ) (hN : 0 < N) (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ j : ℕ,j < N ∧ ‖(Complex.exp (((2*Real.pi/(N:ℝ):ℝ):ℂ)*Complex.I))^j-v‖ ≤ 8/(N:ℝ) := by
  obtain ⟨t,ht0,htmax,ht⟩ := phase_angle_representative v hv
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  let x := (N:ℝ)*t/(2*Real.pi)
  let j := Nat.floor x
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hjlo : (j:ℝ) ≤ x := Nat.floor_le hx0
  have hjhi : x < (j:ℝ)+1 := Nat.lt_floor_add_one x
  have hxN : x < (N:ℝ) := by
    dsimp [x]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hjN : j < N := by exact_mod_cast hjlo.trans_lt hxN
  have hang : |2*Real.pi*(j:ℝ)/(N:ℝ)-t| ≤ 2*Real.pi/(N:ℝ) := by
    have hxl : 2*Real.pi*(j:ℝ) ≤ (N:ℝ)*t := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mp hjlo
      nlinarith
    have hxu : (N:ℝ)*t < 2*Real.pi*((j:ℝ)+1) := by
      have h := (div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mp hjhi
      nlinarith
    have hmul : (2*Real.pi*(j:ℝ)/(N:ℝ)-t)*(N:ℝ) = 2*Real.pi*(j:ℝ)-(N:ℝ)*t := by
      field_simp
    apply abs_le.mpr
    constructor
    · rw [← neg_div]
      apply (div_le_iff₀ hNR).mpr
      rw [hmul]
      nlinarith
    · apply (le_div_iff₀ hNR).mpr
      rw [hmul]
      nlinarith [Real.pi_pos]
  have hpow : (Complex.exp (((2*Real.pi/(N:ℝ):ℝ):ℂ)*Complex.I))^j =
      Complex.exp (((2*Real.pi*(j:ℝ)/(N:ℝ):ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨j,hjN,?_⟩
  rw [hpow,← ht]
  exact (norm_exp_mul_I_sub_le _ _).trans (hang.trans (by
    apply div_le_div_of_nonneg_right _ hNR.le
    linarith [Real.pi_lt_four]))

theorem phase_grid_actual_cover_and_table_cost : ∀ r q : ℕ,
  let N := 2^r
  let z := numericalDyadicPhase r false q
  let points := (phaseTable z N).1
  points.length=N ∧ (phaseTable z N).2=N-1 ∧
  (∀ j < N, gaussianRatComplex (points.getD j gone)=(gaussianRatComplex z)^j ∧
    ‖gaussianRatComplex (points.getD j gone)‖=1) ∧
  (∀ v : ℂ, ‖v‖=1 → ∃ j : ℕ, j<N ∧
    ‖gaussianRatComplex (points.getD j gone)-v‖ ≤ 8/(N:ℝ)+(N:ℝ)*((2:ℝ)⁻¹)^q) := by
  intro r q
  (try dsimp only)
  have ht := phaseTable_spec (numericalDyadicPhase r false q) (2^r)
  have hn := (numerical_dyadic_phase_exact_unitarity_and_error r q false).1
  have he := (numerical_dyadic_phase_exact_unitarity_and_error r q false).2
  have ha : dyadicPhaseAngle r false = 2*Real.pi/(2^r:ℕ) := by simp [dyadicPhaseAngle]
  rw [ha] at he
  refine ⟨ht.1,ht.2.1,?_,?_⟩
  · intro j hj
    exact ⟨ht.2.2 j hj,by rw [ht.2.2 j hj,norm_pow,hn,one_pow]⟩
  · intro v hv
    obtain ⟨j,hj,hd⟩ := phase_ideal_grid_cover (2^r) (by positivity) v hv
    refine ⟨j,hj,?_⟩
    rw [ht.2.2 j hj]
    have hn2 : ‖Complex.exp (((2*Real.pi/(2^r:ℕ):ℝ):ℂ)*Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,Real.exp_zero]
    have hp := phase_power_error _ _ _ hn hn2 he j
    have hjR : (j:ℝ) ≤ (2^r:ℕ) := by exact_mod_cast hj.le
    have hb := mul_le_mul_of_nonneg_right hjR (show 0 ≤ ((2:ℝ)⁻¹)^q by positivity)
    have htri : ‖gaussianRatComplex (numericalDyadicPhase r false q)^j-v‖ ≤
        ‖gaussianRatComplex (numericalDyadicPhase r false q)^j-(Complex.exp (((2*Real.pi/(2^r:ℕ):ℝ):ℂ)*Complex.I))^j‖+
        ‖(Complex.exp (((2*Real.pi/(2^r:ℕ):ℝ):ℂ)*Complex.I))^j-v‖ := by
      convert norm_add_le
        (gaussianRatComplex (numericalDyadicPhase r false q)^j-(Complex.exp (((2*Real.pi/(2^r:ℕ):ℝ):ℂ)*Complex.I))^j)
        ((Complex.exp (((2*Real.pi/(2^r:ℕ):ℝ):ℂ)*Complex.I))^j-v) using 1; congr 1; ring
    exact htri.trans (by linarith)

end Qatlib.Concepts.NativeNumerics.PhaseSynthesis
