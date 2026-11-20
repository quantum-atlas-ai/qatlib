/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressBorn

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Partial Address Matching

Partial Address Matching constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
noncomputable section
open scoped BigOperators
open Qatlib ShiftCircuit NativeBridge RetainedSpin

namespace UniformMatching
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- Abbreviation for Global Record in the partial address matching model. -/
abbrev GlobalRecord (E : Type*) := E × PartialAddress.Record

/-- Construction for average in the partial address matching model. -/
def average (f : E → ℝ) : ℝ := (∑ e : E,f e)/(Fintype.card E : ℝ)

omit [DecidableEq E] in
/-- The real-valued cardinality of the finite edge set is positive when the set is nonempty. -/
theorem card_pos : (0 : ℝ)<Fintype.card E := by exact_mod_cast Fintype.card_pos

/-- Construction for law in the partial address matching model. -/
def law (u v : E → Bool → ℂ) (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    FinDist (GlobalRecord E) where
  prob r := actualProb (u r.1) (v r.1) r.2.1 r.2.2.1 r.2.2.2/(Fintype.card E : ℝ)
  nonneg r := div_nonneg (actual_prob_nonneg _ _ _ _ _) card_pos.le
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div]
    have hsum (e : E) : (∑ r : PartialAddress.Record,actualProb (u e) (v e) r.1 r.2.1 r.2.2)=1 :=
      (recordLaw (u e) (v e) (hu e) (hv e)).sum_one
    simp_rw [hsum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simpa only [mul_one] using div_self (ne_of_gt (card_pos (E:=E)))

/-- Construction for edge Scale in the partial address matching model. -/
def edgeScale : ℂ :=1/(Real.sqrt (Fintype.card E : ℝ) : ℂ)

omit [DecidableEq E] [Nonempty E] in
/-- The squared norm of the amplitude scale for one edge is the reciprocal of the edge count,
with Lean's totalized division. -/
theorem edge_scale_norm : Complex.normSq (edgeScale (E:=E))=1/(Fintype.card E : ℝ) := by
  simp [edgeScale,Complex.normSq_ofReal,Real.mul_self_sqrt]

omit [DecidableEq E] [Nonempty E] in
/-- Multiplying both endpoint spinors by `c` scales every Born record weight by the squared
complex norm of `c`. -/
theorem actual_prob_scale (c : ℂ) (u v : Bool → ℂ) (spin : Bool) (basis : Fin 3) (a : Bool) :
    actualProb (fun b => c*u b) (fun b => c*v b) spin basis a=
      Complex.normSq c*actualProb u v spin basis a := by
  fin_cases basis <;> cases a <;>
    simp [actual_prob_eq_signed,signedProb,sectorMass,sectorBloch,bitSign,
      Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im] <;> ring

/-- Construction for supplied in the partial address matching model. -/
def supplied (u v : E → Bool → ℂ) : QState (E × Reg 2) :=
  fun r => edgeScale (E:=E)*edgeInput (u r.1) (v r.1) r.2

omit [DecidableEq E] [Nonempty E] in
/-- The slice of the supplied state at edge `e` is the two-wire edge state formed from its
endpoint amplitudes scaled by the common edge factor. -/
theorem supplied_slice (u v : E → Bool → ℂ) (e : E) :
    (fun x => supplied u v (e,x))=
      edgeInput (fun b => edgeScale (E:=E)*u e b) (fun b => edgeScale (E:=E)*v e b) := by
  funext x
  cases h : x 0 <;> simp [supplied,edgeInput,h] <;> ring

omit [DecidableEq E] in
/-- On a nonempty matching, the supplied state has unit mass if both endpoint spinors have unit
mass on every edge. -/
theorem supplied_normalized (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) : Normalized (supplied u v) := by
  have he (e : E) : (∑ x : Reg 2,Complex.normSq (edgeInput (u e) (v e) x))=1 := by
    simpa only [Normalized,Complex.sq_norm] using edge_input_normalized (u e) (v e) (hu e) (hv e)
  unfold Normalized
  rw [Fintype.sum_prod_type]
  simp only [supplied,Complex.sq_norm,Complex.normSq_mul]
  simp_rw [← Finset.mul_sum,he]
  rw [edge_scale_norm]
  simp only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact (mul_comm _ _).trans (mul_one_div_cancel (ne_of_gt (card_pos (E:=E))))

omit [DecidableEq E] [Nonempty E] in
/-- At edge `e` and register bits `(a, b)`, the supplied amplitude selects the endpoint by `a`
and the spin by `b`, then divides by the square root of twice the edge count. -/
theorem supplied_amplitude (u v : E → Bool → ℂ) (e : E) (a b : Bool) :
    supplied u v (e,pairReg a b)=
      (if a then v e b else u e b)/(Real.sqrt (2*(Fintype.card E : ℝ)) : ℂ) := by
  have hr : (Real.sqrt (2*(Fintype.card E : ℝ)) : ℂ)=
      (Real.sqrt 2 : ℂ)*(Real.sqrt (Fintype.card E : ℝ) : ℂ) := by
    norm_cast
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card E : ℝ)
  rw [hr]
  simp only [supplied,edgeScale,edgeInput,pair_reg_first,pair_reg_second,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Construction for native Prob in the partial address matching model. -/
def nativeProb (u v : E → Bool → ℂ) (z : GlobalRecord E) : ℝ :=
  BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (endpointProgram z.2.2.1)
    (spinProjection z.2.1 (fun x => supplied u v (z.1,x)))) (pairReg z.2.2.2 z.2.1)/3

omit [DecidableEq E] [Nonempty E] in
/-- A native global record has Born weight equal to its local record weight on the selected
edge divided by the number of edges. -/
theorem native_prob_uniform (u v : E → Bool → ℂ) (z : GlobalRecord E) :
    nativeProb u v z=actualProb (u z.1) (v z.1) z.2.1 z.2.2.1 z.2.2.2/(Fintype.card E : ℝ) := by
  unfold nativeProb
  rw [supplied_slice,← edge_spin_filter]
  change actualProb (fun b => edgeScale (E:=E)*u z.1 b)
    (fun b => edgeScale (E:=E)*v z.1 b) z.2.1 z.2.2.1 z.2.2.2=_
  rw [actual_prob_scale,edge_scale_norm]
  ring

omit [DecidableEq E] in
/-- For unit spinors on every edge, each probability in the uniform matching law agrees with
the native circuit's record weight. -/
theorem law_prob_native (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (z : GlobalRecord E) :
    (law u v hu hv).prob z=nativeProb u v z := by
  exact (native_prob_uniform u v z).symm

/-- Construction for global Kernel in the partial address matching model. -/
def globalKernel (r s : GlobalRecord E) : ℝ :=
  if r.1=s.1 then (Fintype.card E : ℝ)*kernel r.2 s.2 else 0

omit [Nonempty E] in
/-- Interchanging the two global records preserves the value of the same-edge kernel. -/
theorem global_kernel_symmetric (r s : GlobalRecord E) : globalKernel r s=globalKernel s r := by
  simp [globalKernel,eq_comm,kernel_symmetric]

omit [DecidableEq E] in
/-- The expectation of an edge-dependent record statistic is the uniform edge average of its
local Born expectations. -/
theorem law_expect (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (f : E → PartialAddress.Record → ℝ) :
    (law u v hu hv).expect (fun r => f r.1 r.2)=
      average (fun e => (recordLaw (u e) (v e) (hu e) (hv e)).expect (f e)) := by
  change (∑ z : GlobalRecord E,actualProb (u z.1) (v z.1) z.2.1 z.2.2.1 z.2.2.2 /
    (Fintype.card E : ℝ)*f z.1 z.2)=
    (∑ e : E,∑ r : PartialAddress.Record,actualProb (u e) (v e) r.1 r.2.1 r.2.2*f e r)/
      (Fintype.card E : ℝ)
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Averaging the global kernel against a second record gives the local projection on the first
record's edge. The edge-count factor cancels its sampling probability. -/
theorem global_projection (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (r : GlobalRecord E) :
    pairKernelProjection (law u v hu hv) globalKernel r=projection (u r.1) (v r.1) r.2 := by
  change (∑ s : GlobalRecord E,actualProb (u s.1) (v s.1) s.2.1 s.2.2.1 s.2.2.2 /
    (Fintype.card E : ℝ)*(if r.1=s.1 then (Fintype.card E : ℝ)*kernel r.2 s.2 else 0))=_
  rw [Fintype.sum_prod_type,Finset.sum_eq_single r.1]
  · simp only [ite_true]
    change (∑ s : PartialAddress.Record,actualProb (u r.1) (v r.1) s.1 s.2.1 s.2.2 /
      (Fintype.card E : ℝ)*((Fintype.card E : ℝ)*kernel r.2 s))=
      ∑ s : PartialAddress.Record,actualProb (u r.1) (v r.1) s.1 s.2.1 s.2.2*kernel r.2 s
    apply Finset.sum_congr rfl
    intro s _
    have hK := ne_of_gt (card_pos (E:=E))
    field_simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

/-- The global kernel mean under two independent records is the uniform average of the edge
Bell probabilities. -/
theorem global_mean (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    pairKernelMean (law u v hu hv) globalKernel=average (fun e => bellProbability (u e) (v e)) := by
  change (law u v hu hv).expect (fun r => pairKernelProjection (law u v hu hv) globalKernel r)=_
  simp_rw [global_projection]
  rw [law_expect u v hu hv (fun e r => projection (u e) (v e) r)]
  change average (fun e => kernelMean (u e) (v e))=_
  simp_rw [kernel_mean_eq_bell]

/-- The conditional second moment of the global kernel with its first record fixed is the edge
count times the local squared-kernel projection at that record. -/
theorem global_square_projection (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (r : GlobalRecord E) :
    (law u v hu hv).expect (fun s => (globalKernel r s)^2)=
      (Fintype.card E : ℝ)*squareProjection (u r.1) (v r.1) r.2 := by
  change (∑ s : GlobalRecord E,actualProb (u s.1) (v s.1) s.2.1 s.2.2.1 s.2.2.2 /
    (Fintype.card E : ℝ)*(if r.1=s.1 then (Fintype.card E : ℝ)*kernel r.2 s.2 else 0)^2)=_
  rw [Fintype.sum_prod_type,Finset.sum_eq_single r.1]
  · simp only [ite_true,squareProjection,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hK := ne_of_gt (card_pos (E:=E))
    field_simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

omit [DecidableEq E] [Nonempty E] in
/-- A scalar constant can be moved outside the uniform edge average. -/
theorem average_const_mul (c : ℝ) (f : E → ℝ) : average (fun e => c*f e)=c*average f := by
  unfold average
  rw [← Finset.mul_sum]
  ring

/-- The global pair kernel's second moment is the edge count times the edge average of thirteen
times the sector product plus the Bell probability. -/
theorem global_kernel_second (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    (law u v hu hv).expect (fun r => (law u v hu hv).expect (fun s => (globalKernel r s)^2))=
      (Fintype.card E : ℝ)*average (fun e => 13*sectorProduct (u e) (v e)+bellProbability (u e) (v e)) := by
  simp_rw [global_square_projection]
  rw [law_expect u v hu hv (fun e r => (Fintype.card E : ℝ)*squareProjection (u e) (v e) r)]
  simp_rw [finite_expect_mul]
  change average (fun e => (Fintype.card E : ℝ)*kernelSecond (u e) (v e))=_
  simp_rw [kernel_second_exact]
  exact average_const_mul _ _

/-- The second moment of the one-record global projection is the edge average of half the
sector product plus half the Bell probability. -/
theorem global_projection_second (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    (law u v hu hv).expect (fun r => (pairKernelProjection (law u v hu hv) globalKernel r)^2)=
      average (fun e => (sectorProduct (u e) (v e)+bellProbability (u e) (v e))/2) := by
  simp_rw [global_projection]
  rw [law_expect u v hu hv (fun e r => (projection (u e) (v e) r)^2)]
  change average (fun e => projectionSecond (u e) (v e))=_
  have he (e : E) := projection_second_exact (u e) (v e) (hu e) (hv e)
  simp_rw [he]

omit [DecidableEq E] [Nonempty E] in
/-- A function that is nonnegative on every edge has nonnegative edge average. -/
theorem average_nonneg (f : E → ℝ) (hf : ∀ e,0 ≤ f e) : 0 ≤ average f := by
  exact div_nonneg (Finset.sum_nonneg fun e _ => hf e) (Nat.cast_nonneg _)

omit [DecidableEq E] [Nonempty E] in
/-- A pointwise inequality between two edge functions is preserved by their uniform averages. -/
theorem average_mono (f g : E → ℝ) (h : ∀ e,f e ≤ g e) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun e _ => h e) (Nat.cast_nonneg _)

/-- For at least two independent matching records from normalized endpoints, the ordered global
U-statistic is unbiased for the average Bell probability. -/
theorem actual_global_unbiased {n : ℕ} (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → GlobalRecord E,(law u v hu hv).probOf ω*orderedUStatistic globalKernel ω)=
      average (fun e => bellProbability (u e) (v e)) := by
  rw [ordered_ustatistic_unbiased (law u v hu hv) globalKernel hn]
  exact global_mean u v hu hv

/-- The global projection variance is the edge average of half the sector product plus half the
Bell probability, minus the square of the mean Bell probability. -/
theorem global_projection_variance (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    (law u v hu hv).variance (pairKernelProjection (law u v hu hv) globalKernel)=
      average (fun e => (sectorProduct (u e) (v e)+bellProbability (u e) (v e))/2)-
        (average (fun e => bellProbability (u e) (v e)))^2 := by
  rw [finite_variance_identity,global_projection_second]
  change average (fun e => (sectorProduct (u e) (v e)+bellProbability (u e) (v e))/2)-
    (pairKernelMean (law u v hu hv) globalKernel)^2=_
  rw [global_mean]

/-- The variance of the kernel on two independent matching records is the edge count times the
mean local second moment, minus the squared mean Bell probability. -/
theorem global_pair_variance (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    (law u v hu hv).expect (fun r => (law u v hu hv).expect
      (fun s => (globalKernel r s-pairKernelMean (law u v hu hv) globalKernel)^2))=
      (Fintype.card E : ℝ)*average
        (fun e => 13*sectorProduct (u e) (v e)+bellProbability (u e) (v e))-
        (average (fun e => bellProbability (u e) (v e)))^2 := by
  rw [pair_variance_identity,global_kernel_second,global_mean]

/-- For `n ≥ 2` records from normalized endpoints, the mean squared error about the average
Bell probability combines global projection variance with weight `4(n-2)/(n(n-1))` and global
pair variance with weight `2/(n(n-1))`. -/
theorem actual_global_variance {n : ℕ} (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → GlobalRecord E,(law u v hu hv).probOf ω*
      (orderedUStatistic globalKernel ω-average (fun e => bellProbability (u e) (v e)))^2)=
      4*((n : ℝ)-2)/(n*(n-1) : ℕ)*
        (average (fun e => (sectorProduct (u e) (v e)+bellProbability (u e) (v e))/2)-
          (average (fun e => bellProbability (u e) (v e)))^2)+
      2/(n*(n-1) : ℕ)*((Fintype.card E : ℝ)*
        average (fun e => 13*sectorProduct (u e) (v e)+bellProbability (u e) (v e))-
          (average (fun e => bellProbability (u e) (v e)))^2) := by
  have h := ordered_ustatistic_variance (law u v hu hv) globalKernel global_kernel_symmetric hn
  rw [global_projection_variance,global_pair_variance,global_mean] at h
  exact h

/-- If the average true-spin mass is at most `q`, the mean squared Bell estimation error from
`n ≥ 2` independent uniform matching records is at most `6q/n` plus `30q` times the edge count
divided by `n(n-1)`. -/
theorem actual_global_variance_bound {n : ℕ} (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) (hn : 2 ≤ n)
    (q : ℝ) (hq : average (fun e => sectorMass (u e) (v e) true) ≤ q) :
    (∑ ω : Fin n → GlobalRecord E,(law u v hu hv).probOf ω*
      (orderedUStatistic globalKernel ω-average (fun e => bellProbability (u e) (v e)))^2) ≤
      6*q/(n : ℝ)+30*(Fintype.card E : ℝ)*q/(n*(n-1) : ℕ) := by
  have hq0 : 0 ≤ q := (average_nonneg _ (fun e => sector_mass_nonneg (u e) (v e) true)).trans hq
  have hloc (e : E) : (sectorProduct (u e) (v e)+bellProbability (u e) (v e))/2 ≤
      (3/2 : ℝ)*sectorMass (u e) (v e) true := by
    have hnu := sector_product_le_minority (u e) (v e) (hu e) (hv e)
    have hmu := bell_le_twice_sector_product (u e) (v e)
    linarith
  have hg0 := average_mono _ _ hloc
  rw [average_const_mul] at hg0
  have hg : (law u v hu hv).variance
      (pairKernelProjection (law u v hu hv) globalKernel) ≤ 3*q/2 := by
    calc
      _ ≤ (law u v hu hv).expect (fun r => (pairKernelProjection (law u v hu hv) globalKernel r)^2) :=
        finite_variance_le_second _ _
      _ = _ := global_projection_second u v hu hv
      _ ≤ 3*q/2 := by linarith
  have hlocD (e : E) : 13*sectorProduct (u e) (v e)+bellProbability (u e) (v e) ≤
      15*sectorMass (u e) (v e) true := by
    have hnu := sector_product_le_minority (u e) (v e) (hu e) (hv e)
    have hmu := bell_le_twice_sector_product (u e) (v e)
    linarith
  have hD0 := average_mono _ _ hlocD
  rw [average_const_mul] at hD0
  have hD1 : average (fun e => 13*sectorProduct (u e) (v e)+bellProbability (u e) (v e)) ≤ 15*q := by
    linarith
  have hD : (law u v hu hv).expect (fun r => (law u v hu hv).expect (fun s => (globalKernel r s)^2)) ≤
      15*(Fintype.card E : ℝ)*q := by
    rw [global_kernel_second]
    calc
      _ ≤ (Fintype.card E : ℝ)*(15*q) := mul_le_mul_of_nonneg_left hD1 (card_pos (E:=E)).le
      _ = _ := by ring
  have h := ordered_ustatistic_variance_bound (law u v hu hv) globalKernel
    global_kernel_symmetric hn (3*q/2) (15*(Fintype.card E : ℝ)*q) (by positivity) hg hD
  rw [global_mean] at h
  convert h using 1
  ring

#print axioms supplied_amplitude
#print axioms supplied_normalized
#print axioms law_prob_native
#print axioms law
#print axioms global_projection
#print axioms global_mean
#print axioms global_kernel_second
#print axioms global_projection_second
#print axioms actual_global_unbiased
#print axioms actual_global_variance
#print axioms actual_global_variance_bound
end UniformMatching

end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
