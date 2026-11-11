/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
import Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap

open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

/-!
# Pair Purification

Literal four pure states, ordered by the two original signs.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification
open Qatlib
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- Literal four pure states, ordered by the two original signs. -/
def sourceStates {D : ℕ} (u v : Fin 2 → QState (Fin D)) : Fin 4 → QState (Fin D) :=
  ![u 0-v 0,u 0+v 0,u 1-v 1,u 1+v 1]

/-- Four environment columns of an explicit purification of the original sign-pair mixture. -/
def columns {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ : ℝ) : Fin 4 → QState (Fin D) :=
  let q : ℂ := (Real.sqrt (2 : ℝ) : ℂ)⁻¹
  let s : ℂ := Real.sqrt (1-ρ^2)
  ![q • (u 0-(ρ:ℂ) • v 0), (q*s) • v 0,
    q • (u 1+(ρ:ℂ) • v 1), (q*s) • v 1]

/-- The constructed vector retains the full physical system and exposes only its purification environment. -/
def witness {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ : ℝ) : QState (Fin D × Fin 4) :=
  fun x => columns u v ρ x.2 x.1

/-- The partial trace is the literal original mixture, including zero parity components. -/
theorem witness_partialTrace {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    PartialTrace (outerProduct (witness u v ρ))=
      ∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i) := by
  have ht : 0≤1-ρ^2 := by nlinarith [mul_nonneg (by linarith : 0≤1-ρ) (by linarith : 0≤1+ρ)]
  have hq : ((Real.sqrt (2 : ℝ) : ℂ)⁻¹)^2=(1/2 : ℂ) := by
    rw [inv_pow,←Complex.ofReal_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
    norm_num
  have hs : ((Real.sqrt (1-ρ^2) : ℂ))^2=1-(ρ:ℂ)^2 := by
    exact_mod_cast Real.sq_sqrt ht
  ext i j
  simp [PartialTrace,outerProduct,witness,columns,sourceStates,signPairLaw,
    Fin.sum_univ_succ,Matrix.sum_apply,Complex.ofReal_add,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_one]
  ring_nf
  simp only [hq,hs]
  ring

/-- Normalized source vectors and the actual sign-pair law give a legal input density. -/
theorem mixture_density {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    IsDensityOperator (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i)) := by
  have hp := signPairLaw_prob ρ hlo hhi
  constructor
  · apply Matrix.posSemidef_sum
    intro i _
    exact (outerProduct_posSemidef (sourceStates u v i)).smul (by exact_mod_cast hp.1 i)
  · simp only [Matrix.trace_sum,Matrix.trace_smul,(outerProduct_density (hn _)).2,
      smul_eq_mul,mul_one]
    exact_mod_cast hp.2

/-- The actual four-column witness is normalized, rather than carrying an assumed norm certificate. -/
theorem witness_isPurification {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    IsPurification (witness u v ρ)
      (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i)) := by
  have hp := witness_partialTrace u v ρ hlo hhi
  refine ⟨?_,hp⟩
  have ht := congrArg Matrix.trace hp
  rw [trace_partialTrace,trace_outerProduct,(mixture_density u v hn ρ hlo hhi).2] at ht
  exact_mod_cast ht

/-- Zero padding supplies a large enough environment for the exact public Uhlmann interface. -/
def paddedWitness {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ : ℝ) :
    QState (Fin D × Fin (4+D)) :=
  fun x => Fin.append (fun e => witness u v ρ (x.1,e)) (fun _ => 0) x.2

/-- Zero environment columns preserve the literal reduced physical density. -/
theorem paddedWitness_partialTrace {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ : ℝ) :
    PartialTrace (outerProduct (paddedWitness u v ρ))=
      PartialTrace (outerProduct (witness u v ρ)) := by
  ext i j
  simp [PartialTrace,outerProduct,paddedWitness,Fin.sum_univ_add]

/-- The padded witness is an actual normalized purification of the same original mixture. -/
theorem paddedWitness_isPurification {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    IsPurification (paddedWitness u v ρ)
      (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i)) := by
  have hp := (paddedWitness_partialTrace u v ρ).trans (witness_partialTrace u v ρ hlo hhi)
  refine ⟨?_,hp⟩
  have ht := congrArg Matrix.trace hp
  rw [trace_partialTrace,trace_outerProduct,(mixture_density u v hn ρ hlo hhi).2] at ht
  exact_mod_cast ht

/-- Padding changes neither the physical registers nor the actual purification overlap. -/
theorem paddedWitness_inner {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ ξ : ℝ) :
    Qatlib.Foundations.PureStateMath.Inner (paddedWitness u v ρ) (paddedWitness u v ξ)=
      Qatlib.Foundations.PureStateMath.Inner (witness u v ρ) (witness u v ξ) := by
  simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct,paddedWitness,
    Fintype.sum_prod_type,Fin.sum_univ_add]

/-- The literal original pair mixtures have at least the overlap of the constructed physical purifications. -/
theorem mixture_fidelity_witness_lower {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ ξ : ℝ)
    (hρlo : -1≤ρ) (hρhi : ρ≤1) (hξlo : -1≤ξ) (hξhi : ξ≤1) :
    ‖Qatlib.Foundations.PureStateMath.Inner (witness u v ρ) (witness u v ξ)‖ ≤
      Froot (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i))
        (∑ i,(signPairLaw ξ i : ℂ) • outerProduct (sourceStates u v i)) := by
  have h := (g2 D (4+D) (by omega)
    _ _ (mixture_density u v hn ρ hρlo hρhi) (mixture_density u v hn ξ hξlo hξhi)).1
    _ _ (paddedWitness_isPurification u v hn ρ hρlo hρhi)
      (paddedWitness_isPurification u v hn ξ hξlo hξhi)
  rw [paddedWitness_inner] at h
  exact h

/-- Literal purification distance depends only on the weak odd-parity components. -/
theorem witness_squareDistance {D : ℕ} (u v : Fin 2 → QState (Fin D)) (ρ ξ : ℝ) :
    (∑ x,‖witness u v ρ x-witness u v ξ x‖^2)=
      ((ρ-ξ)^2+(Real.sqrt (1-ρ^2)-Real.sqrt (1-ξ^2))^2)/2 *
        (∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) := by
  have hq : ‖(Real.sqrt (2 : ℝ) : ℂ)⁻¹‖^2=(1/2 : ℝ) := by
    rw [norm_inv,inv_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hi (i : Fin D) :
      (∑ e : Fin 4,‖columns u v ρ e i-columns u v ξ e i‖^2)=
        ((ρ-ξ)^2+(Real.sqrt (1-ρ^2)-Real.sqrt (1-ξ^2))^2)/2 *
          (‖v 0 i‖^2+‖v 1 i‖^2) := by
    have h0 : columns u v ρ 0 i-columns u v ξ 0 i=
        (Real.sqrt (2 : ℝ) : ℂ)⁻¹ * ((ξ-ρ : ℝ) : ℂ) * v 0 i := by
      simp [columns]
      ring
    have h1 : columns u v ρ 1 i-columns u v ξ 1 i=
        (Real.sqrt (2 : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (1-ρ^2)-Real.sqrt (1-ξ^2) : ℝ) : ℂ) * v 0 i := by
      simp [columns]
      ring
    have h2 : columns u v ρ 2 i-columns u v ξ 2 i=
        (Real.sqrt (2 : ℝ) : ℂ)⁻¹ * ((ρ-ξ : ℝ) : ℂ) * v 1 i := by
      simp [columns]
      ring
    have h3 : columns u v ρ 3 i-columns u v ξ 3 i=
        (Real.sqrt (2 : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (1-ρ^2)-Real.sqrt (1-ξ^2) : ℝ) : ℂ) * v 1 i := by
      simp [columns]
      ring
    have he1 : (0 : Fin 3).succ=(1 : Fin 4) := by decide
    have he2 : (0 : Fin 2).succ.succ=(2 : Fin 4) := by decide
    have he3 : (0 : Fin 1).succ.succ.succ=(3 : Fin 4) := by decide
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,he1,he2,he3]
    rw [h0,h1,h2,h3]
    simp only [norm_mul,mul_pow,hq,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  rw [Fintype.sum_prod_type]
  simp only [witness,hi,←Finset.mul_sum]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap

/-- The explicit physical witness has exactly the overlap needed for the weak-pair information bound. -/
theorem witness_real_inner {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ ξ : ℝ)
    (hρlo : -1 ≤ ρ) (hρhi : ρ ≤ 1) (hξlo : -1 ≤ ξ) (hξhi : ξ ≤ 1) :
    (Qatlib.Foundations.PureStateMath.Inner (witness u v ρ) (witness u v ξ)).re=
      1-semicircleDeficit ρ ξ/2*(∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) := by
  have hρn : 0 ≤ 1-ρ^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-ρ) (by linarith : 0 ≤ 1+ρ)]
  have hξn : 0 ≤ 1-ξ^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-ξ) (by linarith : 0 ≤ 1+ξ)]
  have hc : ((ρ-ξ)^2+(Real.sqrt (1-ρ^2)-Real.sqrt (1-ξ^2))^2)/2=
      semicircleDeficit ρ ξ := by
    rw [semicircleDeficit,Real.sqrt_mul hρn]
    nlinarith [Real.sq_sqrt hρn,Real.sq_sqrt hξn]
  rw [real_inner_eq_one_sub_distance _ _
    (witness_isPurification u v hn ρ hρlo hρhi).1
    (witness_isPurification u v hn ξ hξlo hξhi).1]
  rw [squareDistance,witness_squareDistance,hc]
  ring

/-- Genuine pair mixtures lose at most their odd-component mass times the semicircle deficit. -/
theorem mixture_fidelity_deficit {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (ρ ξ : ℝ)
    (hρlo : -1 ≤ ρ) (hρhi : ρ ≤ 1) (hξlo : -1 ≤ ξ) (hξhi : ξ ≤ 1) :
    1-Froot (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i))
      (∑ i,(signPairLaw ξ i : ℂ) • outerProduct (sourceStates u v i)) ≤
        semicircleDeficit ρ ξ/2*(∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) := by
  have h := mixture_fidelity_witness_lower u v hn ρ ξ hρlo hρhi hξlo hξhi
  have hr := Complex.re_le_norm
    (Qatlib.Foundations.PureStateMath.Inner (witness u v ρ) (witness u v ξ))
  rw [witness_real_inner u v hn ρ ξ hρlo hρhi hξlo hξhi] at hr
  linarith

/-- An actual normalized four-state family has a quadratic fidelity loss controlled by its literal odd components. -/
theorem mixture_fidelity_quadratic {D : ℕ} (u v : Fin 2 → QState (Fin D))
    (hn : ∀ i,Normalized (sourceStates u v i)) (a ρ ξ : ℝ)
    (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-Froot (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (sourceStates u v i))
      (∑ i,(signPairLaw ξ i : ℂ) • outerProduct (sourceStates u v i)) ≤
        (ρ-ξ)^2/(4*(1-a^2))*(∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) := by
  have hr := abs_le.mp hρ
  have hx := abs_le.mp hξ
  have h := mixture_fidelity_deficit u v hn ρ ξ (by linarith) (by linarith) (by linarith) (by linarith)
  have hb := (semicircleDeficit_bound a ρ ξ ha hρ hξ).2
  have hn0 : 0 ≤ ∑ i : Fin D,(‖v 0 i‖^2+‖v 1 i‖^2) :=
    Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc _ ≤ semicircleDeficit ρ ξ/2*(∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) := h
       _ ≤ ((ρ-ξ)^2/(2*(1-a^2)))/2*(∑ i,(‖v 0 i‖^2+‖v 1 i‖^2)) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb (by norm_num)) hn0
       _ = _ := by
         have he : 2*(1-a^2)*2=4*(1-a^2) := by ring
         rw [div_div,he]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification
