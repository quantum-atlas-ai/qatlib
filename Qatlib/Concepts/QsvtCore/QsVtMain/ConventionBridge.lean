/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.List.Indexes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvtConsumers
set_option warningAsError false

open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtMain
open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def sourceDefWord (U P Q : Matrix H H ℂ) : List ℝ → Matrix H H ℂ
  | [] => 1
  | φ :: Φ => phaseRotation Q (anglePhase φ) * U * sourceDefWord Uᴴ Q P Φ

def sourceConstantMinimalLength (c : ℝ) : ℕ :=
  if c = 1 then 0 else if c = 0 then 1 else 2

theorem sourceDefWord_eq_phasedAlternating (U P Q : Matrix H H ℂ) (Φ : List ℝ) :
    sourceDefWord U P Q Φ = phasedAlternating U P Q 1 (Φ.map anglePhase) := by
  induction Φ generalizing U P Q with
  | nil => simp [sourceDefWord, phasedAlternating]
  | cons φ Φ ih => simp only [sourceDefWord, List.map_cons, phasedAlternating, ih]

theorem source_response_global_phase (base : ℂ) (zs : List ℂ) :
    responseP base zs = C base*responseP 1 zs ∧ responseQ base zs = C base*responseQ 1 zs := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
    constructor <;> ring

theorem source_phase_real_normal_form (zs : List ℂ) (hz : ∀ z ∈ zs, IsPhase z) :
    ∃ Φ : List ℝ, Φ.length = zs.length ∧ sourcePhaseResponse Φ = responseP 1 zs := by
  have hmap : (zs.map Complex.arg).map anglePhase = zs := by
    rw [List.map_map]
    calc
      zs.map (anglePhase ∘ Complex.arg) = zs.map id := by
        apply List.map_congr_left
        intro z h
        exact anglePhase_arg_of_isPhase (hz z h)
      _ = zs := List.map_id zs
  exact ⟨zs.map Complex.arg, by simp, by rw [sourcePhaseResponse, hmap]⟩

theorem source_terminal_base_absorption (b : ℂ) (φ : ℝ) (Φ : List ℝ) (hb : IsPhase b) :
    ∃ θ : ℝ, sourcePhaseResponse (θ::Φ) = C b*sourcePhaseResponse (φ::Φ) := by
  have hz : IsPhase (b*anglePhase φ) := by
    have hφ := anglePhase_isPhase φ
    unfold IsPhase at hb hφ ⊢
    rw [star_mul]
    calc
      star (anglePhase φ)*star b*(b*anglePhase φ) =
          (star b*b)*(star (anglePhase φ)*anglePhase φ) := by ring
      _ = 1 := by rw [hb,hφ]; simp
  refine ⟨(b*anglePhase φ).arg, ?_⟩
  simp only [sourcePhaseResponse, List.map_cons, anglePhase_arg_of_isPhase hz, responseP_cons,
    map_mul]
  ring

private theorem source_angle_add (a b : ℝ) : anglePhase (a+b) = anglePhase a*anglePhase b := by
  apply Complex.ext <;> simp [anglePhase, Real.cos_add, Real.sin_add, Complex.mul_re,
      Complex.mul_im, add_comm]

private theorem source_angle_neg (a : ℝ) : anglePhase (-a) = star (anglePhase a) := by
  apply Complex.ext <;> simp [anglePhase]
private def sourceAltSum (Φ : List ℝ) : ℝ := (Φ.mapIdx (fun i φ => (-1 : ℝ)^i*φ)).sum

private theorem source_alt_cons (φ : ℝ) (Φ : List ℝ) : sourceAltSum (φ::Φ) = φ-sourceAltSum Φ := by
  unfold sourceAltSum
  rw [List.mapIdx_cons, List.sum_cons]
  simp only [pow_zero, one_mul]
  have htail : Φ.mapIdx (fun i φ => (-1 : ℝ)^(i+1)*φ) =
      (Φ.mapIdx (fun i φ => (-1 : ℝ)^i*φ)).map Neg.neg := by
    simp only [List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    simp only [pow_succ]
    ring
  rw [htail]
  have hneg (xs : List ℝ) : (xs.map Neg.neg).sum = -xs.sum := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, add_comm]
  rw [hneg]
  ring

private theorem source_response_zero (Φ : List ℝ) :
    (responseP 1 (Φ.map anglePhase)).eval 0 =
      (if Φ.length%2=0 then anglePhase (sourceAltSum Φ) else 0) ∧
    (responseQ 1 (Φ.map anglePhase)).eval 0 =
      (if Φ.length%2=1 then anglePhase (-sourceAltSum Φ) else 0) := by
  induction Φ with
  | nil =>
    simp only [List.map_nil, responseP_nil, responseQ_nil, eval_C, eval_zero,
      List.length_nil, Nat.zero_mod, sourceAltSum, List.mapIdx_nil, List.sum_nil,
      neg_zero]
    constructor
    · apply Complex.ext <;> simp [anglePhase]
    · simp
  | cons φ Φ ih =>
    simp only [List.map_cons, responseP_cons, responseQ_cons, eval_mul, eval_add,
      eval_sub, eval_C, eval_X, eval_one, eval_pow, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_zero, one_mul, zero_add, ih.1, ih.2, List.length_cons, source_alt_cons]
    rcases Nat.mod_two_eq_zero_or_one Φ.length with hm | hm
    · simp only [hm, Nat.add_mod, Nat.zero_add, Nat.reduceMod, ite_true]
      constructor
      · simp
      · rw [← source_angle_neg, ← source_angle_add]
        congr 1
        ring
    · simp only [hm, Nat.add_mod, Nat.reduceAdd, Nat.reduceMod, ite_true]
      constructor
      · exact (source_angle_add φ (-sourceAltSum Φ)).symm
      · simp

theorem source_response_endpoint_values (Φ : List ℝ) :
    (sourcePhaseResponse Φ).eval (1 : ℂ) = (Φ.map anglePhase).prod ∧
    (sourcePhaseResponse Φ).eval (-1 : ℂ) = (-1 : ℂ)^Φ.length*(Φ.map anglePhase).prod ∧
    (Φ.length%2=1 → (sourcePhaseResponse Φ).eval (0 : ℂ)=0) ∧
    (Φ.length%2=0 → (sourcePhaseResponse Φ).eval (0 : ℂ)=
      anglePhase ((Φ.mapIdx (fun i φ => (-1 : ℝ)^i*φ)).sum)) := by
  have hone : (sourcePhaseResponse Φ).eval (1 : ℂ) = (Φ.map anglePhase).prod := by
    induction Φ with
    | nil => simp [sourcePhaseResponse]
    | cons φ Φ ih =>
      simp only [sourcePhaseResponse, List.map_cons, responseP_cons, eval_mul, eval_add,
        eval_sub, eval_C, eval_X, eval_one, eval_pow, one_pow, sub_self, zero_mul, add_zero,
        one_mul, List.prod_cons]
      exact congrArg (anglePhase φ * ·) ih
  refine ⟨hone, ?_, ?_, ?_⟩
  · simpa only [sourcePhaseResponse, List.length_map] using
      ((response_parity 1 (Φ.map anglePhase) (1 : ℂ)).1.trans
        (congrArg ((-1 : ℂ)^(Φ.map anglePhase).length * ·) hone))
  · intro hodd
    simpa [sourcePhaseResponse, hodd] using (source_response_zero Φ).1
  · intro heven
    simpa [sourcePhaseResponse, heven, sourceAltSum] using (source_response_zero Φ).1

theorem source_corner_odd_eq
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (Φ : List ℝ) (hodd : Φ.length%2=1) :
    rangeProjector L * phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        (Φ.map anglePhase) * rangeProjector R =
      L * oddSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ := by
  have he := qsvt_odd_eq_oddSingularTransform h 1 (Φ.map anglePhase)
    (by simpa only [List.length_map] using hodd)
  calc
    _ = L * compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        (Φ.map anglePhase)) R * Rᴴ := by
      simp only [rangeProjector, compress, Matrix.mul_assoc]
    _ = _ := by rw [he]; rfl

theorem source_corner_even_eq
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (Φ : List ℝ) (heven : Φ.length%2=0) :
    rangeProjector R * phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) 1
        (Φ.map anglePhase) * rangeProjector R =
      R * rightSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ := by
  have he := qsvt_even_right_eq_rightSingularTransform h 1 (Φ.map anglePhase)
    (by simpa only [List.length_map] using heven)
  calc
    _ = R * compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) 1
        (Φ.map anglePhase)) R * Rᴴ := by
      simp only [rangeProjector, compress, Matrix.mul_assoc]
    _ = _ := by rw [he]; rfl

private theorem source_real_part_polynomial (p : Polynomial ℝ) (P : Polynomial ℂ)
    (hre : ∀ x : ℝ, (P.eval (x : ℂ)).re = p.eval x) :
    P + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial P = C 2 * p.map Complex.ofRealHom := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨x, rfl⟩
  change (P + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial P).eval (x : ℂ) =
    (C 2 * p.map Complex.ofRealHom).eval (x : ℂ)
  have hm : (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
    change (p.map Complex.ofRealHom).eval (Complex.ofRealHom x) = Complex.ofRealHom (p.eval x)
    exact Polynomial.eval_map_apply Complex.ofRealHom x
  rw [eval_add,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial_eval_real P x, eval_mul, eval_C, hm]
  apply Complex.ext <;> simp [hre, two_mul]

theorem source_phase_length_minimality (p : Polynomial ℝ) (Φ : List ℝ)
    (hre : ∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) (_hp : p ≠ 0) :
    p.natDegree ≤ Φ.length ∧ HasRealParity Φ.length p := by
  have he := source_real_part_polynomial p (sourcePhaseResponse Φ) hre
  have hdeg := Polynomial.natDegree_add_le (sourcePhaseResponse Φ)
    (Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (sourcePhaseResponse Φ))
  rw [he, Polynomial.natDegree_C_mul (by norm_num : (2 : ℂ) ≠ 0),
    Polynomial.natDegree_map Complex.ofRealHom] at hdeg
  have hb : (sourcePhaseResponse Φ).natDegree ≤ Φ.length := by
    simpa only [sourcePhaseResponse, List.length_map] using (response_degree 1 (Φ.map anglePhase)).1
  refine ⟨hdeg.trans (max_le hb ?_), ?_⟩
  · exact (Polynomial.natDegree_map_le (f := starRingEnd ℂ)).trans hb
  · unfold HasRealParity
    apply Polynomial.funext
    intro x
    have hs := congrArg Complex.re ((response_parity 1 (Φ.map anglePhase) (x : ℂ)).1)
    simp only [List.length_map] at hs
    have hleft : ((sourcePhaseResponse Φ).eval (-(x : ℂ))).re = p.eval (-x) := by
      simpa only [Complex.ofReal_neg] using hre (-x)
    change ((sourcePhaseResponse Φ).eval (-(x : ℂ))).re =
      (((-1 : ℂ)^Φ.length)*((sourcePhaseResponse Φ).eval (x : ℂ))).re at hs
    rw [hleft] at hs
    have hpow : (-1 : ℂ)^Φ.length = (((-1 : ℝ)^Φ.length : ℝ) : ℂ) := by simp
    simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, hpow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre x] using hs

private theorem source_parity_unique (p : Polynomial ℝ) (hp : p ≠ 0) (n d : ℕ)
    (hn : HasRealParity n p) (hd : HasRealParity d p) : n%2=d%2 := by
  have he : C ((-1 : ℝ)^n)*p = C ((-1 : ℝ)^d)*p := hn.symm.trans hd
  have hs : (-1 : ℝ)^n = (-1 : ℝ)^d := C_injective (mul_right_cancel₀ hp he)
  conv_lhs at hs => rw [neg_one_pow_eq_pow_mod_two]
  conv_rhs at hs => rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1 <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · omega
  · norm_num [hn0,hd1] at hs
  · norm_num [hn1,hd0] at hs
  · omega

theorem source_minimal_degree_existence (p : Polynomial ℝ) (d : ℕ) (hd : 0 < d)
    (hdeg : p.degree = (d : WithBot ℕ)) (hpar : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ Φ : List ℝ, Φ.length=d ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re=p.eval x) ∧
      (∀ Ψ : List ℝ, (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re=p.eval x) →
        d ≤ Ψ.length ∧ Ψ.length%2=d%2) := by
  obtain ⟨Φ, hlen, hre⟩ := source_length_real_phase_existence p d hd hdeg.le hpar hb
  have hp : p ≠ 0 := by intro hz; simp [hz] at hdeg
  have hnat : p.natDegree = d := (Polynomial.degree_eq_iff_natDegree_eq hp).mp hdeg
  refine ⟨Φ, hlen, hre, ?_⟩
  intro Ψ hΨ
  have h := source_phase_length_minimality p Ψ hΨ hp
  exact ⟨hnat ▸ h.1, source_parity_unique p hp Ψ.length d h.2 hpar⟩

theorem source_constant_minimal_length (c : ℝ) (hc : |c| ≤ 1) :
    (∃ Φ : List ℝ, Φ.length=sourceConstantMinimalLength c ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re=c)) ∧
    (∀ Ψ : List ℝ, (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re=c) →
      sourceConstantMinimalLength c ≤ Ψ.length) := by
  by_cases hc1 : c=1
  · subst c
    simp only [sourceConstantMinimalLength]
    exact ⟨⟨[], rfl, by simp [sourcePhaseResponse]⟩, fun _ _ => Nat.zero_le _⟩
  by_cases hc0 : c=0
  · subst c
    simp only [sourceConstantMinimalLength, show (0 : ℝ) ≠ 1 by norm_num, if_false]
    constructor
    · refine ⟨[Real.pi/2], rfl, ?_⟩
      intro x
      simp [sourcePhaseResponse, anglePhase, Real.cos_pi_div_two,
        Real.sin_pi_div_two, Complex.mul_re]
    · intro Ψ hΨ
      cases Ψ with
      | nil => have h := hΨ 0; simp [sourcePhaseResponse] at h
      | cons φ Φ => simp
  · simp only [sourceConstantMinimalLength, hc1, hc0, if_false]
    constructor
    · obtain ⟨Φ, hlen, hre⟩ := source_length_real_phase_existence (C c) 2 (by norm_num)
        (degree_C_le.trans (by norm_num)) (by simp [HasRealParity])
        (by simpa only [eval_C] using fun _ _ => hc)
      exact ⟨Φ, hlen, fun x => (hre x).trans (by simp)⟩
    · intro Ψ hΨ
      cases Ψ with
      | nil => have h := hΨ 0; simp [sourcePhaseResponse] at h; exact (hc1 h.symm).elim
      | cons φ Φ =>
        cases Φ with
        | nil =>
          have h := hΨ 0
          simp [sourcePhaseResponse] at h
          exact (hc0 h.symm).elim
        | cons θ Φ => simp

end Qatlib.Concepts.QsvtCore.QsVtMain
