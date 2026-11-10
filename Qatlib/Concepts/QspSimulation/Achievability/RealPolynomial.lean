/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacs
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Real.Sqrt
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PolyApprox

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

def HasRealParity (d : ℕ) (p : Polynomial ℝ) : Prop :=
  p.comp (-X) = C ((-1 : ℝ) ^ d) * p

noncomputable def squareResidual (p : Polynomial ℝ) : Polynomial ℝ :=
  contract 2 (1 - p ^ 2)

private theorem neg_one_pow_sq (d : ℕ) : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
  norm_num

theorem residual_even {d : ℕ} {p : Polynomial ℝ} (hp : HasRealParity d p) :
    (1 - p ^ 2).comp (-X) = 1 - p ^ 2 := by
  change p.comp (-X) = C ((-1 : ℝ) ^ d) * p at hp
  simp only [sub_comp, one_comp, pow_comp, hp, mul_pow, ← C_pow,
    neg_one_pow_sq, C_1, one_mul]

private theorem coeff_zero_of_odd {f : Polynomial ℝ}
    (hf : f.comp (-X) = f) {k : ℕ} (hk : ¬ 2 ∣ k) : f.coeff k = 0 := by
  have he := congrArg (fun q : Polynomial ℝ => q.coeff k) hf
  have hx : (-X : Polynomial ℝ) = C (-1) * X := by simp
  have ho : Odd k := Nat.not_even_iff_odd.mp (fun h => hk h.two_dvd)
  simp only [hx, comp_C_mul_X_coeff, ho.neg_one_pow] at he
  linarith

theorem comp_square_contract_of_even {f : Polynomial ℝ}
    (hf : f.comp (-X) = f) : (contract 2 f).comp (X ^ 2) = f := by
  rw [← expand_eq_comp_X_pow]
  ext k
  rw [coeff_expand (by decide : 0 < 2), coeff_contract (by decide : 2 ≠ 0)]
  split_ifs with hk
  · rw [Nat.div_mul_cancel hk]
  · exact (coeff_zero_of_odd hf hk).symm

theorem squareResidual_comp {d : ℕ} {p : Polynomial ℝ} (hp : HasRealParity d p) :
    (squareResidual p).comp (X ^ 2) = 1 - p ^ 2 :=
  comp_square_contract_of_even (residual_even hp)

theorem squareResidual_eq_of_comp {p h : Polynomial ℝ} {d : ℕ}
    (hp : HasRealParity d p) (hh : h.comp (X ^ 2) = 1 - p ^ 2) :
    squareResidual p = h := by
  apply expand_injective (R := ℝ) (n := 2) (by decide)
  change (squareResidual p).comp (X ^ 2) = h.comp (X ^ 2)
  rw [squareResidual_comp hp, hh]

theorem contract_two_degree_le {f : Polynomial ℝ} {d : ℕ}
    (hf : f.degree ≤ ((2 * d : ℕ) : WithBot ℕ)) :
    (contract 2 f).degree ≤ (d : WithBot ℕ) := by
  apply (degree_le_iff_coeff_zero _ _).mpr
  intro k hk
  rw [coeff_contract (by decide : 2 ≠ 0)]
  apply (degree_le_iff_coeff_zero _ _).mp hf
  have hkd : d < k := by exact_mod_cast hk
  exact_mod_cast (show 2 * d < k * 2 by omega)

theorem squareResidual_degree_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p.degree ≤ (d : WithBot ℕ)) :
    (squareResidual p).degree ≤ (d : WithBot ℕ) := by
  apply contract_two_degree_le
  apply degree_le_of_natDegree_le
  have hpd := natDegree_le_of_degree_le hp
  have hsq : (p ^ 2).natDegree ≤ 2 * d := by
    rw [natDegree_pow]
    omega
  exact (natDegree_sub_le _ _).trans (max_le (by simp) hsq)

theorem squareResidual_pos {p : Polynomial ℝ} {d : ℕ}
    (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| < 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (squareResidual p).eval t := by
  intro t ht
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).mpr ht.2
  have hs := hb (Real.sqrt t) ⟨by linarith, hs1⟩
  have he := congrArg (Polynomial.eval (Real.sqrt t)) (squareResidual_comp hp)
  simp only [eval_comp, eval_pow, eval_X, Real.sq_sqrt ht.1, eval_sub, eval_one] at he
  rw [he]
  rcases abs_lt.mp hs with ⟨hlo, hhi⟩
  nlinarith

private theorem comp_square_degree_le {f : Polynomial ℝ} {m : ℕ}
    (hf : f.degree ≤ (m : WithBot ℕ)) :
    (f.comp (X ^ 2)).degree ≤ ((2 * m : ℕ) : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  rw [← expand_eq_comp_X_pow, natDegree_expand]
  have hd := natDegree_le_of_degree_le hf
  omega

private theorem X_comp_square_degree_le {f : Polynomial ℝ} {m : ℕ}
    (hf : f.degree ≤ (m : WithBot ℕ)) :
    (X * f.comp (X ^ 2)).degree ≤ ((2 * m + 1 : ℕ) : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := f.comp (X ^ 2))
  have hsq := natDegree_le_of_degree_le (comp_square_degree_le hf)
  rw [natDegree_X] at h
  omega

private theorem X_comp_square_degree_lt {f : Polynomial ℝ} {m : ℕ}
    (hf : f.degree < (m : WithBot ℕ)) :
    (X * f.comp (X ^ 2)).degree < ((2 * m : ℕ) : WithBot ℕ) := by
  by_cases hz : f = 0
  · simp only [hz, zero_comp, mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  have hfd : f.natDegree < m := by
    rw [degree_eq_natDegree hz] at hf
    exact_mod_cast hf
  apply lt_of_le_of_lt (degree_le_natDegree (p := X * f.comp (X ^ 2)))
  have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := f.comp (X ^ 2))
  have hsq : (f.comp (X ^ 2)).natDegree = f.natDegree * 2 :=
    natDegree_expand 2 f
  rw [natDegree_X, hsq] at h
  exact_mod_cast (show (X * f.comp (X ^ 2)).natDegree < 2 * m by omega)

private theorem comp_square_parity (f : Polynomial ℝ) (m : ℕ) :
    HasRealParity (2 * m) (f.comp (X ^ 2)) := by
  simp [HasRealParity, comp_assoc, pow_comp, pow_mul]

private theorem X_comp_square_parity (f : Polynomial ℝ) (m : ℕ) :
    HasRealParity (2 * m + 1) (X * f.comp (X ^ 2)) := by
  simp [HasRealParity, mul_comp, comp_assoc, pow_comp, pow_add, pow_mul]

theorem exists_real_sos_of_rep {p : Polynomial ℝ} {d : ℕ}
    (hp : HasRealParity d p) (rep : Representation d (squareResidual p)) :
    ∃ A B : Polynomial ℝ,
      1 - p ^ 2 = A ^ 2 + (1 - X ^ 2) * B ^ 2 ∧
      A.degree ≤ (d : WithBot ℕ) ∧ B.degree < (d : WithBot ℕ) ∧
      HasRealParity d A ∧ HasRealParity (d + 1) B := by
  by_cases he : d % 2 = 0
  · let r : EvenRep (d / 2) (squareResidual p) := by
      simpa only [Qatlib.Concepts.QsvtCore.PolyApprox.Representation, if_pos he] using rep
    have hd : d = 2 * (d / 2) := by omega
    refine ⟨r.a.comp (X ^ 2), X * r.b.comp (X ^ 2), ?_, ?_, ?_, ?_, ?_⟩
    · have hi := congrArg (fun f : Polynomial ℝ => f.comp (X ^ 2)) r.identity
      simp only [add_comp, mul_comp, pow_comp, X_comp, sub_comp, one_comp,
        squareResidual_comp hp] at hi
      rw [hi]
      ring
    · have hh := comp_square_degree_le r.degreeA
      rwa [← hd] at hh
    · have hh := X_comp_square_degree_lt r.degreeB
      rwa [← hd] at hh
    · convert comp_square_parity r.a (d / 2) using 1
    · convert X_comp_square_parity r.b (d / 2) using 1
      omega
  · let r : OddRep (d / 2) (squareResidual p) := by
      simpa only [Qatlib.Concepts.QsvtCore.PolyApprox.Representation, if_neg he] using rep
    have hd : d = 2 * (d / 2) + 1 := by omega
    refine ⟨X * r.a.comp (X ^ 2), r.b.comp (X ^ 2), ?_, ?_, ?_, ?_, ?_⟩
    · have hi := congrArg (fun f : Polynomial ℝ => f.comp (X ^ 2)) r.identity
      simp only [add_comp, mul_comp, pow_comp, X_comp, sub_comp, one_comp,
        squareResidual_comp hp] at hi
      rw [hi]
      ring
    · have hh := X_comp_square_degree_le r.degreeA
      rwa [← hd] at hh
    · exact lt_of_le_of_lt (comp_square_degree_le r.degreeB)
        (by exact_mod_cast (by omega : 2 * (d / 2) < d))
    · convert X_comp_square_parity r.a (d / 2) using 1
    · convert comp_square_parity r.b (d / 2 + 1) using 1
      omega

open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

noncomputable def completionP (p A : Polynomial ℝ) : Polynomial ℂ :=
  p.map Complex.ofRealHom + C Complex.I * A.map Complex.ofRealHom

@[simp] theorem conjugate_real_map (p : Polynomial ℝ) :
    conjugatePolynomial (p.map Complex.ofRealHom) = p.map Complex.ofRealHom := by
  ext k
  simp

theorem HasRealParity.map {d : ℕ} {p : Polynomial ℝ} (hp : HasRealParity d p) :
    HasResponseParity d (p.map Complex.ofRealHom) := by
  have h := congrArg (Polynomial.map Complex.ofRealHom) hp
  simpa [HasResponseParity, Polynomial.map_comp] using h

theorem completionP_real_part (p A : Polynomial ℝ) :
    completionP p A + conjugatePolynomial (completionP p A) =
      C (2 : ℂ) * p.map Complex.ofRealHom := by
  simp only [completionP, conjugatePolynomial_add, conjugatePolynomial_mul,
    conjugatePolynomial_C, conjugate_real_map]
  simp only [Complex.star_def, Complex.conj_I, map_neg, map_ofNat]
  ring

theorem completionP_eval_re (p A : Polynomial ℝ) (x : ℝ) :
    ((completionP p A).eval (x : ℂ)).re = p.eval x := by
  have hp : (p.map Complex.ofRealHom).eval (x : ℂ) = Complex.ofReal (p.eval x) :=
    Polynomial.eval_map_apply (p := p) Complex.ofRealHom x
  have hA : (A.map Complex.ofRealHom).eval (x : ℂ) = Complex.ofReal (A.eval x) :=
    Polynomial.eval_map_apply (p := A) Complex.ofRealHom x
  simp [completionP, hp, hA, Complex.mul_re]

theorem completedPair_of_real_sos {p A B : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hi : 1 - p ^ 2 = A ^ 2 + (1 - X ^ 2) * B ^ 2)
    (hA : A.degree ≤ (d : WithBot ℕ)) (hB : B.degree < (d : WithBot ℕ))
    (hAp : HasRealParity d A) (hBp : HasRealParity (d + 1) B) :
    CompletedPair d (completionP p A) (B.map Complex.ofRealHom) := by
  refine ⟨?_, degree_map_le.trans_lt hB, ?_, hBp.map, ?_⟩
  · apply degree_le_of_natDegree_le
    apply (natDegree_add_le _ _).trans
    exact max_le (natDegree_map_le.trans (natDegree_le_of_degree_le hpdeg))
      ((natDegree_C_mul_le _ _).trans
        (natDegree_map_le.trans (natDegree_le_of_degree_le hA)))
  · have hp' := hp.map
    have hA' := hAp.map
    simp only [HasResponseParity] at hp' hA' ⊢
    simp only [completionP, add_comp, mul_comp, C_comp, hp', hA']
    ring
  · have hi' := congrArg (Polynomial.map Complex.ofRealHom) hi
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X] at hi'
    have hi2 : (C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
      rw [← C_pow, Complex.I_sq]
      simp
    simp only [responsePairNorm, completionP, conjugatePolynomial_add,
      conjugatePolynomial_mul, conjugatePolynomial_C, conjugate_real_map,
      Complex.star_def, Complex.conj_I, map_neg]
    calc
      _ = (p.map Complex.ofRealHom) ^ 2 - (C Complex.I) ^ 2 *
          (A.map Complex.ofRealHom) ^ 2 +
          (1 - X ^ 2) * (B.map Complex.ofRealHom) ^ 2 := by ring
      _ = (p.map Complex.ofRealHom) ^ 2 +
          ((A.map Complex.ofRealHom) ^ 2 +
          (1 - X ^ 2) * (B.map Complex.ofRealHom) ^ 2) := by rw [hi2]; ring
      _ = 1 := by rw [← hi']; ring

theorem exists_completedPair_of_rep {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (rep : Representation d (squareResidual p)) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = p.eval x := by
  obtain ⟨A, B, hi, hA, hB, hAp, hBp⟩ := exists_real_sos_of_rep hp rep
  exact ⟨completionP p A, B.map Complex.ofRealHom,
    completedPair_of_real_sos hpdeg hp hi hA hB hAp hBp,
    completionP_real_part p A, completionP_eval_re p A⟩

theorem exists_phases_of_rep {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (rep : Representation d (squareResidual p)) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = d ∧ ∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x := by
  obtain ⟨P, Q, hpair, _, hre⟩ := exists_completedPair_of_rep hpdeg hp rep
  obtain ⟨base, zs, hb, hzs, hn, hP, _⟩ := exists_response_of_completedPair hpair
  exact ⟨base, zs, hb, hzs, hn, by simpa only [hP] using hre⟩

theorem exists_completedPair_of_strict {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| < 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = p.eval x := by
  obtain ⟨rep⟩ := Qatlib.Concepts.QsvtCore.PolyApprox.exists_rep_of_pos (squareResidual p)
    (squareResidual_pos hp hb) (squareResidual_degree_le hpdeg)
  exact exists_completedPair_of_rep hpdeg hp rep

theorem exists_phases_of_strict {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| < 1) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = d ∧
      responseP base zs + conjugatePolynomial (responseP base zs) =
        C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x := by
  obtain ⟨P, Q, hpair, hpoly, hre⟩ := exists_completedPair_of_strict hpdeg hp hb
  obtain ⟨base, zs, hbase, hzs, hn, hP, _⟩ := exists_response_of_completedPair hpair
  exact ⟨base, zs, hbase, hzs, hn, by simpa only [hP] using hpoly,
    by simpa only [hP] using hre⟩

noncomputable def halfTarget (p : Polynomial ℝ) : Polynomial ℝ := C (1 / 2) * p

theorem halfTarget_degree_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p.degree ≤ (d : WithBot ℕ)) :
    (halfTarget p).degree ≤ (d : WithBot ℕ) := by
  exact degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans
    (natDegree_le_of_degree_le hp))

theorem halfTarget_parity {p : Polynomial ℝ} {d : ℕ} (hp : HasRealParity d p) :
    HasRealParity d (halfTarget p) := by
  change p.comp (-X) = C ((-1 : ℝ) ^ d) * p at hp
  simp only [HasRealParity, halfTarget, mul_comp, C_comp, hp]
  ring

theorem halfTarget_strict {p : Polynomial ℝ}
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(halfTarget p).eval x| < 1 := by
  intro x hx
  have hh := hb x hx
  simp only [halfTarget, eval_mul, eval_C, abs_mul]
  norm_num
  linarith

theorem halfTarget_normalization (p : Polynomial ℝ) (x : ℝ) :
    2 * (halfTarget p).eval x = p.eval x := by
  simp only [halfTarget, eval_mul, eval_C]
  ring

private theorem halfTarget_map_twice (p : Polynomial ℝ) :
    C (2 : ℂ) * (halfTarget p).map Complex.ofRealHom = p.map Complex.ofRealHom := by
  have h : C (2 : ℝ) * halfTarget p = p := by
    rw [halfTarget, ← mul_assoc, ← C_mul]
    norm_num
  have hc := congrArg (Polynomial.map Complex.ofRealHom) h
  simpa only [Polynomial.map_mul, Polynomial.map_C, map_ofNat,
    Polynomial.map_ofNat] using hc

theorem exists_completedPair_half_of_bounded {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      P + conjugatePolynomial P = p.map Complex.ofRealHom ∧
      ∀ x : ℝ, 2 * (P.eval (x : ℂ)).re = p.eval x := by
  obtain ⟨P, Q, hpair, hpoly, hre⟩ := exists_completedPair_of_strict
    (halfTarget_degree_le hpdeg) (halfTarget_parity hp) (halfTarget_strict hb)
  refine ⟨P, Q, hpair, ?_, ?_⟩
  · simpa only [halfTarget_map_twice] using hpoly
  · intro x
    rw [hre]
    exact halfTarget_normalization p x

theorem exists_phases_half_of_bounded {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = d ∧
      responseP base zs + conjugatePolynomial (responseP base zs) =
        p.map Complex.ofRealHom ∧
      ∀ x : ℝ, 2 * ((responseP base zs).eval (x : ℂ)).re = p.eval x := by
  obtain ⟨P, Q, hpair, hpoly, hre⟩ := exists_completedPair_half_of_bounded hpdeg hp hb
  obtain ⟨base, zs, hbase, hzs, hn, hP, _⟩ := exists_response_of_completedPair hpair
  exact ⟨base, zs, hbase, hzs, hn, by simpa only [hP] using hpoly,
    by simpa only [hP] using hre⟩

section NormalizationLedger
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

theorem blockEncoding_two_of_half_target
    {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℝ) • A) U L R) :
    BlockEncoding A U L R 2 0 := by
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, by norm_num, le_rfl, ?_⟩
  rw [h.encoded, smul_smul]
  norm_num

end NormalizationLedger

end Qatlib.Concepts.QspSimulation.Achievability
