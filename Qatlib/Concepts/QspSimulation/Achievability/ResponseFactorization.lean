/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib

noncomputable def responseFactors (base : ℂ) : List ℂ → Polynomial ℂ × Polynomial ℂ
  | [] => (C base, 0)
  | z :: zs =>
    let pq := responseFactors base zs
    if zs.length % 2 = 0 then
      (C z * (pq.1 + (1 - X) * pq.2),
        C (star z) * (pq.1 - X * pq.2))
    else
      (C z * (X * pq.1 + (1 - X) * pq.2),
        C (star z) * (pq.1 - pq.2))

theorem response_factorization (base : ℂ) (zs : List ℂ) :
    if zs.length % 2 = 0 then
      responseP base zs = evenSingularPolynomial (responseFactors base zs).1 ∧
      responseQ base zs = oddSingularPolynomial (responseFactors base zs).2
    else
      responseP base zs = oddSingularPolynomial (responseFactors base zs).1 ∧
      responseQ base zs = evenSingularPolynomial (responseFactors base zs).2 := by
  induction zs with
  | nil => simp [responseFactors, evenSingularPolynomial, oddSingularPolynomial]
  | cons z zs ih =>
    by_cases heven : zs.length % 2 = 0
    · have hnew : (z :: zs).length % 2 ≠ 0 := by
        simp only [List.length_cons]
        omega
      rw [if_pos heven] at ih
      rw [if_neg hnew]
      simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
      simp only [responseFactors, if_pos heven]
      simp only [evenSingularPolynomial, oddSingularPolynomial,
        Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp,
        Polynomial.C_comp, Polynomial.X_comp, Polynomial.one_comp]
      constructor <;> ring
    · have hnew : (z :: zs).length % 2 = 0 := by
        simp only [List.length_cons]
        omega
      rw [if_neg heven] at ih
      rw [if_pos hnew]
      simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
      simp only [responseFactors, if_neg heven]
      simp only [evenSingularPolynomial, oddSingularPolynomial,
        Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp,
        Polynomial.C_comp, Polynomial.X_comp, Polynomial.one_comp]
      constructor <;> ring

theorem responseP_factor_even (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    responseP base zs = evenSingularPolynomial (responseFactors base zs).1 := by
  have h := response_factorization base zs
  rw [if_pos heven] at h
  exact h.1

theorem responseP_factor_odd (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    responseP base zs = oddSingularPolynomial (responseFactors base zs).1 := by
  have h := response_factorization base zs
  rw [if_neg (by omega : zs.length % 2 ≠ 0)] at h
  exact h.1

theorem responseQ_factor_even (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    responseQ base zs = oddSingularPolynomial (responseFactors base zs).2 := by
  have h := response_factorization base zs
  rw [if_pos heven] at h
  exact h.2

theorem responseQ_factor_odd (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    responseQ base zs = evenSingularPolynomial (responseFactors base zs).2 := by
  have h := response_factorization base zs
  rw [if_neg (by omega : zs.length % 2 ≠ 0)] at h
  exact h.2

section WholeMatrix

variable {H I O : Type*}
  [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

theorem qsvt_odd_eq_responseFactor {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
      A * aeval (Aᴴ * A) (responseFactors base zs).1 := by
  exact qsvt_odd_eq_singularPolynomial h base zs (responseFactors base zs).1
    (responseP_factor_odd base zs hodd) hodd

theorem qsvt_even_left_eq_responseFactor {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L =
      aeval (A * Aᴴ) (responseFactors base zs).1 := by
  exact qsvt_even_left_eq_singularPolynomial h base zs (responseFactors base zs).1
    (responseP_factor_even base zs heven) heven

theorem qsvt_even_right_eq_responseFactor {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R =
      aeval (Aᴴ * A) (responseFactors base zs).1 := by
  exact qsvt_even_right_eq_singularPolynomial h base zs (responseFactors base zs).1
    (responseP_factor_even base zs heven) heven

end WholeMatrix

theorem responseFactors_nil (base : ℂ) : responseFactors base [] = (C base, 0) := rfl

theorem responseFactors_singleton (base z : ℂ) :
    responseFactors base [z] = (C z * C base, C (star z) * C base) := by
  simp [responseFactors]

theorem responseFactors_pair (base z w : ℂ) :
    responseFactors base [z, w] =
      (C z * (X * (C w * C base) + (1 - X) * (C (star w) * C base)),
        C (star z) * (C w * C base - C (star w) * C base)) := by
  simp [responseFactors]

end Qatlib.Concepts.QspSimulation.Achievability
