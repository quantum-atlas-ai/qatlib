/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacsNonnegative
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial

/-!
# Parity-preserving sums of squares on the unit interval

`even_interval_sos_with_source_parities` decomposes an even real polynomial nonnegative on `[-1,
1]` as `b^2 + (1 - X^2) * c^2`. The construction transfers a Markov–Lukács representation
through the substitution `X^2`, retaining the degree bounds and alternating parities required
for signal-processing completion. See [GilyenSuLowWiebe2019].

## Main statements

* `sos_of_rep`: transfer a representation of the contracted polynomial.
* `even_interval_sos_with_source_parities`: obtain the interval decomposition with prescribed
  parities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.PolyApprox
open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib

/-- Substituting `X^2` into a polynomial of degree at most `m` gives degree at most `2 * m`. -/
private theorem comp_square_degree_le {f : Polynomial ℝ} {m : ℕ}
    (hf : f.degree ≤ (m : WithBot ℕ)) :
    (f.comp (X ^ 2)).degree ≤ ((2 * m : ℕ) : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  rw [← expand_eq_comp_X_pow, natDegree_expand]
  have hd := natDegree_le_of_degree_le hf
  omega

/-- Multiplying a polynomial composed with `X^2` by `X` gives degree at most `2 * m + 1` when
the original degree is at most `m`. -/
private theorem X_comp_square_degree_le {f : Polynomial ℝ} {m : ℕ}
    (hf : f.degree ≤ (m : WithBot ℕ)) :
    (X * f.comp (X ^ 2)).degree ≤ ((2 * m + 1 : ℕ) : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := f.comp (X ^ 2))
  have hsq := natDegree_le_of_degree_le (comp_square_degree_le hf)
  rw [natDegree_X] at h
  omega

/-- If the original polynomial has degree less than `m`, multiplying its composition with `X^2`
by `X` gives degree less than `2 * m`. -/
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

/-- Composition with `X^2` has real parity `2 * m` for every natural `m`. -/
private theorem comp_square_parity (f : Polynomial ℝ) (m : ℕ) :
    HasRealParity (2 * m) (f.comp (X ^ 2)) := by
  simp [HasRealParity, comp_assoc, pow_comp, pow_mul]

/-- Multiplying a polynomial composed with `X^2` by `X` gives real parity `2 * m + 1`. -/
private theorem X_comp_square_parity (f : Polynomial ℝ) (m : ℕ) :
    HasRealParity (2 * m + 1) (X * f.comp (X ^ 2)) := by
  simp [HasRealParity, mul_comp, comp_assoc, pow_comp, pow_add, pow_mul]

/-- A degree-indexed representation of `contract 2 a` yields a decomposition `a = b^2 + (1 -
X^2) * c^2` with the prescribed degree bounds and alternating parities when composition with
`X^2` recovers `a`. -/
private theorem sos_of_rep (a : Polynomial ℝ) (k : ℕ)
    (haComp : (contract 2 a).comp (X ^ 2) = a)
    (rep : Representation k (contract 2 a)) :
    ∃ b c : Polynomial ℝ, a = b ^ 2 + (1 - X ^ 2) * c ^ 2 ∧
      b.degree ≤ (k : WithBot ℕ) ∧ c.degree < (k : WithBot ℕ) ∧
      HasRealParity k b ∧ HasRealParity (k + 1) c := by
  by_cases he : k % 2 = 0
  · let r : EvenRep (k / 2) (contract 2 a) := by
      simpa only [Qatlib.Concepts.QsvtCore.PolyApprox.Representation, if_pos he] using rep
    have hd : k = 2 * (k / 2) := by omega
    refine ⟨r.a.comp (X ^ 2), X * r.b.comp (X ^ 2), ?_, ?_, ?_, ?_, ?_⟩
    · have hi := congrArg (fun f : Polynomial ℝ => f.comp (X ^ 2)) r.identity
      simp only [add_comp, mul_comp, pow_comp, X_comp, sub_comp, one_comp,
        haComp] at hi
      exact hi.trans (by ring)
    · have hh := comp_square_degree_le r.degreeA
      rwa [← hd] at hh
    · have hh := X_comp_square_degree_lt r.degreeB
      rwa [← hd] at hh
    · convert comp_square_parity r.a (k / 2) using 1
    · convert X_comp_square_parity r.b (k / 2) using 1
      omega
  · let r : OddRep (k / 2) (contract 2 a) := by
      simpa only [Qatlib.Concepts.QsvtCore.PolyApprox.Representation, if_neg he] using rep
    have hd : k = 2 * (k / 2) + 1 := by omega
    refine ⟨X * r.a.comp (X ^ 2), r.b.comp (X ^ 2), ?_, ?_, ?_, ?_, ?_⟩
    · have hi := congrArg (fun f : Polynomial ℝ => f.comp (X ^ 2)) r.identity
      simp only [add_comp, mul_comp, pow_comp, X_comp, sub_comp, one_comp,
        haComp] at hi
      exact hi.trans (by ring)
    · have hh := X_comp_square_degree_le r.degreeA
      rwa [← hd] at hh
    · exact lt_of_le_of_lt (comp_square_degree_le r.degreeB)
        (by exact_mod_cast (by omega : 2 * (k / 2) < k))
    · convert X_comp_square_parity r.a (k / 2) using 1
    · convert comp_square_parity r.b (k / 2 + 1) using 1
      omega

/-- An even polynomial of degree at most `2 * k` nonnegative on `[-1, 1]` has a decomposition
`b^2 + (1 - X^2) * c^2` with the stated degree bounds and parities, as in [Gilyén et al.,
Lemma 6][GilyenSuLowWiebe2019]. -/
theorem even_interval_sos_with_source_parities : ∀ (a : Polynomial ℝ) (k : ℕ),
  HasRealParity 0 a → a.degree ≤ (2*k : WithBot ℕ) →
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ a.eval x) →
  ∃ b c : Polynomial ℝ, a = b^2 + (1-X^2)*c^2 ∧
    b.degree ≤ (k : WithBot ℕ) ∧ (c=0 ∨ c.degree+1 ≤ (k : WithBot ℕ)) ∧
    HasRealParity k b ∧ HasRealParity (k+1) c := by
  intro a k ha hd hn
  have haEven : a.comp (-X) = a := by simpa [HasRealParity] using ha
  have haComp := comp_square_contract_of_even haEven
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (contract 2 a).eval t := by
    intro t ht
    have hs := hn (Real.sqrt t)
      ⟨by linarith [Real.sqrt_nonneg t], Real.sqrt_le_one.mpr ht.2⟩
    have he := congrArg (Polynomial.eval (Real.sqrt t)) haComp
    simp only [eval_comp, eval_pow, eval_X, Real.sq_sqrt ht.1] at he
    rwa [he]
  have hd' : a.degree ≤ ((2*k : ℕ) : WithBot ℕ) := by simpa using hd
  obtain ⟨rep⟩ := exists_rep_of_nonneg (contract 2 a) hf (contract_two_degree_le hd')
  obtain ⟨b,c,hi,hb,hc,hbp,hcp⟩ := sos_of_rep a k haComp rep
  refine ⟨b,c,hi,hb,?_,hbp,hcp⟩
  by_cases hz : c = 0
  · exact Or.inl hz
  · right
    rw [degree_eq_natDegree hz] at hc ⊢
    exact_mod_cast (show c.natDegree + 1 ≤ k by exact Nat.succ_le_of_lt (by exact_mod_cast hc))

end Qatlib.Concepts.QsvtCore.PolyApprox
