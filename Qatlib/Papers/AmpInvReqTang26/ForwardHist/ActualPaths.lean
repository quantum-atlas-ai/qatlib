/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPolynomial
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
set_option warningAsError false

def pathSupport {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : Finset (Fin d →₀ ℕ) := by
  classical
  exact Finset.univ.biUnion (fun x => (queryPolynomial Alg n x).support)

theorem pathSupport_member {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (h : pathSupport Alg n) : ∃ x, h.val ∈ (queryPolynomial Alg n x).support := by
  classical
  simpa only [pathSupport,Finset.mem_biUnion,Finset.mem_univ,true_and] using! h.property

def pathHistogram {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n q : ℕ) (hn : n<q)
    (h : pathSupport Alg n) : Fin d → Fin q := fun i => ⟨h.val i,by
  obtain ⟨x,hx⟩ := pathSupport_member Alg n h
  exact queryPolynomial_support_lt Alg n q hn x h.val hx i⟩

theorem pathHistogram_injective {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) : Function.Injective (pathHistogram Alg n q hn) := by
  intro h k heq
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun heq i)

theorem pathHistogram_mass {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) (h : pathSupport Alg n) :
    ∑i,(pathHistogram Alg n q hn h i:ℕ)=n := by
  obtain ⟨x,hx⟩ := pathSupport_member Alg n h
  have hd := (queryPolynomial_homogeneous Alg n x).degree_eq_sum_deg_support hx
  have hf := Finsupp.sum_fintype h.val (fun (_ : Fin d) (v : ℕ) => v) (by intro i; rfl)
  change ∑i,h.val i=n
  exact hf.symm.trans hd.symm

def pathCoefficient {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    Matrix (Fin d × Fin a) (pathSupport Alg n) ℂ := fun x h =>
  (queryPolynomial Alg n x).coeff h.val

theorem actual_path_expansion {d a : ℕ} {S : Type} (phi : S → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n q : ℕ) (hn : n<q)
    (U : Fin d → S) (x : Fin d × Fin a) :
    run phi Alg n U x = ∑ h : pathSupport Alg n,
      pathCoefficient Alg n x h * ∏i, phi (U i) ^ (pathHistogram Alg n q hn h i:ℕ) := by
  classical
  rw [← queryPolynomial_eval phi Alg n U x,MvPolynomial.eval_eq']
  change (∑h ∈ (queryPolynomial Alg n x).support,
      (queryPolynomial Alg n x).coeff h * ∏i, phi (U i)^h i) =
    ∑h : pathSupport Alg n,(queryPolynomial Alg n x).coeff h.val * ∏i,phi (U i)^h.val i
  rw [Finset.sum_coe_sort (pathSupport Alg n) (fun h => (queryPolynomial Alg n x).coeff h * ∏i,phi (U i)^h i)]
  apply Finset.sum_subset
  · intro h hh
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hh⟩
  · intro h _ hh
    simp only [MvPolynomial.mem_support_iff,not_not] at hh
    rw [hh,zero_mul]

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
