/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree

/-!
# Certificates and block sensitivity for monotone functions

For a monotone Boolean function, a certificate at a true input can be reduced to coordinates
whose input values are true. The finite-set indicator lemmas support the proof that
`oneCertificateComplexity` is bounded by `blockSensitivity`.

The mathematical background is developed in [BealsEtAl2001].

## Main statements

* `qc_cert_filter_ones`: removes false coordinates from a certificate at a true input.
* `monotone_oneCertificate_le_blockSensitivity`: bounds one-certificate complexity by block
  sensitivity.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib
open Qatlib
open scoped Classical

/-- The Boolean characteristic function of a finite set of input coordinates. -/
private def qcIndicate {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool :=
  fun i => decide (i ∈ S)

/-- The indicator of `S` is true at `i` exactly when `i` belongs to `S`. -/
private theorem qcIndicate_eq_true {N : ℕ} {S : Finset (Fin N)} {i : Fin N} :
    qcIndicate S i = true ↔ i ∈ S := by
  simp [qcIndicate]

/-- Flipping a singleton coordinate present in a finite-set indicator gives the indicator of the
set with that coordinate erased. -/
private theorem qcIndicate_erase {N : ℕ} (S : Finset (Fin N)) {i : Fin N} (hi : i ∈ S) :
    flipBlock (qcIndicate S) {i} = qcIndicate (S.erase i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipBlock, qcIndicate, hi]
  · by_cases hjS : j ∈ S
    · have hjE : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hj, hjS⟩
      simp [flipBlock, qcIndicate, hj, hjS, hjE]
    · have hjE : j ∉ S.erase i := fun h => hjS (Finset.mem_of_mem_erase h)
      simp [flipBlock, qcIndicate, hj, hjS, hjE]

/-- For a monotone Boolean function at a true input, retaining only the true coordinates of a
certificate still gives a certificate. -/
private theorem qc_cert_filter_ones {N : ℕ} {f : (Fin N → Bool) → Bool}
    (hmono : ∀ x y : Fin N → Bool, (∀ i : Fin N, x i = true → y i = true) →
        f x = true → f y = true)
    {x : Fin N → Bool} (hx : f x = true) {S : Finset (Fin N)}
    (hS : IsCertificateFor f x S) :
    IsCertificateFor f x (S.filter fun i => x i = true) := by
  intro y hy
  have hz : ∃ z : Fin N → Bool, (∀ j ∈ S, z j = x j) ∧
      (∀ j : Fin N, z j = true → y j = true) := by
    refine ⟨fun j => if j ∈ S ∧ x j = false then false else y j, ?_, ?_⟩
    · intro j hj
      by_cases hxj : x j = false
      · simp [hj, hxj]
      · have hnot : ¬ (j ∈ S ∧ x j = false) := fun h => hxj h.2
        have hyj : y j = x j := by
          refine hy j (Finset.mem_filter.mpr ⟨hj, ?_⟩)
          cases h : x j <;> simp_all
        simp [hnot, hyj]
    · intro j hj
      by_cases hcond : j ∈ S ∧ x j = false
      · simp [hcond] at hj
      · simp [hcond] at hj
        exact hj
  obtain ⟨z, hzS, hzle⟩ := hz
  have hzf : f z = true := by
    rw [hS z hzS, hx]
  have hfy := hmono z y hzle hzf
  rw [hfy, hx]

/-- The one-certificate complexity of a monotone Boolean function is at most its block
sensitivity. -/
theorem monotone_oneCertificate_le_blockSensitivity {N : ℕ} {f : (Fin N → Bool) → Bool}
    (hmono : ∀ x y : Fin N → Bool, (∀ i : Fin N, x i = true → y i = true) →
        f x = true → f y = true) :
    oneCertificateComplexity f ≤ blockSensitivity f := by
  unfold oneCertificateComplexity
  refine Finset.sup_le ?_
  intro b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  have hx1 : f x = true := (Finset.mem_filter.mp hx).2
  obtain ⟨S, hS, hScard⟩ := certificate_minimum f x
  set T : Finset (Fin N) := S.filter (fun i => x i = true) with hTdef
  have hT : IsCertificateFor f x T := by
    rw [hTdef]
    exact qc_cert_filter_ones hmono hx1 hS
  have hTon : ∀ i ∈ T, x i = true := by
    intro i hi
    rw [hTdef] at hi
    exact (Finset.mem_filter.mp hi).2
  have hTcard : T.card = certificateSizeAt f x := by
    have h1 : certificateSizeAt f x ≤ T.card := certificateSizeAt_le hT
    have h2 : T.card ≤ S.card := by
      rw [hTdef]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have hxf : f (qcIndicate T) = true := by
    have hagree : ∀ i ∈ T, qcIndicate T i = x i := by
      intro i hi
      rw [qcIndicate_eq_true.mpr hi, hTon i hi]
    rw [hT (qcIndicate T) hagree, hx1]
  have hflip : ∀ i ∈ T, f (flipBlock (qcIndicate T) {i}) = false := by
    intro i hi
    have hE : f (qcIndicate (T.erase i)) = false := by
      by_contra hnot
      have hne : f (qcIndicate (T.erase i)) = true := by
        cases h : f (qcIndicate (T.erase i)) <;> simp_all
      have herase : IsCertificateFor f x (T.erase i) := by
        intro y hy
        have hle : ∀ j : Fin N, qcIndicate (T.erase i) j = true → y j = true := by
          intro j hj
          have hjE : j ∈ T.erase i := qcIndicate_eq_true.mp hj
          have hyj : y j = x j := hy j hjE
          rw [hyj]
          exact hTon j (Finset.mem_of_mem_erase hjE)
        have hfy : f y = true := hmono (qcIndicate (T.erase i)) y hle hne
        rw [hfy, hx1]
      have hlt : (T.erase i).card < T.card := Finset.card_erase_lt_of_mem hi
      have hle2 : certificateSizeAt f x ≤ (T.erase i).card := certificateSizeAt_le herase
      omega
    rw [qcIndicate_erase T hi, hE]
  have hF : SensitiveFamily f (qcIndicate T) (T.image fun i => ({i} : Finset (Fin N))) := by
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      show f (qcIndicate T) ≠ f (flipBlock (qcIndicate T) {i})
      rw [hxf, hflip i hi]
      simp
    · intro B hB C hC hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hC
      have hij : i ≠ j := fun h => hne (h ▸ rfl)
      simp [hij]
  have hcard : (T.image fun i => ({i} : Finset (Fin N))).card = T.card :=
    Finset.card_image_iff.mpr (by
      intro i _ j _ h
      simpa using h)
  calc
    certificateSizeAt f x = T.card := hTcard.symm
    _ = (T.image fun i => ({i} : Finset (Fin N))).card := hcard.symm
    _ ≤ blockSensitivity f := sensitiveFamily_card_le f (qcIndicate T)
        (T.image fun i => ({i} : Finset (Fin N))) hF

end Qatlib.Concepts.QueryComplexity.DegreeMethod
