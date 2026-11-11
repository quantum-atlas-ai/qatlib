/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RationalScan.Step2Scan.RationalStep2ScanDefs
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithms
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmRefutations

/-!
# Correctness of the rational Step 2 scan

This module proves that `run` scans rational candidate tables in row-major order and returns the
first accepted pair, with an exact visited count and resource ledger. It transfers the rational
acceptance test to real inequalities and proves width and separation bounds for the same
returned candidate, in the SDP setting of [BrandaoSvore2017].

## Main statements

* `run_first_accepted`: first-success semantics, failure characterization, and visited-resource
  formulas.
* `run_candidate_sound`: real acceptance, sampled-width control, and a separation lower bound
  for a returned pair.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.RationalScan.Step2Scan

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RationalScan.Step2Scan
set_option autoImplicit false
open Matrix Qatlib.Concepts.RationalScan.Step2Scan
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

/-- Scanning a duplicate-free candidate list visits at most its length and returns no choice
exactly when every test fails. A returned candidate is the first accepted entry, with
visited count equal to its zero-based index plus one. -/
private theorem scan_spec {m γ Nmax M : ℕ} (d : Input m γ Nmax M)
    (xs : List (Fin γ × Fin Nmax)) (hn : xs.Nodup) :
    (scan d xs).visited ≤ xs.length ∧
    ((scan d xs).choice = none ↔ ∀ p ∈ xs, accepts d p = false) ∧
    ((scan d xs).choice = none → (scan d xs).visited = xs.length) ∧
    (∀ p, (scan d xs).choice = some p → p ∈ xs ∧ accepts d p = true ∧
      (scan d xs).visited = xs.idxOf p+1 ∧
      ∀ q ∈ xs, xs.idxOf q < xs.idxOf p → accepts d q = false) := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    have hnot : a ∉ xs := (List.nodup_cons.mp hn).1
    have hnd : xs.Nodup := (List.nodup_cons.mp hn).2
    obtain ⟨hbound,hnone,hlen,hsome⟩ := ih hnd
    cases ha : accepts d a with
    | true =>
      simp only [scan,ha,ite_true]
      refine ⟨by simp, ?_, by simp, ?_⟩
      · constructor
        · intro h; cases h
        · intro h
          have hh := h a (by simp)
          simp [ha] at hh
      · intro p hp
        have heq : a=p := Option.some.inj hp
        subst p
        refine ⟨by simp,ha,by simp,?_⟩
        intro q _ hq
        simp at hq
    | false =>
      simp only [scan,ha,Bool.false_eq_true,ite_false]
      refine ⟨by simpa using! Nat.succ_le_succ hbound, ?_, ?_, ?_⟩
      · rw [hnone]
        constructor
        · intro h p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ha
          · exact h p hp
        · intro h p hp
          exact h p (List.mem_cons_of_mem a hp)
      · intro h
        simp [hlen h]
      · intro p hp
        obtain ⟨hpm,hpa,hpv,hfirst⟩ := hsome p hp
        have hne : a≠p := by intro heq; subst p; exact hnot hpm
        refine ⟨List.mem_cons_of_mem a hpm,hpa,?_,?_⟩
        · simp [hne,hpv]
        · intro q hq hlt
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ha
          · have haq : a≠q := by intro heq; subst q; exact hnot hq
            apply hfirst q hq
            simpa [List.idxOf_cons,hne,haq] using! hlt

/-- Enumerating the inverse finite-product equivalence gives the row-major candidate list. -/
private theorem candidates_ofFn (γ Nmax : ℕ) :
    List.ofFn (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax) = candidates γ Nmax := by
  rw [List.ofFn_mul]
  have hp (i : Fin γ) (j : Fin Nmax) (h : i.val*Nmax+j.val<γ*Nmax) :
      (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax) ⟨i.val*Nmax+j.val,h⟩ = (i,j) := by
    apply finProdFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp_rw [hp]
  simp [candidates,List.ofFn_eq_map,List.flatMap_def]

/-- The row-major candidate list has no duplicate pairs. -/
private theorem candidates_nodup (γ Nmax : ℕ) : (candidates γ Nmax).Nodup := by
  rw [← candidates_ofFn]
  exact List.nodup_ofFn_ofInjective finProdFinEquiv.symm.injective

/-- The row-major candidate list has length `γ*Nmax`. -/
private theorem candidates_length (γ Nmax : ℕ) : (candidates γ Nmax).length=γ*Nmax := by
  rw [← candidates_ofFn,List.length_ofFn]

/-- Every pair of valid finite indices belongs to the candidate list. -/
private theorem candidates_mem {γ Nmax : ℕ} (p : Fin γ × Fin Nmax) : p ∈ candidates γ Nmax := by
  rw [← candidates_ofFn,List.mem_ofFn]
  exact ⟨finProdFinEquiv p,Equiv.symm_apply_apply _ p⟩

/-- The zero-based list index of a candidate pair is `p.1.val*Nmax+p.2.val`. -/
private theorem candidates_idxOf {γ Nmax : ℕ} (p : Fin γ × Fin Nmax) :
    (candidates γ Nmax).idxOf p = p.1.val*Nmax+p.2.val := by
  rw [← candidates_ofFn]
  have hn := List.nodup_ofFn_ofInjective
    (finProdFinEquiv.symm.injective : Function.Injective (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax))
  have h := hn.idxOf_getElem (finProdFinEquiv p).val
    (by simpa only [List.length_ofFn] using! (finProdFinEquiv p).isLt)
  simp only [List.getElem_ofFn] at h
  change (List.ofFn (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax)).idxOf
    (finProdFinEquiv.symm (finProdFinEquiv p)) = (finProdFinEquiv p).val at h
  rw [Equiv.symm_apply_apply] at h
  have hh : (List.ofFn (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax)).idxOf p =
      (finProdFinEquiv p).val := h
  change (List.ofFn (finProdFinEquiv.symm : Fin (γ*Nmax) → Fin γ × Fin Nmax)).idxOf p =
    p.2.val+Nmax*p.1.val at hh
  simpa only [Nat.mul_comm,Nat.add_comm] using! hh

/-- The full scan returns the first row-major accepted candidate, or no choice exactly when
every candidate fails, with exact visited counts. Its Gibbs and law-draw counts agree and
satisfy the grid bound, and its state-copy count is `(M+1)*L*visited`. -/
theorem run_first_accepted :
  ∀ (m γ Nmax M : ℕ) (d : Input m γ Nmax M),
    (run d).visited ≤ γ*Nmax ∧
    ((run d).choice = none ↔ ∀ p : Fin γ × Fin Nmax, accepts d p = false) ∧
    ((run d).choice = none → (run d).visited = γ*Nmax) ∧
    (∀ p : Fin γ × Fin Nmax, (run d).choice = some p →
      accepts d p = true ∧ (run d).visited = p.1.val*Nmax+p.2.val+1 ∧
      (∀ q : Fin γ × Fin Nmax,
        q.1.val*Nmax+q.2.val < p.1.val*Nmax+p.2.val → accepts d q = false)) ∧
    (∀ L : ℕ, gibbsCopies M (run d) ≤ M*(γ*Nmax) ∧
      qDraws M (run d) = gibbsCopies M (run d) ∧
      stateCopies M L (run d) = (M+1)*L*(run d).visited) := by
  intro m γ Nmax M d
  obtain ⟨hb,hn,hl,hs⟩ := scan_spec d (candidates γ Nmax) (candidates_nodup γ Nmax)
  have hbound : (run d).visited≤γ*Nmax := by simpa [run,candidates_length] using! hb
  refine ⟨hbound,?_,?_,?_,?_⟩
  · exact hn.trans ⟨fun h p => h p (candidates_mem p),fun h p _ => h p⟩
  · intro h
    simpa [run,candidates_length] using! hl h
  · intro p hp
    obtain ⟨_,ha,hv,hfirst⟩ := hs p hp
    refine ⟨ha,by simpa [candidates_idxOf,run] using! hv,?_⟩
    intro q hq
    apply hfirst q (candidates_mem q)
    simpa [candidates_idxOf] using! hq
  · intro L
    exact ⟨Nat.mul_le_mul_left M hbound,rfl,rfl⟩

/-- A true rational acceptance test implies the corresponding real-valued `step2Accepts`
predicate after casting the input data. -/
private theorem accepts_cast {m γ Nmax M : ℕ} (d : Input m γ Nmax M)
    (p : Fin γ × Fin Nmax) (h : accepts d p = true) :
    step2Accepts m M (fun i => (d.b i:ℝ)) (fun i => (d.estA p.1 p.2 i:ℝ))
      (d.estC p.1 p.2:ℝ) (d.draws p.1 p.2) d.α d.R d.κ d.ν (mass d p.2:ℚ) := by
  unfold accepts at h
  have hh := of_decide_eq_true h
  have h₁ : ((d.estC p.1 p.2 / mass d p.2 - (d.κ+d.ν):ℚ):ℝ) ≤
      (((∑ j : Fin M,d.estA p.1 p.2 (d.draws p.1 p.2 j))/(M:ℚ):ℚ):ℝ) := by
    exact_mod_cast hh.1
  have h₂ : (((∑ j : Fin M,d.b (d.draws p.1 p.2 j))/(M:ℚ):ℚ):ℝ) ≤
      ((d.α/mass d p.2+d.R*(d.κ+d.ν):ℚ):ℝ) := by
    exact_mod_cast hh.2
  push_cast at h₁ h₂
  exact ⟨h₁,h₂⟩

/-- Under the stated positivity, sampling-law, and estimation assumptions, a returned candidate
satisfies real acceptance and the sampled-width objective bound. Its separation is at least
`-(μ*(2*(κ+ν)+ν)+ν)`, where `μ` is the returned mass and parameters are cast to real
numbers. -/
theorem run_candidate_sound :
  ∀ (D m γ Nmax M : ℕ) (d : Input m γ Nmax M) (A : Fin m → Operator D) (Cv ρ : Operator D),
    0<M → 0<d.κ → 0≤d.R → 0≤d.ν → d.κ*(Nmax:ℚ)≤d.α →
    (∀ k : Fin γ, IsSamplingLaw m (fun i => (d.law k i:ℝ))) →
    (∀ (k : Fin γ) (N : Fin Nmax) (i : Fin m),
      |(d.estA k N i:ℝ)-(Matrix.trace (A i*ρ)).re|≤(d.ν:ℝ)) →
    (∀ (k : Fin γ) (N : Fin Nmax), |(d.estC k N:ℝ)-(Matrix.trace (Cv*ρ)).re|≤(d.ν:ℝ)) →
    (∀ (k : Fin γ) (N : Fin Nmax),
      |(∑ i : Fin m,(d.law k i:ℝ)*(d.b i:ℝ))-(∑ j : Fin M,(d.b (d.draws k N j):ℝ))/(M:ℝ)|≤
        (d.R:ℝ)*((d.κ:ℝ)+(d.ν:ℝ))) →
    (∀ (k : Fin γ) (N : Fin Nmax),
      |(∑ j : Fin M,(d.estA k N (d.draws k N j):ℝ))/(M:ℝ)-
        (∑ i : Fin m,(d.law k i:ℝ)*(d.estA k N i:ℝ))|≤(d.κ:ℝ)+(d.ν:ℝ)) →
    ∀ p : Fin γ × Fin Nmax,(run d).choice=some p →
      let μ : ℝ := (mass d p.2:ℚ)
      let y : Fin m→ℝ := step2RoundVector m μ (fun i => (d.law p.1 i:ℝ))
      step2Accepts m M (fun i => (d.b i:ℝ)) (fun i => (d.estA p.1 p.2 i:ℝ)) (d.estC p.1 p.2:ℝ)
        (d.draws p.1 p.2) (d.α:ℝ) (d.R:ℝ) (d.κ:ℝ) (d.ν:ℝ) μ ∧
      (∑ i,(d.b i:ℝ)*y i)≤widthSampled (d.α:ℝ) (d.R:ℝ) ((d.κ:ℝ)+(d.ν:ℝ)) ∧
      -(μ*(2*((d.κ:ℝ)+(d.ν:ℝ))+(d.ν:ℝ))+(d.ν:ℝ))≤
        (∑ i,y i*(Matrix.trace (A i*ρ)).re)-(Matrix.trace (Cv*ρ)).re := by
  intro D m γ Nmax M d A Cv ρ _hM hκ hR hν hα hlaw hA hC hb he p hp
  have haccept := accepts_cast d p ((run_first_accepted m γ Nmax M d).2.2.2.1 p hp).1
  have hμ : 0<(mass d p.2:ℝ) := by
    have hh : 0 < mass d p.2 := by unfold mass; positivity
    exact_mod_cast hh
  have hμα : (mass d p.2:ℝ)≤(d.α:ℝ) := by
    have hh : mass d p.2≤d.α := by
      unfold mass
      have hN : (p.2.val:ℚ)+1≤(Nmax:ℚ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr p.2.isLt)
      exact (mul_le_mul_of_nonneg_left hN (le_of_lt hκ)).trans hα
    exact_mod_cast hh
  have hR' : (0:ℝ)≤d.R := by exact_mod_cast hR
  have hκ' : (0:ℝ)<d.κ := by exact_mod_cast hκ
  have hν' : (0:ℝ)≤d.ν := by exact_mod_cast hν
  refine ⟨haccept,?_,?_⟩
  · exact step2Accepted_width m M (fun i => (d.b i:ℝ)) (fun i => (d.estA p.1 p.2 i:ℝ))
      (d.estC p.1 p.2:ℝ) (d.draws p.1 p.2) (fun i => (d.law p.1 i:ℝ))
      d.κ d.R d.ν d.α (mass d p.2:ℚ) hR' (by linarith) hμ hμα (hb p.1 p.2) haccept
  · exact step2Accepted_separation_lower D m M A Cv (fun i => (d.b i:ℝ)) ρ
      (fun i => (d.estA p.1 p.2 i:ℝ)) (d.estC p.1 p.2:ℝ) (d.draws p.1 p.2)
      (fun i => (d.law p.1 i:ℝ)) d.κ d.R d.ν d.α (mass d p.2:ℚ) hμ
      ⟨hA p.1 p.2,hC p.1 p.2⟩ (hlaw p.1) (he p.1 p.2) haccept
end Qatlib.Concepts.RationalScan.Step2Scan
