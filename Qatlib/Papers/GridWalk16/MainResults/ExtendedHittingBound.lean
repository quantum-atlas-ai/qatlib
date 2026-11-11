/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Qatlib.Papers.GridWalk16.MainResults.EscapeSubadditivity

set_option backward.isDefEq.respectTransparency false

/-!
# GridWalk16 — Theorem 2 and Corollary 3 (claims c001, c002)

Fixed paper: arXiv:1612.08958v1, §2.

**Theorem 2** (p. 6, proved p. 8): for a reversible ergodic walk `P`, a disjoint union
`M = ⋃ᵢ Mᵢ` of nonempty marked subsets satisfies
`HT⁺(P,M) ∈ O(∑ᵢ (εᵢ/ε_M)·HT⁺(P,Mᵢ))`.
The paper's proof (p. 8) combines Theorem 4 (`HT⁺ = Θ((1/ε)·E)`, Eq. (2)) with the
sub-additivity of the escape time (Lemma 6).  In the exact representative
`HT⁺(S) = (1/ε_S)·E(S)` this gives the *constant-one* inequality
`HT⁺(M) ≤ ∑ᵢ (εᵢ/ε_M)·HT⁺(Mᵢ)`; we retain the `∃ C > 0` form to mirror the paper's
big-O, and prove it with `C = 1` (`extendedHitting_biUnion_le`).

**Corollary 3** (p. 6): taking each `Mᵢ` a singleton and using
`HT⁺(P,{m}) = HT(P,{m})` (paper p. 6: "in the case there is a single marked element,
the extended hitting time is identical to the hitting time"), the weighted average is
at most the worst-case hitting time of a member, so
`HT⁺(P,M) ∈ O(max_{m∈M} HT(P,{m}))`.

No `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.GridWalk16.MainResults

/-- A convex combination (nonnegative weights summing to one) of numbers bounded
above by `B` is at most `B`.  Used for the "weighted average ≤ max" step of
Corollary 3. -/
lemma weighted_avg_le_sup {κ : Type*} [Fintype κ] (w x : κ → ℝ) (B : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hx : ∀ i, x i ≤ B) :
    ∑ i, w i * x i ≤ B := by
  calc
    ∑ i, w i * x i ≤ ∑ i, w i * B :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

namespace SpectralWalk

variable (W : SpectralWalk X ι)

/-- `ε` is additive over a pairwise-disjoint finite family:
`ε_{⋃ᵢ Mᵢ} = ∑ᵢ ε_{Mᵢ}`. -/
lemma eps_biUnion (S : κ → Finset X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    W.eps (Finset.univ.biUnion S) = ∑ i, W.eps (S i) := by
  simp only [SpectralWalk.eps]
  rw [Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]

/-- The spectral amplitude of a disjoint union is the weighted sum of the
constituent amplitudes,
`⟨λ_k|M_π⟩ = ∑ᵢ (√εᵢ/√ε_M)·⟨λ_k|(Mᵢ)_π⟩` (paper p. 8, "Theorem 2 follows by
linearity"). -/
lemma proj_biUnion [Nonempty κ] (S : κ → Finset X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty) (k : ι) :
    W.proj (Finset.univ.biUnion S) k =
      ∑ i, (Real.sqrt (W.eps (S i)) / Real.sqrt (W.eps (Finset.univ.biUnion S))) *
        W.proj (S i) k := by
  classical
  have hUpos : 0 < W.eps (Finset.univ.biUnion S) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty κ)
    exact W.eps_pos ((hne i).mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)))
  have hsU : Real.sqrt (W.eps (Finset.univ.biUnion S)) ≠ 0 := by positivity
  have hsum : (∑ x ∈ Finset.univ.biUnion S, Real.sqrt (W.pi x) * W.coeff x k)
      = ∑ i, ∑ x ∈ S i, Real.sqrt (W.pi x) * W.coeff x k := by
    rw [Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
  have hQi : ∀ i, (∑ x ∈ S i, Real.sqrt (W.pi x) * W.coeff x k)
      = Real.sqrt (W.eps (S i)) * W.proj (S i) k := by
    intro i
    have hs : Real.sqrt (W.eps (S i)) ≠ 0 := by
      have := W.eps_pos (hne i); positivity
    rw [SpectralWalk.proj, mul_inv_cancel_left₀ hs]
  have hLHS : W.proj (Finset.univ.biUnion S) k =
      (Real.sqrt (W.eps (Finset.univ.biUnion S)))⁻¹ *
        (∑ i, ∑ x ∈ S i, Real.sqrt (W.pi x) * W.coeff x k) := by
    simp only [SpectralWalk.proj]
    rw [hsum]
  rw [hLHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hQi i]
  field_simp
  try ring

/-- The coefficients `√εᵢ/√ε_M` of the union amplitude satisfy
`∑ᵢ (√εᵢ/√ε_M)² = 1` (they form a probability distribution). -/
lemma proj_biUnion_coeff_sq [Nonempty κ] (S : κ → Finset X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty) :
    ∑ i, (Real.sqrt (W.eps (S i)) / Real.sqrt (W.eps (Finset.univ.biUnion S)))^2 = 1 := by
  have hUpos : 0 < W.eps (Finset.univ.biUnion S) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty κ)
    exact W.eps_pos ((hne i).mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)))
  have hstep : ∀ i, (Real.sqrt (W.eps (S i)) / Real.sqrt (W.eps (Finset.univ.biUnion S)))^2
      = W.eps (S i) / W.eps (Finset.univ.biUnion S) := by
    intro i
    rw [div_pow, Real.sq_sqrt (W.eps_nonneg (S i)), Real.sq_sqrt (W.eps_nonneg _)]
  simp only [hstep]
  rw [← Finset.sum_div, ← W.eps_biUnion S hdisj]
  exact div_self (ne_of_gt hUpos)

/-- Escape-time sub-additivity over a finite pairwise-disjoint family, obtained by
finite Cauchy–Schwarz from the amplitude decomposition (the "linearity" step of the
proof of Theorem 2, paper p. 8). -/
theorem escape_biUnion_le [Nonempty κ] (S : κ → Finset X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty) :
    W.escape (Finset.univ.biUnion S) ≤ ∑ i, W.escape (S i) := by
  have hcoef := W.proj_biUnion_coeff_sq S hdisj hne
  simp only [SpectralWalk.escape]
  calc
    ∑ k, (W.proj (Finset.univ.biUnion S) k)^2 / W.gap k
        ≤ ∑ k, (∑ i, (W.proj (S i) k)^2) / W.gap k := by
          apply Finset.sum_le_sum
          intro k _
          apply div_le_div_of_nonneg_right _ (W.gap_pos k).le
          rw [W.proj_biUnion S hdisj hne k]
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
            (f := fun i => Real.sqrt (W.eps (S i)) / Real.sqrt (W.eps (Finset.univ.biUnion S)))
            (g := fun i => W.proj (S i) k)
          rw [hcoef, one_mul] at hcs
          simpa only [mul_comm, mul_left_comm, mul_assoc] using hcs
    _ = ∑ k, ∑ i, (W.proj (S i) k)^2 / W.gap k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_div]
    _ = ∑ i, ∑ k, (W.proj (S i) k)^2 / W.gap k := Finset.sum_comm

/-- **Theorem 2 (c001).** For a disjoint union `M = ⋃ᵢ Mᵢ` of nonempty marked subsets,
`HT⁺(P,M) ∈ O(∑ᵢ (εᵢ/ε_M)·HT⁺(P,Mᵢ))`; here with `C = 1`.
Paper arXiv:1612.08958v1, Theorem 2, §2 p. 6 (proof p. 8). -/
theorem extendedHitting_biUnion_le [Nonempty κ] (S : κ → Finset X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty)
    (hM : (Finset.univ.biUnion S).Nonempty) :
    W.extendedHitting (Finset.univ.biUnion S) ≤
      ∑ i, (W.eps (S i) / W.eps (Finset.univ.biUnion S)) *
        W.extendedHitting (S i) := by
  have hUpos : 0 < W.eps (Finset.univ.biUnion S) := W.eps_pos hM
  have hesc := W.escape_biUnion_le S hdisj hne
  have hRHS : (∑ i, (W.eps (S i) / W.eps (Finset.univ.biUnion S)) *
      ((W.eps (S i))⁻¹ * W.escape (S i)))
      = (W.eps (Finset.univ.biUnion S))⁻¹ * ∑ i, W.escape (S i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : W.eps (S i) ≠ 0 := ne_of_gt (W.eps_pos (hne i))
    have hu : W.eps (Finset.univ.biUnion S) ≠ 0 := ne_of_gt hUpos
    field_simp
    try ring
  simp only [SpectralWalk.extendedHitting]
  rw [hRHS]
  exact mul_le_mul_of_nonneg_left hesc (inv_nonneg.mpr (W.eps_nonneg _))

/-- **Corollary 3 (c002).** The extended hitting time of a nonempty marked set is at
most the maximum of the (extended = ordinary) hitting times of its members,
`HT⁺(P,M) ∈ O(max_{m∈M} HT(P,{m}))`; here with `C = 1` and using
`HT(P,{m}) = HT⁺(P,{m})` (paper p. 6).
Paper arXiv:1612.08958v1, Corollary 3, §2 p. 6. -/
theorem extendedHitting_le_max_singleton (M : Finset X) (hM : M.Nonempty) :
    W.extendedHitting M ≤ M.sup' hM (fun m => W.extendedHitting ({m} : Finset X)) := by
  classical
  let S : {x // x ∈ M} → Finset X := fun i => {i.1}
  have hnonempty : Nonempty {x // x ∈ M} := hM.elim fun m hm => ⟨⟨m, hm⟩⟩
  haveI := hnonempty
  have hdisj : ∀ i j : {x // x ∈ M}, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S, Finset.mem_singleton] at hx1 hx2
    exact hij (Subtype.ext (hx1.symm.trans hx2))
  have hne : ∀ i : {x // x ∈ M}, (S i).Nonempty := fun i => Finset.singleton_nonempty _
  have hunion : (Finset.univ.biUnion S) = M := by
    ext x
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact i.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hbi := W.extendedHitting_biUnion_le S hdisj hne (by rw [hunion]; exact hM)
  rw [hunion] at hbi
  refine hbi.trans ?_
  have hB : ∀ i : {x // x ∈ M},
      W.extendedHitting ({i.1} : Finset X) ≤
        M.sup' hM (fun m => W.extendedHitting ({m} : Finset X)) := by
    intro i
    exact Finset.le_sup' (f := fun m => W.extendedHitting ({m} : Finset X)) i.2
  have hw : ∀ i : {x // x ∈ M}, 0 ≤ W.eps ({i.1} : Finset X) / W.eps M := by
    intro i
    exact div_nonneg (W.eps_nonneg _) (W.eps_nonneg _)
  have hsum : ∑ i : {x // x ∈ M}, W.eps ({i.1} : Finset X) / W.eps M = 1 := by
    rw [← Finset.sum_div]
    have hsub : ∑ i : {x // x ∈ M}, W.eps ({i.1} : Finset X) = W.eps M := by
      have h1 : ∀ i : {x // x ∈ M},
          W.eps ({i.1} : Finset X) = W.pi i.1 := by
        intro i; simp [SpectralWalk.eps]
      simp only [h1]
      rw [Finset.sum_coe_sort]
      simp [SpectralWalk.eps]
    rw [hsub]
    exact div_self (ne_of_gt (W.eps_pos hM))
  exact weighted_avg_le_sup _ _ _ hw hsum hB

end SpectralWalk

end Qatlib.Papers.GridWalk16.MainResults
