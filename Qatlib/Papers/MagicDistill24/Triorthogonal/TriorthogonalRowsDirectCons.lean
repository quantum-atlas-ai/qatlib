/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

def clause0Row {m n k : ℕ} (D : TriorthogonalData m n k) (a' : Fin (m - k)) :
    Fin n → F1024 :=
  D.G ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
    (Fin.natAdd k a'))

/-- Computes the sigma-weighted pairing of two distinguished rows as a diagonal expression
involving `D.τ`. -/
theorem triPair_rows {m n k : ℕ} (D : TriorthogonalData m n k) (a b : Fin k) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * D.G (Fin.castLE D.hk a) i
      = if a = b then D.τ b else 0 := by
  have h := D.triPair (Fin.castLE D.hk b) (Fin.castLE D.hk a)
  simp only [Fin.val_castLE] at h
  by_cases hab : a = b
  · rw [hab] at h ⊢
    rw [dite_eq_left ⟨rfl, b.isLt⟩, b.eta, ite_eq_left rfl] at *
    exact h
  · rw [dite_eq_right (fun hc => hab (Fin.val_inj.mp hc.1.symm))] at h
    rw [ite_eq_right hab]
    exact h

/-- Shows that a distinguished row has zero sigma-weighted pairing with a clause-zero row. -/
theorem triPair_clause1_clause0 {m n k : ℕ} (D : TriorthogonalData m n k)
    (b : Fin k) (a' : Fin (m - k)) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * clause0Row D a' i = 0 := by
  have hb : (b : ℕ) < k := b.isLt
  have h := D.triPair (Fin.castLE D.hk b)
    ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
      (Fin.natAdd k a'))
  simp only [Fin.val_castLE, Fin.val_natAdd, Fin.val_cast] at h
  rw [dite_eq_right (fun hc => by have := hc.1; omega)] at h
  exact h

/-- Evaluates a vector linear combination of distinguished rows coordinatewise. -/
private theorem val_sum_rows {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (i : Fin n) :
    (∑ a, c a • D.G (Fin.castLE D.hk a)) i = ∑ a, c a * D.G (Fin.castLE D.hk a) i := by
  simp [Finset.sum_apply]

/-- Distributes the sigma-weighted pairing over a distinguished-row linear combination. -/
private theorem pair_lin_comb {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (b : Fin k) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = ∑ a, c a * ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * D.G (Fin.castLE D.hk a) i := by
  have h : ∀ i : Fin n,
      D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        = ∑ a, D.σ i * D.G (Fin.castLE D.hk b) i * (c a * D.G (Fin.castLE D.hk a) i) := by
    intro i
    rw [Finset.mul_sum]
  calc ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = ∑ i, ∑ a, D.σ i * D.G (Fin.castLE D.hk b) i
          * (c a * D.G (Fin.castLE D.hk a) i) :=
        Finset.sum_congr rfl fun i _ => h i
    _ = ∑ a, ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
          * (c a * D.G (Fin.castLE D.hk a) i) := Finset.sum_comm
    _ = ∑ a, c a * ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
          * D.G (Fin.castLE D.hk a) i := by
        refine Finset.sum_congr rfl fun (a : Fin k) _ => ?_
        try rw [Finset.mul_sum]
        try exact Finset.sum_congr rfl fun i _ => by ring

/-- Shows that a distinguished row has zero sigma-weighted pairing with any clause-zero linear
combination. -/
theorem pair_clause0_comb {m n k : ℕ} (D : TriorthogonalData m n k)
    (d : Fin (m - k) → F1024) (b : Fin k) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a', d a' * clause0Row D a' i) = 0 := by
  have h : ∀ i : Fin n,
      D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a', d a' * clause0Row D a' i)
        = ∑ a', D.σ i * D.G (Fin.castLE D.hk b) i * (d a' * clause0Row D a' i) := by
    intro i
    rw [Finset.mul_sum]
  calc ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a', d a' * clause0Row D a' i)
      = ∑ i, ∑ a', D.σ i * D.G (Fin.castLE D.hk b) i * (d a' * clause0Row D a' i) :=
        Finset.sum_congr rfl fun i _ => h i
    _ = ∑ a', ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (d a' * clause0Row D a' i) :=
        Finset.sum_comm
    _ = ∑ a', d a' * ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * clause0Row D a' i := by
        refine Finset.sum_congr rfl fun (a' : Fin (m - k)) _ => ?_
        try rw [Finset.mul_sum]
        try exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := Finset.sum_eq_zero fun a' _ => by rw [triPair_clause1_clause0 D b a', mul_zero]

/-- Characterizes orthogonal dual membership by vanishing pairings with all submodule elements. -/
theorem mem_triDual_iff {n : ℕ} (S : Submodule F1024 (Fin n → F1024))
    (y : Fin n → F1024) :
    y ∈ triDual S ↔ ∀ x ∈ S, ∑ i, x i * y i = 0 := by
  simp only [triDual, Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

/-- Shows that every generator row belongs to `triG`. -/
theorem row_mem_triG {m n k : ℕ} (D : TriorthogonalData m n k) (t : Fin m) :
    D.G t ∈ triG D :=
  Submodule.subset_span ⟨t, rfl⟩

/-- Characterizes membership in `triG0` by a linear combination of clause-zero rows. -/
theorem mem_triG0_iff {m n k : ℕ} (D : TriorthogonalData m n k)
    (v : Fin n → F1024) :
    v ∈ triG0 D ↔ ∃ d : Fin (m - k) → F1024, ∀ i, v i = ∑ a', d a' * clause0Row D a' i := by
  constructor
  · intro hv
    have h := hv
    unfold triG0 at h
    rw [Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨d, hd⟩ := h
    exact ⟨d, fun i => by
      have := congrFun hd i
      simpa [Finset.sum_apply, clause0Row] using this.symm⟩
  · rintro ⟨d, hd⟩
    unfold triG0
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨d, funext fun i => ?_⟩
    have := hd i
    simpa [Finset.sum_apply, clause0Row] using this.symm

/-- Shows that a distinguished row has zero sigma-weighted pairing with every element of
`triG0`. -/
theorem sigma_pair_clause0 {m n k : ℕ} (D : TriorthogonalData m n k) (b : Fin k)
    (v : Fin n → F1024) (hv : v ∈ triG0 D) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * v i = 0 := by
  obtain ⟨d, hd⟩ := mem_triG0_iff D v |>.mp hv
  rw [Finset.sum_congr rfl fun i _ => by rw [hd i]]
  exact pair_clause0_comb D d b

/-- Shows that the pairing of a code vector with a vector in its orthogonal dual vanishes. -/
theorem dot_eq_zero_of_mem_dual {m n k : ℕ} (D : TriorthogonalData m n k)
    {w : Fin n → F1024} (hw : w ∈ triDual (triG D)) {x : Fin n → F1024}
    (hx : x ∈ triG D) :
    ∑ i, x i * w i = 0 :=
  mem_triDual_iff (triG D) w |>.mp hw x hx

/-- Shows that a vanishing linear combination of distinguished rows has all coefficients zero. -/
theorem clause1_rows_indep {m n k : ℕ} (D : TriorthogonalData m n k) :
    ∀ c : Fin k → F1024,
      ∑ a, c a • D.G (Fin.castLE D.hk a) = 0 → ∀ a, c a = 0 := by
  intro c hc b
  have hz : ∀ i : Fin n, ∑ a, c a * D.G (Fin.castLE D.hk a) i = 0 := by
    intro i
    rw [← val_sum_rows D c i, hc]
    rfl
  have key := pair_lin_comb D c b
  rw [Finset.sum_congr rfl fun (a : Fin k) _ => by rw [triPair_rows D a b]] at key
  simp only [hz, mul_zero, Finset.sum_const_zero, mul_ite] at key
  rw [Finset.sum_ite_eq' Finset.univ b (fun a => c a * D.τ b),
    ite_eq_left (Finset.mem_univ b)] at key
  exact mul_eq_zero.mp key.symm |>.resolve_right (D.hτ b)

/-- Shows that `triG1` and `triG0` have trivial intersection. -/
theorem clause1_inf_clause0 {m n k : ℕ} (D : TriorthogonalData m n k) :
    triG1 D ⊓ triG0 D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx1 := hx.1
  have hx2 := hx.2
  unfold triG1 at hx1
  unfold triG0 at hx2
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hx1
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hx2
  obtain ⟨c, hc⟩ := hx1
  obtain ⟨d, hd⟩ := hx2
  have hcb : ∀ b : Fin k, c b = 0 := by
    intro b
    have hxc : ∀ i : Fin n, x i = ∑ a, c a * D.G (Fin.castLE D.hk a) i := by
      intro i
      rw [← val_sum_rows D c i]
      exact (congrFun hc i).symm
    have hxd : ∀ i : Fin n, x i = ∑ a', d a' * clause0Row D a' i := by
      intro i
      have h1 : (∑ a', d a' • clause0Row D a') i = ∑ a', d a' * clause0Row D a' i := by
        simp [Finset.sum_apply]
      rw [← h1]
      exact (congrFun hd i).symm
    have E1 : ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * x i = c b * D.τ b := by
      rw [Finset.sum_congr rfl fun i _ => by rw [hxc i]]
      rw [pair_lin_comb D c b, Finset.sum_eq_single b]
      · rw [triPair_rows D b b, ite_eq_left rfl]
      · intro a _ hab
        rw [triPair_rows D a b, ite_eq_right hab, mul_zero]
      · intro hab
        exact absurd (Finset.mem_univ b) hab
    have E2 : ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * x i = 0 := by
      rw [Finset.sum_congr rfl fun i _ => by rw [hxd i], pair_clause0_comb D d b]
    exact mul_eq_zero.mp (E1.symm.trans E2) |>.resolve_right (D.hτ b)
  calc x = ∑ a, c a • D.G (Fin.castLE D.hk a) := hc.symm
    _ = ∑ a, (0 : F1024) • D.G (Fin.castLE D.hk a) := Finset.sum_congr rfl
          fun a _ => by rw [hcb a]
    _ = 0 := by simp

/-- Establishes the directness properties of triorthogonal rows specified by
`TriorthogonalRowsDirect`. -/
theorem triorthogonalRowsDirect : TriorthogonalRowsDirect := by
  intro m n k D
  exact ⟨clause1_rows_indep D, clause1_inf_clause0 D⟩

end Qatlib.Papers.MagicDistill24.Triorthogonal
