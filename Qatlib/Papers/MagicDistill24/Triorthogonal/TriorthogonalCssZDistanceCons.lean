/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectCons
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCssZDistanceStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Computes the sigma-weighted pairing of a distinguished row with a distinguished-row linear
combination. -/
private theorem pair_clause1_coord {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (b : Fin k) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = c b * D.τ b := by
  have hstep :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = ∑ a, c a * ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
          * D.G (Fin.castLE D.hk a) i := by
    have h : ∀ i : Fin n,
        D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
          = ∑ a, D.σ i * D.G (Fin.castLE D.hk b) i
              * (c a * D.G (Fin.castLE D.hk a) i) := by
      intro i
      rw [Finset.mul_sum]
    calc ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        = ∑ i, ∑ a, D.σ i * D.G (Fin.castLE D.hk b) i
            * (c a * D.G (Fin.castLE D.hk a) i) :=
          Finset.sum_congr rfl fun i _ => h i
      _ = ∑ a, ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
            * (c a * D.G (Fin.castLE D.hk a) i) := Finset.sum_comm
      _ = ∑ a, c a * ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
              * D.G (Fin.castLE D.hk a) i := by
          refine Finset.sum_congr rfl fun (a : Fin k) _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [hstep, Finset.sum_eq_single b]
  · rw [triPair_rows D b b, ite_eq_left rfl]
  · intro a _ hab
    rw [triPair_rows D a b, ite_eq_right hab, mul_zero]
  · intro hab
    exact absurd (Finset.mem_univ b) hab

/-- Shows that a clause-zero row and a distinguished row have zero sigma-weighted pairing. -/
private theorem triPair_clause0_clause1 {m n k : ℕ} (D : TriorthogonalData m n k)
    (a' : Fin (m - k)) (b : Fin k) :
    ∑ i, D.σ i * clause0Row D a' i * D.G (Fin.castLE D.hk b) i = 0 := by
  have h : ∑ i, D.σ i * clause0Row D a' i * D.G (Fin.castLE D.hk b) i
      = ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * clause0Row D a' i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, triPair_clause1_clause0 D b a']

/-- Shows that any two clause-zero rows have zero sigma-weighted pairing. -/
private theorem triPair_clause0_clause0 {m n k : ℕ} (D : TriorthogonalData m n k)
    (a' a'' : Fin (m - k)) :
    ∑ i, D.σ i * clause0Row D a' i * clause0Row D a'' i = 0 := by
  have h := D.triPair ((Fin.cast (by have hk := D.hk; omega) :
      Fin (k + (m - k)) → Fin m) (Fin.natAdd k a'))
    ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
      (Fin.natAdd k a''))
  simp only [Fin.val_natAdd, Fin.val_cast] at h
  have hk : k ≤ k + (a' : ℕ) := by omega
  rw [dite_eq_right (fun hc => by have := hc.2; omega)] at h
  exact h

/-- Shows that a clause-zero row has zero sigma-weighted pairing with a distinguished-row linear
combination. -/
private theorem pair_g0row_lin {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (a' : Fin (m - k)) :
    ∑ i, D.σ i * clause0Row D a' i * (∑ a, c a * D.G (Fin.castLE D.hk a) i) = 0 := by
  have h : ∀ i : Fin n,
      D.σ i * clause0Row D a' i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        = ∑ a, D.σ i * clause0Row D a' i * (c a * D.G (Fin.castLE D.hk a) i) := by
    intro i
    rw [Finset.mul_sum]
  have h2 : ∀ a : Fin k, ∑ i, D.σ i * clause0Row D a' i
        * (c a * D.G (Fin.castLE D.hk a) i)
      = c a * ∑ i, D.σ i * clause0Row D a' i * D.G (Fin.castLE D.hk a) i := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_comm,
    Finset.sum_congr rfl fun (a : Fin k) _ => h2 a]
  exact Finset.sum_eq_zero fun a _ => by rw [triPair_clause0_clause1 D a' a, mul_zero]

/-- Shows that a clause-zero row has zero sigma-weighted pairing with a clause-zero linear
combination. -/
private theorem pair_g0row_comb {m n k : ℕ} (D : TriorthogonalData m n k)
    (d : Fin (m - k) → F1024) (a' : Fin (m - k)) :
    ∑ i, D.σ i * clause0Row D a' i * (∑ a'', d a'' * clause0Row D a'' i) = 0 := by
  have h : ∀ i : Fin n,
      D.σ i * clause0Row D a' i * (∑ a'', d a'' * clause0Row D a'' i)
        = ∑ a'', D.σ i * clause0Row D a' i * (d a'' * clause0Row D a'' i) := by
    intro i
    rw [Finset.mul_sum]
  have h2 : ∀ a'' : Fin (m - k), ∑ i, D.σ i * clause0Row D a' i
        * (d a'' * clause0Row D a'' i)
      = d a'' * ∑ i, D.σ i * clause0Row D a' i * clause0Row D a'' i := by
    intro a''
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_comm,
    Finset.sum_congr rfl fun (a'' : Fin (m - k)) _ => h2 a'']
  exact Finset.sum_eq_zero fun a'' _ => by rw [triPair_clause0_clause0 D a' a'', mul_zero]

/-- Characterizes membership in `triG1` by a linear combination of distinguished generator rows. -/
private theorem mem_triG1_iff {m n k : ℕ} (D : TriorthogonalData m n k)
    (v : Fin n → F1024) :
    v ∈ triG1 D ↔ ∃ c : Fin k → F1024,
      ∀ i, v i = ∑ a, c a * D.G (Fin.castLE D.hk a) i := by
  constructor
  · intro hv
    have h := hv
    unfold triG1 at h
    rw [Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, fun i => by
      have := congrFun hc i
      simpa [Finset.sum_apply] using this.symm⟩
  · rintro ⟨c, hc⟩
    unfold triG1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, funext fun i => ?_⟩
    have := hc i
    simpa [Finset.sum_apply] using this.symm

/-- Expresses `triG` as the sum of `triG1` and `triG0`. -/
private theorem triG_eq_sup {m n k : ℕ} (D : TriorthogonalData m n k) :
    triG D = triG1 D ⊔ triG0 D := by
  refine le_antisymm ?_ ?_
  · rw [triG, triRowSpace]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    rcases Nat.lt_or_ge (t : ℕ) k with hlt | hge
    · refine Submodule.mem_sup_left ?_
      have he : Fin.castLE D.hk ⟨(t : ℕ), hlt⟩ = t := Fin.ext rfl
      exact Submodule.subset_span ⟨(⟨(t : ℕ), hlt⟩ : Fin k), congrArg D.G he⟩
    · refine Submodule.mem_sup_right ?_
      have he : (Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k ⟨(t : ℕ) - k, by omega⟩) = t :=
        Fin.ext (by simp only [Fin.val_natAdd, Fin.val_cast]; omega)
      exact Submodule.subset_span ⟨(⟨(t : ℕ) - k, by omega⟩ : Fin (m - k)),
        congrArg D.G he⟩
  · refine sup_le ?_ ?_
    · unfold triG1 triG
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Fin.castLE D.hk a, rfl⟩
    · unfold triG0 triG
      rw [Submodule.span_le]
      rintro _ ⟨a', rfl⟩
      exact Submodule.subset_span ⟨(Fin.cast (by have hk := D.hk; omega) :
        Fin (k + (m - k)) → Fin m) (Fin.natAdd k a'), rfl⟩

/-- Decomposes each vector of `triG` into distinguished-row and clause-zero linear combinations. -/
private theorem mem_triG_decomp {m n k : ℕ} (D : TriorthogonalData m n k)
    (f : Fin n → F1024) (hf : f ∈ triG D) :
    ∃ c : Fin k → F1024, ∃ d : Fin (m - k) → F1024,
      ∀ i, f i = (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + ∑ a', d a' * clause0Row D a' i := by
  rw [triG_eq_sup D] at hf
  obtain ⟨g1, hg1, g0, hg0, hfg⟩ := Submodule.mem_sup.mp hf
  obtain ⟨c, hc⟩ := mem_triG1_iff D g1 |>.mp hg1
  obtain ⟨d, hd⟩ := mem_triG0_iff D g0 |>.mp hg0
  refine ⟨c, d, fun i => ?_⟩
  rw [← hfg, Pi.add_apply, hc i, hd i]

private noncomputable def mulSigma {m n k : ℕ} (D : TriorthogonalData m n k)
    (f : Fin n → F1024) : Fin n → F1024 :=
  fun i => D.σ i * f i

/-- Shows that coordinatewise multiplication by `D.σ` preserves Hamming weight. -/
private theorem hammingWeight_mulSigma {m n k : ℕ} (D : TriorthogonalData m n k)
    (f : Fin n → F1024) :
    triHammingWeight (mulSigma D f) = triHammingWeight f := by
  unfold triHammingWeight mulSigma
  have hfil : (Finset.univ.filter fun i => D.σ i * f i ≠ 0)
      = Finset.univ.filter fun i => f i ≠ 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ]
    exact ⟨fun h => ⟨h.1, (mul_ne_zero_iff.mp h.2).2⟩,
      fun h => ⟨h.1, mul_ne_zero (D.hσ i) h.2⟩⟩
  rw [hfil]

/-- Computes the sigma-weighted pairing of a distinguished row with a decomposed code vector. -/
private theorem sigma_pair_decomp {m n k : ℕ} (D : TriorthogonalData m n k)
    (b : Fin k) (c : Fin k → F1024) (d : Fin (m - k) → F1024) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
        * ((∑ a, c a * D.G (Fin.castLE D.hk a) i) + ∑ a', d a' * clause0Row D a' i)
      = c b * D.τ b := by
  have h1 : ∀ i : Fin n, D.σ i * D.G (Fin.castLE D.hk b) i
        * ((∑ a, c a * D.G (Fin.castLE D.hk a) i) + ∑ a', d a' * clause0Row D a' i)
      = D.σ i * D.G (Fin.castLE D.hk b) i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + D.σ i * D.G (Fin.castLE D.hk b) i * ∑ a', d a' * clause0Row D a' i :=
    fun i => by rw [mul_add]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib,
    pair_clause1_coord D c b, pair_clause0_comb D d b, add_zero]

/-- Shows that the sigma-weighted pairing of a clause-zero row with a decomposed code vector is
zero. -/
private theorem sigma_pair_clause0_decomp {m n k : ℕ} (D : TriorthogonalData m n k)
    (a' : Fin (m - k)) (c : Fin k → F1024) (d : Fin (m - k) → F1024) :
    ∑ i, D.σ i * clause0Row D a' i
        * ((∑ a, c a * D.G (Fin.castLE D.hk a) i) + ∑ a'', d a'' * clause0Row D a'' i)
      = 0 := by
  have h1 : ∀ i : Fin n, D.σ i * clause0Row D a' i
        * ((∑ a, c a * D.G (Fin.castLE D.hk a) i) + ∑ a'', d a'' * clause0Row D a'' i)
      = D.σ i * clause0Row D a' i * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + D.σ i * clause0Row D a' i * ∑ a'', d a'' * clause0Row D a'' i :=
    fun i => by rw [mul_add]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib,
    pair_g0row_lin D c a', pair_g0row_comb D d a', add_zero]

/-- Shows that sigma multiplication maps `triG` into the dual of `triG0`. -/
private theorem mulSigma_mem_dual_clause0 {m n k : ℕ} (D : TriorthogonalData m n k)
    (f : Fin n → F1024) (hf : f ∈ triG D) :
    mulSigma D f ∈ triDual (triG0 D) := by
  obtain ⟨c, d, hdec⟩ := mem_triG_decomp D f hf
  rw [mem_triDual_iff]
  intro v hv
  obtain ⟨e, he⟩ := mem_triG0_iff D v |>.mp hv
  have hstep : ∀ i : Fin n, v i * mulSigma D f i
      = ∑ a'', e a'' * (D.σ i * f i * clause0Row D a'' i) := by
    intro i
    simp only [mulSigma]
    rw [he i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a'' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  have hpull : ∀ a'' : Fin (m - k),
      (∑ i, e a'' * (D.σ i * f i * clause0Row D a'' i))
        = e a'' * ∑ i, D.σ i * f i * clause0Row D a'' i := by
    intro a''
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun (a'' : Fin (m - k)) _ => hpull a'']
  refine Finset.sum_eq_zero fun a'' _ => ?_
  have hin : ∑ i, D.σ i * f i * clause0Row D a'' i
      = ∑ i, D.σ i * clause0Row D a'' i
          * ((∑ a, c a * D.G (Fin.castLE D.hk a) i) + ∑ a₀, d a₀ * clause0Row D a₀ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i]
    ring
  rw [hin, sigma_pair_clause0_decomp D a'' c d, mul_zero]

/-- Shows that sigma multiplication of a vector in `triG` outside `triG0` lies outside the dual
of `triG`. -/
private theorem mulSigma_not_mem_dual_g {m n k : ℕ} (D : TriorthogonalData m n k)
    (f : Fin n → F1024) (hf : f ∈ triG D) (hf0 : f ∉ triG0 D) :
    mulSigma D f ∉ triDual (triG D) := by
  obtain ⟨c, d, hdec⟩ := mem_triG_decomp D f hf
  intro hcon
  apply hf0
  have hc0 : ∀ b : Fin k, c b = 0 := by
    intro b
    have hb0 := mem_triDual_iff (triG D) (mulSigma D f) |>.mp hcon
      (D.G (Fin.castLE D.hk b)) (row_mem_triG D (Fin.castLE D.hk b))
    have hcong : ∀ i : Fin n, D.G (Fin.castLE D.hk b) i * mulSigma D f i
        = D.σ i * D.G (Fin.castLE D.hk b) i * f i := by
      intro i
      show D.G (Fin.castLE D.hk b) i * (D.σ i * f i)
        = D.σ i * D.G (Fin.castLE D.hk b) i * f i
      ring
    rw [Finset.sum_congr rfl fun i _ => hcong i] at hb0
    rw [Finset.sum_congr rfl fun i _ => by rw [hdec i]] at hb0
    rw [sigma_pair_decomp D b c d] at hb0
    exact mul_eq_zero.mp hb0 |>.resolve_right (D.hτ b)
  rw [mem_triG0_iff D f]
  refine ⟨d, fun i => ?_⟩
  rw [hdec i]
  have hr : ∑ a, c a * D.G (Fin.castLE D.hk a) i = 0 := by
    rw [Finset.sum_congr rfl fun a _ => by rw [hc0 a, zero_mul], Finset.sum_const_zero]
  rw [hr, zero_add]

/-- Establishes the Z-distance result specified by `TriorthogonalCssZDistance`. -/
theorem triorthogonalCssZDistance : TriorthogonalCssZDistance := by
  intro m n k D
  unfold triDistanceZ triDistanceX
  refine sInf_le_sInf ?_
  intro w hw
  obtain ⟨f, hf, hf0, hwf⟩ := hw
  exact ⟨mulSigma D f, mulSigma_mem_dual_clause0 D f hf, mulSigma_not_mem_dual_g D f hf hf0,
    by rw [← hwf, hammingWeight_mulSigma]⟩

end Qatlib.Papers.MagicDistill24.Triorthogonal
