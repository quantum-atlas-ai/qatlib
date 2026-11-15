/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCssZDistanceCons
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalTransversalGateStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Shows that squaring is additive in `F1024`. -/
private theorem add_pow_two (a b : F1024) : (a + b) ^ 2 = a ^ 2 + b ^ 2 :=
  add_pow_expChar (p := 2) a b

/-- Shows that taking fourth powers is additive in `F1024`. -/
private theorem add_pow_four (a b : F1024) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have h1 : (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by rw [← pow_mul]
  have h2 : ((a + b) ^ 2) ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by rw [add_pow_two]
  have h3 : (a ^ 2 + b ^ 2) ^ 2 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2 := add_pow_two _ _
  have h4 : (a ^ 2) ^ 2 = a ^ 4 := by rw [← pow_mul]
  have h5 : (b ^ 2) ^ 2 = b ^ 4 := by rw [← pow_mul]
  rw [h1, h2, h3, h4, h5]

private noncomputable def frob4 : F1024 →+* F1024 where
  toFun x := x ^ 4
  map_one' := by simp
  map_mul' x y := by rw [mul_pow]
  map_zero' := by simp
  map_add' x y := add_pow_four x y

private noncomputable def frob2 : F1024 →+* F1024 where
  toFun x := x ^ 2
  map_one' := by simp
  map_mul' x y := by rw [mul_pow]
  map_zero' := by simp
  map_add' x y := add_pow_two x y

/-- Reverses the outer and inner indices of a finite triple sum. -/
private theorem sum3_comm {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (F : ι → κ → ν → F1024) :
    (∑ t, ∑ s, ∑ r, F t s r) = ∑ r, ∑ s, ∑ t, F t s r := by
  have h1 : (∑ t, ∑ s, ∑ r, F t s r) = ∑ s, ∑ t, ∑ r, F t s r :=
    Finset.sum_comm (β := F1024) (f := fun t s => ∑ r, F t s r)
  have h2 : (∑ s, ∑ t, ∑ r, F t s r) = ∑ s, ∑ r, ∑ t, F t s r := by
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finset.sum_comm (β := F1024) (f := fun t r => F t s r)
  have h3 : (∑ s, ∑ r, ∑ t, F t s r) = ∑ r, ∑ s, ∑ t, F t s r :=
    Finset.sum_comm (β := F1024) (f := fun s r => ∑ t, F t s r)
  rw [h1, h2, h3]

/-- Moves the outer coordinate sum inside three finite index sums. -/
private theorem swap4 {ι κ ν φ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [Fintype φ] (f : ι → κ → ν → φ → F1024) :
    (∑ i, ∑ t, ∑ s, ∑ r, f i t s r) = ∑ t, ∑ s, ∑ r, ∑ i, f i t s r := by
  have h1 : (∑ i, ∑ t, ∑ s, ∑ r, f i t s r) = ∑ t, ∑ i, ∑ s, ∑ r, f i t s r :=
    Finset.sum_comm (β := F1024) (f := fun i t => ∑ s, ∑ r, f i t s r)
  have h2 : (∑ t, ∑ i, ∑ s, ∑ r, f i t s r) = ∑ t, ∑ s, ∑ i, ∑ r, f i t s r := by
    refine Finset.sum_congr rfl fun t _ => ?_
    exact Finset.sum_comm (β := F1024) (f := fun i s => ∑ r, f i t s r)
  have h3 : (∑ t, ∑ s, ∑ i, ∑ r, f i t s r) = ∑ t, ∑ s, ∑ r, ∑ i, f i t s r := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    exact Finset.sum_comm (β := F1024) (f := fun i r => f i t s r)
  rw [h1, h2, h3]

/-- Expands a product of three finite sums as a triple sum of products. -/
private theorem prod3_expand {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {n : ℕ} (A : ι → Fin n → F1024) (B : κ → Fin n → F1024)
    (C : ν → Fin n → F1024) (i : Fin n) :
    (∑ t, A t i) * (∑ s, B s i) * (∑ r, C r i)
      = ∑ t, ∑ s, ∑ r, A t i * B s i * C r i := by
  have h1 : (∑ t, A t i) * (∑ s, B s i) * (∑ r, C r i)
      = ∑ r, ((∑ t, A t i) * (∑ s, B s i)) * C r i := by
    rw [Finset.mul_sum (R := F1024)]
  have h3 : ∀ (r : ν) (t : ι), ((A t i) * (∑ s, B s i)) * C r i
      = ∑ s, A t i * B s i * C r i := by
    intro r t
    rw [Finset.mul_sum (R := F1024), Finset.sum_mul (R := F1024)]
  have h2 : ∀ r : ν, ((∑ t, A t i) * (∑ s, B s i)) * C r i
      = ∑ t, ∑ s, A t i * B s i * C r i := by
    intro r
    rw [Finset.sum_mul (R := F1024), Finset.sum_mul (R := F1024)]
    exact Finset.sum_congr (M := F1024) rfl fun t _ => h3 r t
  calc (∑ t, A t i) * (∑ s, B s i) * (∑ r, C r i)
      = ∑ r, ((∑ t, A t i) * (∑ s, B s i)) * C r i := h1
    _ = ∑ r, ∑ t, ∑ s, A t i * B s i * C r i :=
        Finset.sum_congr (M := F1024) rfl fun r _ => h2 r
    _ = ∑ t, ∑ s, ∑ r, A t i * B s i * C r i := by
        rw [sum3_comm (F := fun r t s => A t i * B s i * C r i)]
        exact Finset.sum_comm (β := F1024)
          (f := fun s t => ∑ r, A t i * B s i * C r i)

/-- Expands a coordinate sum of three products of sums and moves the coordinate sum innermost. -/
private theorem prod3_sums {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {n : ℕ} (A : ι → Fin n → F1024) (B : κ → Fin n → F1024)
    (C : ν → Fin n → F1024) :
    (∑ i, (∑ t, A t i) * (∑ s, B s i) * (∑ r, C r i))
      = ∑ t, ∑ s, ∑ r, ∑ i, A t i * B s i * C r i := by
  have hstep : ∀ i : Fin n, (∑ t, A t i) * (∑ s, B s i) * (∑ r, C r i)
      = ∑ t, ∑ s, ∑ r, A t i * B s i * C r i := fun i => prod3_expand A B C i
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  exact swap4 (fun i t s r => A t i * B s i * C r i)

/-- Factors three constant multipliers out of a sum of triple products. -/
private theorem pull3 {n : ℕ} (p q z : F1024) (X Y Z : Fin n → F1024) :
    ∑ i, (p * X i) * (q * Y i) * (z * Z i) = p * q * z * ∑ i, X i * Y i * Z i := by
  have h : ∀ i : Fin n, (p * X i) * (q * Y i) * (z * Z i)
      = p * q * z * (X i * Y i * Z i) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum (R := F1024)]

/-- Computes the distinguished-row triple pairing with exponents four, two, and one as the
all-equal index indicator. -/
private theorem triTriple_rows {m n k : ℕ} (D : TriorthogonalData m n k)
    (a b e : Fin k) :
    ∑ i, D.G (Fin.castLE D.hk a) i ^ 4 * D.G (Fin.castLE D.hk b) i ^ 2
        * D.G (Fin.castLE D.hk e) i
      = if a = b ∧ b = e then 1 else 0 := by
  have h := D.triTriple (Fin.castLE D.hk a) (Fin.castLE D.hk b)
    (Fin.castLE D.hk e)
  simp only [Fin.val_castLE] at h
  by_cases h1 : a = b ∧ b = e
  · obtain ⟨hab, hbe⟩ := h1
    rw [ite_eq_left ⟨congrArg Fin.val hab,
      congrArg Fin.val hbe, a.isLt⟩] at h
    rw [ite_eq_left ⟨hab, hbe⟩]
    exact h
  · rw [ite_eq_right (fun hc => h1 ⟨Fin.val_inj.mp hc.1, Fin.val_inj.mp hc.2.1⟩)] at h
    rw [ite_eq_right h1]
    exact h

/-- Shows that the triple row pairing vanishes if any row index belongs to the clause-zero
range. -/
private theorem triTriple_zero_of_ge {m n k : ℕ} (D : TriorthogonalData m n k)
    (t s r : Fin m) (hge : k ≤ (t : ℕ) ∨ k ≤ (s : ℕ) ∨ k ≤ (r : ℕ)) :
    ∑ i, D.G t i ^ 4 * D.G s i ^ 2 * D.G r i = 0 := by
  have h := D.triTriple t s r
  rw [ite_eq_right] at h
  · exact h
  · intro hc
    obtain ⟨e1, e2, e3⟩ := hc
    rcases hge with hg | hg | hg
    · omega
    · omega
    · omega

/-- Collapses a triple sum supported on equal indices to its diagonal sum. -/
private theorem diag3_collapse {k : ℕ} (G : Fin k → Fin k → Fin k → F1024) :
    (∑ a, ∑ b, ∑ e, (if a = b ∧ b = e then G a b e else 0)) = ∑ a, G a a a := by
  have step1 : ∀ a b : Fin k,
      (∑ e, (if a = b ∧ b = e then G a b e else 0))
        = (if a = b then G a b b else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [ite_eq_right hab]
      exact Finset.sum_eq_zero fun e _ => by
        rw [ite_eq_right (fun hc => hab hc.1)]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => step1 a b]
  simp

private noncomputable def rPart {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) : Fin n → F1024 :=
  fun i => ∑ a, c a * D.G (Fin.castLE D.hk a) i

private noncomputable def vPart {m n k : ℕ} (D : TriorthogonalData m n k)
    (d : Fin (m - k) → F1024) : Fin n → F1024 :=
  fun i => ∑ a', d a' * clause0Row D a' i

/-- Distributes the square or fourth power of a distinguished-row linear combination over its
summands. -/
private theorem rPart_pow {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (r : ℕ) (hr : r = 4 ∨ r = 2) (i : Fin n) :
    (rPart D c i) ^ r
      = ∑ a, c a ^ r * D.G (Fin.castLE D.hk a) i ^ r := by
  rcases hr with rfl | rfl
  · show frob4 (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = ∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4
    rw [map_sum frob4 (fun a => c a * D.G (Fin.castLE D.hk a) i) Finset.univ]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (c a * D.G (Fin.castLE D.hk a) i) ^ 4
      = c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4
    rw [mul_pow]
  · show frob2 (∑ a, c a * D.G (Fin.castLE D.hk a) i)
      = ∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2
    rw [map_sum frob2 (fun a => c a * D.G (Fin.castLE D.hk a) i) Finset.univ]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (c a * D.G (Fin.castLE D.hk a) i) ^ 2
      = c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2
    rw [mul_pow]

/-- Distributes the square or fourth power of a clause-zero linear combination over its
summands. -/
private theorem vPart_pow {m n k : ℕ} (D : TriorthogonalData m n k)
    (d : Fin (m - k) → F1024) (r : ℕ) (hr : r = 4 ∨ r = 2) (i : Fin n) :
    (vPart D d i) ^ r
      = ∑ a', d a' ^ r * clause0Row D a' i ^ r := by
  rcases hr with rfl | rfl
  · show frob4 (∑ a', d a' * clause0Row D a' i) = ∑ a', d a' ^ 4 * clause0Row D a' i ^ 4
    rw [map_sum frob4 (fun a' => d a' * clause0Row D a' i) Finset.univ]
    refine Finset.sum_congr rfl fun a' _ => ?_
    show (d a' * clause0Row D a' i) ^ 4 = d a' ^ 4 * clause0Row D a' i ^ 4
    rw [mul_pow]
  · show frob2 (∑ a', d a' * clause0Row D a' i) = ∑ a', d a' ^ 2 * clause0Row D a' i ^ 2
    rw [map_sum frob2 (fun a' => d a' * clause0Row D a' i) Finset.univ]
    refine Finset.sum_congr rfl fun a' _ => ?_
    show (d a' * clause0Row D a' i) ^ 2 = d a' ^ 2 * clause0Row D a' i ^ 2
    rw [mul_pow]

/-- Shows that a clause-zero row's generator index is at least `k`. -/
private theorem clause0Row_index_val {m k : ℕ} (hk : k ≤ m) (a' : Fin (m - k)) :
    k ≤ ((Fin.cast (by omega) : Fin (k + (m - k)) → Fin m) (Fin.natAdd k a') :
      ℕ) := by
  simp only [Fin.val_natAdd, Fin.val_cast]
  omega

/-- Shows that the sum of seventh powers of a decomposed code vector equals the sum of seventh
powers of its logical coefficients. -/
private theorem seventh_sum_split {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (d : Fin (m - k) → F1024) :
    (∑ i, (rPart D c i + vPart D d i) ^ 7) = ∑ a, c a ^ 7 := by
  have hfinal : ∀ i : Fin n, (rPart D c i + vPart D d i) ^ 7
      = (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)
        + (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)
        + (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)
        + (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)
        + (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a', d a' * clause0Row D a' i) := by
    intro i
    have h1 : (rPart D c i + vPart D d i) ^ 7
        = (rPart D c i + vPart D d i) ^ 4
            * ((rPart D c i + vPart D d i) ^ 2 * (rPart D c i + vPart D d i)) := by
      ring
    rw [h1, add_pow_four, add_pow_two, rPart_pow D c 4 (Or.inl rfl) i,
      rPart_pow D c 2 (Or.inr rfl) i, vPart_pow D d 4 (Or.inl rfl) i,
      vPart_pow D d 2 (Or.inr rfl) i]
    simp only [rPart, vPart]
    ring
  rw [Finset.sum_congr rfl fun i _ => hfinal i]
  simp only [Finset.sum_add_distrib]

  have e1 : (∑ i, (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)) = ∑ a, c a ^ 7 := by
    rw [prod3_sums (fun (a : Fin k) (i : Fin n) =>
        c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
      (fun (b : Fin k) (i : Fin n) => c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
      (fun (e : Fin k) (i : Fin n) => c e * D.G (Fin.castLE D.hk e) i)]
    have stepB : ∀ (a b e : Fin k), ∑ i, (c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
          * (c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
          * (c e * D.G (Fin.castLE D.hk e) i)
        = if a = b ∧ b = e then c a ^ 4 * c b ^ 2 * c e else 0 := by
      intro a b e
      rw [pull3 (c a ^ 4) (c b ^ 2) (c e)
        (fun i => D.G (Fin.castLE D.hk a) i ^ 4)
        (fun i => D.G (Fin.castLE D.hk b) i ^ 2)
        (fun i => D.G (Fin.castLE D.hk e) i), triTriple_rows D a b e, mul_ite,
        mul_one, mul_zero]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => stepB a b e,
      diag3_collapse (fun a b e => c a ^ 4 * c b ^ 2 * c e)]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : (∑ i, (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)) = 0 := by
    rw [prod3_sums (fun (a : Fin k) (i : Fin n) =>
        c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
      (fun (b : Fin k) (i : Fin n) => c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' * clause0Row D a' i)]
    have stepB : ∀ (a b : Fin k) (a' : Fin (m - k)),
        ∑ i, (c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
          * (c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
          * (d a' * clause0Row D a' i) = 0 := by
      intro a b a'
      rw [pull3 (c a ^ 4) (c b ^ 2) (d a')
        (fun i => D.G (Fin.castLE D.hk a) i ^ 4)
        (fun i => D.G (Fin.castLE D.hk b) i ^ 2)
        (fun i => clause0Row D a' i)]
      have h0 := triTriple_zero_of_ge D (Fin.castLE D.hk a) (Fin.castLE D.hk b)
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a'))
        (Or.inr (Or.inr (clause0Row_index_val D.hk a')))
      rw [show (∑ i, D.G (Fin.castLE D.hk a) i ^ 4 * D.G (Fin.castLE D.hk b) i ^ 2
        * clause0Row D a' i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun a' _ => stepB a b a'
  have e3 : (∑ i, (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)) = 0 := by
    rw [prod3_sums (fun (a : Fin k) (i : Fin n) =>
        c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' ^ 2 * clause0Row D a' i ^ 2)
      (fun (e : Fin k) (i : Fin n) => c e * D.G (Fin.castLE D.hk e) i)]
    have stepB : ∀ (a e : Fin k) (a' : Fin (m - k)),
        ∑ i, (c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
          * (d a' ^ 2 * clause0Row D a' i ^ 2)
          * (c e * D.G (Fin.castLE D.hk e) i) = 0 := by
      intro a e a'
      rw [pull3 (c a ^ 4) (d a' ^ 2) (c e)
        (fun i => D.G (Fin.castLE D.hk a) i ^ 4)
        (fun i => clause0Row D a' i ^ 2)
        (fun i => D.G (Fin.castLE D.hk e) i)]
      have h0 := triTriple_zero_of_ge D (Fin.castLE D.hk a)
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a'))
        (Fin.castLE D.hk e)
        (Or.inr (Or.inl (clause0Row_index_val D.hk a')))
      rw [show (∑ i, D.G (Fin.castLE D.hk a) i ^ 4 * clause0Row D a' i ^ 2
        * D.G (Fin.castLE D.hk e) i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ =>
      Finset.sum_eq_zero fun e _ => stepB a e a'
  have e4 : (∑ i, (∑ a, c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)) = 0 := by
    rw [prod3_sums (fun (a : Fin k) (i : Fin n) =>
        c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' ^ 2 * clause0Row D a' i ^ 2)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' * clause0Row D a' i)]
    have stepB : ∀ (a : Fin k) (a₁ a₂ : Fin (m - k)),
        ∑ i, (c a ^ 4 * D.G (Fin.castLE D.hk a) i ^ 4)
          * (d a₁ ^ 2 * clause0Row D a₁ i ^ 2)
          * (d a₂ * clause0Row D a₂ i) = 0 := by
      intro a a₁ a₂
      rw [pull3 (c a ^ 4) (d a₁ ^ 2) (d a₂)
        (fun i => D.G (Fin.castLE D.hk a) i ^ 4)
        (fun i => clause0Row D a₁ i ^ 2)
        (fun i => clause0Row D a₂ i)]
      have h0 := triTriple_zero_of_ge D (Fin.castLE D.hk a)
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₁))
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₂))
        (Or.inr (Or.inl (clause0Row_index_val D.hk a₁)))
      rw [show (∑ i, D.G (Fin.castLE D.hk a) i ^ 4 * clause0Row D a₁ i ^ 2
        * clause0Row D a₂ i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a₁ _ =>
      Finset.sum_eq_zero fun a₂ _ => stepB a a₁ a₂
  have e5 : (∑ i, (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)) = 0 := by
    rw [prod3_sums (fun (a' : Fin (m - k)) (i : Fin n) =>
        d a' ^ 4 * clause0Row D a' i ^ 4)
      (fun (b : Fin k) (i : Fin n) => c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
      (fun (e : Fin k) (i : Fin n) => c e * D.G (Fin.castLE D.hk e) i)]
    have stepB : ∀ (b e : Fin k) (a' : Fin (m - k)),
        ∑ i, (d a' ^ 4 * clause0Row D a' i ^ 4)
          * (c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
          * (c e * D.G (Fin.castLE D.hk e) i) = 0 := by
      intro b e a'
      rw [pull3 (d a' ^ 4) (c b ^ 2) (c e)
        (fun i => clause0Row D a' i ^ 4)
        (fun i => D.G (Fin.castLE D.hk b) i ^ 2)
        (fun i => D.G (Fin.castLE D.hk e) i)]
      have h0 := triTriple_zero_of_ge D
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a'))
        (Fin.castLE D.hk b) (Fin.castLE D.hk e)
        (Or.inl (clause0Row_index_val D.hk a'))
      rw [show (∑ i, clause0Row D a' i ^ 4 * D.G (Fin.castLE D.hk b) i ^ 2
        * D.G (Fin.castLE D.hk e) i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun e _ => stepB b e a'
  have e6 : (∑ i, (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a, c a ^ 2 * D.G (Fin.castLE D.hk a) i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)) = 0 := by
    rw [prod3_sums (fun (a' : Fin (m - k)) (i : Fin n) =>
        d a' ^ 4 * clause0Row D a' i ^ 4)
      (fun (b : Fin k) (i : Fin n) => c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' * clause0Row D a' i)]
    have stepB : ∀ (b : Fin k) (a₁ a₂ : Fin (m - k)),
        ∑ i, (d a₁ ^ 4 * clause0Row D a₁ i ^ 4)
          * (c b ^ 2 * D.G (Fin.castLE D.hk b) i ^ 2)
          * (d a₂ * clause0Row D a₂ i) = 0 := by
      intro b a₁ a₂
      rw [pull3 (d a₁ ^ 4) (c b ^ 2) (d a₂)
        (fun i => clause0Row D a₁ i ^ 4)
        (fun i => D.G (Fin.castLE D.hk b) i ^ 2)
        (fun i => clause0Row D a₂ i)]
      have h0 := triTriple_zero_of_ge D
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₁))
        (Fin.castLE D.hk b)
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₂))
        (Or.inl (clause0Row_index_val D.hk a₁))
      rw [show (∑ i, clause0Row D a₁ i ^ 4 * D.G (Fin.castLE D.hk b) i ^ 2
        * clause0Row D a₂ i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun a₂ _ => stepB b a₁ a₂
  have e7 : (∑ i, (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a, c a * D.G (Fin.castLE D.hk a) i)) = 0 := by
    rw [prod3_sums (fun (a' : Fin (m - k)) (i : Fin n) =>
        d a' ^ 4 * clause0Row D a' i ^ 4)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' ^ 2 * clause0Row D a' i ^ 2)
      (fun (e : Fin k) (i : Fin n) => c e * D.G (Fin.castLE D.hk e) i)]
    have stepB : ∀ (e : Fin k) (a₁ a₂ : Fin (m - k)),
        ∑ i, (d a₁ ^ 4 * clause0Row D a₁ i ^ 4)
          * (d a₂ ^ 2 * clause0Row D a₂ i ^ 2)
          * (c e * D.G (Fin.castLE D.hk e) i) = 0 := by
      intro e a₁ a₂
      rw [pull3 (d a₁ ^ 4) (d a₂ ^ 2) (c e)
        (fun i => clause0Row D a₁ i ^ 4)
        (fun i => clause0Row D a₂ i ^ 2)
        (fun i => D.G (Fin.castLE D.hk e) i)]
      have h0 := triTriple_zero_of_ge D
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₁))
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₂))
        (Fin.castLE D.hk e)
        (Or.inl (clause0Row_index_val D.hk a₁))
      rw [show (∑ i, clause0Row D a₁ i ^ 4 * clause0Row D a₂ i ^ 2
        * D.G (Fin.castLE D.hk e) i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun a₂ _ =>
      Finset.sum_eq_zero fun e _ => stepB e a₁ a₂
  have e8 : (∑ i, (∑ a', d a' ^ 4 * clause0Row D a' i ^ 4)
            * (∑ a', d a' ^ 2 * clause0Row D a' i ^ 2)
            * (∑ a', d a' * clause0Row D a' i)) = 0 := by
    rw [prod3_sums (fun (a' : Fin (m - k)) (i : Fin n) =>
        d a' ^ 4 * clause0Row D a' i ^ 4)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' ^ 2 * clause0Row D a' i ^ 2)
      (fun (a' : Fin (m - k)) (i : Fin n) => d a' * clause0Row D a' i)]
    have stepB : ∀ (a₁ a₂ a₃ : Fin (m - k)),
        ∑ i, (d a₁ ^ 4 * clause0Row D a₁ i ^ 4)
          * (d a₂ ^ 2 * clause0Row D a₂ i ^ 2)
          * (d a₃ * clause0Row D a₃ i) = 0 := by
      intro a₁ a₂ a₃
      rw [pull3 (d a₁ ^ 4) (d a₂ ^ 2) (d a₃)
        (fun i => clause0Row D a₁ i ^ 4)
        (fun i => clause0Row D a₂ i ^ 2)
        (fun i => clause0Row D a₃ i)]
      have h0 := triTriple_zero_of_ge D
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₁))
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₂))
        ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k a₃))
        (Or.inl (clause0Row_index_val D.hk a₁))
      rw [show (∑ i, clause0Row D a₁ i ^ 4 * clause0Row D a₂ i ^ 2
        * clause0Row D a₃ i) = 0 from h0, mul_zero]
    exact Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun a₂ _ =>
      Finset.sum_eq_zero fun a₃ _ => stepB a₁ a₂ a₃
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  simp

/-- Evaluates the complex exponential at twice pi times the imaginary unit as one. -/
private theorem expIpi_two : Complex.exp (Complex.I * Real.pi * 2) = 1 := by
  rw [show Complex.I * Real.pi * 2 = 2 * Real.pi * Complex.I from by ring,
    Complex.exp_mul_I]
  norm_num [Real.cos_two_pi, Real.sin_two_pi]

/-- Evaluates the complex exponential at pi times the imaginary unit as minus one. -/
private theorem expIpi_one : Complex.exp (Complex.I * Real.pi * (1 : ℝ)) = -1 := by
  rw [show Complex.I * Real.pi * (1 : ℝ) = Real.pi * Complex.I from by push_cast; ring,
    Complex.exp_mul_I]
  norm_num [Real.cos_pi, Real.sin_pi]

/-- Cancels two occurrences of the same summand in `F1024`. -/
private theorem char2_add_add_cancel (a b : F1024) : a + (b + a) = b := by
  have h : (2 : F1024) = 0 := CharTwo.two_eq_zero
  linear_combination h * a

/-- Shows that every element of `F1024` added to itself is zero. -/
private theorem char2_add_self (a : F1024) : a + a = 0 := by
  have h : (2 : F1024) = 0 := CharTwo.two_eq_zero
  linear_combination h * a

/-- Shows that adding two to an integer multiple of pi leaves its complex exponential unchanged. -/
private theorem expIpi_two_mul (n : ℕ) :
    Complex.exp (Complex.I * Real.pi * ((n + 2 : ℕ) : ℝ))
      = Complex.exp (Complex.I * Real.pi * ((n : ℕ) : ℝ)) := by
  have h : Complex.I * Real.pi * ((n + 2 : ℕ) : ℝ)
      = Complex.I * Real.pi * ((n : ℕ) : ℝ) + Complex.I * Real.pi * 2 := by
    push_cast
    ring
  rw [h, Complex.exp_add, expIpi_two, mul_one]

/-- Evaluates the exponential of a natural multiple of pi times the imaginary unit according to
its parity. -/
private theorem expIpi_nat : ∀ n : ℕ,
    Complex.exp (Complex.I * Real.pi * (n : ℝ))
      = if n % 2 = 0 then (1 : ℂ) else -1 := by
  intro n
  match n with
  | 0 => simp
  | 1 => rw [show ((1 : ℕ) : ℝ) = 1 from by norm_num, expIpi_one]; norm_num
  | (m + 2) =>
    rw [expIpi_two_mul m, expIpi_nat m,
      show (m + 2) % 2 = m % 2 from by omega]

/-- Computes the representative of a sum modulo two as the sum of representatives reduced modulo
two. -/
private theorem zmod2_val_sum {n : ℕ} (v : Fin n → ZMod 2) :
    ((∑ j, v j : ZMod 2)).val = (∑ j, (v j).val) % 2 := by
  have h : (∑ j, v j : ZMod 2) = ((∑ j, (v j).val : ℕ) : ZMod 2) := by
    refine Eq.trans (Finset.sum_congr rfl fun j _ =>
      (ZMod.natCast_zmod_val (v j)).symm) ?_
    exact (map_sum (Nat.castRingHom (ZMod 2)) (fun j => (v j).val)
      Finset.univ).symm
  rw [h, ZMod.val_natCast]

/-- Characterizes logical coset membership by translation into `triG0` using `rPart`. -/
private theorem mem_triCoset_iff {m n k : ℕ} (D : TriorthogonalData m n k)
    (u : Fin k → F1024) (x : Fin n → F1024) :
    x ∈ triCoset D u
      ↔ x + rPart D u ∈ triG0 D := by
  constructor
  · rintro ⟨g, hg, hxg⟩
    have hfun : x + rPart D u = g := by
      funext i
      have h2 : x i = (∑ a, u a * D.G (Fin.castLE D.hk a) i) + g i := by
        have hbeta := congrFun hxg i
        simp only at hbeta
        exact hbeta.symm
      simp only [Pi.add_apply, rPart, h2]
      calc (∑ a, u a * D.G (Fin.castLE D.hk a) i) + g i
            + (∑ a, u a * D.G (Fin.castLE D.hk a) i)
          = (∑ a, u a * D.G (Fin.castLE D.hk a) i)
              + (g i + ∑ a, u a * D.G (Fin.castLE D.hk a) i) := add_assoc _ _ _
        _ = g i := char2_add_add_cancel _ _
    rw [hfun]
    exact hg
  · intro h
    refine ⟨x + rPart D u, h, ?_⟩
    funext i
    simp only [Pi.add_apply, rPart]
    calc (∑ a, u a * D.G (Fin.castLE D.hk a) i) + (x i
            + ∑ a, u a * D.G (Fin.castLE D.hk a) i)
        = x i + ((∑ a, u a * D.G (Fin.castLE D.hk a) i)
            + ∑ a, u a * D.G (Fin.castLE D.hk a) i) := by ring
      _ = x i + 0 := by rw [char2_add_self]
      _ = x i := add_zero _

/-- Establishes the transversal gate action specified by `TriorthogonalTransversalGate`. -/
theorem triorthogonalTransversalGate : TriorthogonalTransversalGate := by
  intro m n k D u
  funext x
  have hmul : (tensorDiagGate u1SeventhPhase *ᵥ triCodeword D u) x
      = (∏ j, u1SeventhPhase (x j)) * triCodeword D u x :=
    Matrix.mulVec_diagonal _ _ x
  rw [hmul]
  by_cases hx : x ∈ triCoset D u
  · have hcw : triCodeword D u x = 1 := by
      rw [triCodeword, Set.indicator, ite_eq_left hx]

    obtain ⟨d, hd⟩ := mem_triG0_iff D (x + rPart D u) |>.mp (mem_triCoset_iff D u x |>.mp hx)
    have hdec : ∀ i : Fin n, x i = rPart D u i + vPart D d i := by
      intro i
      have h1 : x i + rPart D u i = vPart D d i := hd i
      rw [← h1]
      exact (char2_add_add_cancel (rPart D u i) (x i)).symm
    have hsum7 : (∑ j, x j ^ 7) = ∑ a, u a ^ 7 := by
      have hsplit := seventh_sum_split D u d
      rw [Finset.sum_congr (M := F1024) rfl fun j _ =>
        (by rw [hdec j] : (rPart D u j + vPart D d j) ^ 7 = x j ^ 7)] at hsplit
      exact hsplit

    have hprod : ∏ j, u1SeventhPhase (x j)
        = Complex.exp (Complex.I * Real.pi
            * ((f1024Trace (∑ a, u a ^ 7)).val : ℝ)) := by
      have htr : f1024Trace (∑ a, u a ^ 7) = ∑ j, f1024Trace (x j ^ 7) := by
        rw [← hsum7]
        exact map_sum (Algebra.trace (ZMod 2) F1024) (fun j => x j ^ 7) Finset.univ
      have hL : ∏ j, u1SeventhPhase (x j)
          = if (∑ j, (f1024Trace (x j ^ 7)).val) % 2 = 0 then (1 : ℂ) else -1 := by
        have hprod2 : ∏ j, u1SeventhPhase (x j)
            = Complex.exp (Complex.I * Real.pi
                * ((∑ j, (f1024Trace (x j ^ 7)).val : ℕ) : ℝ)) := by
          simp only [u1SeventhPhase]
          rw [← Complex.exp_sum, ← Finset.mul_sum (R := ℂ)]
          congr 1
          norm_num [Nat.cast_sum]
        rw [hprod2, expIpi_nat]
      have hR : Complex.exp (Complex.I * Real.pi
            * ((f1024Trace (∑ a, u a ^ 7)).val : ℝ))
          = if (∑ j, (f1024Trace (x j ^ 7)).val) % 2 = 0 then (1 : ℂ) else -1 := by
        rw [expIpi_nat, htr, zmod2_val_sum]
        simp
      rw [hL, hR]
    rw [hcw, mul_one, Pi.smul_apply, smul_eq_mul, hcw, mul_one, hprod]
  · have hcw : triCodeword D u x = 0 := by
      rw [triCodeword, Set.indicator, ite_eq_right hx]
    rw [hcw, Pi.smul_apply, smul_eq_mul, hcw]
    ring

end Qatlib.Papers.MagicDistill24.Triorthogonal
