/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SignedWtEnum99.MainResults.Readout
import Qatlib.Papers.SignedWtEnum99.MainResults.Factorization

/-!
# Pauli product expansions and signed weight enumerators

`gateProd` expands products of the matrices `gate b = (4 / 5) • 1 + (3 / 5) • sMat b` using
binary choices of Pauli factors. The phase is expressed by the strictly lower triangular part of
`gram`, and the vacuum entry and trace are rewritten as the signed enumerators `qsen` and
`qsen2`. See [KnillLaflamme1999] for the source development.

## Main statements

* `gateProd_eq_expansion`: expresses the product as a finite Pauli sum with normalization `5⁻ᴺ`.
* `gateProd_vacuum_eq_qsen`: identifies the vacuum entry with a normalized `qsen` value.
* `trace_gateProd_eq_qsen2`: identifies the trace with a normalized two-constraint enumerator.

## References

* [Knill and Laflamme, 1999][KnillLaflamme1999]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

open Pauli

variable {n : ℕ}

/-- The binary linear combination of a family of Pauli pair-vectors with coefficient vector `a`. -/
def pauliSum {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) : PV n :=
  ∑ j : Fin N, a j • b j

/-- The matrix whose entry at `j, k` is the binary bilinear pairing `bform (b j) (b k)`. -/
def gram {N : ℕ} (b : Fin N → PV n) : Matrix (Fin N) (Fin N) (ZMod 2) :=
  fun j k => bform (b j) (b k)

/-- The binary quadratic phase obtained by summing `a j * a k * bform (b j) (b k)` over `k < j`. -/
def triForm {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) : ZMod 2 :=
  ∑ j : Fin N, ∑ k : Fin N, if k < j then a j * a k * bform (b j) (b k) else 0

/-- The triangular phase equals the quadratic form of the strictly lower triangular part of
`gram b`. -/
lemma triForm_eq_quadForm {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    triForm b a = quadForm (lwtr (gram b)) a := by
  simp only [triForm, quadForm, lwtr, gram, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k < j
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-- The Hamming weight of a binary vector of length `N` is at most `N`. -/
lemma bitWeight_le {N : ℕ} (a : Fin N → ZMod 2) : bitWeight a ≤ N := by
  unfold bitWeight
  calc (Finset.univ.filter (fun i => a i = 1)).card
      ≤ (Finset.univ : Finset (Fin N)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by rw [Finset.card_univ, Fintype.card_fin]

/-- The Hamming weight is the sum of the indicators that the coordinates equal one. -/
lemma bitWeight_eq_sum {N : ℕ} (a : Fin N → ZMod 2) :
    bitWeight a = ∑ i : Fin N, if a i = 1 then (1 : ℕ) else 0 := by
  unfold bitWeight
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_filter _ _

/-- Appending a bit increases the Hamming weight by one exactly when the appended bit is one. -/
lemma bitWeight_snoc {N : ℕ} (a : Fin N → ZMod 2) (c : ZMod 2) :
    bitWeight (Fin.snoc a c) = bitWeight a + (if c = 1 then 1 else 0) := by
  rw [bitWeight_eq_sum, bitWeight_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => ZMod 2),
    Fin.snoc_last (α := fun _ : Fin (N + 1) => ZMod 2)]

/-- Appending a coefficient separates the Pauli sum into the initial sum and the last
coefficient times the last pair-vector. -/
lemma pauliSum_snoc {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2)
    (c : ZMod 2) :
    pauliSum b (Fin.snoc a c)
      = pauliSum (fun j : Fin N => b j.castSucc) a + c • b (Fin.last N) := by
  simp only [pauliSum, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => ZMod 2),
    Fin.snoc_last (α := fun _ : Fin (N + 1) => ZMod 2)]

/-- For an initial index, the inner triangular sum is unchanged when a final coordinate is
appended. -/
lemma triForm_inner_castSucc {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2)
    (c : ZMod 2) (j : Fin N) :
    (∑ k : Fin (N + 1),
        if k < j.castSucc then
          (Fin.snoc a c : Fin (N + 1) → ZMod 2) j.castSucc *
            (Fin.snoc a c : Fin (N + 1) → ZMod 2) k * bform (b j.castSucc) (b k)
        else 0)
      = ∑ k : Fin N, if k < j then a j * a k * bform (b j.castSucc) (b k.castSucc) else 0 := by
  rw [Fin.sum_univ_castSucc]
  have hlast : ¬ (Fin.last N < j.castSucc) := by
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
    omega
  simp only [hlast, if_false, add_zero, Fin.castSucc_lt_castSucc_iff,
    Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => ZMod 2)]

/-- The last row of the triangular phase is the last bit times its bilinear pairing sum with the
earlier selected vectors. -/
lemma triForm_inner_last {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2)
    (c : ZMod 2) :
    (∑ k : Fin (N + 1),
        if k < Fin.last N then
          (Fin.snoc a c : Fin (N + 1) → ZMod 2) (Fin.last N) *
            (Fin.snoc a c : Fin (N + 1) → ZMod 2) k * bform (b (Fin.last N)) (b k)
        else 0)
      = c * ∑ k : Fin N, a k * bform (b (Fin.last N)) (b k.castSucc) := by
  rw [Fin.sum_univ_castSucc]
  have hlastlast : ¬ (Fin.last N < Fin.last N) := by
    simp only [Fin.lt_def]
    omega
  simp only [hlastlast, if_false, add_zero,
    Fin.snoc_castSucc (α := fun _ : Fin (N + 1) => ZMod 2),
    Fin.snoc_last (α := fun _ : Fin (N + 1) => ZMod 2),
    Fin.castSucc_lt_last, if_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Appending a bit adds its weighted bilinear pairings with the earlier vectors to the
triangular phase. -/
lemma triForm_snoc {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2)
    (c : ZMod 2) :
    triForm b (Fin.snoc a c)
      = triForm (fun j : Fin N => b j.castSucc) a
        + c * ∑ k : Fin N, a k * bform (b (Fin.last N)) (b k.castSucc) := by
  unfold triForm
  rw [Fin.sum_univ_castSucc]
  have hinner : ∀ j : Fin N,
      (∑ k : Fin (N + 1),
          if k < j.castSucc then
            (Fin.snoc a c : Fin (N + 1) → ZMod 2) j.castSucc *
              (Fin.snoc a c : Fin (N + 1) → ZMod 2) k * bform (b j.castSucc) (b k)
          else 0)
        = ∑ k : Fin N, if k < j then a j * a k * bform (b j.castSucc) (b k.castSucc) else 0 :=
    fun j => triForm_inner_castSucc b a c j
  simp only [hinner, triForm_inner_last]

/-- The matrix `(4 / 5) • 1 + (3 / 5) • sMat b` associated with a Pauli pair-vector `b`. -/
def gate (b : PV n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  (4 / 5 : ℂ) • (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) + (3 / 5 : ℂ) • sMat b

/-- The complex expansion coefficient with sign `sgn (triForm b a)` and weight factor `3 ^
bitWeight a * 4 ^ (N - bitWeight a)`. -/
def coef {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) : ℂ :=
  sgn (triForm b a) * (3 : ℂ) ^ bitWeight a * (4 : ℂ) ^ (N - bitWeight a)

/-- The ordered product of the associated gate matrices, with the last indexed gate multiplying
on the left. -/
def gateProd {n : ℕ} :
    (N : ℕ) → (Fin N → PV n) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ
  | 0, _ => 1
  | N + 1, b => gate (b (Fin.last N)) * gateProd N (fun j : Fin N => b j.castSucc)

/-- Pairing a fixed vector with a binary linear combination distributes over the sum and its
coefficients. -/
lemma bform_sum_smul {N : ℕ} (x : PV n) (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    bform x (∑ j : Fin N, a j • b j) = ∑ j : Fin N, a j * bform x (b j) := by
  simp only [bform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Appending a zero bit multiplies the expansion coefficient by four. -/
lemma coef_snoc_zero {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2) :
    coef b (Fin.snoc a (0 : ZMod 2))
      = 4 * coef (fun j : Fin N => b j.castSucc) a := by
  unfold coef
  have hbw : bitWeight (Fin.snoc a (0 : ZMod 2)) = bitWeight a := by
    rw [bitWeight_snoc]; simp
  have htri : triForm b (Fin.snoc a (0 : ZMod 2))
      = triForm (fun j : Fin N => b j.castSucc) a := by
    rw [triForm_snoc]; simp
  rw [hbw, htri]
  have hle := bitWeight_le a
  rw [show N + 1 - bitWeight a = (N - bitWeight a) + 1 by omega, pow_succ]
  ring

/-- Appending a one bit multiplies the expansion coefficient by three and the sign from pairing
the last vector with the earlier Pauli sum. -/
lemma coef_snoc_one {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2) :
    coef b (Fin.snoc a (1 : ZMod 2))
      = 3 * sgn (bform (b (Fin.last N)) (pauliSum (fun j : Fin N => b j.castSucc) a))
          * coef (fun j : Fin N => b j.castSucc) a := by
  unfold coef
  have hbw : bitWeight (Fin.snoc a (1 : ZMod 2)) = bitWeight a + 1 := by
    rw [bitWeight_snoc]; simp
  have htri : triForm b (Fin.snoc a (1 : ZMod 2))
      = triForm (fun j : Fin N => b j.castSucc) a
        + bform (b (Fin.last N)) (pauliSum (fun j : Fin N => b j.castSucc) a) := by
    rw [triForm_snoc, one_mul]
    congr 1
    rw [pauliSum, bform_sum_smul]
  rw [hbw, htri, sgn_mul]
  have hle := bitWeight_le a
  rw [show N + 1 - (bitWeight a + 1) = N - bitWeight a by omega, pow_succ]
  ring

/-- Appending a zero coefficient leaves the matrix of the selected Pauli sum unchanged. -/
lemma sMat_pauliSum_snoc_zero {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2) :
    sMat (pauliSum b (Fin.snoc a (0 : ZMod 2)))
      = sMat (pauliSum (fun j : Fin N => b j.castSucc) a) := by
  rw [pauliSum_snoc]; simp

/-- Appending a one coefficient adds the last pair-vector to the argument of `sMat`. -/
lemma sMat_pauliSum_snoc_one {N : ℕ} (b : Fin (N + 1) → PV n) (a : Fin N → ZMod 2) :
    sMat (pauliSum b (Fin.snoc a (1 : ZMod 2)))
      = sMat (pauliSum (fun j : Fin N => b j.castSucc) a + b (Fin.last N)) := by
  rw [pauliSum_snoc]; simp

/-- The ordered gate product equals `5⁻ᴺ` times the sum of `coef b a • sMat (pauliSum b a)` over
all binary choice vectors. -/
theorem gateProd_eq_expansion {n : ℕ} (N : ℕ) :
    ∀ b : Fin N → PV n,
      gateProd N b = ((1 / 5 : ℂ) ^ N) •
        ∑ a : Fin N → ZMod 2, coef b a • sMat (pauliSum b a) := by
  induction N with
  | zero =>
      intro b
      have hconst : ∀ a : Fin 0 → ZMod 2, coef b a • sMat (pauliSum b a) = 1 := by
        intro a
        have hp : pauliSum b a = 0 := by simp [pauliSum]
        have ht : triForm b a = 0 := by simp [triForm]
        have hb : bitWeight a = 0 := by
          unfold bitWeight
          have hsub : (Finset.univ.filter (fun i : Fin 0 => a i = 1)).card
              ≤ (Finset.univ : Finset (Fin 0)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          have h0 : (Finset.univ : Finset (Fin 0)).card = 0 := by
            rw [Finset.card_univ, Fintype.card_fin]
          omega
        rw [hp]
        unfold coef
        rw [ht, hb]
        simp [sMat_zero, sgn]
      have hsum : (∑ a : Fin 0 → ZMod 2, coef b a • sMat (pauliSum b a)) = 1 := by
        have hsingle : (∑ a : Fin 0 → ZMod 2, coef b a • sMat (pauliSum b a))
            = coef b default • sMat (pauliSum b default) :=
          Finset.sum_eq_single (default : Fin 0 → ZMod 2)
            (fun a _ ha => absurd (Subsingleton.elim a default) ha)
            (fun h => absurd (Finset.mem_univ _) h)
        rw [hsingle]
        exact hconst default
      have hf : gateProd 0 b = (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := rfl
      rw [hf, hsum]
      simp
  | succ N ih =>
      intro b
      have hprod : gateProd (N + 1) b
          = gate (b (Fin.last N)) * gateProd N (fun j : Fin N => b j.castSucc) := rfl
      rw [hprod, ih (fun j : Fin N => b j.castSucc)]
      set S : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
        ∑ a' : Fin N → ZMod 2,
          coef (fun j : Fin N => b j.castSucc) a' •
            sMat (pauliSum (fun j : Fin N => b j.castSucc) a') with hS
      have hz0 : ∀ a' : Fin N → ZMod 2,
          coef b (Fin.snoc a' (0 : ZMod 2)) • sMat (pauliSum b (Fin.snoc a' (0 : ZMod 2)))
            = (4 : ℂ) • (coef (fun j : Fin N => b j.castSucc) a' •
                sMat (pauliSum (fun j : Fin N => b j.castSucc) a')) := by
        intro a'
        rw [coef_snoc_zero, sMat_pauliSum_snoc_zero, smul_smul]
      have hz1 : ∀ a' : Fin N → ZMod 2,
          coef b (Fin.snoc a' (1 : ZMod 2)) • sMat (pauliSum b (Fin.snoc a' (1 : ZMod 2)))
            = (3 : ℂ) • ((coef (fun j : Fin N => b j.castSucc) a' *
                sgn (bform (b (Fin.last N))
                  (pauliSum (fun j : Fin N => b j.castSucc) a'))) •
                sMat (pauliSum (fun j : Fin N => b j.castSucc) a' + b (Fin.last N))) := by
        intro a'
        rw [coef_snoc_one, sMat_pauliSum_snoc_one, smul_smul]
        congr 1
        ring
      have hsplit : (∑ a : Fin (N + 1) → ZMod 2, coef b a • sMat (pauliSum b a))
          = (4 : ℂ) • S
            + (3 : ℂ) • (∑ a' : Fin N → ZMod 2,
                (coef (fun j : Fin N => b j.castSucc) a' *
                  sgn (bform (b (Fin.last N))
                    (pauliSum (fun j : Fin N => b j.castSucc) a'))) •
                  sMat (pauliSum (fun j : Fin N => b j.castSucc) a' + b (Fin.last N))) := by
        have h1 : (∑ a : Fin (N + 1) → ZMod 2, coef b a • sMat (pauliSum b a))
            = ∑ p : ZMod 2 × (Fin N → ZMod 2),
                coef b (Fin.snoc p.2 p.1) • sMat (pauliSum b (Fin.snoc p.2 p.1)) :=
          (Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N + 1) => ZMod 2))
            (fun a => coef b a • sMat (pauliSum b a))).symm
        rw [h1, Fintype.sum_prod_type]
        rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]
        rw [hS, Finset.smul_sum, Finset.smul_sum]
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a' _
        simp only [hz0, hz1]
      have hsMat : sMat (b (Fin.last N)) * S
          = ∑ a' : Fin N → ZMod 2,
              (coef (fun j : Fin N => b j.castSucc) a' *
                sgn (bform (b (Fin.last N))
                  (pauliSum (fun j : Fin N => b j.castSucc) a'))) •
                sMat (pauliSum (fun j : Fin N => b j.castSucc) a' + b (Fin.last N)) := by
        rw [hS, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a' _
        rw [mul_smul_comm, sMat_mul, smul_smul, add_comm]
      have hmain : gate (b (Fin.last N)) * S = (1 / 5 : ℂ) •
          ((4 : ℂ) • S + (3 : ℂ) • (∑ a' : Fin N → ZMod 2,
              (coef (fun j : Fin N => b j.castSucc) a' *
                sgn (bform (b (Fin.last N))
                  (pauliSum (fun j : Fin N => b j.castSucc) a'))) •
                sMat (pauliSum (fun j : Fin N => b j.castSucc) a' + b (Fin.last N)))) := by
        rw [show gate (b (Fin.last N)) =
              (4 / 5 : ℂ) • (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
              + (3 / 5 : ℂ) • sMat (b (Fin.last N)) from rfl,
          add_mul, smul_mul_assoc, Matrix.one_mul, smul_mul_assoc, hsMat]
        rw [smul_add]
        congr 1
        · rw [smul_smul, show (1 / 5 : ℂ) * 4 = 4 / 5 by norm_num]
        · rw [smul_smul, show (1 / 5 : ℂ) * 3 = 3 / 5 by norm_num]
      rw [mul_smul_comm, hmain, smul_smul, ← pow_succ, hsplit]

/-- The matrix of the zero-indexed component in each Pauli coordinate pair, with the
pair-vectors as columns. -/
def evenRows {N : ℕ} (b : Fin N → PV n) : Matrix (Fin n) (Fin N) (ZMod 2) :=
  fun i j => b j (i, 0)

/-- The matrix of the one-indexed component in each Pauli coordinate pair, with the pair-vectors
as columns. -/
def oddRows {N : ℕ} (b : Fin N → PV n) : Matrix (Fin n) (Fin N) (ZMod 2) :=
  fun i j => b j (i, 1)

/-- The pairing matrix factors as the transpose of `evenRows b` times `oddRows b`. -/
lemma gram_eq_transpose_mul {N : ℕ} (b : Fin N → PV n) :
    gram b = (evenRows b)ᵀ * oddRows b := by
  ext j k
  simp [gram, evenRows, oddRows, bform, Matrix.mul_apply]

/-- The Z component of the selected Pauli sum is the matrix-vector product of `evenRows b` with
the choice vector. -/
lemma zpart_pauliSum {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    zpart (pauliSum b a) = (evenRows b).mulVec a := by
  funext i
  simp only [zpart, pauliSum, evenRows, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The X component of the selected Pauli sum is the matrix-vector product of `oddRows b` with
the choice vector. -/
lemma xpart_pauliSum {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    xpart (pauliSum b a) = (oddRows b).mulVec a := by
  funext i
  simp only [xpart, pauliSum, oddRows, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The X component of the selected Pauli sum vanishes exactly when the choice vector is in the
kernel of `oddRows b`. -/
lemma xpart_pauliSum_eq_zero_iff {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    xpart (pauliSum b a) = 0 ↔ (oddRows b).mulVec a = 0 := by
  rw [xpart_pauliSum]

/-- The selected Pauli sum vanishes exactly when both its even-row and odd-row matrix-vector
products vanish. -/
lemma pauliSum_eq_zero_iff {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    pauliSum b a = 0 ↔ (evenRows b).mulVec a = 0 ∧ (oddRows b).mulVec a = 0 := by
  rw [eq_zero_iff_parts, zpart_pauliSum, xpart_pauliSum]

/-- A selected Pauli sum with zero X component has zero Y weight. -/
lemma yWeight_pauliSum_eq_zero_of_xpart_eq_zero {N : ℕ} {b : Fin N → PV n}
    {a : Fin N → ZMod 2} (h : xpart (pauliSum b a) = 0) :
    yWeight (pauliSum b a) = 0 :=
  yWeight_eq_zero_of_isZ ((isZ_iff_xpart _).mpr h)

/-- The vacuum entry of the gate product is the normalized coefficient sum restricted to zero X
component, retaining the explicit Y-weight sign. -/
theorem gateProd_vacuum_aux {n : ℕ} (N : ℕ) (b : Fin N → PV n) :
    gateProd N b 0 0 = (1 / 5 : ℂ) ^ N *
      ∑ a : Fin N → ZMod 2,
        if xpart (pauliSum b a) = 0 then ((-1 : ℂ) ^ yWeight (pauliSum b a)) * coef b a
        else 0 := by
  rw [gateProd_eq_expansion]
  have hsum : (∑ a : Fin N → ZMod 2, coef b a * sMat (pauliSum b a) 0 0)
      = ∑ a : Fin N → ZMod 2,
          if xpart (pauliSum b a) = 0 then
            ((-1 : ℂ) ^ yWeight (pauliSum b a)) * coef b a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [sMat_vacuum]
    by_cases h : xpart (pauliSum b a) = 0 <;> simp [h, mul_comm]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hsum]

/-- The vacuum entry of the gate product is `5⁻ᴺ` times the coefficient sum over the kernel of
`oddRows b`. -/
theorem gateProd_vacuum {n : ℕ} (N : ℕ) (b : Fin N → PV n) :
    gateProd N b 0 0 = (1 / 5 : ℂ) ^ N *
      ∑ a : Fin N → ZMod 2, if (oddRows b).mulVec a = 0 then coef b a else 0 := by
  rw [gateProd_vacuum_aux]
  have hsum : (∑ a : Fin N → ZMod 2,
        if xpart (pauliSum b a) = 0 then
          ((-1 : ℂ) ^ yWeight (pauliSum b a)) * coef b a else 0)
      = ∑ a : Fin N → ZMod 2, if (oddRows b).mulVec a = 0 then coef b a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : xpart (pauliSum b a) = 0
    · rw [if_pos h, if_pos ((xpart_pauliSum_eq_zero_iff b a).mp h),
        yWeight_pauliSum_eq_zero_of_xpart_eq_zero h, pow_zero, one_mul]
    · rw [if_neg h, if_neg (fun hh => h ((xpart_pauliSum_eq_zero_iff b a).mpr hh))]
  rw [hsum]

/-- The complex sign `sgn z` equals the integer sign `sgnZ z` cast to the complex numbers. -/
lemma sgn_eq_intCast_sgnZ (z : ZMod 2) : sgn z = (sgnZ z : ℂ) := by
  unfold sgn sgnZ
  by_cases h : z = 0 <;> simp [h]

/-- Each expansion coefficient is the signed weight-enumerator term for the quadratic form of
`lwtr (gram b)` at weights three and four. -/
lemma coef_eq_qsen_term {N : ℕ} (b : Fin N → PV n) (a : Fin N → ZMod 2) :
    coef b a = (sgnZ (quadForm (lwtr (gram b)) a) : ℂ) * (3 : ℂ) ^ bitWeight a *
      (4 : ℂ) ^ (N - bitWeight a) := by
  unfold coef
  rw [triForm_eq_quadForm, sgn_eq_intCast_sgnZ]

/-- The vacuum entry of the gate product equals `5⁻ᴺ` times `qsen (oddRows b) (lwtr (gram b)) 3
4`, cast to the complex numbers. See [KnillLaflamme1999]. -/
theorem gateProd_vacuum_eq_qsen {n : ℕ} (N : ℕ) (b : Fin N → PV n) :
    gateProd N b 0 0 = (1 / 5 : ℂ) ^ N *
      ((qsen (oddRows b) (lwtr (gram b)) 3 4 : ℤ) : ℂ) := by
  rw [gateProd_vacuum]
  have hcast : ((qsen (oddRows b) (lwtr (gram b)) 3 4 : ℤ) : ℂ)
      = ∑ a : Fin N → ZMod 2, if (oddRows b).mulVec a = 0 then coef b a else 0 := by
    unfold qsen
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : (oddRows b).mulVec a = 0
    · rw [if_pos h, if_pos h, coef_eq_qsen_term]
    · rw [if_neg h, if_neg h]
  rw [hcast]

/-- The trace of the gate product equals `2 ^ n * 5⁻ᴺ` times the two-constraint signed
enumerator for `oddRows b`, `evenRows b`, and `lwtr (gram b)`. See [KnillLaflamme1999]. -/
theorem trace_gateProd_eq_qsen2 {n : ℕ} (N : ℕ) (b : Fin N → PV n) :
    Matrix.trace (gateProd N b) = (2 : ℂ) ^ n * ((1 / 5 : ℂ) ^ N *
      ((qsen2 (oddRows b) (evenRows b) (lwtr (gram b)) 3 4 : ℤ) : ℂ)) := by
  rw [gateProd_eq_expansion]
  simp only [Matrix.trace_smul, smul_eq_mul]
  have htrace : Matrix.trace (∑ a : Fin N → ZMod 2, coef b a • sMat (pauliSum b a))
      = (2 : ℂ) ^ n *
        ∑ a : Fin N → ZMod 2, if pauliSum b a = 0 then coef b a else 0 := by
    simp only [Matrix.trace_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Matrix.trace_smul, smul_eq_mul, trace_sMat]
    by_cases h : pauliSum b a = 0
    · rw [if_pos h, if_pos h, mul_comm]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  rw [htrace]
  have hq : ((qsen2 (oddRows b) (evenRows b) (lwtr (gram b)) 3 4 : ℤ) : ℂ)
      = ∑ a : Fin N → ZMod 2, if pauliSum b a = 0 then coef b a else 0 := by
    unfold qsen2
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : pauliSum b a = 0
    · have h1 : (evenRows b).mulVec a = 0 :=
        ((pauliSum_eq_zero_iff b a).mp h).1
      have h2 : (oddRows b).mulVec a = 0 :=
        ((pauliSum_eq_zero_iff b a).mp h).2
      rw [if_pos ⟨h2, h1⟩, if_pos h, coef_eq_qsen_term]
    · have h' : ¬ ((oddRows b).mulVec a = 0 ∧ (evenRows b).mulVec a = 0) :=
        fun hh => h ((pauliSum_eq_zero_iff b a).mpr ⟨hh.2, hh.1⟩)
      rw [if_neg h', if_neg h]
  rw [hq]
  ring

end Qatlib.Papers.SignedWtEnum99.MainResults
