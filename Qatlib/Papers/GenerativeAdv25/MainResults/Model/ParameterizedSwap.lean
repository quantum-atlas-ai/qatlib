/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenerativeAdv25.MainResults.Model.FiniteLaws
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — permutation matrices, `e^{iθ SWAP}` gates and the three-layer
parameterized SWAP circuit (Proposition 2)

Fixed paper version: arXiv:2509.09033v1, Appendix G.1.a, Eqs. (S.1.3)–(S.1.11).

The paper's Proposition 2 constructs a parameterized circuit

`U(θ) = ∏_j e^{i θ₁ⱼ SWAP_{2j+1,2j+2}} · ∏_j e^{i θ₂ⱼ SWAP_{2j,2j+1}} · ∏_j e^{i θ₃ⱼ SWAP_{2j+1,2j+2}}`

and shows that at `θ*` (all block parameters `π/2`, all inter-block link parameters `0`) it
implements `U_S = ∏_{j∈S} SWAP_{4j+1,4j+4}`.

Lean model:

* `QOp X` — square complex matrices on a finite index type `X`;
* `permMat σ` — the permutation matrix of `σ : Equiv.Perm X`, with
  `permMat_mul : permMat σ * permMat τ = permMat (σ * τ)`;
* `swapPerm i j` — the permutation of `Bit n` induced by the coordinate swap `i ↔ j`;
* `gate θ σ = cos θ • 1 + (I * sin θ) • permMat σ`, the paper's `e^{iθ SWAP}` for an
  involution `σ` (at `θ = π/2` this is `I • permMat σ`);
* `blockCircuit` — the five gates of one `4`-qubit block (three layers, with the inter-block
  link parameter set to zero, exactly as in the paper's parameter configuration `θ*`);
* `paperBlock j = (4j, 4j+1, 4j+2, 4j+3)` for `j < n / 4`;
* `multiBlockCircuit S θ` — the product of the block circuits over the blocks in the list `S`
  (which enumerates the paper's index set `S`).

The key algebraic identity, proved in `swapBlockIdentity`, is

`(s_ab * s_cd) * s_bc * (s_ab * s_cd) = s_ad`

for distinct `a, b, c, d`: the five nearest-neighbour SWAPs of a block compose to the
long-range SWAP `a ↔ d` (Eq. (S.1.5)–(S.1.6)).

Matrix products are taken with `List.prod` (a product in a possibly noncommutative monoid),
since `Finset.prod` requires a commutative monoid and matrices over `ℂ` are not commutative.
The paper's index set `S` is represented by a `Nodup` list.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GenerativeAdv25.MainResults

/-- Square complex matrices on a finite index type. -/
abbrev QOp (X : Type*) [Fintype X] [DecidableEq X] := Matrix X X ℂ

/-- The permutation matrix of `σ`. -/
def permMat {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) : QOp X :=
  fun i j => if σ j = i then (1 : ℂ) else 0

/-- Permutation matrices compose along the group product. -/
theorem permMat_mul {X : Type*} [Fintype X] [DecidableEq X]
    (σ τ : Equiv.Perm X) : permMat σ * permMat τ = permMat (σ * τ) := by
  ext i j
  simp only [Matrix.mul_apply, permMat, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    have h : τ j ≠ k := fun h => hk h.symm
    simp [h]
  · intro h; exact (h (Finset.mem_univ (τ j))).elim

/-- The identity permutation matrix. -/
theorem permMat_one {X : Type*} [Fintype X] [DecidableEq X] :
    permMat (1 : Equiv.Perm X) = (1 : QOp X) := by
  ext i j
  simp only [permMat, Matrix.one_apply, Equiv.Perm.coe_one, id_eq]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Product of permutation matrices is the permutation matrix of the product. -/
theorem permMat_listProd {X ι : Type*} [Fintype X] [DecidableEq X]
    (l : List ι) (σ : ι → Equiv.Perm X) :
    (l.map (fun i => permMat (σ i))).prod = permMat ((l.map σ).prod) := by
  induction l with
  | nil => simp [permMat_one]
  | cons a l ih => simp [ih, permMat_mul]

/-- Scalar multiplication is compatible with matrix multiplication. -/
theorem smul_mul_smul {X : Type*} [Fintype X] [DecidableEq X]
    (c d : ℂ) (A B : QOp X) : (c • A) * (d • B) = (c * d) • (A * B) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- A product of uniformly scaled matrices over a list. -/
theorem listProd_smul_permMat {X ι : Type*} [Fintype X] [DecidableEq X]
    (l : List ι) (c : ι → ℂ) (σ : ι → Equiv.Perm X) :
    (l.map (fun i => c i • permMat (σ i))).prod
      = (l.map c).prod • permMat ((l.map σ).prod) := by
  induction l with
  | nil => simp [permMat_one]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, ih, smul_mul_smul, permMat_mul]

/-- A constant product of scalars. -/
theorem listProd_const_complex {ι : Type*} (l : List ι) (c : ℂ) :
    (l.map (fun _ => c)).prod = c ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [pow_succ, mul_comm]

/-- The permutation of `Bit n` induced by the coordinate transposition `i ↔ j`
(precomposition with the coordinate swap). -/
def swapPerm {n : ℕ} (i j : Fin n) : Equiv.Perm (Bit n) :=
  Equiv.arrowCongr (Equiv.swap i j) (Equiv.refl Bool)

/-- `swapPerm` is a homomorphism from coordinate permutations to permutations of `Bit n`. -/
theorem swapPerm_mul {n : ℕ} (e₁ e₂ : Equiv.Perm (Fin n)) :
    Equiv.arrowCongr e₁ (Equiv.refl Bool) * Equiv.arrowCongr e₂ (Equiv.refl Bool)
      = Equiv.arrowCongr (e₁ * e₂) (Equiv.refl Bool) := by
  ext b k
  simp [Equiv.arrowCongr, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-- **Eqs. (S.1.5)–(S.1.6):** five nearest-neighbour SWAPs compose to the long-range SWAP
`a ↔ d`, for four distinct indices. -/
theorem swapBlockIdentity {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap c d) * Equiv.swap b c * (Equiv.swap a b * Equiv.swap c d)
      = Equiv.swap a d := by
  set p : Equiv.Perm α := Equiv.swap a b
  set q : Equiv.Perm α := Equiv.swap c d
  set r : Equiv.Perm α := Equiv.swap b c
  have hcomm : Commute p q := by
    apply Equiv.Perm.Disjoint.commute
    apply Equiv.Perm.disjoint_swap_swap
    simp [hab, hac, had, hbc, hbd, hcd]
  have hq : q * r * q = Equiv.swap b d := by
    have h := Equiv.swap_mul_swap_mul_swap (x := b) (y := c) (z := d) hbc hbd
    simpa [q, r, Equiv.swap_comm] using h
  have h1 : p * q * r * p * q = p * (q * r * q) * p := by
    calc
      p * q * r * p * q = p * (q * (r * (p * q))) := by group
      _ = p * (q * (r * (q * p))) := by rw [hcomm.eq]
      _ = p * (q * r * q) * p := by group
  have h2 : p * Equiv.swap b d * p = Equiv.swap a d := by
    have hms := Equiv.mul_swap_eq_swap_mul p b d
    calc
      p * Equiv.swap b d * p = (Equiv.swap (p b) (p d) * p) * p := by rw [hms]
      _ = Equiv.swap (p b) (p d) * (p * p) := by group
      _ = Equiv.swap (p b) (p d) := by rw [Equiv.swap_mul_self]; simp
      _ = Equiv.swap a d := by
        have hpb : p b = a := by simp [p, Equiv.swap_apply_right]
        have hpd : p d = d := by
          simp [p, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
        rw [hpb, hpd]
  calc
    (Equiv.swap a b * Equiv.swap c d) * Equiv.swap b c
        * (Equiv.swap a b * Equiv.swap c d) = p * q * r * p * q := by
          simp only [p, q, r]; group
    _ = p * (q * r * q) * p := h1
    _ = p * Equiv.swap b d * p := by rw [hq]
    _ = Equiv.swap a d := h2

/-- The same identity in fully left-associated form, matching the product of gate
permutations in `blockCircuit`. -/
theorem swapBlockIdentity' {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d * Equiv.swap b c * Equiv.swap a b * Equiv.swap c d
      = Equiv.swap a d := by
  rw [← swapBlockIdentity hab hac had hbc hbd hcd]
  group

/-- The paper's gate `e^{iθ SWAP}` for an involutive permutation `σ`:
`cos θ • 1 + (I * sin θ) • permMat σ` (Eq. (S.1.4)). -/
def gate {n : ℕ} (θ : ℝ) (σ : Equiv.Perm (Bit n)) : QOp (Bit n) :=
  (Real.cos θ : ℂ) • (1 : QOp (Bit n)) + (Complex.I * (Real.sin θ : ℂ)) • permMat σ

/-- At `θ = π/2` the gate is `I • permMat σ`. -/
theorem gate_pi_div_two {n : ℕ} (σ : Equiv.Perm (Bit n)) :
    gate (Real.pi / 2) σ = Complex.I • permMat σ := by
  rw [gate, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The four qubits of a block, named as in the proof of Theorem 9 (one-based `4j+1` to
`4j+4` in the paper). -/
structure Block4 (n : ℕ) where
  /-- First qubit of the block. -/
  a : Fin n
  /-- Second qubit of the block. -/
  b : Fin n
  /-- Third qubit of the block. -/
  c : Fin n
  /-- Fourth qubit of the block. -/
  d : Fin n

/-- The coordinate permutations of the five gates in one block, in circuit order: layer 1
(`a↔b`, `c↔d`), layer 2 (`b↔c`), layer 3 (`a↔b`, `c↔d`). -/
def blockGateCoord {n : ℕ} (B : Block4 n) : Fin 5 → Equiv.Perm (Fin n)
  | 0 => Equiv.swap B.a B.b
  | 1 => Equiv.swap B.c B.d
  | 2 => Equiv.swap B.b B.c
  | 3 => Equiv.swap B.a B.b
  | 4 => Equiv.swap B.c B.d

/-- The corresponding permutations of `Bit n`. -/
def blockGatePerm {n : ℕ} (B : Block4 n) : Fin 5 → Equiv.Perm (Bit n) :=
  fun i => Equiv.arrowCongr (blockGateCoord B i) (Equiv.refl Bool)

/-- One block of the three-layer parameterized SWAP circuit, Eq. (S.1.4), with the inter-block
link parameter fixed to zero: the five gates written in circuit order. -/
def blockCircuit {n : ℕ} (B : Block4 n) (θ : Fin 5 → ℝ) : QOp (Bit n) :=
  gate (θ 0) (blockGatePerm B 0) * gate (θ 1) (blockGatePerm B 1)
    * gate (θ 2) (blockGatePerm B 2) * gate (θ 3) (blockGatePerm B 3)
    * gate (θ 4) (blockGatePerm B 4)

/-- The product of the five block gate permutations is the long-range SWAP `a ↔ d`. -/
theorem blockGatePerm_prod {n : ℕ} (B : Block4 n)
    (hab : B.a ≠ B.b) (hac : B.a ≠ B.c) (had : B.a ≠ B.d)
    (hbc : B.b ≠ B.c) (hbd : B.b ≠ B.d) (hcd : B.c ≠ B.d) :
    blockGatePerm B 0 * blockGatePerm B 1 * blockGatePerm B 2 * blockGatePerm B 3
        * blockGatePerm B 4 = swapPerm B.a B.d := by
  simp only [blockGatePerm, blockGateCoord, swapPerm]
  simp only [swapPerm_mul]
  congr 1
  exact swapBlockIdentity' hab hac had hbc hbd hcd

/-- **Proposition 2, block level:** at `θ*` (all five block angles `π/2`) the block circuit
is `I^5 • SWAP_{a,d}`. -/
theorem blockCircuit_pi {n : ℕ} (B : Block4 n)
    (hab : B.a ≠ B.b) (hac : B.a ≠ B.c) (had : B.a ≠ B.d)
    (hbc : B.b ≠ B.c) (hbd : B.b ≠ B.d) (hcd : B.c ≠ B.d) :
    blockCircuit B (fun _ => Real.pi / 2)
      = (Complex.I ^ 5) • permMat (swapPerm B.a B.d) := by
  unfold blockCircuit
  rw [gate_pi_div_two, gate_pi_div_two, gate_pi_div_two, gate_pi_div_two, gate_pi_div_two]
  simp only [smul_mul_smul, permMat_mul]
  rw [show Complex.I * Complex.I * Complex.I * Complex.I * Complex.I = Complex.I ^ 5 by ring,
    blockGatePerm_prod B hab hac had hbc hbd hcd]

/-- The block indexed by `j`: qubits `4j, 4j+1, 4j+2, 4j+3` (zero-based). -/
def paperBlock (n : ℕ) (j : Fin (n / 4)) : Block4 n where
  a := ⟨4 * j.val, by
    have h := Nat.div_mul_le_self n 4
    omega⟩
  b := ⟨4 * j.val + 1, by
    have h := Nat.div_mul_le_self n 4
    omega⟩
  c := ⟨4 * j.val + 2, by
    have h := Nat.div_mul_le_self n 4
    omega⟩
  d := ⟨4 * j.val + 3, by
    have h := Nat.div_mul_le_self n 4
    omega⟩

/-- The target unitary `U_S = ∏_{j∈S} SWAP_{4j+1,4j+4}` (Eq. (S.1.3)), for the list `S`
enumerating the paper's index set. -/
def targetUnitary (n : ℕ) (S : List (Fin (n / 4))) : QOp (Bit n) :=
  permMat ((S.map (fun j => swapPerm (paperBlock n j).a (paperBlock n j).d)).prod)

/-- The three-layer parameterized SWAP circuit restricted to the blocks in `S`, with all
inter-block link parameters zero. -/
def multiBlockCircuit (n : ℕ) (S : List (Fin (n / 4)))
    (θ : Fin (n / 4) → Fin 5 → ℝ) : QOp (Bit n) :=
  (S.map (fun j => blockCircuit (paperBlock n j) (θ j))).prod

/-- The paper's parameter configuration `θ*`: every block parameter is `π/2`. -/
def thetaStar (n : ℕ) : Fin (n / 4) → Fin 5 → ℝ := fun _ _ => Real.pi / 2

/-- **Proposition 2 (Eqs. (S.1.3)–(S.1.11)):** there exists a parameter configuration `θ*`
such that the three-layer parameterized SWAP circuit implements the target unitary `U_S`, up
to the unit-modulus global phase `I^(5|S|)` generated by the five `e^{i(π/2) SWAP}` gates in
each block.  The paper writes the identity without the global phase; the phase is physically
irrelevant and is recorded explicitly here. -/
theorem proposition2_implementation (n : ℕ) (S : List (Fin (n / 4))) (_hS : S.Nodup) :
    ∃ θ : Fin (n / 4) → Fin 5 → ℝ,
      multiBlockCircuit n S θ = (Complex.I ^ (5 * S.length)) • targetUnitary n S := by
  refine ⟨thetaStar n, ?_⟩
  unfold multiBlockCircuit thetaStar
  rw [show (S.map (fun j => blockCircuit (paperBlock n j) (fun _ => Real.pi / 2)))
        = (S.map (fun j => (Complex.I ^ 5)
            • permMat (swapPerm (paperBlock n j).a (paperBlock n j).d))) by
      apply List.map_congr_left
      intro j _
      exact blockCircuit_pi (paperBlock n j) (by simp [paperBlock]) (by simp [paperBlock])
        (by simp [paperBlock]) (by simp [paperBlock]) (by simp [paperBlock])
        (by simp [paperBlock])]
  rw [listProd_smul_permMat, listProd_const_complex, ← pow_mul]
  rfl

end Qatlib.Papers.GenerativeAdv25.MainResults
