/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GameTree09.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Matrix
open Classical
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.GameTree09.MainResults

def orSourceBlock {m α β : Type*} (A : Matrix m α ℝ) (B : Matrix m β ℝ) :
    Matrix m (α ⊕ β) ℝ :=
  fun i j => Sum.elim (fun a => A i a) (fun b => B i b) j

def orComposedBlock {m α β : Type*} (δ ε₁ ε₂ : ℝ) (A : Matrix m α ℝ)
    (B : Matrix m β ℝ) : Matrix m (α ⊕ (β ⊕ β)) ℝ :=
  fun i j => match j with
    | Sum.inl a => δ * A i a
    | Sum.inr (Sum.inl b) => ε₁ * B i b
    | Sum.inr (Sum.inr b) => ε₂ * B i b

def andSourceBlock {m k α β : Type*} (A : Matrix m α ℝ) (B : Matrix m β ℝ)
    (C : Matrix k α ℝ) : Matrix (m ⊕ k) (α ⊕ β) ℝ :=
  fun i j => match i, j with
    | Sum.inl r, Sum.inl a => A r a
    | Sum.inl r, Sum.inr b => B r b
    | Sum.inr r, Sum.inl a => C r a
    | Sum.inr _, Sum.inr _ => 0

def andComposedBlock {m k α β : Type*} (a₁ a₂ a : ℝ) (A : Matrix m α ℝ)
    (B : Matrix m β ℝ) (C : Matrix k α ℝ) : Matrix (m ⊕ m ⊕ k) (α ⊕ β ⊕ β) ℝ :=
  fun i j => match i, j with
    | Sum.inl r, Sum.inl x => a₁ * A r x
    | Sum.inl r, Sum.inr (Sum.inl b) => B r b
    | Sum.inl _, Sum.inr (Sum.inr _) => 0
    | Sum.inr (Sum.inl r), Sum.inl x => a₂ * A r x
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inl r), Sum.inr (Sum.inr b) => B r b
    | Sum.inr (Sum.inr r), Sum.inl x => a * C r x
    | Sum.inr (Sum.inr _), Sum.inr _ => 0

def source_lemma_3_4_or_statement {m α β : Type*} [Fintype m] [DecidableEq m]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix m α ℝ) (B : Matrix m β ℝ) (s : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (h0 : 0 < s 0) (h1 : 0 < s 1) : Prop :=
  ‖orComposedBlock 1 (alpha s 0) (alpha s 1) A B‖ ^ 2 ≤
    (Real.sqrt (s 0) + Real.sqrt (s 1)) / Real.sqrt (s 0 + s 1) *
      ‖orSourceBlock A B‖ ^ 2

def source_lemma_3_4_and_statement {m k α β : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix m α ℝ) (B : Matrix m β ℝ) (C : Matrix k α ℝ) (s : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (h0 : 0 < s 0) (h1 : 0 < s 1) : Prop :=
  ‖andComposedBlock (alpha s 0) (alpha s 1) (alphaNorm s) A B C‖ ^ 2 ≤
    (Real.sqrt (s 0) + Real.sqrt (s 1)) / Real.sqrt (s 0 + s 1) *
      ‖andSourceBlock A B C‖ ^ 2

def IsLeafPath {n : ℕ} (φ : Formula n) (γ : Fin n → List Bool) : Prop :=
  ∀ k, φ.nodeAt (γ k) = some (Formula.leaf k)

def pairS {n : ℕ} (φ : Formula n) (p : List Bool) : Fin 2 → ℝ :=
  match φ.nodeAt p with
  | some (Formula.and a b) =>
      fun j => if j.val = 0 then (a.size : ℝ) else (b.size : ℝ)
  | some (Formula.or a b) =>
      fun j => if j.val = 0 then (a.size : ℝ) else (b.size : ℝ)
  | _ => fun _ => 1

def childIndex (c : Bool) : Fin 2 := if c then 1 else 0

def falseChild {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (p : List Bool) : Fin 2 :=
  if φ.evalAt (p ++ [false]) x = false then 0 else 1

def gateCoeffT {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (p : List Bool) : ℝ :=
  match φ.gateAt p with
  | some .and2 =>
      if φ.InTx x p then alpha (pairS φ p) (falseChild φ x p)
      else alphaNorm (pairS φ p)
  | some .or2 => 1
  | none => 1

def gateCoeffK {n : ℕ} (φ : Formula n) (p : List Bool) (c : Bool) : ℝ :=
  match φ.gateAt p with
  | some .and2 => 1
  | some .or2 => alpha (pairS φ p) (childIndex c)
  | none => 1

def branchAfter (γ : List Bool) (p : List Bool) : Bool := (γ[p.length]?).getD false

def gateCoeffV {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (γ p : List Bool) : ℝ :=
  if p ∈ Formula.pathVertices γ then gateCoeffK φ p (branchAfter γ p) else gateCoeffT φ x p

def targetCoeff {n : ℕ} (φ : Formula n) (x : Fin n → Bool) : ℂ :=
  ↑((φ.internalPaths.map (fun p => gateCoeffT φ x p)).prod : ℝ)

def vecCoeff {n : ℕ} (φ : Formula n) (γ : Fin n → List Bool) (k : Fin n)
    (x : Fin n → Bool) : ℂ :=
  if x k = false then
    ↑((φ.internalPaths.map (fun p => gateCoeffV φ x (γ k) p)).prod : ℝ)
  else 0

def Pphi {n : ℕ} (φ : Formula n) (γ : Fin n → List Bool) :
    SpanProgram (Fin n) φ.MaxFalse where
  target u := targetCoeff φ u.val
  vec k u := vecCoeff φ γ k u.val

theorem Formula.size_pos {n : ℕ} (φ : Formula n) : 0 < φ.size := by
  induction φ with
  | leaf i => exact Nat.one_pos
  | and a b ha hb => exact Nat.add_pos_left ha b.size
  | or a b ha hb => exact Nat.add_pos_left ha b.size

theorem pairS_pos {n : ℕ} (φ : Formula n) (p : List Bool) (j : Fin 2) :
    0 < pairS φ p j := by
  unfold pairS
  cases h : φ.nodeAt p with
  | none => simp
  | some ψ =>
      cases ψ with
      | leaf i => simp
      | and a b =>
          by_cases hj : j.val = 0
          · simp [h, hj]; exact_mod_cast Formula.size_pos a
          · simp [h, hj]; exact_mod_cast Formula.size_pos b
      | or a b =>
          by_cases hj : j.val = 0
          · simp [h, hj]; exact_mod_cast Formula.size_pos a
          · simp [h, hj]; exact_mod_cast Formula.size_pos b

theorem alpha_pos_pair {n : ℕ} (φ : Formula n) (p : List Bool) (j : Fin 2) :
    0 < alpha (pairS φ p) j :=
  alpha_pos (pairS_pos φ p 0) (pairS_pos φ p 1) j

theorem alphaNorm_pos_pair {n : ℕ} (φ : Formula n) (p : List Bool) :
    0 < alphaNorm (pairS φ p) := by
  unfold alphaNorm
  apply Real.sqrt_pos.mpr
  have h0 : 0 < alpha (pairS φ p) 0 ^ 2 := pow_pos (alpha_pos_pair φ p 0) 2
  have h1 : 0 < alpha (pairS φ p) 1 ^ 2 := pow_pos (alpha_pos_pair φ p 1) 2
  linarith

theorem gateCoeffT_pos {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (p : List Bool) :
    0 < gateCoeffT φ x p := by
  unfold gateCoeffT
  cases h : φ.gateAt p with
  | none => simp [h]
  | some gk =>
      cases gk with
      | and2 =>
          by_cases hin : φ.InTx x p
          · simp [h, hin]; exact alpha_pos_pair φ p _
          · simp [h, hin]; exact alphaNorm_pos_pair φ p
      | or2 => simp [h]

theorem gateCoeffK_pos {n : ℕ} (φ : Formula n) (p : List Bool) (c : Bool) :
    0 < gateCoeffK φ p c := by
  unfold gateCoeffK
  cases h : φ.gateAt p with
  | none => simp [h]
  | some gk =>
      cases gk with
      | and2 => simp [h]
      | or2 => simp [h]; exact alpha_pos_pair φ p _

theorem gateCoeffV_pos {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (γ p : List Bool) :
    0 < gateCoeffV φ x γ p := by
  unfold gateCoeffV
  by_cases h : p ∈ Formula.pathVertices γ
  · simp [h]; exact gateCoeffK_pos φ p _
  · simp [h]; exact gateCoeffT_pos φ x p

theorem prod_coeffT_pos {n : ℕ} (φ : Formula n) (x : Fin n → Bool) :
    0 < (φ.internalPaths.map (fun p => gateCoeffT φ x p)).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact gateCoeffT_pos φ x p

theorem prod_coeffV_pos {n : ℕ} (φ : Formula n) (x : Fin n → Bool) (γ : List Bool) :
    0 < (φ.internalPaths.map (fun p => gateCoeffV φ x γ p)).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact gateCoeffV_pos φ x γ p

theorem targetCoeff_ne_zero {n : ℕ} (φ : Formula n) (x : Fin n → Bool) :
    targetCoeff φ x ≠ 0 := by
  unfold targetCoeff
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (prod_coeffT_pos φ x))

theorem vecCoeff_ne_zero {n : ℕ} (φ : Formula n) (γ : Fin n → List Bool) (k : Fin n)
    (x : Fin n → Bool) (h : x k = false) : vecCoeff φ γ k x ≠ 0 := by
  unfold vecCoeff
  rw [if_pos h]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (prod_coeffV_pos φ x (γ k)))

def basis {α : Type*} [DecidableEq α] (u : α) : α → ℂ := fun v => if v = u then 1 else 0

theorem dot_basis {α : Type*} [Fintype α] [DecidableEq α] (u : α) (w : α → ℂ) :
    SpanProgram.dot (basis u) w = w u := by
  unfold SpanProgram.dot basis
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ u) h

theorem source_lemma_3_6 {n : ℕ} (φ : Formula n) (γ : Fin n → List Bool)
    (hγ : IsLeafPath φ γ) :
    (∀ (u : φ.MaxFalse) (k : Fin n),
        SpanProgram.dot (basis u) ((Pphi φ γ).vec k) = 0 ↔ u.val k = true) ∧
      (∀ u : φ.MaxFalse,
        SpanProgram.NegWitness (Pphi φ γ) u.val
          (fun v => if v = u then 1 / (Pphi φ γ).target u else 0)) := by
  constructor
  · intro u k
    constructor
    · intro hdot
      by_contra hne
      have hfalse : u.val k = false := by
        cases hk : u.val k <;> simp_all
      rw [dot_basis] at hdot
      exact vecCoeff_ne_zero φ γ k u.val hfalse hdot
    · intro htrue
      rw [dot_basis]
      show vecCoeff φ γ k u.val = 0
      simp [vecCoeff, htrue]
  · intro u
    constructor
    · unfold SpanProgram.dot
      have ht : (Pphi φ γ).target u ≠ 0 := targetCoeff_ne_zero φ u.val
      have hstar : star ((Pphi φ γ).target u) = (Pphi φ γ).target u := by
        unfold Pphi targetCoeff
        simp
      rw [Finset.sum_eq_single u]
      · simp only [if_true]
        rw [hstar, one_div, mul_inv_cancel₀ ht]
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ u) h
    · intro b hb
      unfold SpanProgram.dot
      have hv : (Pphi φ γ).vec b u = 0 := by
        show vecCoeff φ γ b u.val = 0
        simp [vecCoeff, hb]
      rw [Finset.sum_eq_single u]
      · simp only [if_true]
        simp [hv]
      · intro v _ hvu
        simp [hvu]
      · intro h
        exact absurd (Finset.mem_univ u) h

namespace Formula

def mapLeaf {m n : ℕ} (f : Fin m → Fin n) : Formula m → Formula n
  | leaf i => leaf (f i)
  | and a b => and (mapLeaf f a) (mapLeaf f b)
  | or a b => or (mapLeaf f a) (mapLeaf f b)

end Formula

def comb : (J : ℕ) → (Fin J → Bool) → Formula (J + 1)
  | 0, _ => Formula.leaf 0
  | J + 1, g =>
      let sub := Formula.mapLeaf Fin.castSucc (comb J (fun i => g i.succ))
      let last := Formula.leaf (Fin.last (J + 1))
      if g 0 then Formula.and sub last else Formula.or sub last

def combPath : (J : ℕ) → Fin (J + 1) → List Bool
  | 0, _ => []
  | J + 1, k =>
      if h : k.val = J + 1 then [true]
      else false :: combPath J ⟨k.val, by omega⟩

def parentGate : (J : ℕ) → (Fin J → Bool) → Fin (J + 1) → Option Bool
  | 0, _, _ => none
  | J + 1, g, k =>
      if h : k.val = J + 1 then some (g 0)
      else if hJ : J = 0 then some (g 0)
      else parentGate J (fun i => g i.succ) ⟨k.val, by omega⟩

def InTF (J : ℕ) (g : Fin J → Bool) (k : Fin (J + 1)) : Prop :=
  k.val = 0 ∨ parentGate J g k = some true

def combFalseInput (J : ℕ) (g : Fin J → Bool) (j : Fin (J + 1)) :
    Fin (J + 1) → Bool :=
  fun k =>
    if k.val < j.val then true
    else if k.val = j.val then false
    else (parentGate J g k).getD false

def combAlphaProdSq (J : ℕ) (g : Fin J → Bool) : ℝ :=
  ((comb J g).internalPaths.map (fun p => alphaNorm (pairS (comb J g) p) ^ 2)).prod

def source_lemma_3_7_statement (J : ℕ) (g : Fin J → Bool) : Prop :=
  (∀ j : Fin (J + 1), (comb J g).IsMaximalFalse (combFalseInput J g j) ↔ InTF J g j) ∧
    (∀ x : Fin (J + 1) → Bool, (comb J g).IsMaximalFalse x →
      ∃ j : Fin (J + 1), InTF J g j ∧ combFalseInput J g j = x) ∧
    (∀ j : Fin (J + 1), InTF J g j → ∀ u : (comb J g).MaxFalse,
      u.val = combFalseInput J g j →
        SpanProgram.NegWitness (Pphi (comb J g) (combPath J)) u.val
          (fun v => if v = u then 1 / (Pphi (comb J g) (combPath J)).target u else 0))

end Qatlib.Papers.GameTree09.MainResults
