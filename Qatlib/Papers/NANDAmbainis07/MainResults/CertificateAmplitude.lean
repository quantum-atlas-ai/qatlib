/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.NANDAmbainis07.MainResults.Certificates
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.NANDAmbainis07.MainResults

def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _

lemma fourthRoot_mul {a b : ℝ} (ha : 0 ≤ a) :
    fourthRoot (a * b) = fourthRoot a * fourthRoot b := by
  unfold fourthRoot
  rw [Real.sqrt_mul ha b, Real.sqrt_mul (Real.sqrt_nonneg a) (Real.sqrt b)]

lemma fourthRoot_pos {a : ℝ} (ha : 0 < a) : 0 < fourthRoot a := by
  unfold fourthRoot
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)

lemma fourthRoot_ne_zero {a : ℝ} (ha : 0 < a) : fourthRoot a ≠ 0 :=
  ne_of_gt (fourthRoot_pos ha)

def NNode.leaves : NNode → ℕ
  | .leaf _ => 1
  | .node l r => NNode.leaves l + NNode.leaves r

@[simp] lemma NNode.leaves_pos (e : NNode) : 0 < e.leaves := by
  induction e with
  | leaf _ => show 0 < 1; omega
  | node l r ihl ihr => show 0 < NNode.leaves l + NNode.leaves r; omega

abbrev Vtx := List Bool

def NNode.sub : NNode → Vtx → Option NNode
  | .leaf i, [] => some (.leaf i)
  | .leaf _, _ :: _ => none
  | .node l r, [] => some (.node l r)
  | .node l _, false :: p => NNode.sub l p
  | .node _ r, true :: p => NNode.sub r p

def cval (mroot mc : ℕ) : ℝ := fourthRoot ((mroot : ℝ) / (4 * (mc : ℝ)))

lemma cval_pos {mroot mc : ℕ} (hm : 0 < mroot) (hc : 0 < mc) : 0 < cval mroot mc := by
  apply fourthRoot_pos
  have hm' : (0:ℝ) < (mroot : ℝ) := by exact_mod_cast hm
  have hc' : (0:ℝ) < (mc : ℝ) := by exact_mod_cast hc
  positivity

lemma kernel_coef_id {mp mu my : ℝ} (hmp : 0 ≤ mp) (hmu : 0 < mu) (hmy : 0 < my) :
    fourthRoot (mp / (2 * mu)) = fourthRoot (2 * my / mu) * fourthRoot (mp / (4 * my)) := by
  have h1 : (0:ℝ) ≤ 2 * my / mu := by positivity
  have h2 : (0:ℝ) ≤ mp / (4 * my) := by positivity
  rw [← fourthRoot_mul h1]
  congr 1
  field_simp
  ring

inductive W (x : ℕ → Bool) : NNode → Type
  | leaf {i : ℕ} (h : x i = false) : W x (.leaf i)
  | nodeLL {a b c d : NNode} (w1 : W x a) (w3 : W x c) : W x (.node (.node a b) (.node c d))
  | nodeLR {a b c d : NNode} (w1 : W x a) (w4 : W x d) : W x (.node (.node a b) (.node c d))
  | nodeRL {a b c d : NNode} (w2 : W x b) (w3 : W x c) : W x (.node (.node a b) (.node c d))
  | nodeRR {a b c d : NNode} (w2 : W x b) (w4 : W x d) : W x (.node (.node a b) (.node c d))

def W.amp {x : ℕ → Bool} : {e : NNode} → W x e → Vtx → ℝ
  | _, W.leaf _ => fun p => if p = [] then 1 else 0
  | _, @W.nodeLL _ a b c d w1 w3 => fun p =>
      match p with
      | [] => 1
      | false :: false :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q
      | true :: false :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q
      | _ => 0
  | _, @W.nodeLR _ a b c d w1 w4 => fun p =>
      match p with
      | [] => 1
      | false :: false :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q
      | true :: true :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q
      | _ => 0
  | _, @W.nodeRL _ a b c d w2 w3 => fun p =>
      match p with
      | [] => 1
      | false :: true :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q
      | true :: false :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q
      | _ => 0
  | _, @W.nodeRR _ a b c d w2 w4 => fun p =>
      match p with
      | [] => 1
      | false :: true :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q
      | true :: true :: q => -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q
      | _ => 0

def W.supp {x : ℕ → Bool} : {e : NNode} → W x e → Vtx → Prop
  | _, W.leaf _ => fun p => p = []
  | _, @W.nodeLL _ a b c d w1 w3 => fun p =>
      p = [] ∨ (∃ q, p = false :: false :: q ∧ W.supp w1 q)
        ∨ (∃ q, p = true :: false :: q ∧ W.supp w3 q)
  | _, @W.nodeLR _ a b c d w1 w4 => fun p =>
      p = [] ∨ (∃ q, p = false :: false :: q ∧ W.supp w1 q)
        ∨ (∃ q, p = true :: true :: q ∧ W.supp w4 q)
  | _, @W.nodeRL _ a b c d w2 w3 => fun p =>
      p = [] ∨ (∃ q, p = false :: true :: q ∧ W.supp w2 q)
        ∨ (∃ q, p = true :: false :: q ∧ W.supp w3 q)
  | _, @W.nodeRR _ a b c d w2 w4 => fun p =>
      p = [] ∨ (∃ q, p = false :: true :: q ∧ W.supp w2 q)
        ∨ (∃ q, p = true :: true :: q ∧ W.supp w4 q)

@[simp] lemma W.amp_nil {x : ℕ → Bool} {e : NNode} (w : W x e) : W.amp w ([] : Vtx) = 1 := by
  cases w <;> rfl

lemma W.supp_even {x : ℕ → Bool} : {e : NNode} → (w : W x e) → ∀ p, W.supp w p → p.length % 2 = 0
  | _, W.leaf _, p, hp => by
      have hp' : p = [] := hp
      subst hp'; rfl
  | _, @W.nodeLL _ a b c d w1 w3, p, hp => by
      rcases hp with rfl | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      · rfl
      · have := W.supp_even w1 q hq; simp only [List.length_cons]; omega
      · have := W.supp_even w3 q hq; simp only [List.length_cons]; omega
  | _, @W.nodeLR _ a b c d w1 w4, p, hp => by
      rcases hp with rfl | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      · rfl
      · have := W.supp_even w1 q hq; simp only [List.length_cons]; omega
      · have := W.supp_even w4 q hq; simp only [List.length_cons]; omega
  | _, @W.nodeRL _ a b c d w2 w3, p, hp => by
      rcases hp with rfl | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      · rfl
      · have := W.supp_even w2 q hq; simp only [List.length_cons]; omega
      · have := W.supp_even w3 q hq; simp only [List.length_cons]; omega
  | _, @W.nodeRR _ a b c d w2 w4, p, hp => by
      rcases hp with rfl | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      · rfl
      · have := W.supp_even w2 q hq; simp only [List.length_cons]; omega
      · have := W.supp_even w4 q hq; simp only [List.length_cons]; omega

lemma W.amp_ne_zero_imp_supp {x : ℕ → Bool} : {e : NNode} → (w : W x e) →
    ∀ p, W.amp w p ≠ 0 → W.supp w p
  | _, W.leaf _, p, hp => by
      by_cases h : p = []
      · subst h; exact rfl
      · simp [W.amp, h] at hp
  | _, @W.nodeLL _ a b c d w1 w3, p, hp => by
      have hc1 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos a) |>.ne'
      have hc3 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos c) |>.ne'
      match p with
      | [] => exact Or.inl rfl
      | false :: false :: q =>
          have hq : W.amp w1 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inl ⟨q, rfl, W.amp_ne_zero_imp_supp w1 q hq⟩)
      | true :: false :: q =>
          have hq : W.amp w3 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inr ⟨q, rfl, W.amp_ne_zero_imp_supp w3 q hq⟩)
      | false :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | false :: true :: q => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: true :: q => simp only [W.amp] at hp; exact absurd rfl hp
  | _, @W.nodeLR _ a b c d w1 w4, p, hp => by
      have hc1 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos a) |>.ne'
      have hc4 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos d) |>.ne'
      match p with
      | [] => exact Or.inl rfl
      | false :: false :: q =>
          have hq : W.amp w1 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inl ⟨q, rfl, W.amp_ne_zero_imp_supp w1 q hq⟩)
      | true :: true :: q =>
          have hq : W.amp w4 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inr ⟨q, rfl, W.amp_ne_zero_imp_supp w4 q hq⟩)
      | false :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | false :: true :: q => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: false :: q => simp only [W.amp] at hp; exact absurd rfl hp
  | _, @W.nodeRL _ a b c d w2 w3, p, hp => by
      have hc2 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos b) |>.ne'
      have hc3 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos c) |>.ne'
      match p with
      | [] => exact Or.inl rfl
      | false :: true :: q =>
          have hq : W.amp w2 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inl ⟨q, rfl, W.amp_ne_zero_imp_supp w2 q hq⟩)
      | true :: false :: q =>
          have hq : W.amp w3 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inr ⟨q, rfl, W.amp_ne_zero_imp_supp w3 q hq⟩)
      | false :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | false :: false :: q => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: true :: q => simp only [W.amp] at hp; exact absurd rfl hp
  | _, @W.nodeRR _ a b c d w2 w4, p, hp => by
      have hc2 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos b) |>.ne'
      have hc4 : cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves ≠ 0 :=
        cval_pos (NNode.leaves_pos (NNode.node (NNode.node a b) (NNode.node c d))) (NNode.leaves_pos d) |>.ne'
      match p with
      | [] => exact Or.inl rfl
      | false :: true :: q =>
          have hq : W.amp w2 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inl ⟨q, rfl, W.amp_ne_zero_imp_supp w2 q hq⟩)
      | true :: true :: q =>
          have hq : W.amp w4 q ≠ 0 := by
            simp only [W.amp] at hp
            intro h; exact hp (by rw [h]; ring)
          exact Or.inr (Or.inr ⟨q, rfl, W.amp_ne_zero_imp_supp w4 q hq⟩)
      | false :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | false :: false :: q => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: [] => simp only [W.amp] at hp; exact absurd rfl hp
      | true :: false :: q => simp only [W.amp] at hp; exact absurd rfl hp

lemma W.amp_eq_zero_of_not_supp {x : ℕ → Bool} : {e : NNode} → (w : W x e) →
    ∀ p, ¬ W.supp w p → W.amp w p = 0 := by
  intro e w p hp
  by_contra h
  exact hp (W.amp_ne_zero_imp_supp w p h)

lemma W.amp_odd_eq_zero {x : ℕ → Bool} : {e : NNode} → (w : W x e) →
    ∀ p, p.length % 2 = 1 → W.amp w p = 0 := by
  intro e w p hp
  by_contra h
  have hs := W.amp_ne_zero_imp_supp w p h
  have := W.supp_even w p hs
  omega

def hEdge (parEven : Bool) (mp mc : ℕ) : ℝ :=
  if parEven then fourthRoot ((mp : ℝ) / (2 * (mc : ℝ)))
  else fourthRoot ((2 * (mc : ℝ)) / (mp : ℝ))

def subOr (e : NNode) (p : Vtx) : NNode := (e.sub p).getD (.leaf 0)

@[simp] lemma subOr_nil (e : NNode) : subOr e [] = e := by cases e <;> rfl

@[simp] lemma subOr_ff (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (false :: false :: q) = subOr a q := rfl

@[simp] lemma subOr_ft (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (false :: true :: q) = subOr b q := rfl

@[simp] lemma subOr_tf (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (true :: false :: q) = subOr c q := rfl

@[simp] lemma subOr_tt (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (true :: true :: q) = subOr d q := rfl

def row (x : ℕ → Bool) {e : NNode} (w : W x e) (p : Vtx) : ℝ :=
  (match p with
   | [] => 0
   | _ => hEdge (decide ((p.dropLast).length % 2 = 0))
            (subOr e (p.dropLast)).leaves (subOr e p).leaves * W.amp w p.dropLast)
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [false])).leaves
      * W.amp w (p ++ [false])
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [true])).leaves
      * W.amp w (p ++ [true])

@[simp] lemma NNode.leaves_node (l r : NNode) : (NNode.node l r).leaves = l.leaves + r.leaves := rfl

@[simp] lemma W.amp_LL_ff {x} {a b c d : NNode} (w1 : W x a) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeLL (b := b) (d := d) w1 w3) (false :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q := rfl

@[simp] lemma W.amp_LL_tf {x} {a b c d : NNode} (w1 : W x a) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeLL (b := b) (d := d) w1 w3) (true :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q := rfl

@[simp] lemma W.amp_LR_ff {x} {a b c d : NNode} (w1 : W x a) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeLR (b := b) (c := c) w1 w4) (false :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q := rfl

@[simp] lemma W.amp_LR_tt {x} {a b c d : NNode} (w1 : W x a) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeLR (b := b) (c := c) w1 w4) (true :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q := rfl

@[simp] lemma W.amp_RL_ft {x} {a b c d : NNode} (w2 : W x b) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeRL (a := a) (d := d) w2 w3) (false :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q := rfl

@[simp] lemma W.amp_RL_tf {x} {a b c d : NNode} (w2 : W x b) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeRL (a := a) (d := d) w2 w3) (true :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q := rfl

@[simp] lemma W.amp_RR_ft {x} {a b c d : NNode} (w2 : W x b) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeRR (a := a) (c := c) w2 w4) (false :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q := rfl

@[simp] lemma W.amp_RR_tt {x} {a b c d : NNode} (w2 : W x b) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeRR (a := a) (c := c) w2 w4) (true :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q := rfl

lemma dropLast_cons_cons (d0 d1 : Bool) {q : Vtx} (hq : q ≠ []) :
    (d0 :: d1 :: q).dropLast = d0 :: d1 :: q.dropLast := by
  cases q with
  | nil => exact absurd rfl hq
  | cons b q => rfl

lemma len_cons_cons_mod (d0 d1 : Bool) (q : Vtx) : (d0 :: d1 :: q).length % 2 = q.length % 2 := by
  simp [List.length_cons]; omega

lemma len_cons_mod (d0 : Bool) (q : Vtx) : (d0 :: q).length % 2 = (q.length + 1) % 2 := by
  simp [List.length_cons]

lemma row_even_zero (x : ℕ → Bool) {e : NNode} (w : W x e) (p : Vtx)
    (hp : p.length % 2 = 0) : row x w p = 0 := by
  cases p with
  | nil =>
      have b1 := W.amp_odd_eq_zero w ([false] : Vtx) (by decide)
      have b2 := W.amp_odd_eq_zero w ([true] : Vtx) (by decide)
      simp only [row, List.nil_append, b1, b2, mul_zero, add_zero]
  | cons d rest =>
      have hplen : (d :: rest).length % 2 = 0 := hp
      have hpar : ((d :: rest).dropLast).length % 2 = 1 := by
        rw [List.length_dropLast]; simp [List.length_cons] at hplen ⊢; omega
      have hch1 : ((d :: rest) ++ [false]).length % 2 = 1 := by
        simp [List.length_append, List.length_cons] at hplen ⊢; omega
      have hch2 : ((d :: rest) ++ [true]).length % 2 = 1 := by
        simp [List.length_append, List.length_cons] at hplen ⊢; omega
      have a1 := W.amp_odd_eq_zero w ((d :: rest).dropLast) hpar
      have a2 := W.amp_odd_eq_zero w ((d :: rest) ++ [false]) hch1
      have a3 := W.amp_odd_eq_zero w ((d :: rest) ++ [true]) hch2
      simp only [row, a1, a2, a3, mul_zero, add_zero]

lemma row_scale_LL_a (x : ℕ → Bool) {a b c d : NNode} (w1 : W x a) (w3 : W x c) (q : Vtx)
    (hq : q ≠ []) :
    row x (W.nodeLL (b := b) (d := d) w1 w3) (false :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * row x w1 q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons d0 rest =>
      simp only [row, List.cons_append, subOr_ff, W.amp_LL_ff, len_cons_cons_mod,
        dropLast_cons_cons false false (List.cons_ne_nil d0 rest)]
      ring

@[simp] lemma dropLast_single (b : Bool) : ([b] : Vtx).dropLast = [] := rfl

@[simp] lemma length_single (b : Bool) : ([b] : Vtx).length = 1 := rfl

@[simp] lemma subOr_f (a b c d : NNode) : subOr (.node (.node a b) (.node c d)) [false] = .node a b := rfl

@[simp] lemma subOr_t (a b c d : NNode) : subOr (.node (.node a b) (.node c d)) [true] = .node c d := rfl

lemma hEdge_eq_a (a b c d : NNode) :
    hEdge true (NNode.node (NNode.node a b) (NNode.node c d)).leaves (NNode.node a b).leaves
      = hEdge false (NNode.node a b).leaves a.leaves
        * cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves := by
  simp only [hEdge, if_true, cval]
  exact kernel_coef_id (by positivity)
    (by exact_mod_cast NNode.leaves_pos (NNode.node a b))
    (by exact_mod_cast NNode.leaves_pos a)

lemma hEdge_eq_a_nat (A B C D : ℕ) (hA : 0 < A) :
    hEdge true (A + B + (C + D)) (A + B)
      = hEdge false (A + B) A * cval (A + B + (C + D)) A := by
  simp only [hEdge, if_true, cval]
  exact kernel_coef_id (by positivity)
    (by exact_mod_cast Nat.add_pos_left hA B)
    (by exact_mod_cast hA)

lemma row_LL_zL (x : ℕ → Bool) {a b c d : NNode} (w1 : W x a) (w3 : W x c) :
    row x (W.nodeLL (b := b) (d := d) w1 w3) ([false] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeLL (b := b) (d := d) w1 w3) ([false, false] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) := by
    simp [W.amp_LL_ff, W.amp_nil]
  have h3 : W.amp (W.nodeLL (b := b) (d := d) w1 w3) ([false, true] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_f, subOr_ff,
    dropLast_single, length_single, List.length_nil, W.amp_nil,
    h2, h3, mul_zero, add_zero, mul_neg]
  norm_num
  rw [hEdge_eq_a_nat a.leaves b.leaves c.leaves d.leaves (NNode.leaves_pos a)]
  ring

end Qatlib.Papers.NANDAmbainis07.MainResults
