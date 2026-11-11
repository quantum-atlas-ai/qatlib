/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.NANDAmbainis07.MainResults.Certificates

/-!
# Certificate amplitudes and weighted rows

This module builds the recursive amplitude data used for the NAND certificate kernel
construction in [Ambainis2007]. Boolean paths `Vtx` locate subtrees through `NNode.sub`, while
`W` selects one grandchild from each of the two child branches and `W.amp` assigns the
corresponding scaled amplitudes.

The support predicate `W.supp`, edge weights `hEdge`, and weighted expression `row` provide
local ingredients for the kernel proof. The results here establish parity restrictions and
selected scaling and cancellation identities.

## Main statements

* `W.supp_even` places the recursive support at even path lengths.
* `W.amp_odd_eq_zero` makes every odd-depth amplitude vanish.
* `row_even_zero` proves vanishing of the weighted row at even path lengths.
* `row_scale_LL_a` and `row_LL_zL` give scaling and first-level cancellation for the `W.nodeLL`
  construction.

## References

* [Ambainis, 2007][Ambainis2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.NANDAmbainis07.MainResults

/-- The real fourth-root function defined by applying `Real.sqrt` twice. -/
def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

/-- The fourth root is nonnegative for every real input. -/
lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _

/-- The fourth root of a product factors as the product of fourth roots when the first factor is
nonnegative. -/
lemma fourthRoot_mul {a b : ℝ} (ha : 0 ≤ a) :
    fourthRoot (a * b) = fourthRoot a * fourthRoot b := by
  unfold fourthRoot
  rw [Real.sqrt_mul ha b, Real.sqrt_mul (Real.sqrt_nonneg a) (Real.sqrt b)]

/-- The fourth root of a positive real number is positive. -/
lemma fourthRoot_pos {a : ℝ} (ha : 0 < a) : 0 < fourthRoot a := by
  unfold fourthRoot
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)

/-- The fourth root of a positive real number is nonzero. -/
lemma fourthRoot_ne_zero {a : ℝ} (ha : 0 < a) : fourthRoot a ≠ 0 :=
  ne_of_gt (fourthRoot_pos ha)

/-- The number of leaf occurrences in a binary NAND formula, obtained by adding the leaf counts
of the two children. -/
def NNode.leaves : NNode → ℕ
  | .leaf _ => 1
  | .node l r => NNode.leaves l + NNode.leaves r

/-- Every binary NAND formula has a positive number of leaf occurrences. -/
@[simp] lemma NNode.leaves_pos (e : NNode) : 0 < e.leaves := by
  induction e with
  | leaf _ => show 0 < 1; omega
  | node l r ihl ihr => show 0 < NNode.leaves l + NNode.leaves r; omega

/-- Boolean-list paths used to address vertices, with `false` selecting the left child and
`true` the right child. -/
abbrev Vtx := List Bool

/-- Looks up the subtree at a Boolean path, returning `none` when the path continues beyond a
leaf. The empty path returns the whole formula. -/
def NNode.sub : NNode → Vtx → Option NNode
  | .leaf i, [] => some (.leaf i)
  | .leaf _, _ :: _ => none
  | .node l r, [] => some (.node l r)
  | .node l _, false :: p => NNode.sub l p
  | .node _ r, true :: p => NNode.sub r p

/-- The amplitude scaling coefficient `fourthRoot ((mroot : ℝ) / (4 * (mc : ℝ)))` for root and
selected-subtree leaf counts. -/
def cval (mroot mc : ℕ) : ℝ := fourthRoot ((mroot : ℝ) / (4 * (mc : ℝ)))

/-- The amplitude coefficient is positive when both leaf-count parameters are positive. -/
lemma cval_pos {mroot mc : ℕ} (hm : 0 < mroot) (hc : 0 < mc) : 0 < cval mroot mc := by
  apply fourthRoot_pos
  have hm' : (0:ℝ) < (mroot : ℝ) := by exact_mod_cast hm
  have hc' : (0:ℝ) < (mc : ℝ) := by exact_mod_cast hc
  positivity

/-- Factors the parent-edge fourth-root coefficient into a child-edge coefficient and an
amplitude coefficient, assuming a nonnegative numerator and positive denominators. -/
lemma kernel_coef_id {mp mu my : ℝ} (hmp : 0 ≤ mp) (hmu : 0 < mu) (hmy : 0 < my) :
    fourthRoot (mp / (2 * mu)) = fourthRoot (2 * my / mu) * fourthRoot (mp / (4 * my)) := by
  have h1 : (0:ℝ) ≤ 2 * my / mu := by positivity
  have h2 : (0:ℝ) ≤ mp / (4 * my) := by positivity
  rw [← fourthRoot_mul h1]
  congr 1
  field_simp
  ring

/-- Recursive witnesses selecting a false input leaf or, at a two-level node, one recursively
witnessed grandchild from each child branch. The four node constructors record the possible
left or right selections in those branches. -/
inductive W (x : ℕ → Bool) : NNode → Type
  | leaf {i : ℕ} (h : x i = false) : W x (.leaf i)
  | nodeLL {a b c d : NNode} (w1 : W x a) (w3 : W x c) : W x (.node (.node a b) (.node c d))
  | nodeLR {a b c d : NNode} (w1 : W x a) (w4 : W x d) : W x (.node (.node a b) (.node c d))
  | nodeRL {a b c d : NNode} (w2 : W x b) (w3 : W x c) : W x (.node (.node a b) (.node c d))
  | nodeRR {a b c d : NNode} (w2 : W x b) (w4 : W x d) : W x (.node (.node a b) (.node c d))

/-- Assigns real amplitudes to Boolean paths from a recursive witness, with root amplitude one
and selected grandchild amplitudes multiplied by the negative coefficient `cval`. All other
paths receive amplitude zero. -/
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

/-- The recursive support predicate containing the root and the paths obtained by prefixing the
selected grandchild branches to their witness supports. -/
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

/-- Every recursive witness has amplitude one at the empty path. -/
@[simp] lemma W.amp_nil {x : ℕ → Bool} {e : NNode} (w : W x e) : W.amp w ([] : Vtx) = 1 := by
  cases w <;> rfl

/-- Every path in the recursive witness support has even length. -/
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

/-- A path with nonzero witness amplitude belongs to the recursive support. -/
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

/-- The witness amplitude vanishes at every path outside its recursive support. -/
lemma W.amp_eq_zero_of_not_supp {x : ℕ → Bool} : {e : NNode} → (w : W x e) →
    ∀ p, ¬ W.supp w p → W.amp w p = 0 := by
  intro e w p hp
  by_contra h
  exact hp (W.amp_ne_zero_imp_supp w p h)

/-- The witness amplitude vanishes at every path of odd length. -/
lemma W.amp_odd_eq_zero {x : ℕ → Bool} : {e : NNode} → (w : W x e) →
    ∀ p, p.length % 2 = 1 → W.amp w p = 0 := by
  intro e w p hp
  by_contra h
  have hs := W.amp_ne_zero_imp_supp w p h
  have := W.supp_even w p hs
  omega

/-- The real edge weight determined by the parent parity and two leaf counts. It is `fourthRoot
(mp / (2 * mc))` for an even parent and `fourthRoot (2 * mc / mp)` otherwise, with the
counts cast to real numbers. -/
def hEdge (parEven : Bool) (mp mc : ℕ) : ℝ :=
  if parEven then fourthRoot ((mp : ℝ) / (2 * (mc : ℝ)))
  else fourthRoot ((2 * (mc : ℝ)) / (mp : ℝ))

/-- Returns the subtree at a path, using `NNode.leaf 0` as the default when subtree lookup
fails. -/
def subOr (e : NNode) (p : Vtx) : NNode := (e.sub p).getD (.leaf 0)

/-- Subtree lookup with a default returns the original formula at the empty path. -/
@[simp] lemma subOr_nil (e : NNode) : subOr e [] = e := by cases e <;> rfl

/-- A path beginning with two left steps reduces subtree lookup to the first grandchild. -/
@[simp] lemma subOr_ff (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (false :: false :: q) = subOr a q := rfl

/-- A path beginning with a left step and then a right step reduces subtree lookup to the second
grandchild. -/
@[simp] lemma subOr_ft (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (false :: true :: q) = subOr b q := rfl

/-- A path beginning with a right step and then a left step reduces subtree lookup to the third
grandchild. -/
@[simp] lemma subOr_tf (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (true :: false :: q) = subOr c q := rfl

/-- A path beginning with two right steps reduces subtree lookup to the fourth grandchild. -/
@[simp] lemma subOr_tt (a b c d : NNode) (q : Vtx) :
    subOr (.node (.node a b) (.node c d)) (true :: true :: q) = subOr d q := rfl

/-- The weighted sum of a witness's amplitudes at a path's parent and two children, with no
parent contribution at the root. The edge coefficients use path parity and leaf counts
obtained through `subOr`. -/
def row (x : ℕ → Bool) {e : NNode} (w : W x e) (p : Vtx) : ℝ :=
  (match p with
   | [] => 0
   | _ => hEdge (decide ((p.dropLast).length % 2 = 0))
            (subOr e (p.dropLast)).leaves (subOr e p).leaves * W.amp w p.dropLast)
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [false])).leaves
      * W.amp w (p ++ [false])
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [true])).leaves
      * W.amp w (p ++ [true])

/-- The leaf count of an internal NAND node is the sum of its children's leaf counts. -/
@[simp] lemma NNode.leaves_node (l r : NNode) : (NNode.node l r).leaves = l.leaves + r.leaves := rfl

/-- For a `W.nodeLL` witness, the amplitude along the first grandchild branch is the amplitude
of `w1` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_LL_ff {x} {a b c d : NNode} (w1 : W x a) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeLL (b := b) (d := d) w1 w3) (false :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q := rfl

/-- For a `W.nodeLL` witness, the amplitude along the third grandchild branch is the amplitude
of `w3` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_LL_tf {x} {a b c d : NNode} (w1 : W x a) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeLL (b := b) (d := d) w1 w3) (true :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q := rfl

/-- For a `W.nodeLR` witness, the amplitude along the first grandchild branch is the amplitude
of `w1` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_LR_ff {x} {a b c d : NNode} (w1 : W x a) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeLR (b := b) (c := c) w1 w4) (false :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) * W.amp w1 q := rfl

/-- For a `W.nodeLR` witness, the amplitude along the fourth grandchild branch is the amplitude
of `w4` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_LR_tt {x} {a b c d : NNode} (w1 : W x a) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeLR (b := b) (c := c) w1 w4) (true :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q := rfl

/-- For a `W.nodeRL` witness, the amplitude along the second grandchild branch is the amplitude
of `w2` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_RL_ft {x} {a b c d : NNode} (w2 : W x b) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeRL (a := a) (d := d) w2 w3) (false :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q := rfl

/-- For a `W.nodeRL` witness, the amplitude along the third grandchild branch is the amplitude
of `w3` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_RL_tf {x} {a b c d : NNode} (w2 : W x b) (w3 : W x c) (q : Vtx) :
    W.amp (W.nodeRL (a := a) (d := d) w2 w3) (true :: false :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) * W.amp w3 q := rfl

/-- For a `W.nodeRR` witness, the amplitude along the second grandchild branch is the amplitude
of `w2` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_RR_ft {x} {a b c d : NNode} (w2 : W x b) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeRR (a := a) (c := c) w2 w4) (false :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) * W.amp w2 q := rfl

/-- For a `W.nodeRR` witness, the amplitude along the fourth grandchild branch is the amplitude
of `w4` multiplied by the negative `cval` coefficient for that grandchild. -/
@[simp] lemma W.amp_RR_tt {x} {a b c d : NNode} (w2 : W x b) (w4 : W x d) (q : Vtx) :
    W.amp (W.nodeRR (a := a) (c := c) w2 w4) (true :: true :: q)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) * W.amp w4 q := rfl

/-- Dropping the final element commutes with prefixing two Boolean entries when the remaining
path is nonempty. -/
lemma dropLast_cons_cons (d0 d1 : Bool) {q : Vtx} (hq : q ≠ []) :
    (d0 :: d1 :: q).dropLast = d0 :: d1 :: q.dropLast := by
  cases q with
  | nil => exact absurd rfl hq
  | cons b q => rfl

/-- Prefixing two Boolean entries preserves path-length parity. -/
lemma len_cons_cons_mod (d0 d1 : Bool) (q : Vtx) : (d0 :: d1 :: q).length % 2 = q.length % 2 := by
  simp [List.length_cons]; omega

/-- The length modulo two after prefixing one Boolean entry is the original length plus one
modulo two. -/
lemma len_cons_mod (d0 : Bool) (q : Vtx) : (d0 :: q).length % 2 = (q.length + 1) % 2 := by
  simp [List.length_cons]

/-- The weighted row of a witness vanishes at every path of even length. -/
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

/-- For a nonempty suffix in the first grandchild branch of a `W.nodeLL` witness, the row equals
the row for `w1` multiplied by the negative `cval` coefficient for that grandchild. -/
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

/-- Dropping the final entry of a singleton Boolean path gives the empty path. -/
@[simp] lemma dropLast_single (b : Bool) : ([b] : Vtx).dropLast = [] := rfl

/-- A singleton Boolean path has length one. -/
@[simp] lemma length_single (b : Bool) : ([b] : Vtx).length = 1 := rfl

/-- The one-step left path in a two-level node returns its left child under `subOr`. -/
@[simp] lemma subOr_f (a b c d : NNode) : subOr (.node (.node a b) (.node c d)) [false] = .node a b := rfl

/-- The one-step right path in a two-level node returns its right child under `subOr`. -/
@[simp] lemma subOr_t (a b c d : NNode) : subOr (.node (.node a b) (.node c d)) [true] = .node c d := rfl

/-- The weight from a two-level root to its left child equals the weight from that child to the
first grandchild times the corresponding amplitude coefficient. -/
lemma hEdge_eq_a (a b c d : NNode) :
    hEdge true (NNode.node (NNode.node a b) (NNode.node c d)).leaves (NNode.node a b).leaves
      = hEdge false (NNode.node a b).leaves a.leaves
        * cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves := by
  simp only [hEdge, if_true, cval]
  exact kernel_coef_id (by positivity)
    (by exact_mod_cast NNode.leaves_pos (NNode.node a b))
    (by exact_mod_cast NNode.leaves_pos a)

/-- Expresses the two-level left-edge cancellation identity in terms of four natural leaf
counts, assuming the first count is positive. -/
lemma hEdge_eq_a_nat (A B C D : ℕ) (hA : 0 < A) :
    hEdge true (A + B + (C + D)) (A + B)
      = hEdge false (A + B) A * cval (A + B + (C + D)) A := by
  simp only [hEdge, if_true, cval]
  exact kernel_coef_id (by positivity)
    (by exact_mod_cast Nat.add_pos_left hA B)
    (by exact_mod_cast hA)

/-- The row of a `W.nodeLL` witness vanishes at the one-step left path. -/
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
