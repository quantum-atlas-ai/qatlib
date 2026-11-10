/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NANDAmbainis07.MainResults.CertificateAmplitude
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.NANDAmbainis07.MainResults

def Hmul (e : NNode) (f : Vtx → ℝ) (p : Vtx) : ℝ :=
  (match p with
   | [] => 0
   | _ => hEdge (decide ((p.dropLast).length % 2 = 0))
            (subOr e (p.dropLast)).leaves (subOr e p).leaves * f p.dropLast)
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [false])).leaves
      * f (p ++ [false])
  + hEdge (decide (p.length % 2 = 0)) (subOr e p).leaves (subOr e (p ++ [true])).leaves
      * f (p ++ [true])

lemma row_eq_Hmul (x : ℕ → Bool) {e : NNode} (w : W x e) (p : Vtx) :
    row x w p = Hmul e (W.amp w) p := by
  cases p <;> rfl

lemma hEdge_cancel {mroot mz my : ℕ} (hz : 0 < mz) (hy : 0 < my) :
    hEdge true mroot mz = hEdge false mz my * cval mroot my := by
  simp only [hEdge, if_true, cval]
  exact kernel_coef_id (by positivity) (by exact_mod_cast hz) (by exact_mod_cast hy)

lemma row_scale {x : ℕ → Bool} {R Y : NNode} (w : W x R) (ws : W x Y) (d0 d1 : Bool)
    (mR mY : ℕ)
    (hamp : ∀ q : Vtx, W.amp w (d0 :: d1 :: q) = -(cval mR mY) * W.amp ws q)
    (hsub : ∀ q : Vtx, subOr R (d0 :: d1 :: q) = subOr Y q) :
    ∀ q : Vtx, q ≠ [] → row x w (d0 :: d1 :: q) = -(cval mR mY) * row x ws q := by
  intro q hq
  cases q with
  | nil => exact absurd rfl hq
  | cons e q =>
    have hne : (e :: q) ≠ ([] : Vtx) := List.cons_ne_nil e q
    simp only [row, List.cons_append, hsub, hamp, len_cons_cons_mod,
      dropLast_cons_cons d0 d1 hne]
    ring

lemma row_zero_gen {x : ℕ → Bool} {R : NNode} (w : W x R) {d0 d1 : Bool} {q : Vtx}
    (hq : q ≠ [])
    (hp0 : W.amp w (d0 :: d1 :: q.dropLast) = 0)
    (h1 : W.amp w (d0 :: d1 :: (q ++ [false])) = 0)
    (h2 : W.amp w (d0 :: d1 :: (q ++ [true])) = 0) :
    row x w (d0 :: d1 :: q) = 0 := by
  have hqd : (d0 :: d1 :: q).dropLast = d0 :: d1 :: q.dropLast :=
    dropLast_cons_cons d0 d1 hq
  simp only [row, hqd, List.cons_append, hp0, h1, h2, mul_zero, add_zero]

lemma row_LR_f (x : ℕ → Bool) {a b c d : NNode} (w1 : W x a) (w4 : W x d) :
    row x (W.nodeLR (b := b) (c := c) w1 w4) ([false] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeLR (b := b) (c := c) w1 w4) ([false, false] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves a.leaves) := by
    simp [W.amp_LR_ff, W.amp_nil]
  have h3 : W.amp (W.nodeLR (b := b) (c := c) w1 w4) ([false, true] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_f, subOr_ff,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := a.leaves + b.leaves) (my := a.leaves)
        (by have h := NNode.leaves_pos a; omega)
        (NNode.leaves_pos a)]
  ring

lemma row_RL_t (x : ℕ → Bool) {a b c d : NNode} (w2 : W x b) (w3 : W x c) :
    row x (W.nodeRL (a := a) (d := d) w2 w3) ([true] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeRL (a := a) (d := d) w2 w3) ([true, false] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) := by
    simp [W.amp_RL_tf, W.amp_nil]
  have h3 : W.amp (W.nodeRL (a := a) (d := d) w2 w3) ([true, true] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_t, subOr_tf,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := c.leaves + d.leaves) (my := c.leaves)
        (by have h := NNode.leaves_pos c; omega)
        (NNode.leaves_pos c)]
  ring

lemma row_LL_t (x : ℕ → Bool) {a b c d : NNode} (w1 : W x a) (w3 : W x c) :
    row x (W.nodeLL (b := b) (d := d) w1 w3) ([true] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeLL (b := b) (d := d) w1 w3) ([true, false] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves c.leaves) := by
    simp [W.amp_LL_tf, W.amp_nil]
  have h3 : W.amp (W.nodeLL (b := b) (d := d) w1 w3) ([true, true] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_t, subOr_tf,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := c.leaves + d.leaves) (my := c.leaves)
        (by have h := NNode.leaves_pos c; omega)
        (NNode.leaves_pos c)]
  ring

lemma row_LR_t (x : ℕ → Bool) {a b c d : NNode} (w1 : W x a) (w4 : W x d) :
    row x (W.nodeLR (b := b) (c := c) w1 w4) ([true] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeLR (b := b) (c := c) w1 w4) ([true, true] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) := by
    simp [W.amp_LR_tt, W.amp_nil]
  have h3 : W.amp (W.nodeLR (b := b) (c := c) w1 w4) ([true, false] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_t, subOr_tt,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := c.leaves + d.leaves) (my := d.leaves)
        (by have h := NNode.leaves_pos d; omega)
        (NNode.leaves_pos d)]
  ring

lemma row_RL_f (x : ℕ → Bool) {a b c d : NNode} (w2 : W x b) (w3 : W x c) :
    row x (W.nodeRL (a := a) (d := d) w2 w3) ([false] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeRL (a := a) (d := d) w2 w3) ([false, true] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) := by
    simp [W.amp_RL_ft, W.amp_nil]
  have h3 : W.amp (W.nodeRL (a := a) (d := d) w2 w3) ([false, false] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_f, subOr_ft,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := a.leaves + b.leaves) (my := b.leaves)
        (by have h := NNode.leaves_pos b; omega)
        (NNode.leaves_pos b)]
  ring

lemma row_RR_f (x : ℕ → Bool) {a b c d : NNode} (w2 : W x b) (w4 : W x d) :
    row x (W.nodeRR (a := a) (c := c) w2 w4) ([false] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeRR (a := a) (c := c) w2 w4) ([false, true] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves b.leaves) := by
    simp [W.amp_RR_ft, W.amp_nil]
  have h3 : W.amp (W.nodeRR (a := a) (c := c) w2 w4) ([false, false] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_f, subOr_ft,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := a.leaves + b.leaves) (my := b.leaves)
        (by have h := NNode.leaves_pos b; omega)
        (NNode.leaves_pos b)]
  ring

lemma row_RR_t (x : ℕ → Bool) {a b c d : NNode} (w2 : W x b) (w4 : W x d) :
    row x (W.nodeRR (a := a) (c := c) w2 w4) ([true] : Vtx) = 0 := by
  have h2 : W.amp (W.nodeRR (a := a) (c := c) w2 w4) ([true, true] : Vtx)
      = -(cval (NNode.node (NNode.node a b) (NNode.node c d)).leaves d.leaves) := by
    simp [W.amp_RR_tt, W.amp_nil]
  have h3 : W.amp (W.nodeRR (a := a) (c := c) w2 w4) ([true, false] : Vtx) = 0 := by
    apply W.amp_eq_zero_of_not_supp
    intro h; simp [W.supp] at h
  simp only [row, List.nil_append, List.cons_append, subOr_nil, subOr_t, subOr_tt,
    dropLast_single, length_single, List.length_nil, W.amp_nil, h2, h3, mul_zero, add_zero,
    mul_neg]
  norm_num
  rw [hEdge_cancel (mroot := a.leaves + b.leaves + (c.leaves + d.leaves))
        (mz := c.leaves + d.leaves) (my := d.leaves)
        (by have h := NNode.leaves_pos d; omega)
        (NNode.leaves_pos d)]
  ring

end Qatlib.Papers.NANDAmbainis07.MainResults

namespace Qatlib.Papers.NANDAmbainis07.MainResults

theorem lemma2_row_zero (x : ℕ → Bool) : {e : NNode} → (w : W x e) →
    ∀ p : Vtx, (e.sub p).isSome → row x w p = 0
  | _, W.leaf i, p, hp => by
      have hp' : p = [] := by
        rcases p with _ | ⟨d, q⟩
        · rfl
        · simp [NNode.sub] at hp
      subst hp'
      simp [row, W.amp]
  | _, @W.nodeLL _ a b c d w1 w3, p, hp => by
      rcases p with _ | ⟨d0, p1⟩
      · exact row_even_zero x _ [] rfl
      rcases p1 with _ | ⟨d1, q⟩
      · cases d0
        · exact row_LL_zL x w1 w3
        · exact row_LL_t x w1 w3
      · by_cases hpar : (d0 :: d1 :: q).length % 2 = 0
        · exact row_even_zero x _ _ hpar
        · have hqlen : q.length % 2 = 1 := by
            simp only [List.length_cons] at hpar; omega
          have hq : q ≠ [] := by intro h; rw [h] at hqlen; simp at hqlen
          cases d0 <;> cases d1
          · rw [row_scale (x := x) (w := W.nodeLL (b := b) (d := d) w1 w3) (ws := w1)
                (d0 := false) (d1 := false)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := a.leaves)
                (by intro r; simp [W.amp_LL_ff]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w1 q hp]
            ring
          · have hp0 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (false :: true :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (false :: true :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (false :: true :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · rw [row_scale (x := x) (w := W.nodeLL (b := b) (d := d) w1 w3) (ws := w3)
                (d0 := true) (d1 := false)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := c.leaves)
                (by intro r; simp [W.amp_LL_tf]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w3 q hp]
            ring
          · have hp0 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (true :: true :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (true :: true :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeLL (b := b) (d := d) w1 w3)
                (true :: true :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
  | _, @W.nodeLR _ a b c d w1 w4, p, hp => by
      rcases p with _ | ⟨d0, p1⟩
      · exact row_even_zero x _ [] rfl
      rcases p1 with _ | ⟨d1, q⟩
      · cases d0
        · exact row_LR_f x w1 w4
        · exact row_LR_t x w1 w4
      · by_cases hpar : (d0 :: d1 :: q).length % 2 = 0
        · exact row_even_zero x _ _ hpar
        · have hqlen : q.length % 2 = 1 := by
            simp only [List.length_cons] at hpar; omega
          have hq : q ≠ [] := by intro h; rw [h] at hqlen; simp at hqlen
          cases d0 <;> cases d1
          · rw [row_scale (x := x) (w := W.nodeLR (b := b) (c := c) w1 w4) (ws := w1)
                (d0 := false) (d1 := false)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := a.leaves)
                (by intro r; simp [W.amp_LR_ff]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w1 q hp]
            ring
          · have hp0 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (false :: true :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (false :: true :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (false :: true :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · have hp0 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (true :: false :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (true :: false :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeLR (b := b) (c := c) w1 w4)
                (true :: false :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · rw [row_scale (x := x) (w := W.nodeLR (b := b) (c := c) w1 w4) (ws := w4)
                (d0 := true) (d1 := true)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := d.leaves)
                (by intro r; simp [W.amp_LR_tt]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w4 q hp]
            ring
  | _, @W.nodeRL _ a b c d w2 w3, p, hp => by
      rcases p with _ | ⟨d0, p1⟩
      · exact row_even_zero x _ [] rfl
      rcases p1 with _ | ⟨d1, q⟩
      · cases d0
        · exact row_RL_f x w2 w3
        · exact row_RL_t x w2 w3
      · by_cases hpar : (d0 :: d1 :: q).length % 2 = 0
        · exact row_even_zero x _ _ hpar
        · have hqlen : q.length % 2 = 1 := by
            simp only [List.length_cons] at hpar; omega
          have hq : q ≠ [] := by intro h; rw [h] at hqlen; simp at hqlen
          cases d0 <;> cases d1
          · have hp0 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (false :: false :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (false :: false :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (false :: false :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · rw [row_scale (x := x) (w := W.nodeRL (a := a) (d := d) w2 w3) (ws := w2)
                (d0 := false) (d1 := true)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := b.leaves)
                (by intro r; simp [W.amp_RL_ft]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w2 q hp]
            ring
          · rw [row_scale (x := x) (w := W.nodeRL (a := a) (d := d) w2 w3) (ws := w3)
                (d0 := true) (d1 := false)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := c.leaves)
                (by intro r; simp [W.amp_RL_tf]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w3 q hp]
            ring
          · have hp0 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (true :: true :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (true :: true :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeRL (a := a) (d := d) w2 w3)
                (true :: true :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
  | _, @W.nodeRR _ a b c d w2 w4, p, hp => by
      rcases p with _ | ⟨d0, p1⟩
      · exact row_even_zero x _ [] rfl
      rcases p1 with _ | ⟨d1, q⟩
      · cases d0
        · exact row_RR_f x w2 w4
        · exact row_RR_t x w2 w4
      · by_cases hpar : (d0 :: d1 :: q).length % 2 = 0
        · exact row_even_zero x _ _ hpar
        · have hqlen : q.length % 2 = 1 := by
            simp only [List.length_cons] at hpar; omega
          have hq : q ≠ [] := by intro h; rw [h] at hqlen; simp at hqlen
          cases d0 <;> cases d1
          · have hp0 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (false :: false :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (false :: false :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (false :: false :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · rw [row_scale (x := x) (w := W.nodeRR (a := a) (c := c) w2 w4) (ws := w2)
                (d0 := false) (d1 := true)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := b.leaves)
                (by intro r; simp [W.amp_RR_ft]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w2 q hp]
            ring
          · have hp0 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (true :: false :: q.dropLast) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h1 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (true :: false :: (q ++ [false])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            have h2 : W.amp (W.nodeRR (a := a) (c := c) w2 w4)
                (true :: false :: (q ++ [true])) = 0 :=
              W.amp_eq_zero_of_not_supp _ _ (by intro h; simp [W.supp] at h)
            exact row_zero_gen _ hq hp0 h1 h2
          · rw [row_scale (x := x) (w := W.nodeRR (a := a) (c := c) w2 w4) (ws := w4)
                (d0 := true) (d1 := true)
                (mR := (NNode.node (NNode.node a b) (NNode.node c d)).leaves)
                (mY := d.leaves)
                (by intro r; simp [W.amp_RR_tt]) (fun r => rfl) q hq]
            rw [lemma2_row_zero x w4 q hp]
            ring

theorem lemma2_Hmul_eq_zero (x : ℕ → Bool) {e : NNode} (w : W x e) :
    ∀ p : Vtx, (e.sub p).isSome → Hmul e (W.amp w) p = 0 := by
  intro p hp
  rw [← row_eq_Hmul]
  exact lemma2_row_zero x w p hp

end Qatlib.Papers.NANDAmbainis07.MainResults
