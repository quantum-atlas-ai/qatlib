/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.List.Basic

@[expose] public section




/-!
# Dual-ancilla linearization of the Navier-Stokes pattern

This file covers the mathematical core of Sect. 6 of the QHAM paper
(Xue et al., arXiv:2411.06759v2, Sci. China-Phys. Mech. Astron. 68, 104702):
the dual (x, t) auxiliary-space linearization of cubic terms that carry a
time derivative, and the order-sum termination argument of its Sect. 2.2.

Two groups of results.

* The readout identity: for the triple product variable
  `W(p1, p2, p3) = f p1 * g p2 * h p3`, differentiation in the time
  coordinate of the third ancilla space touches only the third factor,
  so the nonlinear term `f * g * dt h` is recovered from `W` by a linear
  readout operator (Eq. (108)/(109) of the paper). Linearity of the
  readout in `W` is proved as well.
* Termination: the lift generation replaces one factor of homotopy order
  `a` by monomials of total order at most `a - 1`, so the order sum
  strictly decreases at every generation and the variable tree is finite,
  halting on order-zero data fixed by the initial guess (Eq. (31) and the
  halting discussion of the paper).

Coverage is partial by design: this file formalizes the linearization
mechanism and its termination for the representative cubic pattern, not
the full Navier-Stokes pipeline nor any resource statement.
-/

namespace Qatlib.Papers.QHamXue25.NSDualLift

/-! ## The readout identity of Eq. (108)/(109) -/

/-- The product variable of Eq. (108): one ancilla copy of space-time per
factor, values multiplied pointwise on the product space. -/
def triple (f g h : ℝ × ℝ → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
  fun p => f p.1 * g p.2.1 * h p.2.2

/-- Differentiating the triple product in the time coordinate of the third
ancilla space touches only the third factor: this is the computation behind
Eq. (109), stated on time slices. The derivative `h' (0, 1)` is the partial
time derivative of `h` at `(x, t)`. -/
theorem ancilla_deriv_triple (f g h : ℝ × ℝ → ℝ) (a b : ℝ × ℝ) (x t : ℝ)
    {h' : (ℝ × ℝ) →L[ℝ] ℝ} (dh : HasFDerivAt h h' (x, t)) :
    HasDerivAt (fun s => f a * g b * h (x, s)) (f a * g b * h' (0, 1)) t := by
  have hpath : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have hcomp : HasFDerivAt (h ∘ (fun s : ℝ => (x, s)))
      (h'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    HasFDerivAt.comp (hg := dh) (hf := hpath)
  have hslice : HasDerivAt (fun s : ℝ => h (x, s)) (h' (0, 1)) t :=
    HasFDerivAt.hasDerivAt hcomp
  exact HasDerivAt.const_mul (f a * g b) hslice

/-- On the diagonal, the readout of the triple product is exactly the cubic
term with a time derivative of Eq. (108): evaluating
`ancilla_deriv_triple` at `a = b = (x, t)` recovers
`f (x, t) * g (x, t) * ∂ₜ h (x, t)` from `triple f g h`. -/
theorem eq109_on_diagonal (f g h : ℝ × ℝ → ℝ) (x t : ℝ)
    {h' : (ℝ × ℝ) →L[ℝ] ℝ} (dh : HasFDerivAt h h' (x, t)) :
    HasDerivAt (fun s => triple f g h ((x, t), (x, t), (x, s)))
      (f (x, t) * g (x, t) * h' (0, 1)) t :=
  ancilla_deriv_triple f g h (x, t) (x, t) x t dh

/-- The readout operator of the lift: restrict a product-space function to
the diagonal in the first two slots and to the time slice `x` in the third,
leaving the third time coordinate free. -/
def readout (W : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (x t : ℝ) : ℝ → ℝ :=
  fun s => W ((x, t), (x, t), (x, s))

/-- The readout operator is linear in the product-space function: diagonal
restriction followed by a single-variable derivative is a linear operation,
which is why lifting a nonlinear monomial to `W` makes it accessible to a
quantum linear system solver. -/
theorem readout_linear (W₁ W₂ : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (c₁ c₂ x t d₁ d₂ : ℝ)
    (H₁ : HasDerivAt (readout W₁ x t) d₁ t)
    (H₂ : HasDerivAt (readout W₂ x t) d₂ t) :
    HasDerivAt (readout (fun p => c₁ * W₁ p + c₂ * W₂ p) x t) (c₁ * d₁ + c₂ * d₂) t :=
  HasDerivAt.add (HasDerivAt.const_mul c₁ H₁) (HasDerivAt.const_mul c₂ H₂)

/-! ## Order-sum descent and termination of the lift -/

/-- One generation step of the lift, in arithmetic form (Eq. (31)): a factor
of homotopy order `a ≥ 1` is replaced by the monomials of its own deformation
right-hand side, whose order sum is at most `a - 1`. Order-zero factors
generate nothing, because the initial guess satisfies the linear part and
its data are known functions. -/
inductive Lifts : List ℕ → List ℕ → Prop
  | mk (pre post : List ℕ) (a : ℕ) (bs : List ℕ) (ha : 1 ≤ a)
      (hle : bs.sum ≤ a - 1) : Lifts (pre ++ a :: post) (pre ++ bs ++ post)

/-- Prefixing a fixed factor in front of a lift keeps it a lift: the lifted
position simply moves deeper into the list. -/
theorem Lifts.cons_lift (c : ℕ) {L M : List ℕ} (hlm : Lifts L M) :
    Lifts (c :: L) (c :: M) := by
  obtain ⟨pre, post, a, bs, ha, hle⟩ := hlm
  exact Lifts.mk (c :: pre) post a bs ha hle

/-- Every generation step strictly decreases the order sum, which is the
descent of Eq. (31). -/
theorem Lifts.sum_lt {L M : List ℕ} (hlm : Lifts L M) : M.sum < L.sum := by
  obtain ⟨pre, post, a, bs, ha, hle⟩ := hlm
  have hsplit : (pre ++ bs ++ post).sum = pre.sum + bs.sum + post.sum := by
    simp only [List.sum_append]
  have horig : (pre ++ a :: post).sum = pre.sum + a + post.sum := by
    simp only [List.sum_append, List.sum_cons]
    omega
  have hzero : bs.sum < a := by omega
  rw [hsplit, horig]
  omega

/-- Any list with positive order sum generates at least one child: some
factor has order `a ≥ 1`, and dropping it to order zero is a legal lift
with `bs = []`. -/
theorem exists_lift_of_pos : ∀ L : List ℕ, 0 < L.sum → ∃ M, Lifts L M := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro h
    by_cases ha : 1 ≤ a
    · exact ⟨rest, Lifts.mk [] rest a [] ha (Nat.zero_le _)⟩
    · have ha0 : a = 0 := by omega
      subst ha0
      have h' : 0 < rest.sum := by
        simp only [List.sum_cons] at h
        omega
      obtain ⟨M, hm⟩ := ih h'
      exact ⟨0 :: M, hm.cons_lift 0⟩

/-- Bounded-height trees for the generation relation. `HasHeight n L` says
that the variable tree rooted at `L` has height at most `n`: leaves carry
no children at all, and inner nodes need a uniform bound for all children. -/
inductive HasHeight : ℕ → List ℕ → Prop
  | stop (L : List ℕ) (h : ∀ M, ¬ Lifts L M) : HasHeight 0 L
  | step (n : ℕ) (L : List ℕ) (h : ∀ M, Lifts L M → HasHeight n M) :
      HasHeight (n + 1) L

/-- A childless node counts as a tree of any height: height bounds are
upper bounds. -/
theorem HasHeight.stop_any (m : ℕ) {L : List ℕ} (hno : ∀ M, ¬ Lifts L M) :
    HasHeight m L := by
  induction m with
  | zero => exact HasHeight.stop L hno
  | succ k => exact HasHeight.step k L (fun M hlm => absurd hlm (hno M))

/-- Height bounds can be weakened. -/
theorem HasHeight.mono {n : ℕ} {L : List ℕ} (h : HasHeight n L) :
    ∀ m : ℕ, n ≤ m → HasHeight m L := by
  induction h with
  | stop L hno => intro m _; exact HasHeight.stop_any m hno
  | step n L hchildren ih =>
    intro m hnm
    cases m with
    | zero => omega
    | succ k =>
      refine HasHeight.step k L (fun M hlm => ?_)
      exact ih M hlm k (by omega)

/-- Termination of the lift: every variable tree has height at most its
order sum. The proof is strong induction on the order sum: by
`Lifts.sum_lt`, every child has strictly smaller sum, and the induction
hypothesis gives each child a tree of height at most its own sum, which is
weakened to the uniform bound `L.sum - 1`. This is the arithmetic form of
the halting argument of the paper: the process ends on products of
order-zero factors, whose data are fixed by the initial guess. -/
theorem lift_terminates (s : ℕ) : ∀ L : List ℕ, L.sum ≤ s → HasHeight L.sum L := by
  induction s with
  | zero =>
    intro L hL
    rw [show L.sum = 0 from by omega]
    exact HasHeight.stop L (fun M hlm => absurd hlm.sum_lt (by omega))
  | succ k ih =>
    intro L hL
    by_cases hpos : 0 < L.sum
    · have hchild : ∀ M', Lifts L M' → HasHeight (L.sum - 1) M' := by
        intro M' hlm'
        have hlt : M'.sum < L.sum := hlm'.sum_lt
        have hle : M'.sum ≤ k := by omega
        exact HasHeight.mono (ih M' hle) (L.sum - 1)
          (show M'.sum ≤ L.sum - 1 by omega)
      rw [show L.sum = L.sum - 1 + 1 from by omega]
      exact HasHeight.step (L.sum - 1) L hchild
    · rw [show L.sum = 0 from by omega]
      exact HasHeight.stop L (fun M hlm => absurd hlm.sum_lt (by omega))

/-- Every variable tree is finite, with an explicit height bound: the lift
of a finite homotopy truncation terminates. -/
theorem lift_tree_bounded (L : List ℕ) : ∃ n, HasHeight n L ∧ n ≤ L.sum :=
  ⟨L.sum, lift_terminates L.sum L le_rfl, le_rfl⟩

end Qatlib.Papers.QHamXue25.NSDualLift
