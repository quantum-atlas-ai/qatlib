/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PepsTransfer.OpenGridPeps.Defs

@[expose] public section


/-!
# Exact complex double-layer expectation

Verstraete--Cirac, arXiv:cond-mat/0407066v1, p. 2, Eqs. (2)--(3).
The amplitude is the contraction of the local ket tensors. The observable
is independently the tensor-product matrix, acting by ordinary `mulVec`;
its expectation is the conjugate-linear bra/linear ket `dotProduct`.
Finite distributivity proves that this equals the contraction of the local
double tensors. No reality, diagonal-observable or efficient-contraction
assumption is used. `Bond` is the entire assignment of virtual bonds and
`legs` supplies the incidences, allowing general finite geometries.

The displayed Eq. (3) uses the unconjugated tensor first. With standard
row/column matrix entries this requires the transposed observable; the
explicit `sourceSwap` theorem records that index convention rather than
silently identifying the transpose with the original complex observable.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RenormAlg04.MainResults

variable {Site Phys Bond Leg : Type*}
  [Fintype Site] [Fintype Phys] [Fintype Bond] [DecidableEq Site]

/-- Contract the virtual bonds to obtain the physical ket amplitude. -/
def netAmp (A : Site → Phys → Leg → ℂ) (legs : Bond → Site → Leg)
    (x : Site → Phys) : ℂ :=
  ∑ b : Bond, ∏ p : Site, A p (x p) (legs b p)

/-- A local double tensor with the standard conjugate-linear bra convention. -/
def doubleSite (A : Site → Phys → Leg → ℂ) (O : Site → Phys → Phys → ℂ)
    (p : Site) (l r : Leg) : ℂ :=
  ∑ s : Phys, ∑ t : Phys, star (A p s l) * O p s t * A p t r

/-- Contract both independent virtual layers with the same incidence pattern. -/
def netContract (E : Site → Leg → Leg → ℂ) (legs : Bond → Site → Leg) : ℂ :=
  ∑ b : Bond, ∑ c : Bond, ∏ p : Site, E p (legs b p) (legs c p)

/-- The physical tensor-product observable, with row index first. -/
def productObs (O : Site → Phys → Phys → ℂ) :
    Matrix (Site → Phys) (Site → Phys) ℂ :=
  fun x y => ∏ p : Site, O p (x p) (y p)

omit [Fintype Phys] [DecidableEq Site] in
/-- Conjugation commutes with the finite virtual contraction. -/
theorem star_netAmp (A : Site → Phys → Leg → ℂ) (legs : Bond → Site → Leg)
    (x : Site → Phys) :
    star (netAmp A legs x) = ∑ b : Bond, ∏ p : Site, star (A p (x p) (legs b p)) := by
  simp only [netAmp, star_sum, star_prod]

private def pairEquiv : (Site → Phys × Phys) ≃ (Site → Phys) × (Site → Phys) where
  toFun q := (fun p => (q p).1, fun p => (q p).2)
  invFun q p := (q.1 p, q.2 p)
  left_inv _ := rfl
  right_inv q := by cases q; rfl

/-- Separate the two physical configurations in a sum over paired indices. -/
theorem pairSum (f : (Site → Phys × Phys) → ℂ) :
    (∑ q, f q) = ∑ x : Site → Phys, ∑ y : Site → Phys, f (fun p => (x p, y p)) := by
  rw [← Fintype.sum_prod_type
    (f := fun q : (Site → Phys) × (Site → Phys) => f (fun p => (q.1 p, q.2 p)))]
  exact Fintype.sum_equiv pairEquiv f
    (fun q : (Site → Phys) × (Site → Phys) => f (fun p => (q.1 p, q.2 p)))
    (fun _ => rfl)

/-- Rotate the virtual and physical finite sums without an analytic limit. -/
theorem fourSum {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  have hL : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ p : α × β, ∑ q : γ × δ, F p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  have hR : (∑ c, ∑ d, ∑ a, ∑ b, F a b c d) =
      ∑ q : γ × δ, ∑ p : α × β, F p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR, Finset.sum_comm]

/-- The double network equals the actual complex bra-ket expectation. -/
theorem expContract (A : Site → Phys → Leg → ℂ) (O : Site → Phys → Phys → ℂ)
    (legs : Bond → Site → Leg) :
    netContract (doubleSite A O) legs =
      dotProduct (star (netAmp A legs)) ((productObs O).mulVec (netAmp A legs)) := by
  classical
  unfold netContract doubleSite
  have hstep (b c : Bond) :
      (∏ p : Site, ∑ s : Phys, ∑ t : Phys,
          star (A p s (legs b p)) * O p s t * A p t (legs c p)) =
        ∑ x : Site → Phys, ∑ y : Site → Phys,
          ∏ p : Site, star (A p (x p) (legs b p)) * O p (x p) (y p) *
            A p (y p) (legs c p) := by
    have hsite (p : Site) :
        (∑ s : Phys, ∑ t : Phys,
          star (A p s (legs b p)) * O p s t * A p t (legs c p)) =
        ∑ q : Phys × Phys, star (A p q.1 (legs b p)) * O p q.1 q.2 *
          A p q.2 (legs c p) := by
      rw [Fintype.sum_prod_type]
    simp_rw [hsite]
    rw [Finset.prod_univ_sum (fun _ : Site => (Finset.univ : Finset (Phys × Phys)))]
    simpa using pairSum (fun q : Site → Phys × Phys =>
      ∏ p : Site, star (A p (q p).1 (legs b p)) * O p (q p).1 (q p).2 *
        A p (q p).2 (legs c p))
  simp only [hstep]
  rw [fourSum]
  simp only [dotProduct, Matrix.mulVec, productObs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.star_apply, star_netAmp]
  simp only [Finset.prod_mul_distrib, netAmp]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_assoc _ _ _

omit [Fintype Site] [DecidableEq Site] in
/-- The paper's ket-first double tensor is the transpose-observable convention. -/
theorem sourceSwap (A : Site → Phys → Leg → ℂ) (O : Site → Phys → Phys → ℂ)
    (p : Site) (l r : Leg) :
    (∑ s : Phys, ∑ t : Phys, O p s t * A p s l * star (A p t r)) =
      doubleSite A (fun p s t => O p t s) p r l := by
  unfold doubleSite
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  ac_rfl

/-- The printed ket-first convention contracts to the transpose expectation. -/
theorem sourceContract (A : Site → Phys → Leg → ℂ) (O : Site → Phys → Phys → ℂ)
    (legs : Bond → Site → Leg) :
    netContract (fun p l r =>
      ∑ s : Phys, ∑ t : Phys, O p s t * A p s l * star (A p t r)) legs =
      dotProduct (star (netAmp A legs))
        ((productObs (fun p s t => O p t s)).mulVec (netAmp A legs)) := by
  rw [← expContract]
  unfold netContract
  simp only [sourceSwap]
  rw [Finset.sum_comm]

/-- The printed formula gives the original expectation for symmetric local matrices. -/
theorem sourceSymm (A : Site → Phys → Leg → ℂ) (O : Site → Phys → Phys → ℂ)
    (legs : Bond → Site → Leg) (hO : ∀ p s t, O p s t = O p t s) :
    netContract (fun p l r =>
      ∑ s : Phys, ∑ t : Phys, O p s t * A p s l * star (A p t r)) legs =
      dotProduct (star (netAmp A legs)) ((productObs O).mulVec (netAmp A legs)) := by
  have ht : (fun p s t => O p t s) = O := by
    funext p s t
    exact hO p t s
  rw [sourceContract, ht]

/-! ## Canonical rectangular open-boundary specialization -/

open Qatlib.Concepts.PepsTransfer.OpenGridPeps

/-- The independent internal horizontal and vertical virtual assignments. -/
abbrev GridBonds (a b D : ℕ) :=
  (Fin a × Fin (b - 1) → Fin D) × (Fin (a - 1) × Fin b → Fin D)

/-- Four virtual legs at a site, ordered up, down, left, right. -/
abbrev GridLeg (D : ℕ) := Fin D × Fin D × Fin D × Fin D

/-- Extract internal legs and fix every missing boundary leg to zero. -/
def gridLegs {a b D : ℕ} (hD : 0 < D) (q : GridBonds a b D)
    (p : Fin a × Fin b) : GridLeg D :=
  let z : Fin D := ⟨0, hD⟩
  (if hi : 0 < p.1.val then q.2 (⟨p.1.val - 1, by omega⟩, p.2) else z,
   if hi : p.1.val + 1 < a then q.2 (⟨p.1.val, by omega⟩, p.2) else z,
   if hj : 0 < p.2.val then q.1 (p.1, ⟨p.2.val - 1, by omega⟩) else z,
   if hj : p.2.val + 1 < b then q.1 (p.1, ⟨p.2.val, by omega⟩) else z)

/-- Read a canonical four-leg PEPS tensor using the generic contraction interface. -/
def gridTensor {a b d D : ℕ} (A : Tensor a b d D)
    (p : Fin a × Fin b) (s : Fin d) (l : GridLeg D) : ℂ :=
  A p.1 p.2 s l.1 l.2.1 l.2.2.1 l.2.2.2

/-- The generic amplitude is the canonical internal-bond-only PEPS amplitude. -/
theorem gridAmp {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D)
    (x : (Fin a × Fin b) → Fin d) :
    netAmp (gridTensor A) (gridLegs hD) x =
      amplitude hD A (fun i j => x (i, j)) := by
  classical
  simp only [netAmp, amplitude, Fintype.sum_prod_type, Fintype.prod_prod_type]
  rfl

/-- An arbitrary complex product observable has the exact open-grid double contraction. -/
theorem gridExp {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D)
    (O : (Fin a × Fin b) → Fin d → Fin d → ℂ) :
    netContract (doubleSite (gridTensor A) O) (gridLegs hD) =
      dotProduct (star (fun x => amplitude hD A (fun i j => x (i, j))))
        ((productObs O).mulVec (fun x => amplitude hD A (fun i j => x (i, j)))) := by
  have hfun : netAmp (gridTensor A) (gridLegs hD) =
      fun x => amplitude hD A (fun i j => x (i, j)) := funext (gridAmp hD A)
  rw [expContract, hfun]


end Qatlib.Papers.RenormAlg04.MainResults
