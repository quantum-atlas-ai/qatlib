/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.EquivFin

set_option backward.isDefEq.respectTransparency false

/-!
# AdversaryKSum12 — source model definitions

Belovs--Špalek, "Adversary Lower Bound for the k-sum Problem", fixed
arXiv:1206.6528v2 (9 Aug 2012).

This file formalises the objects used by the paper's main construction:

* Definition 2 (p.2): orthogonal arrays of length `k` over an alphabet `α`.
* The k-sum problem and the k-orthogonal-array problem (p.2).
* The Hamming-association-scheme projectors `E_m^{(d)}` (p.4), represented by
  their entries in the standard basis: `E_m^{(d)}[u,v]` is the sum over
  `m`-element coordinate sets of `∏_{j∈T}(δ_{u_j v_j} - 1/q)` on `T` and `1/q`
  off `T`.  This is the entry form of the tensor product of `E_0 = J_q/q` and
  `E_1 = I - J_q/q` over the chosen coordinates.
* Definition 8 (p.5): `F_S = √q · (E_{<k}^{(k)})|_{T_S}`.
* Equations (2) and (4) (pp.4–5): the stacked adversary matrix `Γ̃` with blocks
  `G̃_S = Σ_m α_m F_S ⊗ E_m^{(n-k)}`.
* Definition 6 (p.3): the query filter `Δ_i`.
* Lemma 11 (p.7): the column mask `removeIllegal` deleting illegal columns.
* Equation (8) (p.7): the optimised coefficient sequence `α_m`.

Everything is a real matrix; `‖·‖` is the `L2Operator` (spectral) norm when
`open scoped Matrix.Norms.L2Operator` is active.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

namespace Qatlib.Papers.AdversaryKSum12.ArrayWitness

/-! ## Definition 2 — orthogonal arrays -/

/-- Overwrite the `i`-th coordinate with `a`. -/
def extendTuple {α : Type} {k : ℕ} (i : Fin k) (g : {j : Fin k // j ≠ i} → α) (a : α) :
    Fin k → α :=
  fun j => if h : j = i then a else g ⟨j, h⟩

/-- **Definition 2 (p.2).**  `T ⊆ [q]^k` is an orthogonal array of length `k`:

for every index `i` and every assignment of the other `k-1` coordinates there
is exactly one value of the `i`-th coordinate completing the tuple into `T`.

The cardinality condition `|T| = q^{k-1}` is a consequence; see
`IsOrthogonalArray.card_eq`. -/
def IsOrthogonalArray {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (T : Finset (Fin k → α)) : Prop :=
  ∀ (i : Fin k) (g : {j : Fin k // j ≠ i} → α), ∃! a : α, extendTuple i g a ∈ T

/-- A tuple agrees with `g` off the `i`-th coordinate. -/
theorem extendTuple_apply_of_ne {α : Type} {k : ℕ} (i : Fin k)
    (g : {j : Fin k // j ≠ i} → α) (a : α) (j : Fin k) (hj : j ≠ i) :
    extendTuple i g a j = g ⟨j, hj⟩ := by
  simp [extendTuple, hj]

/-- Reconstructing a tuple from its coordinate `i` and its restriction. -/
theorem extendTuple_apply_self {α : Type} {k : ℕ} (i : Fin k)
    (g : {j : Fin k // j ≠ i} → α) (a : α) :
    extendTuple i g a i = a := by
  simp [extendTuple]

/-- Rebuilding a tuple from coordinate `i` and its restriction to the other
coordinates gives back the tuple. -/
theorem extendTuple_self {α : Type} {k : ℕ} (i : Fin k) (f : Fin k → α) :
    extendTuple i (fun j => f j.1) (f i) = f := by
  funext j
  by_cases h : j = i
  · subst h; simp [extendTuple]
  · simp [extendTuple, h]

/-- **Definition 2, cardinality.**  An orthogonal array of length `k ≥ 1` has
exactly `|α|^{k-1}` elements.  This is the `card` half of Definition 2, proved
from the unique-completion half by the restriction map at coordinate `0`. -/
theorem IsOrthogonalArray.card_eq {α : Type} [Fintype α] [DecidableEq α]
    {k : ℕ} {T : Finset (Fin k → α)} (hT : IsOrthogonalArray T) (hk : 1 ≤ k) :
    T.card = Fintype.card α ^ (k - 1) := by
  classical
  let i : Fin k := ⟨0, hk⟩
  have hcard : Fintype.card {j : Fin k // j ≠ i} = k - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin k => j = i), Fintype.card_subtype_eq]
    simp [Fintype.card_fin]
  have hbij : T.card = Fintype.card ({j : Fin k // j ≠ i} → α) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun a _ => fun j => a j.1) (fun a _ => Finset.mem_univ _)
      ?_ ?_
    · intro a ha b hb hab
      have hg : ∀ j : {j : Fin k // j ≠ i}, a j.1 = b j.1 := fun j => congrFun hab j
      have hga : (fun j : {j : Fin k // j ≠ i} => a j.1) =
          (fun j => b j.1) := funext hg
      have hae : extendTuple i (fun j => a j.1) (a i) ∈ T := by
        rw [extendTuple_self]; exact ha
      have hbe : extendTuple i (fun j => a j.1) (b i) ∈ T := by
        rw [hga, extendTuple_self]; exact hb
      have huniq : a i = b i := (hT i (fun j => a j.1)).unique hae hbe
      funext j
      by_cases h : j = i
      · subst h; exact huniq
      · exact hg ⟨j, h⟩
    · intro g _
      obtain ⟨a, ha, -⟩ := hT i g
      refine ⟨extendTuple i g a, ha, ?_⟩
      funext j
      exact extendTuple_apply_of_ne i g a j.1 j.2
  rw [hbij, Fintype.card_fun, hcard]

/-! ## The k-sum and k-orthogonal-array problems (p.2) -/

/-- The projection of an input on an ordered `k`-subset `S`, written with the
elements of `S` in increasing order (the paper's `x_S`). -/
def restrictTo {q n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (x : Fin n → Fin q) :
    Fin k → Fin q :=
  fun i => x (S.orderEmbOfFin hS i)

/-- The projection on the complement of an ordered `k`-subset. -/
def restrictCompl {q n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (x : Fin n → Fin q) :
    Fin (n - k) → Fin q :=
  fun i => x ((Sᶜ).orderEmbOfFin (by
    rw [Finset.card_compl, Fintype.card_fin, hS]) i)

/-- **The k-sum problem** (p.1): the input `x : [n] → G` contains a `k`-subset
summing to `t`. -/
def KSumProblem {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (t : G) (k : ℕ) {n : ℕ} (x : Fin n → G) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ ∑ i ∈ S, x i = t

/-- **The k-orthogonal-array problem** (p.2): some `k`-subset of the input
belongs to the corresponding orthogonal array. -/
def KOrthArrayProblem {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (x : Fin n → Fin q) : Prop :=
  ∃ (S : Finset (Fin n)) (hS : S.card = k), restrictTo S hS x ∈ T S hS

/-! ## The Hamming-association-scheme projectors (p.4) -/

/-- Entry `(u,v)` of the weight-`m` projector `E_m^{(d)}` of the Hamming
association scheme on `[q]^d`, in the standard basis.

`E_0 = J_q / q` and `E_1 = I - J_q / q`; the weight-`m` projector is the sum
over `m`-element coordinate sets of `E_1` on the set and `E_0` on its
complement, which gives the displayed product formula. -/
def assocEntry (q d m : ℕ) (u v : Fin d → Fin q) : ℝ :=
  ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin d) => T.card = m)),
    ∏ j : Fin d,
      if j ∈ T then (if u j = v j then (1 : ℝ) - (q : ℝ)⁻¹ else -(q : ℝ)⁻¹)
      else (q : ℝ)⁻¹

/-- The weight-`m` association-scheme projector as a real matrix. -/
def assocProjector (q d m : ℕ) : Matrix (Fin d → Fin q) (Fin d → Fin q) ℝ :=
  fun u v => assocEntry q d m u v

/-- **Definition 8 (p.5).**  `F_S = √q` times the sub-matrix of
`E_{<k}^{(k)} = I - E_k^{(k)}` consisting of the rows in `T_S`. -/
def sourceF (q k : ℕ) (T : Finset (Fin k → Fin q)) :
    Matrix ↥T (Fin k → Fin q) ℝ :=
  fun a v =>
    Real.sqrt (q : ℝ) *
      ((if a.1 = v then (1 : ℝ) else 0) - assocEntry q k k a.1 v)

/-! ## The stacked adversary matrix `Γ̃` (Eqs. (2),(4)) -/

/-- Row labels of `Γ̃`: a `k`-subset `S` together with the full input `x`.
Rows with `x_S ∉ T_S` are present but carry the zero row; this does not change
the spectral norm and avoids a dependent subtype. -/
abbrev AdvRow (q n k : ℕ) := { S : Finset (Fin n) // S.card = k } × (Fin n → Fin q)

/-- **Equations (2) and (4) (pp.4–5).**  The adversary matrix `Γ̃`: the vertical
stack, over all `k`-subsets `S`, of the blocks
`G̃_S = Σ_{m=0}^{n-k} α_m · F_S ⊗ E_m^{(n-k)}`.

The row labelled `(S,x)` with `x_S ∈ T_S` carries the block entry
`Σ_m α_m F_S[x_S, y_S] E_m^{(n-k)}[x_{Sᶜ}, y_{Sᶜ}]`; the row is zero when
`x_S ∉ T_S`. -/
def advGamma (q n k : ℕ)
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (α : ℕ → ℝ) : Matrix (AdvRow q n k) (Fin n → Fin q) ℝ :=
  fun r y =>
    if hx : restrictTo r.1.1 r.1.2 r.2 ∈ T r.1.1 r.1.2 then
      ∑ m ∈ Finset.range (n - k + 1),
        α m * sourceF q k (T r.1.1 r.1.2) ⟨restrictTo r.1.1 r.1.2 r.2, hx⟩
                (restrictTo r.1.1 r.1.2 y) *
              assocProjector q (n - k) m (restrictCompl r.1.1 r.1.2 r.2)
                (restrictCompl r.1.1 r.1.2 y)
    else 0

/-! ## The query filter `Δ_i` (Definition 6, p.3) -/

/-- **Definition 6 (p.3).**  `Δ_i[(x,a),(y,b)] = 1` when `x_i ≠ y_i` and `0`
otherwise.  Here rows and columns are labelled by inputs; the row label type is
the same `AdvRow` as for `Γ̃` (multiplicities on the positive side do not enter
the definition of `Δ_i`). -/
def deltaAt (q n k : ℕ) (i : Fin n) : Matrix (AdvRow q n k) (Fin n → Fin q) ℝ :=
  fun r y => if r.2 i = y i then 0 else 1

/-! ## Lemma 11 — removing illegal columns (p.7) -/

/-- A column `y` is illegal when some `k`-subset of it lies in the
corresponding orthogonal array (i.e. `f(y) = 1`). -/
def IsIllegal {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (y : Fin n → Fin q) : Prop :=
  ∃ (S : Finset (Fin n)) (hS : S.card = k), restrictTo S hS y ∈ T S hS

instance {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q)) :
    DecidablePred (IsIllegal T) := by
  intro y
  unfold IsIllegal
  infer_instance

/-- **Lemma 11 (p.7), column operation.**  `Γ` is `Γ̃` with the illegal columns
removed.  We represent column deletion by zeroing those columns: this is an
isometry on the column space and leaves the spectral norm unchanged. -/
def removeIllegal {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (Γ : Matrix (AdvRow q n k) (Fin n → Fin q) ℝ) :
    Matrix (AdvRow q n k) (Fin n → Fin q) ℝ :=
  fun r y => if IsIllegal T y then 0 else Γ r y

/-- The `0/1` diagonal of legal columns. -/
def legalDiagonal {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q)) :
    (Fin n → Fin q) → ℝ :=
  fun y => if IsIllegal T y then 0 else 1

/-! ## The optimised coefficient sequence (Eq. (8), p.7) -/

/-- **Equation (8) (p.7).**
`α_m = max{2 − m / n^{k/(k+1)}, 0} · n^{k(1−k)/(2(k+1))}`. -/
def alphaOpt (n k : ℕ) : ℕ → ℝ :=
  fun m =>
    max (2 - (m : ℝ) / (n : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) 0 *
      (n : ℝ) ^ (((k : ℝ) * (1 - (k : ℝ))) / (2 * ((k : ℝ) + 1)))

/-- The maximum of `α` over `m = 0, …, N`. -/
def maxAlpha (α : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩ α

end Qatlib.Papers.AdversaryKSum12.ArrayWitness
