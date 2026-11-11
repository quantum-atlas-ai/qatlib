/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PetzRecovery26.VirtualAdjoint.Model

set_option backward.isDefEq.respectTransparency false

/-!
# No-go for universal complex conjugation (Theorem 1)

Fixed source version: arXiv:2602.05828v1 (2026-02-05), Theorem 1 on p. 3, and
the proof of Theorem 1 which invokes the impossibility of a universal
state-transposition map (Refs. [36, 37] of the paper).

The mathematical core is finite-dimensional and is proven completely here:

* `choi_transposeMap`: the Choi matrix of the transpose map `Nᵀ` is the flip
  (SWAP) operator `F` (p. 3, Notation);
* `flip_not_posSemidef`: for `dim ≥ 2` the flip operator is not positive
  semidefinite (it has the `2×2` block `[[0,1],[1,0]]`);
* `transposeMap_not_completelyPositive`: hence the transpose map is not
  completely positive (Choi's theorem);
* `no_universal_state_transpose`: a completely positive map cannot transpose
  every quantum state;
* `conjMap_statePrep`: the complex conjugate of the state-preparation channel
  `R_ρ` is `R_{ρᵀ}` (used in the paper's reduction);
* `source_theorem1_no_go`: the paper's contradiction, showing that no
  supermap action that (i) is completely positive on the state-preparation
  family and (ii) universally realizes the complex conjugate can exist.
  The hypothesis `hinduced` is the Choi-matrix form of "the supermap is
  completely positive"; see the docstring of `source_theorem1_no_go` for the
  precise relation to the paper's `n`-slot statement.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## The Choi matrix of the transpose map is the flip operator -/

-- `choi_transposeMap` is proven in `Model` (shared with Theorem 3).

/-! ## The flip operator is not positive semidefinite -/

/-- The `2×2` block of the flip operator on the two states `(0,1)` and `(1,0)`
is `[[0,1],[1,0]]`, and this matrix is not positive semidefinite: its quadratic
form on `(1,-1)` equals `-2`. -/
theorem flip_not_posSemidef_fin2 :
    ¬ (flip : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).PosSemidef := by
  intro h
  let e : Fin 2 → Fin 2 × Fin 2 := fun i => if i = 0 then (0, 1) else (1, 0)
  have hsub : (flip.submatrix e e : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := h.submatrix e
  have heq : (flip.submatrix e e : Matrix (Fin 2) (Fin 2) ℂ) = !![(0 : ℂ), 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.submatrix, flip, e]
  rw [heq] at hsub
  let v : Fin 2 → ℂ := ![(1 : ℂ), -1]
  have hnn := hsub.re_dotProduct_nonneg v
  have hcalc :
      RCLike.re (star v ⬝ᵥ ((!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)) = -2 := by
    simp only [v, Matrix.mulVec, dotProduct, Pi.star_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  rw [hcalc] at hnn
  norm_num at hnn

/-- For systems of dimension at least two, the flip (SWAP) operator is not
positive semidefinite. -/
theorem flip_not_posSemidef [Nontrivial A] :
    ¬ (flip : Matrix (A × A) (A × A) ℂ).PosSemidef := by
  intro h
  obtain ⟨a0, a1, hne⟩ := exists_pair_ne A
  let a : Fin 2 → A := fun i => if i = 0 then a0 else a1
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let e : Fin 2 × Fin 2 → A × A := fun x => (a x.1, a x.2)
  have hsub : (flip.submatrix e e : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).PosSemidef :=
    h.submatrix e
  have heq : (flip.submatrix e e : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = flip := by
    ext x y
    simp only [Matrix.submatrix_apply, flip_apply, e, ha.eq_iff]
  exact flip_not_posSemidef_fin2 (heq ▸ hsub)

/-! ## The transpose map is not completely positive -/

/-- The transpose map `Nᵀ` is not completely positive. This is the structural
obstruction behind Theorem 1 (p. 3): no physical (completely positive)
operation can implement transposition. -/
theorem transposeMap_not_completelyPositive [Nontrivial A] :
    ¬ (transposeMap : MatrixMap A A ℂ).IsCompletelyPositive := by
  intro hcp
  have hpsd : (transposeMap : MatrixMap A A ℂ).choi_matrix.PosSemidef :=
    (MatrixMap.choi_PSD_iff_CP_map _).mp hcp
  rw [choi_transposeMap] at hpsd
  exact flip_not_posSemidef hpsd

/-! ## No universal state transposition -/

/-- A completely positive map cannot transpose every quantum state: there is no
completely positive `Λ` with `Λ ρ = ρᵀ` for all positive semidefinite `ρ`. This
is the `n = 1` instance of the no-go of Refs. [36, 37] used in the proof of
Theorem 1 (p. 3).

The proof upgrades `Λ` and the transpose map to Hermitian-preserving maps
(`HPMap`), uses that they agree on every positive trace-one operator, hence by
`HPMap.funext_pos_trace` they are equal as linear maps, which would make the
transpose completely positive, contradicting `transposeMap_not_completelyPositive`. -/
theorem no_universal_state_transpose [Nontrivial A]
    (Λ : MatrixMap A A ℂ) (hCP : Λ.IsCompletelyPositive)
    (h : ∀ ρ : Matrix A A ℂ, ρ.PosSemidef → Λ ρ = ρᵀ) : False := by
  let HΛ : HPMap A A ℂ := { toLinearMap := Λ, HP := hCP.IsPositive.IsHermitianPreserving }
  let HT : HPMap A A ℂ :=
    { toLinearMap := transposeMap, HP := fun _ hx => by
        simpa [transposeMap] using hx.transpose }
  have heq : HΛ = HT := by
    apply HPMap.funext_pos_trace (CΛ₁ := HΛ) (CΛ₂ := HT)
    intro M hM _
    exact h M (HermitianMat.zero_le_iff.mp hM)
  have hmap : Λ = (transposeMap : MatrixMap A A ℂ) := by
    have := congrArg HPMap.map heq
    simpa [HΛ, HT] using this
  exact transposeMap_not_completelyPositive (hmap ▸ hCP)

/-! ## Theorem 1: no universal complex conjugation -/

/-- **Theorem 1 (No-go for complex conjugation), p. 3.** There is no completely
positive supermap that universally realizes the complex conjugate `N*` of every
CPTP channel `N`, for any finite number `n ≥ 1` of copies.

The paper's proof restricts to state-preparation channels `R_ρ(X) = Tr(X) ρ`:
the complex conjugate of `R_ρ` is `R_{ρᵀ}` (`conjMap_statePrep`), so a
supermap `C` with `C(N^{⊗n}) = N*` would satisfy `C(R_ρ) = R_{ρᵀ}`. Complete
positivity of `C` makes `ρ ↦ C(R_ρ)` a completely positive map `L`, and
injectivity of `ρ ↦ R_ρ` (`statePrep_injective`) turns `C(R_ρ) = R_{ρᵀ}` into
`L ρ = ρᵀ` for all states `ρ`, contradicting `no_universal_state_transpose`.

`hinduced` records exactly the Choi-matrix consequence of the supermap being
completely positive on the state-preparation family (the other `n-1` slots of
`R_ρ^{⊗n}` contribute a fixed positive tensor factor, which preserves complete
positivity); a full formalization of `n`-slot supermaps as completely positive
maps on comb spaces is not available in the current repository, so this
reduction step is an explicit hypothesis. The contradiction itself is proven. -/
theorem source_theorem1_no_go
    [Nonempty A] [Nontrivial B]
    (n : ℕ) (_hn : 1 ≤ n)
    (C : MatrixMap A B ℂ → MatrixMap A B ℂ)
    (L : MatrixMap B B ℂ) (hL : L.IsCompletelyPositive)
    (hinduced : ∀ ρ : Matrix B B ℂ, ρ.PosSemidef → C (statePrep ρ) = statePrep (L ρ))
    (huniv : ∀ ρ : Matrix B B ℂ, ρ.PosSemidef → C (statePrep ρ) = statePrep (ρᵀ)) :
    False := by
  apply no_universal_state_transpose (A := B) L hL
  intro ρ hρ
  have h1 : statePrep (A := A) (B := B) (L ρ) = statePrep (A := A) (B := B) (ρᵀ) := by
    rw [← hinduced ρ hρ, huniv ρ hρ]
  exact statePrep_injective (A := A) (B := B) h1

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
