/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Spin–boson mapping of QAOA — the states of Eqs. (31), (32), (39), (40), (90)

Fixed source: arXiv:2505.07929v2, *Spin–Boson Mapping of the Quantum Approximate
Optimization Algorithm* (Boulebnane, Khan, Liu, Larson, Herman, Shaydulin, Pistoia).

This module builds the states that Proposition 1 and Proposition 2 talk about:

* the layer unitary `U_t = exp(-i β_t X) K(-i γ_t L_{:,t})` of eq. (36) (PDF p. 12),
  with the spin-controlled displacement `K` of eq. (35);
* the plain generalized QAOA state `U_p ⋯ U_1 |+⟩ ⊗ |0⟩` of eq. (32) (and eq. (90),
  PDF p. 21) — this is `psi … PsiIndex.zero` with the `Z` insertion removed, see
  `qaoaState` in `SourceDefinitions`;
* the `Z`-inserted states `|Ψ_l⟩ = U_p ⋯ U_{l+1} Z U_l ⋯ U_1 |+⟩⊗|0⟩` of eq. (39)
  and `|Ψ_0⟩ = Z U_p ⋯ U_1 |+⟩⊗|0⟩` of eq. (40) (PDF p. 12), encoded as
  `psi … (PsiIndex.pos l)` and `psi … PsiIndex.zero`;
* the spin basis ket `|a⟩` used in the path-integral representation (eq. (A40)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

/-- The displacement family `W.D` of a `WeylFock`, coerced to a plain function
`(Fin p' → ℂ) → B → B` (the form in which the layer maps are written). -/
def WeylFock.dop {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] {p' : ℕ}
    (W : WeylFock (B := B) p') : (Fin p' → ℂ) → B → B :=
  fun z => W.D z

/-- The inner product of two spin–boson states, in the two-component form
`⟨s, t⟩ = ∑_i ⟨s_i, t_i⟩` matching `ℂ² ⊗ B ≃ B × B`.  (`Fin 2 → B` carries no
Mathlib inner-product structure, so the paper's `⟨Ψ_k|Ψ_j⟩` is this explicit sum;
`inner ℂ` is linear in its second argument, so `stateInner s t` is `⟨s|t⟩`.) -/
def stateInner {B : Type*} [Inner ℂ B] (s t : SBState B) : ℂ :=
  ∑ i, inner ℂ (s i) (t i)

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The layer unitary `U_t = exp(-i β_t X) K(-i γ_t L_{:,t})` of eq. (36) (PDF p. 12):
the spin-controlled displacement `K` of eq. (35) acts on the two spin components with
opposite displacement directions (`displaceLayer`), and the mixer `exp(-i β_t X)` of
eq. (36) acts on the spin factor (`mixerLayer`). -/
def uLayer {p' p : ℕ} (Dop : (Fin p' → ℂ) → B → B) (L : Matrix (Fin p') (Fin p) ℂ)
    (γ β : Fin p → ℝ) (t : Fin p) (s : SBState B) : SBState B :=
  mixerLayer (β t) (displaceLayer Dop (fun l => -Complex.I * (γ t : ℂ) * L l t) s)

/-- The Pauli `Z` acting on the spin factor: the `+1` component (`0 : Fin 2`) is fixed,
the `-1` component (`1 : Fin 2`) changes sign.  This is the `Z` inserted between
layers in Eqs. (39), (40) (PDF p. 12). -/
def zLayer (s : SBState B) : SBState B := fun i => (spinOfIndex i : ℂ) • s i

/-- Apply the first `l` layers `U_1, …, U_l` (in this order) to a state. -/
def applyPrefix {p' p : ℕ} (Dop : (Fin p' → ℂ) → B → B) (L : Matrix (Fin p') (Fin p) ℂ)
    (γ β : Fin p → ℝ) (l : ℕ) (hl : l ≤ p) (s : SBState B) : SBState B :=
  (List.finRange l).foldl
    (fun s t => uLayer Dop L γ β ⟨t.val, lt_of_lt_of_le t.isLt hl⟩ s) s

/-- Apply the layers `U_{l+1}, U_{l+2}, …, U_p` to a state (layers are `0`-indexed here,
so `l` counts the layers already applied). -/
def applySuffix {p' p : ℕ} (Dop : (Fin p' → ℂ) → B → B) (L : Matrix (Fin p') (Fin p) ℂ)
    (γ β : Fin p → ℝ) (l : ℕ) (hl : l ≤ p) (s : SBState B) : SBState B :=
  (List.finRange p).foldl
    (fun s t => if l ≤ t.val then uLayer Dop L γ β t s else s) s

/-- The index set `{1, …, p, 0}` of the states of Proposition 1 (eqs. (39), (40)):
`PsiIndex.pos l` is `|Ψ_{l+1}⟩` and `PsiIndex.zero` is `|Ψ_0⟩`. -/
inductive PsiIndex (p : ℕ) : Type
  /-- The state `|Ψ_0⟩ = Z U_p ⋯ U_1 |+⟩ ⊗ |0⟩` of eq. (40). -/
  | zero : PsiIndex p
  /-- The state `|Ψ_{l+1}⟩ = U_p ⋯ U_{l+2} Z U_{l+1} ⋯ U_1 |+⟩ ⊗ |0⟩` of eq. (39),
  indexed by `l : Fin p`. -/
  | pos (l : Fin p) : PsiIndex p

/-- The `Z`-inserted states of Proposition 1 (eqs. (39), (40), PDF p. 12). -/
def psi {p' p : ℕ} (Dop : (Fin p' → ℂ) → B → B) (vac : B) (L : Matrix (Fin p') (Fin p) ℂ)
    (γ β : Fin p → ℝ) : PsiIndex p → SBState B
  | PsiIndex.zero => zLayer (applyPrefix Dop L γ β p le_rfl (initialSBState vac))
  | PsiIndex.pos l =>
      applySuffix Dop L γ β (l.val + 1) (Nat.succ_le_of_lt l.isLt)
        (zLayer (applyPrefix Dop L γ β (l.val + 1) (Nat.succ_le_of_lt l.isLt)
          (initialSBState vac)))

/-- The spin component carrying the spin value `a` (`true ↦ +1`, `false ↦ -1`). -/
def spinComponentOf (a : Bool) : Fin 2 := if a then 0 else 1

/-- The spin basis ket `|a⟩` tensored with a bosonic vector `b`: the `a`-component carries
`b`, the other component is zero.  This is the `|a_{p+1}⟩ ⊗ (…)` of Eq. (A40). -/
def spinKet (a : Bool) (b : B) : SBState B := fun i => if i = spinComponentOf a then b else 0

/-- The displacement vector `-i ∑_t γ_t a_t L_{:,t}` of Eq. (A40) (PDF p. 33):
the argument of the displacement operator that creates the coherent state
`| -i ∑_t γ_t a_t L_{:,t} ⟩` appearing in the spin path-integral representation. -/
def coherentDisp {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (γ : Fin p → ℝ)
    (a : Fin p → ℝ) : Fin p' → ℂ :=
  fun l => ∑ t : Fin p, -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t

end Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions
