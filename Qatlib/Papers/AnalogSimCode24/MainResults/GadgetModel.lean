/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Perturbative-gadget model of Appendix D (arXiv:2412.07764v1)

Fixed paper: arXiv:2412.07764v1 (10 Dec 2024), Appendix D, pp. 16--21.

The penalty Hamiltonian of Eq. (D4) is diagonal in the Bell basis of Eq. (D1).  Each `[[4,2,2]]`
block carries two Bell pairs; a basis state of a pair is `|φ_{s,t}⟩` with `s` the `Z⊗Z`
eigenvalue and `t` the `X⊗X` eigenvalue, and Eq. (D5) gives the energy of a basis state of the
whole system as

`Σ_b gz_b (s_{b,1} + s_{b,2}) + gx_b (t_{b,1} + t_{b,2})`.

We encode a basis state as a function from the four "Bell-pair coordinates" `(block, pair, s/t)` of
each block to a sign `±1`; the energy is then the sum over coordinates of `weight · sign`, with
weight `gz` on `s`-coordinates and `gx` on `t`-coordinates.  The Pauli operators of Eq. (D2) act
by negating one coordinate and multiplying by `1` or by the sign of another coordinate of the
same pair:

* `Z` on qubit 1: `|φ_{s,t}⟩ ↦ |φ_{s,-t}⟩`, coefficient `1`;
* `Z` on qubit 2: coefficient `s`;
* `X` on qubit 1: coefficient `t`;
* `X` on qubit 2: coefficient `1`,

and analogously for the second pair (qubits 3, 4).

`Hpen` is the diagonal matrix of energies, `P0` the diagonal projector onto the zero-energy
eigenspace, and `HpenInv` the diagonal pseudoinverse (`0` on `S0`, the reciprocal of the energy
elsewhere).  `pseudoinverse` verifies the paper's defining relations
`R0 = Q0 R0 Q0` and `R0 H0 = H0 R0 = Q0`.

The main tool is `interference_zero`: for two monomial ("weighted permutation") matrices
`A = mono fA cA`, `B = mono fB cB` whose flips commute, whose energy increments are independent
(`hEadd`) and whose total coefficients are order independent (`hcoeff`), the two-gadget
interference term of Eq. (D11) vanishes.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AnalogSimCode24.MainResults.GadgetModel

/-! ## Signs and Bell-pair coordinates -/

/-- The two eigenvalues `±1` of the Pauli operators on a Bell-pair half, Eq. (D1). -/
inductive Sign where
  | pos
  | neg
deriving DecidableEq, Fintype

namespace Sign

/-- The eigenvalue as an integer: `pos ↦ 1`, `neg ↦ -1`. -/
def sgn : Sign → ℤ
  | pos => 1
  | neg => -1

/-- Negating the eigenvalue, i.e. the action of the Pauli operator on that half of the pair
(Eq. (D2)). -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

/-- The `sgn_flip` result for the AnalogSimCode24 paper model. -/
@[simp] theorem sgn_flip (s : Sign) : sgn (flip s) = -sgn s := by
  cases s <;> rfl

/-- The `flip_flip` result for the AnalogSimCode24 paper model. -/
@[simp] theorem flip_flip (s : Sign) : flip (flip s) = s := by
  cases s <;> rfl

/-- The `flip_ne` result for the AnalogSimCode24 paper model. -/
theorem flip_ne (s : Sign) : flip s ≠ s := by
  cases s <;> simp [flip]

/-- The `sgn_ne_zero` result for the AnalogSimCode24 paper model. -/
theorem sgn_ne_zero (s : Sign) : sgn s ≠ 0 := by
  cases s <;> decide

end Sign

/-- The four Bell-pair coordinates of a block: `(pair index, s or t)`.  The `s`-coordinate is the
`Z⊗Z` eigenvalue of that pair, the `t`-coordinate its `X⊗X` eigenvalue (Eq. (D1)). -/
abbrev Coord (β : Type) := β × Fin 2 × Fin 2

variable {β : Type} [Fintype β] [DecidableEq β]

/-- A basis state of the `n`-block system (Eq. (D5)): a sign for every Bell-pair coordinate. -/
abbrev State (β : Type) := Coord β → Sign

/-- The coefficient multiplying a coordinate's sign in the energy (Eq. (D5)): `gz` for
`s`-coordinates and `gx` for `t`-coordinates. -/
def coordWeight {β : Type} (gx gz : β → ℝ) (c : Coord β) : ℝ :=
  if c.2.2 = 0 then gz c.1 else gx c.1

/-- The energy of a basis state, Eq. (D5). -/
def energy (gx gz : β → ℝ) (ω : State β) : ℝ :=
  ∑ c, coordWeight gx gz c * (Sign.sgn (ω c) : ℝ)

/-! ## Flipping one coordinate -/

/-- Negate the sign of a single Bell-pair coordinate (the action of a Pauli operator, Eq. (D2)). -/
def flipAt (c : Coord β) (ω : State β) : State β :=
  fun d => if d = c then Sign.flip (ω c) else ω d

/-- The `flipAt_self` result for the AnalogSimCode24 paper model. -/
theorem flipAt_self (c : Coord β) (ω : State β) : flipAt c ω c = Sign.flip (ω c) := by
  simp [flipAt]

/-- The `flipAt_of_ne` result for the AnalogSimCode24 paper model. -/
theorem flipAt_of_ne {c c' : Coord β} (h : c' ≠ c) (ω : State β) :
    flipAt c ω c' = ω c' := by
  simp [flipAt, h]

/-- The `flipAt_flipAt` result for the AnalogSimCode24 paper model. -/
theorem flipAt_flipAt (c : Coord β) (ω : State β) : flipAt c (flipAt c ω) = ω := by
  funext x
  by_cases hx : x = c
  · subst hx
    simp [flipAt]
  · simp [flipAt, hx]

/-- The `flipAt_comm` result for the AnalogSimCode24 paper model. -/
theorem flipAt_comm {c d : Coord β} (h : c ≠ d) (ω : State β) :
    flipAt c (flipAt d ω) = flipAt d (flipAt c ω) := by
  funext x
  by_cases hx : x = c
  · subst hx
    simp [flipAt, h]
  · by_cases hx' : x = d
    · subst hx'
      simp [flipAt, hx, Ne.symm h]
    · simp [flipAt, hx, hx']

/-! ## Energy increments -/

/-- Flipping a coordinate changes the energy by `-2 · weight · sign`. -/
theorem energy_flipAt (gx gz : β → ℝ) (c : Coord β) (ω : State β) :
    energy gx gz (flipAt c ω)
      = energy gx gz ω + (-2 * coordWeight gx gz c * (Sign.sgn (ω c) : ℝ)) := by
  have hsplit : ∀ ω' : State β, energy gx gz ω'
      = coordWeight gx gz c * (Sign.sgn (ω' c) : ℝ)
        + ∑ d ∈ Finset.univ.erase c, coordWeight gx gz d * (Sign.sgn (ω' d) : ℝ) := by
    intro ω'
    rw [energy, ← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
    ring
  rw [hsplit (flipAt c ω), hsplit ω, flipAt_self, Sign.sgn_flip]
  have hsum : (∑ d ∈ Finset.univ.erase c,
        coordWeight gx gz d * (Sign.sgn (flipAt c ω d) : ℝ))
      = ∑ d ∈ Finset.univ.erase c, coordWeight gx gz d * (Sign.sgn (ω d) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [flipAt_of_ne (Finset.ne_of_mem_erase hd)]
  rw [hsum]
  push_cast
  ring

/-- Flipping two distinct coordinates adds the two increments, both computed on the original
state. -/
theorem energy_flipAt_flipAt (gx gz : β → ℝ) {c c' : Coord β} (h : c ≠ c') (ω : State β) :
    energy gx gz (flipAt c (flipAt c' ω))
      = energy gx gz ω + (-2 * coordWeight gx gz c * (Sign.sgn (ω c) : ℝ))
        + (-2 * coordWeight gx gz c' * (Sign.sgn (ω c') : ℝ)) := by
  rw [energy_flipAt gx gz c (flipAt c' ω), energy_flipAt gx gz c' ω,
    flipAt_of_ne (c := c') (c' := c) h]
  ring

/-- The energy increment of a flip is unchanged by a second flip at a different coordinate. -/
theorem energy_flipAt_ne (gx gz : β → ℝ) {c c' : Coord β} (h : c ≠ c') (ω : State β) :
    energy gx gz (flipAt c (flipAt c' ω)) - energy gx gz (flipAt c ω)
      = energy gx gz (flipAt c' ω) - energy gx gz ω := by
  rw [energy_flipAt gx gz c (flipAt c' ω), energy_flipAt gx gz c ω, energy_flipAt gx gz c' ω,
    flipAt_of_ne (c := c') (c' := c) h]
  ring

/-- Independence of the energy increments of two pairs of flips at pairwise distinct coordinates
(the `hEadd` hypothesis of `interference_zero`). -/
theorem energy_comp_comp (gx gz : β → ℝ) {c₁ c₂ d₁ d₂ : Coord β}
    (hcc : c₁ ≠ c₂) (h₁₁ : c₁ ≠ d₁) (h₁₂ : c₁ ≠ d₂) (h₂₁ : c₂ ≠ d₁) (h₂₂ : c₂ ≠ d₂)
    (ω : State β) :
    energy gx gz ((flipAt c₁ ∘ flipAt c₂) ((flipAt d₁ ∘ flipAt d₂) ω))
      - energy gx gz ((flipAt c₁ ∘ flipAt c₂) ω)
      = energy gx gz ((flipAt d₁ ∘ flipAt d₂) ω) - energy gx gz ω := by
  simp only [Function.comp_apply]
  set W : State β := flipAt d₁ (flipAt d₂ ω) with hW
  rw [energy_flipAt_flipAt gx gz hcc (ω := W), energy_flipAt_flipAt gx gz hcc (ω := ω)]
  have hc₁ : W c₁ = ω c₁ := by
    rw [hW, flipAt_of_ne (c := d₁) (c' := c₁) h₁₁, flipAt_of_ne (c := d₂) (c' := c₁) h₁₂]
  have hc₂ : W c₂ = ω c₂ := by
    rw [hW, flipAt_of_ne (c := d₁) (c' := c₂) h₂₁, flipAt_of_ne (c := d₂) (c' := c₂) h₂₂]
  rw [hc₁, hc₂]
  ring

/-! ## Monomial matrices -/

/-- A *monomial* ("weighted permutation") matrix: the `j`-th basis vector is sent to the `f j`-th
basis vector with coefficient `c j`.  In the Bell basis all Pauli operators of Eq. (D2) are of
this form. -/
def mono {ι : Type} [DecidableEq ι] (f : ι → ι) (c : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if f j = i then c j else 0

/-- The `mono_mul` result for the AnalogSimCode24 paper model. -/
theorem mono_mul {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι) (c d : ι → ℂ) :
    mono f c * mono g d = mono (f ∘ g) (fun ω => c (g ω) * d ω) := by
  ext i j
  simp only [mono, Matrix.mul_apply]
  rw [Finset.sum_eq_single (g j)]
  · simp
  · intro b _ hb
    have hbg : ¬ (g j = b) := fun h => hb h.symm
    simp [hbg]
  · intro h
    exact absurd (Finset.mem_univ (g j)) h

/-- The `mono_add` result for the AnalogSimCode24 paper model. -/
theorem mono_add {ι : Type} [DecidableEq ι] (f : ι → ι) (x y : ι → ℂ) :
    mono f x + mono f y = mono f (fun i => x i + y i) := by
  ext i j
  simp only [mono, Matrix.add_apply]
  by_cases h : f j = i <;> simp [h]

/-- The `mono_zero` result for the AnalogSimCode24 paper model. -/
theorem mono_zero {ι : Type} [DecidableEq ι] (f : ι → ι) : mono f (fun _ => 0) = 0 := by
  ext i j
  simp [mono]

/-- The `mono_one` result for the AnalogSimCode24 paper model. -/
theorem mono_one {ι : Type} [DecidableEq ι] : mono (id : ι → ι) (fun _ => 1) = 1 := by
  ext i j
  show (if (j : ι) = i then (1 : ℂ) else 0) = (1 : Matrix ι ι ℂ) i j
  rw [Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh : i = j => h hh.symm)]

/-- Two monomials with equal flip and coefficient functions are equal. -/
theorem mono_congr {ι : Type} [DecidableEq ι] {f g : ι → ι} {c d : ι → ℂ} (hf : f = g) (hc : c = d) :
    mono f c = mono g d := by
  rw [hf, hc]

/-- The product `P0 A Hpen⁻¹ B P0` for `A = mono fA cA`, `B = mono fB cB`, with `P0` and
`Hpen⁻¹` diagonal, as a single monomial. -/
theorem sandwich_mono {ι : Type} [Fintype ι] [DecidableEq ι] (p r : ι → ℂ) (fA fB : ι → ι)
    (cA cB : ι → ℂ) :
    mono id p * mono fA cA * mono id r * mono fB cB * mono id p
      = mono (fA ∘ fB)
          (fun ω => p (fA (fB ω)) * cA (fB ω) * r (fB ω) * cB ω * p ω) := by
  rw [mono_mul, mono_mul, mono_mul, mono_mul]
  apply mono_congr
  · funext x
    rfl
  · funext ω
    rfl

/-- The two-gadget interference term vanishes when the flips commute, the energy increments are
independent, and the total coefficients are order independent.  This is the common core of
Lemmas D.1--D.5 (Eqs. (D12), (D15), (D16), (D19), (D22)). -/
theorem interference_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (fA fB : ι → ι) (cA cB : ι → ℂ)
    (hcomm : ∀ ω, fA (fB ω) = fB (fA ω))
    (hEadd : ∀ ω, E (fA (fB ω)) - E (fA ω) = E (fB ω) - E ω)
    (hcoeff : ∀ ω, cA (fB ω) * cB ω = cB (fA ω) * cA ω) :
    mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0) * mono fA cA *
        mono id (fun ω => if E ω = 0 then 0 else ((E ω : ℂ))⁻¹) * mono fB cB *
        mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0)
      + mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0) * mono fB cB *
        mono id (fun ω => if E ω = 0 then 0 else ((E ω : ℂ))⁻¹) * mono fA cA *
        mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0) = 0 := by
  rw [sandwich_mono (p := fun ω => if E ω = 0 then (1 : ℂ) else 0)
        (r := fun ω => if E ω = 0 then 0 else ((E ω : ℂ))⁻¹) (fA := fA) (fB := fB)
        (cA := cA) (cB := cB),
      sandwich_mono (p := fun ω => if E ω = 0 then (1 : ℂ) else 0)
        (r := fun ω => if E ω = 0 then 0 else ((E ω : ℂ))⁻¹) (fA := fB) (fB := fA)
        (cA := cB) (cB := cA)]
  rw [show (fB ∘ fA) = (fA ∘ fB) from funext (fun ω => (hcomm ω).symm)]
  rw [mono_add]
  have hpoint : ∀ ω : ι,
      (if E (fA (fB ω)) = 0 then (1 : ℂ) else 0) * cA (fB ω) *
          (if E (fB ω) = 0 then 0 else ((E (fB ω) : ℂ))⁻¹) * cB ω *
          (if E ω = 0 then (1 : ℂ) else 0)
        + ((if E (fB (fA ω)) = 0 then (1 : ℂ) else 0) * cB (fA ω) *
            (if E (fA ω) = 0 then 0 else ((E (fA ω) : ℂ))⁻¹) * cA ω *
            (if E ω = 0 then (1 : ℂ) else 0)) = 0 := by
    intro ω
    rw [← hcomm ω]
    by_cases hω : E ω = 0
    · by_cases hf : E (fA (fB ω)) = 0
      · have hδ : E (fA ω) = -E (fB ω) := by
          have := hEadd ω
          rw [hf, hω] at this
          linarith
        by_cases hB : E (fB ω) = 0
        · have hA : E (fA ω) = 0 := by rw [hδ, hB]; norm_num
          simp [hω, hf, hB, hA]
        · have hA : E (fA ω) ≠ 0 := by
            rw [hδ]
            simp [hB]
          have hinv : ((E (fA ω) : ℂ))⁻¹ = -((E (fB ω) : ℂ))⁻¹ := by
            rw [hδ]
            push_cast
            rw [inv_neg]
          simp only [hω, hf, hB, hA, if_true, if_false, one_mul, zero_mul, hinv]
          have hc := hcoeff ω
          linear_combination ((E (fB ω) : ℂ))⁻¹ * hc
      · simp [hω, hf]
    · simp [hω]
  rw [show (fun ω =>
      (if E (fA (fB ω)) = 0 then (1 : ℂ) else 0) * cA (fB ω) *
          (if E (fB ω) = 0 then 0 else ((E (fB ω) : ℂ))⁻¹) * cB ω *
          (if E ω = 0 then (1 : ℂ) else 0)
        + ((if E (fB (fA ω)) = 0 then (1 : ℂ) else 0) * cB (fA ω) *
            (if E (fA ω) = 0 then 0 else ((E (fA ω) : ℂ))⁻¹) * cA ω *
            (if E ω = 0 then (1 : ℂ) else 0)))
      = (fun _ => 0) from funext hpoint]
  rw [mono_zero]

/-- If the composed flip always leaves the nonzero energy region, the sandwich vanishes
(used for Lemmas D.6 and D.7, where the final energy is never zero). -/
theorem sandwich_mono_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (fA fB : ι → ι)
    (cA cB : ι → ℂ) (h : ∀ ω, E ω = 0 → E (fA (fB ω)) ≠ 0) :
    mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0) * mono fA cA *
        mono id (fun ω => if E ω = 0 then 0 else ((E ω : ℂ))⁻¹) * mono fB cB *
        mono id (fun ω => if E ω = 0 then (1 : ℂ) else 0) = 0 := by
  rw [sandwich_mono]
  rw [show (fun ω => (if E (fA (fB ω)) = 0 then (1 : ℂ) else 0) * cA (fB ω) *
        (if E (fB ω) = 0 then 0 else ((E (fB ω) : ℂ))⁻¹) * cB ω *
        (if E ω = 0 then (1 : ℂ) else 0)) = (fun _ => 0) from ?_, mono_zero]
  funext ω
  by_cases hω : E ω = 0
  · have hf : E (fA (fB ω)) ≠ 0 := h ω hω
    simp [hω, hf]
  · simp [hω]

/-! ## The penalty Hamiltonian, its zero-energy projector and pseudoinverse -/

/-- The penalty Hamiltonian `Hpen` of Eq. (D4), diagonal in the Bell basis (Eq. (D5)). -/
def Hpen (gx gz : β → ℝ) : Matrix (State β) (State β) ℂ :=
  mono id (fun ω => (energy gx gz ω : ℂ))

/-- The projector `P0` onto the zero-energy eigenspace `S0` of `Hpen`. -/
def P0 (gx gz : β → ℝ) : Matrix (State β) (State β) ℂ :=
  mono id (fun ω => if energy gx gz ω = 0 then (1 : ℂ) else 0)

/-- The orthogonal complement projector `Q0 = 1 - P0`. -/
def Q0 (gx gz : β → ℝ) : Matrix (State β) (State β) ℂ :=
  mono id (fun ω => if energy gx gz ω = 0 then 0 else (1 : ℂ))

/-- The pseudoinverse `Hpen⁻¹`: `0` on `S0` and the reciprocal energy on its complement. -/
def HpenInv (gx gz : β → ℝ) : Matrix (State β) (State β) ℂ :=
  mono id (fun ω => if energy gx gz ω = 0 then 0 else ((energy gx gz ω : ℂ))⁻¹)

/-- The `one_sub_P0` result for the AnalogSimCode24 paper model. -/
theorem one_sub_P0 (gx gz : β → ℝ) : (1 : Matrix (State β) (State β) ℂ) - P0 gx gz = Q0 gx gz := by
  rw [← mono_one, Q0, P0]
  ext i j
  simp only [mono, Matrix.sub_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    by_cases hE : energy gx gz i = 0 <;> simp [hE]
  · simp [h, eq_comm]

/-- `HpenInv · Hpen = Q0`. -/
theorem HpenInv_mul_Hpen (gx gz : β → ℝ) : HpenInv gx gz * Hpen gx gz = Q0 gx gz := by
  rw [HpenInv, Hpen, mono_mul, Q0]
  congr 1
  funext ω
  by_cases h : energy gx gz ω = 0
  · simp [h]
  · have h0 : (energy gx gz ω : ℂ) ≠ 0 := by
      exact_mod_cast h
    simp [h, h0]

/-- `Hpen · HpenInv = Q0`. -/
theorem Hpen_mul_HpenInv (gx gz : β → ℝ) : Hpen gx gz * HpenInv gx gz = Q0 gx gz := by
  rw [HpenInv, Hpen, mono_mul, Q0]
  congr 1
  funext ω
  by_cases h : energy gx gz ω = 0
  · simp [h]
  · have h0 : (energy gx gz ω : ℂ) ≠ 0 := by exact_mod_cast h
    simp [h, h0]

/-- `HpenInv = Q0 · HpenInv · Q0`. -/
theorem HpenInv_sandwich (gx gz : β → ℝ) :
    HpenInv gx gz = Q0 gx gz * HpenInv gx gz * Q0 gx gz := by
  rw [HpenInv, Q0, mono_mul, mono_mul]
  apply mono_congr
  · funext x
    rfl
  · funext ω
    by_cases h : energy gx gz ω = 0 <;> simp [h]

/-! ## Local Pauli operators as monomials (Eq. (D2)) -/

/-- The pair index (`0` or `1`) of a physical qubit `i ∈ {1,2,3,4}`. -/
def qubitPair (i : Fin 4) : Fin 2 :=
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- The side (`0` = first qubit of the pair, `1` = second qubit) of `i ∈ {1,2,3,4}`. -/
def qubitSide (i : Fin 4) : Fin 2 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | _ => 0

/-- The coordinate `(block, pair, s/t)` of a Bell-pair half. -/
def coord (b : β) (i : Fin 4) (st : Fin 2) : Coord β := (b, qubitPair i, st)

/-- A single Pauli operator on one physical qubit, in the Bell basis: it negates one coordinate
and multiplies the state by `1` or by the sign of a coordinate of the same pair (Eq. (D2)). -/
structure PauliOp where
  flipCoord : Coord β
  coeffCoord : Option (Coord β)

namespace PauliOp

/-- The scalar coefficient of the monomial. -/
def coeff (p : PauliOp (β := β)) (ω : State β) : ℂ :=
  match p.coeffCoord with
  | none => 1
  | some c => (Sign.sgn (ω c) : ℂ)

/-- The matrix of a Pauli operator in the Bell basis. -/
def mat (p : PauliOp (β := β)) : Matrix (State β) (State β) ℂ :=
  mono (flipAt p.flipCoord) p.coeff

end PauliOp

/-- The Pauli operators `X` and `Z`. -/
inductive PauliUnit where
  | X
  | Z
deriving DecidableEq, Fintype

/-- The Pauli operator `P_i^(b)` of Eq. (D4) in the Bell basis; Eq. (D2) gives the action
`(Z⊗1)|φ_{s,t}⟩ = |φ_{s,-t}⟩`, `(1⊗Z)|φ_{s,t}⟩ = s|φ_{s,-t}⟩`,
`(X⊗1)|φ_{s,t}⟩ = t|φ_{−s,t}⟩`, `(1⊗X)|φ_{s,t}⟩ = |φ_{−s,t}⟩`. -/
def PauliUnit.op (P : PauliUnit) (b : β) (i : Fin 4) : PauliOp (β := β) :=
  match P with
  | .Z =>
    { flipCoord := coord b i 1,
      coeffCoord := if qubitSide i = 0 then none else some (coord b i 0) }
  | .X =>
    { flipCoord := coord b i 0,
      coeffCoord := if qubitSide i = 0 then some (coord b i 1) else none }

/-- `Z_i^(a) X_j^(b)`: a product of two physical Pauli operators on (possibly) two blocks. -/
def gadgetTerm (Pa : PauliUnit) (a : β) (i : Fin 4) (Pb : PauliUnit) (b : β) (j : Fin 4) :
    Matrix (State β) (State β) ℂ :=
  (Pa.op a i).mat * (Pb.op b j).mat

end Qatlib.Papers.AnalogSimCode24.MainResults.GadgetModel
