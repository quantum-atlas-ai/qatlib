/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AnalogSimCode24.MainResults.GadgetModel

@[expose] public section


set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AnalogSimCode24.MainResults.Interference

open Qatlib.Papers.AnalogSimCode24.MainResults.GadgetModel

variable {β : Type} [_instFintypeβ : Fintype β] [_instDecidableEqβ : DecidableEq β]

omit _instFintypeβ _instDecidableEqβ in
/-- Equality of Bell-pair coordinates, componentwise. -/
theorem coord_inj {a a' : β} {i i' : Fin 4} {st st' : Fin 2} :
    coord a i st = coord a' i' st' ↔ a = a' ∧ qubitPair i = qubitPair i' ∧ st = st' := by
  simp [coord]

omit _instFintypeβ _instDecidableEqβ in
/-- Coordinates of qubits in different blocks are always different. -/
theorem coord_ne_of_block_ne {a b : β} (h : a ≠ b) (i j : Fin 4) (st st' : Fin 2) :
    coord a i st ≠ coord b j st' := by
  intro hc
  exact h (by simpa using (coord_inj.1 hc).1)

omit _instFintypeβ _instDecidableEqβ in
/-- Coordinates of qubits in different Bell pairs of the same block are different. -/
theorem coord_ne_of_pair_ne {a : β} {i j : Fin 4} (h : qubitPair i ≠ qubitPair j)
    (st st' : Fin 2) : coord a i st ≠ coord a j st' := by
  intro hc
  exact h (by simpa using (coord_inj.1 hc).2.1)

omit _instFintypeβ _instDecidableEqβ in
/-- Coordinates of the two axes of one Bell pair are different. -/
theorem coord_ne_of_axis_ne {a : β} {i j : Fin 4} {st st' : Fin 2} (h : st ≠ st') :
    coord a i st ≠ coord a j st' := by
  intro hc
  exact h (by simpa using (coord_inj.1 hc).2.2)

/-- Two pairs of flips at four distinct coordinates commute. -/
theorem comp_flipAt_comm {c₁ c₂ d₁ d₂ : Coord β}
    (h₁₁ : c₁ ≠ d₁) (h₁₂ : c₁ ≠ d₂) (h₂₁ : c₂ ≠ d₁) (h₂₂ : c₂ ≠ d₂) (ω : State β) :
    (flipAt c₁ ∘ flipAt c₂) ((flipAt d₁ ∘ flipAt d₂) ω)
      = (flipAt d₁ ∘ flipAt d₂) ((flipAt c₁ ∘ flipAt c₂) ω) := by
  simp only [Function.comp_apply]
  rw [flipAt_comm h₂₁, flipAt_comm h₂₂, flipAt_comm h₁₁, flipAt_comm h₁₂]

omit _instFintypeβ _instDecidableEqβ in
/-- Two states that agree on the coordinate supporting a Pauli operator's coefficient give the
same coefficient. -/
theorem PauliOp.coeff_congr (p : PauliOp (β := β)) {ω ω' : State β}
    (h : ∀ c, p.coeffCoord = some c → ω c = ω' c) : p.coeff ω = p.coeff ω' := by
  cases hc : p.coeffCoord with
  | none => simp [PauliOp.coeff, hc]
  | some c => simp [PauliOp.coeff, hc, h c hc]

/-- A flip at a coordinate that does not support the coefficient leaves the coefficient
unchanged. -/
theorem PauliOp.coeff_flipAt (p : PauliOp (β := β)) {c : Coord β} (ω : State β)
    (h : ∀ c', p.coeffCoord = some c' → c' ≠ c) : p.coeff (flipAt c ω) = p.coeff ω := by
  apply PauliOp.coeff_congr
  intro c' hc'
  exact flipAt_of_ne (h c' hc') ω

/-- A flip at each of two coordinates that do not support the coefficient leaves it unchanged. -/
theorem PauliOp.coeff_flipAt_two (p : PauliOp (β := β)) {c₁ c₂ : Coord β} (ω : State β)
    (h₁ : ∀ c', p.coeffCoord = some c' → c' ≠ c₁)
    (h₂ : ∀ c', p.coeffCoord = some c' → c' ≠ c₂) :
    p.coeff (flipAt c₁ (flipAt c₂ ω)) = p.coeff ω := by
  rw [PauliOp.coeff_flipAt (p := p) (c := c₁) (ω := flipAt c₂ ω) h₁,
    PauliOp.coeff_flipAt (p := p) (c := c₂) (ω := ω) h₂]

/-- A flip at each of three coordinates that do not support the coefficient leaves it
unchanged. -/
theorem PauliOp.coeff_flipAt_three (p : PauliOp (β := β)) {c₁ c₂ c₃ : Coord β} (ω : State β)
    (h₁ : ∀ c', p.coeffCoord = some c' → c' ≠ c₁)
    (h₂ : ∀ c', p.coeffCoord = some c' → c' ≠ c₂)
    (h₃ : ∀ c', p.coeffCoord = some c' → c' ≠ c₃) :
    p.coeff (flipAt c₁ (flipAt c₂ (flipAt c₃ ω))) = p.coeff ω := by
  rw [PauliOp.coeff_flipAt (p := p) (c := c₁) (ω := flipAt c₂ (flipAt c₃ ω)) h₁,
    PauliOp.coeff_flipAt (p := p) (c := c₂) (ω := flipAt c₃ ω) h₂,
    PauliOp.coeff_flipAt (p := p) (c := c₃) (ω := ω) h₃]

/-- A two-Pauli gadget term `P_i^(a) P'_j^(b)` is a single monomial. -/
theorem gadgetTerm_eq_mono (Pa Pb : PauliUnit) (a b : β) (i j : Fin 4) :
    gadgetTerm Pa a i Pb b j
      = mono (flipAt (Pa.op a i).flipCoord ∘ flipAt (Pb.op b j).flipCoord)
          (fun ω => (Pa.op a i).coeff (flipAt (Pb.op b j).flipCoord ω) *
            (Pb.op b j).coeff ω) := by
  rw [gadgetTerm, PauliOp.mat, PauliOp.mat, mono_mul]

omit _instFintypeβ _instDecidableEqβ in
/-- The coordinate supporting the coefficient of a Pauli operator on qubit `i` of block `b`
(if any) lies in block `b`. -/
theorem PauliUnit.op_coeffCoord_block (P : PauliUnit) (b : β) (i : Fin 4) {c : Coord β}
    (h : (P.op b i).coeffCoord = some c) : c.1 = b := by
  cases P
  · by_cases hs : qubitSide i = 0
    · simp [PauliUnit.op, hs] at h
      rw [← h]
      simp [coord]
    · simp [PauliUnit.op, hs] at h
  · by_cases hs : qubitSide i = 0
    · simp [PauliUnit.op, hs] at h
    · simp [PauliUnit.op, hs] at h
      rw [← h]
      simp [coord]

omit _instFintypeβ _instDecidableEqβ in
/-- The coordinate supporting the coefficient of a Pauli operator on qubit `i` of block `b`
(if any) lies in the Bell pair of `i`. -/
theorem PauliUnit.op_coeffCoord_pair (P : PauliUnit) (b : β) (i : Fin 4) {c : Coord β}
    (h : (P.op b i).coeffCoord = some c) : c.2.1 = qubitPair i := by
  cases P
  · by_cases hs : qubitSide i = 0
    · simp [PauliUnit.op, hs] at h
      rw [← h]
      simp [coord]
    · simp [PauliUnit.op, hs] at h
  · by_cases hs : qubitSide i = 0
    · simp [PauliUnit.op, hs] at h
    · simp [PauliUnit.op, hs] at h
      rw [← h]
      simp [coord]

omit _instFintypeβ _instDecidableEqβ in
/-- A coefficient coordinate in block `b` is never the flip coordinate of a qubit in a
different block. -/
theorem PauliUnit.op_coeffCoord_ne {P : PauliUnit} {b : β} {i : Fin 4} {c : Coord β}
    (h : (P.op b i).coeffCoord = some c) {b' : β} (hb : b ≠ b') (j : Fin 4) (st : Fin 2) :
    c ≠ coord b' j st := by
  intro hc
  have h1 : c.1 = b := PauliUnit.op_coeffCoord_block P b i h
  have h2 : c.1 = b' := by simpa [coord] using congrArg (fun x : Coord β => x.1) hc
  exact hb (by rw [← h1, h2])

omit _instFintypeβ _instDecidableEqβ in
/-- A coefficient coordinate of qubit `i` is never the flip coordinate of a qubit in a
different Bell pair of the same block. -/
theorem PauliUnit.op_coeffCoord_ne_pair {P : PauliUnit} {b : β} {i : Fin 4} {c : Coord β}
    (h : (P.op b i).coeffCoord = some c) {j : Fin 4} (hj : qubitPair i ≠ qubitPair j)
    (st : Fin 2) : c ≠ coord b j st := by
  intro hc
  have h1 : c.2.1 = qubitPair i := PauliUnit.op_coeffCoord_pair P b i h
  have h2 : c.2.1 = qubitPair j := by
    simpa [coord] using congrArg (fun x : Coord β => x.2.1) hc
  exact hj (by rw [← h1, h2])

omit _instFintypeβ _instDecidableEqβ in
/-- Flip coordinates of qubits in different blocks are different, for any Pauli types. -/
theorem PauliUnit.op_flipCoord_ne_of_block_ne (P Q : PauliUnit) {b b' : β} (h : b ≠ b')
    (i j : Fin 4) : (P.op b i).flipCoord ≠ (Q.op b' j).flipCoord := by
  cases P <;> cases Q <;> exact coord_ne_of_block_ne h i j _ _

omit _instFintypeβ _instDecidableEqβ in
/-- Flip coordinates of qubits in different Bell pairs of the same block are different, for
any Pauli types. -/
theorem PauliUnit.op_flipCoord_ne_of_pair_ne (P Q : PauliUnit) {b : β} {i j : Fin 4}
    (h : qubitPair i ≠ qubitPair j) : (P.op b i).flipCoord ≠ (Q.op b j).flipCoord := by
  cases P <;> cases Q <;> exact coord_ne_of_pair_ne h _ _

omit _instFintypeβ _instDecidableEqβ in
/-- A coefficient coordinate in block `b` is never the flip coordinate of a qubit in another
block, for any Pauli type of the latter. -/
theorem PauliUnit.op_coeffCoord_ne_flipCoord (P Q : PauliUnit) {b b' : β} (h : b ≠ b')
    {i j : Fin 4} {c : Coord β} (hc : (P.op b i).coeffCoord = some c) :
    c ≠ (Q.op b' j).flipCoord := by
  cases Q <;> exact PauliUnit.op_coeffCoord_ne hc h j _

omit _instFintypeβ _instDecidableEqβ in
/-- A coefficient coordinate of qubit `i` is never the flip coordinate of a qubit in another
Bell pair of the same block, for any Pauli type of the latter. -/
theorem PauliUnit.op_coeffCoord_ne_flipCoord_pair (P Q : PauliUnit) {b : β} {i j : Fin 4}
    (h : qubitPair i ≠ qubitPair j) {c : Coord β} (hc : (P.op b i).coeffCoord = some c) :
    c ≠ (Q.op b j).flipCoord := by
  cases Q <;> exact PauliUnit.op_coeffCoord_ne_pair hc h _

/-- Generic core of Lemmas D.1--D.3: if the four flip coordinates of the two gadgets are
pairwise distinct and the coefficient coordinates are untouched by the other operator, the
two-gadget interference term of Eq. (D11) vanishes. -/
theorem interference_zero_of_disjoint (gx gz : β → ℝ) (pA1 pA2 pB1 pB2 : PauliOp (β := β))
    (hflipA : pA1.flipCoord ≠ pA2.flipCoord)
    (h₁₁ : pA1.flipCoord ≠ pB1.flipCoord) (h₁₂ : pA1.flipCoord ≠ pB2.flipCoord)
    (h₂₁ : pA2.flipCoord ≠ pB1.flipCoord) (h₂₂ : pA2.flipCoord ≠ pB2.flipCoord)
    (hA12 : ∀ c, pA1.coeffCoord = some c → c ≠ pA2.flipCoord)
    (hA1B1 : ∀ c, pA1.coeffCoord = some c → c ≠ pB1.flipCoord)
    (hA1B2 : ∀ c, pA1.coeffCoord = some c → c ≠ pB2.flipCoord)
    (hA2B1 : ∀ c, pA2.coeffCoord = some c → c ≠ pB1.flipCoord)
    (hA2B2 : ∀ c, pA2.coeffCoord = some c → c ≠ pB2.flipCoord)
    (hB12 : ∀ c, pB1.coeffCoord = some c → c ≠ pB2.flipCoord)
    (hB1A1 : ∀ c, pB1.coeffCoord = some c → c ≠ pA1.flipCoord)
    (hB1A2 : ∀ c, pB1.coeffCoord = some c → c ≠ pA2.flipCoord)
    (hB2A1 : ∀ c, pB2.coeffCoord = some c → c ≠ pA1.flipCoord)
    (hB2A2 : ∀ c, pB2.coeffCoord = some c → c ≠ pA2.flipCoord) :
    P0 gx gz * (pA1.mat * pA2.mat) * HpenInv gx gz * (pB1.mat * pB2.mat) * P0 gx gz
      + P0 gx gz * (pB1.mat * pB2.mat) * HpenInv gx gz * (pA1.mat * pA2.mat) * P0 gx gz = 0 := by
  have _hA : pA1.mat * pA2.mat
      = mono (flipAt pA1.flipCoord ∘ flipAt pA2.flipCoord)
          (fun ω => pA1.coeff (flipAt pA2.flipCoord ω) * pA2.coeff ω) := by
    rw [PauliOp.mat, PauliOp.mat, mono_mul]
  have _hB : pB1.mat * pB2.mat
      = mono (flipAt pB1.flipCoord ∘ flipAt pB2.flipCoord)
          (fun ω => pB1.coeff (flipAt pB2.flipCoord ω) * pB2.coeff ω) := by
    rw [PauliOp.mat, PauliOp.mat, mono_mul]
  rw [_hA, _hB]
  refine interference_zero (energy gx gz) _ _ _ _ ?_ ?_ ?_
  · intro ω
    exact comp_flipAt_comm h₁₁ h₁₂ h₂₁ h₂₂ ω
  · intro ω
    exact energy_comp_comp gx gz hflipA h₁₁ h₁₂ h₂₁ h₂₂ ω
  · -- the coefficients are order independent: neither operator changes the other's coefficient
    intro ω
    have h1 := PauliOp.coeff_flipAt_three (p := pA1) (c₁ := pA2.flipCoord) (c₂ := pB1.flipCoord)
      (c₃ := pB2.flipCoord) ω hA12 hA1B1 hA1B2
    have h2 := PauliOp.coeff_flipAt_two (p := pA2) (c₁ := pB1.flipCoord) (c₂ := pB2.flipCoord)
      ω hA2B1 hA2B2
    have h3 := PauliOp.coeff_flipAt_three (p := pB1) (c₁ := pB2.flipCoord) (c₂ := pA1.flipCoord)
      (c₃ := pA2.flipCoord) ω hB12 hB1A1 hB1A2
    have h4 := PauliOp.coeff_flipAt_two (p := pB2) (c₁ := pA1.flipCoord) (c₂ := pA2.flipCoord)
      ω hB2A1 hB2A2
    have h5 := PauliOp.coeff_flipAt (p := pA1) (c := pA2.flipCoord) (ω := ω) hA12
    have h6 := PauliOp.coeff_flipAt (p := pB1) (c := pB2.flipCoord) (ω := ω) hB12
    simp only [Function.comp_apply, h1, h2, h3, h4, h5, h6]
    ring

/-- **Lemma D.1** (arXiv:2412.07764v1, App. D p. 19, Eq. (D12)).  For four distinct blocks
`a, b, c, d` and arbitrary local indices `i, j, k, l`, the gadgets `A = Z_i^(a) X_j^(b)` and
`B = Z_k^(c) X_l^(d)` do not interfere: `P0 A Hpen⁻¹ B P0 + P0 B Hpen⁻¹ A P0 = 0`. -/
theorem lemma_D1 (gx gz : β → ℝ) {a b c d : β}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (i j k l : Fin 4) :
    P0 gx gz * gadgetTerm PauliUnit.Z a i PauliUnit.X b j * HpenInv gx gz *
        gadgetTerm PauliUnit.Z c k PauliUnit.X d l * P0 gx gz
      + P0 gx gz * gadgetTerm PauliUnit.Z c k PauliUnit.X d l * HpenInv gx gz *
        gadgetTerm PauliUnit.Z a i PauliUnit.X b j * P0 gx gz = 0 := by
  simp only [gadgetTerm]
  exact interference_zero_of_disjoint gx gz _ _ _ _
    (PauliUnit.op_flipCoord_ne_of_block_ne PauliUnit.Z PauliUnit.X hab i j)
    (PauliUnit.op_flipCoord_ne_of_block_ne PauliUnit.Z PauliUnit.Z hac i k)
    (PauliUnit.op_flipCoord_ne_of_block_ne PauliUnit.Z PauliUnit.X had i l)
    (PauliUnit.op_flipCoord_ne_of_block_ne PauliUnit.X PauliUnit.Z hbc j k)
    (PauliUnit.op_flipCoord_ne_of_block_ne PauliUnit.X PauliUnit.X hbd j l)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.X hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.Z hac hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.X had hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.X PauliUnit.Z hbc hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.X PauliUnit.X hbd hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.X hcd hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.Z hac.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.Z PauliUnit.X hbc.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.X PauliUnit.Z had.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord PauliUnit.X PauliUnit.X hbd.symm hc)

/-- **Lemma D.2** (arXiv:2412.07764v1, App. D p. 19, Eq. (D15)).  For three distinct blocks
`a, b, c`, gadgets `A = Z_i^(a) X_j^(b)` (or `X_i^(a) Z_j^(b)`) and
`B = Z_k^(a) X_l^(c)` (or `X_k^(a) Z_l^(c)`) whose operators on the common block `a` sit in
different Bell pairs (`(i,k) ∈ {(1,3),…,(4,2)}`) do not interfere. -/
theorem lemma_D2 (gx gz : β → ℝ) {a b c : β}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j k l : Fin 4) (hik : qubitPair i ≠ qubitPair k)
    (Pa Pb Qa Qb : PauliUnit)
    (_hA : (Pa = PauliUnit.Z ∧ Pb = PauliUnit.X) ∨ (Pa = PauliUnit.X ∧ Pb = PauliUnit.Z))
    (_hB : (Qa = PauliUnit.Z ∧ Qb = PauliUnit.X) ∨ (Qa = PauliUnit.X ∧ Qb = PauliUnit.Z)) :
    P0 gx gz * gadgetTerm Pa a i Pb b j * HpenInv gx gz * gadgetTerm Qa a k Qb c l * P0 gx gz
      + P0 gx gz * gadgetTerm Qa a k Qb c l * HpenInv gx gz *
        gadgetTerm Pa a i Pb b j * P0 gx gz = 0 := by
  simp only [gadgetTerm]
  exact interference_zero_of_disjoint gx gz _ _ _ _
    (PauliUnit.op_flipCoord_ne_of_block_ne Pa Pb hab i j)
    (PauliUnit.op_flipCoord_ne_of_pair_ne Pa Qa hik)
    (PauliUnit.op_flipCoord_ne_of_block_ne Pa Qb hac i l)
    (PauliUnit.op_flipCoord_ne_of_block_ne Pb Qa hab.symm j k)
    (PauliUnit.op_flipCoord_ne_of_block_ne Pb Qb hbc j l)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pa Pb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Pa Qa hik hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pa Qb hac hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pb Qa hab.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pb Qb hbc hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qa Qb hac hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Qa Pa hik.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qa Pb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qb Pa hac.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qb Pb hbc.symm hc)

/-- **Lemma D.3** (arXiv:2412.07764v1, App. D p. 19, Eq. (D16)).  For two distinct blocks
`a, b`, gadgets `A = Z_i^(a) X_j^(b)` (or `X_i^(a) Z_j^(b)`) and
`B = Z_k^(a) X_l^(b)` (or `X_k^(a) Z_l^(b)`) whose operators on each block sit in different
Bell pairs (`(i,k), (j,l) ∈ {(1,3),…,(4,2)}`) do not interfere. -/
theorem lemma_D3 (gx gz : β → ℝ) {a b : β} (hab : a ≠ b)
    (i j k l : Fin 4) (hik : qubitPair i ≠ qubitPair k) (hjl : qubitPair j ≠ qubitPair l)
    (Pa Pb Qa Qb : PauliUnit)
    (_hA : (Pa = PauliUnit.Z ∧ Pb = PauliUnit.X) ∨ (Pa = PauliUnit.X ∧ Pb = PauliUnit.Z))
    (_hB : (Qa = PauliUnit.Z ∧ Qb = PauliUnit.X) ∨ (Qa = PauliUnit.X ∧ Qb = PauliUnit.Z)) :
    P0 gx gz * gadgetTerm Pa a i Pb b j * HpenInv gx gz * gadgetTerm Qa a k Qb b l * P0 gx gz
      + P0 gx gz * gadgetTerm Qa a k Qb b l * HpenInv gx gz *
        gadgetTerm Pa a i Pb b j * P0 gx gz = 0 := by
  simp only [gadgetTerm]
  exact interference_zero_of_disjoint gx gz _ _ _ _
    (PauliUnit.op_flipCoord_ne_of_block_ne Pa Pb hab i j)
    (PauliUnit.op_flipCoord_ne_of_pair_ne Pa Qa hik)
    (PauliUnit.op_flipCoord_ne_of_block_ne Pa Qb hab i l)
    (PauliUnit.op_flipCoord_ne_of_block_ne Pb Qa hab.symm j k)
    (PauliUnit.op_flipCoord_ne_of_pair_ne Pb Qb hjl)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pa Pb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Pa Qa hik hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pa Qb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Pb Qa hab.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Pb Qb hjl hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qa Qb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Qa Pa hik.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qa Pb hab hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord Qb Pa hab.symm hc)
    (fun c₁ hc => PauliUnit.op_coeffCoord_ne_flipCoord_pair Qb Pb hjl.symm hc)

end Qatlib.Papers.AnalogSimCode24.MainResults.Interference
