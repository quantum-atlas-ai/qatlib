/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# HaarAverages/Twirling — Lemma 3 (Eqs. (304)–(311)) and Supplemental Proposition 4
(Eqs. (312)–(314))

Paper: Rudolph–Lerch–Thanasilp–Kiss–Shaya–Vallecorsa–Grossi–Holmes, *Trainability barriers and
opportunities in quantum generative modeling*, fixed arXiv:2305.02881v2, Lemma 3
(pp.~54–55) and Supplemental Proposition 4 (p.~55).

Lemma 3 studies a single Pauli-rotation layer of a hardware-efficient ansatz,
`U(α) = e^{−iαG/2} V` with `G` a Pauli operator (Eq. 305).  Because `G` and the observable `B`
are Pauli operators one has `G² = 1` and `GB = ±BG`, so the conjugation collapses to
(Eqs. 306–308)

`U† B U = cos²(α/2) V†BV + sin²(α/2) V†GBGV + sin(α) V†(i/2 [G,B]) V`.

At the **Clifford angles** `α ∈ {0, π/2}` this reduces (Eq. 310) either to `V†BV` (`α = 0`) or to
`V†(i/2 [G,B])V` (`α = π/2`), and because `V` is a Clifford gate the result is again a signed
Pauli string (Eq. 311), giving Eq. (304) `B_{αc} = U†(αc) B U(αc) ∈ ±P_n`.

This file formalises:

* the Pauli-string layer (`Pauli`, `pauliMat`, `pauliString`, `pauliWeight`) and the signed-Pauli
  predicate `IsSignedPauliString` capturing `±P_n`;
* the conjugation `conjBy V B = Vᴴ B V` with its linearity, and the predicate
  `IsCliffordGate` (a gate mapping signed Pauli strings to signed Pauli strings — this is exactly
  the content of `V†BV, V†(i/2[G,B])V ∈ ±{1,X,Y,Z}^{⊗n}`, Eq. 311);
* the iterative form of Eq. (304) (`lemma3_layered`: composing Clifford layers preserves the
  signed-Pauli property);
* the angle collapse of Eq. (310): `lemma3_branch_zero` (`α = 0` leaves the first term) and
  `lemma3_branch_half` (`α = π/2` with `GBG = −B` leaves the third term), both by genuine
  trigonometric evaluation at the Clifford angles;
* Supplemental Proposition 4 in averaged form: the Clifford average `cliffordAvg` over
  `D_c = Unif({0, π/2}^M)`, its normalisation `cliffordAvg_const`, nonnegativity, the second
  moment identity Eq. (312) (`suppProp4_second_moment`), the δ-structure of the two-copy cross
  moment Eq. (313) (`suppProp4_cross_moment`) and the vanishing three-copy moment Eq. (314)
  (`suppProp4_third_moment_zero`).

The model-level derivations (the operator algebra behind Eqs. 306–308, the two-copy tensor
algebra of Eq. 312 and the vectorised Dirac/Pauli contractions of Eqs. 313–314) are recorded in
the module comment `twirling_gap`.
-/

open scoped BigOperators

namespace Qatlib.Papers.Trainability23.HaarAverages.Twirling

noncomputable section

/-- The matrix algebra acting on `n` qubits, with bitstrings `Fin n → Fin 2` as a basis. -/
abbrev Mat (n : ℕ) := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ

/-! ## Pauli strings and the signed-Pauli predicate `±P_n` -/

/-- The four single-qubit Pauli matrices, as an inductive index type. -/
inductive Pauli
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype, Repr

/-- The single-qubit Pauli matrix associated with an index.  (Defined entrywise; `!!!`-style
matrix literals are not available in this Mathlib snapshot.) -/
def pauliMat : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | Pauli.I => fun i j => if i = j then 1 else 0
  | Pauli.X => fun i j => if i ≠ j then 1 else 0
  | Pauli.Y => fun i j => if i = 0 ∧ j = 1 then -Complex.I else if i = 1 ∧ j = 0 then Complex.I else 0
  | Pauli.Z => fun i j => if i = j then (if i = 0 then 1 else -1) else 0

/-- The `n`-qubit Pauli string `P_σ = ⊗ᵢ P_{σᵢ}`: the entry on basis vectors `x, y` is the
product of the single-qubit entries. -/
def pauliString (n : ℕ) (σ : Fin n → Pauli) : Mat n :=
  Matrix.of fun x y => ∏ i, pauliMat (σ i) (x i) (y i)

/-- The weight of a Pauli string: the number of non-identity factors. -/
def pauliWeight (n : ℕ) (σ : Fin n → Pauli) : ℕ :=
  (Finset.univ.filter fun i => σ i ≠ Pauli.I).card

/-- A Pauli string has weight at most `n`. -/
theorem pauliWeight_le (n : ℕ) (σ : Fin n → Pauli) : pauliWeight n σ ≤ n := by
  unfold pauliWeight
  calc (Finset.univ.filter fun i => σ i ≠ Pauli.I).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- `M` is a *signed Pauli string*, i.e. `M ∈ ±P_n` in the notation of Eq. (304). -/
def IsSignedPauliString {n : ℕ} (M : Mat n) : Prop :=
  ∃ σ : Fin n → Pauli, M = pauliString n σ ∨ M = -pauliString n σ

/-- `±P_n` is closed under negation. -/
theorem signedPauli_neg {n : ℕ} {M : Mat n} (h : IsSignedPauliString M) :
    IsSignedPauliString (-M) := by
  obtain ⟨σ, hσ | hσ⟩ := h
  · exact ⟨σ, Or.inr (by rw [hσ])⟩
  · exact ⟨σ, Or.inl (by rw [hσ, neg_neg])⟩

/-! ## Conjugation by a gate and Clifford gates -/

/-- Conjugation `B ↦ V† B V`.  This is the action of Eq. (304) with `V = U(αc)`; it is written in
terms of `Matrix.conjTranspose` so that no Hilbert-space adjoint API is needed. -/
def conjBy {n : ℕ} (V B : Mat n) : Mat n := Matrix.conjTranspose V * B * V

/-- Conjugation is additive in the observable. -/
theorem conjBy_add {n : ℕ} (V B C : Mat n) :
    conjBy V (B + C) = conjBy V B + conjBy V C := by
  unfold conjBy
  rw [Matrix.mul_add, Matrix.add_mul]

/-- Conjugation is additive in the observable (subtraction form). -/
theorem conjBy_sub {n : ℕ} (V B C : Mat n) :
    conjBy V (B - C) = conjBy V B - conjBy V C := by
  unfold conjBy
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- Conjugation preserves negation of the observable. -/
theorem conjBy_neg {n : ℕ} (V B : Mat n) : conjBy V (-B) = -conjBy V B := by
  unfold conjBy
  rw [Matrix.mul_neg, Matrix.neg_mul]

/-- Conjugation by a gate sends `0` to `0`. -/
theorem conjBy_zero {n : ℕ} (V : Mat n) : conjBy V (0 : Mat n) = 0 := by
  unfold conjBy
  simp

/-- Conjugating twice composes the gates: `V† (W† B W) V = (WV)† B (WV)`.  This is what makes the
layer-by-layer construction of Eq. (304) well behaved. -/
theorem conjBy_conjBy {n : ℕ} (V W B : Mat n) :
    conjBy V (conjBy W B) = conjBy (W * V) B := by
  unfold conjBy
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A gate is a *Clifford gate* if it maps every signed Pauli string to a signed Pauli string.
This is precisely the property Eq. (311) establishes for the layers `V†BV` and `V†(i/2[G,B])V`. -/
def IsCliffordGate {n : ℕ} (V : Mat n) : Prop :=
  ∀ B : Mat n, IsSignedPauliString B → IsSignedPauliString (conjBy V B)

/-- The identity gate is Clifford. -/
theorem isCliffordGate_one {n : ℕ} : IsCliffordGate (1 : Mat n) := by
  intro B hB
  rw [show conjBy (1 : Mat n) B = B from by unfold conjBy; simp]
  exact hB

/-- **Eq. (304), iterative form.**  Applying a list of Clifford layers (each of which is a
`V† · V` or a `V†(i/2[G,B])·` step, Eq. 311) to a signed Pauli string produces a signed Pauli
string: `B_{αc} = U†(αc) B U(αc) ∈ ±P_n` for every Clifford angle vector. -/
theorem lemma3_layered {n : ℕ} (layers : List (Mat n)) (B : Mat n)
    (hlayers : ∀ L ∈ layers, IsCliffordGate L) (hB : IsSignedPauliString B) :
    IsSignedPauliString (layers.foldr conjBy B) := by
  induction layers with
  | nil => simpa using hB
  | cons L ls ih =>
      simp only [List.foldr_cons]
      exact (hlayers L (List.mem_cons_self ..))
        (List.foldr conjBy B ls) (ih fun L' hL' => hlayers L' (List.mem_cons_of_mem _ hL'))

/-- **Eq. (311) / Eq. (310), first branch.**  If `V` is a Clifford gate then `V†BV` is a signed
Pauli string for every signed Pauli string `B`. -/
theorem lemma3_effective_is_signed_pauli {n : ℕ} (V B : Mat n)
    (hV : IsCliffordGate V) (hB : IsSignedPauliString B) :
    IsSignedPauliString (conjBy V B) :=
  hV B hB

/-- **Eq. (311) / Eq. (310), second branch.**  If `V` is a Clifford gate and the commutator
`i[G,B] = i(GB − BG)` is a signed Pauli string (which it is for Pauli `G, B`), then
`V†(i/2 [G,B])V` is again a signed Pauli string. -/
theorem lemma3_effective_is_signed_pauli_commutator {n : ℕ} (V G B : Mat n)
    (hV : IsCliffordGate V) (hcomm : IsSignedPauliString (G * B - B * G)) :
    IsSignedPauliString (conjBy V (G * B - B * G)) :=
  hV (G * B - B * G) hcomm

/-! ## Eq. (310): collapse of the angle expansion at the Clifford angles -/

/-- `cos(π/4)² = 1/2`. -/
theorem cos_pi_div_four_sq : Real.cos (Real.pi / 4) ^ 2 = (1 / 2 : ℝ) := by
  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `sin(π/4)² = 1/2`. -/
theorem sin_pi_div_four_sq : Real.sin (Real.pi / 4) ^ 2 = (1 / 2 : ℝ) := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The half-angle identity behind Eqs. (306)–(308): the coefficients `cos²(α/2)` and
`sin²(α/2)` sum to one, so the expansion is a convex combination of the two Pauli branches. -/
theorem coefficient_normalisation (α : ℝ) :
    Real.cos (α / 2) ^ 2 + Real.sin (α / 2) ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq (α / 2)

/-- **Eq. (310), first branch, `α = 0`.**  At the Clifford angle `α = 0` the sandwich expansion
`cos²(α/2)·e₀ + sin²(α/2)·e₁ + sin(α)·e₂` of Eqs. (306)–(308) collapses onto the first branch
`e₀ = V†BV`.  Here `e₀, e₁, e₂` are the three operator terms `V†BV`, `V†GBGV`, `V†(i/2[G,B])V`,
represented as the standard basis vectors of `Fin 3 → ℝ` (the operator algebra itself is the
model-layer gap documented in `twirling_gap`). -/
theorem lemma3_branch_zero :
    (Real.cos (0 / 2)) ^ 2 • (Pi.single 0 (1 : ℝ) : Fin 3 → ℝ)
        + (Real.sin (0 / 2)) ^ 2 • (Pi.single 1 (1 : ℝ) : Fin 3 → ℝ)
        + Real.sin 0 • (Pi.single 2 (1 : ℝ) : Fin 3 → ℝ)
      = Pi.single 0 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp (config := { decide := true }) [Real.cos_zero, Real.sin_zero]

/-- **Eq. (310), second branch, `α = π/2`.**  At the Clifford angle `α = π/2`, if the two Pauli
branches are related by `e₁ = −e₀` (which is `GBG = −B`, i.e. `G` and `B` anticommute — one of
the two branches of Eq. 309), the expansion collapses onto the third branch
`e₂ = V†(i/2[G,B])V`.  The first two coefficients are both `1/2`, so they cancel. -/
theorem lemma3_branch_half :
    (Real.cos (Real.pi / 2 / 2)) ^ 2 • (Pi.single 0 (1 : ℝ) : Fin 3 → ℝ)
        + (Real.sin (Real.pi / 2 / 2)) ^ 2 • (-(Pi.single 0 (1 : ℝ) : Fin 3 → ℝ))
        + Real.sin (Real.pi / 2) • (Pi.single 2 (1 : ℝ) : Fin 3 → ℝ)
      = Pi.single 2 (1 : ℝ) := by
  have hpi : Real.pi / 2 / 2 = Real.pi / 4 := by ring
  funext i
  fin_cases i <;> simp (config := { decide := true }) [hpi, Real.sin_pi_div_two]

/-- **Eq. (309), anticommuting branch.**  If `G * B * G = −B` then the commutator doubles:
`G*B − B*G = 2 • (G*B)`, which is why at `α = π/2` the effective operator is
`V†(i G B)V` (Eq. 310). -/
theorem commutator_of_anticommute {n : ℕ} (G B : Mat n) (h : G * B = -(B * G)) :
    G * B - B * G = (2 : ℂ) • (G * B) := by
  have h2 : (2 : ℂ) • (G * B) = G * B + G * B := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
  rw [h2, h, sub_eq_add_neg]

/-! ## Supplemental Proposition 4: Clifford twirling averages (Eqs. (312)–(314)) -/

/-- The Clifford angle vector associated with a bit vector `αc ∈ {0,1}^M`:
`αc k = true ↦ α_k = π/2`, `αc k = false ↦ α_k = 0` (the angles appearing in Eq. 296). -/
def cliffordAngle {M : ℕ} (αc : Fin M → Bool) : Fin M → ℝ :=
  fun k => if αc k then Real.pi / 2 else 0

/-- The Clifford average over `D_c = Unif({0, π/2}^M)` (Eq. 296):
`E_{αc∼D_c}[f(αc)] = 2^{−M} Σ_{αc} f(αc)`. -/
def cliffordAvg {M : ℕ} (f : (Fin M → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool, f αc

/-- The Clifford average is normalised: averaging a constant returns the constant. -/
theorem cliffordAvg_const {M : ℕ} (c : ℝ) : cliffordAvg (fun _ : Fin M → Bool => c) = c := by
  unfold cliffordAvg
  have hcard : Fintype.card (Fin M → Bool) = 2 ^ M := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow]
  field_simp
  norm_num

/-- The Clifford average respects pointwise equality. -/
theorem cliffordAvg_congr {M : ℕ} {f g : (Fin M → Bool) → ℝ} (h : ∀ αc, f αc = g αc) :
    cliffordAvg f = cliffordAvg g := by
  unfold cliffordAvg
  congr 1
  exact Finset.sum_congr rfl fun αc _ => h αc

/-- A pointwise nonnegative function has nonnegative Clifford average. -/
theorem cliffordAvg_nonneg {M : ℕ} {f : (Fin M → Bool) → ℝ} (h : ∀ αc, 0 ≤ f αc) :
    0 ≤ cliffordAvg f := by
  unfold cliffordAvg
  refine mul_nonneg ?_ (Finset.sum_nonneg fun αc _ => h αc)
  positivity

/-- **Supplemental Proposition 4, Eq. (312).**  If, for every Clifford angle vector, the
two-copy matrix element `(U†(αc))^{⊗2} B^{⊗2} (U(αc))^{⊗2}` evaluates to the operator `B_{αc}`
(Eq. 304), then the average over all angles equals the Clifford average of the operators
`B_{αc}`.  This is the residue form of Eq. (312): the paper's work is the per-setting
evaluation, which is the model-layer gap recorded in `twirling_gap`. -/
theorem suppProp4_second_moment {M : ℕ} (Mobs : (Fin M → ℝ) → ℝ)
    (Beff : (Fin M → Bool) → ℝ) (hres : ∀ αc, Mobs (cliffordAngle αc) = Beff αc) :
    cliffordAvg (fun αc => Mobs (cliffordAngle αc)) = cliffordAvg Beff :=
  cliffordAvg_congr hres

/-- **Supplemental Proposition 4, Eq. (313).**  The two-copy cross moment
`E_{α,β} Tr[(U_tensor(β))^{⊗2} ρ₀^{⊗2} (U_tensor(β))^{†⊗2} (U†(α))^{⊗2} (B⊗B') (U(α))^{⊗2}]`
carries a Kronecker delta `δ_{B,B'}`: it vanishes for `B ≠ B'`, and for `B = B'` it equals the
Clifford average of `(1/3)^{Δ_B(αc)}`.  The per-setting evaluations (the Pauli orthogonality of
the two-copy contraction) are the hypothesis here; the equation records the resulting averaged
statement. -/
theorem suppProp4_cross_moment {M : ℕ} (crossMoment : (Fin M → Bool) → ℝ)
    (ΔB : (Fin M → Bool) → ℕ) (B B' : ℕ)
    (hne : B ≠ B' → ∀ αc, crossMoment αc = 0)
    (heq : B = B' → ∀ αc, crossMoment αc = (1 / 3 : ℝ) ^ (ΔB αc)) :
    cliffordAvg crossMoment
      = if B = B' then cliffordAvg (fun αc => (1 / 3 : ℝ) ^ (ΔB αc)) else 0 := by
  by_cases h : B = B'
  · subst h
    rw [if_pos rfl]
    exact cliffordAvg_congr fun αc => heq rfl αc
  · rw [if_neg h]
    unfold cliffordAvg
    rw [Finset.sum_eq_zero fun αc _ => hne h αc, mul_zero]

/-- **Supplemental Proposition 4, Eq. (314).**  The three-copy moment vanishes identically: if
every per-setting value of the three-copy contraction is zero, so is the Clifford average. -/
theorem suppProp4_third_moment_zero {M : ℕ} (oddMoment : (Fin M → Bool) → ℝ)
    (hzero : ∀ αc, oddMoment αc = 0) : cliffordAvg oddMoment = 0 := by
  unfold cliffordAvg
  rw [Finset.sum_eq_zero fun αc _ => hzero αc, mul_zero]

/-- The Clifford angles take only the values `0` and `π/2`: the sanity check behind the
discrete set `D_c = Unif({0, π/2}^M)` of Eq. (296). -/
theorem cliffordAngle_cases {M : ℕ} (αc : Fin M → Bool) (k : Fin M) :
    cliffordAngle αc k = 0 ∨ cliffordAngle αc k = Real.pi / 2 := by
  unfold cliffordAngle
  by_cases h : αc k
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-!
## `twirling_gap` — proof route and current library gap

Fixed paper version: arXiv:2305.02881v2 (npj QI 2024, DOI 10.1038/s41534-024-00902-0), Lemma 3
(pp.~54–55) and Supplemental Proposition 4 (p.~55).

Paper proof steps for Lemma 3: (i) `U(α) = e^{−iαG/2} V` (Eq. 305) with `G² = 1`, `GB = ±BG`, so
`e^{iαG/2} B e^{−iαG/2} = cos²(α/2) B + sin²(α/2) GBG + i sin(α/2)cos(α/2)(GB − BG)`
(Eqs. 306–308); (ii) at `α = 0` only the first term survives, at `α = π/2` the first two cancel
because `GBG = −B` (Eqs. 309–310); (iii) `V` Clifford and `B`, `i/2[G,B]` Pauli give Eq. (311);
(iv) applying the layers one at a time gives `B_{αc} ∈ ±P_n` (Eq. 304).

Paper proof steps for Supplemental Proposition 4: (i) the two-copy average over all angles equals
the average over the Clifford angles after expanding in the Pauli basis (Eq. 312), because the
single-qubit functions `cos², sin², sin·cos` have the same average over the Clifford angle set
and over the full continuous range; (ii) two-copy Pauli contractions are orthogonal unless the
Pauli strings agree, giving `δ_{B,B'}` with survivor weight `(1/3)^{Δ_B(αc)}` (Eq. 313);
(iii) three-copy contractions vanish because copies are traced out in pairs (Eq. 314).

Current Lean gap: this file formalises the layer structure (`IsCliffordGate`, `conjBy`,
`lemma3_layered`), the exact trigonometric collapse at the Clifford angles
(`lemma3_branch_zero`, `lemma3_branch_half`), and the averaged form of Eqs. (312)–(314).  Two
model-layer pieces are not developed and are the reason the last three theorems take the
per-setting evaluations as hypotheses: (a) the Hilbert-space adjoint and the exponential
`e^{−iαG/2}` as a `Matrix` object with the expansion (306)–(308); (b) the two- and three-copy tensor
algebra `Tr[(V^{⊗k})† B^{⊗k} V^{⊗k} · ρ₀^{⊗k}]` and the Pauli orthogonality behind `δ_{B,B'}`.

Candidate reusable dependencies: `Matrix.conjTranspose_mul`, `Matrix.mul_add`,
`Matrix.add_mul`, `Matrix.mul_neg`, `Matrix.neg_mul`, `Real.cos_sq_add_sin_sq`,
`Real.cos_pi_div_four`, `Real.sin_pi_div_four`, `Real.sin_pi_div_two`, `Matrix.trace_mul_cycle`,
`Finset.sum_congr`, `Finset.sum_eq_zero`.

Suggested takeover tactics: (1) build `e^{−iαG/2}` from the Pauli exponential (a `2×2`
`Complex.exp`/`Matrix.exp` computation on the `G² = 1` eigenbasis) and derive (306)–(308) by
`Matrix.ext` and `ring`; (2) define the two-copy map `B ↦ (B ⊗ B)` and use `Matrix.trace_mul_cycle`
with `Fintype.sum_prod_type` to prove the Pauli orthogonality `Tr[P_σ P_τ] = 2^n δ_{σ,τ}`;
(3) instantiate `suppProp4_second_moment`/`suppProp4_cross_moment` with those evaluations.
-/

end

end Qatlib.Papers.Trainability23.HaarAverages.Twirling
