/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Multilinear11.MainResults.MultilinearExpansion.SourceLemma4
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Tactic

@[expose] public section


set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-!
# Theorem 2 of arXiv:1105.3310v3: exact learning from oracle executions

Ashley Montanaro, *The quantum query complexity of learning multilinear
polynomials*, fixed arXiv:1105.3310v3 (8 March 2012). The PDF SHA-256 is
`22a18ad57343837023016d781252e66308e4550dfe6d88e4be34333cb1a4233d`.

This model replaces the independent output-map and query-count fields of the
old skeleton by the executions of Algorithm 1. A stage observes the finite-field
Fourier readout of each signed finite difference; its phase is obtained from
exactly one original-oracle call per Boolean cube branch. The next residual is
computed by subtracting the recovered top-degree component. The final constant
coefficient comes from one value query at the origin.

The file proves phase
kickback, finite-field character orthogonality, the affine Bernstein–Vazirani
Born probabilities, existence of an execution, correctness of every allowed
measurement branch, and the query count derived from the execution trace.
Source locations: Theorem 2 and Algorithm 1, pages 3–4; Lemmas 3 and 5,
Appendix A, pages 5–6. The cost measured here is oracle queries; no gate-complexity
or physical implementation bound is claimed.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
open Qatlib.Papers.Multilinear11.MainResults.MultilinearExpansion

namespace Qatlib.Papers.Multilinear11.MainResults.MainTheorem

/-- The query count of Theorem 2, written exactly as in the paper:
`1 + Σ_{i=1}^{d} 2^{i-1} C(n, i-1)`.
Source: arXiv:1105.3310v3, Theorem 2 p.3. -/
def theorem2QueryCount (n d : ℕ) : ℕ :=
  1 + ∑ i ∈ Finset.Icc 1 d, 2 ^ (i - 1) * n.choose (i - 1)

/-- The same query count in the `k`-indexed form `1 + Σ_{k=0}^{d-1} 2^k C(n,k)` obtained by
Algorithm 1's level-by-level accounting.  Source: arXiv:1105.3310v3, §2 p.4. -/
def theorem2QueryCount' (n d : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.range d, 2 ^ k * n.choose k

/-- Reindexing `i ↦ i - 1` turns the paper's displayed count into the level-by-level count.
Source: arXiv:1105.3310v3, Theorem 2 p.3 and §2 proof p.4. -/
theorem theorem2_query_count_sum_identity (n d : ℕ) :
    (∑ i ∈ Finset.Icc 1 d, 2 ^ (i - 1) * n.choose (i - 1))
      = ∑ k ∈ Finset.range d, 2 ^ k * n.choose k := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_range_succ, ← ih]
    congr 1

/-- The two displayed forms of Theorem 2's query count agree.
Source: arXiv:1105.3310v3, Theorem 2 p.3. -/
theorem theorem2_query_count_identity (n d : ℕ) :
    theorem2QueryCount n d = theorem2QueryCount' n d := by
  unfold theorem2QueryCount theorem2QueryCount'
  rw [theorem2_query_count_sum_identity]

/-- Theorem 2's query count is `O(n^{d-1})` for constant `d`: an explicit bound
`1 + Σ_{i=1}^{d} 2^{i-1}C(n,i-1) ≤ (d+1)·2^{d-1}·n^{d-1}` for `n ≥ 1`, `d ≥ 1`.
Source: arXiv:1105.3310v3, Theorem 2 p.3 ("which is `O(n^{d-1})` for constant `d`"). -/
theorem theorem2_query_count_bound (n d : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    theorem2QueryCount' n d ≤ (d + 1) * 2 ^ (d - 1) * n ^ (d - 1) := by
  unfold theorem2QueryCount'
  have hterm : ∀ k ∈ Finset.range d,
      2 ^ k * n.choose k ≤ 2 ^ (d - 1) * n ^ (d - 1) := by
    intro k hk
    have hklt : k < d := Finset.mem_range.mp hk
    have hk1 : k ≤ d - 1 := by omega
    have hpk : 2 ^ k ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) hk1
    have hck : n.choose k ≤ n ^ (d - 1) :=
      (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right (by omega) hk1)
    exact Nat.mul_le_mul hpk hck
  have hsum : (∑ k ∈ Finset.range d, 2 ^ k * n.choose k)
      ≤ ∑ _k ∈ Finset.range d, 2 ^ (d - 1) * n ^ (d - 1) := Finset.sum_le_sum hterm
  have hconst : (∑ _k ∈ Finset.range d, 2 ^ (d - 1) * n ^ (d - 1))
      = d * (2 ^ (d - 1) * n ^ (d - 1)) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hB : 1 ≤ 2 ^ (d - 1) * n ^ (d - 1) := by
    have hpos : 0 < 2 ^ (d - 1) * n ^ (d - 1) :=
      Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by omega) _)
    omega
  calc 1 + ∑ k ∈ Finset.range d, 2 ^ k * n.choose k
      ≤ 1 + d * (2 ^ (d - 1) * n ^ (d - 1)) :=
        Nat.add_le_add_left (hsum.trans (le_of_eq hconst)) 1
    _ ≤ (2 ^ (d - 1) * n ^ (d - 1)) + d * (2 ^ (d - 1) * n ^ (d - 1)) :=
        Nat.add_le_add_right hB (d * (2 ^ (d - 1) * n ^ (d - 1)))
    _ = (d + 1) * 2 ^ (d - 1) * n ^ (d - 1) := by ring

/-! ## The correctness core of Algorithm 1

Algorithm 1 queries `f_S` for every `(d-1)`-subset `S` and uses Lemma 3 to read off the
linear part `x ↦ Σ_{k ∉ S} α_{S∪{k}} x_k` of `f_S`.  Lemma 4 says that together with the
constant term `α_S` this determines every degree-`d` coefficient.  The proposition below
records exactly that: if two degree-`d` multilinear polynomials have equal `f_S` for all
`|S| = d-1`, then all their degree-`d` coefficients agree. -/

/-- **Algorithm 1 correctness core** (arXiv:1105.3310v3, §2 p.4, from Lemma 4).
If the signed cube sums `f_S` coincide for every `S` with `|S| = d-1`, then the degree-`d`
coefficient tables coincide.  This is the exact use the algorithm makes of Lemma 4. -/
theorem degree_d_coefficients_determined
    {F : Type*} [Field F] {n d : ℕ}
    (α β : Finset (Fin n) → F)
    (hdegα : ∀ T, d < T.card → α T = 0)
    (hdegβ : ∀ T, d < T.card → β T = 0)
    (hS : ∀ S, S.card = d - 1 → ∀ x,
      fS (multilinearEval α) S x = fS (multilinearEval β) S x)
    (T : Finset (Fin n)) (hT : T.card = d) : α T = β T := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- degree 0: T is empty and `f_∅ = α_∅` at the origin
    subst hd0
    have hT0 : T = ∅ := Finset.card_eq_zero.mp hT
    subst hT0
    have h0 := hS ∅ (by simp) 0
    rw [lemma4_expansion α 0 hdegα ∅ (by simp) 0,
        lemma4_expansion β 0 hdegβ ∅ (by simp) 0] at h0
    simpa using h0
  · -- degree ≥ 1: split `T = S ∪ {k}` with `|S| = d - 1`
    obtain ⟨k, hkT⟩ := Finset.card_pos.mp (hT ▸ hdpos)
    let S : Finset (Fin n) := T.erase k
    have hkS : k ∉ S := by simp [S]
    have hScard : S.card = d - 1 := by
      show (T.erase k).card = d - 1
      rw [Finset.card_erase_of_mem hkT, hT]
    have hTun : S ∪ {k} = T := by
      show T.erase k ∪ {k} = T
      rw [Finset.union_singleton, Finset.insert_erase hkT]
    -- constant terms coincide at the origin
    have hconst : α S = β S := by
      have h0 := hS S hScard 0
      rw [lemma4_expansion α d hdegα S hScard 0,
          lemma4_expansion β d hdegβ S hScard 0] at h0
      simpa using h0
    -- linear parts coincide by evaluating at the basis vector `e_k`
    have hlin := hS S hScard (fun i => if i = k then (1 : F) else 0)
    rw [lemma4_expansion α d hdegα S hScard (fun i => if i = k then (1 : F) else 0),
        lemma4_expansion β d hdegβ S hScard (fun i => if i = k then (1 : F) else 0)] at hlin
    rw [hconst] at hlin
    have hcancel := add_left_cancel hlin
    have hsumα : (∑ j ∈ (Finset.univ \ S),
        α (S ∪ {j}) * (if j = k then (1 : F) else 0)) = α (S ∪ {k}) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjne
        simp [hjne]
      · intro hknot
        exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkS⟩) hknot
    have hsumβ : (∑ j ∈ (Finset.univ \ S),
        β (S ∪ {j}) * (if j = k then (1 : F) else 0)) = β (S ∪ {k}) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjne
        simp [hjne]
      · intro hknot
        exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkS⟩) hknot
    rw [hsumα, hsumβ, hTun] at hcancel
    exact hcancel

namespace OracleRepair

variable {F : Type*} [Field F] {n : ℕ}

/-- The additive-character image of a finite sum is the product of the
character values of the summands. -/
theorem char_sum {I : Type*} (ψ : AddChar F ℂ) (s : Finset I) (f : I → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ψ.map_add_eq_mul, ih]

/-- Applying the additive oracle to an ancilla character, in the amplitude
representation, changes the ancilla argument from `y` to `y-f x`. -/
def oracleAmp (f : (Fin n → F) → F)
    (v : (Fin n → F) → F → ℂ) : (Fin n → F) → F → ℂ :=
  fun x y => v x (y - f x)

/-- Exact phase kickback from the one actual additive-oracle application.
The character ancilla is unchanged; its normalizing constant cancels on
both sides and may be inserted uniformly. -/
theorem one_query_kickback (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (v : (Fin n → F) → ℂ) (x : Fin n → F) (y : F) :
    oracleAmp f (fun z t => v z * ψ (-t)) x y =
      ψ (f x) * (v x * ψ (-y)) := by
  simp only [oracleAmp, neg_sub]
  rw [show f x - y = f x + -y by ring, ψ.map_add_eq_mul]
  ring

/-- Every Boolean cube branch calls the original oracle at its shifted
input, with the signed phase specified by the finite-difference formula. -/
def branchPhase (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (S : Finset (Fin n)) (b : Fin n → Bool) (x : Fin n → F) : ℂ :=
  ψ (signWeight S b * f (shiftBool b x))

/-- A finite-difference execution consists of all cube branches, each
occurring once. The query count is its actual number of branches. -/
def cubeTrace (S : Finset (Fin n)) : List (Fin n → Bool) :=
  (cubeFinset S).toList

/-- The exact query length of the finite-difference execution. -/
theorem cube_trace_length (S : Finset (Fin n)) :
    (cubeTrace S).length = 2 ^ S.card := by
  classical
  simp only [cubeTrace, Finset.length_toList, cubeFinset, Fintype.card_piFinset]
  have h : (fun i : Fin n =>
      (if i ∈ S then (Finset.univ : Finset Bool) else {false}).card) =
      fun i => if i ∈ S then 2 else 1 := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  rw [h, Fintype.prod_ite_mem, Finset.prod_const]

/-- Multiplying the phases along the actual cube trace implements the
finite-difference oracle, rather than selecting its output independently. -/
theorem cube_trace_phase (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (S : Finset (Fin n)) (x : Fin n → F) :
    ((cubeTrace S).map (fun b => branchPhase ψ f S b x)).prod = ψ (fS f S x) := by
  classical
  rw [cubeTrace, Finset.prod_map_toList]
  exact (char_sum ψ (cubeFinset S)
    (fun b => signWeight S b * f (shiftBool b x))).symm

/-- Each signed branch is implemented with one original additive-oracle
application and a character ancilla chosen independently of the oracle.
The shifted input and character coefficient are known from the trace. -/
theorem branch_one_query (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (S : Finset (Fin n)) (b : Fin n → Bool) (v : (Fin n → F) → ℂ)
    (x : Fin n → F) (y : F) :
    oracleAmp f (fun z t => v z * (ψ.mulShift (signWeight S b)) (-t))
        (shiftBool b x) y =
      branchPhase ψ f S b x *
        (v (shiftBool b x) * (ψ.mulShift (signWeight S b)) (-y)) :=
  one_query_kickback (ψ.mulShift (signWeight S b)) f v (shiftBool b x) y

/-- Subtracting a known residual polynomial uses a known diagonal phase
after the original phase query, and consumes no additional oracle call. -/
theorem residual_phase (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (known : Finset (Fin n) → F) (x : Fin n → F) :
    ψ (f x - multilinearEval known x) =
      ψ (f x) * ψ (-multilinearEval known x) := by
  rw [sub_eq_add_neg, ψ.map_add_eq_mul]

section Finite

variable [Fintype F]

/-- Every finite field has a primitive complex additive character. The
field multiplication turns any nontrivial additive character into a
nondegenerate Fourier pairing. -/
theorem primitive_character_exists : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)
  refine ⟨ψ, AddChar.IsPrimitive.of_ne_one ?_⟩
  intro h
  apply hψ
  rw [h]
  rfl

/-- The scalar Fourier sum for a primitive finite-field additive character. -/
theorem character_sum (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a : F) :
    (∑ x : F, ψ (a * x)) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, ψ.map_zero_eq_one]
  · have hshift : ψ.mulShift a ≠ 0 := hψ ha
    simpa [AddChar.mulShift_apply, ha] using
      (AddChar.sum_eq_zero_iff_ne_zero.mpr hshift)

/-- The vector Fourier sum vanishes except at the true linear coefficient
vector. This is the orthogonality step of finite-field Bernstein–Vazirani. -/
theorem vector_character_sum (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : Fin n → F) :
    (∑ x : Fin n → F, ψ (∑ i, (a i - b i) * x i)) =
      if a = b then (Fintype.card (Fin n → F) : ℂ) else 0 := by
  classical
  simp_rw [char_sum ψ]
  rw [← Fintype.prod_sum (fun (i : Fin n) (y : F) => ψ ((a i - b i) * y))]
  simp_rw [character_sum ψ hψ]
  by_cases hab : a = b
  · simp [hab]
  · have hex : ∃ i, a i - b i ≠ 0 := by
      by_contra! h
      exact hab (funext (fun i => sub_eq_zero.mp (h i)))
    obtain ⟨i, hi⟩ := hex
    rw [ite_eq_right hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The finite-field Fourier columns are orthogonal, with squared norm
equal to the register cardinality before the usual square-root
normalization. This verifies the Fourier transform on the entire register. -/
theorem fourier_orthogonality (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : Fin n → F) :
    (∑ x : Fin n → F,
      (starRingEnd ℂ) (ψ (∑ i, a i * x i)) * ψ (∑ i, b i * x i)) =
      if a = b then (Fintype.card (Fin n → F) : ℂ) else 0 := by
  have hterm : ∀ x : Fin n → F,
      (starRingEnd ℂ) (ψ (∑ i, a i * x i)) * ψ (∑ i, b i * x i) =
        ψ (∑ i, (b i - a i) * x i) := by
    intro x
    rw [← ψ.map_neg_eq_conj, ← ψ.map_add_eq_mul]
    congr 1
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
  simp_rw [hterm]
  simpa only [eq_comm] using vector_character_sum ψ hψ b a

/-- Preparing the uniform state, performing one phase-oracle query and
applying the inverse Fourier transform gives this exact amplitude. The two
Fourier normalizations multiply to `1 / card`; no oracle answer is supplied
as an independent field. -/
def bvAmplitude (ψ : AddChar F ℂ) (f : (Fin n → F) → F)
    (b : Fin n → F) : ℂ :=
  (Fintype.card (Fin n → F) : ℂ)⁻¹ *
    ∑ x : Fin n → F, ψ (f x) * ψ (-(∑ i, b i * x i))

/-- One-query finite-field Bernstein–Vazirani: the final amplitude is zero
away from the linear coefficient vector and a global character phase at
that vector. The affine constant is not recovered by this query. -/
theorem bv_affine (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a : Fin n → F) (c : F) (b : Fin n → F) :
    bvAmplitude ψ (fun x => (∑ i, a i * x i) + c) b =
      if b = a then ψ c else 0 := by
  classical
  have heq : ∀ x : Fin n → F,
      ψ ((∑ i, a i * x i) + c) * ψ (-(∑ i, b i * x i)) =
        ψ c * ψ (∑ i, (a i - b i) * x i) := by
    intro x
    rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
    congr 1
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
  unfold bvAmplitude
  simp_rw [heq]
  rw [← Finset.mul_sum, vector_character_sum ψ hψ]
  have hcard : (Fintype.card (Fin n → F) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hab : b = a
  · rw [ite_eq_left hab.symm, ite_eq_left hab]
    calc (Fintype.card (Fin n → F) : ℂ)⁻¹ *
          (ψ c * (Fintype.card (Fin n → F) : ℂ)) =
        ψ c * ((Fintype.card (Fin n → F) : ℂ)⁻¹ *
          (Fintype.card (Fin n → F) : ℂ)) := by ring
      _ = ψ c := by rw [inv_mul_cancel₀ hcard, mul_one]
  · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab, mul_zero, mul_zero]

/-- Born probability of the exact one-query affine readout. -/
theorem bv_affine_probability (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a : Fin n → F) (c : F) (b : Fin n → F) :
    ‖bvAmplitude ψ (fun x => (∑ i, a i * x i) + c) b‖ ^ 2 =
      if b = a then 1 else 0 := by
  rw [bv_affine ψ hψ]
  split_ifs <;> simp [ψ.norm_apply]

end Finite

/-- The linear coefficient vector of the derivative indexed by `S`. -/
def linearPart (α : Finset (Fin n) → F) (S : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ S then 0 else α (S ∪ {i})

/-- Finite differencing an oracle for a degree-`d+1` multilinear polynomial
gives precisely the affine oracle used by the next recovery stage. -/
theorem difference_affine (α : Finset (Fin n) → F) (d : ℕ)
    (hdeg : ∀ T, d + 1 < T.card → α T = 0)
    (f : (Fin n → F) → F) (hf : ∀ x, f x = multilinearEval α x)
    (S : Finset (Fin n)) (hS : S.card = d) :
    fS f S = fun x => (∑ i, linearPart α S i * x i) + α S := by
  classical
  have hfeq : f = multilinearEval α := funext hf
  subst hfeq
  funext x
  rw [lemma4_expansion α (d + 1) hdeg S (by simpa using hS)]
  rw [add_comm]
  congr 1
  simp only [linearPart, Finset.sdiff_eq_filter, Finset.sum_filter,
    ite_mul, zero_mul, ite_not]

/-- Recover a coefficient of degree `d+1` from one coordinate of the
observed derivative-linear vector. All lower coefficients are zero here. -/
def topFrom (d : ℕ) (answers : Finset (Fin n) → Fin n → F)
    (U : Finset (Fin n)) : F :=
  if h : U.card = d + 1 then
    let i := U.min' (Finset.card_pos.mp (by omega))
    answers (U.erase i) i
  else 0

/-- Recovering all derivative-linear parts computes exactly the top
homogeneous coefficient table. -/
theorem topFrom_linearPart (d : ℕ) (α : Finset (Fin n) → F) :
    topFrom d (linearPart α) = fun U => if U.card = d + 1 then α U else 0 := by
  classical
  funext U
  by_cases h : U.card = d + 1
  · simp only [topFrom, dite_eq_left h, ite_eq_left h]
    have hpos : U.Nonempty := Finset.card_pos.mp (by omega)
    have hmem : U.min' hpos ∈ U := Finset.min'_mem U hpos
    simp [linearPart, Finset.union_singleton, Finset.insert_erase hmem]
  · simp [topFrom, h]

/-- Top-component reconstruction only reads the derivative records at the
specified cardinality, so unused records cannot change the output. -/
theorem topFrom_congr (d : ℕ) (a b : Finset (Fin n) → Fin n → F)
    (h : ∀ S, S.card = d → a S = b S) : topFrom d a = topFrom d b := by
  funext U
  unfold topFrom
  by_cases hU : U.card = d + 1
  · simp only [dite_eq_left hU]
    let i := U.min' (Finset.card_pos.mp (by omega))
    have hi : i ∈ U := Finset.min'_mem U _
    exact congrFun (h (U.erase i) (by rw [Finset.card_erase_of_mem hi, hU]; omega)) i
  · simp [hU]

section Finite

variable [Fintype F]

/-- An execution of Algorithm 1, including every oracle-dependent
observation. A value instruction is one additive-oracle query. A stage
instruction runs the explicit cube phase trace followed by Fourier
measurement for every subset of the required size. Its observed vectors
must have nonzero Born amplitude. The next oracle is obtained by
subtracting the already reconstructed, classically known top component.
There is no independently assignable answer or query-count field. -/
inductive Execution (ψ : AddChar F ℂ) : ℕ → ((Fin n → F) → F) → Type _
  | value (f : (Fin n → F) → F) : Execution ψ 0 f
  | stage (d : ℕ) (f : (Fin n → F) → F)
      (answers : Finset (Fin n) → Fin n → F)
      (valid : ∀ S, S.card = d → bvAmplitude ψ (fS f S) (answers S) ≠ 0)
      (tail : Execution ψ d
        (fun x => f x - multilinearEval (topFrom d answers) x)) :
      Execution ψ (d + 1) f

/-- The coefficient table is computed from the query observations in the
execution, using ordinary field arithmetic only. -/
def Execution.output {ψ : AddChar F ℂ} {d : ℕ} {f : (Fin n → F) → F} :
    Execution ψ d f → (Finset (Fin n) → F)
  | .value f => fun U => if U = ∅ then f 0 else 0
  | .stage k _ answers _ tail => topFrom k answers + tail.output

/-- The actual list of original-oracle calls made in one derivative stage.
The pair identifies the derivative subset and its Boolean cube branch. -/
def stageTrace (d : ℕ) : List (Finset (Fin n) × (Fin n → Bool)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard d).toList.flatMap
    (fun S => (cubeTrace S).map (fun b => (S, b)))

/-- Query accounting is derived from the explicit stage trace. -/
theorem stage_trace_length (d : ℕ) :
    (stageTrace (n := n) d).length = 2 ^ d * n.choose d := by
  classical
  simp only [stageTrace, List.length_flatMap, List.length_map, cube_trace_length]
  rw [Finset.sum_map_toList]
  have h : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      2 ^ S.card = 2 ^ d := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_comm]
  rfl

/-- This derived query count counts every phase query in the execution and
the final value query. It cannot be chosen independently of the output. -/
def Execution.queries {ψ : AddChar F ℂ} {d : ℕ} {f : (Fin n → F) → F} :
    Execution ψ d f → ℕ
  | .value _ => 1
  | .stage k _ _ _ tail => (stageTrace (n := n) k).length + tail.queries

omit [Fintype F] in
/-- Multilinear evaluation respects subtraction of coefficient tables. -/
theorem eval_sub (α β : Finset (Fin n) → F) (x : Fin n → F) :
    multilinearEval (α - β) x = multilinearEval α x - multilinearEval β x := by
  simp [multilinearEval, sub_mul, Finset.sum_sub_distrib]

omit [Fintype F] in
/-- At the origin, only the constant coefficient survives. -/
theorem eval_zero (α : Finset (Fin n) → F) :
    multilinearEval α 0 = α ∅ := by
  classical
  unfold multilinearEval
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T _ hT
    have hnonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    obtain ⟨i, hi⟩ := hnonempty
    rw [Finset.prod_eq_zero hi (by rfl), mul_zero]
  · simp

omit [Fintype F] in
/-- Removing the reconstructed degree-`d+1` component lowers the degree. -/
theorem residual_degree (d : ℕ) (α : Finset (Fin n) → F)
    (hdeg : ∀ U, d + 1 < U.card → α U = 0) :
    ∀ U, d < U.card → (α - topFrom d (linearPart α)) U = 0 := by
  rw [topFrom_linearPart]
  intro U hU
  by_cases h : U.card = d + 1
  · simp [h]
  · have hlt : d + 1 < U.card := by omega
    simp [h, hdeg U hlt]

/-- A genuine execution exists for every promised polynomial oracle.
Observed vectors are justified by the nonzero Fourier amplitude, while
the returned coefficient table is computed by `Execution.output`. -/
theorem execution_exists (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (d : ℕ) (α : Finset (Fin n) → F)
    (hdeg : ∀ U, d < U.card → α U = 0)
    (f : (Fin n → F) → F) (hf : ∀ x, f x = multilinearEval α x) :
    ∃ e : Execution ψ d f, e.output = α := by
  induction d generalizing α f with
  | zero =>
    refine ⟨Execution.value f, ?_⟩
    funext U
    change (if U = ∅ then f 0 else 0) = α U
    by_cases hU : U = ∅
    · subst hU
      simp only [ite_true]
      rw [hf 0, eval_zero]
    · rw [ite_eq_right hU, hdeg U (Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hU))]
  | succ d ih =>
    let top := topFrom d (linearPart α)
    let β := α - top
    have hβ : ∀ U, d < U.card → β U = 0 := residual_degree d α hdeg
    have hfβ : ∀ x, f x - multilinearEval top x = multilinearEval β x := by
      intro x
      rw [hf x]
      exact (eval_sub α top x).symm
    obtain ⟨tail, htail⟩ := ih β hβ
      (fun x => f x - multilinearEval top x) hfβ
    have hvalid : ∀ S, S.card = d →
        bvAmplitude ψ (fS f S) (linearPart α S) ≠ 0 := by
      intro S hS
      rw [difference_affine α d hdeg f hf S hS, bv_affine ψ hψ]
      simpa using (ψ.val_isUnit (α S)).ne_zero
    refine ⟨Execution.stage d f (linearPart α) hvalid tail, ?_⟩
    change top + tail.output = α
    rw [htail]
    funext U
    change top U + (α U - top U) = α U
    ring

/-- Every allowed measurement branch of the execution returns the same
true coefficient table. Existence alone would not express exact learning. -/
theorem execution_sound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (d : ℕ) (α : Finset (Fin n) → F)
    (hdeg : ∀ U, d < U.card → α U = 0)
    (f : (Fin n → F) → F) (hf : ∀ x, f x = multilinearEval α x)
    (e : Execution ψ d f) : e.output = α := by
  induction d generalizing α f with
  | zero =>
    cases e with
    | value _ =>
      funext U
      change (if U = ∅ then f 0 else 0) = α U
      by_cases hU : U = ∅
      · subst hU
        simp only [ite_true]
        rw [hf 0, eval_zero]
      · rw [ite_eq_right hU, hdeg U (Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hU))]
  | succ d ih =>
    cases e with
    | stage _ _ answers valid tail =>
      have ha : ∀ S, S.card = d → answers S = linearPart α S := by
        intro S hS
        have h := valid S hS
        rw [difference_affine α d hdeg f hf S hS, bv_affine ψ hψ] at h
        by_contra hne
        simp [hne] at h
      have htop : topFrom d answers = topFrom d (linearPart α) :=
        topFrom_congr d answers (linearPart α) ha
      let β := α - topFrom d answers
      have hβ : ∀ U, d < U.card → β U = 0 := by
        simpa only [β, htop] using residual_degree d α hdeg
      have hfβ : ∀ x, f x - multilinearEval (topFrom d answers) x =
          multilinearEval β x := by
        intro x
        rw [hf x]
        exact (eval_sub α (topFrom d answers) x).symm
      have htail := ih β hβ _ hfβ tail
      change topFrom d answers + tail.output = α
      rw [htail]
      funext U
      change topFrom d answers U + (α U - topFrom d answers U) = α U
      ring

/-- Every execution has exactly the paper's stage-by-stage query count.
The count comes from the cube-query trace and the final value query. -/
theorem execution_queries {ψ : AddChar F ℂ} {d : ℕ}
    {f : (Fin n → F) → F} (e : Execution ψ d f) :
    e.queries = 1 + ∑ k ∈ Finset.range d, 2 ^ k * n.choose k := by
  induction e with
  | value => simp [Execution.queries]
  | stage d f answers valid tail ih =>
    simp only [Execution.queries, stage_trace_length, Finset.sum_range_succ]
    rw [ih]
    omega

/-- Every execution contains at least its final actual value-oracle query. -/
theorem execution_queries_pos {ψ : AddChar F ℂ} {d : ℕ}
    {f : (Fin n → F) → F} (e : Execution ψ d f) : 0 < e.queries := by
  rw [execution_queries]
  omega

/-- A nonconstant, one-variable polynomial is recovered through a real
execution with one Fourier query and one constant-term query. -/
theorem one_variable_execution (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ∃ e : Execution ψ 1 (fun x : Fin 1 → F => x 0),
      (∀ U, e.output U = if U = Finset.univ then 1 else 0) ∧ e.queries = 2 := by
  let α : Finset (Fin 1) → F := fun U => if U = Finset.univ then 1 else 0
  have hdeg : ∀ U, 1 < U.card → α U = 0 := by
    intro U hU
    have hle : U.card ≤ 1 := by simpa using Finset.card_le_univ U
    omega
  have hf : ∀ x : Fin 1 → F, x 0 = multilinearEval α x := by
    intro x
    simp [α, multilinearEval]
  obtain ⟨e, he⟩ := execution_exists ψ hψ 1 α hdeg (fun x => x 0) hf
  refine ⟨e, fun U => congrFun he U, ?_⟩
  simpa using execution_queries e
end Finite

end OracleRepair

open OracleRepair

/-- The fixed recursive learner is parameterized only by its nondegenerate
finite-field Fourier character. Its input/output behavior is the concrete
`Execution` semantics, and its query count is derived from that execution.
There are no independently selectable output or resource fields. -/
structure ExactLearner (n d : ℕ) (F : Type*) [Field F] [Fintype F] where
  /-- Additive character used by the Fourier transforms and phase ancillas. -/
  character : AddChar F ℂ
  /-- Nondegeneracy of the finite-field Fourier pairing. -/
  primitive : character.IsPrimitive

/-- **Theorem 2, arXiv:1105.3310v3.** Over every finite field the fixed
Algorithm-1 learner has an execution on every promised oracle, every allowed
measurement branch returns the true coefficient table, and every execution
uses exactly the displayed number of original-oracle queries. The explicit
polynomial bound is retained for positive dimension. -/
theorem theorem2_exact_learning
    (n d : ℕ) (F : Type*) [Field F] [Fintype F] (hd : 1 ≤ d) :
    ∃ L : ExactLearner n d F,
      ∀ (f : (Fin n → F) → F) (α : Finset (Fin n) → F),
        (∀ U, d < U.card → α U = 0) →
        (∀ x, f x = multilinearEval α x) →
        (∃ e : Execution L.character d f, e.output = α) ∧
        ∀ e : Execution L.character d f,
          e.output = α ∧ e.queries = theorem2QueryCount n d ∧
          (1 ≤ n → e.queries ≤ (d + 1) * 2 ^ (d - 1) * n ^ (d - 1)) := by
  obtain ⟨ψ, hψ⟩ := primitive_character_exists (F := F)
  refine ⟨⟨ψ, hψ⟩, ?_⟩
  intro f α hdeg hf
  refine ⟨execution_exists ψ hψ d α hdeg f hf, ?_⟩
  intro e
  have hcount : e.queries = theorem2QueryCount' n d := execution_queries e
  refine ⟨execution_sound ψ hψ d α hdeg f hf e, ?_, ?_⟩
  · exact hcount.trans (theorem2_query_count_identity n d).symm
  · intro hn
    rw [hcount]
    exact theorem2_query_count_bound n d hd hn

end Qatlib.Papers.Multilinear11.MainResults.MainTheorem
