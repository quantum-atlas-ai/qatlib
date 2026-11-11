/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SubgraphDet26.MainResults.GraphModel
import Qatlib.Papers.SubgraphDet26.MainResults.CertificateSearch
import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# The compressed-oracle lemmas of §3 (arXiv:2609.40263v1)

Paper: Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for Subgraph Detection*,
fixed arXiv:2609.40263v1.

* Lemma 3.3: the compressed-oracle expansion and the marginal identity;
* Lemma 3.4: database support and the binomial moment bound;
* Lemma 3.5: conditioning intertwines the query and the input-independent gates
  (Eqs. (28), (29)), plus the normalization statement;
* Lemma 3.6: progress across a threshold (Eqs. (32), (34));
* Lemma 3.7: the exact conditioning norm below threshold (Eq. (37));
* Lemma 3.8: the boundary-crossing bound (Eq. (38)).

The Frozen library already implements the representation layer
(`SubgraphQuery.CompressOracle`): `bernoulliPmf`,
`bernoulliState`, `decompressGate`, `compressedOracle`, `compressedRunState`,
`joint_run_expansion`, `compressed_run_from_empty`, `compressed_marginal`,
`database_support_bound`, `database_moment_bound`, `compressed_oracle_entry`.
The conditioning layer (`T_C`, `R_C`, `Π_{C,lo}`, `Π_{C,hi}`, `κ_t`, `B_C`) is
defined here for the first time, at paper fidelity.  Of this layer, Eq. (29) of
Lemma 3.5 and Eq. (37) of Lemma 3.7 are proved below; the remaining statements of
Lemmas 3.5, 3.6 and 3.8 (Eqs. (28), the normalization, (32), (34), (38)) depend on
the conditional distribution `μ_{p,C}` and the boundary-crossing expansion, which
are not yet available, and their scaffolds were removed (statements preserved in
the branch history at `161317a85`).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.SubgraphDet26.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-! ## The conditioning map `T_C` and the low/high projectors (Eq. (27), §3.3) -/

/-- `η = √((1−p)/p)`, the likelihood-ratio parameter of Eq. (27). -/
def eta (p : ℝ) : ℝ := Real.sqrt ((1 - p) / p)

/-- Removing the coordinates of `C` from a database. -/
def removeCoord (C : Finset I) (d : I → Bool) : I → Bool :=
  fun j => if j ∈ C then false else d j

/-- The conditioning map `T_C` of Eq. (27): `T_C |S⟩ = (−η)^{|S∩C|} |S \ C⟩`.
It removes the coordinates of `C` from the database, with the likelihood-ratio
weight; it is a partial isometry on the low subspace and may have large norm
elsewhere (as the paper notes). -/
def conditioningMap (C : Finset I) (p : ℝ) : Matrix (I → Bool) (I → Bool) ℂ :=
  fun d S => if d = removeCoord C S then
    (((-(eta p) : ℝ)) : ℂ) ^ (databaseSupport S ∩ C).card else 0

/-- The low projector `Π_{C,lo}`: diagonal on databases with `S ∩ C ∈ L_C`. -/
def lowProjector (low : Finset I → Finset (Finset I)) (C : Finset I) :
    Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.diagonal fun S => if databaseSupport S ∩ C ∈ low C then (1 : ℂ) else 0

/-- The high projector `Π_{C,hi} = I − Π_{C,lo}`. -/
def highProjector (low : Finset I → Finset (Finset I)) (C : Finset I) :
    Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.diagonal fun S => if databaseSupport S ∩ C ∈ low C then (0 : ℂ) else 1

/-- The conditional oracle `R_C` of Eq. (28): on `|j, 1⟩` it applies the phase `−1`
when `j ∈ C` and the compressed single-coordinate query `R_j` when `j ∉ C`; on
`|j, 0⟩` it is the identity.  (Ambient form on the full database register `D`;
the paper states it on `D_C`.) -/
def conditionedOracle (C : Finset I) (p : ℝ) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  fun (((j, b), w), d) (((j', b'), w'), d') =>
    if j = j' ∧ b = b' ∧ w = w' then
      (if b then
        (if j ∈ C then (if d = d' then (-1 : ℂ) else 0)
         else (if ∀ k, k ≠ j → d k = d' k then compressedQueryEntry p (d j) (d' j) else 0))
      else (if d = d' then 1 else 0))
    else 0

/-! ## The compressed state at time `t`, the progress `κ_t`, the boundary operator -/

/-- The compressed state after `t` queries: the first `t` steps of the lifted circuit,
run from `|ψ⟩ ⊗ |∅⟩` under the compressed oracle. -/
def queryPrefixState (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (t : ℕ) : QState (((I × Bool) × W) × (I → Bool)) :=
  Run (compressedOracle p) ((tensorLiftCircuit C).take t)
    (TensorState ψ (Ket (fun _ => false)))

/-- The squared Hilbert-space norm `‖v‖² = Σ_x |v x|²` of a state vector. -/
def l2NormSq {X : Type} [Fintype X] (v : QState X) : ℝ :=
  ∑ x, ‖v x‖ ^ 2

/-- The progress `κ_t` of Eq. (31):
`κ_t = ( (1/|F|) Σ_{C∈F} ‖ T_C Π_{C,hi} |ψ_t⟩ ‖² )^{1/2}`. -/
def kappa (p : ℝ) (F : Finset (Finset I)) (low : Finset I → Finset (Finset I))
    (C : Circuit ((I × Bool) × W)) (init : QState ((I × Bool) × W)) (t : ℕ) : ℝ :=
  Real.sqrt ((1 / (F.card : ℝ)) *
    ∑ C₀ ∈ F, l2NormSq (ApplyGate
      (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (conditioningMap C₀ p))
      (ApplyGate
        (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (highProjector low C₀))
        (queryPrefixState p C init t))))

/-- The boundary crossing operator `B_C = T_C [Π_{C,hi}, R]` of Eq. (33). -/
def boundaryOp (C : Finset I) (p : ℝ) (low : Finset I → Finset (Finset I)) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (conditioningMap C p) *
    (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (highProjector low C) *
        compressedOracle p -
      compressedOracle p *
        TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (highProjector low C))

/-- The database size operator `N`. -/
def databaseSizeOp : Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.diagonal fun d => (databaseCard d : ℂ)

/-- The binomial moment operator `C(N, i)`. -/
def binomOp (i : ℕ) : Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.diagonal fun d => (Nat.choose (databaseCard d) i : ℂ)

/-- The real expectation `⟨ψ| A |ψ⟩` (real part of the sesquilinear form). -/
def expectationRE {X : Type} [Fintype X] (A : Matrix X X ℂ) (ψ : QState X) : ℝ :=
  (∑ x, star (ψ x) * ApplyGate A ψ x).re

/-! ## Lemma 3.3 (bridges to the Frozen representation layer)

Paper: Lemma 3.3 on p. 16, fixed arXiv:2609.40263v1.  The Frozen theorems
`joint_run_expansion`, `compressed_run_from_empty` and `compressed_marginal`
implement the content. -/

/-- Lemma 3.3, expansion form: the compressed run is the sum over inputs `x` of the
Bernoulli amplitude times the workspace run, with the decompression map `S†` on the
database register.  Reused FQNs:
`SubgraphQuery.CompressOracle.compressed_run_from_empty`
and `...joint_run_expansion`. -/
theorem lemma33_compressed_oracle_expansion (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q : (I × Bool) × W) (d : I → Bool) :
    compressedRunState p C ψ (q,d)
      = ∑ x : I → Bool, (decompressGate (I := I) p)ᴴ d x * bernoulliState p x *
          Run (workspacePhaseOracle x) C ψ q := by
  rw [compressedRunState, compressed_run_from_empty p hp0 hp1]
  have hslice :
      ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
          (decompressGate (I := I) p)ᴴ)
          (Run jointPhaseOracle (tensorLiftCircuit C) (TensorState ψ (bernoulliState p))) (q,d)
        = ApplyGate (decompressGate (I := I) p)ᴴ
            (fun x => Run jointPhaseOracle (tensorLiftCircuit C)
              (TensorState ψ (bernoulliState p)) (q,x)) d := by
    simp [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply]
  rw [hslice]
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [joint_run_expansion p C ψ q x]
  ring

/-- Lemma 3.3, marginal form: tracing out the database recovers the Bernoulli average
of the workspace run.  This is exactly the Frozen theorem
`SubgraphQuery.CompressOracle.compressed_marginal`. -/
theorem lemma33_compressed_marginal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q q' : (I × Bool) × W) :
    (∑ d : I → Bool,
        compressedRunState p C ψ (q,d) * star (compressedRunState p C ψ (q',d)))
      = ∑ x : I → Bool, bernoulliPmf p x *
          Run (workspacePhaseOracle x) C ψ q * star (Run (workspacePhaseOracle x) C ψ q') :=
  compressed_marginal p hp0 hp1 C ψ q q'

/-! ## Lemma 3.4 (bridges to the Frozen representation layer)

Paper: Lemma 3.4 on p. 17, Eq. (21), fixed arXiv:2609.40263v1.  The Frozen theorems
`database_support_bound` and `database_moment_bound` implement the content. -/

/-- Lemma 3.4, support form: after `t` queries the compressed state is supported on
databases of size at most `t`.  Reused FQN:
`SubgraphQuery.CompressOracle.database_support_bound`. -/
theorem lemma34_database_support (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (t : ℕ)
    (ht : QueryCount C ≤ t) (q : (I × Bool) × W) (d : I → Bool)
    (hd : t < databaseCard d) : compressedRunState p C ψ (q,d) = 0 :=
  database_support_bound p hp0 hp1 C ψ t ht q d hd

/-- Lemma 3.4, moment form (Eq. (21)): the `i`-th binomial moment of the database
size is at most `C(t,i) (2√(p(1−p)))^i`.  Reused FQN:
`SubgraphQuery.CompressOracle.database_moment_bound`. -/
theorem lemma34_database_moment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) (i t : ℕ)
    (ht : QueryCount C ≤ t) :
    (∑ q : (I × Bool) × W, ∑ d : I → Bool,
        (Nat.choose (databaseCard d) i : ℝ) * ‖compressedRunState p C ψ (q,d)‖ ^ 2)
      ≤ (Nat.choose t i : ℝ) * (2 * Real.sqrt (p * (1 - p))) ^ i :=
  database_moment_bound p hp0 hp1 C hC ψ hψ i t ht

/-! ## Lemma 3.5: conditioning the compressed computation

Paper: Lemma 3.5 on p. 19, Eqs. (28) and (29), fixed arXiv:2609.40263v1.
Eq. (28) (the query intertwining `(I_W ⊗ T_C) R = R_C (I_W ⊗ T_C)`) and the
normalization statement are not proved here: they need the single-coordinate
identity `L R_j = −L` assembled into the composite matrix identity and the
conditional distribution `μ_{p,C}` respectively; the scaffolds were removed.  -/

/-- Lemma 3.5, Eq. (29): `(I_W ⊗ T_C)(V ⊗ I_D) = (V ⊗ I_{D_C})(I_W ⊗ T_C)` for every
unitary `V` on the workspace that is independent of the input.
Proof: both sides are `V ⊗ T_C` by Kronecker multiplicativity
(`tensorGate_mul`, `Matrix.one_mul`, `Matrix.mul_one`); the identity `I_{D_C}` is
represented here by the ambient identity, which agrees on the image of `T_C`. -/
theorem lemma35_gate_intertwining (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : Finset I)
    (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) :
    TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (conditioningMap C p) *
        TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ)
      = TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ) *
        TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (conditioningMap C p) := by
  rw [tensorGate_mul, tensorGate_mul]
  simp [Matrix.one_mul, Matrix.mul_one]

/-! ## Lemma 3.6: progress across a threshold

Paper: Lemma 3.6 on p. 20, Eqs. (32) and (34), fixed arXiv:2609.40263v1.  Both
statements need the success-probability decomposition of Eq. (35) and the
intertwined-query identity of Eq. (36), which depend on the unproved parts of
Lemma 3.5; the scaffolds were removed (statements preserved in the branch history
at `161317a85`).  -/

/-! ## Lemma 3.7: the conditioning norm below threshold

Paper: Lemma 3.7 on p. 21, Eq. (37), fixed arXiv:2609.40263v1. -/

/-- Lemma 3.7, Eq. (37): `‖T_C Π_{C,lo}‖² = Σ_{A ∈ L_C} ((1−p)/p)^{|A|}`, for a low
family `L_C` consisting of subsets of `C` (in the paper `L_C ⊆ 2^C`; without this
hypothesis the identity fails for families containing sets outside `C`).
Proof: `T_C Π_{C,lo}` maps `|S⟩` to `(−η)^{|S∩C|}|S \ C⟩`, so all columns with the
same `S \ C` pile up on one basis vector and
`M Mᴴ = (Σ_{A∈L_C} ((1−p)/p)^{|A|}) · Π_{\{d : d|_C = 0\}}` is diagonal; conclude by
`Matrix.l2_opNorm_conjTranspose_mul_self` and `Matrix.l2_opNorm_diagonal`. -/
theorem lemma37_conditioning_norm_below_threshold
    (C : Finset I) (low : Finset I → Finset (Finset I)) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hlow : ∀ A ∈ low C, A ⊆ C) :
    ‖conditioningMap C p * lowProjector low C‖ ^ 2
      = ∑ A ∈ low C, ((1 - p) / p) ^ A.card := by
  have hrp : 0 < (1 - p) / p := by positivity
  have he2 : (eta p) ^ 2 = (1 - p) / p := by
    simp only [eta, Real.sq_sqrt (by linarith : 0 ≤ (1 - p) / p)]
  -- the entries of `M := conditioningMap C p * lowProjector low C`
  have hentry : ∀ (d S : I → Bool),
      (conditioningMap C p * lowProjector low C) d S =
        if removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
        then ((-(eta p) : ℝ) : ℂ) ^ (databaseSupport S ∩ C).card else 0 := by
    intro d S
    have hL : (lowProjector low C) S S =
        if databaseSupport S ∩ C ∈ low C then (1 : ℂ) else 0 := by
      simp [lowProjector, Matrix.diagonal_apply]
    have hL0 : ∀ S' : I → Bool, S' ≠ S → (lowProjector low C) S' S = 0 := by
      intro S' hS'
      simp [lowProjector, Matrix.diagonal_apply, hS']
    rw [Matrix.mul_apply,
      Finset.sum_eq_single S (fun b _ hb => by rw [hL0 b hb, mul_zero])
        (fun h => absurd (Finset.mem_univ S) h), hL]
    by_cases hmem : databaseSupport S ∩ C ∈ low C
    · rw [if_pos hmem, mul_one]
      show (if d = removeCoord C S
          then (((-(eta p) : ℝ)) : ℂ) ^ (databaseSupport S ∩ C).card else 0) = _
      by_cases hd : removeCoord C S = d
      · rw [if_pos hd.symm, if_pos ⟨hd, hmem⟩]
      · rw [if_neg (fun h => hd h.symm), if_neg (fun h => hd h.1)]
    · rw [if_neg hmem, mul_zero, if_neg (fun h => hmem h.2)]
  -- the square of a real entry, as a real power of `(1-p)/p`
  have hsq : ∀ n : ℕ,
      (((-(eta p) : ℝ) : ℂ) ^ n) * (star (((-(eta p) : ℝ) : ℂ) ^ n))
        = (((1 - p) / p : ℝ) : ℂ) ^ n := by
    intro n
    have hreal : ((-(eta p) : ℝ) ^ n) * ((-(eta p) : ℝ) ^ n)
        = ((1 - p) / p) ^ n := by
      rw [← pow_add, ← two_mul, pow_mul, neg_sq, he2]
    have hstar : star (((-(eta p) : ℝ) : ℂ) ^ n) = (((-(eta p) : ℝ) : ℂ) ^ n) := by
      show starRingEnd ℂ _ = _
      rw [map_pow, Complex.conj_ofReal]
    rw [hstar, ← Complex.ofReal_pow, ← Complex.ofReal_mul, hreal, Complex.ofReal_pow]
  -- `M Mᴴ` is the diagonal matrix with entry `S₀` on databases that vanish on `C`
  have hdiag : (conditioningMap C p * lowProjector low C) *
      (conditioningMap C p * lowProjector low C)ᴴ
      = Matrix.diagonal (fun d : I → Bool =>
          if (∀ j ∈ C, d j = false) then
            Complex.ofReal (∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ)) else 0) := by
    ext d d'
    by_cases hdd : d = d'
    · subst hdd
      rw [Matrix.diagonal_apply_eq]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hentry]
      have hterm : ∀ S : I → Bool,
          ((if removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
              then ((-(eta p) : ℝ) : ℂ) ^ (databaseSupport S ∩ C).card else 0) *
            star (if removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
              then ((-(eta p) : ℝ) : ℂ) ^ (databaseSupport S ∩ C).card else 0)) =
            (if removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
              then (((1 - p) / p : ℝ) : ℂ) ^ (databaseSupport S ∩ C).card else 0) := by
        intro S
        by_cases hS : removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
        · simp only [if_pos hS, hsq]
        · simp [hS]
      rw [Finset.sum_congr rfl fun S _ => hterm S]
      by_cases hd : ∀ j ∈ C, d j = false
      · rw [if_pos hd]
        -- the bijection `S ↦ databaseSupport S ∩ C` onto `low C`
        have hfil : ∑ S ∈ Finset.univ.filter
            (fun S => removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C),
            (((1 - p) / p : ℝ) : ℂ) ^ (databaseSupport S ∩ C).card
            = ∑ A ∈ low C, (((1 - p) / p : ℝ) : ℂ) ^ (A.card : ℕ) := by
          have hinj : ∀ S₁ ∈ Finset.univ.filter
                (fun S => removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C),
              ∀ S₂ ∈ Finset.univ.filter
                (fun S => removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C),
              databaseSupport S₁ ∩ C = databaseSupport S₂ ∩ C → S₁ = S₂ := by
            intro S₁ h₁ S₂ h₂ hφ
            have e1 : removeCoord C S₁ = d := (Finset.mem_filter.mp h₁).2.1
            have e2 : removeCoord C S₂ = d := (Finset.mem_filter.mp h₂).2.1
            funext j
            by_cases hj : j ∈ C
            · have key : (S₁ j = true) ↔ (S₂ j = true) := by
                constructor <;> intro h
                · have hm : j ∈ databaseSupport S₁ ∩ C := by
                    simp [databaseSupport, Finset.mem_filter, Finset.mem_inter, hj, h]
                  rw [hφ] at hm
                  simpa [databaseSupport, Finset.mem_filter, Finset.mem_inter, hj] using hm
                · have hm : j ∈ databaseSupport S₂ ∩ C := by
                    simp [databaseSupport, Finset.mem_filter, Finset.mem_inter, hj, h]
                  rw [← hφ] at hm
                  simpa [databaseSupport, Finset.mem_filter, Finset.mem_inter, hj] using hm
              revert key
              cases S₁ j <;> cases S₂ j <;> simp_all
            · have j1 : S₁ j = d j := by
                simpa [removeCoord, hj] using congrFun e1 j
              have j2 : S₂ j = d j := by
                simpa [removeCoord, hj] using congrFun e2 j
              rw [j1, j2]
          refine Finset.sum_bij (fun S _ => databaseSupport S ∩ C) ?_ ?_ ?_ ?_
          · intro S hS
            exact (Finset.mem_filter.mp hS).2.2
          · exact hinj
          · intro A hA
            have hdb : (databaseSupport (fun j => if j ∈ A then true else d j)) ∩ C = A := by
              ext j
              simp only [databaseSupport, Finset.mem_filter, Finset.mem_inter,
                Finset.mem_univ, true_and]
              by_cases hj : j ∈ C
              · simp only [hj]
                by_cases hja : j ∈ A <;> simp [hja, hd j hj]
              · by_cases hja : j ∈ A
                · exact absurd (hlow A hA hja) hj
                · simp [hja, hj]
            have hrc : removeCoord C (fun j => if j ∈ A then true else d j) = d := by
              funext j
              by_cases hj : j ∈ C
              · simp only [removeCoord, if_pos hj, hd j hj]
              · by_cases hja : j ∈ A
                · exact absurd (hlow A hA hja) hj
                · simp only [removeCoord, if_neg hj, hja, if_false]
            exact ⟨fun j => if j ∈ A then true else d j,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrc, hdb.symm ▸ hA⟩, hdb⟩
          · intro S hS
            rfl
        rw [← Finset.sum_filter, hfil, Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun A _ => (Complex.ofReal_pow _ _).symm
      · rw [if_neg hd]
        push_neg at hd
        obtain ⟨j₀, hj₀, hdj⟩ := hd
        have hnone : ∀ S : I → Bool,
            ¬(removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C) := by
          intro S hS
          have h1 : (removeCoord C S) j₀ = false := by simp [removeCoord, hj₀]
          rw [hS.1] at h1
          exact absurd h1 hdj
        simp [hnone]
    · simp only [Matrix.diagonal_apply]
      rw [if_neg hdd]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hentry]
      refine Finset.sum_eq_zero fun S _ => ?_
      by_cases h1 : removeCoord C S = d ∧ databaseSupport S ∩ C ∈ low C
      · rw [if_pos h1]
        by_cases h2 : removeCoord C S = d' ∧ databaseSupport S ∩ C ∈ low C
        · rw [if_pos h2]
          exact absurd ((h2.1.symm.trans h1.1).symm) hdd
        · rw [if_neg h2]; simp
      · rw [if_neg h1]; simp
  -- take operator norms
  have hS0nn : 0 ≤ ∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ) :=
    Finset.sum_nonneg fun A _ => pow_nonneg (le_of_lt hrp) _
  have hM2 : ‖conditioningMap C p * lowProjector low C‖ ^ 2
      = ‖(conditioningMap C p * lowProjector low C) *
          (conditioningMap C p * lowProjector low C)ᴴ‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self
      ((conditioningMap C p * lowProjector low C)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, ← sq] at h
    exact h.symm
  rw [hM2, hdiag, Matrix.l2_opNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg hS0nn).mpr fun d => ?_) ?_
  · by_cases hd : ∀ j ∈ C, d j = false
    · rw [if_pos hd]
      have hEq : ‖(Complex.ofReal (∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ)))‖
          = ∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ) := by
        exact_mod_cast abs_of_nonneg hS0nn
      rw [hEq]
    · rw [if_neg hd, norm_zero]
      exact hS0nn
  · have hle := norm_le_pi_norm
      (fun d : I → Bool =>
        if (∀ j ∈ C, d j = false)
        then Complex.ofReal (∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ)) else 0)
      (fun _ => false)
    rw [if_pos (by simp)] at hle
    have hEq : ‖(Complex.ofReal (∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ)))‖
        = ∑ A ∈ low C, ((1 - p) / p) ^ (A.card : ℕ) := by
      exact_mod_cast abs_of_nonneg hS0nn
    rwa [hEq] at hle

/-! ## Lemma 3.8: the boundary crossing bound

Paper: Lemma 3.8 on p. 22, Eq. (38), fixed arXiv:2609.40263v1.  The proof needs the
coefficient expansion of Eq. (39) and the crossing-pair analysis, which are not in
the Frozen library; the scaffold was removed (statement preserved in the branch
history at `161317a85`).  -/

end Qatlib.Papers.SubgraphDet26.MainResults
