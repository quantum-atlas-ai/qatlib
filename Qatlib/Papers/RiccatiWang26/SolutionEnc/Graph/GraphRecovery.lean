/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# GraphRecovery — graph projectors and upper-block recovery

RiccatiWang26, arXiv:2609.37207v1.
Covers: Theorem 3.2 (p. 13), Lemma 3.3 (p. 13), Lemma 3.6 (p. 22), Lemma 3.8 (p. 23),
Lemma D.3 (p. 78), Theorem E.2 (p. 84), Corollary E.3 (p. 84), Lemma F.1 (p. 95).

The source's recovery identity is Eq. (1.1)/(3.9)/(D.3):

  `P = (E₂* E) (E₁* E)⁺`  and  `(E₂* E) = P (E₁* E)`,  `(E₁* E) [I; P] = I`.

Mathlib has no matrix pseudoinverse, so `(·)⁺` is represented by the four
Moore–Penrose equations (`IsMPPseudoinverse`).  The paper uses "full row rank implies
the pseudoinverse is a right inverse"; the proof below derives `A A⁺ = I` from the
Moore–Penrose equations and surjectivity, so no additional assumption is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Graph

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Elementary block identities -/

/-- `E₁* [I; P] = I`. -/
lemma E1_adj_mul_graph (P : Sq n) : (E1 n)ᴴ * graph P = 1 := by
  ext i j
  simp [E1, graph, blockCol, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

/-- `E₂* [I; P] = P`. -/
lemma E2_adj_mul_graph (P : Sq n) : (E2 n)ᴴ * graph P = P := by
  ext i j
  simp [E2, graph, blockCol, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply]

/-- `E₁* E₁ = I`. -/
lemma E1_adj_mul_E1 : (E1 n)ᴴ * E1 n = 1 := by
  ext i j
  simp [E1, blockCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Matrix.one_apply, eq_comm]

/-- Matrices are equal when their `mulVec` actions agree. -/
lemma matrix_ext_of_mulVec_eq {m : Type*} [Fintype m] {l : Type*} [Fintype l] [DecidableEq l]
    (A B : Matrix m l ℂ) (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-! ## Moore–Penrose right inverse -/

/-- A Moore–Penrose pseudoinverse of a full-row-rank matrix is a right inverse.
Source: the sentence after (1.1) and after (3.9). -/
lemma mp_mul_eq_one {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {A : Matrix m l ℂ} {P : Matrix l m ℂ}
    (hMP : IsMPPseudoinverse A P) (hA : FullRowRank A) : A * P = 1 := by
  have hidem : (A * P) * (A * P) = A * P := by
    calc (A * P) * (A * P) = A * ((P * A) * P) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = A * P := by rw [hMP.2.1]
  have hsurj : Function.Surjective (A * P).mulVec := by
    intro v
    obtain ⟨w, hw⟩ := hA v
    refine ⟨A *ᵥ w, ?_⟩
    rw [(Matrix.mulVec_mulVec (A *ᵥ w) A P).symm, Matrix.mulVec_mulVec w P A,
      Matrix.mulVec_mulVec w A (P * A), ← Matrix.mul_assoc, hMP.1]
    exact hw
  refine matrix_ext_of_mulVec_eq _ _ (fun v => ?_)
  rw [Matrix.one_mulVec]
  obtain ⟨w, hw⟩ := hsurj v
  rw [← hw]
  calc (A * P) *ᵥ ((A * P) *ᵥ w) = ((A * P) * (A * P)) *ᵥ w :=
        Matrix.mulVec_mulVec w (A * P) (A * P)
    _ = (A * P) *ᵥ w := by rw [hidem]

/-- Full row rank of the upper block row, derived from the graph property. -/
lemma upper_blockrow_fullRowRank
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ)
    (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v))) :
    FullRowRank ((E1 n)ᴴ * E) := by
  intro w
  refine ⟨graph P *ᵥ w, ?_⟩
  rw [Matrix.mulVec_mulVec w ((E1 n)ᴴ * E) (graph P), Matrix.mul_assoc, hfix,
    E1_adj_mul_graph, Matrix.one_mulVec]

/-- The three recovery identities of Eq. (3.9), given the graph-projector property. -/
theorem graph_projector_identities
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hproj : E * E = E) (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * E) Aplus) :
    ((E1 n)ᴴ * E) * graph P = 1 ∧
      (E2 n)ᴴ * E = P * ((E1 n)ᴴ * E) ∧
      P = ((E2 n)ᴴ * E) * Aplus := by
  have h1 : ((E1 n)ᴴ * E) * graph P = 1 := by
    rw [Matrix.mul_assoc, hfix, E1_adj_mul_graph]
  have h2 : (E2 n)ᴴ * E = P * ((E1 n)ᴴ * E) := by
    refine matrix_ext_of_mulVec_eq _ _ (fun v => ?_)
    have hmv : E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)) := hact v
    calc ((E2 n)ᴴ * E) *ᵥ v = (E2 n)ᴴ *ᵥ (E *ᵥ v) :=
          (Matrix.mulVec_mulVec v (E2 n)ᴴ E).symm
      _ = (E2 n)ᴴ *ᵥ (graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v))) := by
          conv_lhs => rw [hmv]
      _ = ((E2 n)ᴴ * graph P) *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)) :=
          Matrix.mulVec_mulVec ((E1 n)ᴴ *ᵥ (E *ᵥ v)) (E2 n)ᴴ (graph P)
      _ = P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)) := by rw [E2_adj_mul_graph]
      _ = P *ᵥ (((E1 n)ᴴ * E) *ᵥ v) := by rw [Matrix.mulVec_mulVec v (E1 n)ᴴ E]
      _ = (P * ((E1 n)ᴴ * E)) *ᵥ v :=
          Matrix.mulVec_mulVec v P ((E1 n)ᴴ * E)
  have h3 : P = ((E2 n)ᴴ * E) * Aplus := by
    have hAA : ((E1 n)ᴴ * E) * Aplus = 1 :=
      mp_mul_eq_one hMP (upper_blockrow_fullRowRank P E hfix hact)
    calc P = P * 1 := (Matrix.mul_one P).symm
      _ = P * (((E1 n)ᴴ * E) * Aplus) := by rw [hAA]
      _ = (P * ((E1 n)ᴴ * E)) * Aplus := (Matrix.mul_assoc _ _ _).symm
      _ = ((E2 n)ᴴ * E) * Aplus := by rw [← h2]
  exact ⟨h1, h2, h3⟩

/-- Range of a graph projector equals the range of the graph it fixes. -/
lemma range_eq_graph_range
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ)
    (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v))) :
    LinearMap.range E.mulVecLin = LinearMap.range (graph P).mulVecLin := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_range] at hv ⊢
    obtain ⟨w, hw⟩ := hv
    exact ⟨(E1 n)ᴴ *ᵥ (E *ᵥ w), by rw [← hw]; exact (hact w).symm⟩
  · intro v hv
    rw [LinearMap.mem_range] at hv ⊢
    obtain ⟨w, hw⟩ := hv
    refine ⟨graph P *ᵥ w, ?_⟩
    rw [← hw]
    change E *ᵥ (graph P *ᵥ w) = graph P *ᵥ w
    rw [Matrix.mulVec_mulVec w E (graph P), hfix]

/-! ## Claim statements -/

/-- An idempotent matrix acts as the identity on its range. -/
lemma idempotent_mulVec_idem (E : Matrix (Sum n n) (Sum n n) ℂ) (hE : E * E = E)
    (v : Sum n n → ℂ) : E *ᵥ (E *ᵥ v) = E *ᵥ v := by
  rw [Matrix.mulVec_mulVec, hE]

/-- The complementary matrix `1 - E` of an idempotent is idempotent. -/
lemma one_sub_idempotent (E : Matrix (Sum n n) (Sum n n) ℂ) (hE : E * E = E) :
    (1 - E) * (1 - E) = 1 - E := by
  calc (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
    _ = 1 - E := by rw [hE]; abel

/-- An idempotent is orthogonal to its complement: `E (1 - E) = 0`. -/
lemma idempotent_mul_complement (E : Matrix (Sum n n) (Sum n n) ℂ) (hE : E * E = E) :
    E * (1 - E) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hE]
  exact sub_self E

/-- The graph embedding `[I; P]` has full column rank: the upper block row `E₁*` is a left
inverse (Eq. (3.9)). -/
lemma graph_fullColumnRank (P : Sq n) : FullColumnRank (graph P) := by
  intro a b hab
  have h := congrArg (fun w => (E1 n)ᴴ *ᵥ w) hab
  simpa [Matrix.mulVec_mulVec, E1_adj_mul_graph] using h

/-- RiccatiWang26, Theorem 3.2 (p. 13), Eq. (3.7)–(3.8), algebraic core.  For an idempotent
`E` that fixes the graph `[I; P]`, the graph columns are fixed pointwise, `1 - E` is the
complementary idempotent, `E(1 - E) = 0`, and `[I; P]` has full column rank.  These are the
identities of (3.8) that the decaying-graph construction uses; the paper's analytic inputs
(the branch identity `Π₊e^{tH}Π₋ = 0` and the identity `W(t) = [I;P(t)]Y(t)` of Lemma D.1)
enter through the hypotheses `hproj`/`hfix`, which the Riesz functional calculus supplies. -/
theorem theorem_3_2_decaying_graph_projector
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ)
    (hproj : E * E = E) (hfix : E * graph P = graph P) :
    (∀ v, E *ᵥ (graph P *ᵥ v) = graph P *ᵥ v) ∧
      (1 - E) * (1 - E) = 1 - E ∧ E * (1 - E) = 0 ∧
      FullColumnRank (graph P) := by
  refine ⟨fun v => ?_, one_sub_idempotent E hproj, idempotent_mul_complement E hproj,
    graph_fullColumnRank P⟩
  rw [Matrix.mulVec_mulVec, hfix]

/-- RiccatiWang26, Lemma 3.3 (p. 13), Eq. (3.9).  Direct projector-block recovery:
under the assumptions of Theorem 3.2, the upper block row `E₁*E(t)` is a left inverse of
`[I;P(t)]`, the lower block row is `P(t)` times the upper one, and `P(t)` is recovered by
the upper-block pseudoinverse.  Proof expands the source's (1.1). -/
theorem lemma_3_3_direct_recovery
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hproj : E * E = E) (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * E) Aplus) :
    ((E1 n)ᴴ * E) * graph P = 1 ∧
      (E2 n)ᴴ * E = P * ((E1 n)ᴴ * E) ∧
      P = ((E2 n)ᴴ * E) * Aplus :=
  graph_projector_identities P E Aplus hproj hfix hact hMP

/-- RiccatiWang26, Lemma 3.6 (p. 22), Eq. (3.22)–(3.23).  For the CARE Hamiltonian, the
stable Riesz projector `Π₋` is idempotent, spans the graph `[I;X]` of the stabilizing
solution, its upper block row has full row rank, and it recovers `X` by (3.23).

The spectral fact that the stable Riesz projector has exactly this range is the source's
Hamiltonian spectral splitting (Appendix B); it enters as `hfix`/`hact`. -/
theorem lemma_3_6_care_graph_projector
    (A G Q X : Sq n)
    (Pim : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hCARE : StabilizingCare A G Q X)
    (hPim : Pim * Pim = Pim)
    (hfix : Pim * graph X = graph X)
    (hact : ∀ v, Pim *ᵥ v = graph X *ᵥ ((E1 n)ᴴ *ᵥ (Pim *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * Pim) Aplus) :
    Pim * Pim = Pim ∧
      LinearMap.range Pim.mulVecLin = LinearMap.range (graph X).mulVecLin ∧
      FullRowRank ((E1 n)ᴴ * Pim) ∧
      X = ((E2 n)ᴴ * Pim) * Aplus := by
  have h := graph_projector_identities X Pim Aplus hPim hfix hact hMP
  exact ⟨hPim, range_eq_graph_range X Pim hfix hact,
    upper_blockrow_fullRowRank X Pim hfix hact, h.2.2⟩

/-- RiccatiWang26, Lemma 3.8 (p. 23), Eq. (3.29)–(3.30).  Same statement for the DARE
pencil projector `Π<`; the source notes the conclusion persists when the complementary
subspace contains infinite modes, which is why no invertibility of `A` or `L` is assumed
here (contrast Lemma B.13). -/
theorem lemma_3_8_dare_graph_projector
    (A G Q X : Sq n)
    (Pil : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hDARE : StabilizingDare A G Q X)
    (hPil : Pil * Pil = Pil)
    (hfix : Pil * graph X = graph X)
    (hact : ∀ v, Pil *ᵥ v = graph X *ᵥ ((E1 n)ᴴ *ᵥ (Pil *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * Pil) Aplus) :
    Pil * Pil = Pil ∧
      LinearMap.range Pil.mulVecLin = LinearMap.range (graph X).mulVecLin ∧
      FullRowRank ((E1 n)ᴴ * Pil) ∧
      X = ((E2 n)ᴴ * Pil) * Aplus := by
  have h := graph_projector_identities X Pil Aplus hPil hfix hact hMP
  exact ⟨hPil, range_eq_graph_range X Pil hfix hact,
    upper_blockrow_fullRowRank X Pil hfix hact, h.2.2⟩

/-- RiccatiWang26, Lemma D.3 (p. 78), Eq. (D.3), recovery part.  For an idempotent `E` with
`E [I;P] = [I;P]`, the upper block row `E₁*E` is a left inverse of `[I;P]`, the lower block row
is `P` times the upper one, `P` is recovered by the upper-block pseudoinverse, and the upper
block row has full row rank.  The paper's additional norm estimate
`‖(E₁*E)⁺‖ ≤ √(1 + ‖P‖²)` concerns the minimum-norm pseudoinverse (`IsMPPseudoinverse` fixes
the pseudoinverse only up to the Moore–Penrose equations, not its norm) and is not available
from the algebraic hypotheses here. -/
theorem lemma_D_3_upper_block_inverse_bound
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hproj : E * E = E) (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * E) Aplus) :
    ((E1 n)ᴴ * E) * graph P = 1 ∧
      (E2 n)ᴴ * E = P * ((E1 n)ᴴ * E) ∧
      P = ((E2 n)ᴴ * E) * Aplus ∧
      FullRowRank ((E1 n)ᴴ * E) := by
  have h := graph_projector_identities P E Aplus hproj hfix hact hMP
  exact ⟨h.1, h.2.1, h.2.2, upper_blockrow_fullRowRank P E hfix hact⟩

/-- Two-sided inverse powers multiply to one, the algebraic fact behind the `S_F^k`/`S_F^{-k}`
pair in Theorem E.2. -/
lemma pow_mul_pow_of_mul_eq_one (S T : Matrix (Sum n n) (Sum n n) ℂ)
    (hST : S * T = 1) (hTS : T * S = 1) (k : ℕ) : S ^ k * T ^ k = 1 := by
  let u : Units (Matrix (Sum n n) (Sum n n) ℂ) := ⟨S, T, hST, hTS⟩
  have h := Units.mul_inv (u ^ k)
  simpa [u, Units.val_pow_eq_pow_val] using h

/-- RiccatiWang26, Theorem E.2 (p. 84), algebraic core.  For an idempotent `E_k` that fixes the
graph `[I; P_k]`, the graph columns are fixed pointwise, the complement is idempotent, and
`[I;P_k]` has full column rank.  Additionally, when `SFinv` is a two-sided inverse of the lift
`S_F`, the powers `S_F^k` and `SFinv^k` multiply to the identity — the identity that makes the
`S_F^k ... SFinv^k` correction in (E.4) a well-defined decaying projector.  The paper's Riesz
splitting of `S_F` supplies `hproj`/`hfix`. -/
theorem theorem_E_2_decaying_graph_projector
    (SF SFinv : Matrix (Sum n n) (Sum n n) ℂ) (P : ℕ → Sq n) (k : ℕ)
    (Ek : Matrix (Sum n n) (Sum n n) ℂ)
    (hST : SF * SFinv = 1) (hTS : SFinv * SF = 1)
    (hproj : Ek * Ek = Ek) (hfix : Ek * graph (P k) = graph (P k)) :
    (∀ v, Ek *ᵥ (graph (P k) *ᵥ v) = graph (P k) *ᵥ v) ∧
      (1 - Ek) * (1 - Ek) = 1 - Ek ∧ Ek * (1 - Ek) = 0 ∧
      SF ^ k * SFinv ^ k = 1 ∧ FullColumnRank (graph (P k)) := by
  refine ⟨fun v => ?_, one_sub_idempotent Ek hproj, idempotent_mul_complement Ek hproj,
    pow_mul_pow_of_mul_eq_one SF SFinv hST hTS k, graph_fullColumnRank (P k)⟩
  rw [Matrix.mulVec_mulVec, hfix]

/-- RiccatiWang26, Corollary E.3 (p. 84), Eq. (E.5), recovery part.  Direct recovery of a
finite iterate: `(E₁*E_k)[Iₙ;P_k] = Iₙ`, `E₂*E_k = P_k (E₁*E_k)`, `P_k = (E₂*E_k)(E₁*E_k)⁺`,
and `E₁*E_k` has full row rank.  The paper's pseudoinverse norm estimate is the D.3 estimate
recorded there. -/
theorem corollary_E_3_direct_recovery
    (P : Sq n) (E : Matrix (Sum n n) (Sum n n) ℂ) (Aplus : Matrix (Sum n n) n ℂ)
    (hproj : E * E = E) (hfix : E * graph P = graph P)
    (hact : ∀ v, E *ᵥ v = graph P *ᵥ ((E1 n)ᴴ *ᵥ (E *ᵥ v)))
    (hMP : IsMPPseudoinverse ((E1 n)ᴴ * E) Aplus) :
    ((E1 n)ᴴ * E) * graph P = 1 ∧
      (E2 n)ᴴ * E = P * ((E1 n)ᴴ * E) ∧
      P = ((E2 n)ᴴ * E) * Aplus ∧
      FullRowRank ((E1 n)ᴴ * E) :=
  lemma_D_3_upper_block_inverse_bound P E Aplus hproj hfix hact hMP

/-- RiccatiWang26, Lemma F.1 (p. 95), Eq. (F.1).  Limit of the CARE decaying graph
projector: if `Π₋R₀` has full column rank, then
`Π₋ + e^{-tH} Π₊ R₀ (Π₋R₀)⁺ e^{tH} Π₋ → Π₋` in operator norm as `t → ∞` (the RR and
DARE statements are the same decay for the powers `S_F^k` and the unit-disk pencil).

Source proof (p. 95): write `H` in the basis where `Π±` are the half-plane projectors;
the unstable part grows like `e^{-tH}Π₊`, and the stable part `e^{tH}Π₋` decays, so the
second summand tends to zero.  The analytic decay hypothesis is exposed as `hdecay`.
Scope note: the theorem is conditional on `hdecay`; deriving matrix-exponential
norm decay on spectral subspaces is outside the scope of this file. A bound of
the form `‖e^{tH}Π₋‖ ≤ C e^{-ct}` relates this hypothesis to the spectral gap. -/
theorem lemma_F_1_limits
    (H : Matrix (Sum n n) (Sum n n) ℂ)
    (Pip Pim : Matrix (Sum n n) (Sum n n) ℂ)
    (R0 : Matrix (Sum n n) n ℂ) (Gplus : Matrix n (Sum n n) ℂ)
    (hrank : FullColumnRank (Pim * R0))
    (hPim : Pim * Pim = Pim)
    (hMP : IsMPPseudoinverse (Pim * R0) Gplus)
    (hdecay : Filter.Tendsto
      (fun t : ℝ => NormedSpace.exp ((-(t : ℂ)) • H) * Pip * R0 * Gplus *
        NormedSpace.exp ((t : ℂ) • H) * Pim) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun t : ℝ => Pim + NormedSpace.exp ((-(t : ℂ)) • H) * Pip * R0 * Gplus *
        NormedSpace.exp ((t : ℂ) • H) * Pim) Filter.atTop (nhds Pim) := by
  have h := hdecay.const_add Pim
  simpa [add_comm] using h

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Graph
