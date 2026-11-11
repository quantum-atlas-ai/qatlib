/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.SchattenDiamond.DiamondSdp
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for *Dimension-Free Polylogarithmic Quantum Shadow Tomography*

This file fixes the finite-dimensional vocabulary shared by all claims of the paper
(Jeronimo–Shad, arXiv:2608.06345v3).  Everything is stated for a finite Hilbert
space `Fin d` and for finite tensor powers `Fin T → Fin d`, so that the
dimension of the Hilbert space never appears in a sample-complexity bound.

The declarations are deliberately generic in the Hilbert-space index type where
possible (`Matrix H H ℂ` for arbitrary finite `H`), because tensor-power spaces
`Fin T → Fin d` are not of the form `Fin D`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Papers.JeronimoShad26.MainResults.SourceModel

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

/-! ## Hilbert spaces, states and effects -/

/-- `ℂ^{d}` regarded as the Hilbert space of one copy. -/
abbrev Hilb (d : ℕ) : Type := Fin d

/-- `T` fresh copies of `ℂ^{d}`. -/
abbrev Reg (T d : ℕ) : Type := Fin T → Fin d

/-- The matrix algebra of one copy. -/
abbrev Op (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- A matrix is a density matrix if it is positive semidefinite and has trace one. -/
def IsDensityOn {H : Type} [Fintype H] [DecidableEq H] (ρ : Matrix H H ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- A matrix is an effect if `0 ≤ E ≤ I`. -/
def IsEffectOn {H : Type} [Fintype H] [DecidableEq H] (E : Matrix H H ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

/-- A matrix is an orthogonal projector. -/
def IsProjectorOn {H : Type} [Fintype H] [DecidableEq H] (P : Matrix H H ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- `P` projects onto a subspace containing `supp ρ` (i.e. `P ρ = ρ`). -/
def SupportedOn {H : Type} [Fintype H] [DecidableEq H]
    (ρ P : Matrix H H ℂ) : Prop :=
  IsProjectorOn P ∧ P * ρ = ρ

/-- `rinv` is the inverse square root of `ρ` compressed to the support projector `P`. -/
def SqrtInverseOn {H : Type} [Fintype H] [DecidableEq H]
    (ρ P rinv : Matrix H H ℂ) : Prop :=
  rinv.IsHermitian ∧ rinv * ρ * rinv = P ∧ P * rinv = rinv

/-! ## POVMs, Born probabilities and trace distance -/

/-- A finite-outcome POVM on a finite Hilbert space `H`. -/
structure Povm (O : Type) [Fintype O] (H : Type) [Fintype H] [DecidableEq H] where
  /-- The effect attached to outcome `o`. -/
  effect : O → Matrix H H ℂ
  /-- Each effect is positive semidefinite. -/
  effect_pos : ∀ o, (effect o).PosSemidef
  /-- The effects sum to the identity. -/
  effect_total : ∑ o, effect o = 1

/-- Trace distance `d_tr(ρ,σ) = ‖ρ−σ‖₁/2`. -/
noncomputable def traceDistOn {H : Type} [Fintype H] [DecidableEq H]
    (ρ σ : Matrix H H ℂ) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

/-- Born probability `Tr(A ρ)` of the effect/matrix `A` on the state `ρ`. -/
noncomputable def bornOn {H : Type} [Fintype H] [DecidableEq H]
    (A ρ : Matrix H H ℂ) : ℝ :=
  (Matrix.trace (A * ρ)).re

/-- Root fidelity `F(ρ,σ) = ‖√ρ √σ‖₁` (Fuchs–van de Graaf convention). -/
noncomputable def rootFidelity {d : ℕ} (ρ σ : Op d) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- The tensor power `ρ^{⊗T}` on `T` fresh copies. -/
noncomputable def tensorPower {d : ℕ} (ρ : Op d) (T : ℕ) :
    Matrix (Reg T d) (Reg T d) ℂ :=
  Matrix.of fun x y => ∏ t : Fin T, ρ (x t) (y t)

/-- `ℓ∞` norm of a real vector indexed by `Fin M` (zero on an empty index set). -/
noncomputable def linfNorm {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  if h : 0 < M then
    letI : Nonempty (Fin M) := (Fin.pos_iff_nonempty).mp h
    Finset.univ.sup' Finset.univ_nonempty (fun j => |v j|)
  else 0

/-! ## Finite ensembles and scalar estimation -/

/-- A finite ensemble of states with a probability vector. -/
structure Ensemble (ι d : ℕ) where
  /-- Prior weights `p_x`. -/
  weight : Fin ι → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_sum : ∑ x, weight x = 1
  /-- The ensemble states. -/
  state : Fin ι → Op d
  state_density : ∀ x, IsDensityOn (state x)

/-- Weighted sum `∑_x q_x ρ_x` over a finite type. -/
noncomputable def avgOn {ι H : Type} [Fintype ι] [Fintype H] [DecidableEq H]
    (q : ι → ℝ) (ρ : ι → Matrix H H ℂ) : Matrix H H ℂ :=
  ∑ x, q x • ρ x

/-- Mean-square risk of a scalar strategy `(N, ẑ)` with true labels `z`. -/
noncomputable def scalarRisk {ι d : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ)
    {m : ℕ} (N : Povm (Fin m) (Fin d)) (zhat : Fin m → ℝ) : ℝ :=
  ∑ x, F.weight x * ∑ w, bornOn (N.effect w) (F.state x) * (z x - zhat w) ^ 2

/-- Quadratic risk of decoding the PGM outcome directly with labels `z`. -/
noncomputable def pgmRisk {ι d : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ)
    (G : Fin ι → Op d) : ℝ :=
  ∑ x, ∑ y, F.weight x * bornOn (G y) (F.state x) * (z x - z y) ^ 2

/-- Quadratic risk of the averaged recovery measurement with labels `z`. -/
noncomputable def recoveryRisk {ι d : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ)
    (D : Fin ι → Op d) : ℝ :=
  ∑ x, ∑ y, F.weight x * bornOn (D y) (F.state x) * (z x - z y) ^ 2

/-- Infimum of the scalar mean-square risk over all finite-outcome scalar strategies. -/
noncomputable def optimalRisk {ι d : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (N : Povm (Fin m) (Fin d)) (zhat : Fin m → ℝ),
    r = scalarRisk F z N zhat}

/-- The completed pretty-good measurement attached to an ensemble.

`P` is the support projector of the average state, `rinv` the inverse square root
compressed to the support, and `G y` is the completed PGM effect, including the
weight `q_y` on the kernel complement `1 - P`. -/
def IsCompletedPGM {ι d : ℕ} (F : Ensemble ι d) (P rinv : Op d)
    (G : Fin ι → Op d) : Prop :=
  SupportedOn (avgOn F.weight F.state) P ∧
  SqrtInverseOn (avgOn F.weight F.state) P rinv ∧
  ∀ y, G y = rinv * (F.weight y • F.state y) * rinv + F.weight y • (1 - P)

/-! ## The spectral coefficient `Λ(a,b)` of Appendix C -/

/-- The scalar coefficient `Λ(a,b)` of Lemma C.1,
`(log a − log b)/(a−b)` for `a ≠ b` and `1/a` on the diagonal. -/
noncomputable def LambdaReal (a b : ℝ) : ℝ :=
  if a = b then 1 / a else (Real.log a - Real.log b) / (a - b)

/-- The averaged recovery effect family of Eq. (5)/(45) on the support of the
average state: in the eigenbasis of `∑_x q_x ρ_x` with eigenvalues `eig`, the
effect for label `y` is entrywise `q_y Λ(d_a,d_b) (ρ_y)_{ab}`. -/
def IsRecoveryEffectFamily {ι H : Type} [Fintype ι] [Fintype H] [DecidableEq H]
    (q : ι → ℝ) (ρ : ι → Matrix H H ℂ) (D : ι → Matrix H H ℂ) : Prop :=
  ∃ (U : Matrix H H ℂ) (eig : H → ℝ),
    (∀ a, 0 < eig a) ∧
    U ∈ Matrix.unitaryGroup H ℂ ∧
    (∑ x, q x • ρ x) = U * Matrix.diagonal (fun a => (eig a : ℂ)) * Matrix.conjTranspose U ∧
    ∀ y a c, (Matrix.conjTranspose U * D y * U) a c =
      (q y : ℂ) * (LambdaReal (eig a) (eig c) : ℂ) * (Matrix.conjTranspose U * ρ y * U) a c

/-- The kernel `K_t(y|x)` of the averaged recovery measurement on `t` copies. -/
noncomputable def recoverKernel {ι d t : ℕ} (F : Ensemble ι d)
    (D : Fin ι → Matrix (Reg t d) (Reg t d) ℂ) (y x : Fin ι) : ℝ :=
  bornOn (D y) (tensorPower (F.state x) t)

/-! ## Grid outcomes for `Z_ε = {0, 1/K, …, 1}^M` -/

/-- The `i`-th grid point `i/K` in `[0,1]`. -/
noncomputable def gridVal (K : ℕ) (i : Fin (K + 1)) : ℝ :=
  (i : ℝ) / (K : ℝ)

/-- A grid outcome `z ∈ Z_ε^M` read as a real vector. -/
noncomputable def gridVec (M K : ℕ) (z : Fin M → Fin (K + 1)) : Fin M → ℝ :=
  fun j => gridVal K (z j)

/-- Failure mass `f_{ρ,ε}(N)` of a `Z_ε`-outcome POVM: the probability that some
coordinate of the grid outcome differs from `Tr(E_j ρ)` by more than `ε`. -/
noncomputable def gridFailMass {M d T K : ℕ}
    (N : Povm (Fin M → Fin (K + 1)) (Reg T d)) (E : Fin M → Op d)
    (ρ : Op d) (ε : ℝ) : ℝ :=
  ∑ z : Fin M → Fin (K + 1),
    if ε < linfNorm (fun j => |gridVec M K z j - bornOn (E j) ρ|) then
      bornOn (N.effect z) (tensorPower ρ T) else 0

/-- A collective finite-outcome shadow-tomography strategy with an arbitrary decoder. -/
structure EstimationStrategy (M T d n : ℕ) where
  /-- The collective POVM on `T` copies. -/
  povm : Povm (Fin n) (Reg T d)
  /-- The decoder producing `M` estimates from an outcome. -/
  decoder : Fin n → Fin M → ℝ
  decoder_nonneg : ∀ z j, 0 ≤ decoder z j
  decoder_le_one : ∀ z j, decoder z j ≤ 1

/-- Failure probability of a strategy at accuracy `ε` on the state `ρ`. -/
noncomputable def failureProb {M T d n : ℕ} (S : EstimationStrategy M T d n)
    (E : Fin M → Op d) (ρ : Op d) (ε : ℝ) : ℝ :=
  ∑ z : Fin n,
    if ε < linfNorm (fun j => |S.decoder z j - bornOn (E j) ρ|) then
      bornOn (S.povm.effect z) (tensorPower ρ T) else 0

/-- The strategy has accuracy `ε` and failure probability `δ` uniformly over all states. -/
def HasAccuracy {M T d n : ℕ} (S : EstimationStrategy M T d n)
    (E : Fin M → Op d) (ε δ : ℝ) : Prop :=
  ∀ ρ, IsDensityOn ρ → failureProb S E ρ ε ≤ δ

/-! ## Sequential (posterior-refocused) PGM of Algorithm 1 -/

/-- The completed PGM of a posterior ensemble `(q_x, ρ_x)`: this is the same
predicate as `IsCompletedPGM`, generalized from `Op d` to an arbitrary finite
Hilbert space (needed for `n`-copy registers). -/
def IsCompletedPGMOfState {ι H : Type} [Fintype ι] [Fintype H] [DecidableEq H]
    (q : ι → ℝ) (ρ : ι → Matrix H H ℂ) (G : ι → Matrix H H ℂ) : Prop :=
  ∃ (P rinv : Matrix H H ℂ),
    SupportedOn (avgOn q ρ) P ∧
    SqrtInverseOn (avgOn q ρ) P rinv ∧
    ∀ y, G y = rinv * (q y • ρ y) * rinv + q y • (1 - P)

/-- The joint probability of `(X = x, H_r = h)` for the posterior PGM: the product
of the round-`s` PGM outcome probabilities `Tr(G_s(h_{<s})_{h_s} ρ_x^{⊗n})` on
the posterior generated by the earlier rounds. -/
noncomputable def pgmJoint {ι d n : ℕ} (F : Ensemble ι d)
    (G : (s : ℕ) → (Fin s → Fin ι) → Fin ι → Matrix (Reg n d) (Reg n d) ℂ)
    (r : ℕ) (x : Fin ι) (h : Fin r → Fin ι) : ℝ :=
  F.weight x * ∏ s : Fin r,
    bornOn (G s.1 (fun i => h (Fin.castLE (Nat.le_of_lt s.2) i)) (h s))
      (tensorPower (F.state x) n)

/-- The joint law of the state label `X` and the full history `H_r` produced by
the `r`-round posterior-refocused PGM with `n` copies per round.  The PGM in each
round is the completed PGM of the posterior distribution over states given the
outcomes of earlier rounds. -/
def IsPosteriorPGMLaw {ι d r n : ℕ} (F : Ensemble ι d)
    (joint : Fin ι → (Fin r → Fin ι) → ℝ) : Prop :=
  ∃ (G : (s : ℕ) → (Fin s → Fin ι) → Fin ι → Matrix (Reg n d) (Reg n d) ℂ),
    (∀ (s : ℕ) (h : Fin s → Fin ι),
      IsCompletedPGMOfState (fun x => pgmJoint F G s x h)
        (fun x => tensorPower (F.state x) n) (G s h)) ∧
    (∀ x h, joint x h = pgmJoint F G r x h) ∧
    (∀ x h, 0 ≤ joint x h)

/-! ## Entropies of marginals (Appendix B.3) -/

/-- Von Neumann entropy `S(ρ) = Σ_i −λ_i log λ_i` of a positive semidefinite
matrix, computed from its eigenvalues. -/
noncomputable def vnEntropy {H : Type} [Fintype H] [DecidableEq H]
    (ρ : Matrix H H ℂ) (hρ : ρ.PosSemidef) : ℝ :=
  ∑ i : H, Real.negMulLog (hρ.1.eigenvalues i)

/-- Embed a prefix of length `t` together with the complementary coordinates into
a full register of length `N`. -/
noncomputable def comb {N d : ℕ} (t : ℕ) (a : Reg t d)
    (z : {i : Fin N // t ≤ i.1} → Fin d) : Reg N d :=
  fun i => if h : (i : ℕ) < t then a ⟨i, h⟩ else z ⟨i, Nat.le_of_not_lt h⟩

/-- Marginal of the joint state on `J` and the first `t` quantum registers. -/
noncomputable def prefixMarg {k N d : ℕ} (t : ℕ) (_ht : t ≤ N)
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) :
    Matrix (Fin k × Reg t d) (Fin k × Reg t d) ℂ :=
  fun a b => ∑ z : {i : Fin N // t ≤ i.1} → Fin d,
    ω (a.1, comb t a.2 z) (b.1, comb t b.2 z)

/-- Marginal of the joint state on the first `t` quantum registers. -/
noncomputable def qMarg {k N d : ℕ} (t : ℕ) (ht : t ≤ N)
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) :
    Matrix (Reg t d) (Reg t d) ℂ :=
  fun a b => ∑ j : Fin k, prefixMarg t ht ω (j, a) (j, b)

/-- Marginal of the joint state on the classical label `J`. -/
noncomputable def jMarg {k N d : ℕ}
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => ∑ z : Reg N d, ω (a, z) (b, z)

/-- Positivity of the `J`-and-prefix marginal. -/
theorem prefixMarg_pos {k N d : ℕ} (t : ℕ) (ht : t ≤ N)
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) :
    (prefixMarg t ht ω).PosSemidef := by
  have h : prefixMarg t ht ω = ∑ z : {i : Fin N // t ≤ i.1} → Fin d,
      ω.submatrix (fun a : Fin k × Reg t d => (a.1, comb t a.2 z))
        (fun b : Fin k × Reg t d => (b.1, comb t b.2 z)) := by
    ext a b
    simp [prefixMarg, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [h]
  simpa using Matrix.posSemidef_sum (Finset.univ)
    (fun z _ => hω.submatrix (fun a : Fin k × Reg t d => (a.1, comb t a.2 z)))

/-- Positivity of the `t`-register marginal. -/
theorem qMarg_pos {k N d : ℕ} (t : ℕ) (ht : t ≤ N)
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) :
    (qMarg t ht ω).PosSemidef := by
  have h : qMarg t ht ω = ∑ j : Fin k,
      (prefixMarg t ht ω).submatrix (fun a : Reg t d => (j, a)) (fun a : Reg t d => (j, a)) := by
    ext a b
    simp [qMarg, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [h]
  simpa using Matrix.posSemidef_sum (Finset.univ)
    (fun j _ => (prefixMarg_pos t ht ω hω).submatrix (fun a : Reg t d => (j, a)))

/-- Positivity of the classical marginal. -/
theorem jMarg_pos {k N d : ℕ}
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) :
    (jMarg ω).PosSemidef := by
  have h : jMarg ω = ∑ z : Reg N d,
      ω.submatrix (fun a : Fin k => (a, z)) (fun b : Fin k => (b, z)) := by
    ext a b
    simp [jMarg, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [h]
  simpa using Matrix.posSemidef_sum (Finset.univ)
    (fun z _ => hω.submatrix (fun a : Fin k => (a, z)))

/-- A joint state is classical on `J` when its off-diagonal `J`-blocks vanish. -/
def IsClassicalOnJ {k N d : ℕ}
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) : Prop :=
  ∀ (a b : Fin k) (z z' : Reg N d), a ≠ b → ω (a, z) (b, z') = 0

/-- The `t`-th conditional mutual information `I(J : Q_{t+1} | Q_1 ⋯ Q_t)`. -/
noncomputable def cmi {k N d : ℕ} (t : ℕ) (ht : t + 1 ≤ N)
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) : ℝ :=
  vnEntropy (prefixMarg t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ω)
      (prefixMarg_pos t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ω hω)
    + vnEntropy (qMarg (t + 1) ht ω) (qMarg_pos (t + 1) ht ω hω)
    - vnEntropy (prefixMarg (t + 1) ht ω) (prefixMarg_pos (t + 1) ht ω hω)
    - vnEntropy (qMarg t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ω)
        (qMarg_pos t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ω hω)

/-- `I(J : Q_1 ⋯ Q_N) = S(J) + S(Q^N) − S(JQ^N)`. -/
noncomputable def infoJQ {k N d : ℕ}
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) : ℝ :=
  vnEntropy (jMarg ω) (jMarg_pos ω hω)
    + vnEntropy (qMarg N (le_refl N) ω) (qMarg_pos N (le_refl N) ω hω)
    - vnEntropy ω hω

/-- `H(J)`, the entropy of the classical label. -/
noncomputable def classicalEntropy {k N d : ℕ}
    (ω : Matrix (Fin k × Reg N d) (Fin k × Reg N d) ℂ) (hω : ω.PosSemidef) : ℝ :=
  vnEntropy (jMarg ω) (jMarg_pos ω hω)

end Qatlib.Papers.JeronimoShad26.MainResults.SourceModel
