/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Paper-layer vocabulary for *The Quantum Decoding Problem* (arXiv:2509.24796v2)

This module owns the paper-specific objects used by the theorem layer of
`Papers/QDecoding25`.  It is *vocabulary and bookkeeping only*: no theorem of
the paper is claimed here, and every definition is the paper's own object
written in Lean.

The fixed source is arXiv:2509.24796v2 (4 Feb 2026), cited by page and
numbered statement in the theorem files.

Main objects:

* `Mass` — a probability mass function on a finite type (the paper's
  probability distributions over `F_q^n`);
* `qaryEntropy` — the `q`-ary entropy `H_q` of Definition 4 (p. 11);
* `Mass.typicalSet` / `Mass.defect` — the typical set and defect of
  Definition 5 (p. 11);
* `Negligible` — negligible functions, §2.1 (p. 10);
* `NiceTypicalFamily` — Definition 9, a *nice family of typical sets* (p. 16);
* `QDPFamily` — a family of quantum-decoding instances together with the
  random linear-code ensemble that the achievability analysis of §3.2 and §4.1
  runs over: the noise law `p = |f̂|²`, the generator matrices, the dual code
  and the quotient `F_q^{n_i}/C^⊥`;
* `POVM`, `densityOf`, `povmSuccess` — the quantum-measurement vocabulary used
  by the strong converse (§3.3, Lemmas 9 and 10).

Notation conventions: `FVec F n` is `F^n`; `qpow q x` is `q^x`; all
probability distributions are real-valued mass functions summing to one.
-/

namespace Qatlib.Papers.QDecoding25.MainResults

open scoped BigOperators ComplexOrder
open Filter Topology

/-- Vectors over `F`, the ambient space `F^n` of the paper. -/
abbrev FVec (F : Type*) (n : ℕ) := Fin n → F

/-- The base-`q` exponential `q ^ x`, written through `exp (x log q)`.
For `0 < q` this is the usual `q ^ x` (Mathlib `Real.rpow`); the exponential
form is used so that the asymptotic arguments of §3.2 can be discharged by
`exp`-estimates. -/
noncomputable def qpow (q x : ℝ) : ℝ := Real.exp (x * Real.log q)

/-- `q`-ary entropy of a real mass function, Definition 4 of the paper (p. 11):
`H_q(p) = -∑_x p(x) log_q p(x)`.  Mathlib's convention `log 0 = 0` implements
the paper's `0 log 0 = 0`. -/
noncomputable def qaryEntropy {α : Type*} [Fintype α] (q : ℝ) (p : α → ℝ) : ℝ :=
  -∑ x, p x * (Real.log (p x) / Real.log q)

/-- A probability mass function on a finite type. -/
structure Mass (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace Mass

variable {α : Type*} [Fintype α]

/-- The typical set of Definition 5 (p. 11): all `y` whose mass lies between
the bounding functions `A ≤ p(y) ≤ B`. -/
noncomputable def typicalSet (A B : ℝ) (p : Mass α) : Finset α := by
  classical
  exact Finset.univ.filter fun y => A ≤ p.mass y ∧ p.mass y ≤ B

/-- The defect `δ = 1 - p(T)` attached to a set `T`. -/
def defect (p : Mass α) (T : Finset α) : ℝ := 1 - ∑ y ∈ T, p.mass y

/-- The defect `δ(ε,n) = 1 - p(T_ε^{(n)})` of the typical set with bounds
`A` and `B`. -/
noncomputable def defectOf (p : Mass α) (A B : ℝ) : ℝ := p.defect (p.typicalSet A B)

/-- The `q`-ary entropy `H_q(p)`. -/
noncomputable def entropy (q : ℝ) (p : Mass α) : ℝ := qaryEntropy q p.mass

/-- The mass of a set. -/
noncomputable def setMass (p : Mass α) (T : Finset α) : ℝ := ∑ y ∈ T, p.mass y

end Mass

/-- A function `η : ℕ → ℝ` is negligible when it decays faster than every
inverse power, §2.1 (p. 10): for every positive integer `a` there is `N` with
`|η n| ≤ n^{-a}` for all `n ≥ N`. -/
def Negligible (η : ℕ → ℝ) : Prop :=
  ∀ a : ℕ, 0 < a → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |η n| ≤ 1 / (n : ℝ) ^ a

/-- The average of `X` over a finite set `s`; used for the expectation `E_G`
over the uniform generator matrix. -/
noncomputable def avgOver {G : Type*} (s : Finset G) (X : G → ℝ) : ℝ :=
  (∑ g ∈ s, X g) / (s.card : ℝ)

/-- The frequency of an event over a finite set `s`; used for `Pr_G`. -/
noncomputable def probOver {G : Type*} (s : Finset G) (E : G → Prop) : ℝ := by
  classical
  exact ((s.filter E).card : ℝ) / (s.card : ℝ)

/-- The variance of `X` over `s`. -/
noncomputable def varOver {G : Type*} (s : Finset G) (X : G → ℝ) : ℝ :=
  avgOver s (fun g => (X g - avgOver s X) ^ 2)

/-- A *nice family of typical sets*, Definition 9 (p. 16).  The sequence
`n_i` is increasing and positive, `p_i` is a distribution on `F_q^{n_i}`, and
the typical sets `T_ε^{(n_i)} = {y : A_i(ε) ≤ p_i(y) ≤ B_i(ε)}` have

1. negligible defect `δ(ε,n_i) = negl(i)` for every `ε > 0`;
2. `A_i(ε) ≥ K₁ q^{-n_i (H + α(ε))}`;
3. `B_i(ε) ≤ K₂ q^{-n_i (H - β(ε))}`,

where `α, β → 0` at `0`. -/
structure NiceTypicalFamily (F : Type*) [Field F] [Fintype F] where
  n : ℕ → ℕ
  n_pos : ∀ i, 0 < n i
  n_strictMono : StrictMono n
  p : ∀ i, Mass (FVec F (n i))
  H : ℝ
  K1 : ℝ
  K2 : ℝ
  K1pos : 0 < K1
  K2pos : 0 < K2
  alpha : ℝ → ℝ
  beta : ℝ → ℝ
  alpha_tendsto : Tendsto alpha (𝓝 0) (𝓝 0)
  beta_tendsto : Tendsto beta (𝓝 0) (𝓝 0)
  A : ℕ → ℝ → ℝ
  B : ℕ → ℝ → ℝ
  delta_negl : ∀ ε : ℝ, 0 < ε → Negligible fun i => (p i).defectOf (A i ε) (B i ε)
  A_ge : ∀ (i : ℕ) (ε : ℝ), 0 < ε →
    K1 * qpow (Fintype.card F : ℝ) (-(n i : ℝ) * (H + alpha ε)) ≤ A i ε
  B_le : ∀ (i : ℕ) (ε : ℝ), 0 < ε →
    B i ε ≤ K2 * qpow (Fintype.card F : ℝ) (-(n i : ℝ) * (H - beta ε))

namespace NiceTypicalFamily

variable {F : Type*} [Field F] [Fintype F]

/-- The defect `δ(ε,n_i)` of the typical set at gap `ε`. -/
noncomputable def delta (fam : NiceTypicalFamily F) (i : ℕ) (ε : ℝ) : ℝ :=
  (fam.p i).defectOf (fam.A i ε) (fam.B i ε)

/-- The typical set `T_ε^{(n_i)}`. -/
noncomputable def typicalSet (fam : NiceTypicalFamily F) (i : ℕ) (ε : ℝ) :
    Finset (FVec F (fam.n i)) :=
  (fam.p i).typicalSet (fam.A i ε) (fam.B i ε)

/-- The entropy per symbol `H_q(p_i)/n_i`. -/
noncomputable def entropyPerSymbol (fam : NiceTypicalFamily F) (i : ℕ) : ℝ :=
  (fam.p i).entropy (Fintype.card F : ℝ) / (fam.n i : ℝ)

end NiceTypicalFamily

/-- A family of quantum-decoding instances together with the random
linear-code ensemble used by the achievability and dual-sampling analyses.
`Gen i` is the finite set of generator matrices, `dual i g` is the dual code
`C^⊥` of the code generated by `g`, and `quot i` indexes the classes of
`F_q^{n_i}/C^⊥` with representatives `rep i`.  `quot_card` records that the
quotient has `q^{k_i}` elements, where `k_i = ⌊R n_i⌋` in the theorems. -/
structure QDPFamily (F : Type*) [Field F] [Fintype F] where
  nice : NiceTypicalFamily F
  k : ℕ → ℕ
  Gen : ℕ → Type*
  gens : ∀ i, Finset (Gen i)
  gens_nonempty : ∀ i, (gens i).Nonempty
  dual : ∀ i, Gen i → Finset (FVec F (nice.n i))
  quot : ℕ → Type*
  quots : ∀ i, Finset (quot i)
  quots_nonempty : ∀ i, (quots i).Nonempty
  rep : ∀ i, quot i → FVec F (nice.n i)
  quot_card : ∀ i, (quots i).card = Fintype.card F ^ k i

namespace QDPFamily

variable {F : Type*} [Field F] [Fintype F]

/-- The coset `s + C^⊥` of a word `s`. -/
noncomputable def coset (fam : QDPFamily F) (i : ℕ) (g : fam.Gen i)
    (s : FVec F (fam.nice.n i)) : Finset (FVec F (fam.nice.n i)) := by
  classical
  exact (fam.dual i g).image fun y => s + y

/-- The noise mass `p_i`. -/
noncomputable def mass (fam : QDPFamily F) (i : ℕ) : FVec F (fam.nice.n i) → ℝ :=
  (fam.nice.p i).mass

/-- `Z_s = ‖|W_s⟩‖ = sqrt (∑_{y ∈ s + C^⊥} p(y))` of Proposition 5 (p. 16). -/
noncomputable def Zs (fam : QDPFamily F) (i : ℕ) (g : fam.Gen i)
    (s : FVec F (fam.nice.n i)) : ℝ :=
  Real.sqrt (∑ y ∈ fam.coset i g s, fam.mass i y)

/-- The truncated quantity `Z̃_s(ε) = sqrt (∑_{y ∈ T_ε ∩ (s+C^⊥)} p(y))`
used in Lemma 4 (p. 19). -/
noncomputable def Ztilde (fam : QDPFamily F) (i : ℕ) (ε : ℝ) (g : fam.Gen i)
    (s : FVec F (fam.nice.n i)) : ℝ := by
  classical
  exact Real.sqrt <| ∑ y ∈ (fam.coset i g s).filter
      (fun y => fam.nice.A i ε ≤ fam.mass i y ∧ fam.mass i y ≤ fam.nice.B i ε),
    fam.mass i y

/-- The probability of success `P_PGM = q^{-k_i} (∑_s Z_s)^2` of the pretty
good measurement, Proposition 5 (p. 16). -/
noncomputable def pgmSuccess (fam : QDPFamily F) (i : ℕ) (g : fam.Gen i) : ℝ :=
  (1 / ((fam.quots i).card : ℝ)) *
    (∑ s ∈ fam.quots i, fam.Zs i g (fam.rep i s)) ^ 2

/-- The average `E_G [P_PGM]` over the uniform choice of the generator. -/
noncomputable def expectedPGM (fam : QDPFamily F) (i : ℕ) : ℝ :=
  avgOver (fam.gens i) fun g => fam.pgmSuccess i g

/-- `X = ∑_{y ∈ T_ε^{(n_i)} ∩ (C^⊥)^*} p(y)`, §4.2 (p. 32). -/
noncomputable def X (fam : QDPFamily F) (i : ℕ) (ε : ℝ) (g : fam.Gen i) : ℝ := by
  classical
  exact ∑ y ∈ ((fam.dual i g).filter fun y => y ≠ 0).filter
      (fun y => fam.nice.A i ε ≤ fam.mass i y ∧ fam.mass i y ≤ fam.nice.B i ε),
    fam.mass i y

/-- `Y = ∑_{y ∈ (C^⊥)^*} p(y)`, §4.2 (p. 32). -/
noncomputable def Y (fam : QDPFamily F) (i : ℕ) (g : fam.Gen i) : ℝ := by
  classical
  exact ∑ y ∈ (fam.dual i g).filter fun y => y ≠ 0, fam.mass i y

end QDPFamily

/-! ## Quantum measurements (strong converse, §3.3 and §2.4) -/

open Matrix

/-- A POVM with outcomes indexed by `ι` acting on `ℂ^d`, Definition 8 context
(p. 13): positive semidefinite operators summing to the identity. -/
structure POVM (ι : Type*) [Fintype ι] (d : ℕ) where
  op : ι → Matrix (Fin d) (Fin d) ℂ
  pos : ∀ j, (op j).PosSemidef
  total : ∑ j, op j = 1

/-- The density matrix `|ψ⟩⟨ψ|` of a vector `ψ ∈ ℂ^d`. -/
noncomputable def densityOf {d : ℕ} (ψ : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => ψ a * star (ψ b)

/-- The average success probability `(1/N) ∑_i tr(M_i |ψ_i⟩⟨ψ_i|)` of a POVM
`M` on the states `ψ`. -/
noncomputable def povmSuccess {ι : Type*} [Fintype ι] {d : ℕ}
    (M : POVM ι d) (ψ : ι → Fin d → ℂ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) *
    ∑ i, (Matrix.trace (M.op i * densityOf (ψ i))).re

/-- The trace distance `D(ρ,σ) = max_{P ≼ I} tr(P(ρ-σ))`, Definition 7 and
Claim 2 (p. 12).  Written as a supremum to keep the definition free of an
eigenvalue decomposition. -/
noncomputable def traceDistance {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {t : ℝ | ∃ P : Matrix (Fin d) (Fin d) ℂ,
    P.PosSemidef ∧ (1 - P).PosSemidef ∧ t = (Matrix.trace (P * (A - B))).re}

end Qatlib.Papers.QDecoding25.MainResults
