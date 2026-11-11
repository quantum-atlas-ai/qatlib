/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

set_option backward.isDefEq.respectTransparency false

/-!
# Capacity functional vocabulary (arXiv:1106.1445v8, Ch. 13, 20–25)

The operational capacities of the paper (`C(N)`, `Q(N)`, `P(N)`, `χ(N)`, …) are
extremisations of entropic quantities over all inputs and all block lengths.
A faithful formalisation of the underlying coding protocols is far beyond a
statement layer, so this file records a uniform *interface*: a `QChanInfo`
bundles a type of channels with a tensor product, tensor powers, the
single-letter entropic functionals `I, P, Q, χ`, the capacities `capC, capQ,
capP, capEA`, the λ-parametrised dynamic-capacity functional `dynCap`, and the
channel-class predicates (`Degradable`, `EntBreaking`, `Hadamard`, `Unital`).

Each paper-layer theorem then states the paper's relation between these
functionals, with the channel-class predicate as an explicit hypothesis.  The
operational definitions (achievability and converse) are not formalised; the
gap is recorded claim by claim.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Model

open scoped BigOperators

noncomputable section

/-- Interface for the channel-information quantities used by Ch. 13 and 20–25. -/
structure QChanInfo where
  /-- The type of channels. -/
  Ch : Type
  /-- Tensor product of channels. -/
  tensor : Ch → Ch → Ch
  /-- `k`-fold tensor power. -/
  tensorPow : Ch → ℕ → Ch
  /-- Convex mixture of two inputs with weight `λ`. -/
  mix : Ch → Ch → ℝ → Ch
  /-- Convex mixture of two signal states with weight `λ`. -/
  mixSig : Ch → Ch → ℝ → Ch
  /-- Channel mutual information `I(N)`. -/
  I : Ch → ℝ
  /-- Private classical information `P(N)`. -/
  P : Ch → ℝ
  /-- Coherent information `Q(N)`. -/
  Q : Ch → ℝ
  /-- Holevo information `χ(N)`. -/
  chi : Ch → ℝ
  /-- Holevo information restricted to pure-state inputs. -/
  chiPure : Ch → ℝ
  /-- Classical capacity `C(N)`. -/
  capC : Ch → ℝ
  /-- Quantum capacity `Q(N)` (operational). -/
  capQ : Ch → ℝ
  /-- Private classical capacity `P(N)` (operational). -/
  capP : Ch → ℝ
  /-- Entanglement-assisted classical capacity `C_EA(N)`. -/
  capEA : Ch → ℝ
  /-- Dynamic-capacity functional `D_λ(N)` for the weight vector `(c,q,e)`. -/
  dynCap : Ch → ℝ → ℝ → ℝ → ℝ
  /-- The channel is degradable. -/
  Degradable : Ch → Prop
  /-- The channel is entanglement breaking. -/
  EntBreaking : Ch → Prop
  /-- The channel is a Hadamard channel. -/
  Hadamard : Ch → Prop
  /-- The channel is unital. -/
  Unital : Ch → Prop
  /-- Pure-state inputs suffice for the Holevo information. -/
  PureInputSuffices : Ch → Prop
  /-- `N` is a `d`-dimensional erasure channel with erasure probability `ε`. -/
  Erasure : Ch → ℕ → ℝ → Prop
  /-- `N` is a `d`-dimensional depolarising channel with parameter `p`. -/
  Depolarizing : Ch → ℕ → ℝ → Prop
  /-- `N` is an amplitude-damping channel with damping parameter `γ`. -/
  AmplitudeDamping : Ch → ℝ → Prop

variable (C : QChanInfo)

/-- Regularised `f`: `lim_{k} (1/k) f(N^{⊗k})` written as its sequence. -/
def QChanInfo.reg (f : C.Ch → ℝ) (N : C.Ch) (k : ℕ) : ℝ :=
  (1 / (k : ℝ)) * f (C.tensorPow N k)

/-- Regularisation hypothesis: `f(N^{⊗k}) = k · f(N)`. -/
def QChanInfo.Regularises (f : C.Ch → ℝ) (N : C.Ch) : Prop :=
  ∀ k : ℕ, 1 ≤ k → f (C.tensorPow N k) = (k : ℝ) * f N

end

end Qatlib.Papers.QShannonWilde11.MainResults.Model
