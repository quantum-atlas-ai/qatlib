/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.CanonicalMPS
import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs

set_option backward.isDefEq.respectTransparency false

/-!
# SourcePepsConstruction — MPS/PEPS amplitudes as finite tensor contractions

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), pp. 1-2, Eqs. (1)-(2) and Fig. 1:
  MPS and PEPS amplitudes are obtained by contracting, for each physical
  configuration, the local tensors along the virtual entangled bonds; boundary
  virtual indices are fixed.  With a sufficiently large bond dimension an
  arbitrary finite state admits such a representation.
PDF SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

Scope retained from the claim: rectangular open boundary tensors, the actual
contractions, and the bond-dimension dependence.  No claim of an efficient
bounded-bond representation for every many-body state.

Reused frozen facts (read in full before citing):
* `QuantumAlgorithm.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude` (definition,
  amplitude layer of the open-chain MPS);
* `QuantumAlgorithm.Concepts.TensorNetwork.GaugeInvariance.pepsAmplitude_eq`
  (`pepsAmplitude` as the boundary sum of `∏ p, pepsFactor`);
* `QuantumAlgorithm.Concepts.TensorNetwork.GaugeInvariance.clause1_clause5` (the PEPS is
  a finite graph tensor network with edge dimension `≤ D`);
* `QuantumAlgorithm.Concepts.TensorNetwork.GaugeInvariance.clause2_clause2` (exact
  left-canonical MPS representation with bond dimension `max 1 (sup cutRank)`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

namespace Qatlib.Papers.RenormAlg04.MainResults.Construction

/-- Source Eqs. (1)-(2), p. 1: the open-chain MPS amplitude is by definition a
finite contraction over the internal virtual bonds (`x` fixes the physical legs). -/
theorem mps_amplitude_finite_contraction {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude A x =
      ∑ α : Fin (n - 1) → Fin D,
        ∏ i : Fin n, A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i) :=
  rfl

/-- Source Eq. (2), p. 2: the open-boundary PEPS amplitude is the finite sum over
internal bond assignments of the product of the local factors (`pepsFactor`). -/
theorem peps_amplitude_finite_contraction (a b d D : ℕ) (hD : NeZero D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    @pepsAmplitude a b d D hD T x
      = ∑ γ : Fin a × Fin b → Fin D × Fin D,
          ∏ p : Fin a × Fin b, pepsFactor T x γ p :=
  pepsAmplitude_eq a b d D T x

/-- Source Fig. 1 / Eq. (2): the PEPS is a finite graph tensor network whose virtual
edge dimension is bounded by the bond dimension `D`, and its contraction reproduces
the amplitude on every physical configuration (frozen `clause1_clause5`). -/
theorem peps_finite_tensor_network (a b d D : ℕ) (hD : NeZero D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    ∃ (N : TensorNet) (enc : (Fin a → Fin b → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
      netBondDimension N ≤ D ∧
        ∀ x : Fin a → Fin b → Fin d,
          netContract N (enc x) = @pepsAmplitude a b d D hD T x :=
  clause1_clause5 a b d D hD T

/-- Source pp. 1-2: with a sufficiently large bond dimension every normalized finite
chain state has an exact left-canonical MPS representation; the required bond
dimension is the maximum cut rank (frozen `clause2_clause2`). -/
theorem mps_representation_sufficiency {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    (hnorm : ∑ x, Complex.normSq (ψ x) = 1) (hn : 1 ≤ n) :
    ∃ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ ∧ LeftCanonical A := by
  obtain ⟨D, hD, A, hrep, hcan, -⟩ := clause2_clause2 n d ψ hnorm hn
  exact ⟨D, hD, A, hrep, hcan⟩

/-! ## Open gap: 2D representation sufficiency

Source pp. 1-2 further asserts that with a sufficiently large bond dimension an
arbitrary finite 2D state admits a PEPS representation.  The 1D analogue is
`mps_representation_sufficiency` above (from Frozen `clause2_clause2`).  The 2D
open-boundary case is **not** formalized here; the expected construction is the
following.

Key source proof steps: encode the whole physical configuration `x` in a single
bond index of cardinality `d ^ (a * b)` (via `finFunctionFinEquiv`/`finPowEnc`
after currying); at the corner `(0,0)` place the amplitude `ψ` and the constraint
`s = x_{0,0}`; at every other site place `δ_{s, x_p}` together with equality
constraints between the internal legs; boundary legs simply output `0`, so they do
not constrain the encoded configuration.
Two further points specific to the Frozen `pepsAmplitude` convention: the boundary
virtual legs are hard-fixed to `0`, so the `a + b` boundary components of `γ`
(bottom row down-legs and last column right-legs) are summed over freely and
contribute a factor `D ^ (a + b)`; the corner tensor has to be scaled by the
inverse of this factor.  The special case `a = b = 1` has no internal leg to
carry the encoded configuration, and is handled directly from the physical index.

Current Lean gap: the construction needs a concrete tensor together with the
`if`-guarded boundary-leg bookkeeping of `pepsAmplitude`, a global "all internal
legs agree" product of deltas, and the reindexing and sum-collapse over
`Fin (d ^ (a * b)) ≃ (Fin a → Fin b → Fin d)`; none of this exists in Frozen.
Candidate reusable dependencies: `finPowEnc`, `Fin (d ^ k) ≃ (Fin k → Fin d)`
(`finFunctionFinEquiv`), `Finset.prod_univ_sum`, `Finset.sum_ite_eq'`,
`Fintype.sum_equiv`.
Suggested follow-up tactic: build `Tcopy` by `classical` `decide`-free `if` on
`decode` of the right leg, then `simp [pepsAmplitude, Tcopy, finPowEnc,
Finset.prod_ite_eq, Finset.sum_ite_eq]` and close the remaining bond sum by
`Finset.sum_congr` at the unique decoded configuration. -/

end Qatlib.Papers.RenormAlg04.MainResults.Construction
