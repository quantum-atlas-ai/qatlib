/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamDecodedQI25.MainResults.Source.OperatorModel
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section


/-!
# HamDecodedQI25 — Bell-basis orthonormality (source App. A.2)

Fixed version: arXiv:2510.07913 (v1), Appendix A.2.  This module carries the
part of the source `Source/Decoding.lean` development whose proofs reduce to
the supplied unitary/orthogonality hypotheses plus finite cardinality
arithmetic: the two orthonormality statements are proved here.

* Lemma 46 (Eq. (230), p. 59): the Bell basis attached to a unitary,
  pairwise trace-orthogonal Pauli family is orthonormal — the matrix half
  `(Pmat P)ᴴ * Pmat P = 1` is exactly unitarity, and the index-cardinality
  half `|PauliString n| = 4^n` is the size of `{I,X,Y,Z}^n`.
* Lemma 48 (Eq. (234), p. 60): the Weyl–Bell analogue over `F_p`, with
  index set `F_p^{2n}` of cardinality `p^{2n}`.

The remaining six statements of the source file — Lemma 55, Lemma 56 and
Corollary 57 (weak-regularity cardinality arithmetic), Theorems 47 and 49
(coherent Bell / Weyl–Bell measurement circuits), and Theorem 62 (extension
of a partial symplectic isometry) — are deferred obligations of this
development; the maximally entangled state, the Clifford gate synthesis and
the symplectic basis completion they need are not available in Mathlib or the
fixed public library.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Papers.HamDecodedQI25.MainResults
open Matrix

namespace Qatlib.Papers.HamDecodedQI25.MainResults

/-- **Source Lemma 46** (arXiv:2510.07913, Eq. (230), p. 59).  For a family
`Pmat` of `2^n × 2^n` matrices indexed by Pauli strings that is unitary with
pairwise trace-orthogonal entries (`hU`, `horth` — exactly the properties used
in the paper's proof), each Bell coefficient matrix satisfies
`(Pmat P)ᴴ * Pmat P = 1`, and the Bell family is indexed by the `4^n` Pauli
strings.  The first conjunct is unitarity; the second is the cardinality of
`{I,X,Y,Z}^n`. -/
theorem bell_basis_orthonormal {n : ℕ} (_hn : 1 ≤ n)
    (Pmat : PauliString n → Mat (2 ^ n))
    (hU : ∀ P, Pmat P ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (_horth : ∀ P Q, P ≠ Q → (Pmat P)ᴴ * Pmat Q = 0) :
    (∀ P, (Pmat P)ᴴ * Pmat P = 1) ∧
      Fintype.card (PauliString n) = 4 ^ n := by
  refine ⟨fun P => (Matrix.mem_unitaryGroup_iff').mp (hU P), ?_⟩
  calc Fintype.card (PauliString n)
      = Fintype.card (Fin n → PauliLetter) := rfl
    _ = (Fintype.card PauliLetter) ^ n := by
        rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = 4 ^ n := by rw [show Fintype.card PauliLetter = 4 by decide]

/-- **Source Lemma 48** (arXiv:2510.07913, Eq. (234), p. 60).  Weyl–Bell
analogue of `bell_basis_orthonormal` over `F_p` for prime `p`: a unitary,
pairwise trace-orthogonal Weyl family `W` indexed by `F_p^{2n}` satisfies
`(W u)ᴴ * W u = 1`, and the index space `F_p^n × F_p^n` has cardinality
`p^{2n}`. -/
theorem weyl_bell_basis_orthonormal {p n : ℕ} [Fact (Nat.Prime p)]
    (W : ((Fin n → ZMod p) × (Fin n → ZMod p)) → Mat (p ^ n))
    (hU : ∀ u, W u ∈ Matrix.unitaryGroup (Fin (p ^ n)) ℂ)
    (_horth : ∀ u v, u ≠ v → (W u)ᴴ * W v = 0) :
    (∀ u, (W u)ᴴ * W u = 1) ∧
      Fintype.card ((Fin n → ZMod p) × (Fin n → ZMod p)) = p ^ (2 * n) := by
  have hp : 0 < p := (Fact.out (p := Nat.Prime p)).pos
  have : NeZero p := ⟨hp.ne'⟩
  refine ⟨fun u => (Matrix.mem_unitaryGroup_iff').mp (hU u), ?_⟩
  calc Fintype.card ((Fin n → ZMod p) × (Fin n → ZMod p))
      = Fintype.card (Fin n → ZMod p) * Fintype.card (Fin n → ZMod p) :=
        Fintype.card_prod _ _
    _ = p ^ n * p ^ n := by
        rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ZMod.card]
    _ = p ^ (2 * n) := by
        rw [show 2 * n = n + n by ring, pow_add]

end Qatlib.Papers.HamDecodedQI25.MainResults
