/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroupIsom10.MainResults.Model
import Mathlib.Data.Multiset.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Lemma 5.2 of arXiv:1001.0608v1 (p.15)

Paper statement (arXiv:1001.0608v1, Lemma 5.2, p.15):

> **Lemma 5.2.** Let `M₁` and `M₂` be two matrices in `GL(r, F)`, where `r` denotes a positive
> integer and `F` denotes a finite field.  Let `m` be an integer such that
> `M₁^m = M₂^m = I`, and `k` be an integer in `Z_m^*`.  Then `M₁` and `M₂^k` are similar in
> `GL(r, F)` if and only if, for all positive integers `d` and `ℓ`, the equality
> `[Σ_{d,ℓ}(M₂)]^k = Σ_{d,ℓ}(M₁)` holds,

where `Σ_{d,ℓ}(M)` is the multiset of eigenvalues in `GF(q^d)` (not in a proper subfield) of
the elementary divisors of degree `ℓ` of `M` (Definition 5.1, p.14).

Mathlib has no elementary divisors and no field-extension decomposition of the minimal
polynomial, so `Σ_{d,ℓ}` is modelled as an abstract function `σ : Matrix → ℕ → ℕ → Multiset K`
satisfying the two facts that the paper uses:

* `hcomplete` — two matrices are similar iff they have the same elementary divisors
  (the classical structure theorem behind the paper's final sentence of the proof);
* `hpow` — `Σ_{d,ℓ}(M₂^k) = (Σ_{d,ℓ}(M₂))^k`, which is Lemma 5.1 applied entrywise
  (the paper: "if `k` is coprime with `m`, then Lemma 5.1 implies ...").

Under these hypotheses the paper's equivalence is proved in full: this isolates the logical
content of Lemma 5.2 from the missing matrix-classification theory.
-/

namespace Qatlib.Papers.GroupIsom10.MainResults.MatrixAlgebra

open Qatlib.Papers.GroupIsom10.MainResults.Model

/-- **Lemma 5.2** (arXiv:1001.0608v1, p.15), reduction form.  Let `σ` be an
elementary-divisor spectrum function satisfying the two standard facts used in the paper
(similarity is determined by the spectra, and taking `k`-th powers raises every eigenvalue to
the `k`-th power).  If `M₁^m = M₂^m = 1` and `k` is coprime with `m`, then `M₁` is similar to
`M₂^k` if and only if the `k`-th powers of the spectra of `M₂` equal the spectra of `M₁`. -/
theorem lemma_5_2 {K : Type*} [Field K] {r : ℕ}
    (σ : Matrix (Fin r) (Fin r) K → ℕ → ℕ → Multiset K)
    (hcomplete : ∀ A B : Matrix (Fin r) (Fin r) K,
      IsSimilar A B ↔ ∀ d ℓ, σ A d ℓ = σ B d ℓ)
    (M1 M2 : Matrix (Fin r) (Fin r) K) (m : ℕ)
    (hM1 : M1 ^ m = 1) (hM2 : M2 ^ m = 1) (k : ℕ) (hk : Nat.Coprime k m)
    (hpow : ∀ d ℓ, σ (M2 ^ k) d ℓ = (σ M2 d ℓ).map (fun x => x ^ k)) :
    (IsSimilar M1 (M2 ^ k) ↔
      ∀ d ℓ, (σ M2 d ℓ).map (fun x => x ^ k) = σ M1 d ℓ) := by
  constructor
  · intro h d ℓ
    -- Similarity gives equality of the spectra of `M₁` and `M₂^k`.
    have h1 : σ M1 d ℓ = σ (M2 ^ k) d ℓ := (hcomplete M1 (M2 ^ k)).mp h d ℓ
    rw [hpow d ℓ] at h1
    exact h1.symm
  · intro h
    -- Equality of the powered spectra gives equality with the spectra of `M₂^k`.
    rw [hcomplete]
    intro d ℓ
    rw [hpow d ℓ]
    exact (h d ℓ).symm

end Qatlib.Papers.GroupIsom10.MainResults.MatrixAlgebra
