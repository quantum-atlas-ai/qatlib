/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.4 of SymQueryComm20: the reduction `((r ∘̃ h_G) ∘ □) ≥ CC(r ∘ G)`

Source: S. Chakraborty, A. Chattopadhyay, P. Høyer, N. S. Mande, M. Paraashar,
R. de Wolf, arXiv:2012.05233v2, Lemma 5.4 and its proof (p. 25).

For `□ = AND₂` the paper preprocesses Alice's input into
`X = ((H(x₁), (−1)^k), …, (H(xₙ), (−1)^k))` and Bob's into
`Y = (((−1)^j, H(y₁)), …, ((−1)^j, H(yₙ)))`, and for `□ = XOR₂` the padding
strings `(−1)^j, (−1)^k` are replaced by `1^j, 1^k`.  Bitwise application of
the gadget then turns block `i` into `(H(xᵢ), H(yᵢ))`, and Definition 2.21 /
Definition 2.3 evaluate `r ∘̃ h_G` on that block as `G(xᵢ, yᵢ)`, giving
`((r ∘̃ h_G) ∘ □)(X, Y) = (r ∘ G)(x, y)`.

The two combinatorial identities are proved below.  The resulting
communication lower bound is then a direct instance of the semantic law
"free local preprocessing does not increase communication complexity"
(`ComplexityProfile.QccStar_preprocess_le`, `UPPcc_preprocess_le`).
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.Lemma5_4

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.SymQueryComm20.MainResults.SourceModel
open Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

/-! ## Definition 2.21 on genuine Hadamard codewords -/

/-- The Hadamardisation of a pair of genuine Hadamard codewords is `G` of the
two sources (Definition 2.21 and `decodeHadamard_hadamardWord`). -/
theorem hadamardization_hadamardWord {l m : ℕ} (G : Cube l → Cube m → Bool)
    (x : Cube l) (y : Cube m) :
    hadamardization G (hadamardWord x, hadamardWord y) = some (G x y) := by
  unfold hadamardization
  rw [decodeHadamard_hadamardWord, decodeHadamard_hadamardWord]

/-! ## The preprocessing identities -/

/-- After Alice's and Bob's `AND₂` preprocessing, block `i` is exactly the pair
of Hadamard codewords `(H(xᵢ), H(yᵢ))` (proof of Lemma 5.4, p. 25). -/
theorem block_and {n l m : ℕ} (X : Word (Fin n × Fin l)) (Y : Word (Fin n × Fin m))
    (i : Fin n) :
    (fun a => and2 (prepAliceAnd (m := m) X (i, Sum.inl a)) (prepBobAnd (l := l) Y (i, Sum.inl a)),
     fun b => and2 (prepAliceAnd (m := m) X (i, Sum.inr b)) (prepBobAnd (l := l) Y (i, Sum.inr b)))
      = (hadamardWord (fun j => X (i, j)), hadamardWord (fun j => Y (i, j))) := by
  have h1 : (fun a => and2 (prepAliceAnd (m := m) X (i, Sum.inl a)) (prepBobAnd (l := l) Y (i, Sum.inl a)))
      = hadamardWord (fun j => X (i, j)) := by
    funext a
    simp [prepAliceAnd, prepBobAnd]
  have h2 : (fun b => and2 (prepAliceAnd (m := m) X (i, Sum.inr b)) (prepBobAnd (l := l) Y (i, Sum.inr b)))
      = hadamardWord (fun j => Y (i, j)) := by
    funext b
    simp [prepBobAnd, prepAliceAnd]
  rw [h1, h2]

/-- After Alice's and Bob's `XOR₂` preprocessing, block `i` is again exactly
the pair of Hadamard codewords `(H(xᵢ), H(yᵢ))`. -/
theorem block_xor {n l m : ℕ} (X : Word (Fin n × Fin l)) (Y : Word (Fin n × Fin m))
    (i : Fin n) :
    (fun a => xor2 (prepAliceXor (m := m) X (i, Sum.inl a)) (prepBobXor (l := l) Y (i, Sum.inl a)),
     fun b => xor2 (prepAliceXor (m := m) X (i, Sum.inr b)) (prepBobXor (l := l) Y (i, Sum.inr b)))
      = (hadamardWord (fun j => X (i, j)), hadamardWord (fun j => Y (i, j))) := by
  have h1 : (fun a => xor2 (prepAliceXor (m := m) X (i, Sum.inl a)) (prepBobXor (l := l) Y (i, Sum.inl a)))
      = hadamardWord (fun j => X (i, j)) := by
    funext a
    simp [prepAliceXor, prepBobXor]
  have h2 : (fun b => xor2 (prepAliceXor (m := m) X (i, Sum.inr b)) (prepBobXor (l := l) Y (i, Sum.inr b)))
      = hadamardWord (fun j => Y (i, j)) := by
    funext b
    simp [prepBobXor, prepAliceXor]
  rw [h1, h2]

/-- The `AND₂` reduction identity of Lemma 5.4:
`((r ∘̃ h_G) ∘ AND₂)(X, Y) = (r ∘ G)(x, y)` on the preprocessed inputs. -/
theorem reduction_and {n l m : ℕ} (r : Cube n → Bool) (G : Cube l → Cube m → Bool)
    (X : Word (Fin n × Fin l)) (Y : Word (Fin n × Fin m)) :
    composeWord r G X Y
      = composeWithInner (hadamardCompose r G) and2 (prepAliceAnd (m := m) X) (prepBobAnd (l := l) Y) := by
  have hval : ∀ i : Fin n, hadamardization G
      ((fun a => and2 (prepAliceAnd (m := m) X (i, Sum.inl a)) (prepBobAnd (l := l) Y (i, Sum.inl a)),
        fun b => and2 (prepAliceAnd (m := m) X (i, Sum.inr b)) (prepBobAnd (l := l) Y (i, Sum.inr b))))
      = some (G (fun j => X (i, j)) (fun j => Y (i, j))) := by
    intro i
    rw [block_and X Y i]
    exact hadamardization_hadamardWord G _ _
  unfold composeWord composeWithInner hadamardCompose partialCompose
  by_cases h : ∀ i : Fin n, ∃ b, hadamardization G
      ((fun a => and2 (prepAliceAnd (m := m) X (i, Sum.inl a)) (prepBobAnd (l := l) Y (i, Sum.inl a)),
        fun b => and2 (prepAliceAnd (m := m) X (i, Sum.inr b)) (prepBobAnd (l := l) Y (i, Sum.inr b)))) = some b
  · rw [dif_pos h]
    apply congrArg r
    funext i
    exact (Option.some.injEq _ _).mp
      ((hval i).symm.trans (Classical.choose_spec (h i)))
  · exact absurd (fun i => ⟨_, hval i⟩) h

/-- The `XOR₂` reduction identity of Lemma 5.4:
`((r ∘̃ h_G) ∘ XOR₂)(X, Y) = (r ∘ G)(x, y)` on the preprocessed inputs. -/
theorem reduction_xor {n l m : ℕ} (r : Cube n → Bool) (G : Cube l → Cube m → Bool)
    (X : Word (Fin n × Fin l)) (Y : Word (Fin n × Fin m)) :
    composeWord r G X Y
      = composeWithInner (hadamardCompose r G) xor2 (prepAliceXor (m := m) X) (prepBobXor (l := l) Y) := by
  have hval : ∀ i : Fin n, hadamardization G
      ((fun a => xor2 (prepAliceXor (m := m) X (i, Sum.inl a)) (prepBobXor (l := l) Y (i, Sum.inl a)),
        fun b => xor2 (prepAliceXor (m := m) X (i, Sum.inr b)) (prepBobXor (l := l) Y (i, Sum.inr b))))
      = some (G (fun j => X (i, j)) (fun j => Y (i, j))) := by
    intro i
    rw [block_xor X Y i]
    exact hadamardization_hadamardWord G _ _
  unfold composeWord composeWithInner hadamardCompose partialCompose
  by_cases h : ∀ i : Fin n, ∃ b, hadamardization G
      ((fun a => xor2 (prepAliceXor (m := m) X (i, Sum.inl a)) (prepBobXor (l := l) Y (i, Sum.inl a)),
        fun b => xor2 (prepAliceXor (m := m) X (i, Sum.inr b)) (prepBobXor (l := l) Y (i, Sum.inr b)))) = some b
  · rw [dif_pos h]
    apply congrArg r
    funext i
    exact (Option.some.injEq _ _).mp
      ((hval i).symm.trans (Classical.choose_spec (h i)))
  · exact absurd (fun i => ⟨_, hval i⟩) h

/-! ## Lemma 5.4 -/

/-- Lemma 5.4 (p. 25), `□ = AND₂`, `CC = Q^{cc,*}`:
`Q^{cc,*}((r ∘̃ h_G) ∘ AND₂) ≥ Q^{cc,*}(r ∘ G)`. -/
theorem lemma5_4_qcc_and (P : ComplexityProfile) (n l m : ℕ) (r : Cube n → Bool)
    (G : Cube l → Cube m → Bool) :
    P.QccStar n (Fin l) (Fin m) (composeWord r G)
      ≤ P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
          (composeWithInner (hadamardCompose r G) and2) :=
  P.QccStar_preprocess_le n (composeWithInner (hadamardCompose r G) and2) (composeWord r G)
    (prepAliceAnd (n := n) (l := l) (m := m)) (prepBobAnd (n := n) (l := l) (m := m))
    (fun X Y => reduction_and r G X Y)

/-- Lemma 5.4 (p. 25), `□ = XOR₂`, `CC = Q^{cc,*}`:
`Q^{cc,*}((r ∘̃ h_G) ∘ XOR₂) ≥ Q^{cc,*}(r ∘ G)`. -/
theorem lemma5_4_qcc_xor (P : ComplexityProfile) (n l m : ℕ) (r : Cube n → Bool)
    (G : Cube l → Cube m → Bool) :
    P.QccStar n (Fin l) (Fin m) (composeWord r G)
      ≤ P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
          (composeWithInner (hadamardCompose r G) xor2) :=
  P.QccStar_preprocess_le n (composeWithInner (hadamardCompose r G) xor2) (composeWord r G)
    (prepAliceXor (n := n) (l := l) (m := m)) (prepBobXor (n := n) (l := l) (m := m))
    (fun X Y => reduction_xor r G X Y)

/-- Lemma 5.4 (p. 25), `□ = AND₂`, `CC = UPP^{cc}`:
`UPP^{cc}((r ∘̃ h_G) ∘ AND₂) ≥ UPP^{cc}(r ∘ G)`. -/
theorem lemma5_4_upp_and (P : ComplexityProfile) (n l m : ℕ) (r : Cube n → Bool)
    (G : Cube l → Cube m → Bool) :
    P.UPPcc n (Fin l) (Fin m) (composeWord r G)
      ≤ P.UPPcc n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
          (composeWithInner (hadamardCompose r G) and2) :=
  P.UPPcc_preprocess_le n (composeWithInner (hadamardCompose r G) and2) (composeWord r G)
    (prepAliceAnd (n := n) (l := l) (m := m)) (prepBobAnd (n := n) (l := l) (m := m))
    (fun X Y => reduction_and r G X Y)

/-- Lemma 5.4 (p. 25), `□ = XOR₂`, `CC = UPP^{cc}`:
`UPP^{cc}((r ∘̃ h_G) ∘ XOR₂) ≥ UPP^{cc}(r ∘ G)`. -/
theorem lemma5_4_upp_xor (P : ComplexityProfile) (n l m : ℕ) (r : Cube n → Bool)
    (G : Cube l → Cube m → Bool) :
    P.UPPcc n (Fin l) (Fin m) (composeWord r G)
      ≤ P.UPPcc n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
          (composeWithInner (hadamardCompose r G) xor2) :=
  P.UPPcc_preprocess_le n (composeWithInner (hadamardCompose r G) xor2) (composeWord r G)
    (prepAliceXor (n := n) (l := l) (m := m)) (prepBobXor (n := n) (l := l) (m := m))
    (fun X Y => reduction_xor r G X Y)

end

end Qatlib.Papers.SymQueryComm20.MainResults.Lemma5_4
