/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CipherCircuits.CipherOracle

namespace Qatlib.Papers.GroverAES15.KeyPredicate
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.CipherCircuits.CipherOracle
variable {K : Type*} {r : ℕ}

abbrev Block := Fin 128 → Bool

def transcript (enc : K → Block → Block) (texts : Fin r → Block) (key : K) :
    Bank (Fin r × Fin 128) := fun ij => enc key (texts ij.1) ij.2

def target (ciphertexts : Fin r → Block) : Bank (Fin r × Fin 128) :=
  fun ij => ciphertexts ij.1 ij.2

theorem transcript_eq_target (enc : K → Block → Block) (texts ciphertexts : Fin r → Block)
    (key : K) :
    transcript enc texts key = target ciphertexts ↔ ∀ i, enc key (texts i) = ciphertexts i := by
  constructor
  · intro h i
    funext j
    exact congrFun h (i,j)
  · intro h
    funext ⟨i,j⟩
    exact congrFun (h i) j
variable [Fintype K]

def marked (enc : K → Block → Block) (texts ciphertexts : Fin r → Block) : Finset K :=
  Finset.univ.filter (fun key => transcript enc texts key = target ciphertexts)

theorem mem_marked (enc : K → Block → Block) (texts ciphertexts : Fin r → Block) (key : K) :
    key ∈ marked enc texts ciphertexts ↔ ∀ i, enc key (texts i) = ciphertexts i := by
  simp [marked, transcript_eq_target]

theorem secret_mem (enc : K → Block → Block) (texts : Fin r → Block) (secret : K) :
    secret ∈ marked enc texts (fun i => enc secret (texts i)) := by
  simp [mem_marked]

theorem marked_nonempty (enc : K → Block → Block) (texts : Fin r → Block) (secret : K) :
    0 < (marked enc texts (fun i => enc secret (texts i))).card :=
  Finset.card_pos.mpr ⟨secret, secret_mem enc texts secret⟩
end
end Qatlib.Papers.GroverAES15.KeyPredicate
