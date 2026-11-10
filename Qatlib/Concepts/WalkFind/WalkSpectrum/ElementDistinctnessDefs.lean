/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Native
import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
open Qatlib
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum
namespace Qatlib.Concepts.WalkFind.WalkSpectrum

def GeneralAlgorithmEndpoint : Prop :=
  GeneralQueryMemoryContract ∧ GeneralOptimizedQueriesContract

def UnknownMassSearchSpec : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ Ck : ℝ, 0 < Ck ∧
    ∀ (N M : ℕ) [NeZero M], 0 < N → 0 < M →
      ∃ A : RandomQueryAlgorithm N M k,
        algorithmCorrect A ∧
        (∀ r : ℕ, k ≤ r → r ≤ N →
          ∀ s, (QueryCount (A.program s) : ℝ) ≤ Ck*queryScale k N r) ∧
        (A.workBits : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*dataBits N M

def compactWidth (N M r w : ℕ) : ℕ :=
  Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+w+r*Nat.clog 2 (M+1)

def compactKet (N M r w : ℕ) (addr v : ℕ) (work data : ℕ → Bool) :
    Reg (compactWidth N M r w) :=
  let ab := Nat.clog 2 (N+1)
  let mb := Nat.clog 2 (M+1)
  fun i =>
    if i.val < ab then naturalBit addr i.val
    else if i.val < ab+mb then naturalBit v (i.val-ab)
    else if i.val < ab+mb+w then work (i.val-(ab+mb))
    else data (i.val-(ab+mb+w))

def compactValueAction {N M r w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w)) : Reg (compactWidth N M r w) :=
  let ab := Nat.clog 2 (N+1)
  let mb := Nat.clog 2 (M+1)
  let address := addressValue ψ 0 ab
  let answer := addressValue ψ ab mb
  if ha : address < N then
    if answer < M then
      let result := (answer+(x ⟨address,ha⟩).val) % M
      fun i => if ab ≤ i.val ∧ i.val < ab+mb then naturalBit result (i.val-ab) else ψ i
    else ψ
  else ψ

def compactValueOracle {N M r w : ℕ} (x : Fin N → ZMod M) :
    Matrix (Reg (compactWidth N M r w)) (Reg (compactWidth N M r w)) ℂ :=
  fun y z => if y = compactValueAction x z then 1 else 0

def CompactMemorySpec : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (Ck : ℝ) (c : ℕ), 0 < Ck ∧
    ∀ (N M r : ℕ) [NeZero M], 0 < N → 0 < M → k ≤ r → r ≤ N →
      ∃ (w : ℕ) (word : List SourceCode),
        let b := compactWidth N M r w
        ((b : ℝ) ≤ Ck*dataBits N M*(r+1)) ∧
        sourceWordLegal b word ∧
        IsUnitaryCircuit (sourceCircuit b word) ∧
        QueryCount (sourceCircuit b word) = 1 ∧
        (((word.map codeBits).sum : ℝ) ≤ Ck*(dataBits N M+1)^c) ∧
        ∀ x : Fin N → ZMod M,
          (compactValueOracle (N := N) (M := M) (r := r) (w := w) x ∈
            Matrix.unitaryGroup (Reg b) ℂ) ∧
          ∀ (i : Fin N) (work data : ℕ → Bool),
            Run (compactValueOracle (N := N) (M := M) (r := r) (w := w) x)
              (sourceCircuit b word) (Qatlib.Foundations.PureStateMath.Ket (compactKet N M r w i.val 0 work data)) =
            Qatlib.Foundations.PureStateMath.Ket (compactKet N M r w i.val (x i).val work data)

def NearPrimePowerExists : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ q p a : ℕ, N ≤ q ∧ (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*N ∧
      Nat.Prime p ∧ 0 < a ∧ q = p^(2*a)

end Qatlib.Concepts.WalkFind.WalkSpectrum
