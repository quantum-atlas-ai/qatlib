/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Native
import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan

/-!
# Collision-search endpoints and compact memory specifications

This module defines propositions for the general collision-search endpoint and for search with a
query bound uniform over admissible memory parameters. It also specifies a compact bit-register
layout and the modular value oracle acting on its address and answer fields [NielsenChuang2010].

`CompactMemorySpec` packages legal source circuits, memory and description bounds, and
value-loading semantics. `NearPrimePowerExists` records a separate arithmetic approximation
proposition used in the collision-search setting [Ambainis2007ElementDistinctness].

## Main statements

* `GeneralAlgorithmEndpoint`: the general memory-tradeoff and optimized-query contracts.
* `compactValueAction`: modular addition of an input value in a compact register.
* `CompactMemorySpec`: compact source-circuit implementation requirements.
* `NearPrimePowerExists`: approximation from above by even prime powers.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

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

/-- The conjunction of the general query-memory contract and the general optimized-query
contract. -/
def GeneralAlgorithmEndpoint : Prop :=
  GeneralQueryMemoryContract ∧ GeneralOptimizedQueriesContract

/-- The proposition that, for each `k ≥ 2`, one correct algorithm has the stated query bound for
every admissible `r` and an optimized-scale work-memory bound, with a positive constant
depending only on `k`. -/
def UnknownMassSearchSpec : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ Ck : ℝ, 0 < Ck ∧
    ∀ (N M : ℕ) [NeZero M], 0 < N → 0 < M →
      ∃ A : RandomQueryAlgorithm N M k,
        algorithmCorrect A ∧
        (∀ r : ℕ, k ≤ r → r ≤ N →
          ∀ s, (QueryCount (A.program s) : ℝ) ≤ Ck*queryScale k N r) ∧
        (A.workBits : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*dataBits N M

/-- The total number of address, answer, work, and `r` stored-value bits in the compact
register. -/
def compactWidth (N M r w : ℕ) : ℕ :=
  Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+w+r*Nat.clog 2 (M+1)

/-- The bit-register label formed by concatenating the address bits, answer bits, work bits, and
stored data bits. -/
def compactKet (N M r w : ℕ) (addr v : ℕ) (work data : ℕ → Bool) :
    Reg (compactWidth N M r w) :=
  let ab := Nat.clog 2 (N+1)
  let mb := Nat.clog 2 (M+1)
  fun i =>
    if i.val < ab then naturalBit addr i.val
    else if i.val < ab+mb then naturalBit v (i.val-ab)
    else if i.val < ab+mb+w then work (i.val-(ab+mb))
    else data (i.val-(ab+mb+w))

/-- Add the addressed input value modulo `M` to a valid answer field, preserving all other bits
and leaving invalid address or answer labels unchanged. -/
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

/-- The zero-one matrix sending each compact register label to its image under
`compactValueAction`. -/
def compactValueOracle {N M r w : ℕ} (x : Fin N → ZMod M) :
    Matrix (Reg (compactWidth N M r w)) (Reg (compactWidth N M r w)) ℂ :=
  fun y z => if y = compactValueAction x z then 1 else 0

/-- The proposition that legal unitary source circuits load a valid input value with one query,
the stated compact memory bound, and a polynomial instruction bit budget. -/
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

/-- The proposition that, for each `k ≥ 2`, every sufficiently large `N` lies below an even
power of a prime at most `(1+1/(2*k²))*N`. -/
def NearPrimePowerExists : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ q p a : ℕ, N ≤ q ∧ (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*N ∧
      Nat.Prime p ∧ 0 < a ∧ q = p^(2*a)

end Qatlib.Concepts.WalkFind.WalkSpectrum
