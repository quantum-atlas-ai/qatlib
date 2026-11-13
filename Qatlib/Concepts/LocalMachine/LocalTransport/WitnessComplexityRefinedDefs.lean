/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

/-!
# Refined witness complexity predicates

`WcWitnessLengthLedger` and `WcOracleAccessBudget` express width consistency and oracle
instruction accounting for uniform verifier families. `WcDiagonalDensity`, `WcDiagonalPart`, and
`WcOffDiagonalPart` isolate classical diagonal contributions of witness matrices without
imposing density conditions themselves.

`WcClassicalAcceptFunctional` requires acceptance to depend only on real diagonal weights. Its
family and language versions record the extra hypotheses used to transfer classical-witness
soundness to general witness densities. See [MarriottWatrous2005] for the quantum-proof context.

## Main definitions

* `WcWitnessLengthLedger`: agreement of generated and family witness widths.
* `WcClassicalAcceptFunctional`: a diagonal formula for every witness matrix.
* `WcDiagonalAcceptLanguage`: the diagonal-functional condition for families satisfying
  classical completeness and soundness.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

/-- The witness width assigned by a uniform family to an input length. -/
def WcWitnessWidth (f : UniformWitnessFamily) (n : ℕ) : ℕ := f.witnessWidth n

/-- The length of the oracle access ledger of the verifier generated for an input. -/
def WcOracleAccessCount (f : SharedOracleUniformFamily) (x : List Bool) : ℕ :=
  (oracleAccessLedger (f.generator x)).length

/-- States that the generated verifier's oracle access count is at most its instruction count. -/
def WcOracleAccessBudget (f : SharedOracleUniformFamily) (x : List Bool) : Prop :=
  WcOracleAccessCount f x ≤ (f.generator x).instructions.length

/-- States that each generated verifier's witness width agrees with the family width at the
input length. -/
def WcWitnessLengthLedger (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool, (f.generator x).witnessBits = WcWitnessWidth f x.length

/-- States that every off-diagonal entry of a witness matrix is zero, without imposing
positivity or normalization. -/
def WcDiagonalDensity {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Prop :=
  ∀ w w' : Reg m, w ≠ w' → σ w w' = 0

/-- States that acceptance of every witness matrix equals the sum of its real diagonal weights
times classical witness acceptance values. -/
def WcClassicalAcceptFunctional (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) : Prop :=
  ∀ σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ,
    acceptProb A p x σ
      = ∑ w : Reg p.witnessBits,
        (σ w w).re * acceptProb A p x (classicalWitnessDensity w)

/-- Builds a verifier with zero witness bits and the supplied input width, ancilla width, output
index, and instructions. -/
def WcEmptyWitnessProgram (iB aB oB : ℕ) (instrs : List WitnessInstruction) :
    WitnessVerifierProgram where
  witnessBits := 0
  inputBits := iB
  ancillaBits := aB
  outputWire := oB
  instructions := instrs

/-- The matrix retaining the diagonal entries of a witness matrix and setting all other entries
to zero. -/
def WcDiagonalPart {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  fun i j => if i = j then σ i i else 0

/-- The difference between a witness matrix and its diagonal part. -/
def WcOffDiagonalPart {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  fun i j => σ i j - (if i = j then σ i i else 0)

/-- Reindexes a Boolean witness register along an equality of register widths. -/
def WcWitnessReindex {w g : ℕ} (hw : g = w) : Reg w → Reg g :=
  fun v => fun k => v (Fin.cast hw k)

/-- Requires every generated verifier, at its corresponding input, to have a classical diagonal
acceptance functional under the constantly false oracle. -/
def WcDiagonalAcceptFamily (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool,
    WcClassicalAcceptFunctional (fun _ _ => false) (f.generator x)
      (listToInput (f.generator x) x)

/-- Requires every uniform family satisfying the language's classical completeness and soundness
conditions to satisfy `WcDiagonalAcceptFamily`. -/
def WcDiagonalAcceptLanguage (L : BitLanguage) : Prop :=
  ∀ (f : UniformWitnessFamily),
    (∀ x : List Bool, L.yes x = true →
      ∃ w : Reg (f.witnessWidth x.length),
        2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w)) →
    (∀ x : List Bool, L.no x = true →
      ∀ w : Reg (f.witnessWidth x.length),
        uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w) ≤ 1 / 3) →
    WcDiagonalAcceptFamily f

end Qatlib.Concepts.LocalMachine.LocalTransport
