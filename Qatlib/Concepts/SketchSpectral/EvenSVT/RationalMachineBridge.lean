/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.NumericsDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

/-!
# Rational-machine bridge for sketch arithmetic

`rational_sketch_ledger` identifies the cache plan's source reads, multiplications, and row
builds with the numerical sketch ledger. `rational_sketch_paid_native` realizes the rational
cache computation by a native Turing machine with explicit additional time, workspace, and
source-field counts, connecting machine costs to the sampling-based arithmetic setting of
[ChiaEtAl2022].

## Main statements

* `rational_sketch_ledger`: The rational matrix-job cache plan has source-read, multiplication,
  and row-build counts equal to the corresponding sketch arithmetic ledger fields.
* `rational_sketch_paid_native`: A native Turing machine extends the supplied input computation
  to execute the rational sketch cache program, producing the decoded rational result with the
  stated additional time, workspace bound, and ledger counts.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CacheOp
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open ConstructionStageB StageBSQNUMERICS
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

/-- The rational matrix-job cache plan has source-read, multiplication, and row-build counts
equal to the corresponding sketch arithmetic ledger fields. -/
theorem rational_sketch_ledger (matrixRows n q r c base : ℕ)
    (rows : Fin q → Fin r → Fin matrixRows) :
    let p := batchPlan n base (matrixJobs matrixRows n q r rows)
    cacheSourceReads p=(sketchArithmeticLedger n r c q).reads ∧
      cacheMultiplies p=(sketchArithmeticLedger n r c q).multiplies ∧
      cacheRowBuilds p=(sketchArithmeticLedger n r c q).cacheBuilds :=
  ⟨matrixJobs_reads matrixRows n q r base rows,
   matrixJobs_multiplies matrixRows n q r base rows,
   matrixJobs_row_builds matrixRows n q r base rows⟩

/-- A native Turing machine extends the supplied input computation to execute the rational
sketch cache program, producing the decoded rational result with the stated additional time,
workspace bound, and ledger counts. -/
theorem rational_sketch_paid_native (a : ℕ) (P : TM0.Machine Symbol (Fin (a+1))) :
    ∃ (states : ℕ) (K : TM0.Machine Symbol (Fin (states+1))) (C : ℕ),0 < C ∧
      ∀ (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
        (A : Fin matrixRows → Fin n → GaussianCode) (X : Fin q → Fin n → GaussianCode)
        (choice : Option (ℕ × Option ℕ)) (B : ℕ) (raw : Bits) (Ts Ss : ℕ),
      let cs := matrixInputs A X
      let jobs := matrixJobs matrixRows n q r rows
      let p := batchPlan n cs.length jobs
      let output := batchChoiceOutput n cs.length (matrixRows*n+q*n) choice
      (∀ i j,(A i j).Valid) → (∀ i j,(X i j).Valid) → batchChoiceValid n (q*r) choice →
      PayloadBound B (cacheOutputProgram p output) ⟨encodeCache cs,[]⟩ →
      Runs P raw (cacheInput p cs output) Ts Ss →
      ∃ (cf : List GaussianCode) (ps' : List Bits),
      cacheRun (matrixRows*n) p cs=some cf ∧ CacheRep ps' cf ∧
      Runs K raw (cacheOutput ps' output)
        (Ts+C*cachePolynomialTime p cs output B+1) (max Ss (C*cachePolynomialWork p cs output B)) ∧
      (decodeGaussian (cacheOutput ps' output)).1.decode=
        batchRatValue n (matrixRows*n+q*n) jobs (cs.map GaussianCode.decode) choice ∧
      (decodeGaussian (cacheOutput ps' output)).2=[] ∧
      cacheSourceReads p=(sketchArithmeticLedger n r 0 q).reads ∧
      cacheMultiplies p=(sketchArithmeticLedger n r 0 q).multiplies ∧
      cacheRowBuilds p=(sketchArithmeticLedger n r 0 q).cacheBuilds ∧
      (cacheOutputProgram p output).countP (sourceField (matrixRows*n))=
        5*(sketchArithmeticLedger n r 0 q).reads ∧
      cachePolynomialWork p cs output B ≤ 625*(1+(cacheInput p cs output).length)^4*(B+1)^4 := by
  obtain ⟨b,N,C,hC,hN⟩ := frontier1
  refine ⟨(a+1)+b,composeMachine (a:=a) (b:=b) P N,C,hC,?_⟩
  intro matrixRows n q r rows A X choice B raw Ts Ss
  (try dsimp only)
  intro hA hX hc hb hP
  obtain ⟨cf,ps',hR,hRep,hNative,hV,hTail,hField,hRead,hMul,hBuild,hPoly,_⟩ :=
    hN matrixRows n q r rows A X choice B hA hX hc hb
  refine ⟨cf,ps',hR,hRep,@paid_plan a b P N raw _ _ Ts Ss _ _ hP hNative,hV,hTail,
    hRead,hMul,hBuild,?_,hPoly⟩
  exact hField.trans (by simp only [sketchArithmeticLedger]; ring)

end Qatlib.Concepts.SketchSpectral.EvenSVT
