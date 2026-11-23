module

public import Qatlib.Papers.ReadManyQry11.MainResults.MatrixProductVerification

set_option autoImplicit false

namespace QatlibTests.ReadManyQry11MatrixProduct

open Qatlib.Papers.ReadManyQry11.MainResults

private def sample : BmpvInstance 1 where
  A := fun _ _ => true
  B := fun _ _ => true
  C := fun _ _ => true

/-- The explicit `1 × 1` positive instance is accepted by the verifier. -/
theorem sample_verifies : bmpv sample = true := by
  rw [bmpv_eq_true_iff]
  intro i j
  fin_cases i
  fin_cases j
  rfl

/-- The tagged entry-oracle consumer agrees with the direct matrix instance. -/
theorem sample_function_verifies :
    bmpvFun (fun x => match x with
      | Sum.inl ij => sample.A ij.1 ij.2
      | Sum.inr (Sum.inl ij) => sample.B ij.1 ij.2
      | Sum.inr (Sum.inr ij) => sample.C ij.1 ij.2) = true := by
  exact (bmpvFun_decode_eq_true_iff sample).2 (by
    intro i j
    fin_cases i
    fin_cases j
    rfl)

/-- The consumer can use the explicit positive-dimension domain witness. -/
theorem positive_domain : Nonempty (BmpvIndex 1) :=
  bmpvIndex_nonempty (by decide)

end QatlibTests.ReadManyQry11MatrixProduct
