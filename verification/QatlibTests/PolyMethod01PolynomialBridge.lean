module

public import Qatlib.Papers.PolyMethod01.MainResults.PolynomialMethodBridge

set_option autoImplicit false

namespace QatlibTests.PolyMethod01PolynomialBridge

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
open Qatlib.Papers.PolyMethod01.MainResults
open Qatlib.Papers.PolyMethod01.MainResults

/-- An ordinary module consumer invokes the tight OR polynomial-method theorem. -/
example (n : ℕ) :
    n ≤ 2 * exactMinimum (@orValue n) ∧
      exactMinimum (@orValue n) = n ∧
      exactDegree (@orValue n) = n :=
  or_polynomial_method_main n

end QatlibTests.PolyMethod01PolynomialBridge
