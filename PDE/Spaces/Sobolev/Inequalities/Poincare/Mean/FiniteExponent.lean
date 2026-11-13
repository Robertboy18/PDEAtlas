/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.FiniteExponent
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Compactness

/-!
# Mean-subtracted Poincaré from the Rellich theorem

The compact base-coordinate map on a C1 extension domain and the connected-domain
zero-gradient theorem give the mean-subtracted estimate. The `L¹` theorem works in every
positive dimension; the finite-exponent Rellich theorem covers every `p ≥ 1` in dimension
at least two. The one-dimensional remaining exponents are treated using the critical embedding.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Mean subtraction gives a gradient bound for the full `W¹¹` norm on a connected
C1 extension domain. Compactness is supplied by the Rellich theorem. -/
theorem exists_norm_subtractMean_le_one_of_c1Domain (hconn : IsConnected Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,1}(Ω),
      ‖subtractMean U‖ ≤ C * ‖∇ U‖ := by
  apply exists_norm_subtractMean_le_of_compact_estimate hΩ.isOpen hconn
    wkpBaseCoordinateCLM RellichKondrachov.baseCoordinateL1_isCompactOperator_of_c1Domain
    1 n
  intro U
  simpa only [NNReal.coe_one, NNReal.coe_natCast, one_mul] using norm_le_base_add_gradient U

/-- At every finite exponent, a connected C1 extension domain of dimension at least two
satisfies the mean-subtracted Poincaré estimate, with no compactness premise. -/
theorem exists_norm_subtractMean_le_finite_of_c1Domain
    (hn : 2 ≤ n) (hconn : IsConnected Ω) {p : ℝ≥0} [hp : Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,(p : ℝ≥0∞)}(Ω),
      ‖subtractMean U‖ ≤ C * ‖∇ U‖ := by
  apply exists_norm_subtractMean_le_of_compact_estimate hΩ.isOpen hconn
    wkpBaseCoordinateCLM
    (RellichKondrachov.baseCoordinate_isCompactOperator_of_c1Domain hn) 1 n
  intro U
  simpa only [NNReal.coe_one, NNReal.coe_natCast, one_mul] using norm_le_base_add_gradient U

end SobolevSpace.GraphSpace
