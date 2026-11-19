/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Examples.Elliptic.Quasilinear.Interior.QuadraticData
public import PDE.Elliptic.Regularity.Quasilinear.Interior.GradientDensity

/-!
# Interior regularity with nonzero boundary data and a signed density

The interior regularity theorem `exists_interior_H2_of_gradientDensity`, for densities
with Hessian between `3/4` and `5/4`, applies to the weak solution `u = x²` of
`exists_quadratic_weakSolution`. On every open `V` compactly contained in a bounded
open `Ω ⊆ ℝ`, `u` lies in `H²(V)` with the interior estimates
(`exists_quadratic_interior_H2`). The density has nonzero value and gradient at the
origin, the load is nonzero, and `u` equals one at both endpoints of the unit
interval.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Quasilinear.Interior

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Examples.GradientEnergy PDE.Elliptic.Regularity.Quasilinear
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

/-- For every open `V` compactly contained in a bounded open `Ω ⊆ ℝ`, the weak solution
`x²` lies in `H²(V)` with both interior estimates, and every test integrand of the weak
equation is integrable. -/
theorem exists_quadratic_interior_H2 {Ω V : Set (ℝ^1)}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ K : ℝ, 0 < K ∧
      ∃ (u : H¹(Ω)) (f : DerivLp 1 2 Ω) (W : W^{2,2}(V)),
        baseRepresentative u =ᵐ[domainMeasure 1 Ω] quadratic ∧
        (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω] quadraticLoad ∧
        lowerOrderCLM (by omega : 1 ≤ 2) W =
          restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
        ‖W‖ ≤ K * (‖u‖ + ‖f‖) ∧
        (∑ i : Fin 1, ∑ j : Fin 1, ‖W.val (pairDerivIndex 1 i j)‖) ≤
          K * (‖∇ u‖ + ‖f‖) ∧
        ∀ v : H¹₀(Ω),
          Integrable (fun x ↦
            ⟪gradient signedDensity (∇ u x), ∇ (v : H¹(Ω)) x⟫)
            (domainMeasure 1 Ω) ∧
          Integrable (fun x ↦ f x * baseCoordCLM v x) (domainMeasure 1 Ω) := by
  obtain ⟨K, hK, hreg⟩ := exists_interior_H2_of_gradientDensity
    hΩ hbounded hV hVc hVΩ (by norm_num : (0 : ℝ) < 3 / 4) (5 / 4)
  obtain ⟨u, f, hu, hf, hweak⟩ := exists_quadratic_weakSolution hΩ hbounded
  obtain ⟨W, hW, hnorm, hsecond, htest⟩ := hreg signedDensity
    signedDensity_contDiff signedDensity_hessian_upper signedDensity_hessian_lower
    u f hweak
  exact ⟨K, hK, u, f, W, hu, hf, hW, hnorm, hsecond, htest⟩

end PDE.Examples.Quasilinear.Interior
