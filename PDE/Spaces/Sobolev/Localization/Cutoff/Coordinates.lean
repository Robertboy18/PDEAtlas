/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.Spaces.Sobolev.Localization.Cutoff.FixedPoints

/-!
# Stored coordinates of cutoff multiplication on the zero-trace space

The cutoff map preserves the zero trace. Its value and derivative
coordinates satisfy the product rule as equalities of `L²` elements.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The base coordinate of `cutoffH10 η u` is `ηu` in `L²`. -/
theorem baseCoordCLM_cutoffH10 (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(Ω)) :
    baseCoordCLM (cutoffH10 hΩ η u) =
      testFunctionLpTop (Ω := Ω) η • baseCoordCLM u := by
  change cutoffLpAt (p := 2) (Ω := Ω) η (baseIndex n 1)
    ((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) = _
  simp only [cutoffLpAt, firstOrderRows_baseIndex, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, mulLpLeft_apply]
  rfl

/-- The first coordinate derivatives of `cutoffH10 η u` satisfy the weak product rule
`∂ᵢ(ηu) = η ∂ᵢu + (∂ᵢη) u` in `L²`. -/
theorem derivCoordCLM_cutoffH10 (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(Ω)) (i : Fin n) :
    derivCoordCLM i (cutoffH10 hΩ η u) =
      testFunctionLpTop (Ω := Ω) η • derivCoordCLM i u +
        partialTestFunctionLpTop (Ω := Ω) η i • baseCoordCLM u := by
  change cutoffLpAt (p := 2) (Ω := Ω) η (singleDerivIndex n i)
    ((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) = _
  simp only [cutoffLpAt, firstOrderRows_singleDerivIndex, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, PiLp.proj_apply, cutoffDerivativeLp_apply]
  rfl

/-- Cutting off a smooth test agrees with its ordinary smooth product.
The equality holds in the zero-trace space, including all stored
weak derivative coordinates. -/
theorem cutoffH10_testFunction (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (φ : TestFunctionOn n Ω) :
    cutoffH10 hΩ η (testFunctionToH10 φ) =
      testFunctionToH10
        ⟨TestFunction.mul η φ.1, tsupport_mul_subset_right.trans φ.2⟩ := by
  apply baseCoordCLM_injective hΩ
  apply MeasureTheory.Lp.ext
  filter_upwards
    [cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Ω) η
        (testFunctionToH1 φ),
      baseCoordCLM_testFunction_apply_ae φ,
      baseCoordCLM_testFunction_apply_ae
        (⟨TestFunction.mul η φ.1, tsupport_mul_subset_right.trans φ.2⟩ :
          TestFunctionOn n Ω)] with x hcut hφ hproduct
  change baseCoordCLM (cutoffH10 hΩ η (testFunctionToH10 φ)) x =
    η.toFun x * baseCoordCLM (testFunctionToH10 φ) x at hcut
  rw [hcut, hφ, hproduct]
  rfl

/-- A cutoff fixes a zero-trace field when it fixes its base
representative almost everywhere. Weak derivative uniqueness supplies all
the other coordinates. -/
theorem cutoffH10_eq_self_of_base_ae (hΩ : IsOpen Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(Ω))
    (h : ∀ᵐ x ∂domainMeasure n Ω,
      χ.toFun x * baseCoordCLM u x = baseCoordCLM u x) :
    cutoffH10 hΩ χ u = u := by
  apply Subtype.ext
  exact cutoffCLM_eq_self_of_base_ae hΩ χ (u : H¹(Ω)) h

/-- A larger cutoff equal to one on the support of a smaller cutoff fixes
every field localized by the smaller one. -/
theorem cutoffH10_cutoffH10_of_eq_one (hΩ : IsOpen Ω)
    (χ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hχη : ∀ x ∈ tsupport η.toFun, χ.toFun x = 1) (u : H¹₀(Ω)) :
    cutoffH10 hΩ χ (cutoffH10 hΩ η u) = cutoffH10 hΩ η u := by
  apply cutoffH10_eq_self_of_base_ae
  filter_upwards [cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Ω) η
    (u : H¹(Ω))] with x hx
  change baseCoordCLM (cutoffH10 hΩ η u) x = η.toFun x * baseCoordCLM u x at hx
  rw [hx]
  by_cases hxη : x ∈ tsupport η.toFun
  · rw [hχη x hxη, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hxη, zero_mul, mul_zero]

end SobolevSpace.GraphSpace
