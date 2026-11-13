/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Localization.Cutoff.FirstOrderBounds
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff -- shake: keep

/-!
# Higher-order cutoff operators

Smooth cutoff multiplication on `W^{k,2}(Ω)` is the bounded
`W^{k,∞}` multiplier associated with the cutoff. The higher-order multiplier
bounds transfer to it, and at order one it agrees with the first-order cutoff
operator `cutoffCLM`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.GraphSpace

open MeasureTheory Set

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- A global test function, restricted to `Ω` and viewed as a
`W^{k,∞}(Ω)` multiplier. -/
noncomputable abbrev globalTestFunctionToWkTopOn
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{k,∞}(Ω) :=
  globalTestFunctionToWkpOn
    (n := n) (k := k) (p := ∞) (Ω := Ω) ψ

/-- The base representative of a global test function regarded as a
`W^{k,∞}(Ω)` coefficient is the original smooth function. -/
theorem globalTestFunctionToWkTopOn_base_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    baseRepresentative
        (globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := Ω) ψ)
      =ᵐ[domainMeasure n Ω] ψ.toFun := by
  simpa [globalTestFunctionToWkTopOn, baseRepresentative,
    baseIndex_toList, iteratedPartialDeriv] using
    (globalTestFunctionToWkpOn_coordinate_ae
      (n := n) (k := k) (p := ∞) (Ω := Ω) ψ (baseIndex n k))

/-- Multiplication by a smooth cutoff as a bounded endomorphism of
`W^{k,2}(Ω)`. -/
noncomputable def higherOrderCutoffCLM
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω) :=
  wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen
    (globalTestFunctionToWkTopOn
      (n := n) (k := k) (Ω := Ω) ψ)

/-- The higher-order cutoff operator evaluates to the canonical
`W^{k,∞}`-by-`W^{k,2}` Sobolev product. -/
@[simp]
theorem higherOrderCutoffCLM_apply
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,2}(Ω)) :
    higherOrderCutoffCLM (n := n) (Ω := Ω) hk hΩopen ψ U =
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen
        (globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := Ω) ψ) U := by
  simp [higherOrderCutoffCLM]

/-- The base representative of the higher-order cutoff operator is the
pointwise product of the cutoff and the input representative. -/
theorem higherOrderCutoffCLM_base_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,2}(Ω)) :
    baseRepresentative
        (higherOrderCutoffCLM
          (n := n) (Ω := Ω) hk hΩopen ψ U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * baseRepresentative U x := by
  rw [higherOrderCutoffCLM_apply]
  filter_upwards
    [wkTopProduct_base_ae
      (n := n) (Ω := Ω) hk hΩopen
      (globalTestFunctionToWkTopOn
        (n := n) (k := k) (Ω := Ω) ψ) U,
    globalTestFunctionToWkTopOn_base_ae
      (n := n) (k := k) (Ω := Ω) ψ] with x hproduct hψ
  rw [hproduct, hψ]

/-- Graph-norm estimate for higher-order smooth cutoff multiplication. -/
theorem norm_higherOrderCutoffCLM_apply_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,2}(Ω)) :
    ‖higherOrderCutoffCLM (n := n) (Ω := Ω) hk hΩopen ψ U‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := Ω) ψ‖ * ‖U‖ := by
  exact norm_wkTopMultiplierCLM_apply_le
    (n := n) (Ω := Ω) hk hΩopen
    (globalTestFunctionToWkTopOn
      (n := n) (k := k) (Ω := Ω) ψ) U

/-- Operator-norm estimate for higher-order smooth cutoff multiplication. -/
theorem norm_higherOrderCutoffCLM_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖higherOrderCutoffCLM (n := n) (Ω := Ω) hk hΩopen ψ‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := Ω) ψ‖ := by
  exact norm_wkTopMultiplierCLM_le
    (n := n) (Ω := Ω) hk hΩopen
    (globalTestFunctionToWkTopOn
      (n := n) (k := k) (Ω := Ω) ψ)

/-- At order one, the canonical higher-order cutoff operator agrees with
the first-order cutoff operator on `H¹(Ω)`. -/
theorem higherOrderCutoffCLM_one_eq_cutoffCLM
    (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    higherOrderCutoffCLM
        (n := n) (k := 1) (Ω := Ω) (by omega) hΩopen ψ =
      cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ := by
  apply ContinuousLinearMap.ext
  intro U
  rw [higherOrderCutoffCLM_apply,
    cutoffCLM_eq_w1TopMultiplierCLM
      (n := n) (Ω := Ω) hΩopen ψ]
  simpa [globalTestFunctionToWkTopOn, globalTestFunctionToW1TopOn] using
    (wkTopProduct_one_eq_w1TopMultiplierCLM
      (n := n) (Ω := Ω) hΩopen
      (globalTestFunctionToWkpOn
        (n := n) (k := 1) (p := ∞) (Ω := Ω) ψ) U)

end SobolevSpace.GraphSpace
