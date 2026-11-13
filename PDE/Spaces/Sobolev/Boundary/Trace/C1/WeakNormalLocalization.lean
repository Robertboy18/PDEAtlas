/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeakNormal
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianTest
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates
public import PDE.FDeriv.Calculus
public import PDE.FDeriv.Laplacian.Congruence
public import PDE.FDeriv.PartialDeriv.Support

/-!
# Smooth evaluation and localization of weak normal traces

The quotient normal trace evaluates on a smooth test by the volume Green
pairing. If a cutoff equals one near the support of that test, localization
of both the field and its actual Poisson load leaves this evaluation unchanged.
No boundary value of the weak gradient is used.
-/

@[expose] public noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions Sobolev Topology InnerProductSpace
open PDE (laplacian iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

/-- The variational weak Laplacian identity implies the compact-test identity. -/
theorem integral_laplacian_eq_of_weakForm {n : ℕ} {Ω : Set ℝ^n}
    (u : H¹(Ω)) (f : DerivLp n 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) u)
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))
    (φ : TestFunctionOn n Ω) :
    (∫ x, baseRepresentative u x * laplacian φ.1.toFun x ∂domainMeasure n Ω) =
      ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω := by
  have h := huf (testFunctionToH10 φ)
  change (∑ i, inner ℝ ((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i))
    (derivCoordCLM i (testFunctionToH10 φ))) = _ at h
  rw [sum_inner_deriv_test_eq_neg_integral_laplacian,
    inner_base_testFunction_eq_integral] at h
  exact neg_injective h

/-- The canonical Sobolev gradient of an ambient test is its classical gradient. -/
theorem wkpGradientCLM_globalTestFunctionToWkpOn_ae
    {n : ℕ} {Ω : Set ℝ^n} (φ : 𝓓((⊤ : Opens ℝ^n), ℝ)) :
    (wkpGradientCLM (globalTestFunctionToWkpOn (Ω := Ω) (p := 2) φ) : ℝ^n → ℝ^n) =ᵐ[
      domainMeasure n Ω] gradient φ.toFun := by
  filter_upwards [wkpGradientCLM_apply_ae
      (globalTestFunctionToWkpOn (Ω := Ω) (p := 2) φ),
    ae_all_iff.mpr (fun i ↦ globalTestFunctionToWkpOn_coordinate_ae
      (Ω := Ω) (p := 2) φ (singleDerivIndex n i))] with x hx hφ
  ext i
  rw [hx i, hφ i, PDE.gradient_apply_eq_partialDeriv]
  simp only [singleDerivIndex_toList, iteratedPartialDeriv]

end SobolevSpace.GraphSpace

namespace SobolevSpace.Trace.C1

open GraphSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A smooth lifting evaluates the weak normal derivative by the actual volume Green pairing. -/
theorem weakNormalTrace_globalTestFunctionToWkpOn
    (u : H¹(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))
    (φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) :
    weakNormalTrace u f huf (traceClass (globalTestFunctionToWkpOn φ)) =
      (∫ x, (f : ℝ^(m + 1) → ℝ) x * φ.toFun x ∂domainMeasure (m + 1) Ω) +
        ∫ x, inner ℝ ((wkpGradientCLM u : ℝ^(m + 1) → ℝ^(m + 1)) x)
          (gradient φ.toFun x) ∂domainMeasure (m + 1) Ω := by
  rw [weakNormalTrace_traceClass, L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [globalTestFunctionToWkpOn_coordinate_ae
      (Ω := Ω) (p := 2) φ (baseIndex (m + 1) 1)] with x hx
    simp only [baseIndex_toList, iteratedPartialDeriv] at hx
    change ((globalTestFunctionToWkpOn (Ω := Ω) (k := 1) (p := 2) φ :
      WkpAmbientOn (m + 1) 1 2 Ω) (baseIndex (m + 1) 1)) x * f x = _
    rw [hx]
    exact mul_comm (φ.toFun x) (f x)
  · apply integral_congr_ae
    filter_upwards [wkpGradientCLM_globalTestFunctionToWkpOn_ae (Ω := Ω) φ] with x hx
    rw [hx]

/-- A cutoff equal to one near the test support preserves the weak normal evaluation.
The localized load is the actual distributional product-rule load. -/
theorem weakNormalTrace_cutoffH10_eq
    (hΩ : IsOpen Ω) (z : H¹₀(Ω)) (f g : DerivLp (m + 1) 2 Ω)
    (η φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ))
    (hη : ∀ x ∈ tsupport φ.toFun, η.toFun =ᶠ[𝓝 x] (fun _ ↦ 1))
    (hg : (g : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] fun x ↦
      η.toFun x * f x +
        2 * ∑ i, (∂[i] η.toFun) x * derivCoordCLM i z x +
        baseCoordCLM z x * laplacian η.toFun x)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (z : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))
    (hug : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i)
        (cutoffH10 hΩ η z : H¹(Ω))) (derivCoordCLM i v)) =
          -inner ℝ g (baseCoordCLM v)) :
    weakNormalTrace (cutoffH10 hΩ η z : H¹(Ω)) g hug
        (traceClass (globalTestFunctionToWkpOn φ)) =
      weakNormalTrace (z : H¹(Ω)) f huf (traceClass (globalTestFunctionToWkpOn φ)) := by
  have hη0 (x : ℝ^(m + 1)) (hx : x ∈ tsupport φ.toFun) :
      η.toFun x = 1 := (hη x hx).eq_of_nhds
  have hη1 (x : ℝ^(m + 1)) (hx : x ∈ tsupport φ.toFun) (i : Fin (m + 1)) :
      (∂[i] η.toFun) x = 0 := by
    rw [PDE.partialDeriv_congr_nhds i (hη x hx)]
    simp only [PDE.partialDeriv_const]
  have hη2 (x : ℝ^(m + 1)) (hx : x ∈ tsupport φ.toFun) :
      laplacian η.toFun x = 0 := by
    rw [EuclideanLaplacian.laplacian_congr_nhds (hη x hx), PDE.laplacian_const]
  rw [weakNormalTrace_traceClass, weakNormalTrace_traceClass,
    inner_wkpGradientCLM_eq_sum, inner_wkpGradientCLM_eq_sum]
  congr 1
  · rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg, globalTestFunctionToWkpOn_coordinate_ae
      (Ω := Ω) (p := 2) φ (baseIndex (m + 1) 1)] with x hx hφ
    simp only [baseIndex_toList, iteratedPartialDeriv] at hφ
    change ((globalTestFunctionToWkpOn (Ω := Ω) (k := 1) (p := 2) φ :
      WkpAmbientOn (m + 1) 1 2 Ω) (baseIndex (m + 1) 1)) x * g x =
        ((globalTestFunctionToWkpOn (Ω := Ω) (k := 1) (p := 2) φ :
          WkpAmbientOn (m + 1) 1 2 Ω) (baseIndex (m + 1) 1)) x * f x
    rw [hφ]
    by_cases hs : x ∈ tsupport φ.toFun
    · rw [hx, hη0 x hs, hη2 x hs]
      simp only [hη1 x hs, one_mul, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cutoffCLM_singleDeriv_apply_ae η (z : H¹(Ω)) i,
      globalTestFunctionToWkpOn_coordinate_ae
        (Ω := Ω) (p := 2) φ (singleDerivIndex (m + 1) i)] with x hx hφ
    simp only [singleDerivIndex_toList, iteratedPartialDeriv] at hφ
    change ((globalTestFunctionToWkpOn (Ω := Ω) (k := 1) (p := 2) φ :
      WkpAmbientOn (m + 1) 1 2 Ω) (singleDerivIndex (m + 1) i)) x *
        ((cutoffCLM η (z : H¹(Ω)) : WkpAmbientOn (m + 1) 1 2 Ω)
          (singleDerivIndex (m + 1) i)) x =
            ((globalTestFunctionToWkpOn (Ω := Ω) (k := 1) (p := 2) φ :
              WkpAmbientOn (m + 1) 1 2 Ω) (singleDerivIndex (m + 1) i)) x *
                derivCoordCLM i z x
    rw [hφ, hx]
    change (∂[i] φ.toFun) x *
      (η.toFun x * derivCoordCLM i z x + (∂[i] η.toFun) x * baseCoordCLM z x) =
        (∂[i] φ.toFun) x * derivCoordCLM i z x
    by_cases hs : x ∈ tsupport φ.toFun
    · rw [hη0 x hs, hη1 x hs, one_mul, zero_mul, add_zero]
    · rw [PDE.partialDeriv_eq_zero_of_notMem_tsupport i hs, zero_mul, zero_mul]

end SobolevSpace.Trace.C1
