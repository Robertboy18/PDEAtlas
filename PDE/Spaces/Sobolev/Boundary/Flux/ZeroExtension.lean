/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.Laplacian
public import PDE.Elliptic.Regularity.Boundary.Rellich.WeakNormalSurface
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# The boundary source in the Laplacian of a zero extension

A zero-trace Poisson field extends to a whole-space H¹ function. Its
Laplacian is the volume load minus the surface distribution of its outward
weak normal density. The identity uses the actual zero extension and does
not assign a boundary value to its gradient.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set TopologicalSpace GraphSpace GraphSpace.ZeroTrace
open Boundary.Geometry.SurfaceMeasure
open scoped Distributions ENNReal Sobolev Laplacian

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Let `w ∈ H¹₀(Ω)` solve `Δw = f` weakly for `f ∈ L²(Ω)`, that is
`∑ᵢ ⟨∂ᵢw, ∂ᵢv⟩ = -⟨f, v⟩` for all `v ∈ H¹₀(Ω)`, and let `q ∈ L²(∂Ω)` represent its weak normal
trace: `weakNormalTrace w f huf z = ∫_{∂Ω} q (boundaryValue z) dS` for every `z` in the trace
space. Then, as distributions on `ℝ^(m+1)`, the Laplacian of the zero extension of `w` is `f dx`
on `Ω` minus `q dS`. -/
theorem laplacian_zeroExtendH10_eq_volume_sub_surface
    (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))
    (q : BoundaryL2 (Ω := Ω))
    (hq : ∀ z : HilbertTraceSpace (Ω := Ω),
      weakNormalTrace (w : H¹(Ω)) f huf z =
        ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω) :
    Δ (Distribution.ofFun ⊤
      (baseRepresentative (zeroExtendH10 H.isOpen.measurableSet w)) volume ⊤) =
        Distribution.ofFun ⊤ (f : ℝ^(m + 1) → ℝ) (domainMeasure (m + 1) Ω) ⊤ -
          Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ := by
  let W := zeroExtendH10 H.isOpen.measurableSet w
  have hW : LocallyIntegrable (baseRepresentative W) volume :=
    locallyIntegrableOn_univ.mp (W.property (baseIndex (m + 1) 1)).locallyIntegrable_f
  have hf := (Lp.memLp f).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hqint := (Lp.memLp q).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  ext φ
  change LineDeriv.laplacianCLM ℝ (ℝ^(m + 1))
      𝓓'((⊤ : Opens ℝ^(m + 1)), ℝ)
      (Distribution.ofFun ⊤ (baseRepresentative W) volume ⊤) φ =
    Distribution.ofFun ⊤ (f : ℝ^(m + 1) → ℝ) (domainMeasure (m + 1) Ω) ⊤ φ -
      Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ φ
  rw [Distribution.laplacianCLM_apply_apply,
    Distribution.ofFun_apply (hW.locallyIntegrableOn univ),
    Distribution.ofFun_apply (hf.locallyIntegrableOn univ),
    Distribution.ofFun_apply (hqint.locallyIntegrableOn univ)]
  simp only [smul_eq_mul, TestFunction.laplacianCLM_apply_eq_laplacian]
  have hzero : baseRepresentative W =ᵐ[volume]
      Ω.indicator (baseCoordCLM w : ℝ^(m + 1) → ℝ) :=
    zeroExtendH10_coordinate_apply_ae H.isOpen.measurableSet w (baseIndex (m + 1) 1)
  have hvolume : (∫ x, PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x *
      baseRepresentative W x) =
      ∫ x, baseCoordCLM w x * PDE.laplacian φ.toFun x ∂domainMeasure (m + 1) Ω := by
    calc
      _ = ∫ x, Ω.indicator
          (fun y ↦ baseCoordCLM w y * PDE.laplacian φ.toFun y) x := by
        apply integral_congr_ae
        filter_upwards [hzero] with x hx
        rw [hx]
        by_cases hxΩ : x ∈ Ω
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
          exact mul_comm _ _
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, mul_zero]
      _ = _ := integral_indicator H.isOpen.measurableSet
  let V : H¹(Ω) := globalTestFunctionToWkpOn φ
  have hgradient : inner ℝ (wkpGradientCLM (w : H¹(Ω))) (wkpGradientCLM V) =
      -(∫ x, baseCoordCLM w x * PDE.laplacian φ.toFun x
        ∂domainMeasure (m + 1) Ω) := by
    rw [real_inner_comm, inner_wkpGradientCLM_eq_sum]
    exact sum_inner_smooth_gradient_eq_neg_integral
      φ.toFun φ.contDiff φ.hasCompactSupport w
  have hload : inner ℝ f (wkpBaseCoordinateCLM V) =
      ∫ x, φ x * f x ∂domainMeasure (m + 1) Ω := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [globalTestFunctionToWkpOn_coordinate_ae
      (Ω := Ω) (p := 2) φ (baseIndex (m + 1) 1)] with x hx
    simp only [baseIndex_toList, iteratedPartialDeriv] at hx
    simp only [RCLike.inner_apply, conj_trivial]
    change wkpBaseCoordinateCLM V x * f x = φ x * f x
    rw [show wkpBaseCoordinateCLM V x = φ x from hx]
  have hsurface : (∫ y, q y * (boundaryValue (traceClass V)) y ∂surfaceMeasure Ω) =
      ∫ y, φ y * q y ∂surfaceMeasure Ω := by
    apply integral_congr_ae
    filter_upwards [trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω) φ] with y hy
    change q y * trace V y = φ y * q y
    rw [hy, mul_comm]
  have hpair := hq (traceClass V)
  rw [weakNormalTrace_traceClass, hload, hgradient, hsurface] at hpair
  rw [hvolume]
  linarith

/-- If `Ω` has a C¹ graph boundary and `w ∈ H¹₀(Ω)` solves `Δw = f ∈ L²(Ω)` weakly, then some
`q ∈ L²(∂Ω)` represents the weak normal trace of `w`, and for this `q` the Laplacian of the zero
extension of `w` is `f dx` on `Ω` minus `q dS`, as in
`laplacian_zeroExtendH10_eq_volume_sub_surface`. -/
theorem exists_laplacian_zeroExtendH10_eq_volume_sub_surface
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v)) :
    ∃ q : BoundaryL2 (Ω := Ω),
      (∀ z : HilbertTraceSpace (Ω := Ω),
        weakNormalTrace (w : H¹(Ω)) f huf z =
          ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω) ∧
      Δ (Distribution.ofFun ⊤
        (baseRepresentative (zeroExtendH10 H.isOpen.measurableSet w)) volume ⊤) =
          Distribution.ofFun ⊤ (f : ℝ^(m + 1) → ℝ) (domainMeasure (m + 1) Ω) ⊤ -
            Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ := by
  obtain ⟨q, hq⟩ := exists_surfaceDensity_weakNormalTrace_of_H10 hgraph w f huf
  exact ⟨q, hq, laplacian_zeroExtendH10_eq_volume_sub_surface w f huf q hq⟩

end SobolevSpace.Trace.C1
