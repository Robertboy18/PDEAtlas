/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Gradient
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Extension
public import PDE.Spaces.Sobolev.Calculus.Pullback.Divergence.Piola

/-!
# Identifying the extended chart flux on the equation's support

The physical flux may be represented by any almost-everywhere equal `L²`
coordinates. Quasi-measure preservation carries this equality to the
restricted chart. On the core of the solution cutoff, the nonlinear
extension is therefore precisely the Piola transform of those coordinates.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.WeakChangeOfVariables
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The weak gradient of the localized pullback produces the Piola
transform of the physical flux on the core of its cutoff. -/
theorem extendedChartFlux_localizedPullback_ae_on_core
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (A : ℝ^n → ℝ^n)
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hκ : tsupport κ.toFun ⊆ (hΩ.chart a).target)
    (hσ : ∀ y ∈ tsupport κ.toFun, σ.toFun y = 1)
    (β : ℝ) (u : H¹₀(Ω)) (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x))
    {K : Set (ℝ^n)} (hcore : ∀ y ∈ K, κ.toFun =ᶠ[nhds y] 1) :
    ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ K →
      extendedChartFlux (hΩ.chart a) A κ σ β y
        (Lp.euclideanTuple (fun i ↦ derivCoordCLM i
          (localizedHalfSpacePullbackCLM hΩ.isOpen.measurableSet
            (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)
            (hΩ.chart_target_bounded a) (hΩ.chart_mem_iff_upper a) κ hκ u)) y) =
      piolaTransform (hΩ.chart a) (fun x ↦ WithLp.toLp 2 (fun i ↦ q i x)) y := by
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  have hsource : E.source ⊆ Ω := fun _ hx ↦ hx.2
  have hlocal : ∀ᵐ y ∂domainMeasure n E.target,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u (E.symm y))) =
        WithLp.toLp 2 (fun i ↦ q i (E.symm y)) :=
    (quasiMeasurePreserving_partialHomeomorph (E := E.symm)
      (hΩ.chart_symm_contDiff a) (hΩ.chart_contDiff a)).ae_eq_comp
        (ae_restrict_of_ae_restrict_of_subset hsource hq)
  have hlocalImp : ∀ᵐ y ∂volume, y ∈ E.target →
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u (E.symm y))) =
        WithLp.toLp 2 (fun i ↦ q i (E.symm y)) :=
    (ae_restrict_iff' E.open_target.measurableSet).mp hlocal
  have hgradient := chartFlux_localizedHalfSpacePullback_ae_on_core
    hΩ.isOpen.measurableSet (hΩ.chart a) (hΩ.chart_contDiff a)
    (hΩ.chart_symm_contDiff a) (hΩ.chart_target_bounded a)
    (hΩ.chart_mem_iff_upper a) κ hκ u A hcore
  filter_upwards [hgradient, ae_restrict_of_ae hlocalImp,
    ae_restrict_mem (HalfSpace.isOpen_upper n).measurableSet] with y hg hq hy hyK
  have hκy : κ.toFun y = 1 := (hcore y hyK).eq_of_nhds
  have hyκ : y ∈ tsupport κ.toFun := subset_tsupport κ.toFun (by
    change κ.toFun y ≠ 0
    rw [hκy]
    norm_num)
  have hyE : y ∈ E.target := by
    rw [SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
    exact ⟨hκ hyκ, hy⟩
  rw [extendedChartFlux_eq_of_eq_one _ A κ σ β hκy (hσ y hyκ), hg hyK]
  exact congrArg
    (fun z ↦ |(fderiv ℝ (fun w ↦ (hΩ.chart a).symm w) y).det| •
      fderiv ℝ (fun w ↦ hΩ.chart a w) ((hΩ.chart a).symm y) z) (hq hyE)

end PDE.Elliptic.Regularity.Quasilinear
