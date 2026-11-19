/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Coordinates
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.LocalTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.Localization

/-!
# Physical coordinates of the curved fractional trace

The localized boundary coordinates are constructed from surface data alone. We
identify their values on a physical trace with the physical representatives of the
local Fourier-defined fractional traces. The proof uses chart measure transport and
the support of the flattened partition pieces, including outside each chart target.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

private theorem chartPhysicalization_congrExponent {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p = q) (i : Fin hΩ.N)
    (g : Lp ℝ p (flatSurfaceMeasure (n := m))) :
    Lp.congrExponent h (surfaceMeasure Ω) (chartPhysicalization p i g) =
      chartPhysicalization q i (Lp.congrExponent h (flatSurfaceMeasure (n := m)) g) := by
  subst q
  rfl

private theorem localPhysicalTraceLp_two (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(Ω)) :
    boundaryLpTwoEquivL2 (localPhysicalTraceLp 2 i u) =
      localPhysicalTrace i (domainW1pTwoEquivH1 u) := by
  change Lp.congrExponent (ENNReal.ofReal_ofNat 2) (surfaceMeasure Ω)
    (chartPhysicalization (ENNReal.ofReal (2 : ℝ)) i (localFlatTraceLp 2 i u)) =
    chartPhysicalization 2 i (localFlatTrace i (domainW1pTwoEquivH1 u))
  rw [chartPhysicalization_congrExponent, localFlatTraceLp_two]

/-- The Hilbert chart contribution is multiplication of the trace by its cutoff. -/
theorem localPhysicalTrace_eq_boundaryCutoff (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    localPhysicalTrace i u = boundaryCutoff 2 i (trace u) := by
  obtain ⟨v, rfl⟩ := (domainW1pTwoEquivH1 (Ω := Ω)).surjective u
  apply Lp.ext
  apply Filter.EventuallyEq.trans _ (boundaryCutoff_apply_ae 2 i _).symm
  rw [← localPhysicalTraceLp_two, ← boundaryLpTwoEquivL2_traceLp]
  simp only [boundaryLpTwoEquivL2, Lp.coeFn_congrExponent]
  exact localPhysicalTraceLp_eq_cutoff_mul_ae 2 i v

/-- The Hilbert flat trace vanishes off its chart target. -/
theorem localFlatTrace_eq_zero_off_target (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    (localFlatTrace i u : ℝ^(m + 1) → ℝ) =ᵐ[
      (flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ] 0 := by
  obtain ⟨v, rfl⟩ := (domainW1pTwoEquivH1 (Ω := Ω)).surjective u
  rw [← localFlatTraceLp_two, Lp.coeFn_congrExponent]
  exact localFlatTraceLp_eq_zero_off_target 2 i v

/-- Boundary coordinates of the physical trace are precisely the local fractional traces. -/
theorem localizedBoundaryCoordinates_trace (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    localizedBoundaryCoordinates 2 i (trace u) =
      HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (localFractionalTrace i u) := by
  let f := localFlatTrace i u
  let v := HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (localFractionalTrace i u)
  have hflatMap : MeasurePreserving (flatEmbedding (n := m))
      (volume : Measure (ℝ^m)) (flatSurfaceMeasure (n := m)) :=
    ⟨(isometry_flatEmbedding (n := m)).continuous.measurable, map_flatEmbedding_volume⟩
  have hfv : (f : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)]
      fun x ↦ v (flatProjection x) := by
    have h := liftLp_apply_ae (n := m) 2 v
    rw [show liftLp (n := m) 2 v = f from physical_localFractionalTrace i u] at h
    exact h
  have hfv' : (fun y ↦ f (flatEmbedding y)) =ᵐ[volume] v := by
    filter_upwards [hflatMap.quasiMeasurePreserving.ae hfv] with y hy
    simpa only [flatProjection_flatEmbedding] using hy
  have hphysical := (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure i).ae_eq
    (localPhysicalTrace_apply_ae i u)
  have hparameter := (measurePreserving_chartBoundaryParametrization i).quasiMeasurePreserving.ae
    hphysical
  have hon : ∀ᵐ y ∂(volume : Measure (ℝ^m)).restrict (chartBoundaryParameterDomain i),
      localPhysicalTrace i u (chartBoundaryParametrization i y) = f (flatEmbedding y) := by
    filter_upwards [hparameter,
      ae_restrict_mem (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet]
      with y hy hyD
    have hx : chartBoundaryParametrization i y ∈ chartBoundaryPatch (Ω := Ω) i := by
      change chartBoundaryParametrization i y ∈ (hΩ.chart i).source ∩ frontier Ω
      rw [← image_chartBoundaryParametrization i]
      exact mem_image_of_mem _ hyD
    rw [indicator_of_mem hx] at hy
    simpa only [chartBoundaryParametrization, (hΩ.chart i).right_inv hyD] using hy
  have hon' := (ae_restrict_iff'
    (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet).mp hon
  have hoff := (ae_restrict_iff' (hΩ.chart i).open_target.measurableSet.compl).mp
    (localFlatTrace_eq_zero_off_target i u)
  have hoff' := hflatMap.quasiMeasurePreserving.ae hoff
  change boundaryCoordinates 2 i (boundaryCutoff 2 i (trace u)) = v
  rw [← localPhysicalTrace_eq_boundaryCutoff]
  apply Lp.ext
  filter_upwards [boundaryCoordinates_apply_ae 2 i (localPhysicalTrace i u), hon', hoff', hfv']
    with y hy honY hoffY hfvY
  rw [hy]
  by_cases hyD : y ∈ chartBoundaryParameterDomain (Ω := Ω) i
  · rw [indicator_of_mem hyD, honY hyD, hfvY]
  · rw [indicator_of_notMem hyD]
    exact (hfvY.symm.trans (hoffY hyD)).symm

/-- Every localized coordinate of a trace lies in the real Bessel half-order range. -/
theorem localizedBoundaryCoordinates_trace_mem_range (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    localizedBoundaryCoordinates 2 i (trace u) ∈
      Set.range (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)) :=
  ⟨localFractionalTrace i u, (localizedBoundaryCoordinates_trace i u).symm⟩

end SobolevSpace.Trace.C1.Fractional
