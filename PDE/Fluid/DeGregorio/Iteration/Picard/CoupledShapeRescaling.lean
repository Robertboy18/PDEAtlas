/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeData

/-!
# Closed shape of a dynamic rescaling of the coupled solution

The production covariance theorem gives the rescaled equation from scale
laws. Oddness passes through the pullback, and continuity and positivity
of the spatial scale give a common support enclosure on each closed slab.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Representations.Similarity PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- Any positive dynamic spatial rescaling of the constructed odd solution
has an interior rescaled PDE and odd, uniformly supported closed slices.
The common support radius is derived by minimizing the continuous scale. -/
theorem IsHkFrozenOutput.rescaled_odd_support_on_Icc
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {F : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hodd : Function.Odd w₀)
    (data : DynamicRescalingData) {a b : ℝ} (hab : a ≤ b)
    (hscale : ContinuousOn data.spatialScale (Icc a b))
    (hpos : ∀ τ ∈ Icc a b, 0 < data.spatialScale τ)
    (htime : MapsTo data.physicalTime (Icc a b) (Icc 0 T))
    (hinterior : MapsTo data.physicalTime (Ioo a b) (Ioo 0 T))
    (hlaws : ∀ τ ∈ Ioo a b, SatisfiesDynamicScaleODEsAt data τ) :
    IsClassicalRescaledSolutionOn 1
      (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩)
      data.spatialRate data.vorticityRate (Ioo a b) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc a b,
      Function.Odd (fun x ↦
        (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩).vorticity x τ) ∧
      Function.Odd (fun x ↦
        (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩).velocity x τ) ∧
      tsupport (fun x ↦
        (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩).vorticity x τ)
          ⊆ Icc (-L) L ∧
      HasCompactSupport (fun x ↦
        (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩).vorticity x τ) := by
  refine ⟨h.isClassicalSolutionOn.dynamicallyRescaledFields 1 data _ _ _
    hinterior hlaws (fun τ hτ ↦ hpos τ (Ioo_subset_Icc_self hτ)), ?_⟩
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab) hscale
  let L := max R 0 / data.spatialScale s
  have hm := hpos s hs
  refine ⟨L, div_nonneg (le_max_right R 0) hm.le, ?_⟩
  intro τ hτ
  have hω := h.odd_vorticity_on_Icc hodd (htime hτ)
  have hu := (h.odd_velocity_even_coefficient_on_Icc hodd (htime hτ)).1
  have hsupp : tsupport (fun x ↦
      (dynamicallyRescaledFields data ⟨w, hkCurveHilbertVelocity hT F⟩).vorticity x τ)
        ⊆ Icc (-L) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hnot
    have hLx : L < |x| := lt_of_not_ge fun hh ↦ hnot (abs_le.mp hh)
    have hRx : R < |data.spatialScale τ * x| := calc
      R ≤ max R 0 := le_max_left R 0
      _ < |x| * data.spatialScale s := (div_lt_iff₀ hm).mp hLx
      _ ≤ |x| * data.spatialScale τ :=
        mul_le_mul_of_nonneg_left (hmin hτ) (abs_nonneg x)
      _ = |data.spatialScale τ * x| := by
        rw [abs_mul, abs_of_pos (hpos τ hτ), mul_comm]
    apply hx
    change data.vorticityScale τ * w (data.spatialScale τ * x) (data.physicalTime τ) = 0
    rw [h.support _ _ (htime hτ) hRx, mul_zero]
  refine ⟨?_, ?_, hsupp,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupp⟩
  · intro x
    change data.vorticityScale τ * w (data.spatialScale τ * -x) (data.physicalTime τ) =
      -(data.vorticityScale τ * w (data.spatialScale τ * x) (data.physicalTime τ))
    simpa only [mul_neg] using
      congrArg (fun z ↦ data.vorticityScale τ * z) (hω (data.spatialScale τ * x))
  · intro x
    change data.vorticityScale τ / data.spatialScale τ *
      hkCurveHilbertVelocity hT F (data.spatialScale τ * -x) (data.physicalTime τ) =
      -(data.vorticityScale τ / data.spatialScale τ *
        hkCurveHilbertVelocity hT F (data.spatialScale τ * x) (data.physicalTime τ))
    simpa only [mul_neg] using congrArg
      (fun z ↦ data.vorticityScale τ / data.spatialScale τ * z) (hu (data.spatialScale τ * x))

end DeGregorio.Iteration
