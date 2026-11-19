/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileScaling
public import PDE.Fluid.Incompressible.RemovableDivergence

/-!
# The scaling field of an unstable profile in every Sobolev space

The scaling field `Ũ + ξ·∇Ũ` of an unstable profile is `2 ((Ũ·∇)Ũ - ΔŨ + ∇P̃)` by the profile
equation. It is divergence free and square integrable, and the Leray projection removes the
pressure gradient, so it is the image `2 Π ((Ũ·∇)Ũ - ΔŨ)` of a field in every `Hᴺ`
(`UnstableProfile.profileScalingSobolev`,
`UnstableProfile.baseRepresentative_profileScalingSobolev_ae`).
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The nonlinear field of the profile is smooth. -/
theorem contDiff_nonlinearField : ContDiff ℝ (⊤ : ℕ∞) (nonlinearField D.U) := by
  have hX := D.contDiff_U
  have hadv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ D.U y (D.U y)) :=
    (contDiff_fderiv_of_top hX).clm_apply hX
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian D.U) := by
    unfold PDE.laplacian
    exact ContDiff.sum fun i _ ↦ PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hX)
  exact hadv.sub hlap

/-- The nonlinear field `(Ũ·∇)Ũ - ΔŨ` of the profile in vector `Hᴺ`. -/
def profileNonlinearSobolev (N : ℕ) : VectorH 3 N :=
  WithLp.toLp 2 (vectorWkpOfContDiff (nonlinearField D.U) D.contDiff_nonlinearField
    fun m _ ↦ D.memLp_iteratedFDeriv_nonlinearField m)

/-- The scaling field of the profile in vector `Hᴺ`: `2 Π ((Ũ·∇)Ũ - ΔŨ)`. -/
def profileScalingSobolev (N : ℕ) : VectorH 3 N :=
  (2 : ℝ) • leraySobolev 3 N (D.profileNonlinearSobolev N)

/-- The pressure of the profile as an element of `H¹`. -/
def pressureH1 : H¹(ℝ^3) :=
  wkpOfContDiff D.P D.contDiff_P fun m hm ↦ by
    interval_cases m
    · refine D.pressure_memLp_two.norm.of_le
        ((D.contDiff_P.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ ?_)
      simp [norm_iteratedFDeriv_zero]
    · refine D.pressure_gradient_memLp_two.norm.of_le
        ((D.contDiff_P.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ ?_)
      simp [norm_iteratedFDeriv_one]

/-- The gradient of the profile pressure has the norm of the derivative. -/
theorem norm_gradient_pressure (x : ℝ^3) : ‖gradient D.P x‖ = ‖fderiv ℝ D.P x‖ :=
  (InnerProductSpace.toDual ℝ (ℝ^3)).symm.norm_map _

/-- The gradient of the profile pressure is continuous. -/
theorem continuous_gradient_pressure : Continuous (gradient D.P) :=
  (InnerProductSpace.toDual ℝ (ℝ^3)).symm.continuous.comp
    (D.contDiff_P.continuous_fderiv (by simp))

/-- The gradient of the profile pressure is square integrable. -/
theorem memLp_gradient_pressure : MemLp (gradient D.P) 2 volume :=
  D.pressure_gradient_memLp_two.of_le D.continuous_gradient_pressure.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ (D.norm_gradient_pressure x).le)

/-- The nonlinear field of the profile is square integrable. -/
theorem memLp_nonlinearField : MemLp (nonlinearField D.U) 2 volume :=
  (D.memLp_iteratedFDeriv_nonlinearField 0).of_le
    D.contDiff_nonlinearField.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])

/-- The scaling field of the profile is square integrable. -/
theorem memLp_velocityDrift : MemLp (SpectralProfile.velocityDrift D.U) 2 volume := by
  have h : SpectralProfile.velocityDrift D.U =
      fun x ↦ (2 : ℝ) • (nonlinearField D.U x + gradient D.P x) :=
    funext D.velocityDrift_eq
  rw [h]
  exact (D.memLp_nonlinearField.add D.memLp_gradient_pressure).const_smul (2 : ℝ)

/-- The scaling field of the profile is distributionally divergence free. -/
theorem distributionallyDivergenceFree_velocityDrift :
    DistributionallyDivergenceFree (SpectralProfile.velocityDrift D.U) := by
  have hX := D.contDiff_U
  have hd : Differentiable ℝ (SpectralProfile.velocityDrift D.U) := fun x ↦
    ((hX.differentiable (by simp)) x).add
      (((contDiff_fderiv_of_top hX).differentiable (by simp)) x |>.clm_apply differentiableAt_id)
  exact distributionallyDivergenceFree_of_continuous_off_countable (n := 2) hd.continuous
    Set.countable_empty (fun x _ ↦ hd x)
    (fun x _ ↦ divergence_velocityDrift hX D.divergence_eq_zero x)

end UnstableProfile

/-- The physical base row of a smooth vector field with square-integrable derivatives is its
`L²` class. -/
theorem l2SobolevRow_base_toLp_vectorWkpOfContDiff {N : ℕ} {X : ℝ^3 → ℝ^3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hmem : ∀ m ≤ N, MemLp (iteratedFDeriv ℝ m X) 2 volume)
    (h0 : MemLp X 2 (domainMeasure 3 univ)) :
    l2SobolevRow (baseIndex 3 N) (WithLp.toLp 2 (vectorWkpOfContDiff X hX hmem)) =
      h0.toLp X := by
  apply Lp.ext
  rw [l2SobolevRow_apply]
  have hb := fun j : Fin 3 ↦ baseRepresentative_vectorWkpOfContDiff X hX hmem j
  filter_upwards [Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex 3 N)
      ((WithLp.toLp 2 (vectorWkpOfContDiff X hX hmem) : VectorH 3 N) j)), h0.coeFn_toLp,
    (by simpa only [domainMeasure, Measure.restrict_univ] using ae_all_iff.mpr hb :
      ∀ᵐ x ∂(domainMeasure 3 univ), ∀ j : Fin 3, baseRepresentative
        (vectorWkpOfContDiff X hX hmem j) x = X x j)] with x ht hx hc
  rw [hx]
  refine PiLp.ext fun j ↦ ?_
  rw [ht j, ← hc j]
  rfl

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The weak gradient of the pressure is the classical gradient. -/
theorem wkpGradientCLM_pressureH1 (h0 : MemLp (gradient D.P) 2 (domainMeasure 3 univ)) :
    wkpGradientCLM D.pressureH1 = h0.toLp (gradient D.P) := by
  apply Lp.ext
  have hc := fun i : Fin 3 ↦ wkpOfContDiff_apply_ae (k := 1) (p := 2) D.P D.contDiff_P
    (fun m hm ↦ by
      interval_cases m
      · refine D.pressure_memLp_two.norm.of_le
          ((D.contDiff_P.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
          (Eventually.of_forall fun x ↦ ?_)
        simp [norm_iteratedFDeriv_zero]
      · refine D.pressure_gradient_memLp_two.norm.of_le
          ((D.contDiff_P.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
          (Eventually.of_forall fun x ↦ ?_)
        simp [norm_iteratedFDeriv_one]) (singleDerivIndex 3 i)
  filter_upwards [wkpGradientCLM_apply_ae D.pressureH1, h0.coeFn_toLp,
    (by simpa only [domainMeasure, Measure.restrict_univ] using ae_all_iff.mpr hc :
      ∀ᵐ x ∂(domainMeasure 3 univ), ∀ i : Fin 3, _)] with x hg hx hc
  rw [hx]
  refine PiLp.ext fun i ↦ ?_
  rw [hg i]
  have := hc i
  simp only [singleDerivIndex_toList, iteratedPartialDeriv] at this
  rw [PDE.gradient_apply_eq_partialDeriv]
  exact this

/-- **The scaling field in every Sobolev space.** The physical base row of
`2 Π ((Ũ·∇)Ũ - ΔŨ)` is the `L²` class of `Ũ + ξ·∇Ũ`. -/
theorem l2SobolevRow_base_profileScalingSobolev (N : ℕ)
    (h0 : MemLp (SpectralProfile.velocityDrift D.U) 2 (domainMeasure 3 univ)) :
    l2SobolevRow (baseIndex 3 N) (D.profileScalingSobolev N) =
      h0.toLp (SpectralProfile.velocityDrift D.U) := by
  have hK0 : MemLp (nonlinearField D.U) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_nonlinearField
  have hG0 : MemLp (gradient D.P) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_gradient_pressure
  have hrow : l2SobolevRow (baseIndex 3 N) (D.profileNonlinearSobolev N) =
      hK0.toLp (nonlinearField D.U) :=
    l2SobolevRow_base_toLp_vectorWkpOfContDiff _ _ hK0
  have hS : h0.toLp (SpectralProfile.velocityDrift D.U) =
      (2 : ℝ) • (hK0.toLp (nonlinearField D.U) + hG0.toLp (gradient D.P)) := by
    rw [← MemLp.toLp_add, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ D.velocityDrift_eq x)
  have hsol : h0.toLp (SpectralProfile.velocityDrift D.U) ∈ l2Solenoidal 3 :=
    toLp_mem_l2Solenoidal h0 D.distributionallyDivergenceFree_velocityDrift
  calc l2SobolevRow (baseIndex 3 N) (D.profileScalingSobolev N)
      = (2 : ℝ) • lerayProjection 3 (hK0.toLp (nonlinearField D.U)) := by
        rw [profileScalingSobolev, map_smul, l2SobolevRow_leraySobolev, hrow]
    _ = lerayProjection 3 (h0.toLp (SpectralProfile.velocityDrift D.U)) := by
        rw [hS, map_smul, map_add, ← D.wkpGradientCLM_pressureH1 hG0,
          lerayProjection_wkpGradient_eq_zero, add_zero]
    _ = h0.toLp (SpectralProfile.velocityDrift D.U) := lerayProjection_eq_self hsol

/-- The components of `2 Π ((Ũ·∇)Ũ - ΔŨ)` are the components of the scaling field. -/
theorem baseRepresentative_profileScalingSobolev_ae (N : ℕ) (j : Fin 3) :
    baseRepresentative (D.profileScalingSobolev N j) =ᵐ[volume]
      fun x ↦ SpectralProfile.velocityDrift D.U x j := by
  have h0 : MemLp (SpectralProfile.velocityDrift D.U) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_velocityDrift
  have h := congrArg (l2Coordinate j) (D.l2SobolevRow_base_profileScalingSobolev N h0)
  rw [l2Coordinate_l2SobolevRow] at h
  have h₁ := l2Coordinate_ae j (h0.toLp (SpectralProfile.velocityDrift D.U))
  have h₂ := h0.coeFn_toLp
  have h₃ : baseRepresentative (D.profileScalingSobolev N j) =
      ⇑(wkpCoordinateCLM (baseIndex 3 N) (D.profileScalingSobolev N j)) := by
    rw [wkpCoordinateCLM_apply]
    rfl
  rw [h₃, h]
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  rw [hx₁, hx₂]

end UnstableProfile

end NavierStokes.Nonuniqueness
