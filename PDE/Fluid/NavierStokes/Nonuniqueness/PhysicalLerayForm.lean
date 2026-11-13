/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalPressure
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalVelocityParts
public import PDE.Fluid.NavierStokes.RieszPressure.Leray
public import PDE.Fluid.NavierStokes.Nonuniqueness.SpaceTimeIntegrability

/-!
# The Leray form of the physical equation

At a time `t ∈ (0, 1)` write the slice of the physical velocity as `v = ũ + u_cut + u_cor`,
with the dilated profile `ũ = a Ũ(a ·)`, `a = t^{-1/2}`. The profile part satisfies
`∂ₜũ - Δũ = -a³ (½ (Ũ + ξ·∇Ũ) + ΔŨ)(a ·)`, and by the profile equation and the dilation
covariance of the Leray projection this is `-Π((ũ·∇)ũ)`
(`UnstableProfile.lerayProjection_toLp_dilateField_advective`). The cutoff part solves the heat
equation, and the correction solves `∂ₜu_cor - Δu_cor = Π g` with the physical forcing `g`;
through the physical coefficient fields `Π g = -Π((v·∇)v - (ũ·∇)ũ)`. So the slice satisfies
`∂ₜv - Δv = -Π((v·∇)v)`, which by the Riesz pressure is `-(v·∇)v - ∇P` (`physical_lerayForm`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The Laplacian of the profile is square integrable. -/
theorem memLp_laplacian : MemLp (PDE.laplacian D.U) 2 volume := by
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian D.U) := contDiff_laplacian_of_top D.contDiff_U
  refine ((D.derivatives_memLp_two 2 (by norm_num)).norm.const_mul 3).of_le
    hlap.continuous.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  have h := norm_iteratedFDeriv_laplacian_le D.contDiff_U 0 x
  rw [norm_iteratedFDeriv_zero] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h

/-- The convection `(Ũ·∇)Ũ` of the profile is square integrable. -/
theorem memLp_advective : MemLp (fun ξ ↦ fderiv ℝ D.U ξ (D.U ξ)) 2 volume := by
  have h : (fun ξ ↦ fderiv ℝ D.U ξ (D.U ξ)) = nonlinearField D.U + PDE.laplacian D.U :=
    funext fun ξ ↦ by simp [nonlinearField]
  rw [h]
  exact D.memLp_nonlinearField.add D.memLp_laplacian

/-- The Laplacian of the profile is divergence free. -/
theorem divergence_laplacian (x : ℝ^3) : PDE.divergence (PDE.laplacian D.U) x = 0 := by
  have hU := D.contDiff_U
  have hUi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ D.U y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hU
  have hcomp (i : Fin 3) : (fun y ↦ PDE.laplacian D.U y i) =
      fun y ↦ PDE.laplacian (fun z ↦ D.U z i) y :=
    funext fun y ↦ PDE.laplacian_apply_of_contDiff (hU.of_le (by simp)) y i
  have hdiv : (fun y ↦ ∑ i : Fin 3, PDE.partialDeriv i (fun z ↦ D.U z i) y) = fun _ ↦ 0 :=
    funext fun y ↦ D.divergence_eq_zero y
  unfold PDE.divergence
  simp_rw [hcomp]
  rw [Finset.sum_congr rfl fun i _ ↦ (PDE.laplacian_partialDeriv_eq (hUi i) i x).symm,
    ← LaplacianEquation.laplacian_finsetSum _
      (fun i _ ↦ (PDE.contDiff_top_partialDeriv (hUi i)).of_le (by simp)) x, hdiv]
  simp [PDE.laplacian, PDE.partialDeriv]

/-- The Laplacian of the profile is distributionally divergence free. -/
theorem distributionallyDivergenceFree_laplacian :
    DistributionallyDivergenceFree (PDE.laplacian D.U) :=
  SpatialFieldDivergenceFree.distributionallyDivergenceFree D.divergence_laplacian
    ((contDiff_laplacian_of_top D.contDiff_U).of_le (by simp))

/-- **The Leray projection of the profile convection.** `Π((Ũ·∇)Ũ) = ½ (Ũ + ξ·∇Ũ) + ΔŨ`. -/
theorem lerayProjection_toLp_advective
    (hA : MemLp (fun ξ ↦ fderiv ℝ D.U ξ (D.U ξ)) 2 (domainMeasure 3 univ))
    (hF : MemLp (fun ξ ↦ (1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U ξ +
      PDE.laplacian D.U ξ) 2 (domainMeasure 3 univ)) :
    lerayProjection 3 (hA.toLp _) = hF.toLp _ := by
  have hK0 : MemLp (nonlinearField D.U) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_nonlinearField
  have hL0 : MemLp (PDE.laplacian D.U) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_laplacian
  have hD0 : MemLp (SpectralProfile.velocityDrift D.U) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_velocityDrift
  have h2 : (2 : ℝ) • lerayProjection 3 (hK0.toLp _) = hD0.toLp _ := by
    have h := D.l2SobolevRow_base_profileScalingSobolev 0 hD0
    rw [profileScalingSobolev, map_smul, l2SobolevRow_leraySobolev] at h
    rwa [UnstableProfile.profileNonlinearSobolev,
      l2SobolevRow_base_toLp_vectorWkpOfContDiff _ _ hK0] at h
  have hA' : hA.toLp _ = hK0.toLp _ + hL0.toLp _ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ ↦ by simp [nonlinearField])
  have hF' : hF.toLp _ = (1 / 2 : ℝ) • hD0.toLp _ + hL0.toLp _ := by
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    rfl
  have hsol : hL0.toLp _ ∈ l2Solenoidal 3 :=
    toLp_mem_l2Solenoidal hL0 D.distributionallyDivergenceFree_laplacian
  rw [hA', map_add, lerayProjection_eq_self hsol, hF', ← h2, smul_smul]
  norm_num

/-- **The Leray projection of the dilated profile convection.** For `a > 0` and the dilated
profile `ũ = a Ũ(a ·)`, `Π((ũ·∇)ũ) = a³ (½ (Ũ + ξ·∇Ũ) + ΔŨ)(a ·)`. -/
theorem lerayProjection_toLp_dilateField_advective {a : ℝ} (ha : 0 < a)
    (hA : MemLp (fun x ↦ fderiv ℝ (dilateField a D.U) x (dilateField a D.U x)) 2
      (domainMeasure 3 univ))
    (hF : MemLp (fun x ↦ a ^ 3 • ((1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U (a • x) +
      PDE.laplacian D.U (a • x))) 2 (domainMeasure 3 univ)) :
    lerayProjection 3 (hA.toLp _) = hF.toLp _ := by
  have hA0 : MemLp (fun ξ ↦ fderiv ℝ D.U ξ (D.U ξ)) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_advective
  have hF0 : MemLp (fun ξ ↦ (1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U ξ +
      PDE.laplacian D.U ξ) 2 (domainMeasure 3 univ) := by
    have h := (D.memLp_velocityDrift.const_smul (1 / 2 : ℝ)).add D.memLp_laplacian
    simp only [domainMeasure, Measure.restrict_univ]
    exact h
  have hdil : (fun x ↦ fderiv ℝ (dilateField a D.U) x (dilateField a D.U x)) =
      fun x ↦ a ^ 3 • fderiv ℝ D.U (a • x) (D.U (a • x)) := by
    funext x
    rw [fderiv_dilateField_apply a D.contDiff_U, dilateField, map_smul, smul_smul]
    ring_nf
  have hA' : MemLp (fun x ↦ a ^ 3 • fderiv ℝ D.U (a • x) (D.U (a • x))) 2
      (domainMeasure 3 univ) := hdil ▸ hA
  have hAeq : hA.toLp _ = hA'.toLp _ := MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ by
    rw [hdil])
  rw [hAeq, toLp_smul_comp_smul hA0 _ ha.ne' hA', toLp_smul_comp_smul hF0 _ ha.ne' hF, map_smul,
    lerayProjection_l2Dilation, D.lerayProjection_toLp_advective hA0 hF0]

/-- The scaled dilate `a³ (½ (Ũ + ξ·∇Ũ) + ΔŨ)(a ·)` is square integrable. -/
theorem memLp_dilate_scaling {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x ↦ a ^ 3 • ((1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U (a • x) +
      PDE.laplacian D.U (a • x))) 2 volume := by
  have h₁ : MemLp (fun ξ ↦ (1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U ξ +
      PDE.laplacian D.U ξ) 2 volume :=
    (D.memLp_velocityDrift.const_smul (1 / 2 : ℝ)).add D.memLp_laplacian
  exact (h₁.comp_smul ha).const_smul (a ^ 3)

/-- The convection of the dilated profile is square integrable. -/
theorem memLp_dilateField_advective {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x ↦ fderiv ℝ (dilateField a D.U) x (dilateField a D.U x)) 2 volume := by
  have hdil : (fun x ↦ fderiv ℝ (dilateField a D.U) x (dilateField a D.U x)) =
      fun x ↦ a ^ 3 • fderiv ℝ D.U (a • x) (D.U (a • x)) := by
    funext x
    rw [fderiv_dilateField_apply a D.contDiff_U, dilateField, map_smul, smul_smul]
    ring_nf
  rw [hdil]
  exact (D.memLp_advective.comp_smul ha).const_smul (a ^ 3)

end UnstableProfile

variable {D : UnstableProfile} {R s : ℝ}

/-! ### The projected physical forcing -/

variable (D R s) in
/-- The convection `(v·∇)v - (ũ·∇)ũ` of the physical velocity minus that of the physical
profile, in vector `Hᵐ⁺¹`: the `L⁴` convections of the cutoff field and the profile, the
transports of the correction by the cutoff field and the profile, and the convection of the
correction. -/
def physicalConvectionRemainder (m : ℕ) (hm : (3 : ℝ) < 2 * m) (t : ℝ) : VectorH 3 (m + 1) :=
  lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
      (physicalCutoffSobolev D R (m + 2) le_rfl t) +
    lebesgueConvection (m + 1) (physicalProfileWkFour D (m + 1) t)
      (physicalCutoffSobolev D R (m + 2) le_rfl t) +
    lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
      (physicalProfileWkFour D (m + 2) t) +
    profileConvection (m + 1) (physicalCutoffSobolev D R (m + 2) le_top t)
      (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t) +
    profileConvection (m + 1) (physicalProfileWkTop D (m + 2) t)
      (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t) +
    mixedConvection (m + 1) (three_lt_two_mul_succ hm) (physicalCorrection D R s m hm t)
      (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t)

/-- **The projected physical forcing.** For `0 < t ≤ 1`, `Π g(t) = -Π((v·∇)v - (ũ·∇)ũ)`. -/
theorem leraySobolev_physicalForcing (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    leraySobolev 3 (m + 1) (physicalForcing D R s m hm t) =
      -leraySobolev 3 (m + 1) (physicalConvectionRemainder D R s m hm t) := by
  rw [physicalForcing_eq hR hs hm ht ht1, physicalCutoffForcing_eq ht, physicalCoefficient_eq ht]
  simp only [physicalConvectionRemainder, sub_apply, profileTransport_apply, map_add, map_sub,
    map_neg, leraySobolev_idempotent]
  abel

/-- **The components of the convection remainder.** For `0 < t ≤ 1` the base representatives
of `physicalConvectionRemainder` are the components of `(v·∇)v - (ũ·∇)ũ`, with `v` the slice of
the physical velocity and `ũ` its profile part. -/
theorem baseRepresentative_physicalConvectionRemainder_ae (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (j : Fin 3) :
    baseRepresentative (physicalConvectionRemainder D R s m hm t j) =ᵐ[volume] fun x ↦
      (fderiv ℝ (velocitySlice (physicalVelocity D R s) t) x
          (velocitySlice (physicalVelocity D R s) t x) -
        fderiv ℝ (physicalProfileField D t) x (physicalProfileField D t x)) j := by
  set P := physicalProfileField D t with hPdef
  set C := physicalCutoffField D R t with hCdef
  set K := physicalCorrectionField D R s t with hKdef
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := contDiff_physicalProfileField t
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := contDiff_physicalCutoffField t
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := contDiff_physicalCorrectionField hR hs ht ht1
  have hm' := three_lt_two_mul_succ hm
  set W₁ := physicalCorrection D R s m hm t
  set W₂ := physicalCorrection D R s (m + 1) hm' t
  have e₁ : baseRepresentative (lebesgueConvection (m + 1)
      (physicalCutoffSobolev D R (m + 1) le_rfl t) (physicalCutoffSobolev D R (m + 2) le_rfl t) j)
      =ᵐ[volume] fun x ↦ ∑ i : Fin 3, C x i * fderiv ℝ C x (EuclideanSpace.single i 1) j :=
    lebesgueConvection_vectorWkpOfContDiff_base_ae _ _ _ _ _ _ _ j
  have e₂ : baseRepresentative (lebesgueConvection (m + 1)
      (physicalProfileWkFour D (m + 1) t) (physicalCutoffSobolev D R (m + 2) le_rfl t) j)
      =ᵐ[volume] fun x ↦ ∑ i : Fin 3, P x i * fderiv ℝ C x (EuclideanSpace.single i 1) j :=
    lebesgueConvection_vectorWkpOfContDiff_base_ae _ _ _ _ _ _ _ j
  have e₃ : baseRepresentative (lebesgueConvection (m + 1)
      (physicalCutoffSobolev D R (m + 1) le_rfl t) (physicalProfileWkFour D (m + 2) t) j)
      =ᵐ[volume] fun x ↦ ∑ i : Fin 3, C x i * fderiv ℝ P x (EuclideanSpace.single i 1) j :=
    lebesgueConvection_vectorWkpOfContDiff_base_ae _ _ _ _ _ _ _ j
  have hW (i : Fin 3) := baseRepresentative_physicalCorrection_ae hR hs hm' ht ht1 i
  have hW₁ (i : Fin 3) := baseRepresentative_physicalCorrection_ae hR hs hm ht ht1 i
  have hdW (i : Fin 3) :=
    baseRepresentative_partialDerivCLM_physicalCorrection_ae hR hs hm ht ht1 i j
  have hconv (V : Fin 3 → W^{m + 2,∞}(ℝ^3)) (F : ℝ^3 → ℝ^3)
      (hb : ∀ i, baseRepresentative (V i) =ᵐ[volume] fun x ↦ F x i)
      (hdb : ∀ i, baseRepresentative (partialDerivCLM i (V j)) =ᵐ[volume]
        fun x ↦ fderiv ℝ F x (EuclideanSpace.single i 1) j) :
      baseRepresentative (profileConvection (m + 1) V W₂ j) =ᵐ[volume] fun x ↦ ∑ i : Fin 3,
        (F x i * fderiv ℝ K x (EuclideanSpace.single i 1) j +
          fderiv ℝ F x (EuclideanSpace.single i 1) j * K x i) := by
    filter_upwards [profileConvection_base_ae (m + 1) V W₂ j, ae_all_iff.mpr hb,
      ae_all_iff.mpr hdb, ae_all_iff.mpr hW, ae_all_iff.mpr hdW] with x h₀ h₁ h₂ h₃ h₄
    rw [h₀]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h₁ i, h₂ i, h₃ i, h₄ i]
  have e₄ := hconv (physicalCutoffSobolev D R (m + 2) le_top t) C
    (fun i ↦ baseRepresentative_vectorWkpOfContDiff _ _ _ i)
    fun i ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff _ _ _ j i
  have e₅ := hconv (physicalProfileWkTop D (m + 2) t) P
    (fun i ↦ baseRepresentative_vectorWkpOfContDiff _ _ _ i)
    fun i ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff _ _ _ j i
  have e₆ : baseRepresentative (mixedConvection (m + 1) hm' W₁ W₂ j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, K x i * fderiv ℝ K x (EuclideanSpace.single i 1) j := by
    filter_upwards [mixedConvection_base_ae hm' W₁ W₂ j, ae_all_iff.mpr hW₁,
      ae_all_iff.mpr hdW] with x h₀ h₁ h₂
    rw [h₀]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h₁ i, h₂ i]
  have hadd (U V : W^{m + 1,2}(ℝ^3)) : baseRepresentative (U + V) =ᵐ[volume]
      fun x ↦ baseRepresentative U x + baseRepresentative V x := by
    simpa only [domainMeasure, Measure.restrict_univ] using baseRepresentative_add_ae U V
  simp only [physicalConvectionRemainder, PiLp.add_apply]
  filter_upwards [hadd _ _, hadd _ _, hadd _ _, hadd _ _, hadd _ _, e₁, e₂, e₃, e₄, e₅, e₆]
    with x a₁ a₂ a₃ a₄ a₅ h₁ h₂ h₃ h₄ h₅ h₆
  rw [a₁, a₂, a₃, a₄, a₅, h₁, h₂, h₃, h₄, h₅, h₆, velocitySlice_physicalVelocity_eq_add ht]
  have hdP := (hP.differentiable (by simp)) x
  have hdC := (hC.differentiable (by simp)) x
  have hdK := (hK.differentiable (by simp)) x
  rw [fderiv_add (hdP.add hdC) hdK, fderiv_add hdP hdC, PiLp.sub_apply,
    ContinuousLinearMap.apply_eq_sum_mul_apply_single
      (fderiv ℝ P x + fderiv ℝ C x + fderiv ℝ K x) ((P + C + K) x) j,
    ContinuousLinearMap.apply_eq_sum_mul_apply_single (fderiv ℝ P x) (P x) j]
  simp only [add_apply, Pi.add_apply, PiLp.add_apply, Fin.sum_univ_three]
  ring

/-- The coordinates of a vector base row are the base representatives of the components. -/
theorem l2SobolevRow_base_apply_ae {k : ℕ} (V : VectorH 3 k) :
    ∀ᵐ x ∂volume, ∀ j : Fin 3,
      (l2SobolevRow (baseIndex 3 k) V x) j = baseRepresentative (V j) x := by
  have h := Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex 3 k) (V j))
  simp only [domainMeasure, Measure.restrict_univ] at h
  filter_upwards [h] with x hx j
  rw [l2SobolevRow_apply, hx j, wkpCoordinateCLM_apply]
  rfl

/-- **The Leray form of the physical equation.** For `0 < t ≤ 1`, with `v` the slice of the
physical velocity, `P` its Riesz pressure and `a = t^{-1/2}`,
`-a³ (½ (Ũ + ξ·∇Ũ) + ΔŨ)(a x) + (Π g(t))(x) = -((v·∇)v + ∇P)(x)` at every `x`, where the first
two terms are `∂ₜv - Δv` (the profile part and the projected physical forcing of the
correction; the cutoff part solves the heat equation). -/
theorem physical_lerayForm (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ^3) (j : Fin 3) :
    -(physicalFactor (Real.log t) ^ 3 * ((1 / 2 : ℝ) *
        SpectralProfile.velocityDrift D.U (physicalFactor (Real.log t) • x) j +
        PDE.laplacian D.U (physicalFactor (Real.log t) • x) j)) +
      classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one
        (by norm_num : (3 : ℝ) < 2 * ((3 : ℕ) : ℝ))) (leraySobolev 3 (3 + 1)
          (physicalForcing D R s 3 (by norm_num) t) j) x =
      -(PDE.advectiveDerivative (velocitySlice (physicalVelocity D R s) t)
          (velocitySlice (physicalVelocity D R s) t) x j +
        PDE.partialDeriv j (rieszPressure (velocitySlice (physicalVelocity D R s) t)) x) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  have hm3 : (3 : ℝ) < 2 * ((3 : ℕ) : ℝ) := by norm_num
  have hk := three_lt_two_mul_succ_sub_one hm3
  -- the classical facts on the slice
  have hvs := contDiff_velocitySlice_physicalVelocity hR hs ht ht1
  have hps := contDiff_rieszPressure_velocitySlice hR hs ht ht1
  obtain ⟨hadv, hPi⟩ := lerayProjection_advective_ae_eq (hvs.of_le (by simp))
    (memLp_velocitySlice_physicalVelocity D s hR0 (q := 4) (by norm_num) ht)
    (memLp_velocitySlice_physicalVelocity D s hR0 (q := ⊤) le_top ht)
    (memLp_fderiv_velocitySlice_physicalVelocity hR hs ht ht1)
    (divergence_velocitySlice_physicalVelocity hR hs ht ht1) (hps.of_le (by simp))
  set a := physicalFactor (Real.log t) with hadef
  have ha : 0 < a := physicalFactor_pos _
  set v := velocitySlice (physicalVelocity D R s) t with hvdef
  set g := physicalForcing D R s 3 hm3 t
  set X := physicalConvectionRemainder D R s 3 hm3 t
  -- the profile part
  have hAp : MemLp (fun x ↦ fderiv ℝ (dilateField a D.U) x (dilateField a D.U x)) 2
      (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_dilateField_advective ha.ne'
  have hFp : MemLp (fun x ↦ a ^ 3 • ((1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U (a • x) +
      PDE.laplacian D.U (a • x))) 2 (domainMeasure 3 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using D.memLp_dilate_scaling ha.ne'
  have hprof := D.lerayProjection_toLp_dilateField_advective ha hAp hFp
  -- the remainder
  have hX := ae_all_iff.mpr fun j ↦
    baseRepresentative_physicalConvectionRemainder_ae hR hs hm3 ht ht1 j
  have hrow : ⇑(l2SobolevRow (baseIndex 3 (3 + 1)) X) =ᵐ[domainMeasure 3 univ] fun x ↦
      PDE.advectiveDerivative v v x - fderiv ℝ (dilateField a D.U) x (dilateField a D.U x) := by
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [l2SobolevRow_base_apply_ae X, hX] with x h₁ h₂
    exact PiLp.ext fun j ↦ (h₁ j).trans (h₂ j)
  have hN := (Lp.memLp _).ae_eq hrow
  have hNrow : hN.toLp _ = l2SobolevRow (baseIndex 3 (3 + 1)) X :=
    (MemLp.toLp_congr hN (Lp.memLp _) hrow.symm).trans (Lp.toLp_coeFn _ _)
  have hsplit : hadv.toLp _ = hAp.toLp _ + hN.toLp _ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ by simp)
  have hproj : lerayProjection 3 (hadv.toLp _) =
      hFp.toLp _ + lerayProjection 3 (l2SobolevRow (baseIndex 3 (3 + 1)) X) := by
    rw [hsplit, map_add, hprof, hNrow]
  -- the forcing
  have hg : l2SobolevRow (baseIndex 3 (3 + 1)) (leraySobolev 3 (3 + 1) g) =
      -lerayProjection 3 (l2SobolevRow (baseIndex 3 (3 + 1)) X) := by
    rw [leraySobolev_physicalForcing hR hs hm3 ht ht1, map_neg, l2SobolevRow_leraySobolev]
  -- the two sides as functions
  set L : ℝ^3 → ℝ^3 := fun x ↦ -(a ^ 3 • ((1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U (a • x) +
      PDE.laplacian D.U (a • x))) + WithLp.toLp 2 fun j ↦
        classicalRepresentativeCLM hk (leraySobolev 3 (3 + 1) g j) x with hLdef
  set Rt : ℝ^3 → ℝ^3 := fun x ↦ -(PDE.advectiveDerivative v v x +
      WithLp.toLp 2 fun j ↦ PDE.partialDeriv j (rieszPressure v) x) with hRdef
  have hae : L =ᵐ[volume] Rt := by
    have h₁ := hFp.coeFn_toLp
    have h₂ := Lp.coeFn_add (hFp.toLp _) (lerayProjection 3 (l2SobolevRow (baseIndex 3 (3 + 1)) X))
    have h₃ := Lp.coeFn_neg (lerayProjection 3 (l2SobolevRow (baseIndex 3 (3 + 1)) X))
    simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂ h₃
    filter_upwards [hPi, h₁, h₂, h₃, l2SobolevRow_base_apply_ae (leraySobolev 3 (3 + 1) g),
      ae_all_iff.mpr fun j ↦ classicalRepresentativeCLM_ae hk (leraySobolev 3 (3 + 1) g j)]
      with x e₁ e₂ e₃ e₄ e₅ e₆
    refine PiLp.ext fun j ↦ ?_
    have hc : classicalRepresentativeCLM hk (leraySobolev 3 (3 + 1) g j) x =
        -(lerayProjection 3 (l2SobolevRow (baseIndex 3 (3 + 1)) X) x) j := by
      rw [e₆ j, ← e₅ j, hg, e₄, Pi.neg_apply, PiLp.neg_apply]
    have hPix := e₁ j
    rw [hproj, e₃, Pi.add_apply, PiLp.add_apply, e₂] at hPix
    simp only [hLdef, hRdef, PiLp.add_apply, PiLp.neg_apply, hc]
    rw [← hPix]
    ring
  have hLc : Continuous L := by
    have hU := D.contDiff_U
    have hd : Continuous (SpectralProfile.velocityDrift D.U) :=
      hU.continuous.add ((hU.continuous_fderiv (by simp)).clm_apply continuous_id)
    have hl : Continuous (PDE.laplacian D.U) :=
      (UnstableProfile.contDiff_laplacian_of_top hU).continuous
    have h₁ : Continuous fun x ↦ a ^ 3 • ((1 / 2 : ℝ) • SpectralProfile.velocityDrift D.U (a • x) +
        PDE.laplacian D.U (a • x)) := by fun_prop
    have h₂ : Continuous fun x ↦ (WithLp.toLp 2 fun j ↦
        classicalRepresentativeCLM hk (leraySobolev 3 (3 + 1) g j) x : ℝ^3) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦
        (classicalRepresentativeCLM hk (leraySobolev 3 (3 + 1) g j)).continuous)
    exact h₁.neg.add h₂
  have hRc : Continuous Rt := by
    refine (((hvs.continuous_fderiv (by simp)).clm_apply hvs.continuous).add
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ ?_))).neg
    exact (PDE.contDiff_top_partialDeriv (i := j) hps).continuous
  have heq := (hLc.ae_eq_iff_eq volume hRc).mp hae
  simpa only [hLdef, hRdef, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul] using
    congrArg (fun F : ℝ^3 → ℝ^3 ↦ F x j) heq

end NavierStokes.Nonuniqueness
