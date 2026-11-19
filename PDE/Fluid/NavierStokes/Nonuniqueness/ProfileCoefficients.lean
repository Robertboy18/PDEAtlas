/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.UnstableProfile
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileCompact
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroupSobolev

/-!
# Linearization coefficients of an unstable profile

An unstable profile `U` has bounded derivatives of every order, all in `L⁴`, so its
components lie in `W^{k,∞}(ℝ³)` and in `W^{k,4}(ℝ³)` for every `k`. The linearization of the
self-similar equation at `U` has the transport coefficients `bᵢ = Uᵢ` and the stretching
coefficients `cⱼᵢ = ∂ᵢUⱼ`; these are the order-zero coefficients of `profileTransport` at `U`.
Since `U` and `∇U` tend to zero at infinity, the coefficients vanish at infinity, and the
time-one map of the profile evolution is a compact perturbation of the free self-similar
evolution. The coefficients satisfy the bounds `ProfileCoefficientBounds k` of every order, so
the profile evolution acts on every `Hᵏ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Topology

namespace NavierStokes.Nonuniqueness.UnstableProfile

variable (D : UnstableProfile)

/-- Every derivative of an unstable profile is essentially bounded. -/
theorem memLp_top_iteratedFDeriv (k : ℕ) : MemLp (iteratedFDeriv ℝ k D.U) ⊤ volume := by
  obtain ⟨C, hC⟩ := D.bounded_derivatives k
  exact memLp_top_of_bound ((D.contDiff_U.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).aestronglyMeasurable) C (Eventually.of_forall hC)

/-- The components of an unstable profile as elements of `W^{1,∞}(ℝ³)`. -/
def velocitySobolev : Fin 3 → W^{1,∞}(ℝ^3) :=
  vectorWkpOfContDiff D.U D.contDiff_U (fun m _ ↦ D.memLp_top_iteratedFDeriv m)

/-- The components of an unstable profile as elements of `W^{k,∞}(ℝ³)`, for every `k`; at
`k = m + 1` they are the coefficient of `profileTransport m`. -/
def velocityWkTop (k : ℕ) : Fin 3 → W^{k,∞}(ℝ^3) :=
  vectorWkpOfContDiff D.U D.contDiff_U (fun m _ ↦ D.memLp_top_iteratedFDeriv m)

theorem velocityWkTop_one : D.velocityWkTop 1 = D.velocitySobolev :=
  rfl

/-- The components of an unstable profile as elements of `W^{k,4}(ℝ³)`, for every `k`. -/
def velocityWkFour (k : ℕ) : Fin 3 → W^{k,4}(ℝ^3) :=
  vectorWkpOfContDiff D.U D.contDiff_U fun m _ ↦ D.derivatives_memLp_four m

/-- The transport coefficients `bᵢ = Uᵢ` of the linearization at the profile. -/
def transportCoefficients : Fin 3 → DerivLp 3 ∞ Set.univ :=
  fun i ↦ wkpBaseCoordinateCLM (D.velocitySobolev i)

/-- The stretching coefficients `cⱼᵢ = ∂ᵢUⱼ` of the linearization at the profile. -/
def stretchingCoefficients : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ :=
  fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (D.velocitySobolev j))

/-- The transport coefficients are the components of the profile almost everywhere. -/
theorem transportCoefficients_ae (i : Fin 3) :
    (D.transportCoefficients i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ D.U x i :=
  baseRepresentative_vectorWkpOfContDiff D.U D.contDiff_U
    (fun m _ ↦ D.memLp_top_iteratedFDeriv m) i

/-- The stretching coefficients are the partial derivatives of the profile components almost
everywhere. -/
theorem stretchingCoefficients_ae (j i : Fin 3) :
    (D.stretchingCoefficients j i : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ fderiv ℝ D.U x (EuclideanSpace.single i 1) j :=
  baseRepresentative_partialDerivCLM_vectorWkpOfContDiff (k := 0) D.U D.contDiff_U
    (fun m _ ↦ D.memLp_top_iteratedFDeriv m) j i

/-- At order zero the projected transport at the profile is minus the bounded projected
transport with the transport and stretching coefficients. -/
theorem profileTransport_zero_velocitySobolev :
    SobolevConvection.profileTransport 0 D.velocitySobolev =
      -BoundedTransport.projectedTransport D.transportCoefficients D.stretchingCoefficients :=
  SobolevConvection.profileTransport_zero _

/-- The linearization coefficients of an unstable profile vanish at infinity. -/
theorem coefficientsVanishAtInfinity :
    BoundedTransport.CoefficientsVanishAtInfinity D.transportCoefficients
      D.stretchingCoefficients := by
  refine BoundedTransport.CoefficientsVanishAtInfinity.of_tendsto
    (f := fun i x ↦ D.U x i)
    (g := fun j i x ↦ fderiv ℝ D.U x (EuclideanSpace.single i 1) j)
    D.transportCoefficients_ae D.stretchingCoefficients_ae (fun i ↦ ?_) (fun j i ↦ ?_)
  · have h0 := D.derivatives_tendsto_zero 0
    rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun x ↦ ?_) h0
    rw [norm_iteratedFDeriv_zero]
    exact PiLp.norm_apply_le (D.U x) i
  · have h1 := D.derivatives_tendsto_zero 1
    rw [tendsto_zero_iff_norm_tendsto_zero] at h1 ⊢
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun x ↦ ?_) h1
    rw [norm_iteratedFDeriv_one]
    calc
      ‖fderiv ℝ D.U x (EuclideanSpace.single i 1) j‖ ≤
          ‖fderiv ℝ D.U x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
      _ ≤ ‖fderiv ℝ D.U x‖ *
          ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))‖ :=
        (fderiv ℝ D.U x).le_opNorm _
      _ = ‖fderiv ℝ D.U x‖ := by simp

/-- For an unstable profile the time-one map of the profile evolution is a compact
perturbation of the time-one map of the free self-similar evolution. -/
theorem isCompactOperator_profileSemigroup_sub
    (hk : Selfsimilar.ProfileCoefficientBounds 0 D.transportCoefficients
      D.stretchingCoefficients) :
    IsCompactOperator
      (Selfsimilar.profileSemigroup0 D.transportCoefficients D.stretchingCoefficients hk 1 -
        HeatEquation.WholeSpace.vectorSelfsimilarHeatSemigroup 3 0 1) :=
  Selfsimilar.isCompactOperator_profileSemigroup_sub _ _ hk D.coefficientsVanishAtInfinity

/-- The linearization coefficients of an unstable profile satisfy the coefficient bounds of every
order: they are the coefficients of `velocityWkTop (k + 1)`. -/
theorem profileCoefficientBounds (k : ℕ) :
    Selfsimilar.ProfileCoefficientBounds k D.transportCoefficients D.stretchingCoefficients := by
  have hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m D.U) ⊤ volume :=
    fun m _ ↦ D.memLp_top_iteratedFDeriv m
  have hb : (fun i ↦ wkpBaseCoordinateCLM (D.velocityWkTop (k + 1) i)) =
      D.transportCoefficients := funext fun i ↦ Lp.ext (by
    have h : baseRepresentative (D.velocityWkTop (k + 1) i) =ᵐ[volume] _ :=
      (baseRepresentative_vectorWkpOfContDiff D.U D.contDiff_U hmem i).trans
        (D.transportCoefficients_ae i).symm
    simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
      wkpBaseCoordinateCLM_apply] using h)
  have hc : (fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (D.velocityWkTop (k + 1) j))) =
      D.stretchingCoefficients := funext fun j ↦ funext fun i ↦ Lp.ext (by
    have h : baseRepresentative (partialDerivCLM i (D.velocityWkTop (k + 1) j)) =ᵐ[volume] _ :=
      (baseRepresentative_partialDerivCLM_vectorWkpOfContDiff (k := k) D.U D.contDiff_U
        hmem j i).trans (D.stretchingCoefficients_ae j i).symm
    simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
      wkpBaseCoordinateCLM_apply] using h)
  rw [← hb, ← hc]
  exact Selfsimilar.ProfileCoefficientBounds.of_profile (D.velocityWkTop (k + 1))

end NavierStokes.Nonuniqueness.UnstableProfile
