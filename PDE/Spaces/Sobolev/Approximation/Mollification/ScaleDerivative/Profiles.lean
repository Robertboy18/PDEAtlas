/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.FDeriv.PartialDeriv

/-!
# Signed derivative profiles of a mollifier

Spatial differentiation gives `∂[i] ρ`, while differentiation of the scale gives
`-n * ρ(z) - Dρ(z)[z]`. These profiles are smooth and supported in the original
kernel's closed support. Neither assertion uses radial symmetry. The standard
mollifier in this library has outer radius two.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace SobolevSpace.Approximation

variable {n : ℕ}

namespace Mollifier

/-- The signed kernel profile for differentiation in spatial coordinate `i`. -/
def spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) : ℝ^n → ℝ :=
  ∂[i] μ.ρ

/-- The signed kernel profile for differentiation of the positive scale. -/
def normalDerivativeProfile (μ : Mollifier n) (z : ℝ^n) : ℝ :=
  -(n : ℝ) * μ.ρ z - fderiv ℝ μ.ρ z z

/-- Spatial derivative profiles are smooth to every finite order. -/
theorem contDiff_spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (μ.spatialDerivativeProfile i) :=
  (μ.smooth.fderiv_right (by simp)).clm_apply contDiff_const

/-- The scale derivative profile is smooth to every finite order. -/
theorem contDiff_normalDerivativeProfile (μ : Mollifier n) :
    ContDiff ℝ (⊤ : ℕ∞) μ.normalDerivativeProfile :=
  (contDiff_const.mul μ.smooth).sub
    ((μ.smooth.fderiv_right (by simp)).clm_apply contDiff_id)

/-- A spatial derivative profile has no support outside the kernel's closed support. -/
theorem tsupport_spatialDerivativeProfile_subset (μ : Mollifier n) (i : Fin n) :
    tsupport (μ.spatialDerivativeProfile i) ⊆ tsupport μ.ρ :=
  tsupport_fderiv_apply_subset ℝ _

/-- The scale derivative profile has no support outside the kernel's closed support. -/
theorem tsupport_normalDerivativeProfile_subset (μ : Mollifier n) :
    tsupport μ.normalDerivativeProfile ⊆ tsupport μ.ρ := by
  apply closure_minimal _ (isClosed_tsupport μ.ρ)
  intro z hz
  by_contra h
  have hρ := image_eq_zero_of_notMem_tsupport h
  have hD := fderiv_of_notMem_tsupport ℝ h
  exact hz (by simp [normalDerivativeProfile, hρ, hD])

/-- Spatial derivative profiles are compactly supported. -/
theorem hasCompactSupport_spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) :
    HasCompactSupport (μ.spatialDerivativeProfile i) :=
  μ.compactSupport.fderiv_apply ℝ _

/-- The scale derivative profile is compactly supported. -/
theorem hasCompactSupport_normalDerivativeProfile (μ : Mollifier n) :
    HasCompactSupport μ.normalDerivativeProfile :=
  μ.compactSupport.of_isClosed_subset (isClosed_tsupport _)
    μ.tsupport_normalDerivativeProfile_subset

/-- Spatial derivative profiles are integrable with respect to Lebesgue measure. -/
theorem integrable_spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) :
    Integrable (μ.spatialDerivativeProfile i) :=
  (μ.contDiff_spatialDerivativeProfile i).continuous.integrable_of_hasCompactSupport
    (μ.hasCompactSupport_spatialDerivativeProfile i)

/-- The scale derivative profile is integrable with respect to Lebesgue measure. -/
theorem integrable_normalDerivativeProfile (μ : Mollifier n) :
    Integrable μ.normalDerivativeProfile :=
  μ.contDiff_normalDerivativeProfile.continuous.integrable_of_hasCompactSupport
    μ.hasCompactSupport_normalDerivativeProfile

/-- In dimension zero, changing scale does not change a kernel. -/
@[simp]
theorem normalDerivativeProfile_zero_dim (μ : Mollifier 0) (z : ℝ^0) :
    μ.normalDerivativeProfile z = 0 := by
  have hz : z = 0 := Subsingleton.elim _ _
  simp [normalDerivativeProfile, hz]

end Mollifier

/-- The closed support of the standard kernel lies in the closed ball of radius two. -/
theorem tsupport_standardMollifier_subset_closedBall (n : ℕ) :
    tsupport (standardMollifier n).ρ ⊆ Metric.closedBall (0 : ℝ^n) 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra h
  have hn : 2 ≤ ‖z‖ := le_of_lt (by simpa using h)
  apply hz
  rw [standardMollifier_eq_norm, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hn),
    zero_div]

/-- The spatial derivative of the standard kernel retains its radius-two support bound. -/
theorem tsupport_standardMollifier_spatialDerivativeProfile_subset_closedBall
    (i : Fin n) :
    tsupport ((standardMollifier n).spatialDerivativeProfile i) ⊆
      Metric.closedBall (0 : ℝ^n) 2 :=
  ((standardMollifier n).tsupport_spatialDerivativeProfile_subset i).trans
    (tsupport_standardMollifier_subset_closedBall n)

/-- The scale derivative of the standard kernel retains its radius-two support bound. -/
theorem tsupport_standardMollifier_normalDerivativeProfile_subset_closedBall (n : ℕ) :
    tsupport (standardMollifier n).normalDerivativeProfile ⊆
      Metric.closedBall (0 : ℝ^n) 2 :=
  (standardMollifier n).tsupport_normalDerivativeProfile_subset.trans
    (tsupport_standardMollifier_subset_closedBall n)

end SobolevSpace.Approximation
