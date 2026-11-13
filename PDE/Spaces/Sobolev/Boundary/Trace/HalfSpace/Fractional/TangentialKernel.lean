/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Polar
public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral.Lebesgue
public import PDE.Spaces.Sobolev.Calculus.Slicing.Tangential
public import PDE.Spaces.Sobolev.Calculus.Translation.Energy

/-!
# Tangential increments at radial height

Translate a tangential slice by `h` at height `‖h‖`. The translation estimate
contributes `‖h‖^p`; after integration in the tangential variable, polar coordinates
cancel this factor against the fractional trace kernel and its radial Jacobian.
The resulting constant is the total angular measure of the unit sphere.

The radial cancellation identity holds for every measurable nonnegative energy,
including energies with infinite integral. The increment estimate applies to
compactly supported C¹ functions into a real Banach space, for `1 ≤ p` and
positive tangential dimension.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace

variable {n : ℕ}

/-- Integrating tangential slices over positive heights recovers the integral on
the upper half-space. Measurability suffices; no integrability is required. -/
theorem lintegral_lintegral_joinTangentialNormal_eq_lintegral_upper
    {g : ℝ^(n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ r in Ioi (0 : ℝ), ∫⁻ y : ℝ^n, g (joinTangentialNormal (y, r))) =
      ∫⁻ z in ℝ^(n + 1)₊, g z := by
  have hj : Measurable (fun z : ℝ^n × ℝ ↦ g (joinTangentialNormal z)) :=
    hg.comp (tangentialNormalContinuousLinearEquiv (n := n)).symm.continuous.measurable
  calc
    _ = ∫⁻ z, g (joinTangentialNormal z)
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
      (lintegral_prod_symm _ hj.aemeasurable).symm
    _ = _ := lintegral_joinTangentialNormal_eq_lintegral_upper g

/-- Polar integration cancels the tangential trace kernel against the translation
factor and the radial Jacobian, leaving the upper-half-space energy. -/
theorem lintegral_tangential_kernel_mul_energy_eq (hn : 0 < n) (p : ℝ)
    {g : ℝ^(n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
      (ENNReal.ofReal (‖h‖ ^ p) * ∫⁻ y : ℝ^n, g (joinTangentialNormal (y, ‖h‖)))) =
      (volume : Measure (ℝ^n)).toSphere univ * ∫⁻ z in ℝ^(n + 1)₊, g z := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hj : Measurable (fun z : ℝ^n × ℝ ↦ g (joinTangentialNormal z)) :=
    hg.comp (tangentialNormalContinuousLinearEquiv (n := n)).symm.continuous.measurable
  have hprofile : Measurable
      (fun r : ℝ ↦ ENNReal.ofReal (r ^ p) *
        ∫⁻ y : ℝ^n, g (joinTangentialNormal (y, r))) :=
    (by fun_prop : Measurable (fun r : ℝ ↦ ENNReal.ofReal (r ^ p))).mul
      hj.lintegral_prod_left'
  calc
    _ = (volume : Measure (ℝ^n)).toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (-p)) *
          (ENNReal.ofReal (r ^ p) * ∫⁻ y : ℝ^n, g (joinTangentialNormal (y, r))) := by
      simpa using lintegral_norm_rpow_mul_addHaar (volume : Measure (ℝ^n)) p hprofile
    _ = (volume : Measure (ℝ^n)).toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ), ∫⁻ y : ℝ^n, g (joinTangentialNormal (y, r)) := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le (-p)),
        ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    _ = _ := congrArg ((volume : Measure (ℝ^n)).toSphere univ * ·)
      (lintegral_lintegral_joinTangentialNormal_eq_lintegral_upper hg)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A tangential increment at a fixed height is controlled by the ambient derivative
energy of that slice. The tangent inclusion has operator norm at most one. -/
theorem lintegral_tangential_increment_le {p : ℝ} (hp : 1 ≤ p)
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (t : ℝ) (h : ℝ^n) :
    (∫⁻ y, ENNReal.ofReal
      (‖f (joinTangentialNormal (y + h, t)) - f (joinTangentialNormal (y, t))‖ ^ p)) ≤
      ENNReal.ofReal (‖h‖ ^ p) *
        ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ f (joinTangentialNormal (y, t))‖ ^ p) := by
  calc
    _ ≤ ENNReal.ofReal (‖h‖ ^ p) *
        ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (tangentialSlice f t) y‖ ^ p) :=
      Translation.lintegral_norm_sub_rpow_le volume (tangentialSlice_contDiff hf t)
        (tangentialSlice_hasCompactSupport hfc t) hp h
    _ ≤ _ := mul_le_mul_right (lintegral_mono fun y ↦
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _)
        (norm_fderiv_tangentialSlice_le t y
          (hf.differentiable (by simp) (joinTangentialNormal (y, t))))
        (le_trans zero_le_one hp))) _

/-- The fractional tangential increment at radial height is bounded by the ambient
derivative energy on the upper half-space, with the exact angular mass as constant. -/
theorem lintegral_tangential_increment_kernel_le (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
      ∫⁻ y : ℝ^n, ENNReal.ofReal
        (‖f (joinTangentialNormal (y + h, ‖h‖)) -
          f (joinTangentialNormal (y, ‖h‖))‖ ^ p)) ≤
      (volume : Measure (ℝ^n)).toSphere univ *
        ∫⁻ z in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ p) := by
  have hg : Measurable (fun z ↦ ENNReal.ofReal (‖fderiv ℝ f z‖ ^ p)) :=
    ((hf.continuous_fderiv (by simp)).norm.rpow_const
      (fun _ ↦ Or.inr (le_trans zero_le_one hp))).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
        (ENNReal.ofReal (‖h‖ ^ p) *
          ∫⁻ y : ℝ^n, ENNReal.ofReal
            (‖fderiv ℝ f (joinTangentialNormal (y, ‖h‖))‖ ^ p)) :=
      lintegral_mono fun h ↦ mul_le_mul_right
        (lintegral_tangential_increment_le hp hf hfc ‖h‖ h) _
    _ = _ := lintegral_tangential_kernel_mul_energy_eq hn p hg

end SobolevSpace.Trace.HalfSpace
