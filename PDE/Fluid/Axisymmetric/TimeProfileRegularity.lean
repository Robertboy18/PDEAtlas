/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.JointTimeProfile
public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.TimeProfile
public import PDE.Fluid.Axisymmetric.AxisRegularDiffusion
public import PDE.Fluid.Axisymmetric.CartesianVorticity
import PDE.FDeriv.Reflection.Coordinate

/-!
# Smooth time profiles in squared-radius coordinates

For a profile written as `f(r,z,t) = Φ(r²,z,t)`, the radial chain rule gives
`∂r f = 2r ∂s Φ`. The apparent quotient `∂r f / r` therefore has the smooth
extension `2 ∂s Φ`, evaluated at `(r²,z,t)`. The second radial chain rule
identifies that extension with `∂rr f` at the axis. These identities let the
axis-extended stream operator act on smooth functions.

`axisRegularPullback` needs smoothness of each spatial slice.
`jointAxisRegularPullback` retains the stronger joint space-time smoothness
needed for time-dependent equations. `IsAxisRegularTimeProfile` asks for such
a joint generator; the proofs then obtain radial evenness, the zero first
radial derivative at the axis, and a smooth radial quotient. A zero radial
derivative alone is not the generator hypothesis.

The squared-radius normalization and its Cartesian velocity formulas are
explained in `PDE.Fluid.Axisymmetric.CartesianReconstruction`.
-/

@[expose] public section

noncomputable section

open PDE.Common PDE.FDeriv
open PDE.CoordinateSystems (meridianR meridianZ)

namespace AxisymmetricFlow

/-! ## Constructive pullbacks -/

/-- Pull a spatially smooth profile in `(s, z)` coordinates back by `s = r²`. -/
def axisRegularPullback (Φ : SmoothTimeProfile) : SmoothTimeProfile :=
  ⟨fun x t ↦ (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap x) t, by
    intro t
    exact
      (SmoothTimeProfile.contDiff Φ t).comp
        AxisymmetricFlow.contDiff_squaredRadiusMap⟩

/-- Pointwise value of the spatial pullback: `Φ(r², z, t)`. -/
@[simp]
theorem axisRegularPullback_apply
    (Φ : SmoothTimeProfile) (x : ℝ^2) (t : ℝ) :
    (axisRegularPullback Φ : TimeProfile) x t =
      (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap x) t :=
  rfl

/-- Pull a jointly smooth profile back by `s = r²`, retaining joint
space-time smoothness. -/
def jointAxisRegularPullback
    (Φ : JointSmoothTimeProfile) : JointSmoothTimeProfile :=
  ⟨fun x t ↦ (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap x) t, by
    have hmap :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun xt : ℝ^2 × ℝ ↦
            (AxisymmetricFlow.squaredRadiusMap xt.1, xt.2)) := by
      exact
        (AxisymmetricFlow.contDiff_squaredRadiusMap.comp contDiff_fst).prodMk
          contDiff_snd
    exact (JointSmoothTimeProfile.contDiff Φ).comp hmap⟩

/-- Pointwise value of the joint pullback: `Φ(r², z, t)`. -/
@[simp]
theorem jointAxisRegularPullback_apply
    (Φ : JointSmoothTimeProfile) (x : ℝ^2) (t : ℝ) :
    (jointAxisRegularPullback Φ : TimeProfile) x t =
      (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap x) t :=
  rfl

/-- Forgetting time regularity commutes with the squared-radius pullback. -/
theorem jointAxisRegularPullback_toSmoothTimeProfile
    (Φ : JointSmoothTimeProfile) :
    JointSmoothTimeProfile.toSmoothTimeProfile
        (jointAxisRegularPullback Φ) =
      axisRegularPullback
        (JointSmoothTimeProfile.toSmoothTimeProfile Φ) := by
  apply Subtype.ext
  rfl

/--
A time profile is axis regular when it factors through `r²` with a generator
that is jointly smooth in squared radius, axial position, and time.
-/
def IsAxisRegularTimeProfile (f : TimeProfile) : Prop :=
  ∃ Φ : JointSmoothTimeProfile,
    f = (jointAxisRegularPullback Φ : TimeProfile)

/-- A squared-radius pullback is axis regular, with its generator as the witness. -/
theorem jointAxisRegularPullback_isAxisRegular
    (Φ : JointSmoothTimeProfile) :
    IsAxisRegularTimeProfile
      (jointAxisRegularPullback Φ : TimeProfile) :=
  ⟨Φ, rfl⟩

/-- Factorization through a jointly smooth generator implies joint
space-time smoothness of the profile itself. -/
theorem IsAxisRegularTimeProfile.contDiff
    {f : TimeProfile} (hf : IsAxisRegularTimeProfile f) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) := by
  rcases hf with ⟨Φ, rfl⟩
  exact JointSmoothTimeProfile.contDiff (jointAxisRegularPullback Φ)

/-! ## Parity -/

/-- Every time slice of a squared-radius pullback is even under reflection of the radial
coordinate. -/
theorem isEvenUnderCoordinateReflection_jointAxisRegularPullback
    (Φ : JointSmoothTimeProfile) (t : ℝ) :
    IsEvenUnderCoordinateReflection 0
      (fun x ↦ (jointAxisRegularPullback Φ : TimeProfile) x t) := by
  intro x
  change
    (Φ : TimeProfile)
        (AxisymmetricFlow.squaredRadiusMap (coordinateReflection 0 x)) t =
      (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap x) t
  have hmap :
      AxisymmetricFlow.squaredRadiusMap (coordinateReflection 0 x) =
        AxisymmetricFlow.squaredRadiusMap x := by
    ext i
    fin_cases i <;> simp [AxisymmetricFlow.squaredRadiusMap]
  rw [hmap]

/-- Every time slice of an axis-regular profile is even under reflection of the radial
coordinate. -/
theorem IsAxisRegularTimeProfile.radial_even
    {f : TimeProfile} (hf : IsAxisRegularTimeProfile f) (t : ℝ) :
    IsEvenUnderCoordinateReflection 0 (fun x ↦ f x t) := by
  rcases hf with ⟨Φ, rfl⟩
  exact isEvenUnderCoordinateReflection_jointAxisRegularPullback Φ t

/-! ## Classical radial derivatives -/

/-- The radial chain rule for a spatially smooth squared-radius pullback. -/
@[simp]
theorem smoothTimeProfileDr_axisRegularPullback
    (Φ : SmoothTimeProfile) :
    smoothTimeProfileDr (axisRegularPullback Φ) =
      (2 : ℝ) •
        (SmoothTimeProfile.radialCoordinate *
          axisRegularPullback (smoothTimeProfileDr Φ)) := by
  apply Subtype.ext
  funext x t
  change
    (∂[0]
        (fun y : ℝ^2 ↦
          (Φ : TimeProfile) (AxisymmetricFlow.squaredRadiusMap y) t)) x =
      2 * (meridianR x *
        (∂[0]
          (fun y : ℝ^2 ↦ (Φ : TimeProfile) y t))
          (AxisymmetricFlow.squaredRadiusMap x))
  have hchain :=
    AxisymmetricFlow.partialDeriv_zero_squaredRadiusPullback
      (Φ := fun y : ℝ^2 ↦ (Φ : TimeProfile) y t)
      ((SmoothTimeProfile.contDiff Φ t).of_le (by norm_num)) x
  calc
    _ = 2 * x 0 *
        (∂[0]
          (fun y : ℝ^2 ↦ (Φ : TimeProfile) y t))
          (AxisymmetricFlow.squaredRadiusMap x) := hchain
    _ = _ := by simp only [meridianR]; ring

/-- The classical radial derivative of an axis-regular pullback vanishes on
the symmetry axis. -/
theorem classical_dr_axisRegularPullback_eq_zero
    (Φ : SmoothTimeProfile) (x : ℝ^2) (t : ℝ)
    (hx : meridianR x = 0) :
    classicalAxisymmetricTimeDifferential.dr
        (axisRegularPullback Φ : TimeProfile) x t = 0 := by
  change
    (smoothTimeProfileDr (axisRegularPullback Φ) : TimeProfile) x t = 0
  rw [smoothTimeProfileDr_axisRegularPullback]
  simp [hx]

/-- Every axis-regular profile has zero classical radial derivative on the
axis: each time slice is even under the radial reflection, so LeanPDE's
`IsEvenUnderCoordinateReflection.partialDeriv_eq_zero` applies on the reflecting
hyperplane `r = 0`. -/
theorem IsAxisRegularTimeProfile.classical_dr_eq_zero
    {f : TimeProfile} (hf : IsAxisRegularTimeProfile f)
    (x : ℝ^2) (t : ℝ) (hx : meridianR x = 0) :
    classicalAxisymmetricTimeDifferential.dr f x t = 0 := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^2 ↦ f y t) :=
    hf.contDiff.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^2 ↦ (y, t)))
  exact (hf.radial_even t).partialDeriv_eq_zero hx
    (hslice.differentiable (by simp)).differentiableAt

/-- The second radial chain rule for a squared-radius pullback. -/
theorem smoothTimeProfileDrr_axisRegularPullback
    (Φ : SmoothTimeProfile) :
    smoothTimeProfileDr
        (smoothTimeProfileDr (axisRegularPullback Φ)) =
      (2 : ℝ) • axisRegularPullback (smoothTimeProfileDr Φ) +
        (4 : ℝ) •
          (SmoothTimeProfile.radialCoordinate *
            SmoothTimeProfile.radialCoordinate *
            axisRegularPullback
              (smoothTimeProfileDr (smoothTimeProfileDr Φ))) := by
  rw [smoothTimeProfileDr_axisRegularPullback]
  simp only [Derivation.map_smul, Derivation.leibniz,
    smoothTimeProfileDr_axisRegularPullback, smul_eq_mul,
    Algebra.mul_smul_comm, smoothTimeProfileDr_radialCoordinate, mul_one,
    smul_add]
  apply Subtype.ext
  funext x t
  simp
  ring

/-- Raw-profile form of the second radial chain rule. -/
theorem classical_drr_axisRegularPullback
    (Φ : SmoothTimeProfile) :
    classicalAxisymmetricTimeDifferential.drr
        (axisRegularPullback Φ : TimeProfile) =
      (((2 : ℝ) • axisRegularPullback (smoothTimeProfileDr Φ) +
        (4 : ℝ) •
          (SmoothTimeProfile.radialCoordinate *
            SmoothTimeProfile.radialCoordinate *
            axisRegularPullback
              (smoothTimeProfileDr (smoothTimeProfileDr Φ))) :
          SmoothTimeProfile) : TimeProfile) := by
  change
    ((smoothTimeProfileDr
      (smoothTimeProfileDr (axisRegularPullback Φ)) :
        SmoothTimeProfile) : TimeProfile) = _
  exact congrArg
    (fun g : SmoothTimeProfile ↦ (g : TimeProfile))
    (smoothTimeProfileDrr_axisRegularPullback Φ)

/--
The concrete regularized quotient `dr/r` is the smooth pullback
`2 ∂s Φ` at every point, including the axis.
-/
theorem classical_drOverR_axisRegularPullback
    (Φ : SmoothTimeProfile) :
    classicalAxisymmetricTimeDifferential.drOverR
        (axisRegularPullback Φ : TimeProfile) =
      (((2 : ℝ) •
        axisRegularPullback (smoothTimeProfileDr Φ) :
          SmoothTimeProfile) : TimeProfile) := by
  funext x t
  by_cases hr : meridianR x = 0
  · rw [classical_drOverR_of_eq_zero _ _ _ hr]
    rw [congrFun
      (congrFun (classical_drr_axisRegularPullback Φ) x) t]
    simp [hr]
  · have hDr := congrArg
      (fun g : SmoothTimeProfile ↦ (g : TimeProfile))
      (smoothTimeProfileDr_axisRegularPullback Φ)
    have hAt := congrFun (congrFun hDr x) t
    rw [classical_drOverR_of_ne_zero _ _ _ hr]
    change _ = 2 *
      (axisRegularPullback (smoothTimeProfileDr Φ) : TimeProfile) x t
    change
      classicalAxisymmetricTimeDifferential.dr
          (axisRegularPullback Φ : TimeProfile) x t =
        2 * (meridianR x *
          (axisRegularPullback
            (smoothTimeProfileDr Φ) : TimeProfile) x t) at hAt
    rw [hAt]
    field_simp [hr]

/-- The spatial radial derivative obtained from joint calculus agrees with
the radial derivative after forgetting time regularity. -/
theorem jointTimeProfileDr_toSmoothTimeProfile
    (Φ : JointSmoothTimeProfile) :
    JointSmoothTimeProfile.toSmoothTimeProfile
        (jointTimeProfileDr Φ) =
      smoothTimeProfileDr
        (JointSmoothTimeProfile.toSmoothTimeProfile Φ) := by
  apply Subtype.ext
  funext x t
  change
    (jointTimeProfileDr Φ : TimeProfile) x t =
      (smoothTimeProfileDr
        (JointSmoothTimeProfile.toSmoothTimeProfile Φ) :
          TimeProfile) x t
  rw [smoothTimeProfileDr_apply, jointTimeProfileDr_apply]
  rfl

/-- The smooth extension of `dr/r` associated to a jointly smooth
axis-regular generator. -/
def jointAxisRegularRadialQuotient
    (Φ : JointSmoothTimeProfile) : JointSmoothTimeProfile :=
  (2 : ℝ) • jointAxisRegularPullback (jointTimeProfileDr Φ)

/-- On a jointly smooth squared-radius pullback, the concrete `dr/r` slot is
represented by a jointly smooth profile. -/
theorem classical_drOverR_jointAxisRegularPullback
    (Φ : JointSmoothTimeProfile) :
    classicalAxisymmetricTimeDifferential.drOverR
        (jointAxisRegularPullback Φ : TimeProfile) =
      (jointAxisRegularRadialQuotient Φ : TimeProfile) := by
  have hs :=
    classical_drOverR_axisRegularPullback
      (JointSmoothTimeProfile.toSmoothTimeProfile Φ)
  have hpull : (jointAxisRegularPullback Φ : TimeProfile) =
      (axisRegularPullback
        (JointSmoothTimeProfile.toSmoothTimeProfile Φ) : TimeProfile) :=
    congrArg Subtype.val (jointAxisRegularPullback_toSmoothTimeProfile Φ)
  funext x t
  rw [hpull]
  have hst := congrFun (congrFun hs x) t
  simpa [jointAxisRegularRadialQuotient,
    jointTimeProfileDr_toSmoothTimeProfile] using hst

/-! ## Elliptic operator in squared-radius coordinates -/

/-- On a smooth squared-radius pullback, the signed axisymmetric elliptic
operator is the negative azimuthal-vorticity coefficient of the generator. -/
theorem signedAxisymmetricTimeElliptic_jointAxisRegularPullback
    (Psi : JointSmoothTimeProfile) (x : ℝ^2) (t : ℝ) :
    signedAxisymmetricTimeElliptic classicalAxisymmetricTimeDifferential
        (jointAxisRegularPullback Psi : TimeProfile) x t =
      -AxisymmetricFlow.meridionalVorticityCoefficient
        (fun q ↦ (Psi : TimeProfile) q t)
        (AxisymmetricFlow.squaredRadiusMap x) := by
  have hPsi : ContDiff ℝ 2 (fun q ↦ (Psi : TimeProfile) q t) :=
    ((JointSmoothTimeProfile.toSmoothTimeProfile Psi).property t).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [signedAxisymmetricTimeElliptic]
  rw [axisymmetricTimeLaplacian_classical_eq_axisExtended]
  change
    -AxisymmetricFlow.axisExtendedRadialFourAxialLaplacian
        (AxisymmetricFlow.squaredRadiusPullback
          (fun q ↦ (Psi : TimeProfile) q t)) x = _
  rw [AxisymmetricFlow.axisExtendedRadialFourAxialLaplacian_squaredRadiusPullback
    hPsi]
  simp [AxisymmetricFlow.squaredRadiusDiffusionPullback,
    AxisymmetricFlow.meridionalVorticityCoefficient]
  ring

/-- Every axis-regular profile has a jointly smooth representative of its
regularized radial quotient. -/
theorem IsAxisRegularTimeProfile.exists_jointSmooth_drOverR
    {f : TimeProfile} (hf : IsAxisRegularTimeProfile f) :
    ∃ q : JointSmoothTimeProfile,
      classicalAxisymmetricTimeDifferential.drOverR f =
        (q : TimeProfile) := by
  rcases hf with ⟨Φ, rfl⟩
  exact ⟨jointAxisRegularRadialQuotient Φ,
    classical_drOverR_jointAxisRegularPullback Φ⟩

end AxisymmetricFlow
