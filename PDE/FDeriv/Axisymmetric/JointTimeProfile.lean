/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.ClassicalTimeProfile
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.SpaceTime

/-!
# Joint space-time calculus for time profiles

`SmoothTimeProfile` imposes smoothness only on each fixed-time spatial slice. That is
enough for the spatial product rules, but not for commuting a spatial derivative with `∂ₜ`:
without joint regularity the mixed derivatives `∂ₜ∂ᵣ f` and `∂ᵣ∂ₜ f` need not agree, or exist.
Here we take profiles `f : (ℝ^2) → ℝ → ℝ` that are `C^∞` as functions on `(ℝ^2) × ℝ`.
They form a subalgebra `JointSmoothTimeProfile` of `TimeProfile`, on which directional
derivatives are Mathlib `Derivation`s.

The three coordinate derivations `jointTimeProfileDr`, `jointTimeProfileDz`,
`jointTimeProfileDt` are the Fréchet derivative of the uncurried profile applied to the fixed
directions `(e₀, 0)`, `(e₁, 0)`, `(0, 1)`. Any two such derivations commute; this is the
symmetry of the second Fréchet derivative of a `C²` function,
`fderiv_fderiv_apply_comm`. Each derivation agrees pointwise with the corresponding field of
`classicalAxisymmetricTimeDifferential`, by the slice lemmas `deriv_prod_timeSlice`
(`PDE.Analysis.Calculus.Prod.SliceDerivative`) and `partialDeriv_prod_spaceSlice`
(`PDE.FDeriv.SpaceTime`), so the commutation results transfer
to the classical operators used in the PDE residuals.

## Main results

* `jointSmoothTimeProfileSubalgebra`, `JointSmoothTimeProfile`: the ℝ-subalgebra of jointly
  smooth profiles, and `JointSmoothTimeProfile.toSmoothTimeProfile` forgetting time regularity.
* `jointTimeProfileDirectionalDerivation`: differentiation in a fixed space-time direction is a
  derivation (linear and Leibniz) of this algebra.
* `jointTimeProfileDirectionalPartial_comm`, `jointTimeProfileDt_Dr_comm`,
  `jointTimeProfileDt_Dz_comm`: directional derivatives commute.
* `jointTimeProfileDt_apply`, `jointTimeProfileDr_apply`, `jointTimeProfileDz_apply` and the
  `_coe` versions: the derivations agree with `classicalAxisymmetricTimeDifferential.dt`,
  `.dr`, `.dz` on jointly smooth profiles.
* `classical_dt_dr_comm`, `classical_dt_dz_comm`: the classical time derivative commutes with
  the classical radial and axial derivatives on jointly smooth profiles.

## Implementation notes

The subalgebra carrier is stated via `Function.uncurry`, so membership is
`ContDiff ℝ ⊤ (fun xt ↦ f xt.1 xt.2)`. The derivations return elements of the subalgebra
again, using `ContDiff.fderiv_right` to see that the derivative of a `C^∞` function is `C^∞`.
-/

@[expose] public section

noncomputable section

open PDE.CoordinateSystems (meridianR meridianZ)

namespace PDE.FDeriv

/-- Time profiles jointly smooth in the spatial variables and time. -/
def jointSmoothTimeProfileSubalgebra : Subalgebra ℝ TimeProfile where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)}
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : (ℝ^2) × ℝ ↦ 0)
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : (ℝ^2) × ℝ ↦ 1)
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      f xt.1 xt.2 + g xt.1 xt.2)
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      f xt.1 xt.2) at hf
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      g xt.1 xt.2) at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      f xt.1 xt.2 * g xt.1 xt.2)
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      f xt.1 xt.2) at hf
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt : (ℝ^2) × ℝ ↦
      g xt.1 xt.2) at hg
    exact hf.mul hg
  algebraMap_mem' := by
    intro c
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : (ℝ^2) × ℝ ↦ c)
    exact contDiff_const

/-- The type of jointly smooth time profiles. -/
abbrev JointSmoothTimeProfile := jointSmoothTimeProfileSubalgebra

namespace JointSmoothTimeProfile

/-- Joint space-time smoothness of a profile. -/
theorem contDiff (f : JointSmoothTimeProfile) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (f : TimeProfile)) :=
  f.property

/-- Joint differentiability of a profile. -/
theorem differentiable (f : JointSmoothTimeProfile) :
    Differentiable ℝ (Function.uncurry (f : TimeProfile)) :=
  (contDiff f).differentiable (by simp)

/-- Forget time regularity while retaining the spatially smooth profile. -/
def toSmoothTimeProfile (f : JointSmoothTimeProfile) : SmoothTimeProfile :=
  ⟨(f : TimeProfile), by
    intro t
    exact (contDiff f).comp
      (by fun_prop :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ^2) ↦ (x, t)))⟩

/-- Forgetting time regularity does not change the underlying profile. -/
@[simp]
theorem toSmoothTimeProfile_coe (f : JointSmoothTimeProfile) :
    (toSmoothTimeProfile f : TimeProfile) = (f : TimeProfile) :=
  rfl

end JointSmoothTimeProfile

/-- Directional derivative of a jointly smooth profile in a fixed
space-time direction. -/
def jointTimeProfileDirectionalPartial
    (v : (ℝ^2) × ℝ) (f : JointSmoothTimeProfile) :
    JointSmoothTimeProfile :=
  ⟨fun x t ↦
      (fderiv ℝ (Function.uncurry (f : TimeProfile)) (x, t)) v,
    by
      have hfderiv :
          ContDiff ℝ (⊤ : ℕ∞)
            (fderiv ℝ (Function.uncurry (f : TimeProfile))) := by
        simpa using
          ((JointSmoothTimeProfile.contDiff f).fderiv_right
            (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp))
      exact hfderiv.clm_apply
        (contDiff_const :
          ContDiff ℝ (⊤ : ℕ∞) (fun _ : (ℝ^2) × ℝ ↦ v))⟩

/-- Directional differentiation is a derivation of the jointly smooth
profile algebra. -/
def jointTimeProfileDirectionalDerivation (v : (ℝ^2) × ℝ) :
    Derivation ℝ JointSmoothTimeProfile JointSmoothTimeProfile where
  toLinearMap :=
    { toFun := jointTimeProfileDirectionalPartial v
      map_add' := by
        intro f g
        apply Subtype.ext
        funext x t
        change
          (fderiv ℝ
            (fun xt : (ℝ^2) × ℝ ↦
              (f : TimeProfile) xt.1 xt.2 +
                (g : TimeProfile) xt.1 xt.2) (x, t)) v =
            (fderiv ℝ
              (Function.uncurry (f : TimeProfile)) (x, t)) v +
              (fderiv ℝ
                (Function.uncurry (g : TimeProfile)) (x, t)) v
        change
          (fderiv ℝ
            (Function.uncurry (f : TimeProfile) +
              Function.uncurry (g : TimeProfile)) (x, t)) v =
            (fderiv ℝ
              (Function.uncurry (f : TimeProfile)) (x, t)) v +
              (fderiv ℝ
                (Function.uncurry (g : TimeProfile)) (x, t)) v
        rw [fderiv_add
          (JointSmoothTimeProfile.differentiable f).differentiableAt
          (JointSmoothTimeProfile.differentiable g).differentiableAt]
        rfl
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext x t
        change
          (fderiv ℝ
            (fun xt : (ℝ^2) × ℝ ↦
              c * (f : TimeProfile) xt.1 xt.2) (x, t)) v =
            c *
              (fderiv ℝ
                (Function.uncurry (f : TimeProfile)) (x, t)) v
        change
          (fderiv ℝ
            (c • Function.uncurry (f : TimeProfile)) (x, t)) v =
            c *
              (fderiv ℝ
                (Function.uncurry (f : TimeProfile)) (x, t)) v
        rw [fderiv_const_smul
          (JointSmoothTimeProfile.differentiable f).differentiableAt c]
        simp [smul_eq_mul] }
  map_one_eq_zero' := by
    apply Subtype.ext
    funext x t
    change (fderiv ℝ (fun _ : (ℝ^2) × ℝ ↦ (1 : ℝ)) (x, t)) v = 0
    simp
  leibniz' := by
    intro f g
    apply Subtype.ext
    funext x t
    change
      (fderiv ℝ
        (fun xt : (ℝ^2) × ℝ ↦
          (f : TimeProfile) xt.1 xt.2 *
            (g : TimeProfile) xt.1 xt.2) (x, t)) v =
        (f : TimeProfile) x t *
            (fderiv ℝ
              (Function.uncurry (g : TimeProfile)) (x, t)) v +
          (g : TimeProfile) x t *
            (fderiv ℝ
              (Function.uncurry (f : TimeProfile)) (x, t)) v
    change
      (fderiv ℝ
        (Function.uncurry (f : TimeProfile) *
          Function.uncurry (g : TimeProfile)) (x, t)) v =
        (f : TimeProfile) x t *
            (fderiv ℝ
              (Function.uncurry (g : TimeProfile)) (x, t)) v +
          (g : TimeProfile) x t *
            (fderiv ℝ
              (Function.uncurry (f : TimeProfile)) (x, t)) v
    rw [fderiv_mul
      (JointSmoothTimeProfile.differentiable f).differentiableAt
      (JointSmoothTimeProfile.differentiable g).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    simp only [Function.uncurry_apply_pair]

/-- Unit radial direction in profile space-time. -/
def radialSpaceTimeDirection : (ℝ^2) × ℝ :=
  (EuclideanSpace.single 0 1, 0)

/-- Unit axial direction in profile space-time. -/
def axialSpaceTimeDirection : (ℝ^2) × ℝ :=
  (EuclideanSpace.single 1 1, 0)

/-- Unit time direction in profile space-time. -/
def timeSpaceTimeDirection : (ℝ^2) × ℝ :=
  (0, 1)

/-- Jointly smooth radial derivative. -/
abbrev jointTimeProfileDr :
    Derivation ℝ JointSmoothTimeProfile JointSmoothTimeProfile :=
  jointTimeProfileDirectionalDerivation radialSpaceTimeDirection

/-- Jointly smooth axial derivative. -/
abbrev jointTimeProfileDz :
    Derivation ℝ JointSmoothTimeProfile JointSmoothTimeProfile :=
  jointTimeProfileDirectionalDerivation axialSpaceTimeDirection

/-- Jointly smooth time derivative. -/
abbrev jointTimeProfileDt :
    Derivation ℝ JointSmoothTimeProfile JointSmoothTimeProfile :=
  jointTimeProfileDirectionalDerivation timeSpaceTimeDirection

/-- Fixed directional derivatives commute on jointly smooth profiles. -/
theorem jointTimeProfileDirectionalPartial_comm
    (v w : (ℝ^2) × ℝ) (f : JointSmoothTimeProfile) :
    jointTimeProfileDirectionalPartial v
        (jointTimeProfileDirectionalPartial w f) =
      jointTimeProfileDirectionalPartial w
        (jointTimeProfileDirectionalPartial v f) := by
  apply Subtype.ext
  funext x t
  have hF2 : ContDiffAt ℝ 2 (Function.uncurry (f : TimeProfile)) (x, t) :=
    (JointSmoothTimeProfile.contDiff f).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt
  change
    (fderiv ℝ (fun y ↦ (fderiv ℝ (Function.uncurry (f : TimeProfile)) y) w) (x, t)) v =
      (fderiv ℝ (fun y ↦ (fderiv ℝ (Function.uncurry (f : TimeProfile)) y) v) (x, t)) w
  exact fderiv_fderiv_apply_comm (Function.uncurry (f : TimeProfile)) (x, t) w v hF2

/-- The time and radial derivations commute on jointly smooth profiles (Schwarz). -/
@[simp]
theorem jointTimeProfileDt_Dr_comm (f : JointSmoothTimeProfile) :
    jointTimeProfileDt (jointTimeProfileDr f) =
      jointTimeProfileDr (jointTimeProfileDt f) :=
  jointTimeProfileDirectionalPartial_comm
    timeSpaceTimeDirection radialSpaceTimeDirection f

/-- The time and axial derivations commute on jointly smooth profiles (Schwarz). -/
@[simp]
theorem jointTimeProfileDt_Dz_comm (f : JointSmoothTimeProfile) :
    jointTimeProfileDt (jointTimeProfileDz f) =
      jointTimeProfileDz (jointTimeProfileDt f) :=
  jointTimeProfileDirectionalPartial_comm
    timeSpaceTimeDirection axialSpaceTimeDirection f

/-! ## Agreement with classical slice derivatives -/

/-- The time derivation is the classical `∂ₜ` of the underlying profile: the Fréchet derivative
of the uncurried profile in direction `(0, 1)` is the one-variable derivative in `t`. -/
@[simp]
theorem jointTimeProfileDt_apply
    (f : JointSmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (jointTimeProfileDt f : TimeProfile) x t =
      classicalAxisymmetricTimeDifferential.dt
        (f : TimeProfile) x t := by
  change
    (fderiv ℝ (Function.uncurry (f : TimeProfile)) (x, t)) (0, 1) =
      deriv (fun s ↦ (f : TimeProfile) x s) t
  exact (deriv_prod_timeSlice (Function.uncurry (f : TimeProfile)) x t
    (JointSmoothTimeProfile.differentiable f).differentiableAt).symm

/-- The radial derivation is the classical `∂ᵣ` of the underlying profile: the Fréchet
derivative of the uncurried profile in direction `(e₀, 0)` is `partialDeriv 0` of the time
slice. -/
@[simp]
theorem jointTimeProfileDr_apply
    (f : JointSmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (jointTimeProfileDr f : TimeProfile) x t =
      classicalAxisymmetricTimeDifferential.dr
        (f : TimeProfile) x t := by
  change
    (fderiv ℝ (Function.uncurry (f : TimeProfile)) (x, t)) (EuclideanSpace.single 0 1, 0) =
      (∂[0] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x
  exact (partialDeriv_prod_spaceSlice 0 (Function.uncurry (f : TimeProfile)) x t
    (JointSmoothTimeProfile.differentiable f).differentiableAt).symm

/-- The axial derivation is the classical `∂_z` of the underlying profile: the Fréchet
derivative of the uncurried profile in direction `(e₁, 0)` is `partialDeriv 1` of the time
slice. -/
@[simp]
theorem jointTimeProfileDz_apply
    (f : JointSmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (jointTimeProfileDz f : TimeProfile) x t =
      classicalAxisymmetricTimeDifferential.dz
        (f : TimeProfile) x t := by
  change
    (fderiv ℝ (Function.uncurry (f : TimeProfile)) (x, t)) (EuclideanSpace.single 1 1, 0) =
      (∂[1] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x
  exact (partialDeriv_prod_spaceSlice 1 (Function.uncurry (f : TimeProfile)) x t
    (JointSmoothTimeProfile.differentiable f).differentiableAt).symm

/-- Function-level form of `jointTimeProfileDt_apply`. -/
theorem jointTimeProfileDt_coe (f : JointSmoothTimeProfile) :
    (jointTimeProfileDt f : TimeProfile) =
      classicalAxisymmetricTimeDifferential.dt (f : TimeProfile) := by
  funext x t
  exact jointTimeProfileDt_apply f x t

/-- Function-level form of `jointTimeProfileDr_apply`. -/
theorem jointTimeProfileDr_coe (f : JointSmoothTimeProfile) :
    (jointTimeProfileDr f : TimeProfile) =
      classicalAxisymmetricTimeDifferential.dr (f : TimeProfile) := by
  funext x t
  exact jointTimeProfileDr_apply f x t

/-- Function-level form of `jointTimeProfileDz_apply`. -/
theorem jointTimeProfileDz_coe (f : JointSmoothTimeProfile) :
    (jointTimeProfileDz f : TimeProfile) =
      classicalAxisymmetricTimeDifferential.dz (f : TimeProfile) := by
  funext x t
  exact jointTimeProfileDz_apply f x t

/-- Classical time and radial derivatives commute on jointly smooth
profiles. -/
theorem classical_dt_dr_comm (f : JointSmoothTimeProfile) :
    classicalAxisymmetricTimeDifferential.dt
        (classicalAxisymmetricTimeDifferential.dr
          (f : TimeProfile)) =
      classicalAxisymmetricTimeDifferential.dr
        (classicalAxisymmetricTimeDifferential.dt
          (f : TimeProfile)) := by
  rw [← jointTimeProfileDr_coe f,
    ← jointTimeProfileDt_coe (jointTimeProfileDr f),
    jointTimeProfileDt_Dr_comm,
    jointTimeProfileDr_coe,
    jointTimeProfileDt_coe]

/-- Classical time and axial derivatives commute on jointly smooth
profiles. -/
theorem classical_dt_dz_comm (f : JointSmoothTimeProfile) :
    classicalAxisymmetricTimeDifferential.dt
        (classicalAxisymmetricTimeDifferential.dz
          (f : TimeProfile)) =
      classicalAxisymmetricTimeDifferential.dz
        (classicalAxisymmetricTimeDifferential.dt
          (f : TimeProfile)) := by
  rw [← jointTimeProfileDz_coe f,
    ← jointTimeProfileDt_coe (jointTimeProfileDz f),
    jointTimeProfileDt_Dz_comm,
    jointTimeProfileDz_coe,
    jointTimeProfileDt_coe]

end PDE.FDeriv
