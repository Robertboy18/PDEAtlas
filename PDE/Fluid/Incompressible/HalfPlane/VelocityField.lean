/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityHigherOrder
public import PDE.Analysis.ODE.Flow.SecondVariation
public import PDE.Analysis.Calculus.Osgood
import PDE.Analysis.Calculus.HolderInterpolation
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Normed.PiLp.CoordinateProjection
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# The half-plane velocity as a field on the whole plane

The half-plane velocity `u = halfPlaneVelocity f` of a vorticity `f` given on the closed upper
half-plane `H̄ = {x₁ ≥ 0}` is smooth only within `H̄`. The extended velocity
`extendedVelocity K f` is the weighted reflection of order `K` of each component of `u` across
the boundary line: it equals `u` on `H̄`, its normal component vanishes on the boundary line, it is
`C^K` on the plane whenever `u` is `C^K` within `H̄`, and its first two derivatives are bounded by
fixed multiples of the bounds of the derivatives of `u` within `H̄`.

For a vorticity history `ω t` with uniform bounds on a time interval `[a, b]` (`IsVorticityHistory`:
continuity on `H̄`, a common support disc, a sup bound and an `α`-Hölder bound, continuity in time
uniformly on `H̄`), the extended velocities form a jointly continuous `C¹` field on `[a, b] × ℝ²`
with bounded derivative (`IsVorticityHistory.isC1FieldOn`), so the flow theory of `PDE.Analysis.ODE`
applies to them. For a history that is in addition `C¹` with an `α`-Hölder gradient
(`IsC1VorticityHistory`), the extended velocities form a `C²` field
(`IsC1VorticityHistory.isC2FieldOn`).

For `C¹` vorticity without a Hölder bound on the gradient the derivative of the velocity is
log-Lipschitz on `H̄` (`dist_fderivWithin_halfPlaneVelocity_le_log_of_support`).

## Main definitions

* `extendedVelocity`: the weighted reflection of order `K` of each component of
  `halfPlaneVelocity f` across the boundary line `x₁ = 0`.
* `katoBound`: the Kato bound `4((50/α)(1 + B log(2 + M)) + 8B + 10πR²B)` of the derivative of the
  velocity.
* `IsVorticityHistory`: a vorticity history on `[a, b]` with a common support disc, a sup bound,
  an `α`-Hölder bound and continuity in time uniformly on `H̄`.
* `IsC1VorticityHistory`: a vorticity history that is `C¹` within `H̄` with a bounded `α`-Hölder
  gradient, continuous in time uniformly on `H̄`.

## Main results

* `extendedVelocity_of_nonneg`: on `H̄` the extended velocity is the velocity; its normal
  component vanishes on the boundary line (`extendedVelocity_normal_eq_zero`).
* `contDiff_extendedVelocity`: the extended velocity is `C^K` when the velocity is `C^K` within
  `H̄`.
* `norm_fderiv_extendedVelocity_le`: the derivative of the extended velocity is at most `2 c₁`
  times the bound of the derivative of the velocity within `H̄`.
* `norm_fderivWithin_halfPlaneVelocity_le_katoModulus`: the homogeneous Kato bound, for data
  bounded by `η ∈ (0, 1]`, which applies to differences.
* `IsVorticityHistory.exists_norm_fderivWithin_sub_le`: the derivative of the velocity is
  continuous in time, uniformly on `H̄`.
* `IsVorticityHistory.isC1FieldOn`: for `0 < α < 1` the extended velocities form a `C¹` field on
  `[a, b] × ℝ²` with bounded derivative.
* `IsC1VorticityHistory.isC2FieldOn`: for a `C¹` history the extended velocities of order two form
  a `C²` field.
* `dist_fderivWithin_halfPlaneVelocity_le_log_of_support`: for `C¹` vorticity the derivative of
  the velocity is log-Lipschitz on `H̄`.

## How it works

We extend each component of `u` by the weighted reflection `weightedReflectionFun 1 K` across
`x₁ = 0`, which is the function itself on `H̄` and a weighted sum of its values at dilated reflected
points below the line. By `PDE.Analysis.contDiff_weightedReflectionFun` the extension is `C^K` on
the plane, and the bounds `reflectionBound K m` of the reflection give
`norm_extendedVelocity_sub_le` and `norm_fderiv_extendedVelocity_le`. For a vorticity history the
velocity at each time is `C¹` within `H̄` with derivative at most `katoBound α R₀ B M`
(`norm_fderivWithin_halfPlaneVelocity_le_katoBound`). The difference `ω s - ω t` of two times is a
datum of the same kind with Hölder constant `2 M` and small sup norm for `s` near `t`
(`IsVorticityHistory.sub_data`), so the homogeneous Kato bound
`norm_fderivWithin_halfPlaneVelocity_le_katoModulus`, whose modulus tends to zero with the sup
bound, makes the derivative continuous in time uniformly on `H̄`
(`IsVorticityHistory.exists_norm_fderivWithin_sub_le`). Joint continuity of the reflected fields and
of their derivatives (`PDE.Analysis.continuousOn_fderiv_weightedReflectionFun`) then gives
`IsVorticityHistory.isC1FieldOn`. For a `C¹` history we treat the second derivatives in the same
way, with the bound `secondDerivBound` of the velocity of a `C^{1,α}` vorticity and the homogeneous
top-order Kato bound for `ω s - ω t`
(`IsC1VorticityHistory.exists_norm_fderivWithin_fderivWithin_sub_le`), which gives
`IsC1VorticityHistory.isC2FieldOn`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal
open SobolevSpace SobolevSpace.GraphSpace.HigherOrderReflection

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Maps into the plane from their components -/

/-- The map sending a functional `L` to the linear map `h ↦ L h • e_k` into the plane. -/
def toComponentL (k : Fin 2) : (ℝ^2 →L[ℝ] ℝ) →L[ℝ] (ℝ^2 →L[ℝ] ℝ^2) :=
  (ContinuousLinearMap.smulRightL ℝ (ℝ^2) (ℝ^2)).flip (EuclideanSpace.single k 1)

/-- `toComponentL k L h = L h • e_k`. -/
@[simp]
theorem toComponentL_apply_apply (k : Fin 2) (L : ℝ^2 →L[ℝ] ℝ) (h : ℝ^2) :
    toComponentL k L h = L h • EuclideanSpace.single k 1 := by
  simp [toComponentL]

/-- The embedding `toComponentL k` preserves norms. -/
theorem norm_toComponentL_apply (k : Fin 2) (L : ℝ^2 →L[ℝ] ℝ) : ‖toComponentL k L‖ = ‖L‖ := by
  simp [toComponentL, ContinuousLinearMap.norm_smulRight_apply]

/-- The embedding `toComponentL k` has norm at most one. -/
theorem norm_toComponentL_le (k : Fin 2) : ‖toComponentL k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    rw [norm_toComponentL_apply, one_mul]

/-- The component `k` of `∑ⱼ toComponentL j (L j)` is `L k`. -/
theorem proj_comp_sum_toComponentL (L : Fin 2 → ℝ^2 →L[ℝ] ℝ) (k : Fin 2) :
    PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) k ∘L ∑ j, toComponentL j (L j) = L k := by
  ext1 h
  fin_cases k <;> simp [Fin.sum_univ_two]

/-- A linear map into the plane is the sum of the embeddings of its components. -/
theorem sum_toComponentL_proj_comp (T : ℝ^2 →L[ℝ] ℝ^2) :
    ∑ j, toComponentL j (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) j ∘L T) = T := by
  ext1 h
  ext k
  fin_cases k <;> simp [Fin.sum_univ_two]

/-- A linear map into the plane is bounded by the sum of the norms of its components. -/
theorem norm_sum_toComponentL_le (L : Fin 2 → ℝ^2 →L[ℝ] ℝ) :
    ‖∑ j, toComponentL j (L j)‖ ≤ ∑ j, ‖L j‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ (norm_toComponentL_apply j (L j)).le)

/-- A map into the plane whose components have derivatives `L k` has derivative
`∑ₖ toComponentL k (L k)`. -/
theorem hasFDerivAt_toLp_of_components {F : Fin 2 → ℝ^2 → ℝ} {L : Fin 2 → ℝ^2 →L[ℝ] ℝ}
    {x : ℝ^2} (hF : ∀ k, HasFDerivAt (F k) (L k) x) :
    HasFDerivAt (fun y ↦ (WithLp.toLp 2 fun k ↦ F k y : ℝ^2)) (∑ j, toComponentL j (L j)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro k
  rw [proj_comp_sum_toComponentL]
  exact (hF k).hasFDerivWithinAt

/-- The derivative within `H̄` of a component of a field into the plane. -/
theorem fderivWithin_apply_eq {u : ℝ^2 → ℝ^2} {x : ℝ^2} (hx : 0 ≤ x 1)
    (hu : DifferentiableWithinAt ℝ u H̄ x) (k : Fin 2) :
    fderivWithin ℝ (fun y ↦ u y k) H̄ x =
      PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) k ∘L fderivWithin ℝ u H̄ x :=
  (((hasFDerivWithinAt_piLp (𝕜 := ℝ) (p := 2) (f := u)).mp hu.hasFDerivWithinAt) k).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

/-- The derivative within `H̄` of a component is bounded by the derivative of the field. -/
theorem norm_fderivWithin_apply_le {u : ℝ^2 → ℝ^2} {x : ℝ^2} (hx : 0 ≤ x 1)
    (hu : DifferentiableWithinAt ℝ u H̄ x) (k : Fin 2) :
    ‖fderivWithin ℝ (fun y ↦ u y k) H̄ x‖ ≤ ‖fderivWithin ℝ u H̄ x‖ := by
  rw [fderivWithin_apply_eq hx hu k]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) (PiLp.norm_proj_le k)

/-- The map `M ↦ proj k ∘ M` on linear maps into the plane. -/
def projCompL (k : Fin 2) : (ℝ^2 →L[ℝ] ℝ^2) →L[ℝ] (ℝ^2 →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2) ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) k)

/-- `projCompL k M = proj k ∘L M`. -/
@[simp]
theorem projCompL_apply (k : Fin 2) (M : ℝ^2 →L[ℝ] ℝ^2) :
    projCompL k M = PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) k ∘L M := rfl

/-- The map `projCompL k` has norm at most one. -/
theorem norm_projCompL_le (k : Fin 2) : ‖projCompL k‖ ≤ 1 :=
  (PDE.Analysis.ODE.norm_compL_apply_le _).trans (PiLp.norm_proj_le k)

/-- The second derivative within `H̄` of a component of a field into the plane. -/
theorem fderivWithin_fderivWithin_apply_eq {u : ℝ^2 → ℝ^2} {x : ℝ^2} (hx : 0 ≤ x 1)
    (hu : ContDiffOn ℝ 2 u H̄) (k : Fin 2) :
    fderivWithin ℝ (fderivWithin ℝ (fun y ↦ u y k) H̄) H̄ x =
      (projCompL k).comp (fderivWithin ℝ (fderivWithin ℝ u H̄) H̄ x) := by
  have hD : ContDiffOn ℝ 1 (fderivWithin ℝ u H̄) H̄ :=
    hu.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have heq : EqOn (fderivWithin ℝ (fun y ↦ u y k) H̄) (fun y ↦ projCompL k (fderivWithin ℝ u H̄ y))
      H̄ := fun y hy ↦ fderivWithin_apply_eq hy
        ((hu.differentiableOn (by norm_num)) y hy) k
  rw [fderivWithin_congr heq (heq hx)]
  exact ((projCompL k).hasFDerivAt.comp_hasFDerivWithinAt x
    ((hD.differentiableOn one_ne_zero x hx).hasFDerivWithinAt)).fderivWithin
      (uniqueDiffOn_closedUpper x hx)

/-- Second derivatives within `H̄` of components of two fields differ by at most the difference
of the second derivatives of the fields. -/
theorem norm_fderivWithin_fderivWithin_apply_sub_le {u w : ℝ^2 → ℝ^2} {x : ℝ^2}
    (hx : 0 ≤ x 1) (hu : ContDiffOn ℝ 2 u H̄) (hw : ContDiffOn ℝ 2 w H̄) (k : Fin 2) :
    ‖fderivWithin ℝ (fderivWithin ℝ (fun y ↦ u y k) H̄) H̄ x -
        fderivWithin ℝ (fderivWithin ℝ (fun y ↦ w y k) H̄) H̄ x‖ ≤
      ‖fderivWithin ℝ (fderivWithin ℝ u H̄) H̄ x - fderivWithin ℝ (fderivWithin ℝ w H̄) H̄ x‖ := by
  rw [fderivWithin_fderivWithin_apply_eq hx hu, fderivWithin_fderivWithin_apply_eq hx hw,
    ← ContinuousLinearMap.comp_sub]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) (norm_projCompL_le k)

/-- Derivatives within `H̄` of components of two fields differ by at most the difference of the
derivatives of the fields. -/
theorem norm_fderivWithin_apply_sub_le {u w : ℝ^2 → ℝ^2} {x : ℝ^2} (hx : 0 ≤ x 1)
    (hu : DifferentiableWithinAt ℝ u H̄ x) (hw : DifferentiableWithinAt ℝ w H̄ x) (k : Fin 2) :
    ‖fderivWithin ℝ (fun y ↦ u y k) H̄ x - fderivWithin ℝ (fun y ↦ w y k) H̄ x‖ ≤
      ‖fderivWithin ℝ u H̄ x - fderivWithin ℝ w H̄ x‖ := by
  rw [fderivWithin_apply_eq hx hu, fderivWithin_apply_eq hx hw, ← ContinuousLinearMap.comp_sub]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) (PiLp.norm_proj_le k)

/-- The difference of two sums is bounded by the sum of the differences of the terms. -/
theorem norm_add_sub_add_le {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b - (c + d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [add_sub_add_comm]
  exact norm_add_le _ _

/-! ### The extended velocity -/

variable {f g : ℝ^2 → ℝ} {R : ℝ}

/-- The extension to the plane of the half-plane velocity of `f`: the weighted reflection of
order `K` of each component of `halfPlaneVelocity f` across the boundary line `x₁ = 0`. -/
def extendedVelocity (K : ℕ) (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 fun k ↦ weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k) x

/-- The `k`-th component of the extended velocity is the weighted reflection of order `K` of the
`k`-th velocity component. -/
@[simp]
theorem extendedVelocity_apply (K : ℕ) (f : ℝ^2 → ℝ) (x : ℝ^2) (k : Fin 2) :
    extendedVelocity K f x k = weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k) x :=
  rfl

/-- On the closed half-plane the extended velocity is the velocity. -/
theorem extendedVelocity_of_nonneg (K : ℕ) (f : ℝ^2 → ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    extendedVelocity K f x = halfPlaneVelocity f x := by
  ext k
  simp [weightedReflectionFun_eq_of_nonneg _ _ _ _ hx]

/-- The normal component of the extended velocity vanishes on the boundary line. -/
theorem extendedVelocity_normal_eq_zero (K : ℕ) (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : x 1 = 0) :
    extendedVelocity K f x 1 = 0 := by
  rw [extendedVelocity_of_nonneg K f hx.symm.le]
  exact halfPlaneVelocity_normal_eq_zero hf hR hx

/-- The components of a velocity that is `C^K` within `H̄` are `C^K` within `H̄`. -/
theorem contDiffOn_halfPlaneVelocity_apply {K : ℕ}
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) (k : Fin 2) :
    ContDiffOn ℝ K (fun y ↦ halfPlaneVelocity f y k) H̄ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) k).contDiff.comp_contDiffOn hu

variable {K : ℕ}

/-- The extended velocity is `C^K` when the velocity is `C^K` within the closed half-plane. -/
theorem contDiff_extendedVelocity (hK : 1 ≤ K) (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) :
    ContDiff ℝ K (extendedVelocity K f) :=
  contDiff_piLp' (p := 2) fun k ↦
    PDE.Analysis.contDiff_weightedReflectionFun 1 hK (contDiffOn_halfPlaneVelocity_apply hu k)

/-- The derivative of the extended velocity from the derivatives of its components. -/
theorem hasFDerivAt_extendedVelocity (hK : 1 ≤ K) (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄)
    (x : ℝ^2) :
    HasFDerivAt (extendedVelocity K f)
      (∑ j, toComponentL j
        (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y j)) x)) x :=
  hasFDerivAt_toLp_of_components fun k ↦
    (((PDE.Analysis.contDiff_weightedReflectionFun 1 hK
      (contDiffOn_halfPlaneVelocity_apply hu k)).differentiable
        (by exact_mod_cast (show K ≠ 0 by omega))) x).hasFDerivAt

/-- The derivative of the extended velocity as the sum of the embedded component derivatives. -/
theorem fderiv_extendedVelocity (hK : 1 ≤ K) (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄)
    (x : ℝ^2) :
    fderiv ℝ (extendedVelocity K f) x = ∑ j, toComponentL j
      (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y j)) x) :=
  (hasFDerivAt_extendedVelocity hK hu x).fderiv

/-- On the closed half-plane the derivative of the extended velocity is the derivative of the
velocity within the closed half-plane. -/
theorem fderiv_extendedVelocity_of_nonneg (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (extendedVelocity K f) x = fderivWithin ℝ (halfPlaneVelocity f) H̄ x := by
  have hd : DifferentiableWithinAt ℝ (halfPlaneVelocity f) H̄ x :=
    hu.differentiableOn (by exact_mod_cast (show K ≠ 0 by omega)) x hx
  rw [fderiv_extendedVelocity hK hu]
  conv_rhs => rw [← sum_toComponentL_proj_comp (fderivWithin ℝ (halfPlaneVelocity f) H̄ x)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 hK
    (contDiffOn_halfPlaneVelocity_apply hu j) hx, fderivWithin_apply_eq hx hd j]

/-- The extended velocities of two vorticities differ by at most `2 c₀` times the bound of the
difference of their velocities on the closed half-plane. -/
theorem norm_extendedVelocity_sub_le (K : ℕ) {Q : ℝ}
    (hQ : ∀ y : ℝ^2, 0 ≤ y 1 → ‖halfPlaneVelocity f y - halfPlaneVelocity g y‖ ≤ Q)
    (x : ℝ^2) :
    ‖extendedVelocity K f x - extendedVelocity K g x‖ ≤
      2 * PDE.Analysis.reflectionBound K 0 * Q := by
  refine (EuclideanSpace.norm_le_abs_add_abs_fin_two _).trans ?_
  have hk (k : Fin 2) : |(extendedVelocity K f x - extendedVelocity K g x) k| ≤
      PDE.Analysis.reflectionBound K 0 * Q := by
    rw [PiLp.sub_apply, extendedVelocity_apply, extendedVelocity_apply]
    refine PDE.Analysis.abs_weightedReflectionFun_sub_le 1 K (fun y hy ↦ ?_) x
    refine le_trans ?_ (hQ y hy)
    rw [← PiLp.sub_apply, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le _ k
  linarith [hk 0, hk 1]

/-- The derivatives of the extended velocities of two vorticities differ by at most `2 c₁` times
the bound of the difference of the derivatives of their velocities within the closed
half-plane. -/
theorem norm_fderiv_extendedVelocity_sub_le (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) (hw : ContDiffOn ℝ K (halfPlaneVelocity g) H̄)
    {Q : ℝ} (hQ : ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ y - fderivWithin ℝ (halfPlaneVelocity g) H̄ y‖ ≤ Q)
    (x : ℝ^2) :
    ‖fderiv ℝ (extendedVelocity K f) x - fderiv ℝ (extendedVelocity K g) x‖ ≤
      2 * PDE.Analysis.reflectionBound K 1 * Q := by
  have hK0 : (K : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  rw [fderiv_extendedVelocity hK hu, fderiv_extendedVelocity hK hw, ← Finset.sum_sub_distrib]
  simp_rw [← map_sub]
  refine (norm_sum_toComponentL_le _).trans ?_
  have hk (k : Fin 2) :
      ‖fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k)) x -
        fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity g y k)) x‖ ≤
      PDE.Analysis.reflectionBound K 1 * Q :=
    PDE.Analysis.norm_fderiv_weightedReflectionFun_sub_le 1 hK
      (contDiffOn_halfPlaneVelocity_apply hu k) (contDiffOn_halfPlaneVelocity_apply hw k)
      (fun y hy ↦ (norm_fderivWithin_apply_sub_le hy (hu.differentiableOn hK0 y hy)
        (hw.differentiableOn hK0 y hy) k).trans (hQ y hy)) x
  rw [Fin.sum_univ_two]
  linarith [hk 0, hk 1]

/-- The derivative of the extended velocity is bounded by `2 c₁` times the bound of the
derivative of the velocity within the closed half-plane. -/
theorem norm_fderiv_extendedVelocity_le (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) {Q : ℝ}
    (hQ : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ y‖ ≤ Q) (x : ℝ^2) :
    ‖fderiv ℝ (extendedVelocity K f) x‖ ≤ 2 * PDE.Analysis.reflectionBound K 1 * Q := by
  have hK0 : (K : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  rw [fderiv_extendedVelocity hK hu]
  refine (norm_sum_toComponentL_le _).trans ?_
  have hk (k : Fin 2) :
      ‖fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k)) x‖ ≤
      PDE.Analysis.reflectionBound K 1 * Q :=
    PDE.Analysis.norm_fderiv_weightedReflectionFun_le 1 hK
      (contDiffOn_halfPlaneVelocity_apply hu k)
      (fun y hy ↦ (norm_fderivWithin_apply_le hy (hu.differentiableOn hK0 y hy) k).trans
        (hQ y hy)) x
  rw [Fin.sum_univ_two]
  linarith [hk 0, hk 1]

/-- The second derivative of the extended velocity from those of its components. -/
theorem fderiv_fderiv_extendedVelocity (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) (x : ℝ^2) :
    fderiv ℝ (fderiv ℝ (extendedVelocity K f)) x = ∑ j, (toComponentL j).comp
      (fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y j))) x) := by
  have hfun : fderiv ℝ (extendedVelocity K f) = fun y ↦ ∑ j, toComponentL j
      (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y j)) y) :=
    funext (fderiv_extendedVelocity (by omega) hu)
  rw [hfun]
  refine HasFDerivAt.fderiv (HasFDerivAt.fun_sum fun j _ ↦ ?_)
  have hE := (PDE.Analysis.contDiff_weightedReflectionFun 1 (by omega)
    (contDiffOn_halfPlaneVelocity_apply hu j)).fderiv_right (m := 1) (by exact_mod_cast hK)
  exact (toComponentL j).hasFDerivAt.comp x
    ((hE.differentiable one_ne_zero) x).hasFDerivAt

/-- On the closed half-plane the second derivative of the extended velocity is the second
derivative of the velocity within the closed half-plane. -/
theorem fderiv_fderiv_extendedVelocity_of_nonneg (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (fderiv ℝ (extendedVelocity K f)) x =
      fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x := by
  have hu2 : ContDiffOn ℝ 2 (halfPlaneVelocity f) H̄ := hu.of_le (by exact_mod_cast hK)
  rw [fderiv_fderiv_extendedVelocity hK hu]
  ext h : 1
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  conv_rhs => rw [← sum_toComponentL_proj_comp
    (fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x h)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.Analysis.fderiv_fderiv_weightedReflectionFun_of_nonneg 1 hK
    (contDiffOn_halfPlaneVelocity_apply hu j) hx, fderivWithin_fderivWithin_apply_eq hx hu2 j]
  rfl

/-- The second derivatives of the extended velocities of two vorticities differ by at most
`2 c₂` times the bound of the difference of the second derivatives of their velocities within the
closed half-plane. -/
theorem norm_fderiv_fderiv_extendedVelocity_sub_le (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) (hw : ContDiffOn ℝ K (halfPlaneVelocity g) H̄)
    {Q : ℝ} (hQ : ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity g) H̄) H̄ y‖ ≤ Q)
    (x : ℝ^2) :
    ‖fderiv ℝ (fderiv ℝ (extendedVelocity K f)) x -
        fderiv ℝ (fderiv ℝ (extendedVelocity K g)) x‖ ≤
      2 * PDE.Analysis.reflectionBound K 2 * Q := by
  have hu2 : ContDiffOn ℝ 2 (halfPlaneVelocity f) H̄ := hu.of_le (by exact_mod_cast hK)
  have hw2 : ContDiffOn ℝ 2 (halfPlaneVelocity g) H̄ := hw.of_le (by exact_mod_cast hK)
  rw [fderiv_fderiv_extendedVelocity hK hu, fderiv_fderiv_extendedVelocity hK hw,
    Fin.sum_univ_two, Fin.sum_univ_two]
  refine (norm_add_sub_add_le (E := ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) _ _ _ _).trans ?_
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_sub]
  have hk (k : Fin 2) :
      ‖(toComponentL k).comp
          (fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k))) x -
            fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity g y k))) x)‖ ≤
        PDE.Analysis.reflectionBound K 2 * Q := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _)
      (norm_toComponentL_le k)).trans ?_
    exact PDE.Analysis.norm_fderiv_fderiv_weightedReflectionFun_sub_le 1 hK
      (contDiffOn_halfPlaneVelocity_apply hu k) (contDiffOn_halfPlaneVelocity_apply hw k)
      (fun y hy ↦ (norm_fderivWithin_fderivWithin_apply_sub_le hy hu2 hw2 k).trans (hQ y hy)) x
  linarith [hk 0, hk 1]

/-- The second derivative of the extended velocity is bounded by `2 c₂` times the bound of the
second derivative of the velocity within the closed half-plane. -/
theorem norm_fderiv_fderiv_extendedVelocity_le (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) {Q : ℝ} (hQ : ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ y‖ ≤ Q) (x : ℝ^2) :
    ‖fderiv ℝ (fderiv ℝ (extendedVelocity K f)) x‖ ≤
      2 * PDE.Analysis.reflectionBound K 2 * Q := by
  have hu2 : ContDiffOn ℝ 2 (halfPlaneVelocity f) H̄ := hu.of_le (by exact_mod_cast hK)
  rw [fderiv_fderiv_extendedVelocity hK hu, Fin.sum_univ_two]
  refine (norm_add_le (E := ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) _ _).trans ?_
  have hk (k : Fin 2) :
      ‖(toComponentL k).comp
          (fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y k))) x)‖ ≤
        PDE.Analysis.reflectionBound K 2 * Q := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _)
      (norm_toComponentL_le k)).trans ?_
    refine PDE.Analysis.norm_fderiv_fderiv_weightedReflectionFun_le 1 hK
      (contDiffOn_halfPlaneVelocity_apply hu k) (fun y hy ↦ ?_) x
    rw [fderivWithin_fderivWithin_apply_eq hy hu2 k]
    refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_).trans (hQ y hy)
    exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) (norm_projCompL_le k)
  linarith [hk 0, hk 1]

/-! ### Bounds of the velocity for data with a support disc -/

/-- The Kato bound `4((50/α)(1 + B log(2 + M)) + 8B + 10πR²B)` of the derivative of the velocity
of data bounded by `B`, `α`-Hölder with constant `M` and supported in the disc of radius `R`. -/
def katoBound (α R B M : ℝ) : ℝ :=
  4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * (Real.pi * R ^ 2 * B))

/-- The modulus `4((50/α) φ(η) + 8η + 10πR²η)`, with `φ = osgoodModulus (2 + M)`, of the
homogeneous Kato bound for data bounded by `η ≤ 1`. It tends to zero with `η`. -/
def katoModulus (α R M η : ℝ) : ℝ :=
  4 * (50 / α * PDE.Analysis.osgoodModulus (2 + M) η + 8 * η + 10 * (Real.pi * R ^ 2 * η))

/-- The Kato modulus is continuous in `η`. -/
theorem continuous_katoModulus (α R : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    Continuous (katoModulus α R M) := by
  have h := PDE.Analysis.continuous_osgoodModulus (A := 2 + M) (by linarith)
  unfold katoModulus
  fun_prop

/-- The Kato modulus vanishes at `η = 0`. -/
@[simp]
theorem katoModulus_zero (α R M : ℝ) : katoModulus α R M 0 = 0 := by
  simp [katoModulus, PDE.Analysis.osgoodModulus_zero]

/-- A function continuous at `0` and vanishing there is at most `ε` at some `η ∈ (0, 1]`. -/
theorem exists_pos_le_one_of_continuousAt {G : ℝ → ℝ} (hG : ContinuousAt G 0) (hG0 : G 0 = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ η, 0 < η ∧ η ≤ 1 ∧ G η ≤ ε := by
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hG ε hε
  refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, ?_⟩
  have hd : dist (min (δ / 2) 1) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have := hδG hd
  rw [hG0, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

variable {α M B : ℝ}

section Support

variable (hf : ContinuousOn f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
  (hα : 0 < α) (hα1 : α < 1)
  (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
include hf hR hR0 hα hα1 hM

/-- The derivative of the velocity within the closed half-plane is bounded by
`katoBound α R B M` for data bounded by `B`. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_katoBound (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤ katoBound α R B M := by
  refine (norm_fderivWithin_halfPlaneVelocity_le_kato hf hR hα hα1 hM hB hx).trans ?_
  have hL := setIntegral_upper_le hR0 hf.abs (fun y hy hyR ↦ by simp [hR y hy hyR])
    (fun y hy ↦ hB y hy) fun y ↦ abs_nonneg _
  unfold katoBound
  gcongr

/-- The derivative of the velocity within the closed half-plane is bounded by
`katoModulus α R M η` for data bounded by `η ∈ (0, 1]`; this is the homogeneous Kato bound, which
applies to differences. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_katoModulus {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hM0 : 0 ≤ M) (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ η) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤ katoModulus α R M η := by
  refine (norm_fderivWithin_halfPlaneVelocity_le_kato_homogeneous hf hR hα hα1 hM hB hη
    hx).trans ?_
  have hL := setIntegral_upper_le hR0 hf.abs (fun y hy hyR ↦ by simp [hR y hy hyR])
    (fun y hy ↦ hB y hy) fun y ↦ abs_nonneg _
  have hlog := PDE.Analysis.mul_one_add_log_le_osgoodModulus hη.le hη1 hM0
  rw [show (2 : ℝ) * 1 + M = 2 + M by ring] at hlog
  have h50 : 50 * η / α * (1 + Real.log (2 + M / η)) =
      50 / α * (η * (1 + Real.log (2 + M / η))) := by ring
  unfold katoModulus
  rw [h50]
  gcongr

end Support

/-- At two points of the closed half-plane, the first iterated derivatives within it differ by
as much as the derivatives within it. -/
theorem norm_iteratedFDerivWithin_one_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : ℝ^2 → F) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖iteratedFDerivWithin ℝ 1 h H̄ x - iteratedFDerivWithin ℝ 1 h H̄ x'‖ =
      ‖fderivWithin ℝ h H̄ x - fderivWithin ℝ h H̄ x'‖ := by
  rw [norm_iteratedFDerivWithin_succ_sub h hx hx' 0,
    PDE.Analysis.norm_iteratedFDerivWithin_zero_sub]

/-- The norm of the second iterated derivative within the closed half-plane is the norm of the
derivative of the derivative within it. -/
theorem norm_iteratedFDerivWithin_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ^2 → F) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ 2 h H̄ x‖ = ‖fderivWithin ℝ (fderivWithin ℝ h H̄) H̄ x‖ := by
  rw [← norm_iteratedFDerivWithin_fderivWithin uniqueDiffOn_closedUpper hx,
    norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx)]

/-! ### Vorticity histories -/

/-- A vorticity history on the times `[a, b]` with uniform bounds: at every time it is continuous
on the closed half-plane `H̄`, vanishes on `H̄` outside the disc of radius `R`, is bounded by `B`
and `α`-Hölder with constant `M` on `H̄`, and it is continuous in time uniformly on `H̄`. -/
structure IsVorticityHistory (ω : ℝ → ℝ^2 → ℝ) (a b α R B M : ℝ) : Prop where
  /-- Continuity on the closed half-plane. -/
  continuousOn : ∀ t ∈ Icc a b, ContinuousOn (ω t) H̄
  /-- A common support disc. -/
  eq_zero : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → ω t y = 0
  /-- A common bound. -/
  abs_le : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → |ω t y| ≤ B
  /-- A common Hölder bound. -/
  holder : ∀ t ∈ Icc a b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |ω t y - ω t z| ≤ M * ‖y - z‖ ^ α
  /-- Continuity in time uniformly on the closed half-plane. -/
  uniform : ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
    ∀ y : ℝ^2, 0 ≤ y 1 → |ω s y - ω t y| ≤ ε

namespace IsVorticityHistory

variable {ω : ℝ → ℝ^2 → ℝ} {a b R : ℝ}

/-- A history vanishes on `H̄` outside the disc of radius `max R 0`. -/
theorem eq_zero_max (hω : IsVorticityHistory ω a b α R B M) {t : ℝ} (ht : t ∈ Icc a b)
    (y : ℝ^2) (hy : 0 ≤ y 1) (hyR : max R 0 < ‖y‖) : ω t y = 0 :=
  hω.eq_zero t ht y hy ((le_max_left R 0).trans_lt hyR)

/-- The Hölder constant of a history on a nonempty time interval is nonnegative. -/
theorem holder_nonneg (hω : IsVorticityHistory ω a b α R B M) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ M := by
  have h := hω.holder t ht (EuclideanSpace.single 0 1) 0 (by simp) (by simp)
  have hn : ‖(EuclideanSpace.single 0 1 : ℝ^2)‖ = 1 := by simp
  rw [sub_zero, hn, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

/-- At every time the velocity is `C¹` within the closed half-plane. For `α ≥ 1` the history is
also `1/2`-Hölder, with constant `M + 2B`. -/
theorem contDiffOn_halfPlaneVelocity (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ 1 (halfPlaneVelocity (ω t)) H̄ := by
  rcases lt_or_ge α 1 with hα1 | hα1
  · have h := IncompressibleFlow.contDiffOn_succ_halfPlaneVelocity hα hα1 (k := 0)
      (by simpa using hω.continuousOn t ht) (hω.eq_zero t ht) (M := M) fun y z hy hz ↦ by
        rw [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs]
        exact hω.holder t ht y z hy hz
    simpa using h
  have hM := hω.holder_nonneg ht
  have hB : 0 ≤ B := (abs_nonneg _).trans (hω.abs_le t ht 0 (by simp))
  have h := IncompressibleFlow.contDiffOn_succ_halfPlaneVelocity (α := 1 / 2) (by norm_num)
    (by norm_num) (k := 0) (by simpa using hω.continuousOn t ht) (hω.eq_zero t ht)
    (M := M + 2 * B) fun y z hy hz ↦ by
      rw [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs]
      have hd := norm_nonneg (y - z)
      rcases le_or_gt ‖y - z‖ 1 with h1 | h1
      · have hpow : ‖y - z‖ ^ α ≤ ‖y - z‖ ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge' hd h1 (by norm_num) (by linarith)
        calc |ω t y - ω t z| ≤ M * ‖y - z‖ ^ α := hω.holder t ht y z hy hz
          _ ≤ M * ‖y - z‖ ^ (1 / 2 : ℝ) := by gcongr
          _ ≤ (M + 2 * B) * ‖y - z‖ ^ (1 / 2 : ℝ) := by
            gcongr
            linarith
      · have hone : 1 ≤ ‖y - z‖ ^ (1 / 2 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
        have hy' := _root_.abs_le.mp (hω.abs_le t ht y hy)
        have hz' := _root_.abs_le.mp (hω.abs_le t ht z hz)
        calc |ω t y - ω t z| ≤ M + 2 * B :=
              _root_.abs_le.mpr ⟨by linarith [hy'.1, hz'.2], by linarith [hy'.2, hz'.1]⟩
          _ ≤ (M + 2 * B) * ‖y - z‖ ^ (1 / 2 : ℝ) := le_mul_of_one_le_right (by linarith) hone
  simpa using h

/-- At every time the derivative of the velocity within the closed half-plane is bounded by the
Kato bound. -/
theorem norm_fderivWithin_le (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α) (hα1 : α < 1)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄ x‖ ≤ katoBound α (max R 0) B M :=
  norm_fderivWithin_halfPlaneVelocity_le_katoBound (hω.continuousOn t ht) (hω.eq_zero_max ht)
    (le_max_right R 0) hα hα1 (hω.holder t ht) (hω.abs_le t ht) hx

/-- The difference of two times of a history is a datum of the same kind, bounded by `η` when
the times are close, with Hölder constant `2M`. -/
theorem sub_data (hω : IsVorticityHistory ω a b α R B M) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    ContinuousOn (ω s - ω t) H̄ ∧
      (∀ y : ℝ^2, 0 ≤ y 1 → max R 0 < ‖y‖ → (ω s - ω t) y = 0) ∧
      ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        |(ω s - ω t) y - (ω s - ω t) z| ≤ 2 * M * ‖y - z‖ ^ α := by
  refine ⟨(hω.continuousOn s hs).sub (hω.continuousOn t ht), fun y hy hyR ↦ ?_,
    fun y z hy hz ↦ ?_⟩
  · simp [hω.eq_zero_max hs y hy hyR, hω.eq_zero_max ht y hy hyR]
  · have h1 := hω.holder s hs y z hy hz
    have h2 := hω.holder t ht y z hy hz
    simp only [Pi.sub_apply]
    calc |ω s y - ω t y - (ω s z - ω t z)| = |(ω s y - ω s z) - (ω t y - ω t z)| := by ring_nf
      _ ≤ |ω s y - ω s z| + |ω t y - ω t z| := abs_sub _ _
      _ ≤ 2 * M * ‖y - z‖ ^ α := by linarith

/-- **Continuity in time of the velocity**, uniformly on the plane. -/
theorem exists_norm_halfPlaneVelocity_sub_le (hω : IsVorticityHistory ω a b α R B M) {t : ℝ}
    (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2,
      ‖halfPlaneVelocity (ω s) y - halfPlaneVelocity (ω t) y‖ ≤ ε := by
  set R₀ := max R 0
  have hR₀ : 0 ≤ R₀ := le_max_right R 0
  have hpos : 0 < 1 + R₀ ^ 2 := by positivity
  obtain ⟨δ, hδ, hδt⟩ := hω.uniform t ht (ε / (1 + R₀ ^ 2)) (by positivity)
  refine ⟨δ, hδ, fun s hs hst y ↦ ?_⟩
  obtain ⟨hgc, hgR, -⟩ := hω.sub_data hs ht
  have hsub := halfPlaneVelocity_sub_of_continuousOn (hω.continuousOn s hs) (hω.eq_zero s hs)
    (hω.continuousOn t ht) (hω.eq_zero t ht)
  have hgB : ∀ y ∈ HalfSpace.upper 2, |(ω s - ω t) y| ≤ ε / (1 + R₀ ^ 2) :=
    fun y hy ↦ hδt s hs hst y (le_of_lt hy)
  have hL := setIntegral_upper_le hR₀ hgc.abs (fun y hy hyR ↦ by simp [hgR y hy hyR])
    (fun y hy ↦ hδt s hs hst y hy) fun y ↦ abs_nonneg _
  have hb := norm_halfPlaneVelocity_le_of_continuousOn hgc hgR hgB y
  rw [hsub, Pi.sub_apply] at hb
  refine hb.trans ?_
  have hpi := Real.pi_pos
  calc ε / (1 + R₀ ^ 2) + (∫ y in HalfSpace.upper 2, |(ω s - ω t) y|) / Real.pi
      ≤ ε / (1 + R₀ ^ 2) + Real.pi * R₀ ^ 2 * (ε / (1 + R₀ ^ 2)) / Real.pi := by gcongr
    _ = ε := by field_simp

/-- **Continuity in time of the derivative of the velocity**, uniformly on the closed
half-plane (the homogeneous Kato bound for `ω s - ω t`). -/
theorem exists_norm_fderivWithin_sub_le (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (halfPlaneVelocity (ω s)) H̄ y -
        fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄ y‖ ≤ ε := by
  set R₀ := max R 0
  have hR₀ : 0 ≤ R₀ := le_max_right R 0
  have hM0 := hω.holder_nonneg ht
  obtain ⟨η, hη, hη1, hηε⟩ := exists_pos_le_one_of_continuousAt
    ((continuous_katoModulus α R₀ (by positivity : (0 : ℝ) ≤ 2 * M)).continuousAt)
    (katoModulus_zero α R₀ (2 * M)) hε
  obtain ⟨δ, hδ, hδt⟩ := hω.uniform t ht η hη
  refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
  obtain ⟨hgc, hgR, hgM⟩ := hω.sub_data hs ht
  have hsub := halfPlaneVelocity_sub_of_continuousOn (hω.continuousOn s hs) (hω.eq_zero s hs)
    (hω.continuousOn t ht) (hω.eq_zero t ht)
  have hds := (hω.contDiffOn_halfPlaneVelocity hα hs).differentiableOn one_ne_zero y hy
  have hdt := (hω.contDiffOn_halfPlaneVelocity hα ht).differentiableOn one_ne_zero y hy
  rw [← fderivWithin_sub (uniqueDiffOn_closedUpper y hy) hds hdt, ← hsub]
  exact (norm_fderivWithin_halfPlaneVelocity_le_katoModulus hgc hgR hR₀ hα hα1 hgM hη hη1
    (by positivity) (fun y hy ↦ hδt s hs hst y hy) hy).trans hηε

/-- `contDiffOn_halfPlaneVelocity` with the order written as a natural number. -/
theorem contDiffOn_halfPlaneVelocity_one (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (halfPlaneVelocity (ω t)) H̄ := by
  exact_mod_cast hω.contDiffOn_halfPlaneVelocity hα ht

/-- The extended velocities of order `K ≥ 1` of a vorticity history whose velocities are `C^K`
within the closed half-plane form a `C¹` field on `[a, b] × ℝ²`, with derivatives bounded by
`2 reflectionBound K 1 · katoBound α R₀ B M`, `R₀ = max R 0`. -/
theorem isC1FieldOn_extendedVelocity (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    (hα1 : α < 1) {K : ℕ} (hK : 1 ≤ K)
    (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (halfPlaneVelocity (ω t)) H̄) :
    PDE.Analysis.ODE.IsC1FieldOn (fun t ↦ extendedVelocity K (ω t))
      (fun t x ↦ fderiv ℝ (extendedVelocity K (ω t)) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound K 1 * katoBound α (max R 0) B M)) where
  continuousOn := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦
        weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity (ω p.1) y k) p.2)
        (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_weightedReflectionFun 1 hK
        (f := fun t y ↦ halfPlaneVelocity (ω t) y k)
        (fun t ht ↦ contDiffOn_halfPlaneVelocity_apply (hu t ht) k) (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_halfPlaneVelocity_sub_le ht hε
      refine ⟨δ, hδ, fun s hs hst y _ ↦ ?_⟩
      rw [← Real.norm_eq_abs, ← PiLp.sub_apply]
      exact (PiLp.norm_apply_le _ k).trans (h s hs hst y)
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hcomp)
  continuousOn_deriv := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦
        fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity (ω p.1) y k)) p.2)
        (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_fderiv_weightedReflectionFun 1 hK
        (f := fun t y ↦ halfPlaneVelocity (ω t) y k)
        (fun t ht ↦ contDiffOn_halfPlaneVelocity_apply (hu t ht) k) (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_fderivWithin_sub_le hα hα1 ht hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      refine (norm_fderivWithin_apply_sub_le hy
        ((hω.contDiffOn_halfPlaneVelocity hα hs).differentiableOn one_ne_zero y hy)
        ((hω.contDiffOn_halfPlaneVelocity hα ht).differentiableOn one_ne_zero y hy)
        k).trans (h s hs hst y hy)
    have heq : EqOn (Function.uncurry fun t x ↦ fderiv ℝ (extendedVelocity K (ω t)) x)
        (fun p : ℝ × ℝ^2 ↦ toComponentL 0
            (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity (ω p.1) y 0)) p.2) +
          toComponentL 1
            (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity (ω p.1) y 1)) p.2))
        (Icc a b ×ˢ univ) := fun p hp ↦ by
      change fderiv ℝ (extendedVelocity K (ω p.1)) p.2 = _
      rw [fderiv_extendedVelocity hK (hu p.1 hp.1), Fin.sum_univ_two]
    refine ContinuousOn.congr ?_ heq
    exact ((toComponentL 0).continuous.comp_continuousOn (hcomp 0)).add
      ((toComponentL 1).continuous.comp_continuousOn (hcomp 1))
  hasFDerivAt t ht x :=
    ((contDiff_extendedVelocity hK (hu t ht)).differentiable
      (by exact_mod_cast (show K ≠ 0 by omega)) x).hasFDerivAt
  norm_le t ht x :=
    (norm_fderiv_extendedVelocity_le hK (hu t ht)
      (fun _ hy ↦ hω.norm_fderivWithin_le hα hα1 ht hy) x).trans (Real.le_coe_toNNReal _)

/-- **The extended velocities of a vorticity history form a `C¹` field.** For `0 < α < 1` the
fields `extendedVelocity 1 (ω t)`, `t ∈ [a, b]`, and their derivatives are jointly continuous on
`[a, b] × ℝ²`, and the derivatives are bounded by `2 c₁ katoBound α R₀ B M`, `R₀ = max R 0`,
`c₁ = reflectionBound 1 1`. -/
theorem isC1FieldOn (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α) (hα1 : α < 1) :
    PDE.Analysis.ODE.IsC1FieldOn (fun t ↦ extendedVelocity 1 (ω t))
      (fun t x ↦ fderiv ℝ (extendedVelocity 1 (ω t)) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 1 1 * katoBound α (max R 0) B M)) :=
  hω.isC1FieldOn_extendedVelocity hα hα1 le_rfl fun _ ht ↦
    hω.contDiffOn_halfPlaneVelocity_one hα ht

end IsVorticityHistory

/-! ### `C¹` vorticity histories -/

/-- A `C¹` vorticity history on `[a, b]`: a vorticity history that is at every time `C¹` within
the closed half-plane `H̄`, with gradient within `H̄` bounded by `B₁` and `α`-Hölder with constant
`M₁` on `H̄`, and with gradient continuous in time uniformly on `H̄`. -/
structure IsC1VorticityHistory (ω : ℝ → ℝ^2 → ℝ) (a b α R B M B₁ M₁ : ℝ) : Prop
    extends IsVorticityHistory ω a b α R B M where
  /-- `C¹` regularity within the closed half-plane. -/
  contDiffOn : ∀ t ∈ Icc a b, ContDiffOn ℝ 1 (ω t) H̄
  /-- A common bound of the gradient. -/
  norm_fderivWithin_le : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ (ω t) H̄ y‖ ≤ B₁
  /-- A common Hölder bound of the gradient. -/
  holder_fderivWithin : ∀ t ∈ Icc a b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖fderivWithin ℝ (ω t) H̄ y - fderivWithin ℝ (ω t) H̄ z‖ ≤ M₁ * ‖y - z‖ ^ α
  /-- Continuity in time of the gradient, uniformly on the closed half-plane. -/
  uniform_fderivWithin : ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
    ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω t) H̄ y‖ ≤ ε

/-- The bound `(200/α + 40π(1 + R²) + 34) max(B, B₁, M₁)` of the second derivatives of the
velocity of a `C^{1,α}` vorticity (the `C^{k+1,α}` bound of the velocity with `k = 1`). -/
def secondDerivBound (α R B B₁ M₁ : ℝ) : ℝ :=
  (200 / α + 40 * Real.pi * (1 + R ^ 2) + 1 + 33) * max B (max B₁ M₁)

namespace IsC1VorticityHistory

variable {ω : ℝ → ℝ^2 → ℝ} {a b R B₁ M₁ : ℝ}

/-- The Hölder bound of the gradient in the form of the first iterated derivative. -/
theorem holder_iteratedFDerivWithin (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) {t : ℝ}
    (ht : t ∈ Icc a b) (y z : ℝ^2) (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDerivWithin ℝ 1 (ω t) H̄ y - iteratedFDerivWithin ℝ 1 (ω t) H̄ z‖ ≤
      M₁ * ‖y - z‖ ^ α := by
  rw [norm_iteratedFDerivWithin_one_sub _ hy hz]
  exact hω.holder_fderivWithin t ht y z hy hz

/-- At every time the velocity is `C²` within the closed half-plane. -/
theorem contDiffOn_halfPlaneVelocity_two (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁)
    (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (halfPlaneVelocity (ω t)) H̄ := by
  have h := IncompressibleFlow.contDiffOn_succ_halfPlaneVelocity hα hα1 (k := 1)
    (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero t ht)
    (hω.holder_iteratedFDerivWithin ht)
  exact_mod_cast h

/-- At every time the second derivatives of the velocity within the closed half-plane are
bounded by `secondDerivBound α R₀ B B₁ M₁`, `R₀ = max R 0`. -/
theorem norm_fderivWithin_fderivWithin_le (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁)
    (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ x‖ ≤
      secondDerivBound α (max R 0) B B₁ M₁ := by
  rw [← norm_iteratedFDerivWithin_two _ hx]
  have hN : ∀ j ≤ 1, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (ω t) H̄ y‖ ≤ max B (max B₁ M₁) := by
    intro j hj y hy
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (hω.abs_le t ht y hy).trans (le_max_left _ _)
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)]
      exact (hω.norm_fderivWithin_le t ht y hy).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  have hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 1 (ω t) H̄ y - iteratedFDerivWithin ℝ 1 (ω t) H̄ z‖ ≤
        max B (max B₁ M₁) * ‖y - z‖ ^ α := fun y z hy hz ↦
    (hω.holder_iteratedFDerivWithin ht y z hy hz).trans (by
      gcongr
      exact (le_max_right _ _).trans (le_max_right _ _))
  have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul (k := 1) hα hα1
    (le_max_right R 0) (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero_max ht) hN hM
    (j := 2) le_rfl hx
  unfold secondDerivBound
  exact_mod_cast h

/-- At every time the second derivatives of the velocity within the closed half-plane are
`α`-Hölder on it with constant `(844/(α(1-α)) + 1) M₁`. -/
theorem norm_fderivWithin_fderivWithin_sub_le (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁)
    (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ z‖ ≤
      (844 / (α * (1 - α)) + 1) * M₁ * ‖y - z‖ ^ α := by
  have h := IncompressibleFlow.norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 (k := 1)
    (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero t ht) (hω.holder_iteratedFDerivWithin ht)
    hy hz
  rw [norm_iteratedFDerivWithin_succ_sub _ hy hz 1, norm_iteratedFDerivWithin_one_sub _ hy hz]
    at h
  exact_mod_cast h

/-- The difference of two times of a `C¹` history is `C¹` within the closed half-plane, with
gradient the difference of the gradients and Hölder constant `2 M₁`. -/
theorem fderivWithin_sub_data (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ContDiffOn ℝ 1 (ω s - ω t) H̄ ∧
      (∀ y : ℝ^2, 0 ≤ y 1 → fderivWithin ℝ (ω s - ω t) H̄ y =
        fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω t) H̄ y) ∧
      ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ y - iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖ ≤
          2 * M₁ * ‖y - z‖ ^ α := by
  have hd (y : ℝ^2) (hy : 0 ≤ y 1) : fderivWithin ℝ (ω s - ω t) H̄ y =
      fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω t) H̄ y :=
    fderivWithin_sub (uniqueDiffOn_closedUpper y hy)
      ((hω.contDiffOn s hs).differentiableOn one_ne_zero y hy)
      ((hω.contDiffOn t ht).differentiableOn one_ne_zero y hy)
  refine ⟨(hω.contDiffOn s hs).sub (hω.contDiffOn t ht), hd, fun y z hy hz ↦ ?_⟩
  rw [norm_iteratedFDerivWithin_one_sub _ hy hz, hd y hy, hd z hz]
  have h1 := hω.holder_fderivWithin s hs y z hy hz
  have h2 := hω.holder_fderivWithin t ht y z hy hz
  calc ‖fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω t) H̄ y -
        (fderivWithin ℝ (ω s) H̄ z - fderivWithin ℝ (ω t) H̄ z)‖
      = ‖(fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω s) H̄ z) -
          (fderivWithin ℝ (ω t) H̄ y - fderivWithin ℝ (ω t) H̄ z)‖ := by
        congr 1; abel
    _ ≤ ‖fderivWithin ℝ (ω s) H̄ y - fderivWithin ℝ (ω s) H̄ z‖ +
          ‖fderivWithin ℝ (ω t) H̄ y - fderivWithin ℝ (ω t) H̄ z‖ := norm_sub_le _ _
    _ ≤ 2 * M₁ * ‖y - z‖ ^ α := by linarith

/-- **Continuity in time of the second derivatives of the velocity**, uniformly on the closed
half-plane (the homogeneous top-order Kato bound for `ω s - ω t`). -/
theorem exists_norm_fderivWithin_fderivWithin_sub_le
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α) (hα1 : α < 1) {t : ℝ}
    (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω s)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ y‖ ≤ ε := by
  set R₀ := max R 0
  have hR₀ : 0 ≤ R₀ := le_max_right R 0
  have hM₁ : 0 ≤ M₁ := by
    have h := hω.holder_fderivWithin t ht (EuclideanSpace.single 0 1) 0 (by simp) (by simp)
    have hn : ‖(EuclideanSpace.single 0 1 : ℝ^2)‖ = 1 := by simp
    rw [sub_zero, hn, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hcont : Continuous fun η ↦ katoModulus α R₀ (2 * M₁) η + η :=
    (continuous_katoModulus α R₀ (by positivity : (0 : ℝ) ≤ 2 * M₁)).add continuous_id
  obtain ⟨η, hη, hη1, hηε⟩ := exists_pos_le_one_of_continuousAt hcont.continuousAt
    (by simp) hε
  obtain ⟨δ, hδ, hδt⟩ := hω.uniform_fderivWithin t ht η hη
  refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
  obtain ⟨hgc, hgd, hgM⟩ := hω.fderivWithin_sub_data hs ht
  have hgR : ∀ z : ℝ^2, 0 ≤ z 1 → R₀ < ‖z‖ → (ω s - ω t) z = 0 :=
    (hω.sub_data hs ht).2.1
  have hsub := halfPlaneVelocity_sub_of_continuousOn (hω.continuousOn s hs) (hω.eq_zero s hs)
    (hω.continuousOn t ht) (hω.eq_zero t ht)
  have hus := hω.contDiffOn_halfPlaneVelocity_two hα hα1 hs
  have hut := hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht
  have hus1 : ContDiffOn ℝ 1 (fderivWithin ℝ (halfPlaneVelocity (ω s)) H̄) H̄ :=
    hus.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hut1 : ContDiffOn ℝ 1 (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ :=
    hut.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have heq : EqOn (fderivWithin ℝ (halfPlaneVelocity (ω s - ω t)) H̄)
      (fderivWithin ℝ (halfPlaneVelocity (ω s)) H̄ - fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄)
      H̄ := fun z hz ↦ by
    rw [hsub, Pi.sub_apply]
    exact fderivWithin_sub (uniqueDiffOn_closedUpper z hz)
      ((hus.differentiableOn (by norm_num)) z hz) ((hut.differentiableOn (by norm_num)) z hz)
  have hD2 : fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω s - ω t)) H̄) H̄ y =
      fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω s)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω t)) H̄) H̄ y := by
    rw [fderivWithin_congr heq (heq hy)]
    exact fderivWithin_sub (uniqueDiffOn_closedUpper y hy)
      ((hus1.differentiableOn one_ne_zero) y hy) ((hut1.differentiableOn one_ne_zero) y hy)
  rw [← hD2, ← norm_iteratedFDerivWithin_two _ hy]
  have hgB : ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖ ≤ η := by
    intro z hz
    rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper z hz), hgd z hz]
    exact hδt s hs hst z hz
  have hgL : ∫ z in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖ ≤
      Real.pi * R₀ ^ 2 * η :=
    setIntegral_upper_le hR₀
      ((hgc.continuousOn_iteratedFDerivWithin le_rfl uniqueDiffOn_closedUpper).norm)
      (fun z hz hzR ↦ by rw [iteratedFDerivWithin_eq_zero_of_eq_zero hgR 1 hz hzR, norm_zero])
      hgB fun z ↦ norm_nonneg _
  have hk := norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato_homogeneous (k := 1) hα hα1
    (by exact_mod_cast hgc) hgR hgM hgB hη hgL hy
  refine le_trans ?_ hηε
  refine hk.trans ?_
  have hlog := PDE.Analysis.mul_one_add_log_le_osgoodModulus hη.le hη1
    (by positivity : (0 : ℝ) ≤ 2 * M₁)
  rw [show (2 : ℝ) * 1 + 2 * M₁ = 2 + 2 * M₁ by ring] at hlog
  have h50 : 50 * η / α * (1 + Real.log (2 + 2 * M₁ / η)) =
      50 / α * (η * (1 + Real.log (2 + 2 * M₁ / η))) := by ring
  unfold katoModulus
  push_cast
  rw [h50, one_mul]
  gcongr

/-- **The extended velocities of a `C¹` vorticity history form a `C²` field.** For `0 < α < 1`
the fields `extendedVelocity 2 (ω t)`, `t ∈ [a, b]`, and their first two derivatives are jointly
continuous on `[a, b] × ℝ²`, the first derivatives are bounded by
`2 reflectionBound 2 1 · katoBound α R₀ B M` and the second by
`2 reflectionBound 2 2 · secondDerivBound α R₀ B B₁ M₁`, `R₀ = max R 0`. -/
theorem isC2FieldOn (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α)
    (hα1 : α < 1) :
    PDE.Analysis.ODE.IsC2FieldOn (fun t ↦ extendedVelocity 2 (ω t))
      (fun t x ↦ fderiv ℝ (extendedVelocity 2 (ω t)) x)
      (fun t x ↦ fderiv ℝ (fderiv ℝ (extendedVelocity 2 (ω t))) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 * katoBound α (max R 0) B M))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R 0) B B₁ M₁)) where
  toIsC1FieldOn := hω.isC1FieldOn_extendedVelocity hα hα1 (by norm_num) fun _ ht ↦
    hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht
  continuousOn_deriv₂ := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦ fderiv ℝ (fderiv ℝ
        (weightedReflectionFun 1 2 (fun y ↦ halfPlaneVelocity (ω p.1) y k))) p.2)
        (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_fderiv_fderiv_weightedReflectionFun 1 le_rfl
        (f := fun t y ↦ halfPlaneVelocity (ω t) y k)
        (fun t ht ↦ contDiffOn_halfPlaneVelocity_apply
          (hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht) k) (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_fderivWithin_fderivWithin_sub_le hα hα1 ht hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      exact (norm_fderivWithin_fderivWithin_apply_sub_le hy
        (by exact_mod_cast hω.contDiffOn_halfPlaneVelocity_two hα hα1 hs)
        (by exact_mod_cast hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht) k).trans
          (h s hs hst y hy)
    have heq : EqOn (Function.uncurry fun t x ↦ fderiv ℝ (fderiv ℝ (extendedVelocity 2 (ω t))) x)
        (fun p : ℝ × ℝ^2 ↦ (toComponentL 0).comp (fderiv ℝ (fderiv ℝ
            (weightedReflectionFun 1 2 (fun y ↦ halfPlaneVelocity (ω p.1) y 0))) p.2) +
          (toComponentL 1).comp (fderiv ℝ (fderiv ℝ
            (weightedReflectionFun 1 2 (fun y ↦ halfPlaneVelocity (ω p.1) y 1))) p.2))
        (Icc a b ×ˢ univ) := fun p hp ↦ by
      change fderiv ℝ (fderiv ℝ (extendedVelocity 2 (ω p.1))) p.2 = _
      rw [fderiv_fderiv_extendedVelocity le_rfl
        (hω.contDiffOn_halfPlaneVelocity_two hα hα1 hp.1), Fin.sum_univ_two]
    refine ContinuousOn.congr ?_ heq
    have : ContinuousAdd (ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) :=
      (inferInstance : IsTopologicalAddGroup (ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2)).toContinuousAdd
    exact (((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2 →L[ℝ] ℝ) (ℝ^2 →L[ℝ] ℝ^2)
      (toComponentL 0)).continuous.comp_continuousOn (hcomp 0)).add
      ((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2 →L[ℝ] ℝ) (ℝ^2 →L[ℝ] ℝ^2)
        (toComponentL 1)).continuous.comp_continuousOn (hcomp 1)))
  hasFDerivAt_deriv t ht x := by
    have hE := (contDiff_extendedVelocity (by norm_num)
      (hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht)).fderiv_right (m := 1) (by norm_num)
    exact ((hE.differentiable one_ne_zero) x).hasFDerivAt
  norm_deriv₂_le t ht x :=
    (norm_fderiv_fderiv_extendedVelocity_le le_rfl
      (hω.contDiffOn_halfPlaneVelocity_two hα hα1 ht)
      (fun _ hy ↦ hω.norm_fderivWithin_fderivWithin_le hα hα1 ht hy) x).trans
        (Real.le_coe_toNNReal _)

end IsC1VorticityHistory

/-! ### `C¹` vorticity without a Hölder bound on the gradient -/

/-- **The derivative of the velocity is log-Lipschitz for `C¹` vorticity.** For `f` `C¹` within
the closed half-plane, vanishing there outside the disc of radius `R ≥ 0`, with gradient bounded
by `B₁` on the closed half-plane, for `x, x'` in the closed half-plane
`‖D u(x) - D u(x')‖ ≤ |x - x'| (11 B₁ + 4πR² B₁ + 4 B₁ log⁺(1/|x - x'|))`. -/
theorem dist_fderivWithin_halfPlaneVelocity_le_log_of_support {B₁ : ℝ}
    (hf : ContDiffOn ℝ 1 f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B₁) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    dist (fderivWithin ℝ (halfPlaneVelocity f) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity f) H̄ x') ≤
      ‖x - x'‖ * (11 * B₁ + 4 * (Real.pi * R ^ 2 * B₁) +
        4 * B₁ * Real.posLog (1 / ‖x - x'‖)) := by
  have hL := setIntegral_upper_le hR0
    ((hf.continuousOn_fderivWithin uniqueDiffOn_closedUpper le_rfl).norm)
    (fun y hy hyR ↦ by rw [fderivWithin_eq_zero_of_eq_zero hR hy hyR, norm_zero]) hB
    fun y ↦ norm_nonneg _
  refine (dist_fderivWithin_halfPlaneVelocity_le_log hf hR hB le_rfl hx hx').trans ?_
  gcongr

/-- A family of `C¹` vorticities on `[a, b]` with a common support disc, common bounds `B` of the
values and `B₁` of the gradients within the closed half-plane, continuous in time uniformly on the
closed half-plane, is a vorticity history for every exponent `α ∈ [0, 1]`, with Hölder constant
`max B₁ (2B)`: the gradient bound makes each `ω t` Lipschitz on the convex closed half-plane. -/
theorem IsVorticityHistory.of_fderivWithin_le {ω : ℝ → ℝ^2 → ℝ} {a b B₁ : ℝ}
    (hc : ∀ t ∈ Icc a b, ContDiffOn ℝ 1 (ω t) H̄)
    (hR : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → ω t y = 0)
    (hB : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → |ω t y| ≤ B)
    (hB₁ : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ (ω t) H̄ y‖ ≤ B₁)
    (huniform : ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
      ∀ y : ℝ^2, 0 ≤ y 1 → |ω s y - ω t y| ≤ ε)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsVorticityHistory ω a b α R B (max B₁ (2 * B)) where
  continuousOn t ht := (hc t ht).continuousOn
  eq_zero := hR
  abs_le := hB
  holder t ht y z hy hz := by
    have hL : ∀ x ∈ H̄, ∀ x' ∈ H̄, ‖ω t x - ω t x'‖ ≤ B₁ * dist x x' := fun x hx x' hx' ↦ by
      rw [dist_eq_norm]
      exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderivWithin_le
        ((hc t ht).differentiableOn one_ne_zero) (fun w hw ↦ hB₁ t ht w hw) hx' hx
    have h := PDE.Analysis.norm_sub_le_max_mul_rpow (f := ω t) (S := H̄) hL
      (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hB t ht x hx) hα0 hα1 (x := y) (y := z) hy hz
    rwa [Real.norm_eq_abs, dist_eq_norm] at h
  uniform := huniform

end IncompressibleFlow
