/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Geometry
public import PDE.Parabolic.Heat.MeanValue.Measurability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import PDE.Common.Euclidean.SpaceTime

/-!
# Parabolic change of variables for heat balls

The map

`(y, s) ↦ (x + r y, t + r² s)`

is a continuous affine equivalence when `r ≠ 0`.  Its linear part is the
product dilation `(s, y) ↦ (r² s, r y)` conjugated by
`timeSpaceContinuousLinearEquiv`.

For `r > 0`, the determinant is `rⁿ⁺²`, the affine map transports the unit
heat ball onto `heatBall x t r`, and Lebesgue volume and set integrals scale
by the corresponding Jacobian.  Together with the `r⁻²` scaling of the
heat-ball weight, this gives the weighted heat-ball integral net scaling `rⁿ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3 (rescaling to the unit heat
  ball).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime time)

noncomputable section

namespace HeatEquation

open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- Scalar multiplication by a nonzero real, bundled as a continuous linear
equivalence. -/
private def scalarContinuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : a ≠ 0) : E ≃L[ℝ] E :=
  (Units.mk0 a ha) • ContinuousLinearEquiv.refl ℝ E

@[simp]
private theorem scalarContinuousLinearEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : a ≠ 0) (v : E) :
    scalarContinuousLinearEquiv a ha v = a • v := by
  simp [scalarContinuousLinearEquiv]

private theorem scalarContinuousLinearEquiv_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : a ≠ 0) :
    LinearMap.det
        ((scalarContinuousLinearEquiv (E := E) a ha :
            E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
      a ^ Module.finrank ℝ E := by
  have hmap :
      ((scalarContinuousLinearEquiv (E := E) a ha :
          E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
        a • (LinearMap.id : E →ₗ[ℝ] E) := by
    ext v
    simp
  rw [hmap, LinearMap.det_smul]
  simp

/-- The product-coordinate dilation `(s, y) ↦ (r² s, r y)`. -/
private def heatBallParabolicProductLinearEquiv
    (r : ℝ) (hr : r ≠ 0) :
    (ℝ × ℝ^n) ≃L[ℝ] (ℝ × ℝ^n) :=
  (scalarContinuousLinearEquiv (E := ℝ) (r ^ 2)
      (pow_ne_zero 2 hr)).prodCongr
    (scalarContinuousLinearEquiv (E := ℝ^n) r hr)

/-- The linear parabolic dilation on canonical spacetime. -/
private def heatBallParabolicLinearEquiv
    (r : ℝ) (hr : r ≠ 0) :
    SpaceTime n ≃L[ℝ] SpaceTime n :=
  ((timeSpaceContinuousLinearEquiv n).trans
      (heatBallParabolicProductLinearEquiv (n := n) r hr)).trans
    (timeSpaceContinuousLinearEquiv n).symm

/-- Translate by `(x,t)` after applying the parabolic linear dilation. -/
private def heatBallParabolicAffineEquiv
    (x : ℝ^n) (t r : ℝ) (hr : r ≠ 0) :
    SpaceTime n ≃ᴬ[ℝ] SpaceTime n :=
  (heatBallParabolicLinearEquiv (n := n) r hr).toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ (SpaceTime n)
      (timeSpaceCons t x))

@[simp]
private theorem heatBallParabolicAffineEquiv_apply
    (x : ℝ^n) (t r : ℝ) (hr : r ≠ 0) (p : SpaceTime n) :
    heatBallParabolicAffineEquiv x t r hr p =
      heatBallParabolicMap x t r p := by
  change
    timeSpaceCons t x +
        timeSpaceCons (r ^ 2 * time p) (r • spatialPart p) =
      timeSpaceCons (t + r ^ 2 * time p)
        (x + r • spatialPart p)
  ext i
  cases i using Fin.cases <;>
    simp [time]

/-- The affine parabolic map pulls a heat ball back to the unit heat ball. -/
private theorem heatBallParabolicAffineEquiv_preimage_heatBall
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    heatBallParabolicAffineEquiv x t r hr.ne' ⁻¹'
        heatBall x t r =
      heatBall (0 : ℝ^n) 0 1 := by
  ext p
  simpa using heatBallParabolicMap_mem_iff x t hr p

/-- The affine parabolic map sends the unit heat ball onto the heat ball with
pole `(x,t)` and radius parameter `r`. -/
private theorem heatBallParabolicAffineEquiv_image_heatBall
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    heatBallParabolicAffineEquiv x t r hr.ne' ''
        heatBall (0 : ℝ^n) 0 1 =
      heatBall x t r := by
  calc
    heatBallParabolicAffineEquiv x t r hr.ne' ''
          heatBall (0 : ℝ^n) 0 1 =
        heatBallParabolicAffineEquiv x t r hr.ne' ''
          (heatBallParabolicAffineEquiv x t r hr.ne' ⁻¹'
            heatBall x t r) := by
      rw [heatBallParabolicAffineEquiv_preimage_heatBall x t hr]
    _ = heatBall x t r :=
      (heatBallParabolicAffineEquiv x t r hr.ne').image_preimage _

private theorem heatBallParabolicProductLinearEquiv_det
    (r : ℝ) (hr : r ≠ 0) :
    LinearMap.det
        ((heatBallParabolicProductLinearEquiv (n := n) r hr :
            (ℝ × ℝ^n) ≃L[ℝ] (ℝ × ℝ^n)) :
          (ℝ × ℝ^n) →ₗ[ℝ] (ℝ × ℝ^n)) =
      r ^ (n + 2) := by
  change LinearMap.det
      (LinearMap.prodMap
        ((scalarContinuousLinearEquiv (E := ℝ) (r ^ 2)
            (pow_ne_zero 2 hr) : ℝ ≃L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)
        ((scalarContinuousLinearEquiv (E := ℝ^n) r hr :
            ℝ^n ≃L[ℝ] ℝ^n) : ℝ^n →ₗ[ℝ] ℝ^n)) =
    r ^ (n + 2)
  rw [LinearMap.det_prodMap,
    scalarContinuousLinearEquiv_det,
    scalarContinuousLinearEquiv_det]
  simp [pow_add, mul_comm]

/-- The Jacobian determinant of parabolic dilation is `rⁿ⁺²`: one factor
`r²` from time and `n` factors `r` from space. -/
private theorem heatBallParabolicLinearEquiv_det
    (r : ℝ) (hr : r ≠ 0) :
    LinearMap.det
        ((heatBallParabolicLinearEquiv (n := n) r hr :
            SpaceTime n ≃L[ℝ] SpaceTime n) :
          SpaceTime n →ₗ[ℝ] SpaceTime n) =
      r ^ (n + 2) := by
  calc
    LinearMap.det
          ((heatBallParabolicLinearEquiv (n := n) r hr :
              SpaceTime n ≃L[ℝ] SpaceTime n) :
            SpaceTime n →ₗ[ℝ] SpaceTime n) =
        LinearMap.det
          ((heatBallParabolicProductLinearEquiv (n := n) r hr :
              (ℝ × ℝ^n) ≃L[ℝ] (ℝ × ℝ^n)) :
            (ℝ × ℝ^n) →ₗ[ℝ] (ℝ × ℝ^n)) := by
      simpa [heatBallParabolicLinearEquiv] using
        (LinearMap.det_conj
          ((heatBallParabolicProductLinearEquiv (n := n) r hr :
              (ℝ × ℝ^n) ≃L[ℝ] (ℝ × ℝ^n)) :
            (ℝ × ℝ^n) →ₗ[ℝ] (ℝ × ℝ^n))
          (timeSpaceContinuousLinearEquiv n).symm.toLinearEquiv)
    _ = r ^ (n + 2) :=
      heatBallParabolicProductLinearEquiv_det r hr

/-- Pushforward of Lebesgue volume by the linear parabolic dilation.  Mathlib's
`Measure.map` convention introduces the inverse Jacobian. -/
private theorem map_heatBallParabolicLinearEquiv_volume
    {r : ℝ} (hr : 0 < r) :
    Measure.map (heatBallParabolicLinearEquiv (n := n) r hr.ne')
        (volume : Measure (SpaceTime n)) =
      ENNReal.ofReal ((r ^ (n + 2))⁻¹) •
        (volume : Measure (SpaceTime n)) := by
  have hdet :
      LinearMap.det
          ((heatBallParabolicLinearEquiv (n := n) r hr.ne' :
              SpaceTime n ≃L[ℝ] SpaceTime n) :
            SpaceTime n →ₗ[ℝ] SpaceTime n) ≠ 0 := by
    rw [heatBallParabolicLinearEquiv_det]
    exact pow_ne_zero _ hr.ne'
  have hJinv : 0 < (r ^ (n + 2))⁻¹ :=
    inv_pos.mpr (pow_pos hr _)
  simpa [heatBallParabolicLinearEquiv_det, abs_of_pos hJinv] using
    (MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (SpaceTime n)) hdet)

/-- Translation leaves Lebesgue volume invariant, so the affine parabolic map
has the same pushforward factor as its linear part. -/
private theorem map_heatBallParabolicAffineEquiv_volume
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Measure.map (heatBallParabolicAffineEquiv x t r hr.ne')
        (volume : Measure (SpaceTime n)) =
      ENNReal.ofReal ((r ^ (n + 2))⁻¹) •
        (volume : Measure (SpaceTime n)) := by
  change Measure.map
      ((fun q : SpaceTime n ↦ timeSpaceCons t x + q) ∘
        fun p ↦ heatBallParabolicLinearEquiv (n := n) r hr.ne' p)
      (volume : Measure (SpaceTime n)) = _
  rw [← Measure.map_map
    (μ := (volume : Measure (SpaceTime n)))
    (g := fun q : SpaceTime n ↦ timeSpaceCons t x + q)
    (f := fun p ↦ heatBallParabolicLinearEquiv (n := n) r hr.ne' p)
    (continuous_const.add continuous_id).measurable
    (heatBallParabolicLinearEquiv (n := n) r hr.ne').continuous.measurable]
  rw [map_heatBallParabolicLinearEquiv_volume hr,
    Measure.map_smul _ (f := fun q : SpaceTime n ↦ timeSpaceCons t x + q)
      (continuous_const.add continuous_id).aemeasurable]
  change ENNReal.ofReal ((r ^ (n + 2))⁻¹) •
      Measure.map
        (fun q : SpaceTime n ↦ timeSpaceCons t x + q)
        (volume : Measure (SpaceTime n)) =
    ENNReal.ofReal ((r ^ (n + 2))⁻¹) •
      (volume : Measure (SpaceTime n))
  rw [MeasureTheory.map_add_left_eq_self]

/-- Change of variables for a set integral over the image of the affine
parabolic map. -/
private theorem setIntegral_image_heatBallParabolicAffineEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : SpaceTime n → E) (s : Set (SpaceTime n))
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ q in heatBallParabolicAffineEquiv x t r hr.ne' '' s,
        F q ∂volume) =
      r ^ (n + 2) •
        ∫ p in s,
          F (heatBallParabolicAffineEquiv x t r hr.ne' p) ∂volume := by
  let A := (heatBallParabolicAffineEquiv x t r hr.ne').toHomeomorph
  have hJ : (0 : ℝ) < r ^ (n + 2) := pow_pos hr _
  have htransport :=
    A.measurableEmbedding.setIntegral_map (μ := (volume : Measure (SpaceTime n))) F (A '' s)
  rw [show Measure.map A (volume : Measure (SpaceTime n)) =
      ENNReal.ofReal ((r ^ (n + 2))⁻¹) • volume from map_heatBallParabolicAffineEquiv_volume x t hr,
    Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hJ.le)] at htransport
  have hscaled : (r ^ (n + 2))⁻¹ • (∫ q in A '' s, F q ∂volume) = ∫ p in s, F (A p) ∂volume := by
    simpa [A] using htransport
  exact (inv_smul_eq_iff₀ hJ.ne').1 hscaled

/-- The weighted heat-ball integral has net scaling `rⁿ`: volume contributes
`rⁿ⁺²` and the heat-ball weight contributes `r⁻²`. -/
theorem heatBallWeighted_setIntegral_scaling
    (u : SpaceTime n → ℝ) (x : ℝ^n) (t : ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ q in heatBall x t r,
        heatBallWeight x t q * u q
          ∂(volume : Measure (SpaceTime n))) =
      r ^ n *
        ∫ p in heatBall (0 : ℝ^n) 0 1,
          heatBallWeight (0 : ℝ^n) 0 p *
            u (heatBallParabolicMap x t r p)
              ∂(volume : Measure (SpaceTime n)) := by
  have hchange := setIntegral_image_heatBallParabolicAffineEquiv (n := n)
    (F := fun q ↦ heatBallWeight x t q * u q) (s := heatBall (0 : ℝ^n) 0 1) x t hr
  rw [heatBallParabolicAffineEquiv_image_heatBall x t hr] at hchange
  simp only [heatBallParabolicAffineEquiv_apply, smul_eq_mul] at hchange
  have hweight : (∫ p in heatBall (0 : ℝ^n) 0 1,
      heatBallWeight x t (heatBallParabolicMap x t r p) * u (heatBallParabolicMap x t r p)) =
        (r ^ 2)⁻¹ * ∫ p in heatBall (0 : ℝ^n) 0 1,
          heatBallWeight (0 : ℝ^n) 0 p * u (heatBallParabolicMap x t r p) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_heatBall (n := n) 0 0 1) fun p hp ↦ ?_
    have hpast : time p < 0 := by
      simpa using time_lt_of_mem_heatBall (n := n) (x := 0) (t := 0) (r := 1) zero_lt_one hp
    beta_reduce
    rw [heatBallWeight_heatBallParabolicMap x t hr p hpast, mul_assoc]
  rw [hchange, hweight]
  simp [pow_add, hr.ne', mul_assoc]

end HeatEquation
