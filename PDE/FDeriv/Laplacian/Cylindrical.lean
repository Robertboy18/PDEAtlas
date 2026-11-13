/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Composition
public import PDE.CoordinateSystems.Cylindrical
public import PDE.FDeriv.Calculus

/-!
# The Laplacian in cylindrical coordinates

The pullback formulas retain the angular derivative and allow any real normed
codomain. For vector fields they differentiate Cartesian components in a fixed
basis. The squared-radius convention is parametrized by `q = a r²`.
All differential identities follow from local `C²` regularity of the field.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems

open EuclideanSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cylindrical Laplacian in radius, angle, and height. Its classical
interpretation uses a nonzero radius. -/
def cylindricalLaplacian (f : ℝ^3 → E) (q : ℝ^3) : E :=
  (∂[0] (∂[0] f)) q + (q 0)⁻¹ • (∂[0] f) q +
    ((q 0) ^ 2)⁻¹ • (∂[1] (∂[1] f)) q + (∂[2] (∂[2] f)) q

/-- The second directional chain rule specialized to a coordinate direction. -/
theorem secondPartialDeriv_comp {f : ℝ^3 → E} {g : ℝ^3 → ℝ^3} {q : ℝ^3}
    (hf : ContDiffAt ℝ 2 f (g q)) (hg : ContDiffAt ℝ 2 g q) (i : Fin 3) :
    (∂[i] (∂[i] (f ∘ g))) q =
      fderiv ℝ (fderiv ℝ f) (g q) ((∂[i] g) q) ((∂[i] g) q) +
        fderiv ℝ f (g q) ((∂[i] (∂[i] g)) q) :=
  PDE.Analysis.fderiv_fderiv_comp_apply hf hg (single i 1) (single i 1)

/-- The radial derivative of the chart is the radial unit vector. -/
theorem partialDeriv_cylindricalMap_zero (q : ℝ^3) :
    (∂[0] cylindricalMap) q =
      Real.cos (q 1) • single (0 : Fin 3) 1 +
        Real.sin (q 1) • single (1 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_cylindricalMap q).fderiv, cylindricalJacobian_apply]

/-- The angular derivative of the chart is the radius times the angular unit vector. -/
theorem partialDeriv_cylindricalMap_one (q : ℝ^3) :
    (∂[1] cylindricalMap) q =
      (-q 0 * Real.sin (q 1)) • single (0 : Fin 3) 1 +
        (q 0 * Real.cos (q 1)) • single (1 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_cylindricalMap q).fderiv, cylindricalJacobian_apply]

/-- The axial derivative of the chart is the vertical unit vector. -/
theorem partialDeriv_cylindricalMap_two (q : ℝ^3) :
    (∂[2] cylindricalMap) q = single (2 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_cylindricalMap q).fderiv, cylindricalJacobian_apply]

/-- The chart is linear in its radius coordinate. -/
theorem secondPartialDeriv_cylindricalMap_zero (q : ℝ^3) :
    (∂[0] (∂[0] cylindricalMap)) q = 0 := by
  rw [show (∂[0] cylindricalMap) = _ from funext partialDeriv_cylindricalMap_zero]
  have h1 := (proj 1 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h : HasFDerivAt
      (fun y : ℝ^3 ↦ Real.cos (y 1) • single (0 : Fin 3) (1 : ℝ) +
        Real.sin (y 1) • single (1 : Fin 3) (1 : ℝ)) _ q :=
    (h1.cos.smul_const _).add (h1.sin.smul_const _)
  simp [partialDeriv, h.fderiv]

/-- The second angular derivative is minus the radius times the radial unit vector. -/
theorem secondPartialDeriv_cylindricalMap_one (q : ℝ^3) :
    (∂[1] (∂[1] cylindricalMap)) q = -q 0 • (∂[0] cylindricalMap) q := by
  rw [show (∂[1] cylindricalMap) = _ from funext partialDeriv_cylindricalMap_one]
  have h0 := (proj 0 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h1 := (proj 1 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h : HasFDerivAt
      (fun y : ℝ^3 ↦ (-y 0 * Real.sin (y 1)) • single (0 : Fin 3) (1 : ℝ) +
        (y 0 * Real.cos (y 1)) • single (1 : Fin 3) (1 : ℝ)) _ q :=
    ((h0.neg.mul h1.sin).smul_const _).add ((h0.mul h1.cos).smul_const _)
  change fderiv ℝ _ q (single (1 : Fin 3) 1) = _
  rw [h.fderiv, partialDeriv_cylindricalMap_zero]
  simp [smul_add, smul_smul]

/-- The chart is linear in its axial coordinate. -/
theorem secondPartialDeriv_cylindricalMap_two (q : ℝ^3) :
    (∂[2] (∂[2] cylindricalMap)) q = 0 := by
  rw [show (∂[2] cylindricalMap) = _ from funext partialDeriv_cylindricalMap_two]
  exact partialDeriv_const _

/-- The cylindrical Laplacian is the pullback of the Cartesian Laplacian.
Local `C²` regularity suffices and no angular invariance is assumed. -/
theorem cylindricalLaplacian_comp_cylindricalMap {f : ℝ^3 → E} {q : ℝ^3}
    (hf : ContDiffAt ℝ 2 f (cylindricalMap q)) (hr : q 0 ≠ 0) :
    cylindricalLaplacian (f ∘ cylindricalMap) q = laplacian f (cylindricalMap q) := by
  have hc : ContDiffAt ℝ 2 cylindricalMap q := contDiff_cylindricalMap.contDiffAt
  have hH (i : Fin 3) : (∂[i] (∂[i] f)) (cylindricalMap q) =
      fderiv ℝ (fderiv ℝ f) (cylindricalMap q) (single i 1) (single i 1) :=
    secondPartialDeriv_eq_fderiv i i
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one)
  have hD : (∂[0] (f ∘ cylindricalMap)) q =
      fderiv ℝ f (cylindricalMap q) ((∂[0] cylindricalMap) q) := by
    simp only [partialDeriv, fderiv_comp q (hf.differentiableAt (by norm_num))
      (hc.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply]
  unfold cylindricalLaplacian laplacian
  rw [secondPartialDeriv_comp hf hc 0, secondPartialDeriv_comp hf hc 1,
    secondPartialDeriv_comp hf hc 2, hD, secondPartialDeriv_cylindricalMap_zero,
    secondPartialDeriv_cylindricalMap_one, secondPartialDeriv_cylindricalMap_two]
  simp only [Fin.sum_univ_three, hH, partialDeriv_cylindricalMap_zero,
    partialDeriv_cylindricalMap_one, partialDeriv_cylindricalMap_two, map_add, map_smul,
    map_zero, _root_.add_apply, _root_.smul_apply, add_zero]
  match_scalars <;> field_simp [hr] <;> nlinarith [Real.cos_sq_add_sin_sq (q 1)]

/-- The Laplacian in scaled squared radius `q = a r²`, angle, and height.
For `a = 1` the radial coefficients are `4q, 4`; for `a = 1/2` they are `2q, 2`. -/
def scaledCylindricalLaplacian (a : ℝ) (f : ℝ^3 → E) (q : ℝ^3) : E :=
  (4 * a * q 0) • (∂[0] (∂[0] f)) q + (4 * a) • (∂[0] f) q +
    (a / q 0) • (∂[1] (∂[1] f)) q + (∂[2] (∂[2] f)) q

/-- The radial derivative of the squared-radius substitution. -/
theorem partialDeriv_squaredRadiusMap_zero (a : ℝ) (q : ℝ^3) :
    (∂[0] (squaredRadiusMap a)) q = (2 * a * q 0) • single (0 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_squaredRadiusMap a q).fderiv]

/-- The squared-radius substitution leaves the angular direction unchanged. -/
theorem partialDeriv_squaredRadiusMap_one (a : ℝ) (q : ℝ^3) :
    (∂[1] (squaredRadiusMap a)) q = single (1 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_squaredRadiusMap a q).fderiv]

/-- The squared-radius substitution leaves the axial direction unchanged. -/
theorem partialDeriv_squaredRadiusMap_two (a : ℝ) (q : ℝ^3) :
    (∂[2] (squaredRadiusMap a)) q = single (2 : Fin 3) 1 := by
  simp [partialDeriv, (hasFDerivAt_squaredRadiusMap a q).fderiv]

/-- The second radial derivative of the squared-radius substitution. -/
theorem secondPartialDeriv_squaredRadiusMap_zero (a : ℝ) (q : ℝ^3) :
    (∂[0] (∂[0] (squaredRadiusMap a))) q = (2 * a) • single (0 : Fin 3) 1 := by
  rw [show (∂[0] (squaredRadiusMap a)) = _ from
    funext (partialDeriv_squaredRadiusMap_zero a)]
  have h : HasFDerivAt
      (fun y : ℝ^3 ↦ (2 * a * y 0) • single (0 : Fin 3) (1 : ℝ)) _ q :=
    (((proj 0 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * a)).smul_const _)
  simp [partialDeriv, h.fderiv]

/-- The substitution is linear in angle. -/
theorem secondPartialDeriv_squaredRadiusMap_one (a : ℝ) (q : ℝ^3) :
    (∂[1] (∂[1] (squaredRadiusMap a))) q = 0 := by
  rw [show (∂[1] (squaredRadiusMap a)) = _ from
    funext (partialDeriv_squaredRadiusMap_one a)]
  exact partialDeriv_const _

/-- The substitution is linear in height. -/
theorem secondPartialDeriv_squaredRadiusMap_two (a : ℝ) (q : ℝ^3) :
    (∂[2] (∂[2] (squaredRadiusMap a))) q = 0 := by
  rw [show (∂[2] (squaredRadiusMap a)) = _ from
    funext (partialDeriv_squaredRadiusMap_two a)]
  exact partialDeriv_const _

/-- Substituting `q = a r²` transforms the cylindrical Laplacian into its scaled
squared-radius expression. The proof differentiates the substitution twice. -/
theorem cylindricalLaplacian_comp_squaredRadiusMap {a : ℝ} (ha : a ≠ 0)
    {f : ℝ^3 → E} {q : ℝ^3} (hf : ContDiffAt ℝ 2 f (squaredRadiusMap a q))
    (hr : q 0 ≠ 0) :
    cylindricalLaplacian (f ∘ squaredRadiusMap a) q =
      scaledCylindricalLaplacian a f (squaredRadiusMap a q) := by
  have hs : ContDiffAt ℝ 2 (squaredRadiusMap a) q :=
    (contDiff_squaredRadiusMap a).contDiffAt
  have hH (i : Fin 3) : (∂[i] (∂[i] f)) (squaredRadiusMap a q) =
      fderiv ℝ (fderiv ℝ f) (squaredRadiusMap a q) (single i 1) (single i 1) :=
    secondPartialDeriv_eq_fderiv i i
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one)
  have hD : (∂[0] (f ∘ squaredRadiusMap a)) q =
      fderiv ℝ f (squaredRadiusMap a q) ((∂[0] (squaredRadiusMap a)) q) := by
    simp only [partialDeriv, fderiv_comp q (hf.differentiableAt (by norm_num))
      (hs.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply]
  unfold cylindricalLaplacian scaledCylindricalLaplacian
  rw [secondPartialDeriv_comp hf hs 0, secondPartialDeriv_comp hf hs 1,
    secondPartialDeriv_comp hf hs 2, hD, secondPartialDeriv_squaredRadiusMap_zero,
    secondPartialDeriv_squaredRadiusMap_one, secondPartialDeriv_squaredRadiusMap_two]
  simp only [hH, partialDeriv_squaredRadiusMap_zero, partialDeriv_squaredRadiusMap_one,
    partialDeriv_squaredRadiusMap_two, map_smul, map_zero, _root_.smul_apply, add_zero]
  change _ = _ + (4 * a) • fderiv ℝ f (squaredRadiusMap a q) (single 0 1) + _ + _
  have hs0 : squaredRadiusMap a q 0 = a * q 0 ^ 2 := by simp [squaredRadiusMap]
  rw [hs0]
  match_scalars <;> field_simp [hr, ha] <;> ring

/-- The scaled squared-radius Laplacian is the pullback of the Cartesian Laplacian.
The condition `0 < q₀/a` is exactly the positive-radius domain of the chart. -/
theorem scaledCylindricalLaplacian_comp_scaledCylindricalMap (a : ℝ)
    {f : ℝ^3 → E} {q : ℝ^3} (hq : 0 < q 0 / a)
    (hf : ContDiffAt ℝ 2 f (scaledCylindricalMap a q)) :
    scaledCylindricalLaplacian a (f ∘ scaledCylindricalMap a) q =
      laplacian f (scaledCylindricalMap a q) := by
  have ha : a ≠ 0 := by rintro rfl; simp at hq
  let r := sqrtRadiusMap a q
  have hr : 0 < r 0 := by simpa [r, sqrtRadiusMap] using Real.sqrt_pos.2 hq
  have hinv : squaredRadiusMap a r = q := squaredRadiusMap_sqrtRadiusMap a hq
  have hcomp : ContDiffAt ℝ 2 (f ∘ scaledCylindricalMap a) q :=
    hf.comp q (contDiffAt_scaledCylindricalMap a hq)
  have hchange := cylindricalLaplacian_comp_squaredRadiusMap ha
    (hinv ▸ hcomp) hr.ne'
  have hnear : ((f ∘ scaledCylindricalMap a) ∘ squaredRadiusMap a) =ᶠ[𝓝 r]
      f ∘ cylindricalMap := by
    filter_upwards [((proj 0 : ℝ^3 →L[ℝ] ℝ).continuous.continuousAt.eventually
      (lt_mem_nhds hr))] with y hy
    change 0 < y 0 at hy
    simp only [Function.comp_apply, scaledCylindricalMap_squaredRadiusMap ha hy.le]
  have hlap : cylindricalLaplacian ((f ∘ scaledCylindricalMap a) ∘ squaredRadiusMap a) r =
      cylindricalLaplacian (f ∘ cylindricalMap) r := by
    unfold cylindricalLaplacian
    rw [((hnear.partialDeriv 0).partialDeriv 0).eq_of_nhds,
      (hnear.partialDeriv 0).eq_of_nhds,
      ((hnear.partialDeriv 1).partialDeriv 1).eq_of_nhds,
      ((hnear.partialDeriv 2).partialDeriv 2).eq_of_nhds]
  rw [hinv, hlap] at hchange
  rw [← hchange]
  exact cylindricalLaplacian_comp_cylindricalMap hf hr.ne'

end PDE.CoordinateSystems
