/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.Profile
public import Mathlib.Analysis.Calculus.Deriv.Slope
import PDE.Analysis.Calculus.Radial.OriginDifferentiability
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Hyperbolic meridian coordinates and their derivative formulas

The change of variables `R = sinh ρ`, `Z = sinh ζ` spreads a computational grid
over the meridian plane. Pulling a profile back along this map introduces `cosh`
factors in its first and second derivatives. The formulas below solve for the
physical derivatives and transfer the axisymmetric elliptic operator to the
computational coordinates.

The radial quotient needs a separate argument at the axis: for an even smooth
profile, its first radial derivative vanishes, and the quotient tends to the
second derivative. We prove that limit before identifying the regularized
operators.
-/

@[expose] public section

noncomputable section

open scoped Topology

open PDE.FDeriv

namespace PDE.CoordinateSystems

/-- The map `(ρ, ζ) ↦ (sinh ρ, sinh ζ)` from computational to profile coordinates. -/
def computationalCoordinateMap (x : (ℝ^2)) : (ℝ^2) :=
  EuclideanSpace.single 0 (Real.sinh (meridianR x)) +
    EuclideanSpace.single 1 (Real.sinh (meridianZ x))

/-- The radial component. -/
@[simp]
theorem computationalCoordinateMap_zero (x : (ℝ^2)) :
    computationalCoordinateMap x 0 = Real.sinh (meridianR x) := by
  simp [computationalCoordinateMap]

/-- The axial component. -/
@[simp]
theorem computationalCoordinateMap_one (x : (ℝ^2)) :
    computationalCoordinateMap x 1 = Real.sinh (meridianZ x) := by
  simp [computationalCoordinateMap]

/-- The physical radial coordinate after the computational coordinate map. -/
@[simp]
theorem meridianR_computationalCoordinateMap (x : (ℝ^2)) :
    meridianR (computationalCoordinateMap x) = Real.sinh (meridianR x) := by
  simp [meridianR]

/-- The physical axial coordinate after the computational coordinate map. -/
@[simp]
theorem meridianZ_computationalCoordinateMap (x : (ℝ^2)) :
    meridianZ (computationalCoordinateMap x) = Real.sinh (meridianZ x) := by
  simp [meridianZ]

/-- The hyperbolic computational coordinate map is smooth. -/
theorem contDiff_computationalCoordinateMap :
    ContDiff ℝ (⊤ : ℕ∞) computationalCoordinateMap := by
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · have hr :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ^2) ↦ Real.sinh (meridianR x)) := by
      simpa [meridianR, Function.comp_def] using
        Real.contDiff_sinh.comp
          (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) 0).contDiff
    simpa [computationalCoordinateMap] using hr
  · have hz :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ^2) ↦ Real.sinh (meridianZ x)) := by
      simpa [meridianZ, Function.comp_def] using
        Real.contDiff_sinh.comp
          (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) 1).contDiff
    simpa [computationalCoordinateMap] using hz

/-- The coordinate identity: pull a physical profile back to computational coordinates. -/
def computationalPullback (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ f (computationalCoordinateMap x)

/-- Computational pullback preserves every finite or infinite smoothness order. -/
theorem contDiff_computationalPullback {n : ℕ∞} {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (computationalPullback f) :=
  hf.comp (contDiff_computationalCoordinateMap.of_le (by simp))

private theorem partialDeriv_zero_sinh_rCoord (x : (ℝ^2)) :
    (∂[(0 : Fin 2)] (fun y : (ℝ^2) ↦ Real.sinh (meridianR y))) x =
      Real.cosh (meridianR x) := by
  unfold meridianR
  cas

private theorem partialDeriv_one_sinh_rCoord (x : (ℝ^2)) :
    (∂[(1 : Fin 2)] (fun y : (ℝ^2) ↦ Real.sinh (meridianR y))) x = 0 := by
  unfold meridianR
  cas

private theorem partialDeriv_zero_sinh_zCoord (x : (ℝ^2)) :
    (∂[(0 : Fin 2)] (fun y : (ℝ^2) ↦ Real.sinh (meridianZ y))) x = 0 := by
  unfold meridianZ
  cas

private theorem partialDeriv_one_sinh_zCoord (x : (ℝ^2)) :
    (∂[(1 : Fin 2)] (fun y : (ℝ^2) ↦ Real.sinh (meridianZ y))) x =
      Real.cosh (meridianZ x) := by
  unfold meridianZ
  cas

private theorem partialDeriv_zero_cosh_rCoord (x : (ℝ^2)) :
    (∂[(0 : Fin 2)] (fun y : (ℝ^2) ↦ Real.cosh (meridianR y))) x =
      Real.sinh (meridianR x) := by
  unfold meridianR
  cas

private theorem partialDeriv_one_cosh_zCoord (x : (ℝ^2)) :
    (∂[(1 : Fin 2)] (fun y : (ℝ^2) ↦ Real.cosh (meridianZ y))) x =
      Real.sinh (meridianZ x) := by
  unfold meridianZ
  cas

/-- The radial chain rule. -/
theorem profileDR_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDR (computationalPullback f) x =
      Real.cosh (meridianR x) * profileDR f (computationalCoordinateMap x) := by
  unfold profileDR computationalPullback
  calc
    _ = ∑ j : Fin 2,
        (∂[(j : Fin 2)] f) (computationalCoordinateMap x) *
          (∂[(0 : Fin 2)]
            (fun y : (ℝ^2) ↦ computationalCoordinateMap y j)) x :=
      partialDeriv_comp 0 f computationalCoordinateMap x
        (hf.differentiable one_ne_zero).differentiableAt
        (contDiff_computationalCoordinateMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, computationalCoordinateMap_zero,
        computationalCoordinateMap_one]
      rw [partialDeriv_zero_sinh_rCoord, partialDeriv_zero_sinh_zCoord]
      ring

/-- The axial chain rule. -/
theorem profileDZ_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDZ (computationalPullback f) x =
      Real.cosh (meridianZ x) * profileDZ f (computationalCoordinateMap x) := by
  unfold profileDZ computationalPullback
  calc
    _ = ∑ j : Fin 2,
        (∂[(j : Fin 2)] f) (computationalCoordinateMap x) *
          (∂[(1 : Fin 2)]
            (fun y : (ℝ^2) ↦ computationalCoordinateMap y j)) x :=
      partialDeriv_comp 1 f computationalCoordinateMap x
        (hf.differentiable one_ne_zero).differentiableAt
        (contDiff_computationalCoordinateMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, computationalCoordinateMap_zero,
        computationalCoordinateMap_one]
      rw [partialDeriv_one_sinh_rCoord, partialDeriv_one_sinh_zCoord]
      ring

/-- The radial derivative solved for the physical derivative. -/
theorem profileDR_at_computationalCoordinateMap {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDR f (computationalCoordinateMap x) =
      profileDR (computationalPullback f) x / Real.cosh (meridianR x) := by
  rw [profileDR_computationalPullback hf x]
  field_simp [(Real.cosh_pos _).ne']

/-- The axial derivative solved for the physical derivative. -/
theorem profileDZ_at_computationalCoordinateMap {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDZ f (computationalCoordinateMap x) =
      profileDZ (computationalPullback f) x / Real.cosh (meridianZ x) := by
  rw [profileDZ_computationalPullback hf x]
  field_simp [(Real.cosh_pos _).ne']

/-- The unsolved second radial chain rule:
`fρρ = sinh ρ fR + cosh² ρ fRR`. -/
theorem profileDRR_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDRR (computationalPullback f) x =
      Real.sinh (meridianR x) * profileDR f (computationalCoordinateMap x) +
        Real.cosh (meridianR x) ^ 2 *
          profileDRR f (computationalCoordinateMap x) := by
  have hf_one : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf_r : ContDiff ℝ 1 (profileDR f) := by
    exact contDiff_partialDeriv_of_succ hf
  have hfirst :
      profileDR (computationalPullback f) =
        fun y ↦
          Real.cosh (meridianR y) *
            profileDR f (computationalCoordinateMap y) := by
    funext y
    exact profileDR_computationalPullback hf_one y
  unfold profileDRR
  rw [hfirst, partialDeriv_mul]
  · change
      (∂[(0 : Fin 2)]
          (fun y : (ℝ^2) ↦ Real.cosh (meridianR y))) x *
          profileDR f (computationalCoordinateMap x) +
        Real.cosh (meridianR x) *
          profileDR (computationalPullback (profileDR f)) x = _
    rw [partialDeriv_zero_cosh_rCoord]
    rw [profileDR_computationalPullback hf_r]
    simp only [profileDR]
    ring
  · change DifferentiableAt ℝ (fun y : (ℝ^2) ↦ Real.cosh (y 0)) x
    fun_prop
  · exact
      ((contDiff_computationalPullback hf_r).differentiable one_ne_zero).differentiableAt

/-- The unsolved second axial chain rule:
`fζζ = sinh ζ fZ + cosh² ζ fZZ`. -/
theorem profileDZZ_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDZZ (computationalPullback f) x =
      Real.sinh (meridianZ x) * profileDZ f (computationalCoordinateMap x) +
        Real.cosh (meridianZ x) ^ 2 *
          profileDZZ f (computationalCoordinateMap x) := by
  have hf_one : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf_z : ContDiff ℝ 1 (profileDZ f) := by
    exact contDiff_partialDeriv_of_succ hf
  have hfirst :
      profileDZ (computationalPullback f) =
        fun y ↦
          Real.cosh (meridianZ y) *
            profileDZ f (computationalCoordinateMap y) := by
    funext y
    exact profileDZ_computationalPullback hf_one y
  unfold profileDZZ
  rw [hfirst, partialDeriv_mul]
  · change
      (∂[(1 : Fin 2)]
          (fun y : (ℝ^2) ↦ Real.cosh (meridianZ y))) x *
          profileDZ f (computationalCoordinateMap x) +
        Real.cosh (meridianZ x) *
          profileDZ (computationalPullback (profileDZ f)) x = _
    rw [partialDeriv_one_cosh_zCoord]
    rw [profileDZ_computationalPullback hf_z]
    simp only [profileDZ]
    ring
  · change DifferentiableAt ℝ (fun y : (ℝ^2) ↦ Real.cosh (y 1)) x
    fun_prop
  · exact
      ((contDiff_computationalPullback hf_z).differentiable one_ne_zero).differentiableAt

/-- The second radial derivative solved for the physical derivative. -/
theorem profileDRR_at_computationalCoordinateMap {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDRR f (computationalCoordinateMap x) =
      profileDRR (computationalPullback f) x / Real.cosh (meridianR x) ^ 2 -
        Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 *
          profileDR (computationalPullback f) x := by
  have hfirst := profileDR_computationalPullback (hf.of_le (by norm_num)) x
  have hsecond := profileDRR_computationalPullback hf x
  have hcosh : Real.cosh (meridianR x) ≠ 0 := (Real.cosh_pos _).ne'
  rw [hsecond, hfirst]
  field_simp [hcosh]
  ring

/-- The second axial derivative solved for the physical derivative. -/
theorem profileDZZ_at_computationalCoordinateMap {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDZZ f (computationalCoordinateMap x) =
      profileDZZ (computationalPullback f) x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 *
          profileDZ (computationalPullback f) x := by
  have hfirst := profileDZ_computationalPullback (hf.of_le (by norm_num)) x
  have hsecond := profileDZZ_computationalPullback hf x
  have hcosh : Real.cosh (meridianZ x) ≠ 0 := (Real.cosh_pos _).ne'
  rw [hsecond, hfirst]
  field_simp [hcosh]
  ring

/-- The computational version of `(∂R f)/R`, with its removable axis value selected. -/
def computationalDrOverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    if meridianR x = 0 then profileDRR f x
    else profileDR f x /
      (Real.sinh (meridianR x) * Real.cosh (meridianR x))

/-- The physical first and second derivatives, and the quotient `(∂R f)/R`, expressed through
derivatives in the `(ρ, ζ)` coordinates. -/
def computationalAxisymmetricDifferential : AxisymmetricDifferential where
  dR := fun f x ↦ profileDR f x / Real.cosh (meridianR x)
  dZ := fun f x ↦ profileDZ f x / Real.cosh (meridianZ x)
  dRR := fun f x ↦
    profileDRR f x / Real.cosh (meridianR x) ^ 2 -
      Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 * profileDR f x
  dZZ := fun f x ↦
    profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
      Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x
  dROverR := computationalDrOverR

/-- The axisymmetric elliptic operator in hyperbolic computational coordinates. -/
def computationalElliptic (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  axisymmetricLaplacian computationalAxisymmetricDifferential f

/-- Off the axis, `computationalElliptic` is exactly the displayed expression. -/
theorem computationalElliptic_of_ne_zero (f : (ℝ^2 → ℝ)) (x : (ℝ^2))
    (hx : meridianR x ≠ 0) :
    computationalElliptic f x =
      profileDRR f x / Real.cosh (meridianR x) ^ 2 -
        Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 * profileDR f x +
        3 * profileDR f x /
          (Real.sinh (meridianR x) * Real.cosh (meridianR x)) +
        profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x := by
  simp [computationalElliptic, axisymmetricLaplacian, computationalAxisymmetricDifferential,
    computationalDrOverR, hx]
  ring

/-- At `ρ = 0`, the radial part of `computationalElliptic` is `4 fρρ`. -/
theorem computationalElliptic_of_eq_zero (f : (ℝ^2 → ℝ)) (x : (ℝ^2))
    (hx : meridianR x = 0) :
    computationalElliptic f x =
      4 * profileDRR f x +
        profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x := by
  simp [computationalElliptic, axisymmetricLaplacian, computationalAxisymmetricDifferential,
    computationalDrOverR, hx]
  ring

/--
The removable radial quotient under explicit differentiability hypotheses.

If `g(0) = 0` and `g` is differentiable at zero with derivative `a`, then
`g(ρ)/(sinh ρ cosh ρ) → a`. Applied to `g = fρ`, radial evenness supplies
`g(0) = 0` and differentiability of the first derivative supplies `a = fρρ(0)`.
-/
theorem tendsto_div_sinh_mul_cosh {g : ℝ → ℝ} {a : ℝ}
    (hg0 : g 0 = 0) (hg : HasDerivAt g a 0) :
    Filter.Tendsto (fun ρ ↦ g ρ / (Real.sinh ρ * Real.cosh ρ))
      (𝓝[≠] 0) (𝓝 a) := by
  have hden : HasDerivAt (fun ρ : ℝ ↦ Real.sinh ρ * Real.cosh ρ) 1 0 := by
    cas
  have hratio := hg.tendsto_slope_zero.div hden.tendsto_slope_zero (by norm_num)
  simp only [zero_add, hg0, sub_zero, Real.sinh_zero, Real.cosh_zero,
    zero_mul, smul_eq_mul, ← div_eq_inv_mul, div_one] at hratio
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  change (g ρ / ρ) / ((Real.sinh ρ * Real.cosh ρ) / ρ) =
    g ρ / (Real.sinh ρ * Real.cosh ρ)
  exact div_div_div_cancel_right₀ hρ _ _

/-- The removable radial quotient for the derivative of an even profile. -/
theorem tendsto_deriv_div_sinh_mul_cosh_of_even {f : ℝ → ℝ} {a : ℝ}
    (heven : Function.Even f) (hsecond : HasDerivAt (deriv f) a 0) :
    Filter.Tendsto (fun ρ ↦ deriv f ρ / (Real.sinh ρ * Real.cosh ρ))
      (𝓝[≠] 0) (𝓝 a) :=
  tendsto_div_sinh_mul_cosh (PDE.Analysis.Radial.deriv_zero_of_even heven) hsecond

/-- The regularized transformed quotient agrees with the physical one after pullback. -/
theorem computationalDrOverR_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    computationalDrOverR (computationalPullback f) x =
      classicalAxisymmetricDifferential.dROverR f
        (computationalCoordinateMap x) := by
  by_cases hx : meridianR x = 0
  · rw [classical_dROverR_of_eq_zero f (computationalCoordinateMap x) (by simp [hx])]
    simp only [computationalDrOverR, hx, ite_eq_left]
    simpa [hx, classicalAxisymmetricDifferential] using
      profileDRR_computationalPullback hf x
  · rw [classical_dROverR_of_ne_zero f (computationalCoordinateMap x)
      (by simpa using (Real.sinh_ne_zero.mpr hx))]
    simp only [computationalDrOverR, hx, ite_false]
    rw [profileDR_computationalPullback (hf.of_le (by norm_num)) x]
    simp only [meridianR_computationalCoordinateMap]
    field_simp [(Real.sinh_ne_zero.mpr hx), (Real.cosh_pos _).ne']
    simp [classicalAxisymmetricDifferential]

/-- `computationalElliptic` is the physical axisymmetric elliptic operator after pullback. -/
theorem computationalElliptic_computationalPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    computationalElliptic (computationalPullback f) x =
      axisymmetricLaplacian classicalAxisymmetricDifferential f
        (computationalCoordinateMap x) := by
  unfold computationalElliptic axisymmetricLaplacian
  dsimp only [computationalAxisymmetricDifferential]
  rw [← profileDRR_at_computationalCoordinateMap hf x]
  rw [← profileDZZ_at_computationalCoordinateMap hf x]
  rw [computationalDrOverR_computationalPullback hf x]
  rfl

end PDE.CoordinateSystems
