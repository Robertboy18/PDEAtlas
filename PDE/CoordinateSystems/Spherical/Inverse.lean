/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric
public import PDE.CoordinateSystems.Spherical
public import PDE.FDeriv.Axisymmetric.Spherical
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import PDE.Analysis.Calculus.Radial.AngularLipschitz

/-!
# The inverse spherical chart

The polar angle `arccos (x₃ / ‖x‖)` and the azimuthal angle `arg (x₁ + i x₂)` are total angle
functions on `ℝ^3`, with values in `[0, π]` and `(-π, π]`. Both are measurable on all of space,
with the values of real division at the origin and of the complex argument on the symmetry axis.
For `r > 0` the polar cosine of `point r θ φ` is `cos θ`, so the Cartesian fields
`meridionalField F G S T` and `azimuthalField H A` become the corresponding combinations of the
spherical frames there.

The polar cosine lies in `[-1, 1]`, so every polynomial in it is bounded, and the direction
rotated by a quarter turn about the axis has norm at most one.

The cosine of the polar angle is the polar cosine and its sine is `ρ / ‖x‖`, with `ρ` the
cylindrical radius; off the axis the cosine and sine of the azimuth are `x₁ / ρ` and `x₂ / ρ`.
Every nonzero point, including the points of the axis, is the spherical point of its radius
and its two angles. Off the axis the polar angle lies in `(0, π)` and is smooth.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open PDE.FDeriv.Spherical Polynomial Metric NormedSpace

/-- The polar angle `arccos (x₃ / ‖x‖)`, with the value `π / 2` of real division at zero. -/
def polarAngle (x : ℝ^3) : ℝ := Real.arccos (x 2 / ‖x‖)

/-- The azimuthal angle `arg (x₁ + i x₂)`, with the complex argument's value on the axis. -/
def azimuthalAngle (x : ℝ^3) : ℝ := Complex.arg ⟨x 0, x 1⟩

/-- The polar angle is measurable on all of space. -/
theorem measurable_polarAngle : Measurable polarAngle := by
  exact Real.measurable_arccos.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable.div measurable_norm)

/-- The azimuthal angle is measurable, including its branch cut and the axis. -/
theorem measurable_azimuthalAngle : Measurable azimuthalAngle := by
  apply Complex.measurable_arg.comp
  change Measurable (fun x : ℝ^3 ↦ Complex.mk (x 0) (x 1))
  have h : (fun x : ℝ^3 ↦ Complex.mk (x 0) (x 1)) =
      (fun x : ℝ^3 ↦ (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) := by
    funext x
    apply Complex.ext <;> simp
  rw [h]
  exact (Complex.measurable_ofReal.comp
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.measurable).add
      ((Complex.measurable_ofReal.comp
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous.measurable).mul_const Complex.I)

/-- The polar cosine of a spherical point is the cosine of its polar angle. -/
theorem polarCosine_point {r : ℝ} (hr : 0 < r) (θ φ : ℝ) :
    polarCosine (point r θ φ) = Real.cos θ := by
  rw [polarCosine, norm_point hr]
  change r * Real.cos θ / r = Real.cos θ
  exact mul_div_cancel_left₀ _ hr.ne'

/-- The Cartesian meridional formula gives the spherical radial and polar frames,
including the limiting frame values on the symmetry axis. -/
theorem meridionalField_point {r : ℝ} (hr : 0 < r) (θ φ : ℝ) (F G S T : ℝ → ℝ) :
    meridionalField F G S T (point r θ φ) =
      (F r * S (Real.cos θ)) • radialFrame θ φ +
      (G r * T (Real.cos θ) * Real.sin θ) • polarFrame θ φ := by
  rw [meridionalField, norm_point hr, polarCosine_point hr]
  ext i
  fin_cases i <;> simp [point, radialFrame, polarFrame]
  all_goals field_simp
  all_goals
    have htrig := congrArg (fun t ↦ G r * T (Real.cos θ) * t)
      (Real.sin_sq_add_cos_sq θ)
    nlinarith only [htrig]

/-- The Cartesian azimuthal formula gives the spherical azimuthal frame. -/
theorem azimuthalField_point {r : ℝ} (hr : 0 < r) (θ φ : ℝ) (H A : ℝ → ℝ) :
    azimuthalField H A (point r θ φ) =
      (H r * A (Real.cos θ) * Real.sin θ) • azimuthalFrame φ := by
  simp only [azimuthalField, norm_point hr, polarCosine_point hr]
  ext i
  fin_cases i <;> simp [point, radialFrame, azimuthalFrame]
  all_goals field_simp

/-- The polar cosine takes values in `[-1, 1]`, with the value `0` at the origin. -/
theorem abs_polarCosine_le_one (x : ℝ^3) : |polarCosine x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, polarCosine]
  · rw [polarCosine, abs_div, abs_of_nonneg (norm_nonneg _)]
    exact (div_le_one (norm_pos_iff.mpr hx)).mpr (PiLp.norm_apply_le x 2)

/-- The polar angle of a spherical point of positive radius and polar angle in `[0, π]`. -/
theorem polarAngle_point {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) (φ : ℝ) :
    polarAngle (point r θ φ) = θ := by
  change Real.arccos (polarCosine (point r θ φ)) = θ
  rw [polarCosine_point hr, Real.arccos_cos hθ.1 hθ.2]

/-- The polar angle of the radial vector at polar angle `θ ∈ [0, π]`. -/
theorem polarAngle_radialFrame {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) (φ : ℝ) :
    polarAngle (radialFrame θ φ) = θ := by
  simpa [point] using polarAngle_point one_pos hθ φ

/-- The cosine of the polar angle is the polar cosine. -/
theorem cos_polarAngle (x : ℝ^3) : Real.cos (polarAngle x) = polarCosine x := by
  have h := abs_le.mp (abs_polarCosine_le_one x)
  exact Real.cos_arccos h.1 h.2

private theorem norm_sq_eq_cylindricalRadius_sq (x : ℝ^3) :
    ‖x‖ ^ 2 = cylindricalRadius x ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, cylindricalRadius_sq,
    cylindricalRadiusSq]

/-- The sine of the polar angle is the cylindrical radius over the radius. -/
theorem sin_polarAngle {x : ℝ^3} (hx : x ≠ 0) :
    Real.sin (polarAngle x) = cylindricalRadius x / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [polarAngle, Real.sin_arccos]
  have h : 1 - (x 2 / ‖x‖) ^ 2 = (cylindricalRadius x / ‖x‖) ^ 2 := by
    have := norm_sq_eq_cylindricalRadius_sq x
    field_simp
    linarith
  rw [h, Real.sqrt_sq (div_nonneg (cylindricalRadius_nonneg x) hn.le)]

private theorem norm_complex_mk (a b : ℝ) : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_mk, sq, sq]

/-- The cosine of the azimuth off the axis is the first coordinate over the cylindrical
radius. -/
theorem cos_azimuthalAngle {x : ℝ^3} (hx : x ∉ symmetryAxis) :
    Real.cos (azimuthalAngle x) = x 0 / cylindricalRadius x := by
  have hne : (⟨x 0, x 1⟩ : ℂ) ≠ 0 := by
    intro h
    exact hx ((mem_symmetryAxis_iff x).mpr ⟨congrArg Complex.re h, congrArg Complex.im h⟩)
  rw [azimuthalAngle, Complex.cos_arg hne, norm_complex_mk]
  rfl

/-- The sine of the azimuth is the second coordinate over the cylindrical radius. -/
theorem sin_azimuthalAngle (x : ℝ^3) :
    Real.sin (azimuthalAngle x) = x 1 / cylindricalRadius x := by
  rw [azimuthalAngle, Complex.sin_arg, norm_complex_mk]
  rfl

private theorem abs_polarCosine_lt_one {x : ℝ^3} (hx : x ∉ symmetryAxis) :
    |polarCosine x| < 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr (ne_zero_of_notMem_symmetryAxis hx)
  have hρ := cylindricalRadius_pos hx
  rw [polarCosine, abs_div, abs_of_pos hn, div_lt_one hn]
  apply abs_lt_of_sq_lt_sq _ hn.le
  nlinarith [norm_sq_eq_cylindricalRadius_sq x]

/-- The polar angle of a point off the symmetry axis lies strictly between `0` and `π`. -/
theorem polarAngle_mem_Ioo {x : ℝ^3} (hx : x ∉ symmetryAxis) :
    polarAngle x ∈ Set.Ioo 0 Real.pi := by
  have hlt := abs_lt.mp (abs_polarCosine_lt_one hx)
  exact ⟨Real.arccos_pos.mpr hlt.2, Real.arccos_lt_pi.mpr hlt.1⟩

/-- The polar angle is smooth off the symmetry axis. -/
theorem contDiffAt_polarAngle {n : WithTop ℕ∞} {x : ℝ^3} (hx : x ∉ symmetryAxis) :
    ContDiffAt ℝ n polarAngle x := by
  have hx0 := ne_zero_of_notMem_symmetryAxis hx
  have hlt := abs_lt.mp (abs_polarCosine_lt_one hx)
  have hc : ContDiffAt ℝ n (fun y : ℝ^3 ↦ y 2 / ‖y‖) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.contDiffAt.div (contDiffAt_norm ℝ hx0)
      (norm_ne_zero_iff.mpr hx0)
  exact (Real.contDiffAt_arccos hlt.1.ne' hlt.2.ne).comp x hc

/-- The polar angle is continuous at every nonzero point, the symmetry axis included. -/
theorem continuousAt_polarAngle {x : ℝ^3} (hx : x ≠ 0) : ContinuousAt polarAngle x :=
  Real.continuous_arccos.continuousAt.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt.div
      continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx))

private theorem cylindricalRadius_mul_cos_azimuthalAngle (x : ℝ^3) :
    cylindricalRadius x * Real.cos (azimuthalAngle x) = x 0 := by
  by_cases hx : x ∈ symmetryAxis
  · have h := (mem_symmetryAxis_iff x).mp hx
    rw [(cylindricalRadius_eq_zero_iff x).mpr h, zero_mul, h.1]
  · rw [cos_azimuthalAngle hx]
    field_simp [(cylindricalRadius_pos hx).ne']

private theorem cylindricalRadius_mul_sin_azimuthalAngle (x : ℝ^3) :
    cylindricalRadius x * Real.sin (azimuthalAngle x) = x 1 := by
  by_cases hx : x ∈ symmetryAxis
  · have h := (mem_symmetryAxis_iff x).mp hx
    rw [(cylindricalRadius_eq_zero_iff x).mpr h, zero_mul, h.2]
  · rw [sin_azimuthalAngle]
    field_simp [(cylindricalRadius_pos hx).ne']

/-- Every nonzero point is the spherical point of its radius and angles, including the points
of the symmetry axis, where the azimuth is `0`. -/
theorem point_norm_polarAngle_azimuthalAngle {x : ℝ^3} (hx : x ≠ 0) :
    point ‖x‖ (polarAngle x) (azimuthalAngle x) = x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h0 := cylindricalRadius_mul_cos_azimuthalAngle x
  have h1 := cylindricalRadius_mul_sin_azimuthalAngle x
  ext i
  fin_cases i <;> simp only [point, radialFrame, cos_polarAngle, sin_polarAngle hx,
    polarCosine] <;> simp <;> field_simp
  · linear_combination h0
  · linear_combination h1

/-- A polynomial in the polar cosine is bounded on all of space. -/
theorem exists_norm_eval_polarCosine_le (P : ℝ[X]) :
    ∃ C > 0, ∀ x : ℝ^3, ‖P.eval (polarCosine x)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).image P.continuous).isBounded
      |>.exists_pos_norm_le
  refine ⟨C, hC, fun x ↦ hbound _ ?_⟩
  apply Set.mem_image_of_mem
  exact abs_le.mp (abs_polarCosine_le_one x)

/-- The meridional field separates its radial factors from fields of the direction. -/
theorem meridionalField_split (F G S T : ℝ → ℝ) (x : ℝ^3) :
    meridionalField F G S T x =
      F ‖x‖ • (S (polarCosine x) • (‖x‖⁻¹ • x)) +
      G ‖x‖ • ((T (polarCosine x) * polarCosine x) • (‖x‖⁻¹ • x) -
        T (polarCosine x) • EuclideanSpace.single (2 : Fin 3) 1) := by
  ext i
  simp only [meridionalField, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-- The azimuthal field is its radial factor times a field of the direction. -/
theorem azimuthalField_split (H A : ℝ → ℝ) (x : ℝ^3) :
    azimuthalField H A x = H ‖x‖ • (A (polarCosine x) •
      WithLp.toLp 2 ![-((‖x‖⁻¹ • x) 1), (‖x‖⁻¹ • x) 0, 0]) := by
  ext i
  fin_cases i <;> simp [azimuthalField] <;> ring

/-- The direction rotated by a quarter turn about the axis has norm at most one. -/
theorem norm_rotated_normalized_le_one (x : ℝ^3) :
    ‖(WithLp.toLp 2 ![-((‖x‖⁻¹ • x) 1), (‖x‖⁻¹ • x) 0, 0] : ℝ^3)‖ ≤ 1 := by
  have hnorm : ‖‖x‖⁻¹ • x‖ ≤ 1 := PDE.Analysis.Radial.norm_normalize_le_one x
  have hsquares := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hnorm
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsquares
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.smul_apply, smul_eq_mul] at hsquares ⊢
  dsimp
  nlinarith only [hsquares, sq_nonneg ((‖x‖⁻¹ • x) 2)]

end PDE.CoordinateSystems.Spherical
