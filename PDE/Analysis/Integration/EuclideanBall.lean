/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
import PDE.Analysis.Integration.Polar

/-!
# Integration on Euclidean balls and spheres

We define the sphere integral, the ball integral, and the corresponding averages over
Euclidean balls and spheres in `ℝ^n`, and prove the coarea formula reducing a ball integral
to a radial integral of sphere integrals. These are the quantities behind the mean-value
formulas for harmonic functions.

The sphere integral `sphereIntegral n u x r` is `|r|^(n-1) ∫_{S} u (x + r ω) dσ(ω)`,
where `S` is the unit sphere and `σ = volume.toSphere` is Mathlib's fixed angular
measure on it; the factor `|r|^(n-1)` is the Jacobian making this the surface
integral over `∂B(x, r)`. The coarea formula is derived from
`PDE.Analysis.integral_polar_addHaar_iterated`; translation invariance of
Lebesgue measure then gives the formula for an arbitrary center.

Sphere and ball integrals are total in the radius. A negative-radius ball is
empty, while `sphereIntegral` is a signed radial parametrization used by the
coarea calculus. Averages agree with the geometric quotient at positive
radius, use the center value at radius zero, and are zero at negative radius.
Geometric theorems about their normalizing constants assume positive ambient
dimension where needed.

## Main results

* `sphereIntegral`, `ballIntegral`, `sphereAverage`, `ballAverage`: the basic
  quantities, with `unitSphereAverage` as the Jacobian-free form.
* `sphereAverage_eq_unitSphereAverage`: at positive radius the sphere average
  is the average against the fixed unit-sphere measure.
* `sphereIntegral_add`, `sphereAverage_add`: linearity for integrable
  parametrized sphere data.
* `sphereIntegral_comp_add_left`, `ballIntegral_comp_add_left`: moving the
  center by translation.
* `coarea_formula_ball`: `∫_{B(x,r)} u = ∫_0^r (∫_{∂B(x,ρ)} u dS) dρ` for `u`
  integrable on the ball.
* `coarea_formula_annulus`: the same identity on `B(x,b) \ B(x,a)`.

`coarea_formula_ball` is Evans's polar coordinates formula (App. C.3, Theorem 4(i)) on a ball,
in the form used in step 2 of his proof of the mean-value formulas (§2.2.2, Theorem 2). It is
the case `u(x) = |x - x₀|` of his coarea formula, Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 2 and step 2 of its proof, pp. 25-26,
  and App. C.3, Theorems 4 and 5, pp. 712-713. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PDE.Analysis

/-- Surface integral over the sphere centered at `x` with radius `r`.

The factor `|r| ^ (n - 1)` is the radial Jacobian for the fixed unit-sphere
measure. -/
def sphereIntegral (n : ℕ)
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) : ℝ :=
  |r| ^ (n - 1) *
    ∫ ω, u (x + r • (ω : ℝ^n))
      ∂((volume : Measure (ℝ^n)).toSphere)

/-- A sphere integral is nonnegative when its integrand is nonnegative on the sphere. -/
theorem sphereIntegral_nonneg {n : ℕ}
    {u : ℝ^n → ℝ} {x : ℝ^n} {r : ℝ}
    (hu : ∀ y ∈ Metric.sphere x |r|, 0 ≤ u y) :
    0 ≤ sphereIntegral n u x r := by
  unfold sphereIntegral
  apply mul_nonneg (pow_nonneg (abs_nonneg r) _)
  apply integral_nonneg
  intro ω
  apply hu
  have hω : ‖(ω : ℝ^n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  rw [Metric.mem_sphere]
  simp [dist_eq_norm, norm_smul, hω]

/-- A sphere integral is nonpositive when its integrand is nonpositive on the sphere. -/
theorem sphereIntegral_nonpos {n : ℕ}
    {u : ℝ^n → ℝ} {x : ℝ^n} {r : ℝ}
    (hu : ∀ y ∈ Metric.sphere x |r|, u y ≤ 0) :
    sphereIntegral n u x r ≤ 0 := by
  unfold sphereIntegral
  apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (abs_nonneg r) _)
  apply integral_nonpos
  intro ω
  apply hu
  have hω : ‖(ω : ℝ^n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  rw [Metric.mem_sphere]
  simp [dist_eq_norm, norm_smul, hω]

/-- Lebesgue integral over the open ball centered at `x` with radius `r`. -/
def ballIntegral (n : ℕ)
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) : ℝ :=
  ∫ y in Metric.ball x r, u y ∂(volume : Measure (ℝ^n))

/-- Average over the sphere centered at `x` with radius `r` in positive
dimension. It is the geometric quotient for `0 < r`, the value `u x` for `r = 0` (the limit
of the averages when `u` is continuous at `x`), and zero for the empty negative-radius sphere. -/
def sphereAverage (n : ℕ)
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) : ℝ :=
  if 0 < r then sphereIntegral n u x r / sphereArea n r
  else if r = 0 then u x else 0

/-- Average of `u` over the sphere of radius `r` about `x`, computed against the fixed
unit-sphere measure, so that no radial Jacobian appears. -/
def unitSphereAverage (n : ℕ)
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) : ℝ :=
  (∫ ω, u (x + r • (ω : ℝ^n))
      ∂((volume : Measure (ℝ^n)).toSphere)) / unitSphereArea n

/-- Average over the open ball centered at `x` with radius `r` in positive
dimension. It is the geometric quotient for `0 < r`, the value `u x` for `r = 0` (the limit
of the averages when `u` is continuous at `x`), and zero for the empty negative-radius ball. -/
def ballAverage (n : ℕ)
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) : ℝ :=
  if 0 < r then ballIntegral n u x r / ballVolume n r
  else if r = 0 then u x else 0

/-- At positive radius, the spherical average is its geometric quotient. -/
theorem sphereAverage_of_pos {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    sphereAverage n u x r = sphereIntegral n u x r / sphereArea n r := by
  simp [sphereAverage, hr]

/-- The continuously extended spherical average at radius zero is the center value. -/
@[simp]
theorem sphereAverage_zero {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) :
    sphereAverage n u x 0 = u x := by
  simp [sphereAverage]

/-- The average over a negative-radius sphere, hence over the empty set, is zero. -/
theorem sphereAverage_of_neg {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : r < 0) :
    sphereAverage n u x r = 0 := by
  simp [sphereAverage, hr.not_gt, hr.ne]

/-- At positive radius, the ball average is its geometric quotient. -/
theorem ballAverage_of_pos {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ballAverage n u x r = ballIntegral n u x r / ballVolume n r := by
  simp [ballAverage, hr]

/-- The continuously extended ball average at radius zero is the center value. -/
@[simp]
theorem ballAverage_zero {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) :
    ballAverage n u x 0 = u x := by
  simp [ballAverage]

/-- The average over a negative-radius ball, hence over the empty set, is zero. -/
theorem ballAverage_of_neg {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : r < 0) :
    ballAverage n u x r = 0 := by
  simp [ballAverage, hr.not_gt, hr.ne]

/-- A sphere integral depends only on the values of the integrand on that sphere. -/
theorem sphereIntegral_congr_on_sphere {n : ℕ}
    {u v : ℝ^n → ℝ} {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (h : Set.EqOn u v (Metric.sphere x r)) :
    sphereIntegral n u x r = sphereIntegral n v x r := by
  classical
  unfold sphereIntegral
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ h (by
    have hω : ‖(ω : ℝ^n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    simp [Metric.sphere, norm_smul, hω, abs_of_pos hr])

/-- A positive-radius sphere average depends only on the boundary values. -/
theorem sphereAverage_congr_on_sphere {n : ℕ}
    {u v : ℝ^n → ℝ} {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (h : Set.EqOn u v (Metric.sphere x r)) :
    sphereAverage n u x r = sphereAverage n v x r := by
  simp only [sphereAverage, ite_eq_left hr]
  rw [sphereIntegral_congr_on_sphere hr h]

/-- Translating an integrand converts a sphere centered at zero to one centered at `x`. -/
theorem sphereIntegral_comp_add_left {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    sphereIntegral n (fun y ↦ u (x + y)) 0 r = sphereIntegral n u x r := by
  unfold sphereIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  simp

/-- Translating an integrand converts a sphere average centered at zero to one centered at `x`. -/
theorem sphereAverage_comp_add_left {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    sphereAverage n (fun y ↦ u (x + y)) 0 r = sphereAverage n u x r := by
  by_cases hr : 0 < r
  · simp [sphereAverage, hr, sphereIntegral_comp_add_left]
  · by_cases hr0 : r = 0
    · simp [sphereAverage, hr0]
    · simp [sphereAverage, hr, hr0]

/-- Translating an integrand converts a ball centered at zero to one centered at `x`. -/
theorem ballIntegral_comp_add_left {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    ballIntegral n (fun y ↦ u (x + y)) 0 r = ballIntegral n u x r := by
  let τ : ℝ^n → ℝ^n := fun y ↦ x + y
  have hτ : MeasurePreserving τ (volume : Measure (ℝ^n)) volume :=
    measurePreserving_add_left (volume : Measure (ℝ^n)) x
  have hτmeas : MeasurableEmbedding τ :=
    (Homeomorph.addLeft x).measurableEmbedding
  have hpre : τ ⁻¹' Metric.ball x r = Metric.ball (0 : ℝ^n) r := by
    ext y
    simp [τ, Metric.mem_ball, dist_eq_norm]
  unfold ballIntegral
  simpa [hpre, τ] using
    hτ.setIntegral_preimage_emb hτmeas u (Metric.ball x r)

/-- Positive-radius sphere averages equal averages over the fixed unit-sphere measure. -/
theorem sphereAverage_eq_unitSphereAverage {n : ℕ} [Fact (0 < n)]
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) (hr : 0 < r) :
    sphereAverage n u x r = unitSphereAverage n u x r := by
  have hpow : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  have hunit : unitSphereArea n ≠ 0 := ne_of_gt unitSphereArea_pos
  simp only [sphereAverage, ite_eq_left hr, sphereIntegral, sphereArea,
    unitSphereAverage, abs_of_pos hr]
  field_simp

/-- The sphere integral of constant data is the constant times the sphere area. -/
theorem sphereIntegral_const {n : ℕ}
    (c : ℝ) (x : ℝ^n) (r : ℝ) :
    sphereIntegral n (fun _ : ℝ^n ↦ c) x r = c * sphereArea n r := by
  classical
  simp [sphereIntegral, sphereArea, unitSphereArea, integral_const,
    measureReal_def, mul_left_comm, mul_comm]

/-- Sphere integration is additive for integrable parametrized data. -/
theorem sphereIntegral_add {n : ℕ}
    (u v : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ)
    (hu : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ u (x + r • (ω : ℝ^n)))
      ((volume : Measure (ℝ^n)).toSphere))
    (hv : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ v (x + r • (ω : ℝ^n)))
      ((volume : Measure (ℝ^n)).toSphere)) :
    sphereIntegral n (fun y ↦ u y + v y) x r =
      sphereIntegral n u x r + sphereIntegral n v x r := by
  unfold sphereIntegral
  rw [integral_add hu hv]
  ring

/-- Sphere averaging is additive for integrable parametrized data at positive radius. -/
theorem sphereAverage_add {n : ℕ}
    (u v : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    (hu : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ u (x + r • (ω : ℝ^n)))
      ((volume : Measure (ℝ^n)).toSphere))
    (hv : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ v (x + r • (ω : ℝ^n)))
      ((volume : Measure (ℝ^n)).toSphere)) :
    sphereAverage n (fun y ↦ u y + v y) x r =
      sphereAverage n u x r + sphereAverage n v x r := by
  simp only [sphereAverage, ite_eq_left hr]
  rw [sphereIntegral_add u v x r hu hv]
  ring

/-- A constant factor can be pulled through sphere integration. -/
theorem sphereIntegral_const_mul {n : ℕ}
    (c : ℝ) (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    sphereIntegral n (fun y ↦ c * u y) x r =
      c * sphereIntegral n u x r := by
  unfold sphereIntegral
  rw [integral_const_mul]
  ring

/-- Sphere integration commutes with negation. -/
theorem sphereIntegral_neg {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    sphereIntegral n (-u) x r = -sphereIntegral n u x r := by
  simp only [sphereIntegral, Pi.neg_apply, integral_neg]
  ring

/-- The sphere average of constant data is constant at every positive radius. -/
theorem sphereAverage_const {n : ℕ} [Fact (0 < n)]
    (c : ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    sphereAverage n (fun _ : ℝ^n ↦ c) x r = c := by
  have harea : sphereArea n r ≠ 0 := sphereArea_ne_zero r hr
  simp [sphereAverage, hr, sphereIntegral_const, harea]

/-- Sphere averaging commutes with negation at every positive radius. -/
theorem sphereAverage_neg {n : ℕ}
    (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    sphereAverage n (-u) x r = -sphereAverage n u x r := by
  simp [sphereAverage, hr, sphereIntegral_neg, neg_div]

/-- Coarea formula for an integrable function on a Euclidean ball. -/
theorem coarea_formula_ball {n : ℕ} [Fact (0 < n)]
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ)
    (hu : IntegrableOn u (Metric.ball x r) (volume : Measure (ℝ^n))) :
    ballIntegral n u x r =
      ∫ ρ in Set.Icc 0 r, sphereIntegral n u x ρ := by
  classical
  have : Nontrivial (ℝ^n) := by
    have hfinrank : 0 < Module.finrank ℝ (ℝ^n) := by
      simpa using (Fact.out : 0 < n)
    exact Module.nontrivial_of_finrank_pos (R := ℝ) hfinrank
  have : NullSingletonClass (volume : Measure (ℝ^n)) := by
    infer_instance
  let τ : ℝ^n → ℝ^n := fun y ↦ x + y
  have hτ : MeasurePreserving τ (volume : Measure (ℝ^n)) volume :=
    measurePreserving_add_left (volume : Measure (ℝ^n)) x
  have hτmeas : MeasurableEmbedding τ :=
    (Homeomorph.addLeft x).measurableEmbedding
  have hpre : τ ⁻¹' Metric.ball x r = Metric.ball (0 : ℝ^n) r := by
    ext y
    simp [τ, Metric.mem_ball, dist_eq_norm]
  have hu0 :
      IntegrableOn (fun y : ℝ^n ↦ u (x + y))
        (Metric.ball (0 : ℝ^n) r) volume := by
    rw [show (fun y : ℝ^n ↦ u (x + y)) = u ∘ τ by rfl]
    simpa [τ, hpre] using
      (hτ.integrableOn_comp_preimage hτmeas (f := u)
        (s := Metric.ball x r)).2 hu
  let g : ℝ^n → ℝ :=
    (Metric.ball (0 : ℝ^n) r).indicator (fun y ↦ u (x + y))
  have hg : Integrable g volume := by
    exact (integrable_indicator_iff measurableSet_ball).2 hu0
  have hpolar :=
    integral_polar_addHaar_iterated (volume : Measure (ℝ^n)) g hg
  have hball :
      ballIntegral n u x r = ∫ y : ℝ^n, g y := by
    rw [← ballIntegral_comp_add_left u x r]
    unfold ballIntegral g
    exact (integral_indicator measurableSet_ball).symm
  rw [hball, hpolar]
  have hradial :
      Set.EqOn
        (fun ρ : ℝ ↦
          ρ ^ (n - 1) •
            ∫ ω : Metric.sphere (0 : ℝ^n) 1,
              g (ρ • (ω : ℝ^n))
                ∂((volume : Measure (ℝ^n)).toSphere))
        (fun ρ ↦ if ρ < r then sphereIntegral n u x ρ else 0)
        (Set.Ioi 0) := by
    intro ρ hρ0
    change 0 < ρ at hρ0
    by_cases hρr : ρ < r
    · have hmem (ω : Metric.sphere (0 : ℝ^n) 1) :
          ρ • (ω : ℝ^n) ∈ Metric.ball (0 : ℝ^n) r := by
        rw [Metric.mem_ball]
        have hω : ‖(ω : ℝ^n)‖ = 1 :=
          mem_sphere_zero_iff_norm.mp ω.property
        simpa [dist_eq_norm, norm_smul, hω, abs_of_pos hρ0] using hρr
      simp only [hρr, ite_true, sphereIntegral, abs_of_pos hρ0, smul_eq_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      simp [g, Set.indicator_of_mem (hmem ω)]
    · have hnotmem (ω : Metric.sphere (0 : ℝ^n) 1) :
          ρ • (ω : ℝ^n) ∉ Metric.ball (0 : ℝ^n) r := by
        rw [Metric.mem_ball]
        have hω : ‖(ω : ℝ^n)‖ = 1 :=
          mem_sphere_zero_iff_norm.mp ω.property
        simpa [dist_eq_norm, norm_smul, hω, abs_of_pos hρ0] using hρr
      simp [hρr, g, Set.indicator_of_notMem, hnotmem]
  simp only [show Module.finrank ℝ (ℝ^n) = n by simp] at hpolar ⊢
  rw [setIntegral_congr_fun measurableSet_Ioi hradial]
  have hindicator :
      (fun ρ : ℝ ↦ if ρ < r then sphereIntegral n u x ρ else 0) =
        (Set.Iio r).indicator (sphereIntegral n u x) := by
    funext ρ
    by_cases hρ : ρ < r <;> simp [hρ]
  rw [hindicator, setIntegral_indicator measurableSet_Iio]
  simp only [Set.Ioi_inter_Iio]
  exact setIntegral_congr_set Ioo_ae_eq_Icc

/-- Coarea formula on a concentric annulus. -/
theorem coarea_formula_annulus {n : ℕ} [Fact (0 < n)]
    (u : ℝ^n → ℝ) (x : ℝ^n) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : IntegrableOn u (Metric.ball x b) (volume : Measure (ℝ^n)))
    (hρ : IntegrableOn (fun ρ ↦ sphereIntegral n u x ρ) (Set.Icc 0 b)) :
    (∫ y in Metric.ball x b \ Metric.ball x a, u y
        ∂(volume : Measure (ℝ^n))) =
      ∫ ρ in Set.Icc a b, sphereIntegral n u x ρ := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hball : Metric.ball x a ⊆ Metric.ball x b :=
    Metric.ball_subset_ball hab
  have hua : IntegrableOn u (Metric.ball x a) volume :=
    hu.mono_set hball
  rw [setIntegral_sdiff measurableSet_ball hu hball]
  change ballIntegral n u x b - ballIntegral n u x a = _
  rw [coarea_formula_ball u x b hu,
    coarea_formula_ball u x a hua]
  have hρ0a : IntervalIntegrable (fun ρ ↦ sphereIntegral n u x ρ)
      volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).2 <|
      hρ.mono_set (Set.Icc_subset_Icc_right hab)
  have hρab : IntervalIntegrable (fun ρ ↦ sphereIntegral n u x ρ)
      volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
      hρ.mono_set (Set.Icc_subset_Icc_left ha)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hρ0a hρab
  rw [intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hb0] at hadd
  rw [setIntegral_congr_set Ioc_ae_eq_Icc.symm,
    setIntegral_congr_set Ioc_ae_eq_Icc.symm,
    setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  linarith

end PDE.Analysis
