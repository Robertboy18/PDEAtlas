/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscous.InitialValue
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Quadratic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.Parabolic.Heat.Kernel.Integrability
import PDE.Parabolic.Heat.InfinitePropagation
import CAS.ExactTactic

/-!
# Gaussian Laplace bounds for the Cole–Hopf field

At time one the exponent is the quadratic Hopf–Lax cost divided by `2ν`.
A Gaussian tilt retains an integrable upper bound on the exponential integral.
A ball around an attained minimizing footpoint supplies a positive lower bound.
Taking logarithms reverses these two bounds for the Cole–Hopf potential.

Both estimates are uniform in the spatial point. The small tilt and ball radius
are chosen before the viscosity; their logarithmic constants are therefore fixed.

The resulting limit `-2ν log ∫ exp (-K/(2ν)) → min K` is Laplace's method in logarithmic form.
Evans's Lemma (Asymptotics) in §4.5.2 is the related limit (24) of a ratio of such integrals,
which he applies to the viscous Burgers equation in Example 2. Only the minimum value enters
the logarithmic limit, so the minimizer need not be unique.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.2, Example 2 and Lemma (Asymptotics), equations
  (20)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi.ColeHopf

open MeasureTheory Set Metric

variable {n : ℕ}

/-- The exponential datum is bounded by `exp (M / (2ν))`. -/
private theorem exp_datum_le {ν M : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ} (hgb : ∀ y, |g y| ≤ M)
    (y : ℝ^n) : Real.exp (-g y / (2 * ν)) ≤ Real.exp (M / (2 * ν)) := by
  gcongr
  linarith [(abs_le.mp (hgb y)).1]

/-- Bounded potentials give a integrable exponential-weighted Gaussian,
even though the datum itself need not be integrable on the whole space. -/
private theorem exponential_heat_integrable {ν M : ℝ} (hν : 0 < ν)
    {g : ℝ^n → ℝ} (hg : Continuous g) (hgb : ∀ y, |g y| ≤ M) (x : ℝ^n) :
    Integrable (fun y ↦ HeatEquation.fundamentalSolutionHeat (x - y) ν *
      Real.exp (-g y / (2 * ν))) :=
  ((HeatEquation.fundamentalSolutionHeat_integrable ν hν).comp_sub_left x).mul_bdd
    (c := Real.exp (M / (2 * ν)))
    (Real.continuous_exp.comp (hg.neg.div_const (2 * ν))).aestronglyMeasurable
    (ae_of_all _ fun y ↦ by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using exp_datum_le hν hgb y)

/-- The positive exponential datum prevents the logarithm from reaching its singularity. -/
private theorem exponential_heat_pos {ν M : ℝ} (hν : 0 < ν)
    {g : ℝ^n → ℝ} (hg : Continuous g) (hgb : ∀ y, |g y| ≤ M) (x : ℝ^n) :
    0 < HeatEquation.initialValueSolution (fun y ↦ Real.exp (-g y / (2 * ν))) x ν :=
  HeatEquation.initialValueSolution_pos_of_nonneg_of_exists_pos _
    (Real.continuous_exp.comp (hg.neg.div_const (2 * ν)))
    ⟨Real.exp (M / (2 * ν)), fun y ↦ (Real.abs_exp _).trans_le (exp_datum_le hν hgb y)⟩
    (fun _ ↦ (Real.exp_pos _).le) ⟨0, Real.exp_pos _⟩ x ν hν

/-- The Gaussian exponent and the exponential datum combine into the quadratic cost. -/
private theorem weighted_heat_eq_exp_cost {ν : ℝ} (hν : 0 < ν) (z : ℝ^n) (a : ℝ) :
    HeatEquation.fundamentalSolutionHeat z ν * Real.exp (-a / (2 * ν)) =
      (4 * Real.pi * ν) ^ (-(n : ℝ) / 2) * Real.exp (-(a + ‖z‖ ^ 2 / 2) / (2 * ν)) := by
  rw [HeatEquation.fundamentalSolutionHeat, ite_eq_right (not_le.mpr hν)]
  generalize ‖z‖ = d
  cas using hν

/-- A fixed Gaussian tilt gives a lower bound for the logarithmic potential.
The tilt error is `2Mθ`; its normalization contributes only a fixed constant times `ν`. -/
theorem quadratic_value_sub_le_initialValueSolution_one {ν θ M : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (hθone : θ ≤ 1) {g : ℝ^n → ℝ} (hg : Continuous g) (hgb : ∀ y, |g y| ≤ M) (x : ℝ^n) :
    HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) g 1 x - 2 * M * θ -
        2 * ν * |Real.log (θ ^ (-(n : ℝ) / 2))| ≤ initialValueSolution ν g x 1 := by
  let m := HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) g 1 x
  let a := θ ^ (-(n : ℝ) / 2)
  let Z := HeatEquation.initialValueSolution (fun y ↦ Real.exp (-g y / (2 * ν))) x ν
  have ha : 0 < a := Real.rpow_pos_of_pos hθ _
  have hZ : 0 < Z := exponential_heat_pos hν hg hgb x
  obtain ⟨y₀, hminval, hmin, _⟩ := HopfLax.exists_quadratic_footpoint hg hgb
    (show (0 : ℝ) < 1 by norm_num) x
  have hm : m ≤ M := (HopfLax.value_norm_sq_div_two_bounds hgb zero_le_one x).2
  have hphase (y : ℝ^n) :
      m - 2 * M * θ + θ * ‖x - y‖ ^ 2 / 2 ≤ g y + ‖x - y‖ ^ 2 / 2 := by
    have hminy : m ≤ g y + ‖x - y‖ ^ 2 / 2 := by
      simpa only [mul_one] using hminval.trans_le (hmin y)
    have hmix := mul_le_mul_of_nonneg_left hminy (sub_nonneg.mpr hθone)
    have hdatum := mul_le_mul_of_nonneg_left (abs_le.mp (hgb y)).1 hθ.le
    have htop := mul_le_mul_of_nonneg_left hm hθ.le
    nlinarith only [hmix, hdatum, htop]
  have hnormfactor : (4 * Real.pi * ν) ^ (-(n : ℝ) / 2) =
      a * (4 * Real.pi * (ν / θ)) ^ (-(n : ℝ) / 2) := by
    dsimp only [a]
    cas [hν, hθ, Real.pi_pos]
  have hpoint (y : ℝ^n) :
      HeatEquation.fundamentalSolutionHeat (x - y) ν * Real.exp (-g y / (2 * ν)) ≤
        (a * Real.exp (-(m - 2 * M * θ) / (2 * ν))) *
          HeatEquation.fundamentalSolutionHeat (x - y) (ν / θ) := by
    rw [weighted_heat_eq_exp_cost hν]
    calc
      _ ≤ (4 * Real.pi * ν) ^ (-(n : ℝ) / 2) *
          Real.exp (-(m - 2 * M * θ + θ * ‖x - y‖ ^ 2 / 2) / (2 * ν)) := by
        gcongr _ * Real.exp (-?_ / _)
        exact hphase y
      _ = _ := by
        rw [HeatEquation.fundamentalSolutionHeat,
          ite_eq_right (not_le.mpr (div_pos hν hθ)), hnormfactor]
        generalize ‖x - y‖ = d
        have hexponent : -(m - 2 * M * θ + θ * d ^ 2 / 2) / (2 * ν) =
              -(m - 2 * M * θ) / (2 * ν) + -(d ^ 2 / (4 * (ν / θ))) := by
          field_simp [hν.ne', hθ.ne']
          ring
        rw [hexponent, Real.exp_add]
        ring
  have hmass : (∫ y, HeatEquation.fundamentalSolutionHeat (x - y) (ν / θ)) = 1 :=
    (integral_sub_left_eq_self
      (fun z : ℝ^n ↦ HeatEquation.fundamentalSolutionHeat z (ν / θ)) volume x).trans
        (HeatEquation.fundamentalSolutionHeat_integral _ (div_pos hν hθ))
  have hZupper : Z ≤ a * Real.exp (-(m - 2 * M * θ) / (2 * ν)) := by
    have hi := integral_mono (exponential_heat_integrable hν hg hgb x)
      (((HeatEquation.fundamentalSolutionHeat_integrable _ (div_pos hν hθ)).comp_sub_left
        x).const_mul (a * Real.exp (-(m - 2 * M * θ) / (2 * ν)))) hpoint
    simpa only [Z, HeatEquation.initialValueSolution, ite_eq_right (not_le.mpr hν),
      integral_const_mul, hmass, mul_one] using hi
  have hlog := Real.log_le_log hZ hZupper
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have htimes := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * ν by positivity)
  have hcancel : 2 * ν * (-(m - 2 * M * θ) / (2 * ν)) = -(m - 2 * M * θ) := by
    cas using hν
  have habs := mul_le_mul_of_nonneg_left (le_abs_self (Real.log a))
    (show 0 ≤ 2 * ν by positivity)
  simp only [initialValueSolution, logarithmicTransform, mul_one]
  change m - 2 * M * θ - 2 * ν * |Real.log a| ≤ -2 * ν * Real.log Z
  linarith only [htimes, hcancel, habs]

/-- Every positive-radius ball captures positive mass from the time-one Gaussian.
This remains true in dimension zero. -/
private theorem integral_heat_ball_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ z in ball (0 : ℝ^n) r, HeatEquation.fundamentalSolutionHeat z 1 := by
  have hi := HeatEquation.fundamentalSolutionHeat_integrable (n := n) 1 (by norm_num)
  apply (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall (fun z ↦
      (HeatEquation.fundamentalSolutionHeat_pos z 1 (by norm_num)).le)) hi.integrableOn).mpr
  have hs : Function.support (fun z : ℝ^n ↦ HeatEquation.fundamentalSolutionHeat z 1) = univ :=
    eq_univ_of_forall fun z ↦ (HeatEquation.fundamentalSolutionHeat_pos z 1 (by norm_num)).ne'
  rw [hs, univ_inter]
  exact Metric.measure_ball_pos (μ := volume) 0 hr

/-- A ball around a minimizing footpoint supplies the upper Laplace bound.
Only the oscillation of the datum on that ball enters. -/
theorem initialValueSolution_one_le_quadratic_value_add {ν r η M : ℝ} (hν : 0 < ν) (hνone : ν ≤ 1)
    (hr : 0 < r) {g : ℝ^n → ℝ} (hg : Continuous g) (hgb : ∀ y, |g y| ≤ M)
    (hmod : ∀ y z, ‖y - z‖ < r → |g y - g z| ≤ η) (x : ℝ^n) :
    initialValueSolution ν g x 1 ≤ HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) g 1 x + η + 2 *
      Real.sqrt M * r + r ^ 2 / 2 + 2 * ν *
      |Real.log (∫ z in ball (0 : ℝ^n) r, HeatEquation.fundamentalSolutionHeat z 1)| := by
  have hM : 0 ≤ M := (abs_nonneg (g 0)).trans (hgb 0)
  let m := HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) g 1 x
  let d := η + 2 * Real.sqrt M * r + r ^ 2 / 2
  let c := ∫ z in ball (0 : ℝ^n) r, HeatEquation.fundamentalSolutionHeat z 1
  let Z := HeatEquation.initialValueSolution (fun y ↦ Real.exp (-g y / (2 * ν))) x ν
  have hc : 0 < c := integral_heat_ball_pos hr
  obtain ⟨y₀, hy₀, _, hy₀dist⟩ := HopfLax.exists_quadratic_footpoint hg hgb
    (show (0 : ℝ) < 1 by norm_num) x
  have hfoot : ‖x - y₀‖ ≤ 2 * Real.sqrt M := by
    simp only [mul_one] at hy₀dist
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, norm_nonneg (x - y₀)]
  have hphase (y : ℝ^n) (hy : ‖y - y₀‖ < r) :
      g y + ‖x - y‖ ^ 2 / 2 ≤ m + d := by
    have hsquare : ‖x - y‖ ^ 2 ≤ (‖x - y₀‖ + r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
      (by linarith [norm_sub_le_norm_sub_add_norm_sub x y₀ y, norm_sub_rev y₀ y]) 2
    have hdatum := (abs_le.mp (hmod y y₀ hy)).2
    have hcross := mul_le_mul_of_nonneg_right hfoot hr.le
    have hvalue : m = g y₀ + ‖x - y₀‖ ^ 2 / 2 := by
      simpa only [mul_one] using hy₀
    dsimp only [d]
    linarith only [hsquare, hdatum, hcross, hvalue]
  let k : ℝ^n → ℝ := (ball (0 : ℝ^n) r).indicator (fun z ↦ HeatEquation.fundamentalSolutionHeat z 1)
  have hkint : Integrable k :=
    (HeatEquation.fundamentalSolutionHeat_integrable 1 (by norm_num)).indicator measurableSet_ball
  have hkmass : (∫ y, k (y - y₀)) = c := by
    rw [integral_sub_right_eq_self]
    exact integral_indicator measurableSet_ball
  have hkernel (z : ℝ^n) : HeatEquation.fundamentalSolutionHeat z 1 ≤
      (4 * Real.pi * ν) ^ (-(n : ℝ) / 2) := by
    have hpref := Real.rpow_le_rpow_of_nonpos
      (show 0 < 4 * Real.pi * ν by positivity)
      (mul_le_mul_of_nonneg_left hνone (show 0 ≤ 4 * Real.pi by positivity))
      (show -(n : ℝ) / 2 ≤ 0 from
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
    have hexp : Real.exp (-(‖z‖ ^ 2 / (4 * (1 : ℝ)))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num))
    rw [HeatEquation.fundamentalSolutionHeat, ite_eq_right (by norm_num)]
    exact (mul_le_mul_of_nonneg_left hexp
      (Real.rpow_pos_of_pos (by positivity) _).le).trans (by simpa only [mul_one] using hpref)
  have hpoint (y : ℝ^n) : Real.exp (-(m + d) / (2 * ν)) * k (y - y₀) ≤
      HeatEquation.fundamentalSolutionHeat (x - y) ν * Real.exp (-g y / (2 * ν)) := by
    by_cases hy : y - y₀ ∈ ball (0 : ℝ^n) r
    · have hyr : ‖y - y₀‖ < r := by simpa only [mem_ball, dist_zero_right] using hy
      simp only [k, indicator_of_mem hy]
      rw [weighted_heat_eq_exp_cost hν]
      have hexp : Real.exp (-(m + d) / (2 * ν)) ≤
          Real.exp (-(g y + ‖x - y‖ ^ 2 / 2) / (2 * ν)) := by
        gcongr Real.exp (-?_ / _)
        exact hphase y hyr
      calc
        _ = HeatEquation.fundamentalSolutionHeat (y - y₀) 1 *
            Real.exp (-(m + d) / (2 * ν)) := mul_comm _ _
        _ ≤ _ := mul_le_mul (hkernel _) hexp (Real.exp_pos _).le
          (Real.rpow_pos_of_pos (by positivity) _).le
    · simp only [k, indicator_of_notMem hy, mul_zero]
      exact mul_nonneg (HeatEquation.fundamentalSolutionHeat_pos _ ν hν).le (Real.exp_pos _).le
  have hZlower : Real.exp (-(m + d) / (2 * ν)) * c ≤ Z := by
    have hi := integral_mono ((hkint.comp_sub_right y₀).const_mul
      (Real.exp (-(m + d) / (2 * ν)))) (exponential_heat_integrable hν hg hgb x) hpoint
    simpa only [integral_const_mul, hkmass, Z, HeatEquation.initialValueSolution,
      ite_eq_right (not_le.mpr hν)] using hi
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hc) hZlower
  rw [Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp] at hlog
  have htimes := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * ν by positivity)
  have hcancel : 2 * ν * (-(m + d) / (2 * ν)) = -(m + d) := by cas using hν
  have habs := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log c))
    (show 0 ≤ 2 * ν by positivity)
  simp only [initialValueSolution, logarithmicTransform, mul_one]
  change -2 * ν * Real.log Z ≤ m + η + 2 * Real.sqrt M * r + r ^ 2 / 2 + 2 * ν * |Real.log c|
  dsimp only [d] at htimes hcancel
  linarith only [htimes, hcancel, habs]

end HamiltonJacobi.ColeHopf
