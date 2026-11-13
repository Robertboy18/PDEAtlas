/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Morrey potential estimate

The first step in Morrey's inequality bounds the distance between a point value `u x` and the
average of `u` over a ball by the Riesz potential of `|Du|`:

`|u(x) - u_{B(c,R)}| ≤ A_n ∫_{B(x,2R)} |Du(z)| |z - x|^{1-n} dz` for `x ∈ B̄(c, R)`.

The proof integrates the fundamental theorem of calculus along the segment from `x` to `y`,
`|u(y) - u(x)| ≤ ∫₀^{|y-x|} |Du(x + sθ)| ds` with `θ = (y-x)/|y-x|`, over `y` in the ball. In
polar coordinates about `x` the unweighted radial integral of `|Du|` becomes
`∫ |Du(z)| |z-x|^{1-n} dz`, because the polar Jacobian `r^{n-1}` cancels against the kernel
`r^{1-n}`. Enlarging `B(c, R)` to `B(x, 2R)` costs the factor `2^n` in `A_n`. The bound of
`lintegral_enorm_sub_center_le_morreyPotential`, with the constant `Sⁿ/n`, is the last display
of step 1 of the proof of Evans, PDE, §5.6.2, Theorem 4 (p. 281), which gives (21).

## Main results

* `morreyKernel`: the Riesz kernel `|z - x|^{1-n}` (valued in `ℝ≥0∞`).
  Ball averages use Mathlib's set-average notation `⨍ z in Metric.ball c R, u z ∂volume`.
* `lintegral_enorm_sub_center_le_morreyPotential`: `∫_{B(x,S)} |u(y) - u(x)| dy` is bounded by
  `Sⁿ/n` times the Riesz potential of `|Du|` over `B(x, S)`.
* `enorm_sub_ballAverage_le_morreyPotential`: the point-to-average estimate above, with the
  explicit constant `morreyBallAverageConstant n = 2^n / (n |B(0,1)|)`.
* `HasBallAveragePotentialBound`: the same-ball estimate as a predicate, a hypothesis of the
  conditional versions of the Morrey estimate; the unconditional theorem does not need it.

## Implementation notes

Polar coordinates come from Mathlib's `Measure.toSphere` and `Measure.volumeIoiPow (n - 1)`. The
radial measure already carries the Jacobian `r^{n-1}`, which makes the cancellation against the
kernel an exact identity on the positive half-line rather than an estimate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, pp. 280-283, step 1 of the proof,
  (21)-(22), pp. 281-282.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

section MultidimensionalFinite

variable {n : ℕ}

/-- The singular kernel `|z - x|^(1-n)` occurring in Evans's proof of Morrey's
inequality (§5.6.2, proof of Theorem 4).  The value at `z = x` is immaterial for Lebesgue
integration. -/
def morreyKernel (x z : ℝ^n) : ℝ≥0∞ :=
  ‖z - x‖ₑ ^ (1 - (n : ℝ))

/-- Polar coordinates for a nonnegative measurable integrand on a Euclidean ball.

The radial measure `volumeIoiPow (n - 1)` already contains the Jacobian
`r^(n-1)`.  Keeping it packaged at this stage makes the later Tonelli argument
considerably cleaner. -/
private theorem lintegral_ball_eq_lintegral_sphere_prod
    (hn : 0 < n) {h : ℝ^n → ℝ≥0∞} (S : ℝ) :
    (∫⁻ z in Metric.ball (0 : ℝ^n) S, h z) =
      ∫⁻ q : Metric.sphere (0 : ℝ^n) 1 × Set.Ioi (0 : ℝ),
        (Metric.ball (0 : ℝ^n) S).indicator h
            ((q.2 : ℝ) • (q.1 : ℝ^n))
          ∂(volume.toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← lintegral_indicator measurableSet_ball,
    ← restrict_compl_singleton (μ := (volume : Measure (ℝ^n))) 0,
    ← lintegral_subtype_comap (measurableSet_singleton (0 : ℝ^n)).compl]
  let e := homeomorphUnitSphereProd (ℝ^n)
  have hpolar := MeasurePreserving.lintegral_comp_emb
    ((volume : Measure (ℝ^n)).measurePreserving_homeomorphUnitSphereProd)
    e.measurableEmbedding
    (fun q ↦ (Metric.ball (0 : ℝ^n) S).indicator h
      (((e.symm q : Subtype ((Set.singleton (0 : ℝ^n))ᶜ)) : ℝ^n)))
  simpa [e, homeomorphUnitSphereProd_symm_apply_coe] using hpolar

/-- Translating a lower integral over `B(x, S)` to the centered ball `B(0, S)`. -/
private theorem setLIntegral_ball_eq_ball_zero (x : ℝ^n) (S : ℝ) (f : ℝ^n → ℝ≥0∞) :
    ∫⁻ y in Metric.ball x S, f y = ∫⁻ w in Metric.ball (0 : ℝ^n) S, f (x + w) := by
  have h := (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft x) f (Metric.ball x S)
  rw [preimage_add_ball, sub_self] at h
  exact h.symm

/-- A nonnegative multiple of a unit vector has norm the multiple. -/
private theorem norm_smul_sphere (θ : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖r • (θ : ℝ^n)‖ = r := by
  simp [norm_smul, abs_of_nonneg hr]

private theorem smul_sphere_mem_ball_iff (θ : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 ≤ r)
    (S : ℝ) : r • (θ : ℝ^n) ∈ Metric.ball (0 : ℝ^n) S ↔ r < S := by
  rw [mem_ball_zero_iff, norm_smul_sphere θ hr]

/-- Fundamental-theorem-of-calculus estimate along a unit-speed radial ray: the pointwise input
in Evans's segment-averaging proof. -/
private theorem enorm_sub_le_lintegral_fderiv_ray
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (x : ℝ^n)
    (θ : Metric.sphere (0 : ℝ^n) 1) (r : ℝ) (hr : 0 ≤ r) :
    ‖u (x + r • (θ : ℝ^n)) - u x‖ₑ ≤
      ∫⁻ s in Set.Icc (0 : ℝ) r,
        ‖fderiv ℝ u (x + s • (θ : ℝ^n))‖ₑ := by
  have hderiv (s : ℝ) : deriv (fun t : ℝ ↦ u (x + t • (θ : ℝ^n))) s =
      fderiv ℝ u (x + s • (θ : ℝ^n)) θ := by
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • (θ : ℝ^n)) (θ : ℝ^n) s := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const (θ : ℝ^n)).const_add x
    exact ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hline).deriv
  have hv : ContDiff ℝ 1 fun t : ℝ ↦ u (x + t • (θ : ℝ^n)) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hv.contDiffOn hr
  have hθ : ‖(θ : ℝ^n)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, norm_eq_of_mem_sphere, ENNReal.ofReal_one]
  simp only [zero_smul, add_zero, hderiv] at h
  exact h.trans <| lintegral_mono fun s ↦
    ((fderiv ℝ u (x + s • (θ : ℝ^n))).le_opENorm_of_le hθ).trans_eq (mul_one _)

/-- Average radial oscillation over a centered ball, before identifying the
unweighted radial integral with the Riesz potential.

The factor `S^n / n` is exact: it is the mass of `(0,S)` for the polar radial
measure `r^(n-1) dr`. -/
private theorem lintegral_enorm_sub_center_le_radial_fderiv
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (hn : 0 < n)
    (x : ℝ^n) {S : ℝ} (hS : 0 < S) :
    (∫⁻ y in Metric.ball x S, ‖u y - u x‖ₑ) ≤
      ENNReal.ofReal (S ^ n / n) *
        ∫⁻ θ : Metric.sphere (0 : ℝ^n) 1,
          ∫⁻ s in Set.Ioo (0 : ℝ) S,
            ‖fderiv ℝ u (x + s • (θ : ℝ^n))‖ₑ
              ∂volume ∂volume.toSphere := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Sr : Set.Ioi (0 : ℝ) := ⟨S, hS⟩
  have hradialMeas : Measurable fun θ : Metric.sphere (0 : ℝ^n) 1 ↦
      ∫⁻ s in Set.Ioo (0 : ℝ) S, ‖fderiv ℝ u (x + s • (θ : ℝ^n))‖ₑ ∂volume :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioo (0 : ℝ) S))
      (f := fun q : Metric.sphere (0 : ℝ^n) 1 × ℝ ↦ ‖fderiv ℝ u (x + q.2 • (q.1 : ℝ^n))‖ₑ)
      ((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).enorm.measurable
  have hmass : Measure.volumeIoiPow (n - 1) (Set.Iio Sr) = ENNReal.ofReal (S ^ n / n) := by
    rw [Measure.volumeIoiPow_apply_Iio, ← Nat.cast_add_one, Nat.sub_add_cancel hn]
  rw [setLIntegral_ball_eq_ball_zero, lintegral_ball_eq_lintegral_sphere_prod hn S, lintegral_prod]
  swap
  · exact ((((hu.continuous.comp (by fun_prop)).sub continuous_const).enorm.measurable
      |>.indicator measurableSet_ball).comp (by fun_prop)).aemeasurable
  calc _ ≤ ∫⁻ θ : Metric.sphere (0 : ℝ^n) 1, ∫⁻ r : Set.Ioi (0 : ℝ),
          (Set.Iio Sr).indicator (fun _ ↦
            ∫⁻ s in Set.Ioo (0 : ℝ) S, ‖fderiv ℝ u (x + s • (θ : ℝ^n))‖ₑ ∂volume) r
          ∂Measure.volumeIoiPow (n - 1) ∂volume.toSphere := by
        refine lintegral_mono fun θ ↦ lintegral_mono fun r ↦ ?_
        by_cases hrS : (r : ℝ) < S
        · rw [Set.indicator_of_mem ((smul_sphere_mem_ball_iff θ r.2.le S).2 hrS),
            Set.indicator_of_mem (show r ∈ Set.Iio Sr from hrS), restrict_Ioo_eq_restrict_Icc]
          exact (enorm_sub_le_lintegral_fderiv_ray u hu x θ r r.2.le).trans
            (lintegral_mono_set (Set.Icc_subset_Icc_right hrS.le))
        · rw [Set.indicator_of_notMem (mt (smul_sphere_mem_ball_iff θ r.2.le S).1 hrS)]
          exact zero_le
    _ = _ := by
        simp_rw [lintegral_indicator_const measurableSet_Iio, hmass]
        rw [lintegral_mul_const _ hradialMeas, mul_comm]

/-- Along a positive unit-speed ray, the Morrey kernel is exactly
`r^(1-n)`. -/
private theorem morreyKernel_zero_smul_sphere
    (θ : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    morreyKernel (0 : ℝ^n) (r • (θ : ℝ^n)) =
      ENNReal.ofReal r ^ (1 - (n : ℝ)) := by
  rw [morreyKernel, sub_zero, ← ofReal_norm, norm_smul_sphere θ hr.le]

/-- Cancellation of the polar Jacobian against the Morrey kernel.

This is the exact identity
`r^(n-1) * r^(1-n) = 1` on the positive radial half-line. -/
private theorem lintegral_volumeIoiPow_mul_morreyKernel_ray
    (hn : 0 < n) (θ : Metric.sphere (0 : ℝ^n) 1)
    {G : ℝ → ℝ≥0∞} (hG : Measurable G) (S : ℝ) :
    (∫⁻ r : Set.Ioi (0 : ℝ),
        (Metric.ball (0 : ℝ^n) S).indicator
          (fun w ↦ G ‖w‖ * morreyKernel (0 : ℝ^n) w)
          ((r : ℝ) • (θ : ℝ^n))
          ∂Measure.volumeIoiPow (n - 1)) =
      ∫⁻ r in Set.Ioo (0 : ℝ) S, G r ∂volume := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hK : Measurable fun w : ℝ^n ↦ G ‖w‖ * morreyKernel (0 : ℝ^n) w :=
    (hG.comp continuous_norm.measurable).mul
      (ENNReal.continuous_rpow_const.comp (continuous_id.sub continuous_const).enorm).measurable
  have hexponent : (((n - 1 : ℕ) : ℝ) + (1 - (n : ℝ))) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    ring
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
  rotate_left
  · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
  · exact (hK.indicator measurableSet_ball).comp (by fun_prop)
  let H : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (n - 1)) *
    (Metric.ball (0 : ℝ^n) S).indicator (fun w ↦ G ‖w‖ * morreyKernel (0 : ℝ^n) w)
      (s • (θ : ℝ^n))
  change (∫⁻ r : Set.Ioi (0 : ℝ), H r ∂Measure.comap Subtype.val volume) = _
  rw [lintegral_subtype_comap measurableSet_Ioi H, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun r ↦ ?_
  rcases le_or_gt r 0 with hr | hr
  · rw [Set.indicator_of_notMem (show r ∉ Set.Ioi (0 : ℝ) from not_lt.2 hr),
      Set.indicator_of_notMem (show r ∉ Set.Ioo (0 : ℝ) S from fun h ↦ hr.not_gt h.1)]
  rw [Set.indicator_of_mem (show r ∈ Set.Ioi (0 : ℝ) from hr)]
  by_cases hrS : r < S
  · rw [Set.indicator_of_mem (show r ∈ Set.Ioo (0 : ℝ) S from ⟨hr, hrS⟩)]
    simp only [H, Set.indicator_of_mem ((smul_sphere_mem_ball_iff θ hr.le S).2 hrS),
      norm_smul_sphere θ hr.le, morreyKernel_zero_smul_sphere θ hr, ENNReal.ofReal_pow hr.le]
    rw [← ENNReal.rpow_natCast, mul_left_comm, ← ENNReal.rpow_add _ _
      (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top, hexponent, ENNReal.rpow_zero,
      mul_one]
  · rw [Set.indicator_of_notMem (show r ∉ Set.Ioo (0 : ℝ) S from fun h ↦ hrS h.2)]
    simp only [H, Set.indicator_of_notMem (mt (smul_sphere_mem_ball_iff θ hr.le S).1 hrS),
      mul_zero]

/-- The unweighted radial derivative integral is exactly the Riesz potential
over the corresponding centered ball. -/
private theorem lintegral_sphere_radial_fderiv_eq_morreyPotential
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (hn : 0 < n)
    (x : ℝ^n) (S : ℝ) :
    (∫⁻ θ : Metric.sphere (0 : ℝ^n) 1,
        ∫⁻ s in Set.Ioo (0 : ℝ) S,
          ‖fderiv ℝ u (x + s • (θ : ℝ^n))‖ₑ
            ∂volume ∂volume.toSphere) =
      ∫⁻ z in Metric.ball x S,
        ‖fderiv ℝ u z‖ₑ * morreyKernel x z := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hDu := (hu.continuous_fderiv one_ne_zero).enorm
  have hkernel (w : ℝ^n) : morreyKernel x (x + w) = morreyKernel (0 : ℝ^n) w := by
    rw [morreyKernel, morreyKernel, add_sub_cancel_left, sub_zero]
  simp_rw [setLIntegral_ball_eq_ball_zero x S, hkernel]
  rw [lintegral_ball_eq_lintegral_sphere_prod hn S, lintegral_prod]
  swap
  · exact ((((hDu.comp (by fun_prop)).measurable.mul (ENNReal.continuous_rpow_const.comp
      (continuous_id.sub continuous_const).enorm).measurable).indicator measurableSet_ball).comp
      (by fun_prop)).aemeasurable
  refine lintegral_congr fun θ ↦ ?_
  rw [← lintegral_volumeIoiPow_mul_morreyKernel_ray hn θ
    (G := fun r ↦ ‖fderiv ℝ u (x + r • (θ : ℝ^n))‖ₑ) (hDu.comp (by fun_prop)).measurable S]
  refine lintegral_congr fun r ↦ ?_
  by_cases hrS : (r : ℝ) • (θ : ℝ^n) ∈ Metric.ball (0 : ℝ^n) S
  · simp only [Set.indicator_of_mem hrS, norm_smul_sphere θ r.2.le]
  · simp only [Set.indicator_of_notMem hrS]

/-- Centered-ball oscillation estimate in Riesz-potential form. -/
theorem lintegral_enorm_sub_center_le_morreyPotential
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (x : ℝ^n) {S : ℝ} (hS : 0 < S) :
    (∫⁻ y in Metric.ball x S, ‖u y - u x‖ₑ) ≤
      ENNReal.ofReal (S ^ n / n) *
        ∫⁻ z in Metric.ball x S,
          ‖fderiv ℝ u z‖ₑ * morreyKernel x z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hpt (y : ℝ^0) : y = x := by ext i; exact i.elim0
    calc (∫⁻ y in Metric.ball x S, ‖u y - u x‖ₑ) = ∫⁻ _ in Metric.ball x S, 0 :=
          lintegral_congr fun y ↦ by rw [hpt y, sub_self, enorm_zero]
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le
  exact lintegral_sphere_radial_fderiv_eq_morreyPotential u hu hn x S ▸
    lintegral_enorm_sub_center_le_radial_fderiv u hu hn x hS

/-- A point differs from the integral average over a positive-radius ball by
at most the normalized average of its pointwise oscillation. -/
private theorem enorm_sub_ballAverage_le_normalized_lintegral
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (c x : ℝ^n) {R : ℝ} (hR : 0 < R) :
    ‖u x - (⨍ z in Metric.ball c R, u z ∂volume)‖ₑ ≤
      ENNReal.ofReal (volume.real (Metric.ball c R))⁻¹ *
        ∫⁻ y in Metric.ball c R, ‖u y - u x‖ₑ := by
  have hvolumePos : 0 < volume.real (Metric.ball c R) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume c hR).ne' measure_ball_lt_top.ne
  have huIntegrable : IntegrableOn u (Metric.ball c R) volume :=
    (hu.continuous.continuousOn.integrableOn_compact (ProperSpace.isCompact_closedBall c R))
      |>.mono_set Metric.ball_subset_closedBall
  have hidentity : u x - (⨍ z in Metric.ball c R, u z ∂volume) =
      (volume.real (Metric.ball c R))⁻¹ * ∫ y in Metric.ball c R, (u x - u y) := by
    rw [integral_sub integrableOn_const huIntegrable, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul, integral_const, measureReal_restrict_apply_univ]
    field_simp
  rw [hidentity, enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hvolumePos)]
  simp_rw [enorm_sub_rev (u _) (u x)]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

/-- Explicit constant in the enlarged-ball point-to-average estimate.

The factor `2^n` comes from the geometric inclusion
`B(c,R) ⊆ B(x,2R)` when `x ∈ B̄(c,R)`. -/
def morreyBallAverageConstant (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (2 ^ n /
      ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1)))

/-- **Point-to-ball-average estimate** on the enlarged ball `B(x, 2R)`.

For `x ∈ B̄(c,R)`, enlarge `B(c,R)` to `B(x,2R)`, average the
line-segment fundamental theorem in polar coordinates, and cancel the polar
Jacobian against the Riesz kernel.  The result is

`|u(x)-u_{B(c,R)}| ≤ Aₙ ∫_{B(x,2R)} |Du(z)| |z-x|^(1-n) dz`,

where `Aₙ = 2^n / (n |B(0,1)|)`.

The enlarged-ball form suffices for Morrey's inequality and leaves no
geometric hypothesis in the final theorem, with an explicit
dimension-dependent factor in the constant. -/
theorem enorm_sub_ballAverage_le_morreyPotential
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (hn : 0 < n)
    {c x : ℝ^n} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ Metric.closedBall c R) :
    ‖u x - (⨍ z in Metric.ball c R, u z ∂volume)‖ₑ ≤
      morreyBallAverageConstant n *
        ∫⁻ z in Metric.ball x (2 * R),
          ‖fderiv ℝ u z‖ₑ * morreyKernel x z := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsubset : Metric.ball c R ⊆ Metric.ball x (2 * R) :=
    Metric.ball_subset_ball' (by linarith [dist_comm c x, Metric.mem_closedBall.1 hx])
  have hvolumePos : 0 < volume.real (Metric.ball c R) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume c hR).ne' measure_ball_lt_top.ne
  have hunitVolumePos : 0 < volume.real (Metric.ball (0 : ℝ^n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  have hvolume : volume.real (Metric.ball c R) =
      R ^ n * volume.real (Metric.ball (0 : ℝ^n) 1) := by
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball (volume : Measure (ℝ^n)) c R]
    simpa using Measure.addHaar_real_closedBall (volume : Measure (ℝ^n)) c hR.le
  have hcoefficient : ENNReal.ofReal (volume.real (Metric.ball c R))⁻¹ *
      ENNReal.ofReal ((2 * R) ^ n / n) = morreyBallAverageConstant n := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hvolumePos.le), morreyBallAverageConstant, hvolume,
      mul_pow]
    field_simp
  calc
    ‖u x - (⨍ z in Metric.ball c R, u z ∂volume)‖ₑ ≤
        ENNReal.ofReal (volume.real (Metric.ball c R))⁻¹ *
          ∫⁻ y in Metric.ball x (2 * R), ‖u y - u x‖ₑ :=
      (enorm_sub_ballAverage_le_normalized_lintegral u hu c x hR).trans
        (by gcongr)
    _ ≤ ENNReal.ofReal (volume.real (Metric.ball c R))⁻¹ *
        (ENNReal.ofReal ((2 * R) ^ n / n) *
          ∫⁻ z in Metric.ball x (2 * R), ‖fderiv ℝ u z‖ₑ * morreyKernel x z) := by
      gcongr
      exact lintegral_enorm_sub_center_le_morreyPotential u hu x (by positivity)
    _ = _ := by rw [← mul_assoc, hcoefficient]

/-- The same-ball point-to-average potential estimate.

For a point `x` in the closed ball `B̄(c,R)`, the oscillation from the ball average is controlled
by the Riesz potential of `|Du|` over `B(c,R)`.  This is the multidimensional segment-averaging
theorem in the proof of Evans §5.6.2, Theorem 4.

`enorm_sub_ballAverage_le_morreyPotential` proves the enlarged-ball form needed for Morrey's
inequality. The predicate records the same-ball estimate used by the conditional
theorems; the main theorem does not assume it, and the predicate alone does not encode Hölder
continuity. -/
def HasBallAveragePotentialBound (u : ℝ^n → ℝ) (A : ℝ≥0∞) : Prop :=
  ∀ ⦃c : ℝ^n⦄ ⦃R : ℝ⦄ ⦃x : ℝ^n⦄,
    0 < R → x ∈ Metric.closedBall c R →
      ‖u x - (⨍ z in Metric.ball c R, u z ∂volume)‖ₑ ≤
        A * ∫⁻ z in Metric.ball c R, ‖fderiv ℝ u z‖ₑ * morreyKernel x z

end MultidimensionalFinite

end SobolevSpace
