/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.Potential
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Exponent
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Morrey kernel integrability

The Morrey kernel is `|z - x|^{1-n}`, the Riesz kernel produced when the fundamental theorem of
calculus along segments from `x` is averaged in polar coordinates. Morrey's inequality needs its
`L^q` norm over a ball, `q` the Hölder conjugate of `p`. In polar coordinates about `x` the
integrand is `r^{(1-n)q} r^{n-1}`, integrable at `r = 0` exactly when `(n-1) q < n`, equivalently
`p > n`, and then

`∫_{B(x,S)} |z - x|^{(1-n)q} dz = n |B(0,1)| S^{n-(n-1)q} / (n - (n-1)q)`.

Taking the `q`-th root turns the exponent `n - (n-1)q` into `q (1 - n/p)`, so the `L^q` norm of
the kernel on `B(x, S)` is an explicit constant times `S^{1-n/p}`. This is where the Morrey
exponent enters the estimate.

## Main results

* `integral_morreyKernelPower_ball`, `lintegral_morreyKernel_rpow_ball_center`: the exact polar
  integral of the kernel power over a ball centered at the singularity, in Bochner and in `ℝ≥0∞`
  form.
* `lintegral_morreyKernel_rpow_ball_center_root`: its `q`-th root,
  `morreyCenteredKernelConstant n q · S^{1-n/p}`.
* `hasMorreyKernelBound_of_holderConjugate`: the kernel bound `HasMorreyKernelBound p q K` used
  by the Morrey estimate holds unconditionally for conjugate `p, q` with `p > n`, with the
  constant `morreyKernelConstant n q` obtained by enlarging an off-center ball `B(c, R)` to
  `B(x, 2R)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, pp. 280-283; steps 2 and 3 of the proof,
  p. 282, use that `∫_{B(x,1)} |x - y|^{-(n-1)p/(p-1)} dy` is finite for `p > n`, and the scaling
  `r^{1-n/p}` in (25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

section MultidimensionalFinite

variable {n : ℕ}

/-- The `L^q` estimate for the singular kernel on a ball that is used in Evans §5.6.2.

If `p` and `q` are Hölder conjugates and `p > n`, polar integration gives this property with a
constant depending only on `n` and `p`.  The theorem
`hasMorreyKernelBound_of_holderConjugate` below proves it from the exact centered-ball integral. -/
def HasMorreyKernelBound (p q : ℝ) (K : ℝ≥0∞) : Prop :=
  ∀ ⦃c : ℝ^n⦄ ⦃R : ℝ⦄ ⦃x : ℝ^n⦄,
    0 < R → x ∈ Metric.closedBall c R →
      (∫⁻ z in Metric.ball c R, morreyKernel x z ^ q) ^ (1 / q) ≤
        K * ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p)

/-- Exact radial integral underlying the finite-exponent Morrey kernel estimate.

For `n > 0` and `(n - 1)q < n`, the singularity
`|z-x|^((1-n)q)` is locally integrable, and its integral over a ball centered at the
singularity is

`n |B(0,1)| S^(n-(n-1)q) / (n-(n-1)q)`.

This is the polar-integration calculation in Evans §5.6.2. -/
theorem integral_morreyKernelPower_ball
    (hn : 0 < n) {q S : ℝ} (hcritical : (n - 1 : ℝ) * q < n) (hS : 0 < S)
    (x : ℝ^n) :
    (∫ z : ℝ^n,
        if ‖z - x‖ < S then ‖z - x‖ ^ ((1 - (n : ℝ)) * q) else 0) =
      (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
          ((n : ℝ) - (n - 1 : ℝ) * q) *
        S ^ ((n : ℝ) - (n - 1 : ℝ) * q) := by
  let a : ℝ := (1 - (n : ℝ)) * q
  let F : ℝ → ℝ := fun r ↦ if r < S then r ^ a else 0
  have hexponent : -1 < (n - 1 : ℝ) + a := by
    dsimp [a]
    linarith
  have hdenom : 0 < (n : ℝ) - (n - 1 : ℝ) * q := by
    exact sub_pos.mpr hcritical
  have hradial :
      (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1) * F r) =
        S ^ ((n : ℝ) - (n - 1 : ℝ) * q) /
          ((n : ℝ) - (n - 1 : ℝ) * q) := by
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1) * F r) =
          ∫ r in (0 : ℝ)..S, r ^ ((n - 1 : ℝ) + a) := by
        rw [intervalIntegral.integral_of_le hS.le]
        rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        have hSae : ∀ᵐ r : ℝ ∂volume, r ≠ S := by
          simpa using (Set.countable_singleton S).ae_notMem (volume : Measure ℝ)
        filter_upwards [hSae] with r hrS
        by_cases hr : 0 < r
        · by_cases hrSle : r ≤ S
          · have hrSlt : r < S := lt_of_le_of_ne hrSle hrS
            have hrpow :
                r ^ (n - 1) * r ^ a = r ^ ((n - 1 : ℝ) + a) := by
              calc
                r ^ (n - 1) * r ^ a =
                    r ^ ((n - 1 : ℕ) : ℝ) * r ^ a := by
                      rw [Real.rpow_natCast]
                _ = r ^ (((n - 1 : ℕ) : ℝ) + a) :=
                  (Real.rpow_add hr _ _).symm
                _ = r ^ ((n - 1 : ℝ) + a) := by
                  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
                  norm_num
            simp [F, Set.mem_Ioi, Set.mem_Ioc, hr, hrSle, hrSlt, hrpow]
          · have hrSlt : ¬r < S := not_lt.mpr (le_of_not_ge hrSle)
            simp [F, Set.mem_Ioi, Set.mem_Ioc, hr, hrSle, hrSlt]
        · simp [F, Set.mem_Ioi, Set.mem_Ioc, hr]
      _ = S ^ ((n : ℝ) - (n - 1 : ℝ) * q) /
          ((n : ℝ) - (n - 1 : ℝ) * q) := by
        rw [integral_rpow (Or.inl hexponent)]
        have hpower :
            (n - 1 : ℝ) + a + 1 = (n : ℝ) - (n - 1 : ℝ) * q := by
          dsimp [a]
          ring
        rw [hpower, Real.zero_rpow hdenom.ne']
        ring
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpolar := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (ℝ^n)) F
  have hpolar' :
      (∫ z : ℝ^n, F ‖z‖) =
        (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) *
          (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1) * F r) := by
    simpa [nsmul_eq_mul, smul_eq_mul, mul_assoc] using hpolar
  let f : ℝ^n → ℝ := fun z ↦
    if ‖z‖ < S then ‖z‖ ^ ((1 - (n : ℝ)) * q) else 0
  calc
    (∫ z : ℝ^n,
        if ‖z - x‖ < S then ‖z - x‖ ^ ((1 - (n : ℝ)) * q) else 0) =
        ∫ z : ℝ^n, f (z - x) := by rfl
    _ = ∫ z : ℝ^n, f z := integral_sub_right_eq_self f x
    _ = ∫ z : ℝ^n, F ‖z‖ := by rfl
    _ = (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) *
        (S ^ ((n : ℝ) - (n - 1 : ℝ) * q) /
          ((n : ℝ) - (n - 1 : ℝ) * q)) := by rw [hpolar', hradial]
    _ = (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
          ((n : ℝ) - (n - 1 : ℝ) * q) *
        S ^ ((n : ℝ) - (n - 1 : ℝ) * q) := by ring

/-- The extended-nonnegative version of `integral_morreyKernelPower_ball`.
The point singularity is retained as `∞` by `morreyKernel`; it does not change
the integral because singletons have zero Lebesgue measure. -/
theorem lintegral_morreyKernel_rpow_ball_center
    (hn : 0 < n) {q S : ℝ}
    (hcritical : (n - 1 : ℝ) * q < n) (hS : 0 < S)
    (x : ℝ^n) :
    (∫⁻ z in Metric.ball x S, morreyKernel x z ^ q) =
      ENNReal.ofReal
        ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
            ((n : ℝ) - (n - 1 : ℝ) * q) *
          S ^ ((n : ℝ) - (n - 1 : ℝ) * q)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g : ℝ^n → ℝ := fun z ↦
    if ‖z - x‖ < S then ‖z - x‖ ^ ((1 - (n : ℝ)) * q) else 0
  have heq :
      (∫ z : ℝ^n, g z) =
        (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
            ((n : ℝ) - (n - 1 : ℝ) * q) *
          S ^ ((n : ℝ) - (n - 1 : ℝ) * q) := by
    simpa [g] using integral_morreyKernelPower_ball hn hcritical hS x
  have hdenom : 0 < (n : ℝ) - (n - 1 : ℝ) * q :=
    sub_pos.mpr hcritical
  have hvolume : 0 < volume.real (Metric.ball (0 : ℝ^n) 1) := by
    simpa [MeasureTheory.Measure.real] using ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : ℝ^n) zero_lt_one).ne'
      (measure_ball_lt_top.ne : volume (Metric.ball (0 : ℝ^n) 1) ≠ ∞)
  have hright :
      0 < (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
            ((n : ℝ) - (n - 1 : ℝ) * q) *
          S ^ ((n : ℝ) - (n - 1 : ℝ) * q) :=
    mul_pos (div_pos (mul_pos (Nat.cast_pos.mpr hn) hvolume) hdenom)
      (Real.rpow_pos_of_pos hS _)
  have hg : Integrable g := by
    by_contra hnot
    rw [integral_undef hnot] at heq
    linarith
  have hgNonneg : 0 ≤ᵐ[volume] g := by
    filter_upwards with z
    simp only [g]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  calc
    (∫⁻ z in Metric.ball x S, morreyKernel x z ^ q) =
        ∫⁻ z, ENNReal.ofReal (g z) := by
          rw [← lintegral_indicator measurableSet_ball]
          apply lintegral_congr_ae
          have hxAe : ∀ᵐ z : ℝ^n ∂volume, z ≠ x := by
            simpa using (Set.countable_singleton x).ae_notMem
              (volume : Measure (ℝ^n))
          filter_upwards [hxAe] with z hzx
          have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
          by_cases hzBall : z ∈ Metric.ball x S
          · have hzS : ‖z - x‖ < S := by
              simpa [Metric.mem_ball, dist_eq_norm] using hzBall
            simp only [Set.indicator_of_mem hzBall, g, hzS, ite_true, morreyKernel]
            rw [← ENNReal.rpow_mul]
            rw [← ENNReal.ofReal_rpow_of_pos hnorm]
            simp [ofReal_norm]
          · have hzS : ¬‖z - x‖ < S := by
              simpa [Metric.mem_ball, dist_eq_norm] using hzBall
            simp [Set.indicator_of_notMem hzBall, g, hzS]
    _ = ENNReal.ofReal (∫ z : ℝ^n, g z) :=
      (ofReal_integral_eq_lintegral_ofReal hg hgNonneg).symm
    _ = _ := by rw [heq]

/-- Exact constant for the `L^q` norm of the Morrey kernel on a ball
centered at its singularity. -/
def morreyCenteredKernelConstant (n : ℕ) (q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
        ((n : ℝ) - (n - 1 : ℝ) * q)) ^ (1 / q)

/-- Exact `L^q` norm of the Morrey kernel on a centered ball.

For Hölder-conjugate `p,q` with `p>n`, the radial exponent after integration is
`n-(n-1)q`, and division by `q` gives exactly `1-n/p`. -/
theorem lintegral_morreyKernel_rpow_ball_center_root
    (hn : 0 < n) {p q S : ℝ} (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (hS : 0 < S) (x : ℝ^n) :
    (∫⁻ z in Metric.ball x S, morreyKernel x z ^ q) ^ (1 / q) =
      morreyCenteredKernelConstant n q *
        ENNReal.ofReal S ^ morreyExponent n (ENNReal.ofReal p) := by
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := lt_trans (Nat.cast_pos.mpr hn) hp
  have hcritical : (n - 1 : ℝ) * q < n := by
    rw [hpq.conjugate_eq]
    calc
      (n - 1 : ℝ) * (p / (p - 1)) =
          ((n - 1 : ℝ) * p) / (p - 1) := by ring
      _ < n := (div_lt_iff₀ hpq.sub_one_pos).2 (by nlinarith)
  have hbeta : 0 < (n : ℝ) - (n - 1 : ℝ) * q :=
    sub_pos.mpr hcritical
  have hexponent :
      ((n : ℝ) - (n - 1 : ℝ) * q) * (1 / q) =
        morreyExponent n (ENNReal.ofReal p) := by
    rw [morreyExponent, ENNReal.toReal_ofReal hp0.le]
    have hconj := hpq.one_div_add_one_div
    field_simp [hpq.ne_zero, hpq.symm.ne_zero] at hconj ⊢
    nlinarith
  have hconstantNonneg :
      0 ≤ (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
        ((n : ℝ) - (n - 1 : ℝ) * q) := by positivity
  rw [lintegral_morreyKernel_rpow_ball_center
    hn hcritical hS x]
  rw [ENNReal.ofReal_mul hconstantNonneg]
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (one_div_nonneg.mpr hq0.le)]
  change morreyCenteredKernelConstant n q *
      (ENNReal.ofReal
        (S ^ ((n : ℝ) - (n - 1 : ℝ) * q))) ^ (1 / q) =
    morreyCenteredKernelConstant n q *
      ENNReal.ofReal S ^ morreyExponent n (ENNReal.ofReal p)
  congr 1
  rw [← ENNReal.ofReal_rpow_of_nonneg hS.le hbeta.le]
  rw [← ENNReal.rpow_mul, hexponent]

/-- The explicit constant obtained by enlarging an off-center radius-`R` ball
to the radius-`2R` ball centered at the kernel singularity. -/
def morreyKernelConstant (n : ℕ) (q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
          ((n : ℝ) - (n - 1 : ℝ) * q) *
        2 ^ ((n : ℝ) - (n - 1 : ℝ) * q)) ^ (1 / q)

/-- The multidimensional kernel hypothesis in Evans's Morrey proof holds
unconditionally for Hölder-conjugate `p,q` with `p>n`.

The proof uses `lintegral_morreyKernel_rpow_ball_center`, the inclusion
`B(c,R) ⊆ B(x,2R)` for `x ∈ B̄(c,R)`, and the conjugacy identity
`1/p + 1/q = 1`.  Thus the constant depends only on `n` and the conjugate
exponents, not on the ball or its center. -/
theorem hasMorreyKernelBound_of_holderConjugate
    (hn : 0 < n) {p q : ℝ} (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    HasMorreyKernelBound (n := n) p q (morreyKernelConstant n q) := by
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := lt_trans (Nat.cast_pos.mpr hn) hp
  have hcritical : (n - 1 : ℝ) * q < n := by
    rw [hpq.conjugate_eq]
    calc
      (n - 1 : ℝ) * (p / (p - 1)) =
          ((n - 1 : ℝ) * p) / (p - 1) := by ring
      _ < n := (div_lt_iff₀ hpq.sub_one_pos).2 (by nlinarith)
  have hbeta : 0 < (n : ℝ) - (n - 1 : ℝ) * q :=
    sub_pos.mpr hcritical
  have hexponent :
      ((n : ℝ) - (n - 1 : ℝ) * q) * (1 / q) =
        morreyExponent n (ENNReal.ofReal p) := by
    rw [morreyExponent, ENNReal.toReal_ofReal hp0.le]
    have hconj := hpq.one_div_add_one_div
    field_simp [hpq.ne_zero, hpq.symm.ne_zero] at hconj ⊢
    nlinarith
  intro c R x hR hx
  have hsubset : Metric.ball c R ⊆ Metric.ball x (2 * R) := by
    intro z hz
    have hzc : dist z c < R := hz
    have hcx : dist c x ≤ R := by
      simpa [dist_comm] using hx
    have hzx : dist z x ≤ dist z c + dist c x := dist_triangle _ _ _
    exact lt_of_le_of_lt hzx (by linarith)
  have hintegral :
      (∫⁻ z in Metric.ball c R, morreyKernel x z ^ q) ≤
        ∫⁻ z in Metric.ball x (2 * R), morreyKernel x z ^ q :=
    lintegral_mono' (Measure.restrict_mono hsubset le_rfl) le_rfl
  have hconstNonneg :
      0 ≤ (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
          ((n : ℝ) - (n - 1 : ℝ) * q) *
        2 ^ ((n : ℝ) - (n - 1 : ℝ) * q) := by positivity
  have hscale :
      (n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
            ((n : ℝ) - (n - 1 : ℝ) * q) *
          (2 * R) ^ ((n : ℝ) - (n - 1 : ℝ) * q) =
        ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
            ((n : ℝ) - (n - 1 : ℝ) * q) *
          2 ^ ((n : ℝ) - (n - 1 : ℝ) * q)) *
        R ^ ((n : ℝ) - (n - 1 : ℝ) * q) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hR.le]
    ring
  calc
    (∫⁻ z in Metric.ball c R, morreyKernel x z ^ q) ^ (1 / q) ≤
        (∫⁻ z in Metric.ball x (2 * R), morreyKernel x z ^ q) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hintegral (one_div_nonneg.mpr hq0.le)
    _ = (ENNReal.ofReal
          ((n : ℝ) * volume.real (Metric.ball (0 : ℝ^n) 1) /
              ((n : ℝ) - (n - 1 : ℝ) * q) *
            (2 * R) ^ ((n : ℝ) - (n - 1 : ℝ) * q))) ^ (1 / q) := by
      rw [lintegral_morreyKernel_rpow_ball_center hn hcritical
        (mul_pos zero_lt_two hR) x]
    _ = morreyKernelConstant n q *
          ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p) := by
      rw [hscale, ENNReal.ofReal_mul hconstNonneg]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le)]
      change morreyKernelConstant n q *
          (ENNReal.ofReal
            (R ^ ((n : ℝ) - (n - 1 : ℝ) * q))) ^ (1 / q) =
        morreyKernelConstant n q *
          ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p)
      congr 1
      rw [← ENNReal.ofReal_rpow_of_nonneg hR.le hbeta.le]
      rw [← ENNReal.rpow_mul, hexponent]

end MultidimensionalFinite

end SobolevSpace
