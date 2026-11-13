/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.DominatedData
public import PDE.Hyperbolic.NonlinearWave.CoercivePotential
import Mathlib.Analysis.ODE.Gronwall
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.Models.Wave.Equation
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import PDE.Hyperbolic.NonlinearWave.ZeroEnergyRigidity
import CAS.ExactTactic

/-!
# Stability and uniqueness for semilinear wave equations

We compare two classical solutions of

`uₜₜ - Δu + f(u) = 0`

when `f` is globally Lipschitz. For the difference `w = u - v`, the augmented
energy

`E(t) = 1 / 2 ∫ (wₜ² + |Dₓw|² + w²)`

satisfies `|E'(t)| ≤ (1 + K) E(t)`. Grönwall's inequality therefore gives
exponential stability and uniqueness from equal Cauchy data.

The quadratic term is an auxiliary coercive term for the difference, not a
primitive of the original nonlinearity.

The computation is the standard one: `w` solves `wₜₜ - Δw + w = w - (f(u) - f(v))`, so the
energy balance for the augmented energy has residual `wₜ (w - (f(u) - f(v)))`, and
`|f(u) - f(v)| ≤ K |w|` together with `2 |wₜ w| ≤ wₜ² + w²` bounds the residual density by
`(1 + K)` times the energy density. The solutions are classical (`C²` on spacetime), and the
differentiation of `E` under the spatial integral is justified by the domination hypotheses on the
energy time derivative and by compact support of the energy flux on each slice.

The augmented energy is the energy `e(t)` of the proof of Theorem 3 of Evans, §12.1.2, taken
over all of space. Evans proves uniqueness for Lipschitz nonlinearities in §12.2.1, Theorem 1,
by a contraction argument.

## Main results

* `abs_semilinearWaveEnergyBalanceResidual_sub_le`,
  `abs_integral_semilinearWaveEnergyBalanceResidual_sub_le`: the pointwise and integrated
  residual bounds `≤ (1 + K) E`.
* `semilinearWaveSpatialEnergy_sub_le_exp_abs`, `semilinearWaveSpatialEnergy_sub_le_exp`:
  `E(t) ≤ E(a) exp((1 + K) |t - a|)`, in both time directions and in forward form.
* `integral_semilinearWaveDifferenceCoerciveSum_le_exp_abs`: the same bound for
  `∫ (wₜ² + |Dₓw|² + w²)`, which is `2 E`.
* `semilinearWave_eq_of_eq_cauchyData`: uniqueness, `u = v`, from equal position and velocity
  data on one time slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 3 and its proof; §12.2.1, Theorem 1
  and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The quadratic auxiliary potential used to control a difference field is
continuously differentiable. -/
private theorem contDiff_quadratic_difference_potential :
    ContDiff ℝ 1 (fun z : ℝ ↦ z ^ 2 / 2) := by
  cas

/-- The quadratic auxiliary potential is nonnegative. -/
private theorem quadratic_difference_potential_nonneg (z : ℝ) :
    0 ≤ z ^ 2 / 2 := by
  positivity

/-- A nonnegative differentiable quantity whose derivative is bounded in
absolute value by `K` times the quantity grows by at most
`exp (K * |t - a|)` between arbitrary times `a` and `t`. -/
private theorem le_mul_exp_abs_of_abs_deriv_le {energy energy' : ℝ → ℝ} {K a t : ℝ}
    (hderiv : ∀ r, HasDerivAt energy (energy' r) r) (hnonneg : ∀ r, 0 ≤ energy r)
    (hbound : ∀ r, |energy' r| ≤ K * energy r) :
    energy t ≤ energy a * Real.exp (K * |t - a|) := by
  have forward {F F' : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r) (hF : ∀ s, HasDerivAt F (F' s) s)
      (h0 : ∀ s, 0 ≤ F s) (hb : ∀ s, |F' s| ≤ K * F s) : F r ≤ F l * Real.exp (K * (r - l)) := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (δ := F l) (K := K) (ε := 0)
      (continuous_iff_continuousAt.mpr fun s ↦ (hF s).continuousAt).continuousOn
      (fun s _ ↦ (hF s).hasDerivWithinAt) (by rw [Real.norm_of_nonneg (h0 l)])
      (fun s _ ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 s)] using hb s) r ⟨hlr, le_rfl⟩
    rwa [gronwallBound_ε0, Real.norm_of_nonneg (h0 r)] at h
  rcases le_total a t with hat | hta
  · simpa [abs_of_nonneg (sub_nonneg.mpr hat)] using forward hat hderiv hnonneg hbound
  have habs : |t - a| = -t - -a := by rw [abs_of_nonpos (sub_nonpos.mpr hta)]; ring
  have h := forward (F := fun r ↦ energy (-r)) (F' := fun r ↦ -energy' (-r)) (neg_le_neg hta)
    (fun r ↦ by simpa [Function.comp_def] using (hderiv (-r)).scomp r (hasDerivAt_neg r))
    (fun r ↦ hnonneg (-r)) fun r ↦ by simpa using hbound (-r)
  simpa [habs] using h

/-- The local energy residual of a difference is its time derivative times
the discrepancy between the difference and the nonlinear forcing. -/
theorem semilinearWaveEnergyBalanceResidual_sub_eq {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) {p : ℝ^(n + 1)}
    (huwave : waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : waveOperator (n := n) v p + f (v p) = 0) :
    semilinearWaveEnergyBalanceResidual (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun q ↦ u q - v q) p =
      (∂[0] (fun q ↦ u q - v q)) p * ((u p - v p) - (f (u p) - f (v p))) := by
  rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator
    (n := n) contDiff_quadratic_difference_potential (hu.sub hv).contDiffAt]
  unfold semilinearWaveOperator
  rw [waveOperator_sub (n := n) hu.contDiffAt hv.contDiffAt]
  rw [show ∀ z : ℝ, deriv (fun y : ℝ ↦ y ^ 2 / 2) z = z from fun z ↦ by cas]
  congr 1
  linarith

/-- A global Lipschitz bound controls the local residual of the difference by
`(1 + K)` times its augmented energy density. -/
theorem abs_semilinearWaveEnergyBalanceResidual_sub_le {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    {p : ℝ^(n + 1)} (huwave : waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : waveOperator (n := n) v p + f (v p) = 0) :
    |semilinearWaveEnergyBalanceResidual (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun q ↦ u q - v q) p| ≤
      (1 + (K : ℝ)) *
      semilinearWaveEnergyDensity (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun q ↦ u q - v q) p := by
  have hd : |f (u p) - f (v p)| ≤ K * |u p - v p| := by
    simpa [Real.dist_eq] using hf.dist_le_mul (u p) (v p)
  rw [semilinearWaveEnergyBalanceResidual_sub_eq hu hv huwave hvwave, abs_mul]
  unfold semilinearWaveEnergyDensity classicalWaveEnergyDensity
  dsimp only
  set a := (∂[0] fun q ↦ u q - v q) p
  set b := u p - v p
  have hbd : |b - (f (u p) - f (v p))| ≤ (1 + K) * |b| := by
    linarith [abs_sub b (f (u p) - f (v p))]
  have hbd := mul_le_mul_of_nonneg_left hbd (abs_nonneg a)
  rw [← sq_abs a, ← sq_abs b]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + K) (sq_nonneg (|a| - |b|)),
    mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + K)
      (sq_nonneg ‖classicalWaveSpatialGradient (fun q ↦ u q - v q) p‖)]

/-- The spatial integral of the difference residual is bounded by
`(1 + K)` times the augmented difference energy. -/
theorem abs_integral_semilinearWaveEnergyBalanceResidual_sub_le {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p, waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ p, waveOperator (n := n) v p + f (v p) = 0) (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t)) :
    |∫ x : ℝ^n,
      semilinearWaveEnergyBalanceResidual (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p)
      (PDE.Common.timeSpaceCons (n := n) t x)| ≤ (1 + (K : ℝ)) *
      semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t := by
  have h := norm_integral_le_of_norm_le (henergyIntegrable.const_mul (1 + (K : ℝ)))
    (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_semilinearWaveEnergyBalanceResidual_sub_le hf hu hv (huwave _) (hvwave _))
  rw [integral_const_mul] at h
  simpa [Real.norm_eq_abs, semilinearWaveSpatialEnergy] using h

/-- Equal position and velocity data give zero augmented difference energy
on the initial slice. -/
theorem semilinearWaveSpatialEnergy_sub_eq_zero_of_eq_cauchyData {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hposition : ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) =
      v (PDE.Common.timeSpaceCons (n := n) t x))
    (hvelocity : ∀ x : ℝ^n, (∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) t x)) :
    semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t = 0 := by
  let w : ℝ^(n + 1) → ℝ := fun p ↦ u p - v p
  have hw : ContDiff ℝ 2 w := hu.sub hv
  have hslice : (fun x : ℝ^n ↦ w (PDE.Common.timeSpaceCons (n := n) t x)) = 0 :=
    funext fun x ↦ sub_eq_zero.mpr (hposition x)
  have hdensity : semilinearWaveSpatialEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) w t = 0 := by
    funext x
    have hgradient : classicalWaveSpatialGradient w (PDE.Common.timeSpaceCons t x) = 0 := by
      ext i
      rw [classicalWaveSpatialGradient_apply, ← PDE.partialDeriv_timeSpaceCons_spatial i w t x
        (hw.differentiable (by norm_num)).differentiableAt, hslice]
      exact PDE.partialDeriv_const 0
    simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
      classicalWaveEnergyDensity, hgradient, w, PDE.partialDeriv_sub
        (hu.differentiable (by norm_num)).differentiableAt
        (hv.differentiable (by norm_num)).differentiableAt, hvelocity x, hposition x, sub_self]
    norm_num
  change (∫ x, semilinearWaveSpatialEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) w t x) = 0
  simp [hdensity]

/-- The augmented energy of two semilinear waves grows at most exponentially
with rate `1 + K` in either time direction. -/
theorem semilinearWaveSpatialEnergy_sub_le_exp_abs {K : NNReal} {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p, waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ p, waveOperator (n := n) v p + f (v p) = 0)
    (hE : DominatedEnergyData (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) univ) (a t : ℝ) :
    semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t ≤
      semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) a *
      Real.exp ((1 + (K : ℝ)) * |t - a|) :=
  le_mul_exp_abs_of_abs_deriv_le (fun r ↦
    hasDerivAt_semilinearWaveSpatialEnergy_eq_integral_balanceResidual
      contDiff_quadratic_difference_potential (.of_forall fun _ _ ↦ (hu.sub hv).contDiffAt)
      (hE.mem_nhds r (mem_univ r)) (hE.energy_integrable r (mem_univ r))
      (hE.dominated r (mem_univ r)) (hE.bound_integrable r (mem_univ r))
      (hE.flux_compact_support r (mem_univ r)))
    (fun r ↦ semilinearWaveSpatialEnergy_nonneg _ quadratic_difference_potential_nonneg _ r)
    fun r ↦ abs_integral_semilinearWaveEnergyBalanceResidual_sub_le hf hu hv huwave hvwave r
      (hE.energy_integrable r (mem_univ r))

/-- Exponential stability controls the full spatial difference norm: the
integral of the squared velocity, spatial gradient, and field difference is
bounded by twice the initial augmented energy times the Grönwall factor. -/
theorem integral_semilinearWaveDifferenceCoerciveSum_le_exp_abs {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p, waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ p, waveOperator (n := n) v p + f (v p) = 0)
    (hE : DominatedEnergyData (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) univ) (a t : ℝ) :
    (∫ x : ℝ^n, ((∂[0] (fun p ↦ u p - v p)) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      ‖classicalWaveSpatialGradient (n := n) (fun p ↦ u p - v p)
        (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
      (u (PDE.Common.timeSpaceCons (n := n) t x) - v (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      2 * semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) a *
      Real.exp ((1 + (K : ℝ)) * |t - a|) := by
  have hcoercive := semilinearWaveCoerciveEnergy_le_two_mul_spatialEnergy (fun z : ℝ ↦ z ^ 2 / 2)
    (1 / 2) (by norm_num) (fun z ↦ le_of_eq (by ring)) (hu.sub hv) t
    (hE.energy_integrable t (mem_univ t))
  simp only [semilinearWaveCoerciveEnergy, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    one_mul] at hcoercive
  linarith [semilinearWaveSpatialEnergy_sub_le_exp_abs hf hu hv huwave hvwave hE a t]

/-- Forward-time form of
`semilinearWaveSpatialEnergy_sub_le_exp_abs` when `a ≤ t`. -/
theorem semilinearWaveSpatialEnergy_sub_le_exp {K : NNReal} {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p, waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ p, waveOperator (n := n) v p + f (v p) = 0)
    (hE : DominatedEnergyData (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) univ) (a t : ℝ)
    (hat : a ≤ t) :
    semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t ≤
      semilinearWaveSpatialEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) a *
      Real.exp ((1 + (K : ℝ)) * (t - a)) := by
  simpa [abs_of_nonneg (sub_nonneg.mpr hat)] using
    semilinearWaveSpatialEnergy_sub_le_exp_abs
      (n := n) hf hu hv huwave hvwave hE a t

/-- Zero augmented difference energy forces equality on the corresponding
time slice. -/
theorem eq_on_timeSlice_of_semilinearWaveSpatialEnergy_sub_eq_zero
    {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v)
    (t : ℝ)
    (henergyIntegrable :
      Integrable
        (semilinearWaveSpatialEnergyDensity (n := n)
          (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t))
    (henergy :
      semilinearWaveSpatialEnergy (n := n)
        (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) t = 0) :
    ∀ x : ℝ^n,
      u (PDE.Common.timeSpaceCons (n := n) t x) =
        v (PDE.Common.timeSpaceCons (n := n) t x) := fun x ↦
  sub_eq_zero.mp (semilinearWave_eq_zero_on_timeSlice_of_spatialEnergy_eq_zero
    (u := fun p ↦ u p - v p) (fun z : ℝ ↦ z ^ 2 / 2)
    quadratic_difference_potential_nonneg (fun z hz ↦ by nlinarith [sq_nonneg z])
    (hu.sub hv).continuous t henergyIntegrable henergy x)

/-- Two classical semilinear waves with a common globally Lipschitz
nonlinearity and equal Cauchy data agree for all time. -/
theorem semilinearWave_eq_of_eq_cauchyData
    {K : NNReal} {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hf : LipschitzWith K f)
    (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v)
    (huwave :
      ∀ p, waveOperator (n := n) u p + f (u p) = 0)
    (hvwave :
      ∀ p, waveOperator (n := n) v p + f (v p) = 0)
    (hE : DominatedEnergyData (fun z : ℝ ↦ z ^ 2 / 2)
      (fun p ↦ u p - v p) univ)
    (a : ℝ)
    (hposition :
      ∀ x : ℝ^n,
        u (PDE.Common.timeSpaceCons (n := n) a x) =
          v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity :
      ∀ x : ℝ^n,
        (∂[0] u)
            (PDE.Common.timeSpaceCons (n := n) a x) =
          (∂[0] v)
            (PDE.Common.timeSpaceCons (n := n) a x)) :
    u = v := by
  funext p
  have hstable := semilinearWaveSpatialEnergy_sub_le_exp_abs hf hu hv huwave hvwave hE a (p 0)
  rw [semilinearWaveSpatialEnergy_sub_eq_zero_of_eq_cauchyData hu hv a hposition hvelocity,
    zero_mul] at hstable
  simpa only [PDE.Common.timeSpaceCons_spatialPart] using
    eq_on_timeSlice_of_semilinearWaveSpatialEnergy_sub_eq_zero hu hv (p 0)
      (hE.energy_integrable (p 0) (mem_univ (p 0))) (le_antisymm hstable
        (semilinearWaveSpatialEnergy_nonneg _ quadratic_difference_potential_nonneg _ (p 0)))
      (PDE.Common.spatialPart p)

end WaveEquation
