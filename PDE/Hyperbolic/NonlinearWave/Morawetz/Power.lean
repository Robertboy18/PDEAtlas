/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Balance
public import PDE.Analysis.Calculus.PowerPotential
import PDE.Analysis.Calculus.PowerPotential.Classical
import CAS.ExactTactic

/-!
# Power potentials in the Morawetz identity

The general power potential makes the bulk coefficient explicit. For the
quintic equation in three dimensions it is negative, giving `-u⁶/3`.
This is the differential identity behind the cone nonconcentration estimate;
the integration over the cone is a separate step.

The quintic case is the identity (6) of the proof of Evans, §12.4, Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equations (6)-(8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- For a real power nonlinearity, the bulk term has an explicit coefficient.
This includes nonintegral powers and zero values of the field. -/
theorem morawetzCurrent_balance_power {r : ℝ} (hr : 1 ≤ r) (c : ℝ^(n + 1))
    {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (scalingCurrentDensity (Real.signedPowerPotential r)
      (((n : ℝ) - 1) / 2) c u)) p -
      (∑ i : Fin n, (∂[i.succ] (scalingCurrentFlux (Real.signedPowerPotential r)
        (((n : ℝ) - 1) / 2) c u i)) p) =
        scalingMultiplier (((n : ℝ) - 1) / 2) c u p *
            semilinearWaveOperator (Real.signedPowerPotential r) u p +
          (((n : ℝ) + 1) / (r + 1) - ((n : ℝ) - 1) / 2) * |u p| ^ (r + 1) := by
  calc
    _ = scalingMultiplier (((n : ℝ) - 1) / 2) c u p *
          semilinearWaveOperator (Real.signedPowerPotential r) u p +
        ((n : ℝ) + 1) * Real.signedPowerPotential r (u p) -
          ((n : ℝ) - 1) / 2 * u p * deriv (Real.signedPowerPotential r) (u p) :=
      morawetzCurrent_balance c (Real.contDiff_one_signedPowerPotential hr).contDiffAt hu
    _ = _ := by
      rw [(Real.hasDerivAt_signedPowerPotential hr (u p)).deriv,
        mul_assoc (((n : ℝ) - 1) / 2), Real.mul_signedPower_eq_abs_rpow hr]
      unfold Real.signedPowerPotential
      cas

/-- In three dimensions, the quintic equation leaves the negative density
`-|u|⁶/3`. The wave residual remains explicit, so the identity can also be used
when the field satisfies a forced equation. -/
theorem morawetzCurrent_balance_quintic (c : ℝ^(3 + 1))
    {u : ℝ^(3 + 1) → ℝ} {p : ℝ^(3 + 1)} (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (scalingCurrentDensity (Real.signedPowerPotential 5) 1 c u)) p -
      (∑ i : Fin 3, (∂[i.succ]
        (scalingCurrentFlux (Real.signedPowerPotential 5) 1 c u i)) p) =
        scalingMultiplier 1 c u p * semilinearWaveOperator (Real.signedPowerPotential 5) u p -
          u p ^ 6 / 3 := by
  have h := morawetzCurrent_balance_power (n := 3) (r := 5) (by norm_num) c hu
  norm_num only [Nat.cast_ofNat] at h
  have hp : |u p| ^ (6 : ℝ) = u p ^ 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast]
    exact (show Even 6 by decide).pow_abs _
  rw [hp] at h
  calc
    _ = _ := h
    _ = _ := by cas

end WaveEquation
