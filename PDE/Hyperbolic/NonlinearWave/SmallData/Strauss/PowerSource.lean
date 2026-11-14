/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential.Classical
import CAS.ExactTactic

/-!
# Regularity of the wave source `|s|^p` for `p ≥ 2`

For every real `p ≥ 2`, the nonlinearity `|s|^p` is `C²` across zero: it is `p` times the power
potential `Real.signedPowerPotential (p - 1)`, which is `C²` by
`Real.contDiff_two_signedPowerPotential`. At `p = 2` it is the polynomial `s²`. It supplies the
source regularity needed by the three-dimensional retarded Kirchhoff construction.

The signed power `|s|^(p-1) s` differs at `p = 2`, where it is `s |s|`:
`PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.contDiff_two_signedPower`
is for `p > 2`. Nothing is proved here about the exponents `p < 2`.
-/

@[expose] public noncomputable section

namespace WaveEquation.SmallData

/-- The absolute power source `x ↦ |x|^p` is `C²` on `ℝ` for every real exponent `p ≥ 2`. -/
theorem contDiff_two_abs_rpow {p : ℝ} (hp : 2 ≤ p) :
    ContDiff ℝ 2 (fun x : ℝ ↦ |x| ^ p) := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp).ne'
  rw [show (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * Real.signedPowerPotential (p - 1) x from
    funext fun x ↦ by rw [Real.signedPowerPotential, sub_add_cancel]; cas]
  exact contDiff_const.mul (Real.contDiff_two_signedPowerPotential (by cas using [hp]))

end WaveEquation.SmallData
