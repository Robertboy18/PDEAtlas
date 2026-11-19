/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
import PDE.FDeriv.Calculus

/-!
# The scaling current for a semilinear wave

The dilation derivative about a spacetime point combines with the kinetic
Lagrangian to give a density and spatial flux. We keep the amplitude weight
free so the same current can be used in every spatial dimension.

For `n = 3`, weight `a = 1` and potential `V(u) = u⁶/6`, the multiplier is the
`m = (t - T)u_t + x · Du + u` of the proof of Evans, §12.4, Theorem 2, with the vertex
`(x₀, T) = (0, T)`, and the density and flux are the `p` and `q` of (7) and (8).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equations (7)-(8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- The kinetic Lagrangian minus the potential: `(uₜ²-|Dₓu|²)/2-V(u)`. -/
def waveLagrangianDensity (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) : ℝ :=
  ((∂[0] u) p ^ 2 - ∑ i : Fin n, (∂[i.succ] u) p ^ 2) / 2 - V (u p)

/-- The dilation derivative about `c`, with an amplitude weight `a`. -/
def scalingMultiplier (a : ℝ) (c : ℝ^(n + 1)) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) : ℝ :=
  (∑ j : Fin (n + 1), (p j - c j) * (∂[j] u) p) + a * u p

/-- Time component of the scaling current, with energy-current sign convention. -/
def scalingCurrentDensity (V : ℝ → ℝ) (a : ℝ) (c : ℝ^(n + 1))
    (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  scalingMultiplier a c u p * (∂[0] u) p -
    (p 0 - c 0) * waveLagrangianDensity V u p

/-- Spatial flux component of the scaling current. Its divergence is subtracted
from the time derivative of the density. -/
def scalingCurrentFlux (V : ℝ → ℝ) (a : ℝ) (c : ℝ^(n + 1))
    (u : ℝ^(n + 1) → ℝ) (i : Fin n) (p : ℝ^(n + 1)) : ℝ :=
  scalingMultiplier a c u p * (∂[i.succ] u) p +
    (p i.succ - c i.succ) * waveLagrangianDensity V u p

/-- The Lagrangian is C¹ wherever the field is C² and the potential is C¹. -/
theorem contDiffAt_waveLagrangianDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) :
    ContDiffAt ℝ 1 (waveLagrangianDensity V u) p := by
  have hpartial (j : Fin (n + 1)) := PDE.contDiffAt_partialDeriv 1 hu j
  exact (((hpartial 0).pow 2).sub (ContDiffAt.sum fun j _ ↦
    (hpartial j.succ).pow 2)).div_const 2 |>.sub (hV.comp p (hu.of_le (by norm_num)))

/-- A C² field gives a C¹ dilation multiplier. -/
theorem contDiffAt_scalingMultiplier (a : ℝ) (c : ℝ^(n + 1))
    {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u p) :
    ContDiffAt ℝ 1 (scalingMultiplier a c u) p :=
  (ContDiffAt.sum fun j _ ↦ (((EuclideanSpace.proj j : ℝ^(n + 1) →L[ℝ] ℝ).contDiff.contDiffAt).sub
      contDiffAt_const).mul (PDE.contDiffAt_partialDeriv 1 hu j)).add
        (contDiffAt_const.mul (hu.of_le (by norm_num)))

/-- The density of the scaling current is C¹ wherever its field is C². -/
theorem contDiffAt_scalingCurrentDensity {V : ℝ → ℝ} (a : ℝ) (c : ℝ^(n + 1)) {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) :
    ContDiffAt ℝ 1 (scalingCurrentDensity V a c u) p :=
  ((contDiffAt_scalingMultiplier a c hu).mul (PDE.contDiffAt_partialDeriv 1 hu 0)).sub
      ((((EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ).contDiff.contDiffAt).sub
        contDiffAt_const).mul (contDiffAt_waveLagrangianDensity hV hu))

/-- Each spatial flux component is C¹ under the same local assumptions. -/
theorem contDiffAt_scalingCurrentFlux {V : ℝ → ℝ} (a : ℝ) (c : ℝ^(n + 1)) {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) (i : Fin n) :
    ContDiffAt ℝ 1 (scalingCurrentFlux V a c u i) p :=
  ((contDiffAt_scalingMultiplier a c hu).mul (PDE.contDiffAt_partialDeriv 1 hu i.succ)).add
      ((((EuclideanSpace.proj i.succ : ℝ^(n + 1) →L[ℝ] ℝ).contDiff.contDiffAt).sub
        contDiffAt_const).mul (contDiffAt_waveLagrangianDensity hV hu))

end WaveEquation
