/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.WeakEvolution
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hilbert-space energy identities

For a differentiable trajectory `u` in a real Hilbert space `V`, the energy
`E(t) = ½ ‖u(t)‖²` has derivative `⟪u'(t), u(t)⟫`.  If moreover `u` satisfies
the weak evolution equation `⟪u', v⟫ + B(u, v) = ℓ(v)` for every `v ∈ V`,
testing with `v = u(t)` gives the pointwise energy identity
`E'(t) = ℓ(u(t)) - B(u(t), u(t))`. The squared norm of an absolutely
continuous trajectory is absolutely continuous, which gives integrated energy
identities for trajectories that are not differentiable everywhere.

Everything here concerns trajectories that are strongly differentiable in `V`
(the situation of Galerkin approximants) and pairs the derivative through the
inner product of `V`.  The integrated `V*`--`V` pairing identity for
`u ∈ L²(0,T;V)` with `u' ∈ L²(0,T;V*)`, which is the setting of Evans's
Chapter 7 and of Lions–Magenes, is in the `LionsMagenes` modules.

## Main results

* `absolutelyContinuousOnInterval_norm_sq`: `‖w‖²` is absolutely continuous
  when `w` is.
* `hasDerivAt_half_norm_sq`, `hasDerivWithinAt_half_norm_sq`: derivatives of
  `½ ‖u‖²`.
* `weakEvolution_energy_identity`: the pointwise energy identity for a
  `V`-differentiable weak evolution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 2, equation (21) (the identity
  for Galerkin approximants), and §5.9.2, Theorem 3 (the `H⁻¹`-`H¹₀` version).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
The squared norm of an absolutely continuous normed-space trajectory is
absolutely continuous on the same compact interval: the norm is `1`-Lipschitz and
products of absolutely continuous real functions are absolutely continuous.
-/
theorem absolutelyContinuousOnInterval_norm_sq
    {H : Type*} [NormedAddCommGroup H]
    {w : ℝ → H} {a b : ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ‖w t‖ ^ 2) a b := by
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hw
  exact (hn.mul hn).congr fun t _ ↦ (pow_two _).symm

/-- Time derivative of the Hilbert energy `1/2 ‖u(t)‖²`. -/
theorem hasDerivAt_half_norm_sq
    {u : ℝ → V} {du : V} {t : ℝ} (hu : HasDerivAt u du t) :
    HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖u s‖ ^ 2) (inner ℝ du (u t)) t := by
  have h := hu.norm_sq.const_mul (1 / 2 : ℝ)
  convert h using 1
  rw [real_inner_comm]
  ring

/-- Time derivative of `1/2 ‖u(t)‖²` within a set `s`, such as a closed time
interval. -/
theorem hasDerivWithinAt_half_norm_sq
    {u : ℝ → V} {du : V} {t : ℝ} {s : Set ℝ}
    (hu : HasDerivWithinAt u du s t) :
    HasDerivWithinAt (fun r ↦ (1 / 2 : ℝ) * ‖u r‖ ^ 2)
      (inner ℝ du (u t)) s t := by
  have h := hu.norm_sq.const_mul (1 / 2 : ℝ)
  convert h using 1
  rw [real_inner_comm]
  ring

/-- Pointwise energy identity for a `V`-differentiable trajectory of an
abstract weak evolution equation.  Testing `⟪u', v⟫ + B(u, v) = ℓ(v)` with
`v = u(t)` gives `E'(t) = ℓ(u(t)) - B(u(t), u(t))` for `E = ½ ‖u‖²`.  The
derivative `du` lies in `V` and is paired through the inner product of `V`. -/
theorem weakEvolution_energy_identity
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    {u : ℝ → V} {du : V} {t : ℝ}
    (hu : HasDerivAt u du t)
    (heq : SatisfiesWeakEvolutionAt B ell (u t) du) :
    HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖u s‖ ^ 2)
      (ell (u t) - B (u t) (u t)) t := by
  have henergy := hasDerivAt_half_norm_sq hu
  have htest := heq (u t)
  convert henergy using 1
  linarith

end PDE.Analysis.Evolution
