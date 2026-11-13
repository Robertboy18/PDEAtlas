/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Uniqueness.Weak
public import PDE.Parabolic.Quasilinear.GradientFlow.Solution

/-!
# Contraction for nonlinear gradient diffusion

Let `Ω` be a bounded open set and let `L` be `C²` with `θ‖v‖² ≤ D²L(x)(v, v)` for some `θ > 0` and
`‖D²L(x)‖ ≤ C`. At every time `t ≥ 0` the `L²` distance between two weak Dirichlet solutions is at
most the distance between their initial values (`norm_sub_le_initial`). Equal initial data therefore
give equal trajectories at every `t ≥ 0` (`eqOn_of_initial_eq`) and almost everywhere equal weak
velocities (`velocity_ae_eq_of_initial_eq`).

This is the uniqueness part of Evans's §9.6.2, Theorem 3, and the contraction estimate of his
Remark (i) after the proof, for the problem (33) of §9.6.3. As in Evans's recasting of (33) as (34),
weak solutions are subgradient flows of the Dirichlet energy
(`isWeakSolution_iff_isSubgradientFlow`); uniform convexity makes the flux monotone, and the
contraction estimate for subgradient flows in a Hilbert space applies.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, Theorem 3 (Solution of gradient flow), (15)-(16),
  p. 566, step 6 of its proof and Remark (i), p. 570; §9.6.3, (33)-(34), pp. 572-573.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Quasilinear.GradientFlow.IsWeakSolution

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CalculusOfVariations
open scoped NNReal

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}
  {u v g h : ℝ → (ℝ^n →₂[domainMeasure n Ω] ℝ)}

/-- At every time `t ≥ 0` the `L²` distance between two weak solutions is at most the
distance between their initial values. -/
theorem norm_sub_le_initial
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (hu : IsWeakSolution L u g) (hv : IsWeakSolution L v h)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u 0 - v 0‖ := by
  have hu' := (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper u g).mp hu
  have hv' := (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper v h).mp hv
  exact hu'.norm_sub_le_initial (isProper_l2DirichletGradientEnergy L) hv' ht

/-- Equal initial data give equal weak trajectories at every nonnegative time. -/
theorem eqOn_of_initial_eq
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (hu : IsWeakSolution L u g) (hv : IsWeakSolution L v h)
    (h0 : u 0 = v 0) : EqOn u v (Ici 0) := by
  intro t ht
  have hbound := hu.norm_sub_le_initial hΩ hbounded hL hθ hlower hupper hv ht
  rw [h0, sub_self, norm_zero] at hbound
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)

/-- The weak velocities agree almost everywhere when the initial data agree. -/
theorem velocity_ae_eq_of_initial_eq
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (hu : IsWeakSolution L u g) (hv : IsWeakSolution L v h)
    (h0 : u 0 = v 0) : g =ᵐ[volume.restrict (Ioi 0)] h := by
  have hu' := (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper u g).mp hu
  have hv' := (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper v h).mp hv
  exact hu'.velocity_ae_eq_of_initial_eq
    (isProper_l2DirichletGradientEnergy L) hv' h0

end PDE.Parabolic.Quasilinear.GradientFlow.IsWeakSolution
