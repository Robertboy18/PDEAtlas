/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.FDeriv.PartialDeriv

/-!
# First derivatives outside a forward support cone

A field with speed-one support is zero in a spacetime neighborhood outside each
preterminal common support ball. Consequently every coordinate derivative is zero
there, including the time derivative. No differentiability or equation is assumed.
-/

@[expose] public noncomputable section

open Set Filter PDE PDE.Common
open scoped Topology

namespace PDE.Analysis

/-- Every first derivative vanishes outside the common preterminal support ball.
The proof uses a spacetime neighborhood, including for the time derivative. -/
theorem partialDeriv_eq_zero_of_forward_support
    {n : ℕ} {u : ℝ^(n + 1) → ℝ} {T R t : ℝ}
    (hsupport : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^n,
      R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (ht : t ∈ Ioo 0 T) (i : Fin (n + 1)) {x : ℝ^n} (hx : R + T < ‖x‖) :
    (∂[i] u) (timeSpaceCons t x) = 0 := by
  have hopen : IsOpen {p : ℝ^(n + 1) | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hspace : IsOpen {p : ℝ^(n + 1) | R + T < ‖(timeSpaceContinuousLinearEquiv n p).2‖} :=
    isOpen_lt continuous_const (timeSpaceContinuousLinearEquiv n).continuous.snd.norm
  have he : u =ᶠ[𝓝 (timeSpaceCons t x)] fun _ ↦ 0 := by
    filter_upwards [hopen.mem_nhds (by simpa using ht),
      hspace.mem_nhds (by simpa using hx)] with p hp hpx
    have hq := hsupport (p 0) hp ((timeSpaceContinuousLinearEquiv n p).2)
      (by linarith [hp.2])
    simpa only [timeSpaceContinuousLinearEquiv_apply, timeSpaceCons_spatialPart] using hq
  unfold partialDeriv
  rw [he.fderiv_eq, fderiv_fun_const]
  rfl

end PDE.Analysis
