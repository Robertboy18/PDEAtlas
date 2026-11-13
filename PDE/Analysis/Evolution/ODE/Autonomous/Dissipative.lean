/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Basic
public import PDE.Analysis.Evolution.Core.EnergyIdentity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Contraction and speed bounds for dissipative autonomous equations

Dissipativity contracts the distance between two classical trajectories. Applying this
to time translates and taking right difference quotients bounds every speed by the
initial speed. The vector field itself need not be differentiable.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A positive time translate of an autonomous half-line integral curve is again
an integral curve of the same field. -/
theorem isIntegralCurveOn_Ici_const_add {u : ℝ → H} {F : H → H}
    (hu : IsIntegralCurveOn u (fun _ ↦ F) (Ici 0)) {s : ℝ} (hs : 0 ≤ s) :
    IsIntegralCurveOn (fun t ↦ u (s + t)) (fun _ ↦ F) (Ici 0) := by
  intro t ht
  simpa only [Function.comp_def, one_smul] using
    (hu (s + t) (add_nonneg hs ht)).scomp t
      (((hasDerivAt_id t).const_add s).hasDerivWithinAt (s := Ici 0))
      (show MapsTo (fun r ↦ s + r) (Ici 0) (Ici 0) from
        fun r hr ↦ add_nonneg hs hr)

/-- Dissipativity contracts the distance between classical trajectories, including
their initial values at the closed endpoint. -/
theorem norm_sub_le_initial_of_dissipative
    {F : H → H} (hF : ∀ x y, inner ℝ (F x - F y) (x - y) ≤ 0)
    {u v : ℝ → H} (hu : IsIntegralCurveOn u (fun _ ↦ F) (Ici 0))
    (hv : IsIntegralCurveOn v (fun _ ↦ F) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u 0 - v 0‖ := by
  have hanti : AntitoneOn (fun r ↦ (1 / 2 : ℝ) * ‖u r - v r‖ ^ 2) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (continuousOn_const.mul ((hu.continuousOn.sub hv.continuousOn).norm.pow 2))
    · intro r hr
      exact (hasDerivWithinAt_half_norm_sq
        ((hu r (interior_subset hr)).sub (hv r (interior_subset hr)))).mono interior_subset
    · intro r _
      exact hF (u r) (v r)
  have h := hanti (by simp) ht ht
  nlinarith [norm_nonneg (u t - v t), norm_nonneg (u 0 - v 0)]

/-- The norm of the velocity of a dissipative autonomous trajectory never exceeds
its initial norm: `‖F (u t)‖ ≤ ‖F (u 0)‖` for `t ≥ 0`. The proof compares `u` with its
time translates and takes right difference quotients at `0`. -/
theorem norm_field_le_initial_of_dissipative
    {F : H → H} (hF : ∀ x y, inner ℝ (F x - F y) (x - y) ≤ 0)
    {u : ℝ → H} (hu : IsIntegralCurveOn u (fun _ ↦ F) (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖F (u t)‖ ≤ ‖F (u 0)‖ := by
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext r
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h ↦ lt_of_le_of_ne h.1 (Ne.symm h.2), fun h ↦ ⟨h.le, h.ne'⟩⟩
  have hleft := (hasDerivWithinAt_iff_tendsto_slope.1
    (isIntegralCurveOn_Ici_const_add hu ht 0 (by simp))).norm
  have hright := (hasDerivWithinAt_iff_tendsto_slope.1 (hu 0 (by simp))).norm
  simp only [hset, add_zero] at hleft hright
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with r hr
  have h := norm_sub_le_initial_of_dissipative hF
    (isIntegralCurveOn_Ici_const_add hu hr.le) hu ht
  simpa only [slope_def_module, sub_zero, add_zero, norm_smul, add_comm t r] using
    mul_le_mul_of_nonneg_left h (norm_nonneg r⁻¹)

/-- The initial velocity norm is a global Lipschitz constant for a dissipative
autonomous trajectory on the half-line. -/
theorem lipschitzOnWith_initial_speed_of_dissipative
    {F : H → H} (hF : ∀ x y, inner ℝ (F x - F y) (x - y) ≤ 0)
    {u : ℝ → H} (hu : IsIntegralCurveOn u (fun _ ↦ F) (Ici 0)) :
    LipschitzOnWith ‖F (u 0)‖₊ u (Ici 0) :=
  (convex_Ici 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hu
    (fun _ ht ↦ norm_field_le_initial_of_dissipative hF hu ht)

end PDE.Analysis.Evolution
