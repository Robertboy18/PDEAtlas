/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Basic
public import PDE.Analysis.Evolution.Semigroup.Generator
import PDE.Analysis.Calculus.StrongOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Variation of constants for a semigroup generator

For a classical forced trajectory, differentiate `T(b-s)u(s)` on the interior
of the time interval. The two generator terms cancel, leaving the propagated
forcing. The fundamental theorem of calculus gives Duhamel's formula.

The generator can be unbounded. Only strong continuity of the semigroup and
continuity of the forcing and trajectory on the given interval are used.

For a vector `x` of the generator domain with `Ax = μx + f`, the exponential trajectory
`t ↦ e^{μt} x` is classical with forcing `-e^{μt} f`, so
`e^{μt} x = T(t) x - ∫₀ᵗ e^{μs} T(t - s) f ds`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A classical solution of `u' = Au + f` satisfies variation of constants on any
finite interval. Generator-domain membership and differentiation are needed only
in its interior; the trajectory and forcing are continuous up to both endpoints. -/
theorem eq_orbit_add_integral_of_hasDerivWithinAt (T : StronglyContinuousSemigroup E)
    {u Au f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hA : ∀ s ∈ Ioo a b, T.HasGeneratorAt (u s) (Au s))
    (hd : ∀ s ∈ Ioo a b, HasDerivWithinAt u (Au s + f s) (Icc a b) s) :
    u b = T (b - a).toNNReal (u a) +
      ∫ s in a..b, T (b - s).toNNReal (f s) := by
  let v : ℝ → E := fun s ↦ T (b - s).toNNReal (u s)
  have hv : ContinuousOn v (Icc a b) :=
    T.continuous_apply.comp_continuousOn
      ((continuous_real_toNNReal.comp
        (continuous_const.sub continuous_id)).continuousOn.prodMk hu)
  have hg : ContinuousOn (fun s ↦ T (b - s).toNNReal (f s)) (Icc a b) :=
    T.continuous_apply.comp_continuousOn
      ((continuous_real_toNNReal.comp
        (continuous_const.sub continuous_id)).continuousOn.prodMk hf)
  have hvd (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt v (T (b - s).toNNReal (f s)) s := by
    have hfixed : HasDerivAt (fun r ↦ T (b - r).toNNReal (u s))
        (-T (b - s).toNNReal (Au s)) s := by
      simpa only [Function.comp_def, neg_smul, one_smul, realOrbit] using
        ((hA s hs).hasDerivAt_realOrbit (sub_pos.mpr hs.2)).scomp s
          ((hasDerivAt_id s).const_sub b)
    have haction : Continuous (fun p : ℝ × E ↦ T (b - p.1).toNNReal p.2) :=
      T.continuous_apply.comp
        ((continuous_real_toNNReal.comp
          (continuous_const.sub continuous_fst)).prodMk continuous_snd)
    have hproduct := PDE.Analysis.hasDerivWithinAt_clm_apply_of_continuousAt
      haction.continuousAt hfixed.hasDerivWithinAt (hd s hs)
    have hwithin : HasDerivWithinAt v (T (b - s).toNNReal (f s)) (Icc a b) s := by
      simpa only [ContinuousLinearMap.map_add, neg_add_cancel_left] using hproduct
    exact hwithin.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hv hvd
    (hg.intervalIntegrable_of_Icc hab)
  simp only [v, sub_self, Real.toNNReal_zero, map_zero_apply] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- Variation of constants for an exponential trajectory: if `x` lies in the generator domain
with `A x = μ x + f`, then `e^{μt} x = T(t) x - ∫₀ᵗ e^{μs} T(t - s) f ds` for `t ≥ 0`. -/
theorem exp_smul_eq_sub_integral_of_hasGeneratorAt (T : StronglyContinuousSemigroup E)
    {x f : E} {μ : ℝ} (hx : T.HasGeneratorAt x (μ • x + f)) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (μ * t) • x =
      T t.toNNReal x - ∫ s in (0 : ℝ)..t, Real.exp (μ * s) • T (t - s).toNNReal f := by
  have hd (s : ℝ) : HasDerivAt (fun r ↦ Real.exp (μ * r) • x)
      (Real.exp (μ * s) • (μ • x + f) + -(Real.exp (μ * s) • f)) s := by
    have h := ((Real.hasDerivAt_exp (μ * s)).comp s
      ((hasDerivAt_id s).const_mul μ)).smul_const x
    convert h using 1
    · rfl
    · rw [smul_add, add_neg_cancel_right, smul_smul, mul_one]
  have h := T.eq_orbit_add_integral_of_hasDerivWithinAt
    (u := fun s ↦ Real.exp (μ * s) • x) (Au := fun s ↦ Real.exp (μ * s) • (μ • x + f))
    (f := fun s ↦ -(Real.exp (μ * s) • f)) ht (by fun_prop) (by fun_prop)
    (fun s _ ↦ hx.smul _) (fun s _ ↦ (hd s).hasDerivWithinAt)
  simp only [mul_zero, Real.exp_zero, one_smul, sub_zero, map_neg, map_smul] at h
  rw [h, intervalIntegral.integral_neg, sub_eq_add_neg]

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
