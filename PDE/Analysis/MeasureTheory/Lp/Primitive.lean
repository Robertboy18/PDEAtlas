/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PDE.Analysis.Calculus.Primitive.Bounded

/-!
# Continuity of interval primitives in L²

Integrating over a fixed bounded interval is a continuous linear functional
on L². Writing it as the difference of two indicator pairings also covers
reversed endpoints. In particular, convergence of a velocity derivative
determines the pointwise limit of its primitive normalized at zero.
The normalized primitive is also continuous in space; an almost-everywhere
bound on its integrand gives a global Lipschitz constant.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- An oriented interval integral is the difference of two L² pairings. -/
theorem intervalIntegral_eq_inner_indicator_sub (a b : ℝ)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (∫ x in a..b, f x) =
      inner ℝ (indicatorConstLp 2 (s := Ioc a b) measurableSet_Ioc
        (by simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])
        (1 : ℝ)) f -
        inner ℝ (indicatorConstLp 2 (s := Ioc b a) measurableSet_Ioc
          (by simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])
          (1 : ℝ)) f := by
  rw [L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one]
  rfl

/-- Strong L² convergence passes to the integral over every fixed interval. -/
theorem tendsto_intervalIntegral_of_tendsto_L2
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ 2 (volume : Measure ℝ)} {g : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : Tendsto f l (𝓝 g)) (a b : ℝ) :
    Tendsto (fun i ↦ ∫ x in a..b, f i x) l (𝓝 (∫ x in a..b, g x)) := by
  simp_rw [intervalIntegral_eq_inner_indicator_sub]
  exact (tendsto_const_nhds.inner hf).sub (tendsto_const_nhds.inner hf)

end MeasureTheory

namespace PDE.Analysis

/-- The real interval primitive normalized to vanish at the origin. -/
def l2Primitive (f : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  ∫ s in 0..x, f s

private theorem intervalIntegrable_l2 (f : Lp ℝ 2 (volume : Measure ℝ)) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact
    isCompact_uIcc |>.intervalIntegrable

/-- For every fixed endpoint, the interval primitive is continuous
in the L² topology. -/
theorem continuous_l2Primitive_apply (x : ℝ) :
    Continuous (fun f : Lp ℝ 2 (volume : Measure ℝ) ↦ l2Primitive f x) := by
  exact continuous_iff_continuousAt.mpr fun _ ↦
    tendsto_intervalIntegral_of_tendsto_L2 tendsto_id 0 x

/-- The normalized primitive is continuous in the spatial endpoint. -/
theorem continuous_l2Primitive (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Continuous (l2Primitive f) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_l2 f) 0

/-- An almost-everywhere bound on an L² class bounds the spatial Lipschitz
constant of its normalized interval primitive. -/
theorem lipschitzWith_l2Primitive_of_ae_bound
    (f : Lp ℝ 2 (volume : Measure ℝ)) (K : NNReal)
    (hK : ∀ᵐ x ∂volume, ‖f x‖ ≤ K) :
    LipschitzWith K (l2Primitive f) := by
  exact lipschitzWith_intervalIntegral_of_ae_bound
    ((Lp.memLp f).locallyIntegrable (by norm_num)) hK 0

end PDE.Analysis
