/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Two mollifications with an intervening multiplier

At a common continuity point of a locally integrable function and a measurable
multiplier, `Jη(b Jε f)` converges to `b f`. The kernels and positive scales may differ.
The inner convolution converges jointly in scale and position, which allows the
approximate identity theorem to be applied again to its varying output.

This gives pointwise normalization limits for localized Sobolev tests without
requiring any derivatives or global integrability of the function.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Two positive-scale mollifications separated by a measurable multiplier converge
at a common continuity point. Local integrability of the source suffices; neither
global boundedness nor a relation between the two scales is required. -/
theorem mollify_mul_mollify_tendsto_of_continuousAt
    (μ ν : Mollifier n) {f b : ℝ^n → ℝ}
    (hf : LocallyIntegrable f volume) (hb : AEStronglyMeasurable b volume)
    {x : ℝ^n} (hfx : ContinuousAt f x) (hbx : ContinuousAt b x)
    (ε η : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hη : ∀ m, 0 < η m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m ↦ mollify ν (η m) (fun y ↦ b y * mollify μ (ε m) f y) x)
      atTop (𝓝 (b x * f x)) := by
  have hjoint :
      Tendsto (fun p : ℕ × ℝ^n ↦ mollify μ (ε p.1) f p.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    have hconstant :
        Tendsto (Function.uncurry (fun _p : ℕ × ℝ^n ↦ f))
          ((atTop ×ˢ 𝓝 x) ×ˢ 𝓝 x) (𝓝 (f x)) :=
      hfx.tendsto.comp tendsto_snd
    simpa only [mollify, convolution] using
      (convolution_tendsto_right
        (μ := (volume : Measure (ℝ^n)))
        (g := fun _p : ℕ × ℝ^n ↦ f)
        (φ := fun p ↦ scaled μ (ε p.1)) (k := Prod.snd)
        (hnφ := Eventually.of_forall fun p y ↦ scaled_nonneg μ (hε p.1) y)
        (hiφ := Eventually.of_forall fun p ↦ scaled_integral_one μ (hε p.1))
        (hφ := (tendsto_support_scaled μ ε hε hε0).comp tendsto_fst)
        (hmg := Eventually.of_forall fun _ ↦ hf.aestronglyMeasurable)
        (hcg := hconstant) (hk := tendsto_snd))
  have hproduct :
      Tendsto (Function.uncurry (fun m y ↦ b y * mollify μ (ε m) f y))
        (atTop ×ˢ 𝓝 x) (𝓝 (b x * f x)) :=
    (hbx.tendsto.comp tendsto_snd).mul hjoint
  simpa only [mollify, convolution] using
    (convolution_tendsto_right
      (μ := (volume : Measure (ℝ^n)))
      (g := fun m y ↦ b y * mollify μ (ε m) f y)
      (φ := fun m ↦ scaled ν (η m)) (k := fun _m ↦ x)
      (hnφ := Eventually.of_forall fun m y ↦ scaled_nonneg ν (hη m) y)
      (hiφ := Eventually.of_forall fun m ↦ scaled_integral_one ν (hη m))
      (hφ := tendsto_support_scaled ν η hη hη0)
      (hmg := Eventually.of_forall fun m ↦
        hb.mul (mollify_contDiff_of_pos μ (hε m) f hf).continuous.aestronglyMeasurable)
      (hcg := hproduct) (hk := tendsto_const_nhds))

end SobolevSpace.Approximation
