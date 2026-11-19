/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Almost-everywhere agreement under mollification

A convolution only samples the translated support of its kernel. Agreement
almost everywhere on that set therefore suffices, even when the functions have
unrelated values elsewhere. These identities require no integrability hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Changing a function on a null set leaves its mollification unchanged at every point.
No integrability assumption is needed for this equality of totalized convolution integrals. -/
theorem mollify_congr_ae (μ : Mollifier n) (ε : ℝ) {f g : ℝ^n → ℝ}
    (hfg : f =ᵐ[volume] g) : mollify μ ε f = mollify μ ε g :=
  convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) EventuallyEq.rfl hfg

/-- Local a.e. equality suffices for equality of convolution wherever the
translated kernel support stays in that local set. No integrability is needed
for this equality of totalized integrals. -/
theorem mollify_congr_ae_on_collar (μ : Mollifier n) (ε : ℝ)
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) {f g : ℝ^n → ℝ}
    (hfg : f =ᵐ[volume.restrict Ω] g) {x : ℝ^n}
    (hcollar : ∀ y ∈ Function.support (scaled μ ε), x - y ∈ Ω) :
    mollify μ ε f x = mollify μ ε g x := by
  have hswap (v : ℝ^n → ℝ) :
      mollify μ ε v x = ∫ y, scaled μ ε (x - y) * v y := by
    simpa only [mollify, convolution_lsmul_eq_mul] using
      (convolution_mul_swap (μ := volume) (x := x) (f := scaled μ ε) (g := v))
  rw [hswap, hswap]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ).mp hfg] with y hy
  by_cases hk : scaled μ ε (x - y) = 0
  · simp only [hk, zero_mul]
  · have hyΩ : y ∈ Ω := by simpa only [sub_sub_cancel] using hcollar (x - y) hk
    rw [hy hyΩ]

/-- If the mollifier ball lies in the domain, almost-everywhere agreement there
is enough to identify the two mollifications at its center. -/
theorem mollify_eq_of_ae_on (μ : Mollifier n) {ε R : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ closedBall (0 : ℝ^n) R)
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) {f g : ℝ^n → ℝ}
    (hfg : f =ᵐ[volume.restrict Ω] g) {x : ℝ^n}
    (hball : closedBall x (ε * R) ⊆ Ω) :
    mollify μ ε f x = mollify μ ε g x := by
  apply mollify_congr_ae_on_collar μ ε hΩ hfg
  intro y hy
  apply hball
  simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, sub_zero]
    using support_scaled_subset_closedBall μ hε hR hy

end SobolevSpace.Approximation
