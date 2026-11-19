/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# L² pairings with a localized coefficient

A coefficient need only be square integrable on the support of the other
factor. Its indicator extension gives the same integrable product and the
same Hilbert-space pairing. No global integrability of the coefficient is
required.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Set
open scoped RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- A locally square integrable coefficient pairs integrably with an L²
function supported almost everywhere in the localization set. -/
theorem integrable_mul_of_memLp_indicator {f v : α → ℝ}
    (hf : MemLp (s.indicator f) 2 μ) (hv : MemLp v 2 μ)
    (hsupp : s.indicator v =ᵐ[μ] v) :
    Integrable (fun x ↦ f x * v x) μ := by
  apply (hf.integrable_mul hv).congr
  filter_upwards [hsupp] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs]
  · have hvzero : v x = 0 := by simpa [hxs] using hx.symm
    simp [hxs, hvzero]

/-- The L² element defined by an indicator coefficient has the original
integral pairing against every L² function supported in that set. -/
theorem inner_toLp_indicator_eq_integral_mul {f : α → ℝ}
    (hf : MemLp (s.indicator f) 2 μ) (v : Lp ℝ 2 μ)
    (hsupp : s.indicator (v : α → ℝ) =ᵐ[μ] v) :
    ⟪hf.toLp (s.indicator f), v⟫ = ∫ x, f x * v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hsupp] with x hfx hvx
  rw [hfx]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hxs : x ∈ s
  · simp [hxs, mul_comm]
  · have hvzero : v x = 0 := by simpa [hxs] using hvx.symm
    simp [hxs, hvzero]

end MeasureTheory
