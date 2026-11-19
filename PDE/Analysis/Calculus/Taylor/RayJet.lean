/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Jets along a ray from a little-o bound

A function that is `o(s²)` as `s → 0⁺` and twice differentiable on `(0, δ)` has first and second
derivatives with limit zero at `0⁺`, whenever those limits exist: by l'Hôpital's rule `h(s)/s`
tends to the limit of `h'` and `h(s)/s²` to half the limit of `h''`, while both quotients tend to
zero. Along a ray `s ↦ s • v` this identifies the limits of the first and second derivatives of a
function in the direction `v` from a little-o bound, without differentiability at the vertex of the
ray. It is the uniqueness of second-order Taylor coefficients used for functions that are smooth
only on an open set whose closure contains the vertex.

## Main results

* `PDE.Analysis.tendsto_deriv_eq_zero_of_isLittleO_sq`: the one-dimensional statement.
* `PDE.Analysis.tendsto_fderiv_eq_zero_of_isLittleO_sq`: the statement along a ray.
-/

@[expose] public section

noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace PDE.Analysis

/-- If `h = o(s²)` as `s → 0⁺`, `h` is twice differentiable on `(0, δ)` and `h'`, `h''` have the
limits `a₁`, `a₂` at `0⁺`, then `a₁ = 0` and `a₂ = 0`. -/
theorem tendsto_deriv_eq_zero_of_isLittleO_sq {h h' h'' : ℝ → ℝ} {δ a₁ a₂ : ℝ} (hδ : 0 < δ)
    (hd : ∀ s ∈ Ioo 0 δ, HasDerivAt h (h' s) s) (hd' : ∀ s ∈ Ioo 0 δ, HasDerivAt h' (h'' s) s)
    (h1 : Tendsto h' (𝓝[>] 0) (𝓝 a₁)) (h2 : Tendsto h'' (𝓝[>] 0) (𝓝 a₂))
    (ho : h =o[𝓝[>] 0] fun s ↦ s ^ 2) : a₁ = 0 ∧ a₂ = 0 := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have hsq : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h0 : Tendsto h (𝓝[>] 0) (𝓝 0) := ho.trans_tendsto hsq
  -- `h(s)/s → a₁` by l'Hôpital and `h(s)/s → 0` from the bound
  have hq1 : Tendsto (fun s ↦ h s / s) (𝓝[>] 0) (𝓝 a₁) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (f' := h') (g' := fun _ ↦ 1)
      (hev.mono fun s hs ↦ hd s hs) (Eventually.of_forall fun s ↦ hasDerivAt_id s)
      (Eventually.of_forall fun _ ↦ one_ne_zero) h0 hid ?_
    simpa using h1
  have hq1' : Tendsto (fun s ↦ h s / s) (𝓝[>] 0) (𝓝 0) := by
    have ho1 : h =o[𝓝[>] 0] fun s ↦ s := by
      refine ho.trans_isBigO ?_
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs
      rw [norm_pow, one_mul, Real.norm_eq_abs, abs_of_pos hs.1]
      nlinarith [hs.1, hs.2]
    exact ho1.tendsto_div_nhds_zero
  have ha₁ : a₁ = 0 := tendsto_nhds_unique hq1 hq1'
  refine ⟨ha₁, ?_⟩
  -- `h'(s)/(2 s) → a₂/2` and then `h(s)/s² → a₂/2`
  have hq2 : Tendsto (fun s ↦ h' s / (2 * s)) (𝓝[>] 0) (𝓝 (a₂ / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (f' := h'') (g' := fun _ ↦ 2)
      (hev.mono fun s hs ↦ hd' s hs)
      (Eventually.of_forall fun s ↦ by simpa using (hasDerivAt_id s).const_mul (2 : ℝ))
      (Eventually.of_forall fun _ ↦ two_ne_zero) (ha₁ ▸ h1) ?_ ?_
    · simpa using hid.const_mul (2 : ℝ)
    · exact h2.div_const 2
  have hq3 : Tendsto (fun s ↦ h s / s ^ 2) (𝓝[>] 0) (𝓝 (a₂ / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (f' := h') (g' := fun s ↦ 2 * s)
      (hev.mono fun s hs ↦ hd s hs)
      (Eventually.of_forall fun s ↦ by simpa using hasDerivAt_pow 2 s)
      (hev.mono fun s hs ↦ by have := hs.1; positivity) h0 hsq hq2
  have hq3' : Tendsto (fun s ↦ h s / s ^ 2) (𝓝[>] 0) (𝓝 0) := ho.tendsto_div_nhds_zero
  have := tendsto_nhds_unique hq3 hq3'
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Jets along a ray.** If `g` is `C²` at the points `s • v`, `0 < s < δ`, the first and
second derivatives of `g` in the direction `v` have the limits `a₁`, `a₂` along the ray, and
`g(s • v) = o(s²)` as `s → 0⁺`, then `a₁ = 0` and `a₂ = 0`. -/
theorem tendsto_fderiv_eq_zero_of_isLittleO_sq {g : E → ℝ} {v : E} {δ a₁ a₂ : ℝ} (hδ : 0 < δ)
    (hg : ∀ s ∈ Ioo 0 δ, ContDiffAt ℝ 2 g (s • v))
    (h1 : Tendsto (fun s : ℝ ↦ fderiv ℝ g (s • v) v) (𝓝[>] 0) (𝓝 a₁))
    (h2 : Tendsto (fun s : ℝ ↦ fderiv ℝ (fderiv ℝ g) (s • v) v v) (𝓝[>] 0) (𝓝 a₂))
    (ho : (fun s : ℝ ↦ g (s • v)) =o[𝓝[>] 0] fun s ↦ s ^ 2) : a₁ = 0 ∧ a₂ = 0 := by
  have hray : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ r • v) v s := fun s ↦ by
    simpa using (hasDerivAt_id s).smul_const v
  refine tendsto_deriv_eq_zero_of_isLittleO_sq hδ (h' := fun s ↦ fderiv ℝ g (s • v) v)
    (h'' := fun s ↦ fderiv ℝ (fderiv ℝ g) (s • v) v v) (fun s hs ↦ ?_) (fun s hs ↦ ?_) h1 h2 ho
  · have hdiff : DifferentiableAt ℝ g (s • v) := (hg s hs).differentiableAt (by norm_num)
    exact hdiff.hasFDerivAt.comp_hasDerivAt s (hray s)
  · have hdiff : DifferentiableAt ℝ (fderiv ℝ g) (s • v) :=
      ((hg s hs).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s (hray s)
    simpa using hcomp.clm_apply (hasDerivAt_const s v)

end PDE.Analysis
