/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import PDE.Analysis.Complex.Definitions
public import PDE.Analysis.MeasureTheory.Lintegral

set_option linter.style.header false

/-!
# Curves in `L¹` and their derivatives

If the pointwise derivatives are in `L¹`, are continuous in time at every point, and converge in
`L¹` at the time in question, then the curve is differentiable in `L¹` there, with the pointwise
derivative as its derivative. The proof bounds the `L¹` norm of the remainder of the difference
quotient by the `L¹` distance of the derivatives on the segment between the two times.

## Main results

* `PDE.Analysis.hasDerivWithinAt_toLp_of_pointwise_coef`: Differentiating a curve in `L¹(μ; ℂ³)`
  point by point. Let `S` be a convex set of times and `t` a point of `S`, and for `s` in `S` let
  `u s` and `v s` be in `L¹`, with `v s x` the derivative within `S` of `τ ↦ u τ x` at `s` for every
  `x`, with `s ↦ v s x` continuous on `S` for every `x`, and with `∫⁻ ‖v s x - v t x‖ₑ → 0` as
  `s → t` within `S`. Then a curve `H` in `L¹` with `H s = u s` for `s` in `S` has the derivative
  `v t` within `S` at `t`.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PDE.Analysis

/-- Differentiating a curve in `L¹(μ; ℂ³)` point by point. Let `S` be a convex set of times and
`t` a point of `S`, and for `s` in `S` let `u s` and `v s` be in `L¹`, with `v s x` the derivative
within `S` of `τ ↦ u τ x` at `s` for every `x`, with `s ↦ v s x` continuous on `S` for every `x`,
and with `∫⁻ ‖v s x - v t x‖ₑ → 0` as `s → t` within `S`. Then a curve `H` in `L¹` with
`H s = u s` for `s` in `S` has the derivative `v t` within `S` at `t`. -/
theorem hasDerivWithinAt_toLp_of_pointwise_coef {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set ℝ} (hS : Convex ℝ S) {u v : ℝ → α → Coef} {t : ℝ} (ht : t ∈ S)
    (hu : ∀ s ∈ S, MemLp (u s) 1 μ) (hv : ∀ s ∈ S, MemLp (v s) 1 μ)
    (hder : ∀ x, ∀ s ∈ S, HasDerivWithinAt (fun τ ↦ u τ x) (v s x) S s)
    (hvc : ∀ x, ContinuousOn (fun s ↦ v s x) S)
    (hlim : Tendsto (fun s ↦ ∫⁻ x, ‖v s x - v t x‖ₑ ∂μ) (𝓝[S] t) (𝓝 0))
    {H : ℝ → Lp Coef 1 μ} (hH : ∀ s (hs : s ∈ S), H s = (hu s hs).toLp (u s)) :
    HasDerivWithinAt H ((hv t ht).toLp (v t)) S t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have h1 := (ENNReal.tendsto_nhds_zero.1 hlim) _ (ENNReal.ofReal_pos.2 hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδ, h1⟩ := h1
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)]
    with s hs hsb
  have hseg : segment ℝ t s ⊆ S := hS.segment_subset ht hs
  have hball : segment ℝ t s ⊆ Metric.ball t δ :=
    (convex_ball t δ).segment_subset (Metric.mem_ball_self hδ) hsb
  have key := lintegral_enorm_sub_sub_smul_deriv_le (μ := μ) (u := u) (v := v) (t := t) (s := s)
    (C := ENNReal.ofReal c)
    (fun x σ hσ ↦ (hder x σ (hseg hσ)).mono hseg) (fun x ↦ (hvc x).mono hseg)
    (fun σ hσ ↦ (hv σ (hseg hσ)).aestronglyMeasurable) (fun σ hσ ↦ h1 (hball hσ) (hseg hσ))
  rw [hH s hs, hH t ht, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub,
    Lp.norm_toLp, eLpNorm_one_eq_lintegral_eNorm
      (((hu s hs).sub (hu t ht)).sub ((hv t ht).const_smul (s - t))).aestronglyMeasurable]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm] at key
  rw [Real.norm_eq_abs]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) key

end PDE.Analysis
