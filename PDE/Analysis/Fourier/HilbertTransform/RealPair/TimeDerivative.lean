/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Limit
public import PDE.Analysis.MeasureTheory.Lp.TimeDerivative.Dominated

/-!
# Time differentiation of the concrete real Hilbert relation

The two real `L²` curves satisfy equality after complex embedding and the
spectral Hilbert transform. Differentiating that equality proves the Hilbert
relation for their derivatives. A common `L²` majorant supplies the required
Banach derivatives from pointwise time differentiation.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- Differentiable real `L²` curves forming Hilbert pairs on a neighborhood
have derivatives forming a concrete Hilbert pair. -/
theorem IsHilbertPair.of_hasDerivAt_toLp
    {f g : ℝ → ℝ → ℝ} {q r : ℝ → ℝ} {t : ℝ}
    (hf : ∀ s, MemLp (f s) 2 volume) (hg : ∀ s, MemLp (g s) 2 volume)
    (hq : MemLp q 2 volume) (hr : MemLp r 2 volume)
    (hpair : ∀ᶠ s in 𝓝 t, IsHilbertPair (f s) (g s))
    (hft : HasDerivAt (fun s ↦ (hf s).toLp (f s)) (hq.toLp q) t)
    (hgt : HasDerivAt (fun s ↦ (hg s).toLp (g s)) (hr.toLp r) t) :
    IsHilbertPair q r := by
  let embed := Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)
  let transform := hilbertTransform.toContinuousLinearMap.restrictScalars ℝ
  have hleft := embed.hasFDerivAt.comp_hasDerivAt t hgt
  have hright := transform.hasFDerivAt.comp_hasDerivAt t
    (embed.hasFDerivAt.comp_hasDerivAt t hft)
  apply (isHilbertPair_iff_compLp_eq hq hr).mpr
  apply hleft.unique
  apply hright.congr_of_eventuallyEq
  filter_upwards [hpair] with s hs
  exact (isHilbertPair_iff_compLp_eq (hf s) (hg s)).mp hs

/-- Common pointwise `L²` bounds justify differentiation of both sides of
the spectral relation. No Hilbert identity for the derivatives is
among the hypotheses. -/
theorem IsHilbertPair.timeDerivative_of_memLp_bounds
    {f g q r : ℝ → ℝ → ℝ} {B C : ℝ → ℝ} {t : ℝ} {times : Set ℝ}
    (hf : ∀ s, MemLp (f s) 2 volume) (hg : ∀ s, MemLp (g s) 2 volume)
    (hq : MemLp (q t) 2 volume) (hr : MemLp (r t) 2 volume)
    (hB : MemLp B 2 volume) (hC : MemLp C 2 volume)
    (htimes : times ∈ 𝓝 t) (hconvex : Convex ℝ times)
    (hpair : ∀ s ∈ times, IsHilbertPair (f s) (g s))
    (hft : ∀ᵐ x, ∀ s ∈ times, HasDerivAt (fun τ ↦ f τ x) (q s x) s)
    (hgt : ∀ᵐ x, ∀ s ∈ times, HasDerivAt (fun τ ↦ g τ x) (r s x) s)
    (hqb : ∀ᵐ x, ∀ s ∈ times, ‖q s x‖ ≤ B x)
    (hrb : ∀ᵐ x, ∀ s ∈ times, ‖r s x‖ ≤ C x) :
    IsHilbertPair (q t) (r t) := by
  apply IsHilbertPair.of_hasDerivAt_toLp hf hg hq hr
    ((show ∀ᶠ s in 𝓝 t, s ∈ times from htimes).mono fun s hs ↦ hpair s hs)
  · exact hasDerivAt_toLp_of_memLp_bound (by simp) hf hq hB
      htimes hconvex hft hqb
  · exact hasDerivAt_toLp_of_memLp_bound (by simp) hg hr hC
      htimes hconvex hgt hrb

end PDE.Analysis
