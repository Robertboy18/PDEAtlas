/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.DistributionTheory.TestFunction.Slice
import PDE.Analysis.Calculus.CompactLpCurry
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Time differentiation of spatial test slices

For a smooth compactly supported spacetime function Φ, the curve of Lᵖ classes
`t ↦ [Φ(t, ·)]` has derivative `[∂ₜΦ(t, ·)]`. This holds on every spatial subset Ω,
with no regularity or finite-volume assumption on Ω, and for `1 ≤ p ≤ ∞`.

The common compact spatial support is obtained by projecting the supports of Φ and
its time derivative. Compact-family differentiation supplies the uniform remainder
estimate before passage to Lᵖ. The classes themselves are the
`toLpOfContCompact` classes, not newly chosen representatives.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Taking a spatial Lᵖ class commutes with time differentiation of a smooth compactly
supported spacetime test. The spatial domain is arbitrary, including unbounded domains. -/
theorem hasDerivAt_toLpOfContCompact_sliceRight
    (Φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ) :
    HasDerivAt
      (fun s ↦ toLpOfContCompact (p := p) (Ω := Ω) (TestFunction.sliceRight s Φ)
        (TestFunction.sliceRight s Φ).continuous (TestFunction.sliceRight s Φ).hasCompactSupport)
      (toLpOfContCompact (p := p) (Ω := Ω)
        (TestFunction.sliceRight t (TestFunction.lineDerivCLM ℝ (1, 0) Φ))
        (TestFunction.sliceRight t (TestFunction.lineDerivCLM ℝ (1, 0) Φ)).continuous
        (TestFunction.sliceRight t (TestFunction.lineDerivCLM ℝ (1, 0) Φ)).hasCompactSupport)
      t := by
  let Ψ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ) :=
    TestFunction.lineDerivCLM ℝ (1, 0) Φ
  let K : Compacts (ℝ^n) :=
    ⟨Prod.snd '' (tsupport Φ ∪ tsupport Ψ),
      (Φ.hasCompactSupport.isCompact.union Ψ.hasCompactSupport.isCompact).image continuous_snd⟩
  have : IsFiniteMeasure ((domainMeasure n Ω).restrict (K : Set (ℝ^n))) :=
    isFiniteMeasure_restrict.mpr K.isCompact.measure_ne_top
  let u (s : ℝ) : Lp ℝ p (domainMeasure n Ω) :=
    toLpOfContCompact (p := p) (Ω := Ω) (TestFunction.sliceRight s Φ)
      (TestFunction.sliceRight s Φ).continuous (TestFunction.sliceRight s Φ).hasCompactSupport
  let v (s : ℝ) : Lp ℝ p (domainMeasure n Ω) :=
    toLpOfContCompact (p := p) (Ω := Ω) (TestFunction.sliceRight s Ψ)
      (TestFunction.sliceRight s Ψ).continuous (TestFunction.sliceRight s Ψ).hasCompactSupport
  let D (s : ℝ) (x : ℝ^n) : ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.toSpanSingleton ℝ (Ψ (s, x))
  have hD : Continuous D.uncurry := by
    change Continuous (fun z : ℝ × ℝ^n ↦
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ) (Ψ z))
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp Ψ.continuous
  have hpoint (s : ℝ) (x : ℝ^n) :
      HasDerivAt (fun r : ℝ ↦ Φ (r, x)) (Ψ (s, x)) s := by
    have hΦ : DifferentiableAt ℝ (fun z ↦ Φ z) (s, x) :=
      (Φ.contDiff.differentiable (by simp)).differentiableAt
    have hcomp := hΦ.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
    have hvalue : Ψ (s, x) = fderiv ℝ (fun z ↦ Φ z) (s, x) (1, 0) := by
      change (TestFunction.lineDerivCLM ℝ (1, 0) Φ) (s, x) = _
      exact testFunction_lineDerivCLM_apply Φ (1, 0) (s, x)
    rw [hvalue]
    exact hcomp
  have houtside (s : ℝ) (x : ℝ^n) (hx : x ∉ K) :
      Φ (s, x) = 0 ∧ Ψ (s, x) = 0 := by
    constructor
    · apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hx ⟨(s, x), Or.inl hz, rfl⟩
    · apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hx ⟨(s, x), Or.inr hz, rfl⟩
  have h :=
    hasFDerivAt_Lp_of_common_compact_support K (fun s x ↦ Φ (s, x)) D
      Φ.continuous hD (fun s x ↦ (hpoint s x).hasFDerivAt)
      (fun s x hx ↦ (houtside s x hx).1)
      u (fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ (v s))
      (fun s ↦ toLpOfContCompact_coeFn
        (TestFunction.sliceRight s Φ).continuous (TestFunction.sliceRight s Φ).hasCompactSupport)
      (fun s c ↦ by
        change (c • v s : Lp ℝ p (domainMeasure n Ω)) =ᵐ[domainMeasure n Ω]
          fun x ↦ c • Ψ (s, x)
        filter_upwards [Lp.coeFn_smul c (v s),
          toLpOfContCompact_coeFn (p := p) (Ω := Ω)
            (TestFunction.sliceRight s Ψ).continuous
            (TestFunction.sliceRight s Ψ).hasCompactSupport] with x hx hxv
        rw [hx, Pi.smul_apply, hxv]
        rfl)
      t
  change HasDerivAt u (v t) t
  exact h

end SobolevSpace.GraphSpace
