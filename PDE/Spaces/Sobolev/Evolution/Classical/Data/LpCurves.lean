/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.Classical.Data.Slices
public import PDE.Analysis.MeasureTheory.Lp.ContinuousExtension
public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative
public import PDE.Analysis.Calculus.CompactCurry

/-!
# Lebesgue curves of raw smooth spacetime derivatives

The canonical continuous fields on the compact spatial closure give continuous
`L²` curves through the bounded linear extension map. Their
time derivatives pass through that map, so the corresponding weak time links
are consequences of the raw data.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Evolution.Classical

open Filter MeasureTheory Set PDE.Common BoundedContinuousFunction
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : ℝ^(n + 1) → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- The `L²` curve of one canonical mixed derivative of the raw data. -/
def derivativeLpCurve (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    ℝ → Lp ℝ 2 (domainMeasure n Ω) :=
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  (subtypeToLp isClosed_closure.measurableSet) ∘
    compactCurry ⟨closure Ω, hbounded.isCompact_closure⟩
      (derivativeSlice hopen hf α) (continuous_derivativeSlice hopen hf α)

/-- The constructed Lebesgue curve is continuous, including at both time endpoints. -/
theorem continuous_derivativeLpCurve (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    Continuous (derivativeLpCurve hopen hbounded hf α) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact (subtypeToLp (p := 2) (μ := domainMeasure n Ω)
    isClosed_closure.measurableSet).continuous.comp
      (continuous_compactCurry ⟨closure Ω, hbounded.isCompact_closure⟩
        (derivativeSlice hopen hf α) (continuous_derivativeSlice hopen hf α))

/-- Its scalar representative agrees with the canonical field on every slice. -/
theorem derivativeLpCurve_ae (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) (t : ℝ) :
    (derivativeLpCurve hopen hbounded hf α t : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      derivativeSlice hopen hf α t := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let K : TopologicalSpace.Compacts (ℝ^n) := ⟨closure Ω, hbounded.isCompact_closure⟩
  filter_upwards [coeFn_subtypeToLp (p := 2) (μ := domainMeasure n Ω)
    isClosed_closure.measurableSet
      (compactCurry K (derivativeSlice hopen hf α) (continuous_derivativeSlice hopen hf α) t),
    ae_restrict_mem hopen.measurableSet] with x heq hx
  exact heq.trans (Subtype.coe_injective.extend_apply _ _ ⟨x, subset_closure hx⟩)

/-- The adjacent canonical field is the time derivative in `L²`. -/
theorem hasDerivAt_derivativeLpCurve (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (derivativeLpCurve hopen hbounded hf α)
      (derivativeLpCurve hopen hbounded hf (0 :: α) t) t := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let K : TopologicalSpace.Compacts (ℝ^n) := ⟨closure Ω, hbounded.isCompact_closure⟩
  let D (s : ℝ) (x : ℝ^n) : ℝ →L[ℝ] ℝ :=
    (1 : ℝ →L[ℝ] ℝ).smulRight (derivativeSlice hopen hf (0 :: α) s x)
  have hD : Continuous D.uncurry :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp
      (continuous_derivativeSlice hopen hf (0 :: α))
  have hd := hasFDerivAt_compactCurry_of_eventually K (derivativeSlice hopen hf α) D
    (continuous_derivativeSlice hopen hf α) hD t (by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      intro x
      exact (hasDerivAt_derivativeSlice hopen hf α hs x.property).hasFDerivAt)
  have hval : compactCurryFDeriv K D hD t 1 =
      compactCurry K (derivativeSlice hopen hf (0 :: α))
        (continuous_derivativeSlice hopen hf (0 :: α)) t := by
    ext x
    simp [D]
  have h := (subtypeToLp (p := 2) (μ := domainMeasure n Ω)
    isClosed_closure.measurableSet).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt
  simpa only [hval, derivativeLpCurve, K, Function.comp_def] using h

/-- The raw data supply adjacent weak time derivatives. -/
theorem hasWeakTimeDerivativeOn_derivativeLpCurve (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Ioo a b)
      (derivativeLpCurve hopen hbounded hf α)
      (derivativeLpCurve hopen hbounded hf (0 :: α)) :=
  PDE.Analysis.Evolution.hasWeakTimeDerivativeOn_of_continuousOn_hasDerivAt
    (continuous_derivativeLpCurve hopen hbounded hf α).continuousOn
    (continuous_derivativeLpCurve hopen hbounded hf (0 :: α)).continuousOn
    (fun _ ht ↦ hasDerivAt_derivativeLpCurve hopen hbounded hf α ht)

end SobolevSpace.Evolution.Classical
