/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Support and oddness under real L² convergence

Restriction and reflection are continuous operators on L². Vanishing on a
fixed region and the oddness relation therefore pass to a strong limit.
The hypotheses need only hold eventually along the convergent family.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory.Lp

/-- Almost-everywhere vanishing on a fixed measurable region survives strong L² convergence. -/
theorem ae_eq_zero_restrict_of_tendsto_L2
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → Lp ℝ 2 (volume : Measure ℝ)} {F : Lp ℝ 2 (volume : Measure ℝ)}
    {S : Set ℝ} (hf : Tendsto f l (𝓝 F))
    (hzero : ∀ᶠ i in l, (f i : ℝ → ℝ) =ᵐ[volume.restrict S] 0) :
    (F : ℝ → ℝ) =ᵐ[volume.restrict S] 0 := by
  let R : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
    restrictionCLMOfLE Measure.restrict_le_self
  have hR : ∀ᶠ i in l, R (f i) = 0 := by
    filter_upwards [hzero] with i hi
    exact Lp.ext ((restrictionCLMOfLE_apply_ae _ _).trans
      (hi.trans (Lp.coeFn_zero ℝ 2 (volume.restrict S)).symm))
  have hlim : R F = 0 := tendsto_nhds_unique ((R.continuous.tendsto F).comp hf)
    (tendsto_const_nhds.congr' (EventuallyEq.symm hR))
  exact (restrictionCLMOfLE_apply_ae _ F).symm.trans
    (hlim ▸ Lp.coeFn_zero ℝ 2 (volume.restrict S))

/-- Reflection preserves the oddness relation of a strongly convergent real L² family. -/
theorem ae_odd_of_tendsto_L2
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → Lp ℝ 2 (volume : Measure ℝ)} {F : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : Tendsto f l (𝓝 F))
    (hodd : ∀ᶠ i in l, ∀ᵐ x ∂volume, f i (-x) = -f i x) :
    ∀ᵐ x ∂volume, F (-x) = -F x := by
  let R : Lp ℝ 2 (volume : Measure ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    Lp.compMeasurePreservingₗᵢ ℝ Neg.neg (Measure.measurePreserving_neg volume)
  have hR : ∀ᶠ i in l, R (f i) = -f i := by
    filter_upwards [hodd] with i hi
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (f i)
      (Measure.measurePreserving_neg volume), hi, Lp.coeFn_neg (f i)] with x hx hix hnx
    exact hx.trans (hix.trans hnx.symm)
  have hlim : R F = -F := tendsto_nhds_unique ((R.continuous.tendsto F).comp hf)
    (hf.neg.congr' (EventuallyEq.symm hR))
  filter_upwards [Lp.coeFn_compMeasurePreserving F (Measure.measurePreserving_neg volume),
    Lp.coeFn_neg F] with x hx hnx
  change (R F : ℝ → ℝ) x = F (-x) at hx
  rw [hlim] at hx
  exact hx.symm.trans hnx

end MeasureTheory.Lp
