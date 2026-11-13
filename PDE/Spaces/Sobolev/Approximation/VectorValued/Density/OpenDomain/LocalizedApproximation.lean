/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain.CutoffExtension
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Small smooth approximation errors after an interior cutoff

Extend an interior localization of the input, mollify it on the whole space, and multiply
the error by a prescribed test function. Continuity of restriction and scalar multiplication
makes that error arbitrarily small in the full Sobolev graph norm.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A prescribed interior cutoff times the smoothing error has arbitrarily small
Sobolev graph norm. The smooth function is obtained by whole-space mollification. -/
theorem exists_localized_smooth_error (hp : p ≠ ∞) (U : W^{k,p}(Ω; F))
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) v ∧
      ∃ E : W^{k,p}(Ω; F),
        (E.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
          (fun x ↦ ψ.toFun x • (v x - U.val (baseIndex n k) x)) ∧ ‖E‖ < δ := by
  obtain ⟨χ, hχ, hχone, _, _⟩ :=
    TestFunction.exists_eq_one_on_compact Ω.isOpen ψ.hasCompactSupport hψ
  let W := extendByCutoff χ hχ U
  let μ := standardMollifier n
  let ε (m : ℕ) : ℝ := 1 / (m + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let V (m : ℕ) := mollify μ (hε m) hp W
  let M := compactSmoothMultiplierCLM (k := k) (p := p) (Ω := ⊤)
    ψ.toFun ψ.contDiff ψ.hasCompactSupport (F := F)
  let R := restrictCLM (n := n) (k := k) (p := p) (F := F) (le_top : Ω ≤ ⊤)
  let A := R.comp M
  have hV : Tendsto (fun m ↦ V m - W) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (mollify_tendsto μ hp W ε hε hε0).sub (tendsto_const_nhds (x := W))
  have hE : Tendsto (fun m ↦ ‖A (V m - W)‖) atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero, Function.comp_apply] using
      (A.continuous.continuousAt.tendsto.comp hV).norm
  obtain ⟨m, hm⟩ := (hE.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨v, hv, hVbase⟩ := mollify_has_smooth_representative μ (hε m) hp W
  refine ⟨v, hv, A (V m - W), ?_, hm⟩
  have hWbase := extendByCutoff_base_ae χ hχ U
  have hprod := compactSmoothMultiplierCLM_base_ae
    ψ.toFun ψ.contDiff ψ.hasCompactSupport (V m - W)
  have hsub : ((V m - W).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)] fun x ↦
        (V m).val (baseIndex n k) x - W.val (baseIndex n k) x :=
    Lp.coeFn_sub _ _
  have hrestrict := restrictCLM_apply_ae (le_top : Ω ≤ ⊤)
    (M (V m - W)) (baseIndex n k)
  have hle : domainMeasure n Ω ≤ domainMeasure n (⊤ : Opens ℝ^n) := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      (Measure.restrict_le_self (μ := (volume : Measure ℝ^n)) (s := (Ω : Set ℝ^n)))
  have hle' : domainMeasure n Ω ≤ volume := Measure.restrict_le_self
  filter_upwards [hrestrict, hprod.filter_mono (ae_mono hle),
    hsub.filter_mono (ae_mono hle), hVbase.filter_mono (ae_mono hle'),
    hWbase.filter_mono (ae_mono hle')] with x hr hp hs hvx hw
  change (A (V m - W)).val (baseIndex n k) x =
    (M (V m - W)).val (baseIndex n k) x at hr
  change W.val (baseIndex n k) x = χ.toFun x • U.val (baseIndex n k) x at hw
  rw [hr, hp, hs, hvx, hw]
  by_cases hx : ψ.toFun x = 0
  · simp [hx]
  · rw [hχone x (subset_tsupport ψ.toFun hx), one_smul]

end SobolevSpace.VectorValued
