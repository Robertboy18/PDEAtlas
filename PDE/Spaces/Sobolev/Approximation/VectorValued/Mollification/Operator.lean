/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.Graph
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Mollification as a contraction of Banach-valued Sobolev graphs

Convolution by a nonnegative kernel of mass one contracts every derivative coordinate.
The finite ℓᵖ graph norm therefore gives the same constant one at every derivative order.
Bundling the mollification makes its linearity and uniform bound available for
composition with extension and restriction operators.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Mollification contracts the full Sobolev graph norm at every finite exponent. -/
theorem norm_mollify_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (U : W^{k,p}(ℝ^n; F)) : ‖mollify μ hε hp U‖ ≤ ‖U‖ := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  change ‖(mollify μ hε hp U).val‖ ≤ ‖U.val‖
  apply PiLp.norm_mono
  intro a
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top (U.val a))
  have hae : ((mollify μ hε hp U).val a : ℝ^n → F) =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)]
      mollifyVector μ ε (U.val a) := by
    simpa [domainMeasure] using mollify_apply_ae μ hε hp U a
  refine (eLpNorm_congr_ae hae).le.trans ?_
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    MollifyLp.eLpNorm_mollifyVector_le μ hε hp
      (by simpa [domainMeasure] using Lp.memLp (U.val a))

/-- Mollification is additive on the Sobolev graph. -/
theorem mollify_add (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (U V : W^{k,p}(ℝ^n; F)) :
    mollify μ hε hp (U + V) = mollify μ hε hp U + mollify μ hε hp V := by
  apply WkpSpaceOn.ext_of_base_ae
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  have hsum : ((U + V).val (baseIndex n k) : ℝ^n → F) =ᵐ[volume]
      (U.val (baseIndex n k) : ℝ^n → F) + V.val (baseIndex n k) := by
    simpa [domainMeasure] using Lp.coeFn_add (U.val (baseIndex n k))
      (V.val (baseIndex n k))
  have hconv := convolution_congr (f := scaled μ ε) (ContinuousLinearMap.lsmul ℝ ℝ)
    EventuallyEq.rfl hsum
  have hadd := mollifyVector_add_of_pos μ hε
    (U.val (baseIndex n k)) (V.val (baseIndex n k))
    (locallyIntegrableOn_univ.mp (U.property (baseIndex n k)).locallyIntegrable_f)
    (locallyIntegrableOn_univ.mp (V.property (baseIndex n k)).locallyIntegrable_f)
  have hresult :
      ((mollify μ hε hp U + mollify μ hε hp V).val (baseIndex n k) : ℝ^n → F)
        =ᵐ[volume] (mollify μ hε hp U).val (baseIndex n k) +
          (mollify μ hε hp V).val (baseIndex n k) := by
    simpa [domainMeasure] using Lp.coeFn_add
      ((mollify μ hε hp U).val (baseIndex n k))
      ((mollify μ hε hp V).val (baseIndex n k))
  filter_upwards [mollify_apply_ae μ hε hp (U + V) (baseIndex n k),
    mollify_apply_ae μ hε hp U (baseIndex n k),
    mollify_apply_ae μ hε hp V (baseIndex n k), hresult] with x hx hU hV hr
  rw [hx, hr, Pi.add_apply, hU, hV]
  exact congrFun (hconv.trans hadd) x

/-- Mollification commutes with real scalar multiplication on the Sobolev graph. -/
theorem mollify_smul (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (c : ℝ) (U : W^{k,p}(ℝ^n; F)) :
    mollify μ hε hp (c • U) = c • mollify μ hε hp U := by
  apply WkpSpaceOn.ext_of_base_ae
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  have hsmul : ((c • U).val (baseIndex n k) : ℝ^n → F) =ᵐ[volume]
      c • (U.val (baseIndex n k) : ℝ^n → F) := by
    simpa [domainMeasure] using Lp.coeFn_smul c (U.val (baseIndex n k))
  have hconv := convolution_congr (f := scaled μ ε) (ContinuousLinearMap.lsmul ℝ ℝ)
    EventuallyEq.rfl hsmul
  have hresult :
      ((c • mollify μ hε hp U).val (baseIndex n k) : ℝ^n → F) =ᵐ[volume]
        c • ((mollify μ hε hp U).val (baseIndex n k) : ℝ^n → F) := by
    simpa [domainMeasure] using Lp.coeFn_smul c
      ((mollify μ hε hp U).val (baseIndex n k))
  filter_upwards [mollify_apply_ae μ hε hp (c • U) (baseIndex n k),
    mollify_apply_ae μ hε hp U (baseIndex n k), hresult] with x hx hU hr
  rw [hx, hr, Pi.smul_apply, hU]
  exact congrFun (hconv.trans convolution_smul) x

/-- Convolution by a positive-scale mollifier as a continuous linear Sobolev operator. -/
def mollifyCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞) :
    W^{k,p}(ℝ^n; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  ({ toFun := mollify μ hε hp
     map_add' := mollify_add μ hε hp
     map_smul' := mollify_smul μ hε hp } :
      W^{k,p}(ℝ^n; F) →ₗ[ℝ] W^{k,p}(ℝ^n; F)).mkContinuous 1
    (fun U ↦ by
      change ‖mollify μ hε hp U‖ ≤ 1 * ‖U‖
      simpa only [one_mul] using norm_mollify_le μ hε hp U)

/-- The bundled operator is the coordinatewise mollification. -/
@[simp] theorem mollifyCLM_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (hp : p ≠ ∞) (U : W^{k,p}(ℝ^n; F)) :
    mollifyCLM μ hε hp U = mollify μ hε hp U :=
  rfl

/-- The mollification operator has norm at most one, uniformly in the positive scale. -/
theorem norm_mollifyCLM_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞) :
    ‖mollifyCLM (F := F) (k := k) μ hε hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  simpa only [one_mul, mollifyCLM_apply] using norm_mollify_le μ hε hp U

/-- One globally smooth function represents the mollified bundle and every derivative row. -/
theorem mollifyCLM_has_smooth_representative (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (hp : p ≠ ∞) (U : W^{k,p}(ℝ^n; F)) :
    ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ a : DerivIndex n k, ((mollifyCLM μ hε hp U).val a : ℝ^n → F) =ᵐ[volume]
        iteratedPartialDeriv a.toList f := by
  refine ⟨mollifyVector μ ε (U.val (baseIndex n k)), ?_, ?_⟩
  · exact mollifyVector_contDiff_of_pos μ hε _
      (locallyIntegrableOn_univ.mp (U.property (baseIndex n k)).locallyIntegrable_f)
  · intro a
    rw [iteratedPartialDeriv_mollifyVector_eq μ hε (U.property a)]
    exact mollify_apply_ae μ hε hp U a

/-- Positive-scale mollification converges strongly to the identity at finite exponents. -/
theorem tendsto_mollifyCLM (μ : Mollifier n) (hp : p ≠ ∞) (U : W^{k,p}(ℝ^n; F))
    (ε : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m ↦ mollifyCLM μ (hε m) hp U) atTop (𝓝 U) :=
  mollify_tendsto μ hp U ε hε hε0

end SobolevSpace.VectorValued
