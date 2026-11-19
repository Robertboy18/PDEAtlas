/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeakConvergence.TestFunctions

/-!
# Strong–weak products against smooth tests

Hölder multiplication followed by a smooth test integral is a continuous
bilinear form. Thus a strongly converging factor can be paired with a bounded
weakly converging factor. The two input exponents may differ; this is the
pairing needed between a Sobolev value and a Jacobian minor of lower degree.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Distributions

namespace MeasureTheory.Lp

variable {n : ℕ} (Ω : Opens (ℝ^n))
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r]

local notation "μΩ" => Measure.restrict
  (volume : Measure (ℝ^n)) (Ω : Set (ℝ^n))

/-- The integral of a Hölder product against a smooth test function. -/
def testProductPairing (φ : 𝓓(Ω, ℝ)) :
    Lp ℝ p μΩ →L[ℝ] Lp ℝ q μΩ →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Lp ℝ q μΩ) (Lp ℝ r μΩ) ℝ
    (testFunctionPairing Ω φ)).comp
      ((ContinuousLinearMap.mul ℝ ℝ).holderL μΩ p q r)

/-- The bilinear form evaluates the product of the chosen representatives. -/
theorem testProductPairing_apply (φ : 𝓓(Ω, ℝ))
    (f : Lp ℝ p μΩ) (g : Lp ℝ q μΩ) :
    testProductPairing Ω (r := r) φ f g = ∫ x, f x * g x * φ x ∂μΩ := by
  change testFunctionPairing Ω φ
    ((ContinuousLinearMap.mul ℝ ℝ).holder r f g) = _
  rw [testFunctionPairing_apply]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := r) f g] with x hx
  simp only [ContinuousLinearMap.mul_apply'] at hx
  rw [hx]

include r in
/-- Joint strong convergence passes products against a fixed smooth test to the limit. -/
theorem tendsto_testProductPairing
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ p μΩ} {g : ι → Lp ℝ q μΩ}
    {F : Lp ℝ p μΩ} {G : Lp ℝ q μΩ}
    (hf : Tendsto f l (𝓝 F)) (hg : Tendsto g l (𝓝 G)) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun i ↦ ∫ x, f i x * g i x * φ x ∂μΩ) l
      (𝓝 (∫ x, F x * G x * φ x ∂μΩ)) := by
  have hc : Continuous (fun z : Lp ℝ p μΩ × Lp ℝ q μΩ ↦
      testProductPairing Ω (r := r) φ z.1 z.2) :=
    ((testProductPairing Ω (r := r) φ).continuous.comp continuous_fst).clm_apply continuous_snd
  have h := (hc.tendsto (F, G)).comp (hf.prodMk_nhds hg)
  simpa only [Function.comp_def, testProductPairing_apply] using h

include r in
/-- Strong convergence in the first factor and bounded weak convergence in the
second factor pass the tested product to the limit along the original filter. -/
theorem tendsto_testProductPairing_of_strong_weak
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ p μΩ} {g : ι → Lp ℝ q μΩ}
    {F : Lp ℝ p μΩ} {G : Lp ℝ q μΩ}
    (hf : Tendsto f l (𝓝 F))
    (hg : Tendsto (fun i ↦ toWeakSpace ℝ (Lp ℝ q μΩ) (g i)) l
      (𝓝 (toWeakSpace ℝ (Lp ℝ q μΩ) G)))
    (hbounded : Bornology.IsBounded (range g)) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun i ↦ ∫ x, f i x * g i x * φ x ∂μΩ) l
      (𝓝 (∫ x, F x * G x * φ x ∂μΩ)) := by
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  have h := PDE.Analysis.WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    ((testProductPairing Ω (r := r) φ).continuous.tendsto F |>.comp hf)
    hg C (fun i ↦ hC _ ⟨i, rfl⟩)
  simpa only [Function.comp_def, testProductPairing_apply] using h

end MeasureTheory.Lp
