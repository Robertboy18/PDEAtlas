/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalHigherBoundaryData
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BochnerIntegral

/-!
# Higher elliptic estimates for Bochner fields

The spatial estimate constructs a higher Sobolev representative at almost every
parameter value. Injectivity of the base coordinate makes this field measurable.
The pointwise estimate then gives its Bochner norm, without assuming a
higher derivative field or an invertible unshifted elliptic operator.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open Filter MeasureTheory Set
open scoped ENNReal

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Classical boundary and coefficient regularity give an `L²(H^{r+2})`
representative of every `L²(H¹₀)` weak elliptic field with load in `L²(H^r)`.
The constant is fixed before either field is chosen. -/
theorem exists_higherOrder_lp_estimate_of_contDiffUpToBoundary
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (r : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (r + 2) Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (r + 1) (fun x ↦ a x i j) Ω)
    (hb : ∀ i, ContDiffUpToBoundary (r + 1) (b i) Ω)
    (hc : ContDiffUpToBoundary (r + 1) c Ω)
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (F : Lp (W^{r,2}(Ω)) 2 μ) (u : Lp (H¹₀(Ω)) 2 μ),
        (∀ᵐ t ∂μ, IsWeakShiftedFullDivergenceSolution
          (fun i j ↦ (ha i j).toLp hopen hbounded ∞)
          (fun i ↦ (hb i).toLp hopen hbounded ∞) (hc.toLp hopen hbounded ∞)
          lambda (wkpBaseCoordinateCLM (F t)) 0 (u t)) →
        ∃ W : Lp (W^{r + 2,2}(Ω)) 2 μ,
          (∀ᵐ t ∂μ, wkpBaseCoordinateCLM (W t) = baseCoordCLM (u t)) ∧
          ‖W‖ ≤ K * (‖F‖ + ‖u‖) := by
  classical
  obtain ⟨K, hK, hspatial⟩ :=
    exists_global_higherOrder_estimate_of_contDiffUpToBoundary
      r hopen hbounded hgraph a b c ha hb hc lambda alpha halpha hElliptic
  refine ⟨K, hK, fun F u hweak ↦ ?_⟩
  let P (t : S) (W : W^{r + 2,2}(Ω)) : Prop :=
    wkpBaseCoordinateCLM W = baseCoordCLM (u t) ∧
      ‖W‖ ≤ K * (‖F t‖ + ‖u t‖)
  have hex : ∀ᵐ t ∂μ, ∃ W, P t W := by
    filter_upwards [hweak] with t ht
    obtain ⟨W, hbase, hnorm⟩ := hspatial (F t) (u t) ht
    exact ⟨W, hbase, hnorm.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (baseCoordCLM_norm_le (u t))) hK.le)⟩
  let w : S → W^{r + 2,2}(Ω) :=
    fun t ↦ if h : ∃ W, P t W then h.choose else 0
  have hw : ∀ᵐ t ∂μ, P t (w t) := by
    filter_upwards [hex] with t ht
    simpa only [w, dite_eq_left ht] using ht.choose_spec
  have hmeas : AEStronglyMeasurable w μ := by
    apply aestronglyMeasurable_of_wkpBaseCoordinateCLM μ hopen
    exact (baseCoordCLM.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).congr
      (hw.mono fun _ ht ↦ ht.1.symm)
  let NF : Lp ℝ 2 μ := (Lp.memLp F).norm.toLp (fun t ↦ ‖F t‖)
  let Nu : Lp ℝ 2 μ := (Lp.memLp u).norm.toLp (fun t ↦ ‖u t‖)
  let N := NF + Nu
  have hNF : (NF : S → ℝ) =ᵐ[μ] fun t ↦ ‖F t‖ := (Lp.memLp F).norm.coeFn_toLp
  have hNu : (Nu : S → ℝ) =ᵐ[μ] fun t ↦ ‖u t‖ := (Lp.memLp u).norm.coeFn_toLp
  have hN : (N : S → ℝ) =ᵐ[μ] fun t ↦ ‖F t‖ + ‖u t‖ := by
    filter_upwards [Lp.coeFn_add NF Nu, hNF, hNu] with t ht hFt hut
    exact ht.trans (congrArg₂ (· + ·) hFt hut)
  have hbound : ∀ᵐ t ∂μ, ‖w t‖ ≤ K * ‖N t‖ := by
    filter_upwards [hw, hN] with t ht hNt
    simpa only [hNt, Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using ht.2
  have hmem : MemLp w 2 μ :=
    ((Lp.memLp N).norm.const_mul K).mono' hmeas hbound
  refine ⟨hmem.toLp w, ?_, ?_⟩
  · filter_upwards [hmem.coeFn_toLp, hw] with t ht hwt
    exact (congrArg wkpBaseCoordinateCLM ht).trans hwt.1
  · have hWN : ‖hmem.toLp w‖ ≤ K * ‖N‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hmem.coeFn_toLp, hbound] with t ht hbt
      simpa only [ht] using hbt
    have hFnorm : ‖NF‖ ≤ ‖F‖ :=
      Lp.norm_le_norm_of_ae_le (hNF.mono fun t ht ↦ by rw [ht, norm_norm])
    have hunorm : ‖Nu‖ ≤ ‖u‖ :=
      Lp.norm_le_norm_of_ae_le (hNu.mono fun t ht ↦ by rw [ht, norm_norm])
    exact hWN.trans (mul_le_mul_of_nonneg_left
      ((norm_add_le NF Nu).trans (add_le_add hFnorm hunorm)) hK.le)

end SobolevSpace.GraphSpace.BoundaryRegularity
