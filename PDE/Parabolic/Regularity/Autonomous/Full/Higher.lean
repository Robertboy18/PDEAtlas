/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherDerivative
public import PDE.Parabolic.Regularity.Autonomous.Full.EllipticLift
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The second improved estimate for a full autonomous operator

An `H² ∩ H¹₀` datum has an `L²` elliptic load. The differentiated weak
equation therefore gives an energy-valued time derivative, with no boundary
condition on its initial value. The principal elliptic solver then gives the
essentially bounded `H²` lift of the original solution. The main result is
`exists_full_form_higher_regularity`.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The second full autonomous estimate holds for every weak solution.
The initial `H²` lift is identified with the given zero-trace datum, and
both time derivatives are weak derivatives of the solution itself. -/
theorem exists_full_form_higher_regularity
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hΩ : C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f df : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (g : H¹₀(Ω)) (G : W^{2,2}(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
      lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2)
        (by omega) G = h10SubtypeL (n := n) (Ω := Ω) g →
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Ioc t₀ t₁)) df) →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
        (fun _ ↦ autonomousDivergenceFormOperator A +
          (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.comp R)
        ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
          2 (volume.restrict (Ioc t₀ t₁)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ (v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
        (dv : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc t₀ t₁)))
        (U₂ : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen) u
          ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).energyToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) v) ∧
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
          v dv ∧
        (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
          lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2)
            (by omega) (U₂ t) = h10SubtypeL (n := n) (Ω := Ω) (u t)) ∧
        MemLp (fun t ↦ U₂ t) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
        MemLp (fun t ↦ baseCoordCLM (n := n) (Ω := Ω) (v t)) ∞
          (volume.restrict (Ioc t₀ t₁)) ∧
        (eLpNormEssSup (fun t ↦ U₂ t) (volume.restrict (Ioc t₀ t₁))).toReal +
          (eLpNormEssSup (fun t ↦ baseCoordCLM (n := n) (Ω := Ω) (v t))
            (volume.restrict (Ioc t₀ t₁))).toReal + ‖v‖ + ‖dv‖ ≤
          K * (‖G‖ + Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2)) := by
  let hopen := hΩ.toC1ExtensionAtlas.isOpen
  let T := h10L2GelfandTriple hopen
  let μ := volume.restrict (Ioc t₀ t₁)
  let S := globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic
  have hfirst := exists_full_form_improved_regularity ht hΩ A a haRep haC1 haSymm
    alpha halpha hElliptic R
  obtain ⟨K₁, hK₁, hfirst⟩ := hfirst
  have hsecond := exists_full_form_time_derivative_of_h2_datum ht hΩ A a haRep
    alpha halpha hElliptic R
  obtain ⟨B, hBpos, hsecond⟩ := hsecond
  let F := Real.sqrt (1 / (t₁ - t₀) + 2)
  let H := F + ‖R‖ * K₁
  let K := 2 * (‖S‖ * (H + B) + 2 * B + 1)
  have hB : 0 ≤ B := hBpos.le
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨K, by dsimp only [K]; positivity, fun f df g G u hG hf hu ↦ ?_⟩
  let D := ‖G‖ + ‖f‖ + ‖df‖
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hgNorm : ‖g‖ ≤ ‖G‖ := by
    have h := norm_lowerOrderCLM_apply_le (n := n) (p := 2) (Ω := Ω) (k := 1) (m := 2)
      (by omega) G
    rwa [hG] at h
  have hvel := hsecond f df g G u hG hf hu
  obtain ⟨v, dv, E, huv, hvdv, hEbound⟩ := hvel
  have hvBound : ∀ᵐ t ∂μ, ‖T.inclusion (v t)‖ ≤ B * D := by
    filter_upwards [E.ae_eq_inclusion.filter_mono (ae_mono (volume.restrict_mono_set
      (Ioc_subset_Icc_self.trans Icc_subset_uIcc))), ae_restrict_mem measurableSet_Ioc]
      with t hrep htmem
    have h := hEbound t ⟨htmem.1.le, htmem.2⟩
    rw [hrep] at h
    linarith only [h, norm_nonneg v, norm_nonneg dv]
  have hreg := hfirst f g u hu
  obtain ⟨ut₁, U₁, _, _, huTop, huEstimate⟩ := hreg
  have huSup : (eLpNormEssSup (fun t ↦ u t) μ).toReal ≤ K₁ * D := by
    have hright : K₁ * (‖g‖ + ‖f‖) ≤ K₁ * D := mul_le_mul_of_nonneg_left
      (by dsimp only [D]; linarith only [hgNorm, norm_nonneg df]) hK₁.le
    linarith only [huEstimate, hright, norm_nonneg U₁, norm_nonneg ut₁]
  have huBound : ∀ᵐ t ∂μ, ‖u t‖ ≤ K₁ * D := by
    filter_upwards [ae_le_lpNorm_exponent_top huTop] with t htmem
    rw [← toReal_eLpNorm, eLpNorm_exponent_top huTop.aestronglyMeasurable] at htmem
    exact htmem.trans huSup
  let : MeasurableSpace (DerivLp n 2 Ω) := borel (DerivLp n 2 Ω)
  let : BorelSpace (DerivLp n 2 Ω) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (DerivLp n 2 Ω)) :=
    borel (StrongDual ℝ (DerivLp n 2 Ω))
  let : BorelSpace (StrongDual ℝ (DerivLp n 2 Ω)) := ⟨rfl⟩
  have htrace := hf.exists_absolutelyContinuousRepresentative_norm_le_of_identity ht
  obtain ⟨_, _, _, _, _, hfBound⟩ := htrace
  have hfBound' : ∀ᵐ t ∂μ, ‖f t‖ ≤ F * D := by
    filter_upwards [hfBound] with t hft
    exact hft.trans ((timeSobolevBound_le_sum_norm ht f df).trans
      (mul_le_mul_of_nonneg_left (by dsimp only [D]; linarith only [norm_nonneg G]) hF))
  have hlift := exists_full_form_spatial_h2_lift hΩ A a haRep haC1 alpha halpha
    hElliptic R f u v (baseCoordCLM (n := n) (Ω := Ω) g)
    (F * D) (K₁ * D) (B * D) (mul_nonneg hB hD) hu huv hfBound' huBound hvBound
  obtain ⟨U₂, hU₂, hU₂Top, hU₂Bound⟩ := hlift
  have hU₂Bound' : ∀ᵐ t ∂μ, ‖U₂ t‖ ≤ ‖S‖ * (H + B) * D := by
    filter_upwards [hU₂Bound] with t h
    exact h.trans_eq (by dsimp only [H]; ring)
  have hsup₂ : (eLpNormEssSup (fun t ↦ U₂ t) μ).toReal ≤ ‖S‖ * (H + B) * D :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hU₂Bound')).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hsupv : (eLpNormEssSup (fun t ↦ T.inclusion (v t)) μ).toReal ≤ B * D :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hvBound)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hB hD))
  have hnorms : ‖v‖ + ‖dv‖ ≤ B * D := by
    linarith only [hEbound t₀ ⟨le_rfl, ht.le⟩, norm_nonneg (E.representative t₀)]
  have hDdata : D ≤ 2 * (‖G‖ + Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2)) := by
    have hfNorm : ‖f‖ ≤ Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
    have hdfNorm : ‖df‖ ≤ Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))
    dsimp only [D]
    linarith only [hfNorm, hdfNorm, norm_nonneg G]
  have hvTop : MemLp (fun t ↦ T.inclusion (v t)) ∞ μ := memLp_top_of_bound
    (T.inclusion.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)) (B * D) hvBound
  have hsum : (eLpNormEssSup (fun t ↦ U₂ t) μ).toReal +
      (eLpNormEssSup (fun t ↦ T.inclusion (v t)) μ).toReal + ‖v‖ + ‖dv‖ ≤
        (‖S‖ * (H + B) + 2 * B + 1) * D := by
    nlinarith only [hsup₂, hsupv, hnorms, hD]
  refine ⟨v, dv, U₂, huv, hvdv, hU₂, hU₂Top, hvTop, hsum.trans ?_⟩
  calc
    _ ≤ (‖S‖ * (H + B) + 2 * B + 1) * (2 * (‖G‖ + Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hDdata (by positivity)
    _ = _ := by dsimp only [K]; ring

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
