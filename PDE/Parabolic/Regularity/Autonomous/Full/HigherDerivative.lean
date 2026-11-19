/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.TimeDerivative
public import PDE.Parabolic.Regularity.Autonomous.Higher.Form
public import PDE.Elliptic.Regularity.SolutionOperator.StrongLoad

/-!
# The differentiated estimate from an `H²` initial datum

The strong divergence expression of the datum gives the initial pivot
load. This yields the time-derivative energy estimate from the original
Sobolev assumptions, including a bound for its continuous pivot trace.
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

/-- An `H² ∩ H¹₀` datum and `H¹` forcing give an energy-valued time
derivative and its three bounds, without initial velocity compatibility. -/
theorem exists_full_form_time_derivative_of_h2_datum
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hΩ : C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ a x i j)
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
        (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
          (fun t ↦ v t) (fun t ↦ dv t) t₀ t₁),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen) u
          ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).energyToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) v) ∧
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
          v dv ∧
        ∀ t ∈ Icc t₀ t₁, ‖E.representative t‖ + ‖v‖ + ‖dv‖ ≤
          K * (‖G‖ + ‖f‖ + ‖df‖) := by
  let hopen := hΩ.toC1ExtensionAtlas.isOpen
  let T := h10L2GelfandTriple hopen
  let Aop := autonomousDivergenceFormOperator A
  have hcoer := exists_autonomous_coercivity_constant hΩ A a haRep alpha halpha hElliptic
  obtain ⟨C, hC, hcoercive⟩ := hcoer
  have hsecond := @exists_full_form_time_derivative n Ω hopen
    hΩ.toC1ExtensionAtlas.bounded Aop R C t₀ t₁ hC ht hcoercive
  obtain ⟨K₂, hK₂, hsecond⟩ := hsecond
  let N := ‖strongLoadCLM A‖ + ‖R‖
  let B := K₂ * (N + 1)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hB : 0 < B := mul_pos hK₂ (by positivity)
  refine ⟨B, hB, ?_⟩
  intro f df g G u hG hf hu
  let D := ‖G‖ + ‖f‖ + ‖df‖
  have hgNorm : ‖g‖ ≤ ‖G‖ := by
    have h := norm_lowerOrderCLM_apply_le (n := n) (p := 2) (Ω := Ω)
      (k := 1) (m := 2) (by omega) G
    rw [hG] at h
    exact h
  let load := strongLoad A G + R g
  have hload : T.pivotToDual load = (Aop + T.pivotToDual.comp R) g := by
    rw [map_add, pivotToDual_strongLoad hopen A G g hG]
    rfl
  have hloadNorm : ‖load‖ ≤ N * ‖G‖ := by
    calc
      _ ≤ ‖strongLoad A G‖ + ‖R g‖ := norm_add_le _ _
      _ ≤ ‖strongLoadCLM A‖ * ‖G‖ + ‖R‖ * ‖G‖ :=
        add_le_add (norm_strongLoad_le A G)
          ((R.le_opNorm g).trans (mul_le_mul_of_nonneg_left hgNorm (norm_nonneg R)))
      _ = _ := by dsimp only [N]; ring
  have hvel := hsecond f df g load u hf hload hu
  obtain ⟨v, dv, E, huv, hvdv, hE⟩ := hvel
  have hdata : ‖load‖ + ‖f‖ + ‖df‖ ≤ (N + 1) * D := by
    dsimp only [D]
    nlinarith only [hloadNorm, hN, norm_nonneg G, norm_nonneg f, norm_nonneg df]
  refine ⟨v, dv, E, huv, hvdv, ?_⟩
  intro t htm
  calc
    _ ≤ K₂ * (‖load‖ + ‖f‖ + ‖df‖) := hE t htm
    _ ≤ K₂ * ((N + 1) * D) := mul_le_mul_of_nonneg_left hdata hK₂.le
    _ = B * D := by dsimp only [B]; ring

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
