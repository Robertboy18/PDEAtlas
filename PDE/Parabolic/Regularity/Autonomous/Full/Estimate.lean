/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Existence
public import PDE.Parabolic.Regularity.Autonomous.Estimate
public import PDE.Parabolic.Regularity.Autonomous.Higher.Form
import PDE.Analysis.Evolution.Integrated.Uniqueness

/-!
# Improved regularity with a full autonomous lower-order term

The basic Gårding estimate controls the lower-order term as an `L²` load.
The symmetric principal estimate then gives the pivot time derivative and
the spatial `H²` lift. Uniqueness identifies this construction with every
weak solution, and the resulting constant depends only on the operator,
domain, and time interval.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem sqrt_quadratic_bound {M L x y D : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hD : 0 ≤ D) (hxD : x ≤ D) (hyD : y ≤ L * D) :
    Real.sqrt (M * x ^ 2 + 2 * y ^ 2) ≤
      Real.sqrt (M + 2 * L ^ 2) * D := by
  have hxs : x ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hx hD).mpr hxD
  have hys : y ^ 2 ≤ (L * D) ^ 2 := (sq_le_sq₀ hy (mul_nonneg hL hD)).mpr hyD
  calc
    _ ≤ Real.sqrt ((M + 2 * L ^ 2) * D ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_left hxs hM]
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD]

private theorem principal_solution_eq
    {t₀ t₁ : ℝ} (ht : t₀ < t₁) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
    (g : H¹₀(Ω))
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
    (q : AutonomousWeakSolutionWithL2TimeDerivative t₀ t₁ hopen A f g)
    (hpos : ∀ v, 0 ≤ variableCoeffForm
      (multiplicationCoefficientOperator (coefficientBase A)) v v)
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ variableCoeffForm (multiplicationCoefficientOperator (coefficientBase A)))
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL
        2 (volume.restrict (Ioc t₀ t₁)) f) u (baseCoordCLM (n := n) (Ω := Ω) g)) :
    q.u = u := by
  let T := h10L2GelfandTriple hopen
  let Aop := variableCoeffForm (multiplicationCoefficientOperator (coefficientBase A))
  have hfcoe := T.pivotToDual.coeFn_compLpL f
  have hq := q.weak_solution.congr_forcing_ae hfcoe.symm
  exact IsGelfandIntegratedWeakSolution.unique
    (T := T) (B := fun _ ↦ Aop)
    (fun _ ↦ aestronglyMeasurable_const) ‖Aop‖
    (Eventually.of_forall fun _ ↦ le_rfl) (fun _ _ ↦ hpos) hq hu ht

variable [Fact (0 < n)]

/-- Every full autonomous weak solution has `u ∈ L∞(H¹₀) ∩ L²(H²)` and
`u' ∈ L²(L²)`, with the sum estimate fixed before its initial and forcing
data. The lower-order operator need only be bounded from `H¹₀` to `L²`. -/
theorem exists_full_form_improved_regularity
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hΩ : C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := ∞) (Ω := Ω) (A i j) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
        fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (g : H¹₀(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
          (fun _ ↦ autonomousDivergenceFormOperator A +
            (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.comp R)
          ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (U₂ : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen) u
          ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) ut) ∧
        (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
          lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2) (by omega) (U₂ t) =
            h10SubtypeL (n := n) (Ω := Ω) (u t)) ∧
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
        (eLpNormEssSup (fun t ↦ u t) (volume.restrict (Ioc t₀ t₁))).toReal +
          ‖U₂‖ + ‖ut‖ ≤ K * (‖g‖ + ‖f‖) := by
  let hopen := hΩ.toC1ExtensionAtlas.isOpen
  let μ := volume.restrict (Ioc t₀ t₁)
  let T := h10L2GelfandTriple hopen
  let Aop := autonomousDivergenceFormOperator A
  let S := globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic
  obtain ⟨C, hC, hcoercive⟩ :=
    exists_autonomous_coercivity_constant hΩ A a haRep alpha halpha hElliptic
  have hex :=
    @exists_full_form_state_bound n Ω hopen hΩ.toC1ExtensionAtlas.bounded
      Aop R C t₀ t₁ hC ht hcoercive
  obtain ⟨K₀, hK₀, hbasic⟩ := hex
  let L := 1 + ‖R‖ * K₀
  let Q := ‖Aop‖ + 2 * L ^ 2
  let K := Real.sqrt (Q / C) + ‖S‖ * (L + Real.sqrt Q) + Real.sqrt Q + 1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro f g u hu
  let D := ‖g‖ + ‖f‖
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have huNorm := hbasic f g u hu
  let F := f - R.compLpL 2 μ u
  have hF : ‖F‖ ≤ L * D := by
    have hr := (R.norm_compLp_le u).trans (mul_le_mul_of_nonneg_left huNorm (norm_nonneg R))
    have hfD : ‖f‖ ≤ D := le_add_of_nonneg_left (norm_nonneg g)
    exact (norm_sub_le _ _).trans ((add_le_add hfD hr).trans_eq (by dsimp only [L]; ring))
  have hAprincipal : IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
      (T.pivotToDual.compLpL 2 μ F) u (baseCoordCLM (n := n) (Ω := Ω) g) :=
    hu.sub_pivot_perturbation Aop R
  have hAbound (v w : H¹₀(Ω)) : |Aop v w| ≤ ‖Aop‖ * ‖v‖ * ‖w‖ := by
    simpa only [Real.norm_eq_abs] using Aop.le_opNorm₂ v w
  have hprincipal :=
    exists_autonomous_symmetric_solution_with_spatial_h2_data_bounds
      t₀ t₁ ht hΩ A a haRep haC1 haSymm F g alpha halpha hElliptic
      ‖Aop‖ (norm_nonneg Aop) hAbound C hC hcoercive
  obtain ⟨q, U₂, hU₂, hsup, hut, hU₂norm⟩ := hprincipal
  have hpos (v : H¹₀(Ω)) : 0 ≤ Aop v v :=
    (mul_nonneg hC.le (sq_nonneg ‖v‖)).trans (hcoercive v)
  have hqu := principal_solution_eq ht hopen A F g u q hpos hAprincipal
  have hbudget : Real.sqrt (‖Aop‖ * ‖g‖ ^ 2 + 2 * ‖F‖ ^ 2) ≤
      Real.sqrt Q * D :=
    sqrt_quadratic_bound (norm_nonneg Aop) hL (norm_nonneg g) (norm_nonneg F) hD
      (le_add_of_nonneg_right (norm_nonneg f)) hF
  have hstate : Real.sqrt ((‖Aop‖ * ‖g‖ ^ 2 + 2 * ‖F‖ ^ 2) / C) ≤
      Real.sqrt (Q / C) * D := by
    rw [Real.sqrt_div' _ hC.le, Real.sqrt_div' _ hC.le]
    exact (div_le_div_of_nonneg_right hbudget (Real.sqrt_nonneg C)).trans_eq (by ring)
  have hsupReal :
      (eLpNormEssSup (fun t ↦ u t) μ).toReal ≤ Real.sqrt (Q / C) * D := by
    rw [hqu] at hsup
    exact ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup).trans_eq
      (ENNReal.toReal_ofReal (Real.sqrt_nonneg _))).trans hstate
  have hutNorm : ‖q.ut‖ ≤ Real.sqrt Q * D := hut.trans hbudget
  have hH₂Norm : ‖U₂‖ ≤ ‖S‖ * (L + Real.sqrt Q) * D :=
    hU₂norm.trans ((mul_le_mul_of_nonneg_left (add_le_add hF hbudget) (norm_nonneg S)).trans_eq
      (by ring))
  refine ⟨q.ut, U₂, ?_, ?_, ?_, ?_⟩
  · simpa only [hqu] using q.weak_time_derivative
  · filter_upwards [hU₂] with t ht
    simpa only [hqu] using ht
  · simpa only [hqu] using q.state_memLp_top
  · calc
      _ ≤ Real.sqrt (Q / C) * D + ‖S‖ * (L + Real.sqrt Q) * D +
          Real.sqrt Q * D := add_le_add (add_le_add hsupReal hH₂Norm) hutNorm
      _ ≤ K * D := by
        dsimp only [K]
        nlinarith only [hD]

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
