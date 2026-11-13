/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Existence
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.MeasurableForcing
import PDE.Analysis.Evolution.Integrated.Uniqueness
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Autonomous parabolic regularity estimate

For an autonomous symmetric divergence-form parabolic equation with principal part only,
we prove the `b = c = 0` case of Evans's §7.1.3, Theorem 5(i), estimate (46), with bounds
in terms of the data alone:

* the essential supremum in time of the `H¹₀` norm of the solution;
* the Bochner `L²` norm of the time derivative;
* the Bochner `L²` norm of the spatial `H²` representative.

`exists_autonomous_symmetric_solution_with_spatial_h2` (in `Existence`) constructs the
solution, its pivot-valued time derivative, and its spatial `H²` lift, but its `H²`
estimate contains `‖f - u_t‖`. The main theorem,
`exists_autonomous_symmetric_solution_with_spatial_h2_data_bounds`, combines it with the
quantitative autonomous Galerkin estimate and uniqueness of the integrated weak solution.
Every right-hand side then involves only an operator bound, a coercivity constant, the
norm of the elliptic `H²` solution operator, the initial datum, and the forcing.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 4 (Uniqueness of weak solutions), p. 379;
  §7.1.3, Theorem 5 (Improved regularity), (46), p. 382, and steps 1-3 of its proof, (48)-(49),
  pp. 382-384.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace PDE.Parabolic.DivergenceFormHeat

open PDE.Analysis.Evolution
open PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

/-- Increasing the coefficient in the nonnegative part of an energy budget
can only increase the budget. -/
private theorem energy_budget_mono
    {operatorNorm operatorBound stateEnergy forcingEnergy : ℝ}
    (hOperatorNorm : operatorNorm ≤ operatorBound)
    (hStateEnergy : 0 ≤ stateEnergy) :
    operatorNorm * stateEnergy + forcingEnergy ≤
      operatorBound * stateEnergy + forcingEnergy := by
  gcongr

/-- The quantitative autonomous Galerkin state bound holds for every weak
solution, by uniqueness, with the operator norm replaced by any upper bound. -/
private theorem ae_norm_le_data_bound_of_autonomous_solution
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {t₀ t₁ coercivityConstant operatorBound : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (trials : StableTrialSystem T)
    (htrials : trials.stabilityConstant = 1)
    (Aop : V →L[ℝ] StrongDual ℝ V)
    (f : Lp H 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : V)
    (u : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (hsolution :
      IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
        (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit))
    (ht : t₀ < t₁)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : V, coercivityConstant * ‖w‖ ^ 2 ≤ Aop w w)
    (hA_symm : ∀ v w : V, Aop v w = Aop w v)
    (hA_nonneg : ∀ w : V, 0 ≤ Aop w w)
    (hOperatorNorm : ‖Aop‖ ≤ operatorBound) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ‖(u : ℝ → V) t‖ ≤
        Real.sqrt
          ((operatorBound * ‖uInit‖ ^ 2 + 2 * ‖f‖ ^ 2) /
            coercivityConstant) := by
  obtain ⟨uQuant, _utQuant, hsolutionQuant, _hderivativeQuant, _hevolutionQuant, _hutQuant,
      hstateQuant⟩ :=
    exists_of_symmetric_principal_measurable_galerkin_L2 (N := 0)
      T trials.space trials.finiteDimensional trials.projection
      trials.denseEnergy (fun _ ↦ Aop) (fun _ ↦ 0) f ht hCoercivityConstant
      aestronglyMeasurable_const ‖Aop‖₊ (fun _ _ ↦ le_rfl) uInit
      (LipschitzWith.const Aop).lipschitzOnWith.absolutelyContinuousOnInterval
      (Filter.Eventually.of_forall fun t ↦ hasDerivAt_const t Aop)
      (Filter.Eventually.of_forall fun _ ↦
        (@norm_zero (V →L[ℝ] StrongDual ℝ V) inferInstance).le)
      (fun _ _ ↦ hA_symm) (fun _ _ ↦ hcoercive)
  simp only [NNReal.coe_zero, zero_div, add_zero, zero_mul, htrials, NNReal.coe_one,
    one_mul] at hstateQuant
  rw [← hsolutionQuant.unique (fun v ↦ aestronglyMeasurable_const.apply_continuousLinearMap v)
    ‖Aop‖ (.of_forall fun _ ↦ le_rfl) (fun _ _ w ↦ hA_nonneg w) hsolution ht]
  filter_upwards [hstateQuant] with t htBound
  exact htBound.trans (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
    (energy_budget_mono hOperatorNorm (sq_nonneg ‖uInit‖)) hCoercivityConstant.le))

/--
The case `b = c = 0` of Evans's §7.1.3, Theorem 5(i), estimate (46), with
data-only right-hand sides.

Write `V = H¹₀(Ω)`, `H = L²(Ω)`, and suppose `operatorBound` bounds the
autonomous principal form. Set

`energyBudget = operatorBound ‖uInit‖² + 2 ‖f‖²`.

For any coercivity constant `coercivityConstant > 0` of the form, the theorem
constructs the weak solution `u`, its pivot derivative `ut`, and the spatial
`H²` lift `h2Lift`, and proves

`ess sup_t ‖u(t)‖_V ≤ sqrt (energyBudget / coercivityConstant)`,

`‖ut‖_{L²_t H} ≤ sqrt energyBudget`,

`‖h2Lift‖_{L²_t H²} ≤ ‖S₂‖ (‖f‖_{L²_t H} + sqrt energyBudget)`,

where `S₂` is the global elliptic `H²` solution operator.  In particular,
neither `ut` nor `h2Lift` occurs on any right-hand side.

The coercivity constant is taken as a hypothesis so that it appears in the
bounds, rather than coming from an existence proof.
-/
theorem exists_autonomous_symmetric_solution_with_spatial_h2_data_bounds
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (f : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : H¹₀(Ω))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (operatorBound : ℝ) (hOperatorBoundNonneg : 0 ≤ operatorBound)
    (hA_bound :
      ∀ v w : H¹₀(Ω),
        |variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A)) v w| ≤
          operatorBound * ‖v‖ * ‖w‖)
    (coercivityConstant : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : H¹₀(Ω),
        coercivityConstant * ‖w‖ ^ 2 ≤
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A)) w w) :
    ∃ (solution :
        AutonomousWeakSolutionWithL2TimeDerivative
          t₀ t₁ hΩ.toC1ExtensionAtlas.isOpen A f uInit)
      (h2Lift : Lp (W^{2,2}(Ω)) 2
        (volume.restrict (Set.Ioc t₀ t₁))),
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
          fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((solution.u : ℝ → H¹₀(Ω)) t)) ∧
      eLpNormEssSup
          (fun t ↦
            ((solution.u : ℝ → H¹₀(Ω)) t))
          (volume.restrict (Set.Ioc t₀ t₁)) ≤
        ENNReal.ofReal
          (Real.sqrt
            ((operatorBound * ‖uInit‖ ^ 2 +
              2 * ‖f‖ ^ 2) / coercivityConstant)) ∧
      ‖solution.ut‖ ≤
        Real.sqrt
          (operatorBound * ‖uInit‖ ^ 2 +
            2 * ‖f‖ ^ 2) ∧
      ‖h2Lift‖ ≤
      ‖globalH2SolveCLM hΩ A a haRep haC1
          alpha halpha hElliptic‖ *
          (‖f‖ +
            Real.sqrt
              (operatorBound * ‖uInit‖ ^ 2 +
                2 * ‖f‖ ^ 2)) := by
  let hΩopen : IsOpen Ω := hΩ.toC1ExtensionAtlas.isOpen
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple hΩopen
  let coeff := coefficientBase A
  let h10InnerProductSpace : InnerProductSpace ℝ V := inferInstance
  let h10CompleteSpace : CompleteSpace V := inferInstance
  let Aop : V →L[ℝ] StrongDual ℝ V :=
    variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) coeff)
  let trials := _root_.SobolevSpace.GraphSpace.h10L2SpectralTrialSystem
    hΩopen hΩ.toC1ExtensionAtlas.bounded
  let energyBudget : ℝ := operatorBound * ‖uInit‖ ^ 2 + 2 * ‖f‖ ^ 2
  let stateBound : ℝ := Real.sqrt (energyBudget / coercivityConstant)
  have hA_symm (v w : V) : Aop v w = Aop w v :=
    variableCoeffForm_symm (n := n) (Ω := Ω)
      (symmetricCoefficientOperator_multiplication_of_ae (n := n) (Ω := Ω) coeff
        (coefficientBase_aeSymmetric hΩopen.measurableSet A a haRep haSymm)) v w
  have hcoercive' : ∀ w : V, coercivityConstant * ‖w‖ ^ 2 ≤ Aop w w := by
    simpa only [V, Aop, coeff, hΩopen] using hcoercive
  have hA_nonneg (w : V) : 0 ≤ Aop w w :=
    (mul_nonneg hCoercivityConstant.le (sq_nonneg ‖w‖)).trans (hcoercive' w)
  have hOperatorNorm : ‖Aop‖ ≤ operatorBound :=
    @ContinuousLinearMap.opNorm_le_bound ℝ ℝ V (StrongDual ℝ V) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance (RingHom.id ℝ) Aop operatorBound
      hOperatorBoundNonneg fun v ↦
        @ContinuousLinearMap.opNorm_le_bound ℝ ℝ V ℝ inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance (RingHom.id ℝ) (Aop v) (operatorBound * ‖v‖)
          (mul_nonneg hOperatorBoundNonneg (norm_nonneg v)) fun w ↦ by
            rw [Real.norm_eq_abs]
            simpa only [Aop, coeff, V, hΩopen] using hA_bound v w
  obtain ⟨solution, h2Lift, h2_order_one, hH2Raw⟩ :=
    exists_autonomous_symmetric_solution_with_spatial_h2
      t₀ t₁ ht hΩ A a haRep haC1 haSymm f uInit alpha halpha hElliptic
  let uV : Lp V 2 μ := solution.u
  have hsolutionBase : IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
      (fun t ↦ T.pivotToDual (f t)) uV (T.inclusion uInit) := by
    simpa only [uV, T, Aop, coeff, V, H, hΩopen, μ] using solution.weak_solution
  -- Transfer the quantitative Galerkin estimate to the solution constructed
  -- by the spatial-regularity theorem, using weak-solution uniqueness.
  have hStateBound : ∀ᵐ t ∂μ, ‖((uV : ℝ → V) t)‖ ≤ stateBound := by
    simpa only [stateBound, energyBudget, μ] using
      @ae_norm_le_data_bound_of_autonomous_solution
        V H inferInstance h10InnerProductSpace h10CompleteSpace
        inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance
        t₀ t₁ coercivityConstant operatorBound T trials
        rfl Aop f uInit uV hsolutionBase ht
        hCoercivityConstant hcoercive' hA_symm hA_nonneg hOperatorNorm
  have hutNorm : ‖solution.ut‖ ≤ Real.sqrt energyBudget :=
    Real.le_sqrt_of_sq_le (solution.time_derivative_bound.trans
      (energy_budget_mono hOperatorNorm (sq_nonneg ‖uInit‖)))
  -- Replace the intermediate `‖f - uₜ‖` term in the elliptic estimate by
  -- norms of the prescribed data only.
  have hH2Norm : ‖h2Lift‖ ≤ ‖globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic‖ *
      (‖f‖ + Real.sqrt energyBudget) :=
    hH2Raw.trans (by gcongr; exact (norm_sub_le f _).trans (by gcongr))
  refine ⟨solution, h2Lift, h2_order_one, ?_, ?_, ?_⟩
  · apply eLpNormEssSup_le_of_ae_bound
    simpa only [stateBound, energyBudget, Aop, coeff, V, H, hΩopen, μ, uV] using
      hStateBound
  · simpa only [energyBudget, Aop, coeff, V, H, hΩopen, μ] using hutNorm
  · simpa only [energyBudget, Aop, coeff, V, H, hΩopen, μ] using hH2Norm

end PDE.Parabolic.DivergenceFormHeat
