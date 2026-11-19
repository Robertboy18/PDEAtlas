/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Higher.DifferentiatedEnergy.CoerciveEnergy
public import PDE.Parabolic.Regularity.Autonomous.Higher.Form
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Differentiated energy bounds for autonomous parabolic equations

We apply the abstract coercive-energy argument to the time-differentiated
equation in the symmetric principal-part case of Evans's §7.1.3, Theorem 5(ii).
Evans proves the corresponding bounds for the Galerkin approximations, (51) and
step 7 of his proof, and then passes to the limit; we prove them for the limiting
differentiated equation.

Given a coercivity constant `C > 0` and the differentiated weak equation,
`exists_second_time_derivative_with_energy_bounds` constructs

* the weak second derivative `uₜₜ`;
* a continuous `L²(Ω)` representative of `uₜ`,

together with the `L²(Ω)` bound on the representative at every time of the
closed interval and the `L²_t H¹₀_x` and `L²_t H⁻¹_x` estimates. The
differentiated forcing is the Bochner lift of `fₜ` through the pivot-to-dual
map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5 (Improved regularity), (47), p. 382, and
  steps 4 and 7 of its proof, (50)-(51), pp. 384-386.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat
namespace AutonomousRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

attribute [local instance 101] secondCountableTopologyEither_of_left

/--
The scalar budget produced by a coercive energy estimate.

The first two arguments are the norm of the initial state and the `L²`
norm of the forcing. The formula does not mention the underlying spaces, so
the analytic and data bounds can be compared directly.
-/
def coerciveEnergyBound
    (initialNorm forcingNorm coercivityConstant : ℝ) : ℝ :=
  initialNorm ^ 2 +
    (1 / coercivityConstant) * forcingNorm ^ 2

/--
The differentiated energy budget written only in terms of `uₜ(t₀)` and the
prescribed forcing derivative `fₜ`.

The pivot-to-dual operator norm appears because `fₜ` is given in `L²(Ω)`,
whereas the differentiated equation is valued in `H⁻¹(Ω)`.
-/
def differentiatedEnergyBound
    {t₀ t₁ : ℝ}
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : DerivLp n 2 Ω)
    (coercivityConstant : ℝ) : ℝ :=
  coerciveEnergyBound ‖utInit‖
    (‖(_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen).pivotToDual‖ * ‖ft‖)
    coercivityConstant

/-- The differentiated energy budget is nonnegative when the coercivity
constant is nonnegative. -/
theorem differentiated_energy_bound_nonneg
    {t₀ t₁ : ℝ}
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : DerivLp n 2 Ω)
    {coercivityConstant : ℝ}
    (hCoercivityConstant : 0 ≤ coercivityConstant) :
    0 ≤ differentiatedEnergyBound hΩ ft utInit coercivityConstant := by
  rw [differentiatedEnergyBound, coerciveEnergyBound]
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg
      (one_div_nonneg.mpr hCoercivityConstant)
      (sq_nonneg _))

/-- Increasing the forcing norm can only increase a coercive energy budget. -/
private theorem coerciveEnergyBound_mono_forcing
    (initialNorm forcingNorm₁ forcingNorm₂ coercivityConstant : ℝ)
    (hCoercivityConstant : 0 ≤ coercivityConstant)
    (hforcing : forcingNorm₁ ≤ forcingNorm₂)
    (hforcing₁ : 0 ≤ forcingNorm₁)
    (hforcing₂ : 0 ≤ forcingNorm₂) :
    coerciveEnergyBound initialNorm forcingNorm₁ coercivityConstant ≤
      coerciveEnergyBound initialNorm forcingNorm₂ coercivityConstant := by
  rw [coerciveEnergyBound, coerciveEnergyBound]
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hforcing₁ hforcing₂).2 hforcing)
      (one_div_nonneg.mpr hCoercivityConstant))

/-- An integral bound on the squared pointwise norm gives the corresponding
Bochner `L²` norm bound. -/
private theorem norm_L2_le_sqrt_of_integral_norm_sq_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (u : Lp E 2 μ) {energyBound : ℝ}
    (hEnergyBound : 0 ≤ energyBound)
    (hIntegral : (∫ t, ‖(u : α → E) t‖ ^ 2 ∂μ) ≤ energyBound) :
    ‖u‖ ≤ Real.sqrt energyBound := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hEnergyBound,
    MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  exact hIntegral

/--
For an autonomous equation, the weak derivative is bounded by the forcing
norm plus the operator norm times the state norm.
-/
private theorem norm_weak_derivative_le_of_autonomous_equation
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {t₀ t₁ : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (Aop : V →L[ℝ] StrongDual ℝ V)
    (ellDot : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (ut : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : H)
    (utt : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (huttWeak : HasGelfandWeakTimeDerivativeOn T ut utt)
    (hutEvolution :
      IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
        (fun t ↦ ellDot t) ut utInit)
    {forcingBound stateBound : ℝ}
    (hforcingNorm : ‖ellDot‖ ≤ forcingBound)
    (hutNorm : ‖ut‖ ≤ stateBound) :
    ‖utt‖ ≤ forcingBound + ‖Aop‖ * stateBound := by
  exact (huttWeak.norm_le_of_integrated_solution
      (fun v ↦ aestronglyMeasurable_const.apply_continuousLinearMap v) ‖Aop‖
      (.of_forall fun _ ↦ le_rfl) hutEvolution).trans
    (add_le_add hforcingNorm (mul_le_mul_of_nonneg_left hutNorm (norm_nonneg Aop)))

/--
Construct a continuous `L²(Ω)` representative of `uₜ` together with its weak
time derivative `uₜₜ`.

Both estimates come from the same coercive energy inequality. The bound on
the continuous representative holds at every point of `Icc t₀ t₁`.
-/
theorem exists_continuous_first_time_derivative_with_energy_bounds
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (ut : Lp
      (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : DerivLp n 2 Ω)
    (coercivityConstant : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : H¹₀(Ω),
        coercivityConstant * ‖w‖ ^ 2 ≤
          autonomousDivergenceFormOperator A w w)
    (hutEvolution :
      IsGelfandIntegratedWeakSolution
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen)
        (fun _ ↦ autonomousDivergenceFormOperator A)
        (fun t ↦
          ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
            hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
              2 (volume.restrict (Set.Ioc t₀ t₁)) ft) t)
        ut utInit) :
    ∃ (utt : Lp
          (StrongDual ℝ
            (H¹₀(Ω)))
          2 (volume.restrict (Set.Ioc t₀ t₁)))
        (utRep : ℝ → DerivLp n 2 Ω),
      HasGelfandWeakTimeDerivativeOn
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen) ut utt ∧
      ContinuousOn utRep (Set.Icc t₀ t₁) ∧
      (utRep =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
        fun t ↦
          baseCoordCLM (n := n) (Ω := Ω)
            ((ut : ℝ → H¹₀(Ω)) t)) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖utRep t‖ ≤
          Real.sqrt
            (differentiatedEnergyBound
              hΩ ft utInit coercivityConstant)) ∧
      (∫ t, ‖(ut : ℝ → H¹₀(Ω)) t‖ ^ 2
        ∂(volume.restrict (Set.Ioc t₀ t₁))) ≤
          differentiatedEnergyBound hΩ ft utInit coercivityConstant /
            coercivityConstant := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  -- Fix the norm on the Bochner type without replacing its
  -- measurable-space instance.
  let : Norm (Lp V 2 μ) := MeasureTheory.Lp.instNorm
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
    hΩ.toC1ExtensionAtlas.isOpen
  let Aop : V →L[ℝ] StrongDual ℝ V :=
    autonomousDivergenceFormOperator A
  let ellDot : Lp (StrongDual ℝ V) 2 μ :=
    T.pivotToDual.compLpL 2 μ ft
  obtain ⟨utt, Eut, huttWeak, hrepBound, hutEnergyBound⟩ :=
    CoerciveEnergy.exists_continuous_pivot_with_coercive_bounds (V := V) (H := H) ht T Aop
      ellDot ut utInit hutEvolution coercivityConstant hCoercivityConstant hcoercive
  have hBudgetLe : coerciveEnergyBound ‖utInit‖ ‖ellDot‖ coercivityConstant ≤
      differentiatedEnergyBound hΩ ft utInit coercivityConstant :=
    coerciveEnergyBound_mono_forcing ‖utInit‖ ‖ellDot‖ (‖T.pivotToDual‖ * ‖ft‖)
      coercivityConstant hCoercivityConstant.le (T.pivotToDual.norm_compLp_le ft)
      (norm_nonneg ellDot) (mul_nonneg (norm_nonneg T.pivotToDual) (norm_nonneg ft))
  refine ⟨utt, Eut.representative, huttWeak,
    by simpa only [Set.uIcc_of_le ht.le] using Eut.continuousOn, ?_,
    fun t ht ↦ (hrepBound t ht).trans (Real.sqrt_le_sqrt hBudgetLe),
    hutEnergyBound.trans (div_le_div_of_nonneg_right hBudgetLe hCoercivityConstant.le)⟩
  simpa only [T, V, H, SobolevSpace.GraphSpace.h10L2GelfandTriple_inclusion_apply] using
    Eut.ae_eq_inclusion.filter_mono (ae_mono (volume.restrict_mono_set
      (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc)))

/--
The differentiated energy witnesses and the quantitative energy estimates
for the principal-part case.

In addition to the coercive estimates, the continuous representative agrees
a.e. with the given pivot-valued trajectory `utH`. The last inequality is the
norm estimate for `uₜₜ = J* fₜ - A uₜ` in `L²(t₀,t₁;H⁻¹(Ω))`, with the
operator norm of `A` as coefficient.
-/
theorem exists_second_time_derivative_with_energy_bounds
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (ut : Lp
      (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utH : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : DerivLp n 2 Ω)
    (coercivityConstant : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : H¹₀(Ω),
        coercivityConstant * ‖w‖ ^ 2 ≤
          autonomousDivergenceFormOperator A w w)
    (hutEvolution :
      IsGelfandIntegratedWeakSolution
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen)
        (fun _ ↦ autonomousDivergenceFormOperator A)
        (fun t ↦
          ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
            hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
              2 (volume.restrict (Set.Ioc t₀ t₁)) ft) t)
        ut utInit)
    (hutH :
      (utH : ℝ → DerivLp n 2 Ω)
        =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
          fun t ↦
            baseCoordCLM (n := n) (Ω := Ω)
              ((ut : ℝ → H¹₀(Ω)) t)) :
    ∃ (utt : Lp
          (StrongDual ℝ
            (H¹₀(Ω)))
          2 (volume.restrict (Set.Ioc t₀ t₁)))
        (utRep : ℝ → DerivLp n 2 Ω),
      HasGelfandWeakTimeDerivativeOn
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen) ut utt ∧
      ContinuousOn utRep (Set.Icc t₀ t₁) ∧
      (utRep =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
        fun t ↦ utH t) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖utRep t‖ ≤
          Real.sqrt
            (differentiatedEnergyBound
              hΩ ft utInit coercivityConstant)) ∧
      (∫ t, ‖(ut : ℝ → H¹₀(Ω)) t‖ ^ 2
        ∂(volume.restrict (Set.Ioc t₀ t₁))) ≤
          differentiatedEnergyBound hΩ ft utInit coercivityConstant /
            coercivityConstant ∧
      ‖utt‖ ≤
        ‖(_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen).pivotToDual‖ * ‖ft‖ +
          ‖autonomousDivergenceFormOperator A‖ *
            Real.sqrt
              (differentiatedEnergyBound
                  hΩ ft utInit coercivityConstant /
                coercivityConstant) := by
  obtain
      ⟨utt, utRep, huttWeak, hutRepContinuous, hutRepEq, hutRepBound,
        hutEnergyBound⟩ :=
    exists_continuous_first_time_derivative_with_energy_bounds
      t₀ t₁ ht hΩ A ft ut utInit coercivityConstant
      hCoercivityConstant hcoercive hutEvolution
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  -- Fix the norm on the Bochner type without replacing its
  -- measurable-space instance.
  let : Norm (Lp V 2 μ) := MeasureTheory.Lp.instNorm
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
    hΩ.toC1ExtensionAtlas.isOpen
  let Aop : V →L[ℝ] StrongDual ℝ V :=
    autonomousDivergenceFormOperator A
  let ellDot : Lp (StrongDual ℝ V) 2 μ :=
    T.pivotToDual.compLpL 2 μ ft
  have hutNorm : ‖ut‖ ≤ Real.sqrt
      (differentiatedEnergyBound hΩ ft utInit coercivityConstant / coercivityConstant) :=
    norm_L2_le_sqrt_of_integral_norm_sq_le ut (div_nonneg
      (differentiated_energy_bound_nonneg hΩ ft utInit hCoercivityConstant.le)
      hCoercivityConstant.le) hutEnergyBound
  exact ⟨utt, utRep, huttWeak, hutRepContinuous, hutRepEq.trans hutH.symm, hutRepBound,
    hutEnergyBound, norm_weak_derivative_le_of_autonomous_equation T Aop ellDot ut utInit utt
      huttWeak hutEvolution (T.pivotToDual.norm_compLp_le ft) hutNorm⟩

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
