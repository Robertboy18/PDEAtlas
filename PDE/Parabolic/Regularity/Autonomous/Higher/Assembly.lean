/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Higher.DifferentiatedTrajectory
public import PDE.Parabolic.Regularity.Autonomous.Higher.DifferentiatedEnergy
import PDE.Parabolic.Regularity.Autonomous.Higher.DifferentiatedEquation

/-!
# Assembly of autonomous higher parabolic regularity

We combine the differentiated weak trajectory from the Galerkin argument with
the energy and elliptic estimates, proving the symmetric principal-part case
(`b = c = 0`) of Evans's §7.1.3, Theorem 5(ii):
`exists_differentiated_weak_trajectory_with_higher_regularity`.

The fields of `DifferentiatedWeakTrajectory` are limits along one Galerkin
subnet. The second time derivative, continuous pivot representative,
coercivity constant, and spatial `H²` lift are existential witnesses.

The energy budget `differentiatedEnergyDataBound` bounds the initial derivative by
`‖uₜ(t₀)‖ ≤ timeSobolevBound f ft + ‖strongLoad A G‖`, so it is a real number
computed from the equation data and the coercivity constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5 (Improved regularity), (47), p. 382, and
  steps 4-7 of its proof, (50)-(54), pp. 384-386.
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
The differentiated energy budget in terms of the forcing, its time derivative,
the strong initial datum, and a coercivity constant.
-/
def differentiatedEnergyDataBound
    {t₀ t₁ : ℝ}
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (G : W^{2,2}(Ω))
    (C : ℝ) : ℝ :=
  (timeSobolevBound f ft + ‖strongLoad A G‖) ^ 2 +
    (1 / C) *
      (‖(_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen).pivotToDual‖ * ‖ft‖) ^ 2

/-- The data energy budget is nonnegative for a nonnegative coercivity
constant. -/
theorem differentiated_energy_data_bound_nonneg
    {t₀ t₁ : ℝ}
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (G : W^{2,2}(Ω))
    {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ differentiatedEnergyDataBound hΩ A f ft G C := by
  rw [differentiatedEnergyDataBound]
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg (one_div_nonneg.mpr hC) (sq_nonneg _))

namespace DifferentiatedWeakTrajectory

variable {t₀ t₁ : ℝ}
variable {hΩ : SobolevSpace.C2BoundaryAtlas n Ω}
variable {A : Fin n → Fin n → W^{1,∞}(Ω)}
variable {f ft : Lp (DerivLp n 2 Ω) 2
  (volume.restrict (Set.Ioc t₀ t₁))}
variable {G : W^{2,2}(Ω)}
variable {g : H¹₀(Ω)}

/--
The differentiated energy budget is bounded by the data budget, using the
initial derivative estimate of the Galerkin trajectory.
-/
theorem differentiated_energy_bound_le_data_bound
    (trajectory : DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g)
    (C : ℝ) :
    differentiatedEnergyBound hΩ ft trajectory.utInit C ≤
      differentiatedEnergyDataBound hΩ A f ft G C := by
  have hInitialSq :
      ‖trajectory.utInit‖ ^ 2 ≤
        (timeSobolevBound f ft + ‖strongLoad A G‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg trajectory.utInit)
      (add_nonneg (timeSobolevBound_nonneg f ft)
        (norm_nonneg (strongLoad A G)))).2
      trajectory.initial_derivative_bound
  rw [differentiatedEnergyBound, coerciveEnergyBound,
    differentiatedEnergyDataBound]
  exact add_le_add hInitialSq le_rfl

end DifferentiatedWeakTrajectory

/--
Apply the differentiated energy theorem and the elliptic `H²` lift to one
differentiated weak trajectory.

The bounds are stated with the data budget. The pivot trajectory is
`T.inclusion.compLpL 2 μ trajectory.ut`, and the bound on the continuous
representative holds at every point of the closed time interval.
-/
theorem exists_higher_regularity_of_differentiated_weak_trajectory
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (hfIsH1 :
      HasGelfandWeakTimeDerivativeOn
        (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁)) ft))
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (trajectory : DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g) :
    let μ := volume.restrict (Set.Ioc t₀ t₁)
    let V := H¹₀(Ω)
    let H := DerivLp n 2 Ω
    let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen
    let utH : Lp H 2 μ := T.inclusion.compLpL 2 μ trajectory.ut
    ∃ (C : ℝ)
        (utt : Lp (StrongDual ℝ V) 2 μ)
        (utRep : ℝ → H)
        (h2Lift : Lp (W^{2,2}(Ω)) 2 μ),
      let dataBound := differentiatedEnergyDataBound hΩ A f ft G C
      0 < C ∧
      HasGelfandWeakTimeDerivativeOn T trajectory.ut utt ∧
      ContinuousOn utRep (Set.Icc t₀ t₁) ∧
      (utRep =ᵐ[μ] fun t ↦ utH t) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖utRep t‖ ≤ Real.sqrt dataBound) ∧
      (∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt dataBound) ∧
      MemLp (fun t ↦ utH t) (⊤ : ℝ≥0∞) μ ∧
      (∫ t, ‖(trajectory.ut : ℝ → V) t‖ ^ 2 ∂μ) ≤ dataBound / C ∧
      ‖utt‖ ≤
        ‖T.pivotToDual‖ * ‖ft‖ +
          ‖autonomousDivergenceFormOperator A‖ *
            Real.sqrt (dataBound / C) ∧
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[μ] fun t ↦
          h10SubtypeL (n := n) (Ω := Ω)
            ((trajectory.u : ℝ → V) t)) ∧
      MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞) μ ∧
      ∀ᵐ t ∂μ,
        ‖h2Lift t‖ ≤
          ‖globalH2SolveCLM hΩ A a haRep haC1
            alpha halpha hElliptic‖ *
            (timeSobolevBound f ft + Real.sqrt dataBound) := by
  intro μ V H T utH
  obtain ⟨C, utt, utRep, h2Lift, hC, huttWeak, hutRepContinuous, hutRepEq, hutRepBound,
      hutEnergyBound, huttBound, h2LiftOrderOne, h2LiftMemLp, h2LiftBound⟩ :=
    exists_second_time_derivative_and_spatial_h2_lift t₀ t₁ ht hΩ A a haRep haC1 f ft
      trajectory.u trajectory.ut trajectory.utInit alpha halpha hElliptic hfIsH1
      (by simpa only [GelfandTriple.pivotToDual_apply] using trajectory.ae_weak_equation)
      trajectory.time_derivative_solution
  have hEnergyLe := trajectory.differentiated_energy_bound_le_data_bound C
  have hsqrt := Real.sqrt_le_sqrt hEnergyLe
  have hDiv := div_le_div_of_nonneg_right hEnergyLe hC.le
  have hutRepDataBound (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) := (hutRepBound t ht).trans hsqrt
  have hutHDataBound :
      ∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt (differentiatedEnergyDataBound hΩ A f ft G C) := by
    filter_upwards [hutRepEq, ae_restrict_mem measurableSet_Ioc] with t hEq ht
    rw [← hEq]
    exact hutRepDataBound t (Set.Ioc_subset_Icc_self ht)
  refine ⟨C, utt, utRep, h2Lift, hC, huttWeak, hutRepContinuous, hutRepEq, hutRepDataBound,
    hutHDataBound, memLp_top_of_bound (Lp.aestronglyMeasurable utH) _ hutHDataBound,
    hutEnergyBound.trans hDiv, huttBound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDiv) (ContinuousLinearMap.opNorm_nonneg _))),
    h2LiftOrderOne, h2LiftMemLp, ?_⟩
  filter_upwards [h2LiftBound] with t hBound
  exact hBound.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsqrt) (ContinuousLinearMap.opNorm_nonneg _))

/--
Under the hypotheses of the principal-part case of Evans's §7.1.3, Theorem 5(ii),
there is a differentiated Galerkin trajectory with all the quantitative
regularity bounds.

Symmetry is used only in the Galerkin construction, for the uniform `L²_t L²_x`
bound on the Galerkin velocities. The bounds use the coercivity constant obtained
from ellipticity and depend only on the data energy budget.
-/
theorem exists_differentiated_weak_trajectory_with_higher_regularity
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
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (hfIsH1 :
      HasGelfandWeakTimeDerivativeOn
        (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁)) ft))
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω))
    (hG :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by omega) G =
        h10SubtypeL (n := n) (Ω := Ω) g)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    let μ := volume.restrict (Set.Ioc t₀ t₁)
    let V := H¹₀(Ω)
    let H := DerivLp n 2 Ω
    let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen
    ∃ (trajectory : DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g)
        (C : ℝ)
        (utt : Lp (StrongDual ℝ V) 2 μ)
        (utRep : ℝ → H)
        (h2Lift : Lp (W^{2,2}(Ω)) 2 μ),
      let utH : Lp H 2 μ := T.inclusion.compLpL 2 μ trajectory.ut
      let dataBound := differentiatedEnergyDataBound hΩ A f ft G C
      0 < C ∧
      HasGelfandWeakTimeDerivativeOn T trajectory.ut utt ∧
      ContinuousOn utRep (Set.Icc t₀ t₁) ∧
      (utRep =ᵐ[μ] fun t ↦ utH t) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖utRep t‖ ≤ Real.sqrt dataBound) ∧
      (∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt dataBound) ∧
      MemLp (fun t ↦ utH t) (⊤ : ℝ≥0∞) μ ∧
      (∫ t, ‖(trajectory.ut : ℝ → V) t‖ ^ 2 ∂μ) ≤ dataBound / C ∧
      ‖utt‖ ≤
        ‖T.pivotToDual‖ * ‖ft‖ +
          ‖autonomousDivergenceFormOperator A‖ *
            Real.sqrt (dataBound / C) ∧
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[μ] fun t ↦
          h10SubtypeL (n := n) (Ω := Ω)
            ((trajectory.u : ℝ → V) t)) ∧
      MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞) μ ∧
      ∀ᵐ t ∂μ,
        ‖h2Lift t‖ ≤
          ‖globalH2SolveCLM hΩ A a haRep haC1
            alpha halpha hElliptic‖ *
            (timeSobolevBound f ft + Real.sqrt dataBound) := by
  intro μ V H T
  obtain ⟨trajectory⟩ := nonempty_differentiated_weak_trajectory t₀ t₁ ht hΩ A a haRep haSymm
    f ft hfIsH1 G g hG alpha halpha hElliptic
  exact ⟨trajectory, exists_higher_regularity_of_differentiated_weak_trajectory t₀ t₁ ht hΩ A a
    haRep haC1 f ft hfIsH1 G g alpha halpha hElliptic trajectory⟩

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
