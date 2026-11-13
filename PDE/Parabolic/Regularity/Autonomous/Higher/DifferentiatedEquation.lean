/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev
public import PDE.Parabolic.Regularity.Autonomous.Higher.DifferentiatedEnergy
import PDE.Parabolic.Regularity.Autonomous.Higher.EllipticBootstrap

/-!
# Regularity from the differentiated parabolic equation

For the symmetric principal-part case (`b = c = 0`) of Evans's §7.1.3, Theorem 5(ii),
suppose the original and differentiated weak equations hold. Then
`exists_second_time_derivative_and_spatial_h2_lift` gives:

* from the differentiated energy estimate,
  `uₜ ∈ L∞(0,T;L²(Ω)) ∩ L²(0,T;H¹₀(Ω))`;
* the differentiated residual is `uₜₜ ∈ L²(0,T;H⁻¹(Ω))`;
* from the pointwise elliptic lift, `u ∈ L∞(0,T;H²(Ω))`;
* the quantitative bounds, which are the principal-part components of
  Evans's estimate (47).

The witnesses are the coercivity constant, `uₜₜ`, a continuous representative
of `uₜ`, and the `H²` lift. The pivot-valued trajectory is the image of `uₜ`
under the Gelfand-triple inclusion.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5 (Improved regularity), (47), p. 382, and
  steps 3-7 of its proof, (49)-(54), pp. 384-386.
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
Construct the time and space regularity witnesses for the differentiated
autonomous equation.

Uniform ellipticity gives a coercivity constant `C > 0`. The differentiated
energy theorem, applied to the pivot trajectory `J uₜ`, produces `uₜₜ`, a
continuous `L²(Ω)` representative of `uₜ`, and the energy bounds. At almost
every time the original equation is the elliptic problem `A u = f - uₜ`, and
the global `H²` solution operator gives the lift.
-/
theorem exists_second_time_derivative_and_spatial_h2_lift
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
    (u ut : Lp
      (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : DerivLp n 2 Ω)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    let μ := volume.restrict (Set.Ioc t₀ t₁)
    let V := H¹₀(Ω)
    let H := DerivLp n 2 Ω
    let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen
    let utH : Lp H 2 μ := T.inclusion.compLpL 2 μ ut
    HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity H) f
      ((GelfandTriple.identity H).energyToDual.compLpL 2 μ ft) →
    (∀ᵐ t ∂μ, ∀ v : V,
      ⟪utH t, T.inclusion v⟫_ℝ +
          autonomousDivergenceFormOperator A
            ((u : ℝ → V) t) v =
        ⟪f t, T.inclusion v⟫_ℝ) →
    IsGelfandIntegratedWeakSolution
      T (fun _ ↦ autonomousDivergenceFormOperator A)
      (fun t ↦ (T.pivotToDual.compLpL 2 μ ft) t) ut utInit →
    ∃ (C : ℝ)
        (utt : Lp (StrongDual ℝ V) 2 μ)
        (utRep : ℝ → H)
        (h2Lift : Lp (W^{2,2}(Ω)) 2 μ),
      let energyBound := differentiatedEnergyBound hΩ ft utInit C
      0 < C ∧
      HasGelfandWeakTimeDerivativeOn
        T ut utt ∧
      ContinuousOn utRep (Set.Icc t₀ t₁) ∧
      (utRep =ᵐ[μ] fun t ↦ utH t) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖utRep t‖ ≤ Real.sqrt energyBound) ∧
      (∫ t, ‖(ut : ℝ → V) t‖ ^ 2 ∂μ) ≤ energyBound / C ∧
      ‖utt‖ ≤
        ‖T.pivotToDual‖ * ‖ft‖ +
          ‖autonomousDivergenceFormOperator A‖ *
            Real.sqrt (energyBound / C) ∧
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[μ] fun t ↦
          h10SubtypeL (n := n) (Ω := Ω)
            ((u : ℝ → V) t)) ∧
      MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞) μ ∧
      ∀ᵐ t ∂μ,
        ‖h2Lift t‖ ≤
          ‖globalH2SolveCLM hΩ A a haRep haC1
            alpha halpha hElliptic‖ *
            (timeSobolevBound f ft + Real.sqrt energyBound) := by
  intro μ V H T utH hfIsH1 huEvolution hutEvolution
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ H) := borel (StrongDual ℝ H)
  let : BorelSpace (StrongDual ℝ H) := ⟨rfl⟩
  have hutH :
      (utH : ℝ → H) =ᵐ[μ] fun t ↦
        baseCoordCLM (n := n) (Ω := Ω)
          ((ut : ℝ → V) t) := by
    simpa only [utH, T, V, H,
      SobolevSpace.GraphSpace.h10L2GelfandTriple_inclusion_apply] using
      T.inclusion.coeFn_compLpL ut
  obtain ⟨C, hC, hcoercive⟩ :=
    exists_autonomous_coercivity_constant
      hΩ A a haRep alpha halpha hElliptic
  obtain
      ⟨utt, utRep, huttWeak, hutRepContinuous, hutRepEq, hutRepBound,
        hutEnergyBound, huttBound⟩ :=
    exists_second_time_derivative_with_energy_bounds
      t₀ t₁ ht hΩ A ft ut utH utInit C hC hcoercive
      hutEvolution hutH
  let forcingBound := timeSobolevBound f ft
  have hfBound : ∀ᵐ t ∂μ, ‖f t‖ ≤ forcingBound :=
    hfIsH1.ae_norm_le_timeSobolevBound_of_identity ht
  have hutHBound :
      ∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt (differentiatedEnergyBound hΩ ft utInit C) := by
    filter_upwards [hutRepEq, ae_restrict_mem measurableSet_Ioc] with t hEq ht
    rw [← hEq]
    exact hutRepBound t (Set.Ioc_subset_Icc_self ht)
  obtain ⟨h2Lift, h2LiftOrderOne, h2LiftMemLp, h2LiftBound⟩ :=
    exists_spatial_h2_lift
      t₀ t₁ hΩ A a haRep haC1 f utH u alpha halpha hElliptic
      forcingBound (differentiatedEnergyBound hΩ ft utInit C)
      hfBound hutHBound
      (by
        simpa only [utH, T, V, H, μ,
          SobolevSpace.GraphSpace.h10L2GelfandTriple_inclusion_apply,
          autonomousDivergenceFormOperator] using huEvolution)
  exact ⟨C, utt, utRep, h2Lift, hC, huttWeak, hutRepContinuous, hutRepEq, hutRepBound,
    hutEnergyBound, huttBound, h2LiftOrderOne, h2LiftMemLp, h2LiftBound⟩

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
