/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Spatial
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional

/-!
# Assembling the next parabolic regularity tuple

A regularity tuple for the differentiated solution gives every positive time
derivative. The elliptic residual constructs the missing head
field. Injectivity of the Sobolev base coordinate lifts the time derivative
identity to its full common spatial order.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The elliptic step constructs the next head field and keeps every adjacent
derivative and every norm term of the differentiated tuple. -/
theorem exists_assembled_solution_jet (P : SmoothFullCoefficients n Ω) (m : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (2 * (m + 1) + 2) Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ E : ℝ, 0 < E ∧
      ∀ (F V : ForcingJet n Ω a b (m + 1))
        (u v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (g : DerivLp n 2 Ω),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) F.headBase) u g →
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
        ((h10L2GelfandTriple hopen).energyToDual.compLpL
          2 (volume.restrict (Ioc a b)) v) →
      V.HasWeakDerivatives →
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        wkpBaseCoordinateCLM (V.head t) = baseCoordCLM (v t)) →
      ∃ W : ForcingJet n Ω a b (m + 1 + 1), W.HasWeakDerivatives ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          wkpBaseCoordinateCLM (W.head t) = baseCoordCLM (u t)) ∧
        W.normSum ≤ E * (‖F.head‖ + ‖V.head‖ + ‖u‖) + V.normSum := by
  obtain ⟨E, hE, hspatial⟩ :=
    exists_higher_spatial_lift P (2 * (m + 1)) hopen hbounded hgraph halpha hell
  refine ⟨E, hE, ?_⟩
  intro F V u v g hu huv hV hVbase
  let T := h10L2GelfandTriple hopen
  have hderiv : HasGelfandWeakTimeDerivativeOn T u
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) V.headBase) := by
    apply HasGelfandWeakTimeDerivativeOn.congr_ae Filter.EventuallyEq.rfl _ huv
    filter_upwards [T.energyToDual.coeFn_compLpL v,
      T.pivotToDual.coeFn_compLpL V.headBase, V.headBase_ae, hVbase]
      with t ht hpt hbt hvt
    rw [ht, hpt, hbt, hvt]
    rfl
  have hsp := hspatial F.head V.head F.headBase V.headBase u g
    F.headBase_ae.symm V.headBase_ae.symm hu hderiv
  have hex : ∃ U : Lp (W^{(2 * (m + 1 + 1)),2}(Ω)) 2
      (volume.restrict (Ioc a b)),
      (∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (U t) = baseCoordCLM (u t)) ∧
      ‖U‖ ≤ E * (‖F.head‖ + ‖V.head‖ + ‖u‖) := by
    rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by omega]
    exact hsp
  obtain ⟨U, hU, hUnorm⟩ := hex
  have hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (U t))
      (fun t ↦ wkpBaseCoordinateCLM (V.head t)) := by
    apply hderiv.pivot_hasWeakTimeDerivativeOn.congr_ae_restrict measurableSet_Ioo
    · exact (Filter.EventuallyEq.symm hU).filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
    · exact V.headBase_ae.filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  refine ⟨(U, V), ForcingJet.HasWeakDerivatives.cons_of_base
    (m := m + 1) (V := V) hopen U hV hweak, hU, ?_⟩
  exact add_le_add hUnorm le_rfl

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
