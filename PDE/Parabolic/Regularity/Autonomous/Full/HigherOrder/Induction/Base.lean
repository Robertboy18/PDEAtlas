/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing
public import PDE.Parabolic.Regularity.Autonomous.Full.ClassicalBoundaryData
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.DifferentiatedSolution
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# The base and energy bounds for all-order parabolic regularity

The first improved estimate constructs the complete order-zero solution tuple:
`u ∈ L²(H²)` and its weak time derivative in `L²(L²)`. The initial datum is
measured in its Sobolev norm, not the `H¹₀` norm, and the Gårding estimate gives
the energy bound used in later elliptic steps.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

private theorem norm_initial_representative_le (hopen : IsOpen Ω) {r : ℕ} (hr : 1 ≤ r)
    (g : W^{r,2}(Ω)) (g₀ : H¹₀(Ω))
    (hg : wkpBaseCoordinateCLM g = baseCoordCLM g₀) : ‖g₀‖ ≤ ‖g‖ := by
  have h : lowerOrderCLM hr g = h10SubtypeL g₀ :=
    wkpBaseCoordinateCLM_injective hopen hg
  change ‖h10SubtypeL g₀‖ ≤ ‖g‖
  rw [← h]
  exact norm_lowerOrderCLM_apply_le hr g

/-- The energy bound is controlled by the initial `W^{r,2}` norm and the
pivot forcing, uniformly over every Sobolev order at least one. -/
theorem exists_raw_initial_state_bound [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℕ), 1 ≤ r →
      ∀ (g : W^{r,2}(Ω)) (g₀ : H¹₀(Ω))
        (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))),
      wkpBaseCoordinateCLM g = baseCoordCLM g₀ →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) f) u (wkpBaseCoordinateCLM g) →
      ‖u‖ ≤ K * (‖g‖ + ‖f‖) := by
  obtain ⟨A, R, C, hC, hform, hcoercive⟩ :=
    P.exists_coercive_decomposition hopen hbounded halpha hell
  obtain ⟨K, hK, hbound⟩ :=
    exists_full_form_state_bound hopen hbounded A R hC hab hcoercive
  refine ⟨K, hK, ?_⟩
  intro r hr g g₀ f u hg hu
  rw [hform, hg] at hu
  have h := hbound f g₀ u hu
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (norm_initial_representative_le hopen hr g g₀ hg) le_rfl) hK.le)

/-- The base case constructs both entries, including the final order-zero
time derivative. It assumes only an `H¹` datum with zero boundary trace. -/
theorem exists_base_solution_jet [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (F : ForcingJet n Ω a b 0) (g : W^{1,2}(Ω))
        (g₀ : H¹₀(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))),
      wkpBaseCoordinateCLM g = baseCoordCLM g₀ →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) F.headBase) u (wkpBaseCoordinateCLM g) →
      ∃ U : ForcingJet n Ω a b 1, U.HasWeakDerivatives ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          wkpBaseCoordinateCLM (U.head t) = baseCoordCLM (u t)) ∧
        U.normSum ≤ K * (‖g‖ + F.normSum) := by
  obtain ⟨K, hK, hreg⟩ := exists_improved_regularity_of_contDiffUpToBoundary hab
    hopen hbounded hgraph P.principal (P.principal_smooth 1) hsymm
    P.drift P.potential (P.drift_smooth 0) (P.potential_smooth 0) alpha halpha hell
  refine ⟨K, hK, ?_⟩
  intro F g g₀ u hg hu
  rw [hg] at hu
  obtain ⟨ut, U₂, hut, hU₂, _, hnorm⟩ := hreg F.headBase g₀ u hu
  let Z : DerivLp n 2 Ω →L[ℝ] W^{0,2}(Ω) :=
    (lpEquivZeroOrder (n := n) (p := 2) (Ω := Ω)).toContinuousLinearEquiv.toContinuousLinearMap
  let V := Z.compLpL 2 (volume.restrict (Ioc a b)) ut
  have hV : ∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (V t) = ut t := by
    filter_upwards [Z.coeFn_compLpL ut] with t ht
    rw [ht]
    exact wkpBaseCoordinateCLM_lpToZeroOrder _
  have hVnorm : ‖V‖ ≤ ‖ut‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Z.coeFn_compLpL ut] with t ht
    rw [ht]
    exact le_of_eq (norm_lpToZeroOrder _)
  have hbase : ∀ᵐ t ∂volume.restrict (Ioc a b),
      wkpBaseCoordinateCLM (U₂ t) = baseCoordCLM (u t) := by
    filter_upwards [hU₂] with t ht
    exact congrArg (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)) ht
  have hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (U₂ t))
      (fun t ↦ wkpBaseCoordinateCLM (V t)) := by
    apply hut.pivot_hasWeakTimeDerivativeOn.congr_ae_restrict measurableSet_Ioo
    · exact (Filter.EventuallyEq.symm hbase).filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
    · exact (Filter.EventuallyEq.symm hV).filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  refine ⟨(U₂, V), ForcingJet.HasWeakDerivatives.cons_of_base
    (m := 0) (V := V) hopen U₂ trivial hweak, hbase, ?_⟩
  have hsum : ‖U₂‖ + ‖V‖ ≤ K * (‖g₀‖ + ‖F.headBase‖) := by
    have hess : 0 ≤ (eLpNormEssSup (fun t ↦ u t)
      (volume.restrict (Ioc a b))).toReal := ENNReal.toReal_nonneg
    linarith only [hnorm, hess, hVnorm]
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (norm_initial_representative_le hopen le_rfl g g₀ hg)
      (F.norm_headBase_le.trans F.norm_head_le_normSum)) hK.le)

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
