/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Compatibility
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.DifferentiatedSolution
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical

/-!
# The differentiated problem from compatible data

The forcing trace is constructed by mixed Sobolev continuity. The full spatial
load computes the next initial datum. Their pivot identity gives the initial
condition in the primitive argument, which constructs the derivative of every
original weak solution together with its differentiated weak equation.
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

private theorem exists_derivative_of_smooth_coefficients (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (f df : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (g₀ g₁ : H¹₀(Ω))
    (hf : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ f t) (fun t ↦ df t))
    (fTrace : ℝ → DerivLp n 2 Ω) (hfCont : ContinuousOn fTrace (Icc a b))
    (hfTrace : fTrace =ᵐ[volume.restrict (Ioc a b)] fun t ↦ f t)
    (hcompat : (h10L2GelfandTriple hopen).pivotToDual
      (baseCoordCLM (n := n) (Ω := Ω) g₁) =
      (h10L2GelfandTriple hopen).pivotToDual (fTrace a) - P.form hopen hbounded g₀)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL
        2 (volume.restrict (Ioc a b)) f) u (baseCoordCLM (n := n) (Ω := Ω) g₀)) :
    ∃ v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
        ((h10L2GelfandTriple hopen).energyToDual.compLpL
          2 (volume.restrict (Ioc a b)) v) ∧
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) df) v (baseCoordCLM (n := n) (Ω := Ω) g₁) := by
  obtain ⟨A, R, C, hC, hform, hcoercive⟩ :=
    P.exists_coercive_decomposition hopen hbounded halpha hell
  simp only [hform] at hu hcompat ⊢
  exact exists_differentiated_full_form_solution (n := n) (Ω := Ω) hopen hbounded A R
    hC hab hcoercive f df g₀ g₁ hf fTrace hfCont hfTrace hcompat u hu

private theorem initial_derivative_dual_identity (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    {m : ℕ} (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives)
    (g : W^{(2 * (m + 1) + 1),2}(Ω)) (g₀ g₁ : H¹₀(Ω))
    (hg : wkpBaseCoordinateCLM g = baseCoordCLM g₀)
    (hg₁ : wkpBaseCoordinateCLM
      (initialDerivative (P.load hopen hbounded) hopen hbounded hgraph hab F hF g) =
        baseCoordCLM g₁) :
    (h10L2GelfandTriple hopen).pivotToDual (baseCoordCLM g₁) =
      (h10L2GelfandTriple hopen).pivotToDual
        (wkpBaseCoordinateCLM (F.trace hopen hbounded hgraph hab hF a)) -
      P.form hopen hbounded g₀ := by
  let T := h10L2GelfandTriple hopen
  let S := wkpBaseCoordinateCLM (n := n) (m := 2 * m + 1) (p := 2) (Ω := Ω)
  let G := lowerOrderCLM (n := n) (p := 2) (Ω := Ω)
    (show 2 * m + 1 + 2 ≤ 2 * (m + 1) + 1 by omega) g
  have hload : T.pivotToDual (S (P.load hopen hbounded (2 * m + 1) G)) =
      P.form hopen hbounded g₀ := by
    ext w
    exact (P.form_eq_load hopen hbounded (2 * m + 1) G g₀ w hg).symm
  rw [← hg₁]
  change T.pivotToDual (S (F.trace hopen hbounded hgraph hab hF a -
    P.load hopen hbounded (2 * m + 1) G)) = _
  rw [map_sub, map_sub, hload]

/-- The recursively computed initial derivative and the forcing tuple give
the differentiated weak solution. No higher trajectory is assumed. -/
theorem exists_derivative_solution (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    {m : ℕ} (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives)
    (g : W^{(2 * (m + 1) + 1),2}(Ω)) (g₀ g₁ : H¹₀(Ω))
    (hg : wkpBaseCoordinateCLM g = baseCoordCLM g₀)
    (hg₁ : wkpBaseCoordinateCLM
      (initialDerivative (P.load hopen hbounded) hopen hbounded hgraph hab F hF g) =
        baseCoordCLM g₁)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL
        2 (volume.restrict (Ioc a b)) F.headBase) u (wkpBaseCoordinateCLM g)) :
    ∃ v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
        ((h10L2GelfandTriple hopen).energyToDual.compLpL
          2 (volume.restrict (Ioc a b)) v) ∧
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) F.2.headBase) v
        (wkpBaseCoordinateCLM
          (initialDerivative (P.load hopen hbounded) hopen hbounded hgraph hab F hF g)) := by
  let S := wkpBaseCoordinateCLM (n := n) (m := 2 * m + 1) (p := 2) (Ω := Ω)
  let fTrace := fun t ↦ S (F.trace hopen hbounded hgraph hab hF t)
  have htrace := F.trace_spec hopen hbounded hgraph hab hF
  have hfCont : ContinuousOn fTrace (Icc a b) :=
    S.continuous.comp_continuousOn htrace.1
  have hfTrace : fTrace =ᵐ[volume.restrict (Ioc a b)] fun t ↦ F.headBase t := by
    filter_upwards [htrace.2.1, F.headBase_ae] with t ht hft
    exact (congrArg S ht).trans hft.symm
  have hcompat := initial_derivative_dual_identity P hopen hbounded hgraph hab F hF
    g g₀ g₁ hg hg₁
  conv at hu =>
    arg 5
    rw [hg]
  obtain ⟨v, hv, hveq⟩ := exists_derivative_of_smooth_coefficients P hopen hbounded hab
    halpha hell F.headBase F.2.headBase g₀ g₁ hF.headBase fTrace hfCont hfTrace
    hcompat u hu
  refine ⟨v, hv, ?_⟩
  conv =>
    arg 5
    rw [hg₁]
  exact hveq

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
