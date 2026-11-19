/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.FullOperator
public import PDE.Hyperbolic.HigherRegularity.Estimate.Jet
public import PDE.Hyperbolic.HigherRegularity.Compatibility.InitialJets
public import PDE.Hyperbolic.HigherRegularity.Data.TimeRestriction
public import PDE.Analysis.Evolution.Time.WeakDerivative.LiftedPrimitive

/-!
# The quantitative spatial step for an integrated wave

Integrating the regular velocity first supplies a higher spatial
representative of the original displacement. Its bound uses only the initial
displacement and the velocity estimate. The shifted inverse then acts on the
unshifted equation's residual and recovers two spatial orders. Adjoining this
head to the velocity jet preserves every weak time derivative.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open PDE.Analysis.Evolution

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Upgrade an integrated wave using a quantified derivative jet. The shift
is paid for by a primitive estimate, so no original solution norm appears. -/
theorem exists_jet_of_integrated_full_wave
    (D : WaveProblemData n (m + 1) Ω a b) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (mu : ℝ) (S : W^{m,2}(Ω) →L[ℝ] W^{(m + 2),2}(Ω))
    (hS : ∀ (F : W^{m,2}(Ω)) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution A B C mu (wkpBaseCoordinateCLM F) 0 u →
      wkpBaseCoordinateCLM (S F) = baseCoordCLM u)
    (q : H¹₀(Ω))
    (hq : h10SubtypeL q = lowerOrderCLM (by omega : 1 ≤ m + 2) D.displacement)
    {u du : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {dv : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    (hweak : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
      (dirichletLoadTimeLp hopen D.forcing.head) u
      ((h10L2GelfandTriple hopen).inclusion.compLpL 2 (volume.restrict (Ioc a b)) du)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) dv)
      q (wkpBaseCoordinateCLM D.velocity))
    (hprimitive : ∀ᵐ t ∂volume.restrict (Ioc a b), u t = q + ∫ s in a..t, du s)
    (dU : SobolevTimeJet n (m + 1) Ω a b)
    (hdU : ∀ᵐ t ∂volume.restrict (Ioc a b),
      lowerOrderCLM (by omega : 1 ≤ m + 1) (dU.head t) = h10SubtypeL (du t))
    (hdv : baseCoordinateTimeLp dU.timeDerivative.head = dv)
    (hdTop : dU.IsEssentiallyBounded)
    {Z : ℝ} (hZ : 0 ≤ Z)
    (hdBound : ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum dU t ≤ Z) :
    ∃ U : SobolevTimeJet n (m + 2) Ω a b,
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (by omega : 1 ≤ m + 2) (U.head t) = h10SubtypeL (u t)) ∧
      U.timeDerivative = dU ∧
      baseCoordinateTimeLp U.timeDerivative.head =
        (h10L2GelfandTriple hopen).inclusion.compLpL 2 (volume.restrict (Ioc a b)) du ∧
      U.IsEssentiallyBounded ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum U t ≤
        Z + ‖S‖ * ((((b - a)⁻¹ + 1) * max 1 (b - a)) *
          forcingSobolevLpNormSum D.forcing + Z +
          |mu| * (‖D.displacement‖ + (b - a) * Z)) := by
  let T := h10L2GelfandTriple hopen
  let Q := lowerOrderCLM (Nat.le_succ (m + 1)) D.displacement
  have hqbase : T.inclusion q = wkpBaseCoordinateCLM Q :=
    congrArg (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)) hq
  have hdBase : ∀ᵐ t ∂volume.restrict (Ioc a b),
      T.inclusion (du t) = wkpBaseCoordinateCLM (dU.head t) :=
    hdU.mono fun _ h ↦ (congrArg wkpBaseCoordinateCLM h).symm
  have hdHead : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖dU.head t‖ ≤ Z :=
    hdBound.mono fun t ht ↦ (norm_solution_head_le dU t).trans ht
  obtain ⟨P₁, hP₁, _, hP₁bound⟩ :=
    exists_lifted_primitive_L2 D.time_lt T.inclusion wkpBaseCoordinateCLM
      u du dU.head q Q hqbase hprimitive hdBase hZ hdHead
  let P := lowerOrderTimeLp P₁
  have hP : ∀ᵐ t ∂volume.restrict (Ioc a b),
      wkpBaseCoordinateCLM (P t) = baseCoordCLM (u t) := by
    filter_upwards [lowerOrderTimeLp_apply_ae P₁, hP₁] with t ht hpt
    rw [show P t = lowerOrderCLM (Nat.le_succ m) (P₁ t) from ht]
    exact hpt
  have hp : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖P t‖ ≤ ‖D.displacement‖ + (b - a) * Z := by
    filter_upwards [lowerOrderTimeLp_apply_ae P₁, hP₁bound] with t ht hpt
    rw [show P t = lowerOrderCLM (Nat.le_succ m) (P₁ t) from ht]
    exact (norm_lowerOrderCLM_apply_le (Nat.le_succ m) _).trans
      (hpt.trans (add_le_add (norm_lowerOrderCLM_apply_le (Nat.le_succ (m + 1)) _) le_rfl))
  obtain ⟨R, _, hR, _, _, hRbound⟩ := D.forcingTraces.exists_head_representative_norm_le D.time_lt
  have hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖lowerOrderTimeLp D.forcing.head t‖ ≤
        (((b - a)⁻¹ + 1) * max 1 (b - a)) * forcingSobolevLpNormSum D.forcing := by
    filter_upwards [lowerOrderTimeLp_apply_ae D.forcing.head, hR,
      ae_restrict_mem measurableSet_Ioc] with t ht hrt htI
    rw [ht, hrt]
    exact (hRbound t (Ioc_subset_Icc_self htI)).trans
      (mul_le_mul_of_nonneg_left (forcing_head_pair_le D.forcing) (by
        have hab := D.time_lt
        positivity))
  have hw : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖dU.timeDerivative.head t‖ ≤ Z :=
    hdBound.mono fun t ht ↦ (norm_solution_derivative_head_le dU t).trans ht
  have hweak' : Hyperbolic.Variational.IsGelfandWeakWaveSolution T
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
      (dirichletLoadTimeLp hopen (lowerOrderTimeLp D.forcing.head)) u
      (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) du)
      (dirichletLoadTimeLp hopen dU.timeDerivative.head) q
      (wkpBaseCoordinateCLM D.velocity) := by
    simpa only [dirichletLoadTimeLp_lowerOrderTimeLp, dirichletLoadTimeLp,
      liftPivotToDualTimeLp, baseCoordinateTimeLp_lowerOrderTimeLp, hdv] using hweak
  obtain ⟨U, hU, hUTop, hUBound⟩ :=
    exists_higher_trajectory_of_full_weakWave hopen A B C mu S hS hweak' hP hf hw hp
  have hdvel : baseCoordinateTimeLp dU.head =
      T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) du := by
    refine Lp.ext ?_
    filter_upwards [baseCoordinateTimeLp_apply_ae dU.head, T.inclusion.coeFn_compLpL du,
      hdBase] with t ht hdt hb
    rw [ht, hdt, hb]
  have hderiv := higherWeakTimeDerivative_of_weakWave hopen _
    (dirichletLoadTimeLp hopen D.forcing.head) U dU.head u
    (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) dv) q
    (wkpBaseCoordinateCLM D.velocity) (hdvel ▸ hweak)
    (hU.mono fun _ h ↦ congrArg wkpBaseCoordinateCLM h)
  refine ⟨SobolevTimeJet.succ U dU hderiv, hU, rfl, hdvel,
    SobolevTimeJet.succ_isEssentiallyBounded U dU hderiv hUTop hdTop, ?_⟩
  filter_upwards [hdBound, hUBound] with t hdt hut
  exact (solutionSobolevNormSum_succ ..).trans_le (add_le_add hdt hut)

end Hyperbolic.HigherRegularity
