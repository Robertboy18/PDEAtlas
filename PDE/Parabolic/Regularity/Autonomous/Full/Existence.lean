/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.PivotPerturbation
public import PDE.Elliptic.Variational.PivotOperator
public import PDE.Parabolic.Heat.Variational.MeasurableBounds

/-!
# Weak solutions for autonomous lower-order perturbations

The spectral trial spaces of `H¹₀` and the measurable Gårding existence
theorem apply to any coercive principal form perturbed by a bounded map
into `L²`. The constant below is fixed before the forcing and initial data.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem exists_autonomous_garding_solution
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (B : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    {a b theta gamma : ℝ} (hab : a < b) (htheta : 0 < theta)
    (hgamma : 0 ≤ gamma)
    (hGarding : ∀ v, theta * ‖v‖ ^ 2 ≤
      B v v + gamma * ‖(h10L2GelfandTriple hopen).inclusion v‖ ^ 2)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
    (g : DerivLp n 2 Ω) :
    Nonempty (GardingWeakSolutionOn (h10L2GelfandTriple hopen)
      (fun _ ↦ B) ell g a b theta gamma) := by
  let S := h10L2SpectralTrialSystem hopen hbounded
  exact @GardingWeakSolutionOn.nonempty_of_ae_garding
    (H¹₀(Ω)) (DerivLp n 2 Ω)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (h10L2GelfandTriple hopen) S.space S.finiteDimensional S.stabilityConstant
    S.projection S.denseEnergy (fun _ ↦ B) a b theta gamma ell
    hab htheta hgamma (fun _ ↦ aestronglyMeasurable_const) ‖B‖₊
    (Eventually.of_forall fun _ ↦ le_rfl) (Eventually.of_forall fun _ ↦ hGarding) g

/-- Existence, uniqueness, the weak time derivative, the continuous initial
trace, and the three energy bounds for an autonomous pivot perturbation. -/
theorem exists_full_form_solution_with_bound
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ v, C * ‖v‖ ^ 2 ≤ A v v) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (g : DerivLp n 2 Ω),
      ∃ U : GardingWeakSolutionOn (h10L2GelfandTriple hopen)
          (fun _ ↦ A + (h10L2GelfandTriple hopen).pivotToDual.comp R)
          ((h10L2GelfandTriple hopen).pivotToDual.compLpL
            2 (volume.restrict (Ioc a b)) f) g a b (C / 2) (‖R‖ ^ 2 / (2 * C)),
        ∀ t ∈ Icc a b,
          ‖U.evolution.representative t‖ + ‖U.state‖ + ‖U.derivative‖ ≤
            K * (‖g‖ + ‖f‖) := by
  let T := h10L2GelfandTriple hopen
  let B := A + T.pivotToDual.comp R
  let K := gardingThreeTermConstant (C / 2) (‖R‖ ^ 2 / (2 * C))
    (b - a) ‖B‖ 1
  have hK : 0 ≤ K := by
    dsimp only [K, gardingThreeTermConstant]
    positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro f g
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  have hgamma : 0 ≤ ‖R‖ ^ 2 / (2 * C) := by positivity
  have hmeas : ∀ v, AEStronglyMeasurable (fun _ : ℝ ↦ B v)
      (volume.restrict (Ioc a b)) :=
    fun _ ↦ aestronglyMeasurable_const
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B‖ ≤ ‖B‖₊ :=
    Eventually.of_forall fun _ ↦ le_rfl
  have hgarding : ∀ v, C / 2 * ‖v‖ ^ 2 ≤
      B v v + (‖R‖ ^ 2 / (2 * C)) * ‖T.inclusion v‖ ^ 2 :=
    garding_bound_of_coercive_principal T A R hC hcoercive
  have hexists : Nonempty (GardingWeakSolutionOn T (fun _ ↦ B) ell g
      a b (C / 2) (‖R‖ ^ 2 / (2 * C))) :=
    exists_autonomous_garding_solution hopen hbounded B hab (half_pos hC) hgamma
      hgarding ell g
  obtain ⟨U⟩ := hexists
  refine ⟨U, ?_⟩
  intro t ht
  have h := U.three_term_bound hab.le (half_pos hC) hgamma hmeas ‖B‖₊ hbound t ht
  have hell : ‖ell‖ ≤ ‖f‖ :=
    HeatEquation.Variational.BoundedMeasurableCoefficients.norm_pivotLoadLp_le hopen f
  change _ ≤ K * (‖g‖ + ‖ell‖) at h
  calc
    _ ≤ K * (‖g‖ + ‖ell‖) := h
    _ ≤ K * (‖g‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    _ ≤ (K + 1) * (‖g‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The basic energy-space estimate applies to every full weak solution,
with a constant fixed before the initial and forcing data. -/
theorem exists_full_form_state_bound
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ v, C * ‖v‖ ^ 2 ≤ A v v) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (g : H¹₀(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ A + (h10L2GelfandTriple hopen).pivotToDual.comp R)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ‖u‖ ≤ K * (‖g‖ + ‖f‖) := by
  have hbasic := @exists_full_form_solution_with_bound n Ω hopen hbounded A R C a b
    hC hab hcoercive
  obtain ⟨K, hK, hbasic⟩ := hbasic
  refine ⟨K, hK, ?_⟩
  intro f g u hu
  have hfull := hbasic f (baseCoordCLM (n := n) (Ω := Ω) g)
  obtain ⟨U, hU⟩ := hfull
  have huU := U.properties.unique u hu
  have hb := hU a ⟨le_rfl, hab.le⟩
  have hgn := baseCoordCLM_norm_le (n := n) (Ω := Ω) g
  have hb' : ‖U.state‖ ≤ K * (‖baseCoordCLM (n := n) (Ω := Ω) g‖ + ‖f‖) := by
    linarith [norm_nonneg (U.evolution.representative a), norm_nonneg U.derivative]
  calc
    _ = ‖U.state‖ := congrArg norm huU
    _ ≤ K * (‖baseCoordCLM (n := n) (Ω := Ω) g‖ + ‖f‖) := hb'
    _ ≤ K * (‖g‖ + ‖f‖) := mul_le_mul_of_nonneg_left (by linarith) hK.le

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
