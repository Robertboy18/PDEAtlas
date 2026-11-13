/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.SmoothLoad
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# An interior subeigenvector for the Dirichlet inverse

A nonzero smooth nonnegative bump has compact support inside the domain. Its
Dirichlet solution is strictly positive there, so a positive minimum on that
compact support gives the subeigenvector inequality. Boundary Hopf estimates
are not needed for this construction.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set Metric
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Construct a nonzero nonnegative `L²` subeigenvector of the full
Dirichlet inverse from connected-domain and coefficient data. -/
theorem exists_subeigenvector_l2SolutionOperator
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    ∃ (w : DerivLp n 2 Ω) (M : ℝ), w ≠ 0 ∧
      (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ w x) ∧ 0 < M ∧
      ∀ᵐ x ∂domainMeasure n Ω, w x ≤ M * P.l2SolutionOperator hopen hbounded w x := by
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hp)
  let b : ContDiffBump p :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hK : closedBall p (r / 2) ⊆ Ω := by
    intro x hx
    exact hball (lt_of_le_of_lt hx (half_lt_self hr))
  let hb (k : ℕ) : ContDiffUpToBoundary k (b : ℝ^n → ℝ) Ω :=
    ContDiffUpToBoundary.of_contDiff b.contDiff hbounded
  let w : DerivLp n 2 Ω := (hb 0).toLp hopen hbounded 2
  have hwval : ⇑w =ᵐ[domainMeasure n Ω] (b : ℝ^n → ℝ) :=
    (hb 0).toLp_coeFn hopen hbounded 2
  have hwne : w ≠ 0 := by
    intro hw
    have hz : ⇑w =ᵐ[domainMeasure n Ω] fun _ ↦ (0 : ℝ) := by
      rw [hw]
      exact Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)
    have hpoint := Measure.eqOn_open_of_ae_eq (hwval.symm.trans hz) hopen
      b.continuous.continuousOn continuousOn_const
    have hb1 : b p = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
    have hb0 := hpoint hp
    linarith
  have hw0 : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ w x :=
    hwval.mono fun x hx ↦ (b.nonneg' x).trans_eq hx.symm
  obtain ⟨z, hz, _, hzae, _, _, hzpos⟩ :=
    P.exists_pos_smoothRepresentative_l2SolutionOperator hopen hbounded hconn.isPreconnected
      hgraph halpha hell hc b hb (fun x _ ↦ b.nonneg' x) hwne
  obtain ⟨x₀, hx₀, hmin⟩ :=
    (isCompact_closedBall p (r / 2)).exists_isMinOn
      ⟨p, mem_closedBall_self (half_pos hr).le⟩
      (hz.continuousOn.mono (hK.trans subset_closure))
  have hz₀ : 0 < z x₀ := hzpos x₀ (hK hx₀)
  refine ⟨w, (z x₀)⁻¹, hwne, hw0, inv_pos.mpr hz₀, ?_⟩
  filter_upwards [hwval, hzae, ae_restrict_mem hopen.measurableSet] with y hyw hyz hy
  rw [hyw, ← hyz]
  by_cases hyK : y ∈ closedBall p (r / 2)
  · calc
      b y ≤ 1 := b.le_one
      _ = (z x₀)⁻¹ * z x₀ := (inv_mul_cancel₀ hz₀.ne').symm
      _ ≤ (z x₀)⁻¹ * z y := mul_le_mul_of_nonneg_left (hmin hyK) (inv_nonneg.mpr hz₀.le)
  · have hdist : b.rOut ≤ dist y p := (lt_of_not_ge hyK).le
    rw [b.zero_of_le_dist hdist]
    exact mul_nonneg (inv_nonneg.mpr hz₀.le) (hzpos y hy).le

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
