/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Regularity
public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.ClassicalSolution

/-!
# Infinite smoothness of the original weak wave

Smooth compatible data and the finite-order wave theorem construct one
joint classical representative of any original weak solution. Its canonical
Sobolev and scalar fields are derivatives: they identify the original
velocity and acceleration, have every computed initial trace, and obey the
time links through both endpoints.

This is the regularity assertion of Evans, §7.2.3, Theorem 7, with the full
autonomous divergence operator and principal-part symmetry only.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Smooth compatible data give the same original weak wave a single
classical representative with all derivative links and initial traces. -/
theorem exists_classicalSolution_of_weakWave (P : SmoothFullCoefficients n Ω) (hn : 0 < n)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) {f : SpaceTime n → ℝ}
    {g h : ℝ^n → ℝ} (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hg : ∀ k, ContDiffUpToBoundary k g Ω) (hh : ∀ k, ContDiffUpToBoundary k h Ω)
    (hcompat : HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
    (hweak : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded) (dirichletLoadTimeLp hopen
      (forcingJet hopen hbounded hab hf 0 0).head) u v w (WaveProblemData.initialPosition
      (problemData_hasCompatibleBoundaryTraces P hopen hbounded hab hf hg hh hn
      ((hgraph 1).hasC1GraphBoundary le_rfl) hcompat 0 0))
      (wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 0 1))) :
    ∃ (U : SpaceTime n → ℝ) (hU : IsClassicalSolution P hopen hf hg hh U),
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) ∧
      ((fun t ↦ wkpBaseCoordinateCLM
        (sobolevCurve hopen hbounded hab hU.smooth 1 1 t))
          =ᵐ[volume.restrict (Ioc a b)] fun t ↦ v t) ∧
      ((fun t ↦ (h10L2GelfandTriple hopen).pivotToDual
        (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth 1 2 t)))
          =ᵐ[volume.restrict (Ioc a b)] fun t ↦ w t) ∧
      (∀ j r, sobolevCurve hopen hbounded hab hU.smooth r j a =
        initialSobolevValue P hopen hbounded hab hf hg hh r j) ∧
      (∀ j x, x ∈ closure Ω →
        derivativeSlice hopen hU.smooth (List.replicate j 0) a x =
          initialBoundaryValue P hopen hbounded hab hf hg hh j x) ∧
      (∀ α x, x ∈ closure Ω → ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s ↦ derivativeSlice hopen hU.smooth α s x)
          (derivativeSlice hopen hU.smooth (0 :: α) t x) (Icc a b) t) ∧
      (∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s ↦ U (timeSpaceCons s x))
          (derivativeSlice hopen hU.smooth [0] t x) (Icc a b) t) ∧
      ∀ r j, HasWeakTimeDerivativeOn (Ioo a b)
        (sobolevCurve hopen hbounded hab hU.smooth r j)
        (sobolevCurve hopen hbounded hab hU.smooth r (j + 1)) := by
  obtain ⟨U, hc, hs, hae⟩ := exists_joint_smooth_representative P hn hopen hbounded
    hgraph hab hsymm halpha hell hf hg hh hcompat u v w hweak
  have hq₀ : baseCoordCLM (WaveProblemData.initialPosition
      (problemData_hasCompatibleBoundaryTraces P hopen hbounded hab hf hg hh
        hn ((hgraph 1).hasC1GraphBoundary le_rfl) hcompat 0 0)) =
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 1 0) := by
    change wkpBaseCoordinateCLM (lowerOrderCLM le_rfl _) = _
    rw [lowerOrderCLM_refl_apply]
    rfl
  have hclass := isClassicalSolution_of_weakWave P hn hopen hbounded
    ((hgraph 1).hasC1GraphBoundary le_rfl) hab hf hg hh hs hc hweak hq₀ rfl hae
  refine ⟨U, hclass, hae, velocity_ae hopen hbounded hab hs hc hweak hae,
    acceleration_ae hopen hbounded hab hs hc hweak hae, ?_, ?_, ?_, ?_, ?_⟩
  · exact initial_sobolev_eq P hopen hbounded hab hf hg hh hs hc hweak hq₀ rfl hae
  · exact fun j x hx ↦
      initial_derivativeSlice_eq P hopen hbounded hab hf hg hh hs hc hweak hq₀ rfl hae j hx
  · exact fun α x hx t ht ↦ hasDerivWithinAt_derivativeSlice hopen hab hs α hx ht
  · exact fun x hx t ht ↦ hasDerivWithinAt_timeSlice hopen hab hs hc hx ht
  · exact hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hs

end Hyperbolic.HigherRegularity.SmoothWave
