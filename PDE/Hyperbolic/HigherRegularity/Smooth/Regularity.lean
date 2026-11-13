/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.WaveProblem
public import PDE.Hyperbolic.HigherRegularity.Smooth.FiniteRegularity
public import PDE.Hyperbolic.HigherRegularity.AllOrder.Classical

/-!
# One joint smooth representative of the original wave

Smooth compatible data realize the finite data in the all-order wave
theorem. Their forcing and initial values agree in the original energy spaces
at every order. Applying that theorem to the same weak solution gives the
finite derivative budgets required by the joint representative theorem.
The result is one function smooth up to the whole closed cylinder.

This is the regularity step of Evans, §7.2.3, Theorem 7, whose proof applies Theorem 6 at every
order. The pointwise equation, boundary conditions and initial values are recovered in
`Representative`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorems 6 and 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Any original weak wave with smooth compatible data has a single joint
smooth representative. All finite forcing jets and derivative chains used in
the proof are constructed from the data. -/
theorem exists_joint_smooth_representative (P : SmoothFullCoefficients n Ω) (hn : 0 < n)
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
    ∃ U : SpaceTime n → ℝ,
      ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      (∀ k : ℕ, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t)) := by
  apply exists_joint_smooth_representative_of_wave_jets hn hopen hbounded
    ((hgraph 1).hasC1GraphBoundary le_rfl) hab u
  intro m
  let D := problemData P hopen hbounded hab hf hg hh m 0
  have hD := problemData_hasCompatibleBoundaryTraces P hopen hbounded hab hf hg hh
    hn ((hgraph 1).hasC1GraphBoundary le_rfl) hcompat m 0
  have h₀ := problemData_hasCompatibleBoundaryTraces P hopen hbounded hab hf hg hh
    hn ((hgraph 1).hasC1GraphBoundary le_rfl) hcompat 0 0
  obtain ⟨_, _, hregular⟩ := exists_allOrderSobolevTimeJet_of_classical_wave
    hn hopen hbounded hgraph hab P.principal_smooth P.drift_smooth P.potential_smooth
    hsymm halpha hell m
  have hwave : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded) (dirichletLoadTimeLp hopen D.forcing.head)
      u v w (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) := by
    rw [problemData_initialPosition_eq P hopen hbounded hab hf hg hh m 0 hD h₀,
      show wkpBaseCoordinateCLM D.velocity =
        wkpBaseCoordinateCLM (problemData P hopen hbounded hab hf hg hh 0 0).velocity from
          problemData_velocity_eq P hopen hbounded hab hf hg hh m 0,
      show dirichletLoadTimeLp hopen D.forcing.head =
        dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head from
          forcingJet_load_eq hopen hbounded hab hf m 0]
    exact hweak
  obtain ⟨U, hU, _⟩ := hregular D hD u v w hwave
  exact ⟨U, hU⟩

end Hyperbolic.HigherRegularity.SmoothWave
