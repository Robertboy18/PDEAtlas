/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.Forcing
public import PDE.Hyperbolic.HigherRegularity.Compatibility.BoundaryTraces

/-!
# Finite wave problems realized by smooth compatible data

Each finite problem uses the same forcing and recursively computed initial
values. Differentiation commutes with this construction, because the canonical
forcing trace is its initial slice and the classical load realizes the
full Sobolev operator. Thus pointwise compatibility supplies every finite
compatibility condition in the all-order wave theorem.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity PDE.Analysis.Evolution
open SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (P : SmoothFullCoefficients n Ω)
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hg : ∀ k, ContDiffUpToBoundary k g Ω)
  (hh : ∀ k, ContDiffUpToBoundary k h Ω)

/-- The finite wave data starting with the `j`-th computed initial value. -/
def problemData (m j : ℕ) : WaveProblemData n m Ω a b where
  time_lt := hab
  displacement := initialSobolevValue P hopen hbounded hab hf hg hh (m + 1) j
  velocity := initialSobolevValue P hopen hbounded hab hf hg hh m (j + 1)
  forcing := forcingJet hopen hbounded hab hf m j

/-- The computed next velocity is exactly the one used when differentiating
the finite wave problem. -/
theorem problemData_next_velocity (m j : ℕ) :
    (problemData P hopen hbounded hab hf hg hh (m + 1) j).forcingTraces.head -
      P.load hopen hbounded m
        (problemData P hopen hbounded hab hf hg hh (m + 1) j).displacement =
      initialSobolevValue P hopen hbounded hab hf hg hh m (j + 2) := by
  change (InitialTraceData.ofJet (forcingJet hopen hbounded hab hf (m + 1) j) hab).head -
    P.load hopen hbounded m (initialSobolevValue P hopen hbounded hab hf hg hh (m + 2) j) = _
  rw [forcingJet_initialTrace]
  exact (classicalWaveInitialSobolevValue_add_two P hopen hbounded
    (forcingTrace_regular hopen hbounded hab hf) hg hh m j).symm

/-- Differentiating the realized finite problem shifts the initial
recurrence and forcing derivatives by one. -/
theorem problemData_timeDerivative (m j : ℕ) :
    (problemData P hopen hbounded hab hf hg hh (m + 1) j).timeDerivative
      ((problemData P hopen hbounded hab hf hg hh (m + 1) j).forcingTraces.head -
        P.load hopen hbounded m
          (problemData P hopen hbounded hab hf hg hh (m + 1) j).displacement) =
      problemData P hopen hbounded hab hf hg hh m (j + 1) := by
  rw [problemData_next_velocity]
  rfl

/-- Pointwise compatibility implies the entire finite Sobolev
compatibility recurrence, with no extra boundary condition on the last velocity. -/
theorem problemData_hasCompatibleBoundaryTraces
    (hn : 0 < n) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hcompat : HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh) (m j : ℕ) :
    (problemData P hopen hbounded hab hf hg hh m j).HasCompatibleBoundaryTraces
      (P.load hopen hbounded) := by
  induction m generalizing j with
  | zero =>
      exact initialSobolevValue_trace_zero P hopen hbounded hab hf hg hh hn hgraph hcompat le_rfl j
  | succ m ih =>
      refine ⟨initialSobolevValue_trace_zero P hopen hbounded hab hf hg hh
        hn hgraph hcompat (by omega) j, ?_⟩
      rw [problemData_timeDerivative]
      exact ih (j + 1)

/-- Every finite problem has the same original energy-space initial position. -/
theorem problemData_initialPosition_eq (m j : ℕ)
    (hm : (problemData P hopen hbounded hab hf hg hh m j).HasCompatibleBoundaryTraces
      (P.load hopen hbounded))
    (h₀ : (problemData P hopen hbounded hab hf hg hh 0 j).HasCompatibleBoundaryTraces
      (P.load hopen hbounded)) :
    WaveProblemData.initialPosition hm = WaveProblemData.initialPosition h₀ := by
  apply Subtype.ext
  change lowerOrderCLM (by omega : 1 ≤ m + 1)
      (initialSobolevValue P hopen hbounded hab hf hg hh (m + 1) j) =
    lowerOrderCLM le_rfl (initialSobolevValue P hopen hbounded hab hf hg hh 1 j)
  rw [lowerOrderCLM_refl_apply]
  exact lowerOrder_classicalWaveInitialSobolevValue P hopen hbounded
    (forcingTrace_regular hopen hbounded hab hf) hg hh (by omega) j

/-- The pivot initial velocity is independent of the finite regularity order. -/
theorem problemData_velocity_eq (m j : ℕ) :
    wkpBaseCoordinateCLM (problemData P hopen hbounded hab hf hg hh m j).velocity =
      wkpBaseCoordinateCLM (problemData P hopen hbounded hab hf hg hh 0 j).velocity := by
  apply Lp.ext
  have hm := initialValue_regular P hopen hbounded hab hf hg hh (j + 1) m
  have h₀ := initialValue_regular P hopen hbounded hab hf hg hh (j + 1) 0
  exact (hm.toWkpSpaceOn_base_ae hopen hbounded 2).trans
    (h₀.toWkpSpaceOn_base_ae hopen hbounded 2).symm

/-- Every finite forcing jet induces the same load in the original weak equation. -/
theorem forcingJet_load_eq (m j : ℕ) :
    dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf m j).head =
      dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 j).head := by
  apply Lp.ext
  filter_upwards [ dirichletLoadTimeLp_apply_ae hopen (forcingJet hopen hbounded hab hf m j).head,
    dirichletLoadTimeLp_apply_ae hopen (forcingJet hopen hbounded hab hf 0 j).head,
    sobolevTimeDerivative_ae hopen hbounded hab hf m j,
    sobolevTimeDerivative_ae hopen hbounded hab hf 0 j,
    ae_restrict_mem measurableSet_Ioc] with t hm h₀ hmt h₀t ht
  rw [hm, h₀]
  change loadFunctional (wkpBaseCoordinateCLM (sobolevTimeDerivative hopen hbounded hab hf m j t)) =
    loadFunctional (wkpBaseCoordinateCLM (sobolevTimeDerivative hopen hbounded hab hf 0 j t))
  rw [hmt, h₀t, wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf m j ⟨ht.1.le, ht.2⟩,
    wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf 0 j ⟨ht.1.le, ht.2⟩]

end Hyperbolic.HigherRegularity.SmoothWave
