/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Compatibility.Conditions

/-!
# The boundary content of wave compatibility

The compatibility condition asks only that the recursively computed positions
have zero Dirichlet trace. Spatial regularity and the terminal velocity are already
provided by the data and the bounded spatial load. Agreement with the weak operator
is a property of that operator, not an extra datum.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, the Remark after Theorem 6, equations (65)-(66).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

namespace WaveProblemData

/-- Evans's zero boundary compatibility through order `m`. At order zero only
the displacement has a boundary condition. Each successor computes the new
velocity from the forcing trace and the spatial load. -/
def HasCompatibleBoundaryTraces
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)) :
    {m : ℕ} → WaveProblemData n m Ω a b → Prop
  | 0, D => HasDirichletTraceZero (by omega) D.displacement
  | m + 1, D => HasDirichletTraceZero (by omega) D.displacement ∧
      HasCompatibleBoundaryTraces L
        (D.timeDerivative (D.forcingTraces.head - L m D.displacement))

/-- The original displacement has zero trace at every compatible order. -/
theorem HasCompatibleBoundaryTraces.displacement
    {L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    {D : WaveProblemData n m Ω a b} (hD : HasCompatibleBoundaryTraces L D) :
    HasDirichletTraceZero (by omega : 1 ≤ m + 1) D.displacement := by
  cases m with
  | zero => exact hD
  | succ m => exact hD.1

/-- The computed initial displacement as an energy-space vector. -/
def initialPosition
    {L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    {D : WaveProblemData n m Ω a b} (hD : HasCompatibleBoundaryTraces L D) :
    H¹₀(Ω) :=
  ⟨lowerOrderCLM (by omega : 1 ≤ m + 1) D.displacement, hD.displacement⟩

/-- Passing to the energy space does not enlarge the initial displacement norm. -/
theorem norm_initialPosition_le {L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    {D : WaveProblemData n m Ω a b} (hD : HasCompatibleBoundaryTraces L D) :
    ‖initialPosition hD‖ ≤ ‖D.displacement‖ :=
  norm_lowerOrderCLM_apply_le (by omega : 1 ≤ m + 1) D.displacement

private theorem realizes_zero
    (f : SobolevTimeJet n 0 Ω a b) (traces : InitialTraceData (F := f))
    (g : W^{1,2}(Ω)) (hg : HasDirichletTraceZero (by omega) g)
    (h : W^{0,2}(Ω))
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)) :
    (WaveCompatibilityValues.zero g hg).Realizes A L traces g h := by
  cases traces
  rfl

private theorem realizes_succ
    {f : SobolevTimeJet n (m + 1) Ω a b} (traces : InitialTraceData (F := f))
    (g : W^{(m + 2),2}(Ω)) (hg : HasDirichletTraceZero (by omega) g)
    (h : W^{(m + 1),2}(Ω))
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (Q : WaveCompatibilityValues n Ω m)
    (hA : A ⟨lowerOrderCLM (by omega) g, hg⟩ =
      loadFunctional (wkpBaseCoordinateCLM (L m g)))
    (hQ : Q.Realizes A L traces.timeDerivative h (traces.head - L m g)) :
    (WaveCompatibilityValues.succ g hg Q).Realizes A L traces g h := by
  cases traces
  exact ⟨rfl, hA, hQ⟩

/-- Zero traces imply the typed compatibility certificate once
the spatial family is proved to represent the weak operator. -/
theorem HasCompatibleBoundaryTraces.isCompatible {L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (hL : ∀ (r : ℕ) (G : W^{(r + 2),2}(Ω)) (g : H¹₀(Ω)), wkpBaseCoordinateCLM G = baseCoordCLM g →
      A g = loadFunctional (wkpBaseCoordinateCLM (L r G)))
    {D : WaveProblemData n m Ω a b} (hD : HasCompatibleBoundaryTraces L D) :
    D.IsCompatible A L := by
  induction m with
  | zero =>
      exact ⟨.zero D.displacement hD,
        realizes_zero D.forcing D.forcingTraces D.displacement hD D.velocity A L⟩
  | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih hD.2
      have htraces : (D.timeDerivative (D.forcingTraces.head - L m D.displacement)).forcingTraces =
            D.forcingTraces.timeDerivative := by
        unfold forcingTraces
        exact (InitialTraceData.ofJet_timeDerivative D.forcing D.time_lt).symm
      rw [htraces] at hQ
      refine ⟨.succ D.displacement hD.1 Q,
        realizes_succ D.forcingTraces D.displacement hD.1 D.velocity A L Q ?_ hQ⟩
      apply hL m D.displacement
      rfl

end WaveProblemData

end Hyperbolic.HigherRegularity
