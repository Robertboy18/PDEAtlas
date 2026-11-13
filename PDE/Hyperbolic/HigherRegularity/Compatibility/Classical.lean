/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad
public import PDE.Hyperbolic.HigherRegularity.Compatibility.BoundaryTraces
public import PDE.Hyperbolic.WeakWave.Autonomous.ClassicalCoefficients

/-!
# Wave compatibility for classical coefficients

The higher divergence operator acts on the canonical Sobolev graphs of
the classical coefficients. Its variational identity identifies every
initial load with the original full wave form. Thus the compatibility input
can consist solely of the recursively computed zero boundary traces.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
  (hA : ∀ k : ℕ, ∀ i j, ContDiffUpToBoundary k (fun x ↦ A x i j) Ω)
  (hB : ∀ k : ℕ, ∀ i, ContDiffUpToBoundary k (B i) Ω)
  (hC : ∀ k : ℕ, ContDiffUpToBoundary k C Ω)

/-- The full spatial load used in the wave initial-data recurrence. -/
def classicalWaveLoad (r : ℕ) :
    W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω) :=
  higherFullLoadCLM r hopen
    (fun i j ↦ (hA (r + 1) i j).toWkpSpaceOn hopen hbounded ∞)
    (fun i ↦ (hB (r + 1) i).toWkpSpaceOn hopen hbounded ∞)
    ((hC (r + 1)).toWkpSpaceOn hopen hbounded ∞)

/-- Every initial spatial load agrees with the original weak form, including
all drift and potential terms. This identity is derived from the coefficients. -/
theorem classicalWaveForm_eq_load (r : ℕ) (G : W^{(r + 2),2}(Ω)) (g : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM G = baseCoordCLM g) :
    classicalAutonomousWaveForm hopen hbounded (hA 1) (hB 1) (hC 0) g =
      loadFunctional (wkpBaseCoordinateCLM (classicalWaveLoad hopen hbounded hA hB hC r G)) := by
  ext v
  have h := fullDivergenceForm_eq_higherFullLoad r hopen
    (fun i j ↦ (hA (r + 1) i j).toWkpSpaceOn hopen hbounded ∞)
    (fun i ↦ (hB (r + 1) i).toWkpSpaceOn hopen hbounded ∞)
    ((hC (r + 1)).toWkpSpaceOn hopen hbounded ∞) G g hbase v
  have hb (b : Fin n → DerivLp n ∞ Ω) :
      multiplicationFirstOrderOperator b = fun i ↦ mulLpLeft (b i) := by
    funext i
    rfl
  rw [hb] at h
  simpa only [classicalAutonomousWaveForm, classicalWaveLoad,
    ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp, ContDiffUpToBoundary.toLp,
    multiplicationFirstOrderOperator, multiplicationZeroOrderOperator, loadFunctional_apply] using h

/-- For the coefficient operator, boundary compatibility automatically
provides the typed weak-form certificate used by the generic constructions. -/
theorem compatible_of_classical_boundary_traces {m : ℕ} {a b : ℝ} {D : WaveProblemData n m Ω a b}
    (hD :
      WaveProblemData.HasCompatibleBoundaryTraces (classicalWaveLoad hopen hbounded hA hB hC) D) :
    D.IsCompatible (classicalAutonomousWaveForm hopen hbounded (hA 1) (hB 1) (hC 0))
      (classicalWaveLoad hopen hbounded hA hB hC) :=
  hD.isCompatible _ (classicalWaveForm_eq_load hopen hbounded hA hB hC)

end Hyperbolic.HigherRegularity
