/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Bochner.Constraints
public import PDE.Analysis.Operator.ClosedRangeFactorization
public import PDE.Analysis.TrilinearForm
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Abstract solenoidal spaces

The functional analysis behind incompressible weak formulations does not depend on
the equation. A continuous divergence operator defines
its solenoidal space as a kernel. The kernel is weakly closed, is preserved
by weak Bochner limits, supports the usual convection cancellation, and
determines a canonical pressure whenever the divergence has closed range.

The domain, boundary condition, and solution concept enter only when the ambient
spaces and the divergence and convection operators are instantiated.

## Main results

* `SolenoidalSpace`, `isClosed_solenoidalWeakSet`, `mem_solenoidalSpace_of_tendsto_weak`: the
  kernel of the divergence and its weak closedness.
* `IsSolenoidalTrajectory`, `isSolenoidalTrajectory_of_tendsto_weak`,
  `isCompact_inter_solenoidalTrajectoryWeakSet`: the same for Bochner `L²` trajectories, with
  weak compactness of bounded solenoidal families.
* `solenoidalConvectionForm`, `solenoidalConvectionForm_energy_eq_zero`: convection restricted
  to solenoidal arguments and its energy cancellation.
* `recoveredPressure`, `existsUnique_pressure_mem_range`: the pressure in the divergence range
  representing a functional that vanishes on solenoidal vectors.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.4, Theorem 3 (weak compactness) and Mazur's
  theorem, p. 723.
  <https://doi.org/10.1090/gsm/019>
* R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter I (solenoidal spaces and the pressure), Chapter II (the convection form) and Chapter III
  (compactness for the evolution problem).
  <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

set_option linter.missingDocs true

namespace IncompressibleFlow

open PDE.Analysis

variable {V Q : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The solenoidal subspace associated with a continuous divergence
operator; compare Temam, Chapter I. -/
abbrev SolenoidalSpace (div : V →L[ℝ] Q) :=
  div.ker

/-- The continuous inclusion of a solenoidal space into its ambient space. -/
def solenoidalInclusion (div : V →L[ℝ] Q) :
    SolenoidalSpace div →L[ℝ] V :=
  div.ker.subtypeL

/-- The solenoidal inclusion returns the underlying ambient vector. -/
@[simp]
theorem solenoidalInclusion_apply (div : V →L[ℝ] Q)
    (v : SolenoidalSpace div) :
    solenoidalInclusion div v = (v : V) :=
  rfl

/-- Membership in the solenoidal space is vanishing of the divergence. -/
theorem mem_solenoidalSpace_iff (div : V →L[ℝ] Q) (v : V) :
    v ∈ SolenoidalSpace div ↔ div v = 0 :=
  div.mem_ker

/-- The solenoidal space regarded as a subset of the weak topology. -/
def solenoidalWeakSet (div : V →L[ℝ] Q) :
    Set (WeakSpace ℝ V) :=
  weakConstraintSet fun _ : Unit ↦ div

/-- Weak-space membership is equivalent to the ambient divergence
constraint. -/
@[simp]
theorem toWeakSpace_mem_solenoidalWeakSet
    (div : V →L[ℝ] Q) (v : V) :
    toWeakSpace ℝ V v ∈ solenoidalWeakSet div ↔ div v = 0 := by
  simp [solenoidalWeakSet]

/-- A solenoidal space is weakly closed; compare Mazur's theorem in Evans, Appendix D.4, p. 723. -/
theorem isClosed_solenoidalWeakSet (div : V →L[ℝ] Q) :
    IsClosed (solenoidalWeakSet div) :=
  isClosed_weakConstraintSet fun _ : Unit ↦ div

/-- Weak limits of eventually solenoidal vectors remain solenoidal. -/
theorem mem_solenoidalSpace_of_tendsto_weak
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (div : V →L[ℝ] Q)
    {u : ι → V} {uLimit : V}
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ V (u i)) l
      (nhds (toWeakSpace ℝ V uLimit)))
    (hdiv : ∀ᶠ i in l, u i ∈ SolenoidalSpace div) :
    uLimit ∈ SolenoidalSpace div := by
  have hconstraints :
      ∀ᶠ i in l, ∀ _ : Unit, div (u i) = 0 := by
    filter_upwards [hdiv] with i hi
    exact fun _ ↦ hi
  exact constraints_eq_zero_of_tendsto_weak
    (fun _ : Unit ↦ div) hu hconstraints ()

section Bochner

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A Bochner `L²` trajectory is solenoidal when its divergence vanishes
almost everywhere in time. -/
def IsSolenoidalTrajectory (div : V →L[ℝ] Q) (u : Lp V 2 μ) : Prop :=
  PDE.Analysis.Evolution.SatisfiesBochnerConstraints
    (fun _ : Unit ↦ div) u

/-- The weak-space set of solenoidal Bochner `L²` trajectories. -/
def solenoidalTrajectoryWeakSet (div : V →L[ℝ] Q) :
    Set (WeakSpace ℝ (Lp V 2 μ)) :=
  PDE.Analysis.Evolution.bochnerWeakConstraintSet
    (μ := μ) fun _ : Unit ↦ div

/-- Solenoidal trajectories are exactly the trajectories with almost
everywhere vanishing divergence. -/
@[simp]
theorem isSolenoidalTrajectory_iff_ae
    (div : V →L[ℝ] Q) (u : Lp V 2 μ) :
    IsSolenoidalTrajectory div u ↔ ∀ᵐ t ∂μ, div (u t) = 0 := by
  simp [IsSolenoidalTrajectory,
    PDE.Analysis.Evolution.SatisfiesBochnerConstraints]

/-- A trajectory is solenoidal exactly when the lifted divergence map
vanishes in Bochner `L²`. -/
theorem isSolenoidalTrajectory_iff_compLpL_eq_zero
    (div : V →L[ℝ] Q) (u : Lp V 2 μ) :
    IsSolenoidalTrajectory div u ↔ div.compLpL 2 μ u = 0 := by
  rw [IsSolenoidalTrajectory]
  simpa using
    (PDE.Analysis.Evolution.satisfiesBochnerConstraints_iff_compLpL_eq_zero
      (fun _ : Unit ↦ div) u)

/-- Weak-space membership is equivalent to the solenoidal trajectory
constraint. -/
@[simp]
theorem toWeakSpace_mem_solenoidalTrajectoryWeakSet
    (div : V →L[ℝ] Q) (u : Lp V 2 μ) :
    toWeakSpace ℝ (Lp V 2 μ) u ∈ solenoidalTrajectoryWeakSet div ↔
      IsSolenoidalTrajectory div u := by
  simp [solenoidalTrajectoryWeakSet, IsSolenoidalTrajectory]

/-- The set of solenoidal Bochner `L²` trajectories is weakly closed. -/
theorem isClosed_solenoidalTrajectoryWeakSet (div : V →L[ℝ] Q) :
    IsClosed (solenoidalTrajectoryWeakSet (μ := μ) div) := by
  simpa [solenoidalTrajectoryWeakSet] using
    (PDE.Analysis.Evolution.isClosed_bochnerWeakConstraintSet
      (μ := μ) fun _ : Unit ↦ div)

/-- Weak Bochner `L²` limits of eventually solenoidal trajectories remain
solenoidal. -/
theorem isSolenoidalTrajectory_of_tendsto_weak
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (div : V →L[ℝ] Q)
    {u : ι → Lp V 2 μ} {uLimit : Lp V 2 μ}
    (hu : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ (Lp V 2 μ) (u i)) l
      (nhds (toWeakSpace ℝ (Lp V 2 μ) uLimit)))
    (hdiv : ∀ᶠ i in l, IsSolenoidalTrajectory div (u i)) :
    IsSolenoidalTrajectory div uLimit :=
  PDE.Analysis.Evolution.satisfiesBochnerConstraints_of_tendsto_weak
    (fun _ : Unit ↦ div) hu hdiv

/-- Imposing the solenoidal constraint on a weakly closed, norm-bounded
Bochner `L²` family preserves weak compactness; compare Temam,
Chapter III. -/
theorem isCompact_inter_solenoidalTrajectoryWeakSet
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (div : H →L[ℝ] K)
    {S : Set (WeakSpace ℝ (Lp H 2 μ))}
    (hSclosed : IsClosed S)
    (hSbounded :
      Bornology.IsBounded ((toWeakSpace ℝ (Lp H 2 μ)) ⁻¹' S)) :
    IsCompact (S ∩ solenoidalTrajectoryWeakSet div) := by
  simpa [solenoidalTrajectoryWeakSet] using
    (PDE.Analysis.Evolution.WeakCompactness.isCompact_inter_bochnerWeakConstraintSet
        (μ := μ) (fun _ : Unit ↦ div) hSclosed hSbounded)

end Bochner

section Convection

/-- Restriction of an ambient convection form to solenoidal arguments. -/
def solenoidalConvectionForm
    (div : V →L[ℝ] Q) (B : ContinuousTrilinearForm V V V) :
    ContinuousTrilinearForm
      (SolenoidalSpace div) (SolenoidalSpace div) (SolenoidalSpace div) :=
  B.restrictToSubmodules div.ker div.ker div.ker

/-- The restricted convection form agrees with the ambient form. -/
@[simp]
theorem solenoidalConvectionForm_apply
    (div : V →L[ℝ] Q) (B : ContinuousTrilinearForm V V V)
    (u v w : SolenoidalSpace div) :
    solenoidalConvectionForm div B u v w =
      B (u : V) (v : V) (w : V) :=
  rfl

/-- An ambient product bound passes to the solenoidal convection form. -/
theorem solenoidalConvectionForm_isBoundedBy
    (div : V →L[ℝ] Q) {B : ContinuousTrilinearForm V V V} {C : ℝ}
    (hB : B.IsBoundedBy C) :
    (solenoidalConvectionForm div B).IsBoundedBy C :=
  hB.restrictToSubmodules div.ker div.ker div.ker

/-- Skew-symmetry for solenoidal transport fields passes to the restricted
convection form; compare Temam, Chapter II. -/
theorem solenoidalConvectionForm_isSkewInLastTwo
    (div : V →L[ℝ] Q) {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwoOn div.ker) :
    (solenoidalConvectionForm div B).IsSkewInLastTwo :=
  hB.restrictToSubmodules div.ker

/-- Skew-symmetric solenoidal convection contributes no cubic energy. -/
theorem solenoidalConvectionForm_energy_eq_zero
    (div : V →L[ℝ] Q) {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwoOn div.ker)
    (u : SolenoidalSpace div) :
    solenoidalConvectionForm div B u u u = 0 :=
  (solenoidalConvectionForm_isSkewInLastTwo div hB).energy_eq_zero u

end Convection

/-- A continuous linear map annihilates solenoidal vectors exactly when its
kernel contains the divergence kernel. -/
theorem annihilates_solenoidal_iff_ker_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (div : V →L[ℝ] Q) (ell : V →L[ℝ] W) :
    (∀ v : SolenoidalSpace div, ell (v : V) = 0) ↔
      div.ker ≤ ell.ker := by
  constructor
  · intro h v hv
    exact h ⟨v, hv⟩
  · intro h v
    exact h v.property

section Pressure

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The canonical pressure in the divergence range reconstructed from a functional
that annihilates every solenoidal vector. -/
def recoveredPressureInRange
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) : div.range :=
  ContinuousLinearMap.ClosedRange.multiplierInRange div ell
    ((annihilates_solenoidal_iff_ker_le div ell).1 hannihilates) hclosed

/-- The canonical recovered pressure, regarded as a vector in the ambient
pressure space. -/
def recoveredPressure
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) : K :=
  recoveredPressureInRange div ell hannihilates hclosed

/-- Coercing the range-valued pressure gives the ambient recovered pressure. -/
@[simp]
theorem coe_recoveredPressureInRange
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    (recoveredPressureInRange div ell hannihilates hclosed : K) =
      recoveredPressure div ell hannihilates hclosed :=
  rfl

/-- The recovered pressure belongs to the divergence range. -/
theorem recoveredPressure_mem_range
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    recoveredPressure div ell hannihilates hclosed ∈ div.range := by
  simpa using
    (recoveredPressureInRange div ell hannihilates hclosed).property

/-- The recovered pressure represents the functional through divergence. -/
theorem inner_recoveredPressure_divergence
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) (v : H) :
    ⟪recoveredPressure div ell hannihilates hclosed, div v⟫_ℝ =
      ell v :=
  ContinuousLinearMap.ClosedRange.inner_multiplier_apply div ell
    ((annihilates_solenoidal_iff_ker_le div ell).1 hannihilates)
    hclosed v

/-- The recovered pressure is the unique representative in the divergence
range. -/
theorem recoveredPressure_unique_of_mem_range
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K))
    (p : K) (hp : p ∈ div.range)
    (hrep : ∀ v : H, ⟪p, div v⟫_ℝ = ell v) :
    p = recoveredPressure div ell hannihilates hclosed :=
  ContinuousLinearMap.ClosedRange.multiplier_unique_of_mem_range
    div ell ((annihilates_solenoidal_iff_ker_le div ell).1 hannihilates)
    hclosed p hp hrep

/-- Every functional annihilating solenoidal vectors has a unique
range-valued pressure representative; compare Temam, Chapter I. -/
theorem existsUnique_pressure_mem_range
    (div : H →L[ℝ] K) (ell : H →L[ℝ] ℝ)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    ∃! p : K, p ∈ div.range ∧
      ∀ v : H, ⟪p, div v⟫_ℝ = ell v := by
  apply ContinuousLinearMap.ClosedRange.existsUnique_multiplier_mem_range
  · exact (annihilates_solenoidal_iff_ker_le div ell).1 hannihilates
  · exact hclosed

/-- The recovered pressure solves the adjoint divergence equation. -/
theorem adjoint_recoveredPressure_eq
    (div : H →L[ℝ] K) (ell : StrongDual ℝ H)
    (hannihilates : ∀ v : SolenoidalSpace div, ell (v : H) = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    div.adjoint (recoveredPressure div ell hannihilates hclosed) =
      (InnerProductSpace.toDual ℝ H).symm ell :=
  ContinuousLinearMap.ClosedRange.adjoint_multiplier_eq div ell
    ((annihilates_solenoidal_iff_ker_le div ell).1 hannihilates) hclosed

end Pressure

end IncompressibleFlow
