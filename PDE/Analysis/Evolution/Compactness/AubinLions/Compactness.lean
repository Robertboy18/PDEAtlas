/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.AubinLions.TemporalCompactness
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PDE.Analysis.Evolution.Compactness.AubinLions.SpatialApproximation
import PDE.Analysis.Evolution.Galerkin.Spectral
import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Operator.CompactConvergence

/-!
# Aubin–Lions compactness

The spatial and temporal Galerkin estimates combine into Hilbert-space
Aubin–Lions compactness. A first lemma regards a bounded continuous curve on
a closed interval as a Bochner `L²` trajectory on the open interval.

For a compact Gelfand inclusion `V ↪ H` and `a < b`, a family of trajectories bounded in
`L²(a, b; V)` whose weak time derivatives are bounded in `L²(a, b; V*)` has compact closure in
`L²(a, b; H)` (`isCompact_closure_range_inclusionLp_of_hasGelfandWeakTimeDerivativeOn`). The
pivot bound used by the Arzelà–Ascoli step follows from the Lions–Magenes energy identity and is
not a hypothesis.

## How it works

The statement is the classical Aubin–Lions lemma. Simon proves it for Banach spaces and all
`L^p`; we use the Hilbert structure and prove total boundedness directly. Given `ε > 0`, one
trial projection `Pₙ` of a stable trial system moves every trajectory by less than `ε` in
`L²(a, b; H)`, because the inclusion is compact
(`StableTrialSystem.eventually_norm_inclusionApproximationErrorLp_apply_lt`). At that fixed
dimension the projected trajectories share a `|t - s|^{1/2}` modulus coming from the derivative
bound, and Arzelà–Ascoli makes them precompact (`isCompact_closure_range_projectedTrajectoryLp`).
`PDE.Analysis.totallyBounded_of_uniformly_approximated` then gives
`isCompact_closure_range_inclusionLp_of_bounds`. In `isCompact_closure_range_inclusionLp` the
trial system is the spectral one, `gramSpectralGalerkinSystem`, and the uniform pivot bound is
derived from the `L²` bounds through the Lions–Magenes identity.

## References

* J. Simon, "Compact sets in the space L^p(0,T;B)", *Ann. Mat. Pura Appl.* 146 (1986), 65-96.
  <https://doi.org/10.1007/BF01762360>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972. <https://doi.org/10.1007/978-3-642-65161-8>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A bounded continuous curve on a compact interval, extended by clamping
time to the interval and regarded as a Bochner `L²` trajectory on its
interior. -/
def boundedContinuousFunctionIccToLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (hab : a ≤ b) :
    (Icc a b →ᵇ E) →L[ℝ]
      Lp E 2 (volume.restrict (Ioc a b)) :=
  (BoundedContinuousFunction.toLp
      2 (volume.restrict (Ioc a b)) ℝ).comp
    (BoundedContinuousFunction.compContinuousCLM E ℝ
      ⟨Set.projIcc a b hab, continuous_projIcc⟩)

/-- The Bochner trajectory associated with a bounded continuous interval
curve agrees almost everywhere with its clamped extension. -/
theorem boundedContinuousFunctionIccToLp_apply_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (hab : a ≤ b) (f : Icc a b →ᵇ E) :
    boundedContinuousFunctionIccToLp a b hab f
        =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ f (Set.projIcc a b hab t) := by
  have hcoe :=
    BoundedContinuousFunction.coeFn_toLp
      2 (volume.restrict (Ioc a b)) ℝ
      ((BoundedContinuousFunction.compContinuousCLM E ℝ
        ⟨Set.projIcc a b hab, continuous_projIcc⟩) f)
  have hcomp :
      (fun t ↦
        (f.compContinuous
          ⟨Set.projIcc a b hab, continuous_projIcc⟩) t) =
        fun t ↦ f (Set.projIcc a b hab t) := rfl
  simpa only [boundedContinuousFunctionIccToLp,
    ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.compContinuousCLM_apply,
    hcomp] using hcoe

/-- Include a bounded continuous trial-space curve into the pivot-space
Bochner `L²` space on the open time interval. -/
def projectionBoundedContinuousFunctionToLp
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V}
    (a b : ℝ) (hab : a ≤ b) :
    (Icc a b →ᵇ S) →L[ℝ]
      Lp H 2 (volume.restrict (Ioc a b)) :=
  ((T.inclusion.comp S.subtypeL).compLpL
      2 (volume.restrict (Ioc a b))).comp
    (boundedContinuousFunctionIccToLp a b hab)

/-- The Bochner image of the projected continuous representative is the
pointwise pivot projection of the original trajectory. -/
theorem projectionBoundedContinuousFunctionToLp_apply_evolution
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (hab : a ≤ b)
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K) :
    projectionBoundedContinuousFunctionToLp (T := T) a b hab
        (E.projectionBoundedContinuousFunction hab P) =
      P.pivotProjection.compLpL
        2 (volume.restrict (Ioc a b))
        (T.inclusion.compLpL
          2 (volume.restrict (Ioc a b)) u) := by
  apply Lp.ext
  have hcurve :=
    boundedContinuousFunctionIccToLp_apply_ae a b hab
      (E.projectionBoundedContinuousFunction hab P)
  have houter :=
    (T.inclusion.comp S.subtypeL).coeFn_compLpL
      (boundedContinuousFunctionIccToLp a b hab
        (E.projectionBoundedContinuousFunction hab P))
  have hpivot :=
    P.pivotProjection.coeFn_compLpL
      (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) u)
  have hinclusion :=
    T.inclusion.coeFn_compLpL u
  have hmeasure :
      volume.restrict (Ioc a b) ≤ volume.restrict (uIcc a b) := by
    simpa only [uIcc_of_le hab] using
      (volume : Measure ℝ).restrict_mono_set Ioc_subset_Icc_self
  have hrep := E.ae_eq_inclusion.filter_mono (ae_mono hmeasure)
  filter_upwards [hcurve, houter, hpivot, hinclusion, hrep,
    ae_restrict_mem measurableSet_Ioc] with t hcurve houter hpivot
      hinclusion hrep ht
  rw [projectionBoundedContinuousFunctionToLp,
    ContinuousLinearMap.comp_apply]
  rw [houter, hcurve, hpivot, hinclusion]
  rw [Set.projIcc_of_mem hab ⟨ht.1.le, ht.2⟩]
  rw [E.projectionBoundedContinuousFunction_apply hab P]
  rw [hrep]
  rfl

/-- At a fixed trial dimension, projected Lions–Magenes trajectories with
uniform pivot and projected-derivative bounds are precompact in Bochner
`L²` of the pivot space. -/
theorem isCompact_closure_range_projectedTrajectoryLp
    {ι : Type*} {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ∀ j, ContinuousPivotEvolutionOn T
      (fun r ↦ u j r) (fun r ↦ g j r) a b)
    (hab : a ≤ b)
    {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
    {K : NNReal} (P : StableTrialProjection T S K)
    (U D : ℝ)
    (hU : ∀ j t, t ∈ Icc a b → ‖(E j).representative t‖ ≤ U)
    (hD : ∀ j,
      ‖(gelfandGalerkinForcingMap T S).compLpL
        2 (volume.restrict (Ioc a b)) (g j)‖ ≤ D) :
    IsCompact (closure (range fun j ↦
      P.pivotProjection.compLpL
        2 (volume.restrict (Ioc a b))
        (T.inclusion.compLpL
          2 (volume.restrict (Ioc a b)) (u j)))) := by
  let L :=
    projectionBoundedContinuousFunctionToLp
      (T := T) (S := S) a b hab
  let A : Set (Icc a b →ᵇ S) :=
    range fun j ↦ (E j).projectionBoundedContinuousFunction hab P
  have hA : IsCompact (closure A) :=
    isCompact_closure_range_projectionBoundedContinuousFunction
      E hab P U D hU hD
  have hImage : IsCompact (L '' closure A) :=
    hA.image L.continuous
  have hsubset :
      range (fun j ↦
        P.pivotProjection.compLpL
          2 (volume.restrict (Ioc a b))
          (T.inclusion.compLpL
            2 (volume.restrict (Ioc a b)) (u j))) ⊆
        L '' closure A := by
    rintro x ⟨j, rfl⟩
    refine ⟨(E j).projectionBoundedContinuousFunction hab P, ?_, ?_⟩
    · exact subset_closure ⟨j, rfl⟩
    · exact projectionBoundedContinuousFunctionToLp_apply_evolution
        (E j) hab P
  exact hImage.of_isClosed_subset isClosed_closure
    (hImage.isClosed.closure_subset_iff.mpr hsubset)

/--
Low-level Hilbert-space Aubin–Lions compactness with an explicit uniform
pivot-representative bound on the closed time interval.

If `V ↪ H` is compact, the trajectories are uniformly bounded in
`L²(a,b;V)`, their Lions–Magenes representatives are uniformly bounded in
`H`, and their dual derivatives are uniformly bounded in `L²(a,b;V*)`, then
the included trajectories have compact closure in `L²(a,b;H)`.
-/
theorem isCompact_closure_range_inclusionLp_of_bounds
    {ι : Type*} {a b : ℝ}
    [CompleteSpace H]
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (hcompact : IsCompactOperator T.inclusion)
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ∀ j, ContinuousPivotEvolutionOn T
      (fun r ↦ u j r) (fun r ↦ g j r) a b)
    (hab : a ≤ b)
    (M U G : ℝ) (hM : 0 ≤ M)
    (hu : ∀ j, ‖u j‖ ≤ M)
    (hU : ∀ j t, t ∈ Icc a b → ‖(E j).representative t‖ ≤ U)
    (hg : ∀ j, ‖g j‖ ≤ G) :
    IsCompact (closure (range fun j ↦
      T.inclusion.compLpL
        2 (volume.restrict (Ioc a b)) (u j))) := by
  let μ := volume.restrict (Ioc a b)
  let A : Set (Lp H 2 μ) :=
    range fun j ↦ T.inclusion.compLpL 2 μ (u j)
  have hATotallyBounded : TotallyBounded A := by
    apply PDE.Analysis.totallyBounded_of_uniformly_approximated
    intro ε hε
    have htail :=
      trials.eventually_norm_inclusionApproximationErrorLp_apply_lt
        hcompact 2 μ hM hε
    obtain ⟨n, hn⟩ := Filter.Eventually.exists htail
    let _ : FiniteDimensional ℝ (trials.space n) :=
      trials.finiteDimensional n
    let _ : CompleteSpace (trials.space n) :=
      FiniteDimensional.complete ℝ (trials.space n)
    let B : Set (Lp H 2 μ) :=
      range fun j ↦
        (trials.pivotProjection n).compLpL 2 μ
          (T.inclusion.compLpL 2 μ (u j))
    let L :=
      (gelfandGalerkinForcingMap T (trials.space n)).compLpL 2 μ
    let D := ‖L‖ * G
    have hD : ∀ j,
        ‖(gelfandGalerkinForcingMap T (trials.space n)).compLpL
          2 μ (g j)‖ ≤ D := by
      intro j
      change ‖L (g j)‖ ≤ ‖L‖ * G
      calc
        ‖L (g j)‖ ≤ ‖L‖ * ‖g j‖ := L.le_opNorm (g j)
        _ ≤ ‖L‖ * G :=
          mul_le_mul_of_nonneg_left (hg j) (norm_nonneg L)
    have hBCompact : IsCompact (closure B) := by
      exact isCompact_closure_range_projectedTrajectoryLp
        E hab (trials.projection n) U D hU hD
    refine ⟨B, hBCompact.totallyBounded.subset subset_closure, ?_⟩
    rintro x ⟨j, rfl⟩
    refine ⟨(trials.pivotProjection n).compLpL 2 μ
      (T.inclusion.compLpL 2 μ (u j)), ⟨j, rfl⟩, ?_⟩
    have herr := hn (u j) (hu j)
    rw [dist_eq_norm, norm_sub_rev,
      ← trials.inclusionApproximationErrorLp_apply_eq]
    exact herr
  exact hATotallyBounded.closure.isCompact_of_isClosed isClosed_closure

/--
Abstract Hilbert-space Aubin–Lions compactness.

Let `V ↪ H` be a compact Gelfand inclusion and let a family of trajectories
be uniformly bounded in `L²(a,b;V)`, with dual time derivatives uniformly
bounded in `L²(a,b;V*)`.  If `a < b`, then the included trajectories have
compact closure in `L²(a,b;H)`.

The pivot-space bound needed for the temporal Arzelà–Ascoli argument is not
an extra hypothesis: it follows quantitatively from the Lions–Magenes
energy identity and the two stated `L²` bounds.
-/
theorem isCompact_closure_range_inclusionLp
    {ι : Type*} {a b : ℝ}
    [CompleteSpace V] [CompleteSpace H]
    {T : GelfandTriple (V := V) (H := H)}
    (hcompact : IsCompactOperator T.inclusion)
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ∀ j, ContinuousPivotEvolutionOn T
      (fun r ↦ u j r) (fun r ↦ g j r) a b)
    (hab : a < b)
    (M G : ℝ) (hM : 0 ≤ M)
    (hu : ∀ j, ‖u j‖ ≤ M)
    (hg : ∀ j, ‖g j‖ ≤ G) :
    IsCompact (closure (range fun j ↦
      T.inclusion.compLpL
        2 (volume.restrict (Ioc a b)) (u j))) := by
  let trials := gramSpectralGalerkinSystem T hcompact
  let U :=
    √
      (‖T.inclusion‖ ^ 2 * M ^ 2 / (b - a) + 2 * M * G)
  apply isCompact_closure_range_inclusionLp_of_bounds
    trials hcompact E hab.le M U G hM hu
  · intro j t ht
    exact (E j).norm_representative_le_of_L2_norm_le
      hab hM (hu j) (hg j) t ht
  · exact hg

/-- Aubin–Lions compactness from weak time derivatives of Bochner classes.
The continuous pivot representatives are constructed from the weak equations;
no representative or endpoint trace is part of the input. -/
theorem isCompact_closure_range_inclusionLp_of_hasGelfandWeakTimeDerivativeOn
    {ι : Type*} {a b : ℝ}
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {T : GelfandTriple (V := V) (H := H)}
    (hcompact : IsCompactOperator T.inclusion)
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (hweak : ∀ j, HasGelfandWeakTimeDerivativeOn T (u j) (g j))
    (hab : a < b) (M G : ℝ) (hM : 0 ≤ M)
    (hu : ∀ j, ‖u j‖ ≤ M) (hg : ∀ j, ‖g j‖ ≤ G) :
    IsCompact (closure (range fun j ↦
      T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) (u j))) := by
  have hrep (j : ι) : Nonempty (ContinuousPivotEvolutionOn T
      (fun t ↦ u j t) (fun t ↦ g j t) a b) := by
    obtain ⟨Eopen⟩ := (hweak j).hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hab
    exact Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp (u j)) (Lp.memLp (g j))
  let E (j : ι) := (hrep j).some
  exact isCompact_closure_range_inclusionLp hcompact E hab M G hM hu hg

end PDE.Analysis.Evolution
