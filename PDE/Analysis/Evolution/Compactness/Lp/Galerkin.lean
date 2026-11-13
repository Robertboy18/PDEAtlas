/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.Approximation
import Mathlib.Tactic.Positivity.Finset
public import PDE.Analysis.Evolution.Compactness.Lp.Basic -- shake: keep
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Bochner L² realizations of Galerkin trajectories

A Gelfand–Galerkin approximation `u_m : [a, b] → S_m` is continuous in time
with a continuous `V*`-valued derivative, so both define Bochner classes in
`L²(a, b; V)` and `L²(a, b; V*)`. We construct those classes and prove the two
dimension-independent bounds that feed the compactness argument: the
integrated coercive energy inequality bounds `‖u_m‖_{L²(V)}` by the initial
pivot energy and the forcing, and, when the trial projections are uniformly
stable, the same quantities together with a uniform bound on `‖B(t)‖` bound
`‖u_m'‖_{L²(V*)}`.  It also lifts a stable trial projection to an ambient
operator `V → V` and shows that strong convergence `Pₙ v → v` transfers to
`L²(a, b; V)`.  These are the space-time forms of the uniform estimates in
Evans's Galerkin proof.

## Main results

* `StableTrialProjection.ambientEnergyProjection`,
  `StableTrialProjection.tendsto_ambientEnergyProjection_compLpL`: the
  ambient projection and its strong convergence on Bochner trajectories.
* `GelfandGalerkinApproximation.trajectoryLp`,
  `GelfandGalerkinApproximation.derivativeLp`: the `L²(V)` and `L²(V*)`
  realizations, with `_apply_ae` lemmas.
* `GelfandGalerkinApproximation.norm_trajectoryLp_sq_le`,
  `GelfandGalerkinApproximation.norm_derivativeLp_sq_le`: explicit
  dimension-independent bounds.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2, estimate (20) (bounds for the
  Galerkin approximations uniform in `m`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace StableTrialProjection

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A stable Galerkin projection, regarded as an ambient operator `V → V`.

`energyProjection` records its range in the finite-dimensional trial
subspace. This ambient form is the one that acts pointwise on Bochner
trajectories and converges strongly to the identity. -/
noncomputable def ambientEnergyProjection
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) : V →L[ℝ] V :=
  S.subtypeL.comp P.energyProjection

omit [CompleteSpace V] in
/-- The ambient projection of `v` is its trial-space projection, viewed in
`V`. -/
@[simp]
theorem ambientEnergyProjection_apply
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (v : V) :
    P.ambientEnergyProjection v = (P.energyProjection v : V) :=
  rfl

omit [CompleteSpace V] in
/-- The ambient projection inherits the dimension-independent energy-space
bound from `StableTrialProjection`. -/
theorem norm_ambientEnergyProjection_le
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (v : V) :
    ‖P.ambientEnergyProjection v‖ ≤ (K : ℝ) * ‖v‖ := by
  change ‖P.energyProjection v‖ ≤ (K : ℝ) * ‖v‖
  simpa only [energyProjection_apply] using P.norm_le v

omit [CompleteSpace V] in
/-- Strong convergence of stable trial projections lifts to every Bochner
`L²` trajectory.

This is the space-time form of the density step in Evans's Galerkin proof:
pointwise convergence `Pₙv → v` plus one dimension-independent stability
constant implies `Pₙu → u` in `L²(a,b;V)` for every `u`. -/
theorem tendsto_ambientEnergyProjection_compLpL
    {T : GelfandTriple (V := V) (H := H)}
    {S : ℕ → Submodule ℝ V} {K : NNReal}
    (P : ∀ n, StableTrialProjection T (S n) K)
    (hP : ∀ v : V, Filter.Tendsto
      (fun n ↦ ((P n).energyProjection v : V))
      Filter.atTop (nhds v))
    (u : Lp V 2 μ) :
    Filter.Tendsto
      (fun n ↦ ((P n).ambientEnergyProjection).compLpL 2 μ u)
      Filter.atTop (nhds u) := by
  exact tendsto_compLpL_of_tendsto_strongly
    (fun n ↦ (P n).ambientEnergyProjection) (K : ℝ) K.coe_nonneg
    (fun n v ↦ (P n).norm_ambientEnergyProjection_le v)
    (fun v ↦ by simpa only [ambientEnergyProjection_apply] using hP v)
    u

end StableTrialProjection

section GelfandGalerkinLp

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace GelfandGalerkinApproximation

/-- A trial-space trajectory viewed in the ambient energy space. -/
def ambientTrajectory
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) : ℝ → V :=
  fun t ↦ (G.trajectory t : V)

omit [CompleteSpace V] in
/-- The ambient trajectory is continuous on the Galerkin time interval. -/
theorem continuousOn_ambientTrajectory
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    ContinuousOn G.ambientTrajectory (Set.Icc a b) := by
  apply S.subtypeL.continuous.comp_continuousOn
  intro t ht
  exact (G.derivative t ht).continuousWithinAt

omit [CompleteSpace V] in
/-- The canonical ambient `V*` derivative is continuous on the Galerkin time
interval. -/
theorem continuousOn_dualDerivative
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    ContinuousOn G.dualDerivative (Set.Icc a b) :=
  T.energyToDual.continuous.comp_continuousOn
    (S.subtypeL.continuous.comp_continuousOn G.derivativeContinuous)

/-- Bochner `L²(0,T;V)` realization of a Galerkin trajectory. -/
noncomputable def trajectoryLp
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    Lp V 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_of_continuousOn G.continuousOn_ambientTrajectory).toLp
    G.ambientTrajectory

/-- Bochner `L²(0,T;V*)` realization of the canonical Galerkin derivative. -/
noncomputable def derivativeLp
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_of_continuousOn G.continuousOn_dualDerivative).toLp
    G.dualDerivative

omit [CompleteSpace V] in
/-- The `L²(V)` realization agrees almost everywhere with the ambient
Galerkin trajectory. -/
theorem trajectoryLp_apply_ae
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    (G.trajectoryLp : ℝ → V) =ᵐ[volume.restrict (Set.Ioc a b)]
      G.ambientTrajectory :=
  (memLp_restrict_Ioc_of_continuousOn G.continuousOn_ambientTrajectory).coeFn_toLp

omit [CompleteSpace V] in
/-- The `L²(V*)` realization agrees almost everywhere with the canonical
dual derivative. -/
theorem derivativeLp_apply_ae
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) :
    (G.derivativeLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
      G.dualDerivative :=
  (memLp_restrict_Ioc_of_continuousOn G.continuousOn_dualDerivative).coeFn_toLp

omit [CompleteSpace V] in
/-- Explicit dimension-independent squared `L²(V)` bound inherited from the
integrated Galerkin energy inequality. -/
theorem norm_trajectoryLp_sq_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C) :
    ‖G.trajectoryLp‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a)) := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  have hae :
      (fun t ↦ ‖G.trajectoryLp t‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun t ↦ ‖G.ambientTrajectory t‖ ^ 2 :=
    G.trajectoryLp_apply_ae.fun_comp (fun z : V ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae]
  rw [← intervalIntegral.integral_of_le hab]
  exact G.integral_norm_sq_le hab hC

omit [CompleteSpace V] in
/-- Explicit dimension-independent squared `L²(V*)` bound for the canonical
Galerkin derivative under a uniformly stable trial projection. -/
theorem norm_derivativeLp_sq_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M MB : ℝ} {K : NNReal} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b) (hC : 0 < C)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hB : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB) :
    ‖G.derivativeLp‖ ^ 2 ≤
      2 * (K : ℝ) ^ 2 *
        (M ^ 2 * (b - a) + MB ^ 2 *
          ((2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
            (M ^ 2 / (2 * C)) * (b - a)))) := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  have hae :
      (fun t ↦ ‖G.derivativeLp t‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun t ↦ ‖G.dualDerivative t‖ ^ 2 :=
    G.derivativeLp_apply_ae.fun_comp (fun z : StrongDual ℝ V ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae, ← intervalIntegral.integral_of_le hab]
  refine (G.integral_norm_dualDerivative_sq_le P hab hell hB).trans ?_
  gcongr
  exact G.integral_norm_sq_le hab hC

end GelfandGalerkinApproximation

end GelfandGalerkinLp

end PDE.Analysis.Evolution
