/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Analysis.Evolution.Bochner.Duality
import Mathlib.Analysis.LocallyConvex.WeakSpace
import PDE.Analysis.Evolution.Compactness.Lp.PointwiseBounds
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.WeakLimit

/-!
# Weak limits of weak-wave solutions

Two limit-passage facts used in the Galerkin existence proof for weak solutions of second-order
hyperbolic equations (Evans, §7.2.2 and §7.2.3). First, the weak-wave predicate is closed
under common weak limits: if a net of weak waves with the same forcing and initial data has
displacements converging weakly in `L²(a, b; V)`, velocities weakly in `L²(a, b; H)` and
accelerations weakly in `L²(a, b; V*)`, the three limits again form a weak wave. Second,
essential bounds survive weak limits: if the approximations satisfy `‖u_m(t)‖_V ≤ C_u` and
`‖u_m'(t)‖_H ≤ C_v` almost everywhere, so do the weak limits, which therefore lie in
`L^∞(a, b; V)` and `L^∞(a, b; H)`.

## Main results

* `of_weak_limits`: weak closure of `IsGelfandWeakWaveSolution` along any nontrivial filter.
  The displacement identity passes through the bounded map `H → V*`, the velocity identity
  through fixed space-time tests, and the spatial equation through the bounded operator-valued
  multiplication by `B(t)`, after which uniqueness of weak limits identifies
  `acceleration + B u = ell`.
* `improvedRegularity_of_weak_L2_limits`: preservation of almost-everywhere norm bounds under
  weak `L²` convergence, hence `L^∞` membership of the limits. This is the abstract content of
  the improved-regularity statement `u ∈ L^∞(0, T; H¹₀)`, `u' ∈ L^∞(0, T; L²)` obtained from the
  Galerkin energy estimates.

## Implementation notes

Weak `L²` convergence gives no pointwise convergence, so the essential bounds are not passed to
the limit pointwise. Instead each almost-everywhere norm ball is a strongly closed convex
subset of `L²`, hence weakly closed. This makes the result applicable to the ultrafilter limits
used by the compactness theorems and avoids any separability assumption needed to extract a
pointwise subsequence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 3, equation (30), and §7.2.3, proof
  of Theorem 5, estimate (52).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}

/--
Weak sequential/net closure of Evans's weak-wave solution predicate.

Suppose a family of weak-wave solutions has a common weak limit in the three
natural Bochner spaces:

* displacement in `L²(a,b;V)`,
* velocity in `L²(a,b;H)`, and
* acceleration in `L²(a,b;V*)`.

The acceleration convergence is stated after Riesz transport, matching the
Hilbert weak topology used by the compactness theorem.  Then the three limit
objects again satisfy the weak-wave predicate with the same initial data and
forcing.

The proof follows the Evans limit passage:

1. bounded linearity of `H → V*` passes the displacement identity;
2. fixed space-time testing passes the velocity identity; and
3. bounded operator-valued multiplication passes `B(t)u` weakly, so
   uniqueness of weak limits yields `u_tt + B(t)u = ell` in `L²(V*)`.
-/
theorem of_weak_limits {ι : Type*} {l : Filter ι} [l.NeBot] [CompleteSpace V] (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (uApprox : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ι → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (uApprox i)) l (nhds (toWeakSpace ℝ _ u)))
    (hvelocity : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (velocityApprox i)) l
      (nhds (toWeakSpace ℝ _ velocity)))
    (hacceleration : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _
      (rieszFromDualLp (accelerationApprox i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp acceleration))))
    (hApprox : ∀ i, IsGelfandWeakWaveSolution T B ell (uApprox i) (velocityApprox i)
      (accelerationApprox i) q₀ p₀) :
    IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀ := by
  let μab := volume.restrict (Set.Ioc a b)
  let P : Lp H 2 μab →L[ℝ] Lp (StrongDual ℝ V) 2 μab := T.pivotToDual.compLpL 2 μab
  let F : Lp V 2 μab →L[ℝ] Lp (StrongDual ℝ V) 2 μab :=
    timeDependentFormLpCLM B (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  have hF (w : Lp V 2 μab) : ∀ᵐ t ∂μab, (F w : ℝ → StrongDual ℝ V) t = B t (w t) :=
    timeDependentFormLp_apply_ae B w (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  have heqLp (i : ι) : accelerationApprox i + F (uApprox i) = ell := Lp.ext (by
    filter_upwards [Lp.coeFn_add (accelerationApprox i) (F (uApprox i)), hF (uApprox i),
      (hApprox i).equationAE] with t hadd hform heq
    rw [hadd, Pi.add_apply, hform, heq])
  have hweak := tendsto_nhds_unique ((hacceleration.add
    (((WeakSpace.map (rieszFromDualLp.comp F)).continuous.tendsto _).comp hu)).congr
      (f₂ := fun _ ↦ toWeakSpace ℝ _ (rieszFromDualLp ell)) fun i ↦ by
        rw [← heqLp i, map_add, map_add]; rfl) tendsto_const_nhds
  have hRiesz : rieszFromDualLp (acceleration + F u) = rieszFromDualLp ell :=
    (toWeakSpace ℝ _).injective (by rw [map_add, map_add]; exact hweak)
  have hLpEq : acceleration + F u = ell := by
    rw [← rieszToDualLp_rieszFromDualLp (acceleration + F u), hRiesz, rieszToDualLp_rieszFromDualLp]
  refine ⟨hab, (IsGelfandIntegratedWeakSolution.of_weak_limits
      (fun v ↦ (aestronglyMeasurable_const (b := (0 : V →L[ℝ] StrongDual ℝ V))
        (μ := μab)).apply_continuousLinearMap v) 0
      (.of_forall fun _ ↦ (norm_zero (E := V →L[ℝ] StrongDual ℝ V)).le)
      (((WeakSpace.map (rieszFromDualLp.comp P)).continuous.tendsto _).comp hvelocity) hu
      fun i ↦ (hApprox i).displacementIdentity.congr_forcing_ae
        (T.pivotToDual.coeFn_compLpL (velocityApprox i)).symm).congr_forcing_ae
      (T.pivotToDual.coeFn_compLpL velocity), fun w τ ↦ ?_, ?_⟩
  · simpa using limit_integrated_initial_identity (formTerm := fun _ ↦ 0) (formLimit := 0)
      (fun i ↦ by simpa using (hApprox i).velocityIdentity w τ)
      (tendsto_timeTest_of_tendsto_weak hvelocity (T.inclusion w) τ.derivToLp) tendsto_const_nhds
      (by simpa only [integral_dual_pairing_eq_riesz, LinearEquiv.symm_apply_apply, μab] using
        tendsto_timeTest_of_tendsto_weak hacceleration w τ.toLp) tendsto_const_nhds
  · filter_upwards [Lp.coeFn_add acceleration (F u), hF u] with t hadd hform
    rw [← hLpEq, hadd, Pi.add_apply, hform]

/--
Evans, §7.2.3: passage of the estimate (52) to the weak limit.

Suppose the Galerkin displacements converge weakly in `L²(a,b;V)` and the
Galerkin velocities converge weakly in `L²(a,b;H)`.  If the approximations
satisfy the dimension-independent essential bounds

`‖uₘ(t)‖_V ≤ Cᵤ` and `‖uₘ'(t)‖_H ≤ Cᵥ`,

then the limits belong to `L∞(a,b;V)` and `L∞(a,b;H)` and satisfy the same
bounds almost everywhere.

This is the passage to limits after (52).  Weak `L²` convergence alone does
not provide pointwise convergence.  The proof uses that each almost-everywhere
norm ball is strongly
closed and convex in `L²`, hence weakly closed. The result applies directly to ultrafilter limits.
-/
theorem improvedRegularity_of_weak_L2_limits {ι : Type*} {l : Filter ι} [l.NeBot]
    (uApprox : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ι → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (uApprox i)) l (nhds (toWeakSpace ℝ _ u)))
    (hvelocity : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (velocityApprox i)) l
      (nhds (toWeakSpace ℝ _ velocity)))
    (Cu Cv : ℝ) (huBound : ∀ᶠ i in l, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖uApprox i t‖ ≤ Cu)
    (hvelocityBound : ∀ᶠ i in l, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖velocityApprox i t‖ ≤ Cv) :
    MemLp (fun t ↦ u t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      MemLp (fun t ↦ velocity t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖u t‖ ≤ Cu) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖velocity t‖ ≤ Cv) := by
  have huLimit := ae_norm_le_of_tendsto_weak_Lp (fun _ ↦ Cu) hu huBound
  have hvelocityLimit := ae_norm_le_of_tendsto_weak_Lp (fun _ ↦ Cv) hvelocity hvelocityBound
  exact ⟨memLp_top_of_bound (Lp.aestronglyMeasurable u) Cu huLimit,
    memLp_top_of_bound (Lp.aestronglyMeasurable velocity) Cv hvelocityLimit, huLimit,
    hvelocityLimit⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
