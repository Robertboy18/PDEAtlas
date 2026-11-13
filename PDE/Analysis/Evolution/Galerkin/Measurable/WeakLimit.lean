/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Bochner
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.Measurable.Bounds
import PDE.Analysis.Evolution.Galerkin.Measurable.IntegratedIdentity
import PDE.Analysis.Evolution.Integrated.WeakLimit
import PDE.Analysis.WeakCompactness

/-!
# Weak limits of measurable Galerkin approximations

The infinite-dimensional half of Evans's Galerkin existence proof, for
coefficients that are merely measurable in time.  Given, for every trial
space `S n` of a stable system, an absolutely continuous Galerkin
approximation with initial value `Pₙ u₀`, the uniform energy estimate bounds
the states in `L²(a, b; V)` independently of `n`, so they converge weakly
along an ultrafilter.  Along the projected test vectors `Pₙ v → v` and the
initial values `ι Pₙ u₀ → u₀`, the integrated Galerkin identities pass to the limit,
since each term pairs a weakly convergent sequence with a strongly convergent one, and the
limit is a Gelfand integrated weak solution with the prescribed initial datum. The
finite-dimensional approximations are a hypothesis; compare
`IsGelfandIntegratedWeakSolution.exists_of_approximations` for continuous data.

## Main results

* `IsGelfandIntegratedWeakSolution.exists_of_ae_approximations`: existence of
  a weak solution `uLimit ∈ L²(a, b; V)` from measurable-in-time Galerkin
  approximations.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 3 (existence of weak solution) and its
  proof. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

/-- Evans's compactness passage for absolutely continuous Galerkin approximations with
coefficients measurable in time.

Let `t ↦ B(t) v` be measurable for each `v`, `‖B(t)‖ ≤ MB` almost everywhere and
`ℓ ∈ L²(a, b; V*)`. If every trial space `S n` carries an almost-everywhere Galerkin
approximation started at the projection of `uInit`, then a weak `L²(a, b; V)` limit of these
approximations is an integrated weak solution with initial value `uInit`. -/
theorem IsGelfandIntegratedWeakSolution.exists_of_ae_approximations
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b C M MB : ℝ} (hab : a < b) (hC : 0 < C)
    (hMB : 0 ≤ MB)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b)))
    (uInit : H)
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n) B ell a b C M
      ((P n).projection uInit)) :
    ∃ uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit := by
  classical
  let state : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)) :=
    fun n ↦ (G n).ambientTrajectoryLp hab.le
  let D : ℝ := (2 / C) * ((1 / 2 : ℝ) * ‖uInit‖ ^ 2 + (M ^ 2 / (2 * C)) * (b - a))
  have hstateSq (n : ℕ) : ‖state n‖ ^ 2 ≤ D := by
    have hinit : ‖T.inclusion ((P n).projection uInit : V)‖ ^ 2 ≤ ‖uInit‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((P n).norm_inclusion_projection_le uInit) 2
    exact ((G n).norm_ambientTrajectoryLp_sq_le hab.le hC).trans (by dsimp only [D]; gcongr)
  obtain ⟨uw, U, hU, huweak⟩ :=
    PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop state
      (isBounded_range_of_norm_sq_le state (by dsimp only [D]; positivity) hstateSq)
  let uLimit := (toWeakSpace ℝ (Lp V 2 (volume.restrict (Set.Ioc a b)))).symm uw
  refine ⟨uLimit, (isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit T B hBmeas MB hMB
    hBbound hab (hell.toLp ell) state uLimit
    (by simpa only [uLimit, LinearEquiv.apply_symm_apply] using huweak) hU (√D)
    (fun n ↦ Real.le_sqrt_of_sq_le (hstateSq n)) (fun n v ↦ ((P n).energyProjection v : V))
    (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdenseEnergy)
    (fun n ↦ T.inclusion ((P n).projection uInit : V)) uInit
    (StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable P
      (eventually_approximable_pivot_of_energy T S hdenseEnergy) uInit)
    fun n v τ ↦ ?_).congr_forcing_ae hell.coeFn_toLp⟩
  have hforcing :
      (∫ t, hell.toLp ell t ((P n).energyProjection v : V) * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) =
      ∫ t, ell t ((P n).energyProjection v : V) * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) :=
    integral_congr_ae (hell.coeFn_toLp.mono fun t ht ↦ by simp only [ht])
  exact hforcing ▸ (G n).integratedInitialIdentity hab.le hBmeas MB hBbound
    ((P n).energyProjection v) τ

end PDE.Analysis.Evolution
