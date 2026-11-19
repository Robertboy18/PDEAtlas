/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.WeakCompactness

/-!
# Compactness for pivot-valued weak time derivatives

The compactness step for the improved time regularity of Evans §7.1.3, Theorem 5(i).
A state sequence bounded in `L²(V)` and
a velocity sequence bounded in `L²(H)` have weak limits along one
ultrafilter. Weak continuity of the canonical map `L²(H) → L²(V*)` then
identifies the limiting velocity with the weak time derivative of the
limiting state.

The second result uses a prescribed strong limit for the states and preserves
the quantitative squared-norm bound for the limiting `H`-valued derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, (27), and §7.1.3, Theorem 5(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis

namespace PDE.Analysis.Evolution

/-! ## Weak compactness for pivot derivatives -/

section PivotWeakDerivativeCompactness

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak limits of states and of `L²(H)` derivatives identify the weak time derivative of the
limiting state: both sides of the defining identity are weakly continuous tests in `L²(H)` and
`L²(V)`. -/
private theorem hasGelfandWeakTimeDerivativeOn_of_pivot_weak_limits
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    {U : Filter ℕ} [U.NeBot] {u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uLimit : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {duH : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b))}
    {duHLimit : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (hu : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (u n)) U (nhds (toWeakSpace ℝ _ uLimit)))
    (hduH : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (duH n)) U
      (nhds (toWeakSpace ℝ _ duHLimit)))
    (happrox : ∀ n, HasGelfandWeakTimeDerivativeOn T (u n)
      (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) (duH n))) :
    HasGelfandWeakTimeDerivativeOn T uLimit
      (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) duHLimit) := by
  have hpair (w : Lp H 2 (volume.restrict (Set.Ioc a b))) (v : V) (τ : TimeTest a b) :
      ∫ t, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) w t v * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
        ∫ t, inner ℝ (w t) (T.inclusion v) * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) := by
    apply integral_congr_ae
    filter_upwards [T.pivotToDual.coeFn_compLpL w] with t ht
    rw [ht, GelfandTriple.pivotToDual_apply]
  intro v τ hτa
  have hdu := tendsto_timeTest_of_tendsto_weak hduH (T.inclusion v) τ.toLp
  have huForm := tendsto_bilinearTimeTest_of_tendsto_weak hu T.energyToDual v τ.derivToLp
  simp only [LinearEquiv.symm_apply_apply, GelfandTriple.energyToDual_apply] at hdu huForm
  rw [hpair]
  refine tendsto_nhds_unique (hdu.congr' (Filter.Eventually.of_forall fun n ↦ ?_)) huForm.neg
  rw [← hpair, happrox n v τ hτa]

/--
Weak compactness for states whose weak time derivatives are represented by a
bounded sequence in the pivot space.

The proof extracts one common ultrafilter along which the state sequence
converges weakly in `L²(a,b;V)` and the pivot derivatives converge weakly in
`L²(a,b;H)`, then identifies the limiting velocity with the weak time derivative of the
limiting state, as Evans does for `u_m' ⇀ u'` in the proof of §7.1.2, Theorem 3. The
conclusion returns the common ultrafilter and
both weak-convergence facts.
-/
theorem exists_hasGelfandWeakTimeDerivativeOn_of_bounded_pivot_derivatives
    [CompleteSpace V] [CompleteSpace H]
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (duH : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hu : Bornology.IsBounded (Set.range u))
    (hduH : Bornology.IsBounded (Set.range duH))
    (happrox : ∀ n,
      HasGelfandWeakTimeDerivativeOn T (u n)
        (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
          (duH n))) :
    ∃ (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (duHLimit : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ _ (u n)) U
        (nhds (toWeakSpace ℝ _ uLimit)) ∧
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ _ (duH n)) U
        (nhds (toWeakSpace ℝ _ duHLimit)) ∧
      HasGelfandWeakTimeDerivativeOn T uLimit
        (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
          duHLimit) := by
  obtain ⟨uLimit, U₁, hU₁, huweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      Filter.atTop u hu
  obtain ⟨duHLimit, U, hU, hduHweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      (U₁ : Filter ℕ) duH hduH
  exact ⟨uLimit, duHLimit, U, hU.trans hU₁, huweak.mono_left hU, hduHweak,
    hasGelfandWeakTimeDerivativeOn_of_pivot_weak_limits T (huweak.mono_left hU) hduHweak
      happrox⟩

/--
Strong `L²(V)` convergence preserves a uniformly bounded `L²(H)`-valued weak
time derivative.

The state sequence converges strongly, while only a uniform quantitative
bound is assumed for the pivot derivatives. Weak compactness supplies a
common ultrafilter limit for those derivatives. The weak derivative identity
passes to the prescribed strong state limit, and weak lower semicontinuity
retains the limiting squared-norm bound.
-/
theorem exists_pivot_derivative_of_tendsto_L2
    [CompleteSpace H]
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
    (duH : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (bound : ℕ → ℝ) (boundLimit : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds uLimit))
    (hduBound : ∀ n, ‖duH n‖ ^ 2 ≤ bound n)
    (hbound : Filter.Tendsto bound Filter.atTop (nhds boundLimit))
    (happrox : ∀ n,
      HasGelfandWeakTimeDerivativeOn T (u n)
        (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
          (duH n))) :
    ∃ duHLimit : Lp H 2 (volume.restrict (Set.Ioc a b)),
      HasGelfandWeakTimeDerivativeOn T uLimit
          (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
            duHLimit) ∧
        ‖duHLimit‖ ^ 2 ≤ boundLimit := by
  have hboundNonneg (n : ℕ) : 0 ≤ bound n :=
    (sq_nonneg ‖duH n‖).trans (hduBound n)
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto bound hbound).exists_norm_le
  have hboundLe (n : ℕ) : bound n ≤ D := (Real.le_norm_self _).trans (hD _ ⟨n, rfl⟩)
  -- Compactify the pivot derivatives first; the strong state convergence
  -- then supplies the state limit along the same ultrafilter.
  obtain ⟨duHWeak, U, hU, hduHWeak⟩ :=
    PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop duH (isBounded_range_of_norm_sq_le duH ((hboundNonneg 0).trans (hboundLe 0))
        fun n ↦ (hduBound n).trans (hboundLe n))
  let duHLimit : Lp H 2 (volume.restrict (Set.Ioc a b)) := (toWeakSpace ℝ _).symm duHWeak
  have hduHWeak' : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (duH n)) U
      (nhds (toWeakSpace ℝ _ duHLimit)) := by
    simpa only [duHLimit, LinearEquiv.apply_symm_apply] using hduHWeak
  have huWeak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (u n)) U
      (nhds (toWeakSpace ℝ _ uLimit)) :=
    (toWeakSpaceCLM ℝ _).continuous.continuousAt.tendsto.comp (hu.mono_left hU)
  -- Test weak convergence against the limit itself to obtain the Hilbert
  -- norm lower-semicontinuity estimate with the varying scalar bound.
  have hinner : Filter.Tendsto (fun n ↦ inner ℝ duHLimit (duH n)) U
      (nhds (inner ℝ duHLimit duHLimit)) := by
    simpa [LinearEquiv.symm_apply_apply] using
      PDE.Analysis.WeakCompactness.tendsto_evaluation hduHWeak' (innerSL ℝ duHLimit)
  have hlimit : ‖duHLimit‖ ^ 2 ≤ ‖duHLimit‖ * √boundLimit := by
    simpa only [real_inner_self_eq_norm_sq] using le_of_tendsto_of_tendsto' hinner
      ((hbound.mono_left hU).sqrt.const_mul ‖duHLimit‖) fun n ↦ (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hduBound n)) (norm_nonneg _))
  refine ⟨duHLimit, hasGelfandWeakTimeDerivativeOn_of_pivot_weak_limits T huWeak hduHWeak'
    happrox, ?_⟩
  nlinarith [sq_nonneg (√boundLimit - ‖duHLimit‖), Real.sq_sqrt
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hbound hboundNonneg)]

end PivotWeakDerivativeCompactness

end PDE.Analysis.Evolution
