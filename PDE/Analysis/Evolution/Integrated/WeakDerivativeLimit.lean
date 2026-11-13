/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.WeakCompactness

/-!
# Compactness for weak time derivatives

Weak-limit closure and compactness existence results for Gelfand weak time
derivatives. The time-regularity and energy APIs live in the neighboring
`Regularity`, `EnergyBounds`, and `Uniqueness` modules.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, (27).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction
open PDE.Analysis

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gelfand weak-time-derivative relation is closed under simultaneous
weak convergence of states in `L²(V)` and Riesz-transported derivatives in
`L²(V*)`. This is the derivative-identification step `u_m' ⇀ u'` in the proof of
Evans §7.1.2, Theorem 3. -/
theorem hasGelfandWeakTimeDerivativeOn_of_weak_limits
    {ι : Type*} {l : Filter ι} [l.NeBot] {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
    (gLimit : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (u i)) l (nhds (toWeakSpace ℝ _ uLimit)))
    (hg : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (rieszFromDualLp (g i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp gLimit))))
    (happrox : ∀ i, HasGelfandWeakTimeDerivativeOn T (u i) (g i)) :
    HasGelfandWeakTimeDerivativeOn T uLimit gLimit := by
  intro v τ hτa
  have hgInner := tendsto_timeTest_of_tendsto_weak hg v τ.toLp
  have hgPair : Filter.Tendsto
      (fun i ↦ ∫ t, g i t v * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) l
      (nhds (∫ t, gLimit t v * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b)))) := by
    simpa only [integral_dual_pairing_eq_riesz,
      LinearEquiv.symm_apply_apply] using hgInner
  have huForm := tendsto_bilinearTimeTest_of_tendsto_weak hu
    T.energyToDual v τ.derivToLp
  have huNeg : Filter.Tendsto
      (fun i ↦ -(∫ t,
        inner ℝ (T.inclusion (u i t)) (T.inclusion v) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b)))) l
      (nhds (-(∫ t,
        inner ℝ (T.inclusion (uLimit t)) (T.inclusion v) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))))) := by
    simpa only [GelfandTriple.energyToDual_apply,
      LinearEquiv.symm_apply_apply] using huForm.neg
  have hgPair' : Filter.Tendsto
      (fun i ↦ -(∫ t,
        inner ℝ (T.inclusion (u i t)) (T.inclusion v) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b)))) l
      (nhds (∫ t, gLimit t v * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b)))) := by
    apply hgPair.congr'
    exact Filter.Eventually.of_forall fun i ↦ happrox i v τ hτa
  exact tendsto_nhds_unique hgPair' huNeg

/-- Compactness for a state together with its `V*`-valued weak time
derivative. The proof extracts a common ultrafilter along which uniform
`L²(V)` and `L²(V*)` bounds give weak limits satisfying the same weak
derivative relation. The conclusion returns that ultrafilter and both
weak-convergence facts for use in later compactness arguments. -/
theorem exists_hasGelfandWeakTimeDerivativeOn_of_galerkin
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (g : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Bornology.IsBounded (Set.range u))
    (hg : Bornology.IsBounded (Set.range g))
    (happrox : ∀ n, HasGelfandWeakTimeDerivativeOn T (u n) (g n)) :
    ∃ (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (gLimit : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
        (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ _ (u n)) U
        (nhds (toWeakSpace ℝ _ uLimit)) ∧
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ _ (rieszFromDualLp (g n))) U
        (nhds (toWeakSpace ℝ _ (rieszFromDualLp gLimit))) ∧
      HasGelfandWeakTimeDerivativeOn T uLimit gLimit := by
  obtain ⟨uLimit, U₁, hU₁, huweak₁⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      Filter.atTop u hu
  obtain ⟨gLimit, U, hU, hgweak⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter
      (U₁ : Filter ℕ) g hg
  have huweak := huweak₁.mono_left hU
  exact ⟨uLimit, gLimit, U, hU.trans hU₁, huweak, hgweak,
    hasGelfandWeakTimeDerivativeOn_of_weak_limits
      T u g uLimit gLimit huweak hgweak happrox⟩

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
