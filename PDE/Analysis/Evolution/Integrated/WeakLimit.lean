/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Bochner.Duality
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.WeakCompactness

/-!
# Limit closure of integrated weak solutions

The integrated weak formulation of `u' + B(t) u = ℓ`, `u(a) = uInit`
(`IsGelfandIntegratedWeakSolution`) consists of identities

`-∫ₐᵇ ⟪i u, i v⟫ τ' + ∫ₐᵇ B(t)(u, v) τ = ∫ₐᵇ ℓ(v) τ + ⟪uInit, i v⟫ τ(a)`

in which `u ∈ L²(a, b; V)` and `ℓ ∈ L²(a, b; V*)` enter only through continuous linear
functionals: the time and form terms are bounded linear in `u` (the latter because `B` is
measurable and bounded, see `timeDependentFormLpCLM`), and the forcing term is bounded
linear in `ℓ`. Consequently the set of solutions is closed under strong convergence of
`(u, ℓ)` and, more usefully for Galerkin schemes, under weak convergence of `u` in
`L²(V)` and of `ℓ` in `L²(V*)`, with the initial data converging strongly in `H`.

This is the limit passage in the proof of Evans §7.1.2, Theorem 3, where the Galerkin
approximants `u_m ⇀ u` weakly in `L²(0, T; H¹₀)` and the equation, tested against
finite-dimensional trial functions, is carried to the limit. The final theorem handles
exactly that situation: the approximate equation is only known against projected tests
`project n v`, which converge strongly to `v`, and a uniform bound `‖u n‖ ≤ R` controls
the error made by replacing `project n v` with `v`.

## Main results

* `IsGelfandIntegratedWeakSolution.tendsto_L2`: strong `L²` closure.
* `IsGelfandIntegratedWeakSolution.of_weak_limits`: weak closure with fixed initial datum;
  weak convergence of the `V*`-valued forcings is expressed after Riesz transport to
  `L²(V)` via `rieszFromDualLp`, matching the compactness theorems.
* `IsGelfandIntegratedWeakSolution.of_weak_limits_of_initial_tendsto`: weak closure with
  strongly convergent initial data `uInit n → uInit`.
* `isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit`: the Galerkin limit
  theorem with varying trial-space tests `project n v`.

## Implementation notes

No pointwise representative of any trajectory is selected and no time derivative of the
limit is differentiated: every step is continuity of a bounded linear functional in the
norm or weak topology of the relevant Bochner space. The filter `l` is arbitrary (with
`l ≤ atTop` in the projected version so that `project n v → v` along `l`), which allows the
results to be applied along subsequences extracted by weak compactness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, (27)-(30).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-- Strong `L²` closure of the integrated Gelfand weak equation.

Suppose both the forcing and state converge strongly in their natural
Bochner spaces and every approximating pair satisfies the same evolution
equation with the same initial datum.  Then the limiting pair satisfies that
equation as well.

The proof does not choose pointwise representatives or differentiate a
limit.  Each term in the integrated identity is already a continuous linear
functional on either `L²(a,b;V)` or `L²(a,b;V*)`; continuity passes all three
space-time integrals to the limit. This is the closed-graph step needed for
the completion argument with rough forcing. -/
theorem IsGelfandIntegratedWeakSolution.tendsto_L2
    {ι V H : Type*} {l : Filter ι} [l.NeBot]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {ell : ι → Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {ellLimit : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {u : ι → Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uLimit : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit : H}
    (hell : Filter.Tendsto ell l (nhds ellLimit))
    (hu : Filter.Tendsto u l (nhds uLimit))
    (hsol : ∀ i,
      IsGelfandIntegratedWeakSolution T B (fun t ↦ ell i t) (u i) uInit) :
    IsGelfandIntegratedWeakSolution T B
      (fun t ↦ ellLimit t) uLimit uInit := by
  obtain ⟨i⟩ : Nonempty ι := l.nonempty_of_neBot
  refine {
    interval_nonempty := (hsol i).interval_nonempty
    integrable_form := fun v τ ↦
      integrable_timeDependentBilinearTimeTest B v τ.toLp
        hBmeas MB hBbound uLimit
    integrable_forcing := fun v τ ↦ integrable_dualTimeTest v τ.toLp ellLimit
    equation := ?_ }
  intro v τ
  let μab := volume.restrict (Set.Ioc a b)
  have htime : Filter.Tendsto
      (fun i ↦ ∫ t,
        inner ℝ (T.inclusion (u i t)) (T.inclusion v) * τ.derivToLp t ∂μab)
      l
      (nhds (∫ t,
        inner ℝ (T.inclusion (uLimit t)) (T.inclusion v) * τ.derivToLp t
          ∂μab)) := by
    have h := (bilinearTimeTestFunctional T.energyToDual v τ.derivToLp).continuous
      |>.continuousAt.tendsto.comp hu
    simpa only [Function.comp_def, bilinearTimeTestFunctional_apply,
      GelfandTriple.energyToDual_apply, μab] using h
  have hform : Filter.Tendsto
      (fun i ↦ ∫ t, B t (u i t) v * τ.toLp t ∂μab)
      l
      (nhds (∫ t, B t (uLimit t) v * τ.toLp t ∂μab)) := by
    have h :=
      (timeDependentBilinearTimeTestFunctional
        B v τ.toLp hBmeas MB hBbound).continuous
        |>.continuousAt.tendsto.comp hu
    simpa only [Function.comp_def,
      timeDependentBilinearTimeTestFunctional_apply, μab] using h
  have hforcing : Filter.Tendsto
      (fun i ↦ ∫ t, ell i t v * τ.toLp t ∂μab)
      l
      (nhds (∫ t, ellLimit t v * τ.toLp t ∂μab)) := by
    have h := (dualTimeTestFunctional v τ.toLp).continuous
      |>.continuousAt.tendsto.comp hell
    simpa only [Function.comp_def, dualTimeTestFunctional_apply, μab] using h
  exact limit_integrated_initial_identity
    (fun i ↦ (hsol i).equation v τ) htime hform hforcing tendsto_const_nhds

/--
Weak `L²` closure of the integrated Gelfand equation with strongly
convergent initial data.

This is the form used by Galerkin schemes whose initial values are trial
space projections of the prescribed datum.  The space-time terms pass to
the limit weakly, while strong convergence of the initial values closes the
endpoint pairing.
-/
theorem IsGelfandIntegratedWeakSolution.of_weak_limits_of_initial_tendsto
    {ι V H : Type*} {l : Filter ι} [l.NeBot]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {ell : ι → Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {ellLimit : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {u : ι → Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uLimit : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit : ι → H} {uInitLimit : H}
    (hell : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (rieszFromDualLp (ell i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp ellLimit))))
    (hu : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (u i)) l
      (nhds (toWeakSpace ℝ _ uLimit)))
    (huInit : Filter.Tendsto uInit l (nhds uInitLimit))
    (hsol : ∀ i,
      IsGelfandIntegratedWeakSolution
        T B (fun t ↦ ell i t) (u i) (uInit i)) :
    IsGelfandIntegratedWeakSolution
      T B (fun t ↦ ellLimit t) uLimit uInitLimit := by
  obtain ⟨i⟩ : Nonempty ι := l.nonempty_of_neBot
  refine {
    interval_nonempty := (hsol i).interval_nonempty
    integrable_form := fun v τ ↦
      integrable_timeDependentBilinearTimeTest B v τ.toLp
        hBmeas MB hBbound uLimit
    integrable_forcing := fun v τ ↦ integrable_dualTimeTest v τ.toLp ellLimit
    equation := ?_ }
  intro v τ
  let μab := volume.restrict (Set.Ioc a b)
  have htime :
      Filter.Tendsto
        (fun i ↦ ∫ t,
          inner ℝ (T.inclusion (u i t)) (T.inclusion v) *
            τ.derivToLp t ∂μab)
        l
        (nhds (∫ t,
          inner ℝ (T.inclusion (uLimit t)) (T.inclusion v) *
            τ.derivToLp t ∂μab)) := by
    have h := tendsto_bilinearTimeTest_of_tendsto_weak
      hu T.energyToDual v τ.derivToLp
    simpa only [GelfandTriple.energyToDual_apply,
      LinearEquiv.symm_apply_apply, μab] using h
  have hform :
      Filter.Tendsto
        (fun i ↦ ∫ t, B t (u i t) v * τ.toLp t ∂μab)
        l
        (nhds (∫ t, B t (uLimit t) v * τ.toLp t ∂μab)) := by
    simpa only [timeDependentBilinearTimeTestFunctional_apply,
      LinearEquiv.symm_apply_apply, μab] using
      PDE.Analysis.WeakCompactness.tendsto_evaluation hu
        (timeDependentBilinearTimeTestFunctional
          B v τ.toLp hBmeas MB hBbound)
  have hforcing :
      Filter.Tendsto
        (fun i ↦ ∫ t, ell i t v * τ.toLp t ∂μab)
        l
        (nhds (∫ t, ellLimit t v * τ.toLp t ∂μab)) := by
    have h := tendsto_timeTest_of_tendsto_weak
      hell v τ.toLp
    simpa only [integral_dual_pairing_eq_riesz,
      LinearEquiv.symm_apply_apply, μab] using h
  have hinitial :
      Filter.Tendsto
        (fun i ↦ inner ℝ (uInit i) (T.inclusion v) * τ.toFun a) l
        (nhds (inner ℝ uInitLimit (T.inclusion v) * τ.toFun a)) :=
    (tendsto_initial_pairing_of_tendsto
      huInit le_rfl (T.inclusion v)).mul_const (τ.toFun a)
  exact limit_integrated_initial_identity
    (fun i ↦ (hsol i).equation v τ) htime hform hforcing hinitial

/--
Weak `L²` closure of the integrated Gelfand equation when both the states
and the dual-valued forcing terms vary.

Weak convergence of the `V*` trajectories is expressed after Riesz
transport to `L²(V)`, exactly as in the compactness theorems above.  Each
term of the integrated identity is a continuous linear functional in the
appropriate weak topology:

* the time and form terms act on `L²(V)`;
* the forcing term acts on `L²(V*)`; and
* the initial trace is fixed.

This result is stronger than the strong-closure theorem
`IsGelfandIntegratedWeakSolution.tendsto_L2` in the direction required by
Galerkin compactness.
-/
theorem IsGelfandIntegratedWeakSolution.of_weak_limits
    {ι V H : Type*} {l : Filter ι} [l.NeBot]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {ell : ι → Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {ellLimit : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {u : ι → Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uLimit : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit : H}
    (hell : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (rieszFromDualLp (ell i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp ellLimit))))
    (hu : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (u i)) l
      (nhds (toWeakSpace ℝ _ uLimit)))
    (hsol : ∀ i,
      IsGelfandIntegratedWeakSolution
        T B (fun t ↦ ell i t) (u i) uInit) :
    IsGelfandIntegratedWeakSolution
      T B (fun t ↦ ellLimit t) uLimit uInit :=
  of_weak_limits_of_initial_tendsto hBmeas MB hBbound hell hu tendsto_const_nhds hsol

/-- The projected-test limit passage of Evans §7.1.2 for a Gelfand triple.

The approximate equation is required only for the varying trial-space test
`project n v`.  Weak convergence of the states, strong convergence
`project n v → v`, a uniform state bound, and strong convergence of the
initial projections identify every term in the integrated equation. -/
theorem isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hab : a < b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
    {l : Filter ℕ} [l.NeBot]
    (huweak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (u n)) l
      (nhds (toWeakSpace ℝ _ uLimit)))
    (hl : l ≤ Filter.atTop) (R : ℝ) (huR : ∀ n, ‖u n‖ ≤ R)
    (project : ℕ → V → V)
    (hproject : ∀ v : V,
      Filter.Tendsto (fun n ↦ project n v) Filter.atTop (nhds v))
    (u₀ : ℕ → H) (uInit : H)
    (hu₀ : Filter.Tendsto u₀ Filter.atTop (nhds uInit))
    (happrox : ∀ n (v : V) (τ : TimeTest a b),
      -(∫ t, inner ℝ (T.inclusion (u n t))
          (T.inclusion (project n v)) * τ.derivToLp t
            ∂(volume.restrict (Set.Ioc a b))) +
          ∫ t, B t (u n t) (project n v) * τ.toLp t
            ∂(volume.restrict (Set.Ioc a b)) =
        (∫ t, ellLp t (project n v) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b))) +
          inner ℝ (u₀ n) (T.inclusion (project n v)) *
            τ.toFun a) :
    IsGelfandIntegratedWeakSolution T B (fun t ↦ ellLp t) uLimit uInit := by
  refine {
    interval_nonempty := hab
    integrable_form := fun v τ ↦
      integrable_timeDependentBilinearTimeTest B v τ.toLp
        hBmeas MB hBbound uLimit
    integrable_forcing := fun v τ ↦ integrable_dualTimeTest v τ.toLp ellLp
    equation := ?_ }
  intro v τ
  have hv : Filter.Tendsto (fun n ↦ project n v) l (nhds v) :=
    (hproject v).mono_left hl
  apply limit_integrated_initial_identity (l := l) (fun n ↦ happrox n v τ)
  · have htime := tendsto_bilinearTimeTest_of_tendsto_weak_of_tendsto_test
      huweak hv R huR T.energyToDual τ.derivToLp
    simpa only [GelfandTriple.energyToDual_apply] using htime
  · exact tendsto_timeDependentBilinearTimeTest_of_tendsto_weak_of_tendsto_test
      huweak hv R huR B τ.toLp hBmeas MB hMB hBbound
  · exact tendsto_dualTimeTest_of_tendsto_test ellLp hv τ.toLp
  · exact (tendsto_gelfandInitialPairing_of_tendsto T
      (hu₀.mono_left hl) hv).mul_const (τ.toFun a)

end PDE.Analysis.Evolution
