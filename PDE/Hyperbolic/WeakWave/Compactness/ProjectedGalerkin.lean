/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.WeakLimit
import PDE.Analysis.WeakCompactness

/-!
# Projected Galerkin weak limits for weak waves

The limit passage from Galerkin approximations to a weak solution in the existence proof for
second-order hyperbolic equations (Evans, §7.2.2), in a basis-free form. A Galerkin
approximation `u_n` on the trial space `S_n ⊆ V` does not solve the ambient equation in `V*`;
it solves the projected equation

`acceleration_n = (ell - B(·) u_n) ∘ P_n`,

that is, the residual tested only through the stable trial projection `P_n`. The theorems here
show that this projected equation, together with common weak limits of displacement, velocity
and acceleration, a uniform displacement bound, and strong convergence `P_n v → v` of the trial
projections, produces a weak wave for the full ambient equation. The mechanism is a
weak–strong pairing: uniform stability of `P_n` and `P_n v → v` give strong convergence of the
lifted projections on `L²(a, b; V)`, and pairing the weakly convergent residuals against these
strongly convergent tests identifies the limit acceleration with `ell - B(·) u` on every
`w ∈ V`.

## Main results

* `equationAE_of_projected_galerkin_weak_limits`: the limit acceleration satisfies
  `acceleration + B(t) u = ell` almost everywhere in `V*`.
* `of_projected_galerkin_weak_limits`: a full weak wave from projected Galerkin data with the
  same exact initial displacement `q₀` and velocity `p₀` at every index.
* `of_projected_galerkin_weak_limits_of_initial_tendsto`: the same when the approximations start
  from index-dependent trial-space initial values converging to `q₀` in `V` and to `p₀` in `H`;
  strong convergence of the data identifies the endpoint terms in the limiting identities.

## Implementation notes

The hypotheses at each index are the two integrated identities (displacement and velocity,
carrying the initial data) and the projected spatial equation, which the canonical
Bochner realization of a finite-dimensional `SecondOrderSolutionOn` provides. The filter `l ≤ atTop`
on `ℕ` accommodates subsequences and ultrafilters alike.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 3, equations (30)-(33).
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
The projected Galerkin spatial equations are closed under Evans's weak
compactness limit.

At level `n`, the acceleration is only the residual precomposed with the
trial projection:

`accelerationₙ = (ell - B(·)uₙ) ∘ Pₙ`.

This is the finite-dimensional statement: in general a Galerkin approximation
does not solve the ambient equation in all of `V*`.  Uniform energy stability
and `Pₙv → v` imply strong convergence of the lifted projections on `L²(V)`.
Pairing the weakly convergent residuals against those strongly convergent
tests identifies the acceleration limit with `ell - B(·)u`, and hence recovers
the full ambient equation only at the limit.
-/
theorem equationAE_of_projected_galerkin_weak_limits [CompleteSpace V]
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (uApprox n)) l (nhds (toWeakSpace ℝ _ u)))
    (hacceleration : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _
      (rieszFromDualLp (accelerationApprox n))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp acceleration))))
    (Ru : ℝ) (huR : ∀ n, ‖uApprox n‖ ≤ Ru)
    (hprojected : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), acceleration t + B t (u t) = ell t := by
  let μab := volume.restrict (Set.Ioc a b)
  let F : Lp V 2 μab →L[ℝ] Lp (StrongDual ℝ V) 2 μab :=
    timeDependentFormLpCLM B (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  let residualApprox : ℕ → Lp (StrongDual ℝ V) 2 μab := fun n ↦
    gelfandResidualLp B ell (uApprox n) (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  let residualLimit : Lp (StrongDual ℝ V) 2 μab :=
    gelfandResidualLp B ell u (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  have hres (w : Lp V 2 μab) : gelfandResidualLp B ell w
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound = ell - F w :=
    congrArg (ell - ·) (timeDependentFormLpCLM_apply B
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound w).symm
  have hform : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (rieszFromDualLp (F (uApprox n)))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp (F u)))) :=
    ((WeakSpace.map (rieszFromDualLp.comp F)).continuous.tendsto _).comp hu
  have hresidual : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (rieszFromDualLp (residualApprox n))) l
        (nhds (toWeakSpace ℝ _ (rieszFromDualLp residualLimit))) := by
    simpa only [residualApprox, residualLimit, hres, map_sub] using
      hform.const_sub (toWeakSpace ℝ _ (rieszFromDualLp ell))
  have hresidualR (n : ℕ) : ‖rieszFromDualLp (residualApprox n)‖ ≤
      ‖(rieszFromDualLp : Lp (StrongDual ℝ V) 2 μab →L[ℝ] Lp V 2 μab)‖ * (‖ell‖ + MB * Ru) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    refine (norm_gelfandResidualLp_le B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound).trans ?_
    gcongr
    exact huR n
  have hRiesz : rieszFromDualLp acceleration = rieszFromDualLp residualLimit :=
    ext_inner_left ℝ fun y ↦ tendsto_nhds_unique
      (by simpa using PDE.Analysis.WeakCompactness.tendsto_evaluation hacceleration (innerSL ℝ y))
      ((SecondOrderSolutionOn.tendsto_inner_riesz_projectedDual_compLpL P hP hl residualApprox
        residualLimit hresidual _ hresidualR y).congr
        (f₂ := fun n ↦ inner ℝ y (rieszFromDualLp (accelerationApprox n))) fun n ↦
          congrArg (fun z ↦ inner ℝ y (rieszFromDualLp z)) (hprojected n).symm)
  have hLpEq : acceleration = residualLimit := by
    rw [← rieszToDualLp_rieszFromDualLp acceleration, hRiesz, rieszToDualLp_rieszFromDualLp]
  filter_upwards [gelfandResidualLp_apply_ae B ell u
    (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound] with t hresidualPoint
  rw [hLpEq, hresidualPoint]
  abel

/--
Evans's projected Galerkin limit passage with convergent approximate initial
data.

Unlike `of_projected_galerkin_weak_limits`, the finite-dimensional
displacement and velocity may start from trial-space projections depending
on the Galerkin index.  Strong convergence of those initial values identifies
the two endpoint terms in the limiting weak-wave equations.
-/
theorem of_projected_galerkin_weak_limits_of_initial_tendsto [CompleteSpace V] (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (uApprox n)) l (nhds (toWeakSpace ℝ _ u)))
    (hvelocity : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (velocityApprox n)) l
      (nhds (toWeakSpace ℝ _ velocity)))
    (hacceleration : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _
      (rieszFromDualLp (accelerationApprox n))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp acceleration))))
    (Ru : ℝ) (huR : ∀ n, ‖uApprox n‖ ≤ Ru) (q₀Approx : ℕ → V) (p₀Approx : ℕ → H)
    (hq₀ : Filter.Tendsto q₀Approx Filter.atTop (nhds q₀))
    (hp₀ : Filter.Tendsto p₀Approx Filter.atTop (nhds p₀))
    (hdisplacementApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox n t)) (uApprox n) (T.inclusion (q₀Approx n)))
    (hvelocityApprox : ∀ n (w : V) (τ : TimeTest a b), -(∫ t,
      inner ℝ (velocityApprox n t) (T.inclusion w) * τ.derivToLp t
      ∂(volume.restrict (Set.Ioc a b))) = (∫ t, accelerationApprox n t w *
      τ.toLp t ∂(volume.restrict (Set.Ioc a b))) + inner ℝ (p₀Approx n) (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)) :
    IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀ := by
  refine ⟨hab, (IsGelfandIntegratedWeakSolution.of_weak_limits_of_initial_tendsto
      (fun v ↦ (aestronglyMeasurable_const (b := (0 : V →L[ℝ] StrongDual ℝ V))
        (μ := volume.restrict (Set.Ioc a b))).apply_continuousLinearMap v) 0
      (.of_forall fun _ ↦ (norm_zero (E := V →L[ℝ] StrongDual ℝ V)).le)
      (((WeakSpace.map (rieszFromDualLp.comp (T.pivotToDual.compLpL 2 _))).continuous.tendsto
        _).comp hvelocity) hu ((T.inclusion.continuous.tendsto _).comp (hq₀.mono_left hl))
      fun n ↦ (hdisplacementApprox n).congr_forcing_ae
        (T.pivotToDual.coeFn_compLpL (velocityApprox n)).symm).congr_forcing_ae
      (T.pivotToDual.coeFn_compLpL velocity), fun w τ ↦ ?_,
    equationAE_of_projected_galerkin_weak_limits hBmeas MB hMB hBbound P hP hl uApprox
      accelerationApprox hu hacceleration Ru huR hprojected⟩
  simpa using limit_integrated_initial_identity (formTerm := fun _ ↦ 0) (formLimit := 0)
    (fun n ↦ by simpa using hvelocityApprox n w τ)
    (tendsto_timeTest_of_tendsto_weak hvelocity (T.inclusion w) τ.derivToLp) tendsto_const_nhds
    (by simpa only [integral_dual_pairing_eq_riesz, LinearEquiv.symm_apply_apply] using
      tendsto_timeTest_of_tendsto_weak hacceleration w τ.toLp)
    ((tendsto_initial_pairing_of_tendsto hp₀ hl (T.inclusion w)).mul_const (τ.toFun a))

/--
Projected Galerkin limit passage with exact common initial data.

At every approximation index, the hypotheses require:

1. the integrated displacement identity `uₙ' = velocityₙ`;
2. the integrated velocity identity `velocityₙ' = accelerationₙ`; and
3. the projected spatial equation identifying `accelerationₙ` with the
   residual tested through `Pₙ`.

The two integrated identities use the same exact initial displacement `q₀`
and velocity `p₀` at every index. When trial-space initial values merely
converge to these data, use
`of_projected_galerkin_weak_limits_of_initial_tendsto` instead.

Together with common weak limits, a uniform displacement bound, and strongly
convergent stable trial projections, these identities produce a genuine
weak wave solution in the natural Evans class

`L²(V) × L²(H) × L²(V*)`.

This is the constant-data case of `of_projected_galerkin_weak_limits_of_initial_tendsto`.
-/
theorem of_projected_galerkin_weak_limits [CompleteSpace V] (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hu : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (uApprox n)) l (nhds (toWeakSpace ℝ _ u)))
    (hvelocity : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (velocityApprox n)) l
      (nhds (toWeakSpace ℝ _ velocity)))
    (hacceleration : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _
      (rieszFromDualLp (accelerationApprox n))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp acceleration))))
    (Ru : ℝ) (huR : ∀ n, ‖uApprox n‖ ≤ Ru)
    (hdisplacementApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox n t)) (uApprox n) (T.inclusion q₀))
    (hvelocityApprox : ∀ n (w : V) (τ : TimeTest a b), -(∫ t,
      inner ℝ (velocityApprox n t) (T.inclusion w) * τ.derivToLp t
      ∂(volume.restrict (Set.Ioc a b))) = (∫ t, accelerationApprox n t w *
      τ.toLp t ∂(volume.restrict (Set.Ioc a b))) + inner ℝ p₀ (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)) :
    IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀ :=
  of_projected_galerkin_weak_limits_of_initial_tendsto hab hBmeas MB hMB hBbound P hP hl
    uApprox velocityApprox accelerationApprox hu hvelocity hacceleration Ru huR (fun _ ↦ q₀)
    (fun _ ↦ p₀) tendsto_const_nhds tendsto_const_nhds hdisplacementApprox hvelocityApprox
    hprojected

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
