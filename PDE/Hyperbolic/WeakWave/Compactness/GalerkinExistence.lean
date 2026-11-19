/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.WeakCompactness
import PDE.Hyperbolic.WeakWave.Compactness.ProjectedGalerkin
import PDE.Hyperbolic.WeakWave.Compactness.WeakLimits
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives

/-!
# Galerkin existence for weak waves

The compactness step of the existence proof for weak solutions of second-order hyperbolic
equations (Evans, §7.2.2), following the dimension-independent energy estimates. Given a
sequence of projected Galerkin approximations with the same exact initial data `q₀ ∈ V`,
`p₀ ∈ H`, bounded in `L²(a, b; V) × L²(a, b; H) × L²(a, b; V*)`, one common weakly convergent
subnet is extracted along an ultrafilter and the projected-limit theorem of `ProjectedGalerkin`
identifies its limit as a weak wave for the ambient equation. When the approximations also
carry the essential bounds `‖u_m(t)‖_V ≤ C_u`, `‖u_m'(t)‖_H ≤ C_v` from the energy estimate,
the limit inherits them and lies in `L^∞(a, b; V) × L^∞(a, b; H)`, which is the improved
regularity statement of Evans, §7.2.3. We also prove the first regularity
consequence of the weak-wave definition, a continuous `H`-valued displacement representative
with the prescribed initial trace.

## Main results

* `exists_of_bounded_projected_galerkin_family`: existence of a weak wave from a bounded
  projected Galerkin family with exact common initial data. The auxiliary bound `Ru` on the
  displacements is the uniform norm the weak–strong projected pairing needs; in applications it
  comes from the Galerkin energy estimate.
* `exists_of_bounded_projected_galerkin_family_with_improvedRegularity`: the same, with the
  additional conclusions `u ∈ L^∞(a, b; V)`, `velocity ∈ L^∞(a, b; H)` and the almost-everywhere
  bounds `C_u`, `C_v`. The regularity is proved; it is not part of the definition of a weak
  solution.
* `exists_displacementContinuousRepresentative`: a weak wave has a continuous `H`-valued
  representative of `J u` on `[a, b]` with value `J q₀` at `a`, obtained from the Lions-Magenes
  theorem applied to `u' = J* velocity`.

## Implementation notes

For approximations whose initial values are trial-space projections depending on the index,
first extract a common weak limit and then use
`of_projected_galerkin_weak_limits_of_initial_tendsto`. Displacement, velocity and acceleration
are passed to the limit along the same ultrafilter, and `improvedRegularity_of_weak_L2_limits`
preserves the closed convex norm balls along that filter.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 3, and §7.2.3, Theorem 5(i) and estimate
  (52).
  <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*, Vol. I,
  Springer, 1972, Chapter 1.
  <https://doi.org/10.1007/978-3-642-65161-8_1>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis
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
Weak-wave existence from a bounded Galerkin family with fixed initial data.

This theorem performs the compactness step that follows the
dimension-independent energy estimates. Every approximation must satisfy
the integrated identities with the same exact displacement `q₀` and velocity
`p₀`, together with the projected spatial equation:

* the integrated displacement equation;
* the integrated velocity equation;
* the spatial equation tested through the stable trial projection.

For general projected initial data, the finite-dimensional identities carry
index-dependent boundary values. Their limit passage is provided by
`of_projected_galerkin_weak_limits_of_initial_tendsto`.

Uniform boundedness in `L²(V)`, `L²(H)`, and `L²(V*)` then yields one common
weakly convergent subnet.  The projected-test limit theorem identifies its
spatial equation on every ambient test in `V`, producing a weak wave
solution in the Evans energy class.

Boundedness supplies the uniform displacement norm used in the weak-strong
projected pairing.
-/
theorem exists_of_bounded_projected_galerkin_family [CompleteSpace V] [CompleteSpace H]
    (hab : a < b) (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ)
    (hMB : 0 ≤ MB) (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {Sseq : ℕ → Submodule ℝ V} {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (huBounded : Bornology.IsBounded (Set.range uApprox))
    (hvelocityBounded : Bornology.IsBounded (Set.range velocityApprox))
    (haccelerationBounded : Bornology.IsBounded (Set.range accelerationApprox))
    (hdisplacementApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox n t)) (uApprox n) (T.inclusion q₀))
    (hvelocityApprox : ∀ n (w : V) (τ : TimeTest a b), -(∫ t,
      inner ℝ (velocityApprox n t) (T.inclusion w) * τ.derivToLp t
      ∂(volume.restrict (Set.Ioc a b))) = (∫ t, accelerationApprox n t w *
      τ.toLp t ∂(volume.restrict (Set.Ioc a b))) + inner ℝ p₀ (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀ := by
  obtain ⟨Ru, hRu⟩ := huBounded.exists_norm_le
  obtain ⟨u, U₁, hU₁, hu₁⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter Filter.atTop uApprox
      huBounded
  obtain ⟨velocity, U₂, hU₂, hvelocity₂⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₁ : Filter ℕ)
      velocityApprox hvelocityBounded
  obtain ⟨acceleration, U, hU₃, hacceleration⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter (U₂ : Filter ℕ)
      accelerationApprox haccelerationBounded
  have hu := hu₁.mono_left (hU₃.trans hU₂)
  have hvelocity := hvelocity₂.mono_left hU₃
  have hsolution := of_projected_galerkin_weak_limits hab hBmeas MB hMB hBbound P hP
    (hU₃.trans (hU₂.trans hU₁)) uApprox velocityApprox accelerationApprox hu hvelocity hacceleration
    Ru (fun n ↦ hRu _ (Set.mem_range_self n)) hdisplacementApprox hvelocityApprox hprojected
  exact ⟨u, velocity, acceleration, hsolution⟩

/--
Evans, §7.2.3, Theorem 5(i): abstract Galerkin form.

Assume a bounded projected Galerkin family with the same exact initial
displacement `q₀` and velocity `p₀` at every index. Suppose in addition that
estimate (52) has supplied dimension-independent essential bounds

`‖uₘ(t)‖_V ≤ Cᵤ` and `‖uₘ'(t)‖_H ≤ Cᵥ`.

Then the compactness construction produces a weak solution satisfying

`u ∈ L∞(a,b;V)` and `u_t ∈ L∞(a,b;H)`,

with the same almost-everywhere bounds.  In concrete divergence-form wave
problems, `ae_norm_displacementLp_le_of_gelfandWaveEnergy_le` and
`ae_norm_velocityLp_le_of_gelfandWaveEnergy_le` supply these two additional
hypotheses from the coercive Galerkin energy estimate.

The proof uses the same common ultrafilter for displacement, velocity, and
acceleration.  The weak-wave equations are passed to the limit exactly as
in `exists_of_bounded_projected_galerkin_family`, while
`improvedRegularity_of_weak_L2_limits` preserves the closed convex
essential norm balls.  Thus the regularity conclusion is proved rather than
stored as extra data in the definition of a weak solution.
-/
theorem exists_of_bounded_projected_galerkin_family_with_improvedRegularity [CompleteSpace V]
    [CompleteSpace H] (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (huBounded : Bornology.IsBounded (Set.range uApprox))
    (hvelocityBounded : Bornology.IsBounded (Set.range velocityApprox))
    (haccelerationBounded : Bornology.IsBounded (Set.range accelerationApprox)) (Cu Cv : ℝ)
    (huEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖uApprox n t‖ ≤ Cu)
    (hvelocityEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖velocityApprox n t‖ ≤ Cv)
    (hdisplacementApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox n t)) (uApprox n) (T.inclusion q₀))
    (hvelocityApprox : ∀ n (w : V) (τ : TimeTest a b), -(∫ t,
      inner ℝ (velocityApprox n t) (T.inclusion w) * τ.derivToLp t
      ∂(volume.restrict (Set.Ioc a b))) = (∫ t, accelerationApprox n t w *
      τ.toLp t ∂(volume.restrict (Set.Ioc a b))) + inner ℝ p₀ (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B ell (uApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖u t‖ ≤ Cu) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖velocity t‖ ≤ Cv) := by
  obtain ⟨Ru, hRu⟩ := huBounded.exists_norm_le
  obtain ⟨u, U₁, hU₁, hu₁⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter Filter.atTop uApprox
      huBounded
  obtain ⟨velocity, U₂, hU₂, hvelocity₂⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₁ : Filter ℕ)
      velocityApprox hvelocityBounded
  obtain ⟨acceleration, U, hU₃, hacceleration⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter (U₂ : Filter ℕ)
      accelerationApprox haccelerationBounded
  have hu := hu₁.mono_left (hU₃.trans hU₂)
  have hvelocity := hvelocity₂.mono_left hU₃
  have hsolution := of_projected_galerkin_weak_limits hab hBmeas MB hMB hBbound P hP
    (hU₃.trans (hU₂.trans hU₁)) uApprox velocityApprox accelerationApprox hu hvelocity hacceleration
    Ru (fun n ↦ hRu _ (Set.mem_range_self n)) hdisplacementApprox hvelocityApprox hprojected
  obtain ⟨h1, h2, h3, h4⟩ := improvedRegularity_of_weak_L2_limits uApprox velocityApprox hu
    hvelocity Cu Cv (.of_forall huEssential) (.of_forall hvelocityEssential)
  exact ⟨u, velocity, acceleration, hsolution, h1, h2, h3, h4⟩

/--
The weak displacement has a strongly continuous pivot-space representative
with the prescribed initial trace.

This is the first regularity consequence of the weak-wave definition.  It is
obtained from the already proved finite-interval Lions-Magenes theorem,
applied to the integrated equation `u_t = velocity`.  No endpoint value of
the `Lp V` representative is evaluated.
-/
theorem exists_displacementContinuousRepresentative [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∃ uH : ℝ → H, ContinuousOn uH (Set.uIcc a b) ∧ uH =ᵐ[volume.restrict (Set.uIcc a b)]
      (fun t ↦ T.inclusion (u t)) ∧ uH a = T.inclusion q₀ := by
  obtain ⟨E, hinitial⟩ := h.exists_continuousDisplacementEvolution
  exact ⟨E.representative, E.continuousOn, E.ae_eq_inclusion, hinitial⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
