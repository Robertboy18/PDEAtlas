/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.AutonomousDifferentiation
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import Mathlib.Analysis.LocallyConvex.WeakSpace
import PDE.Analysis.Evolution.Compactness.Lp.Ultrafilter
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.WeakDerivativeLimit
import PDE.Analysis.WeakCompactness
import PDE.Hyperbolic.HigherRegularity.Temporal.ThirdDerivative
import PDE.Hyperbolic.WeakWave.Compactness.ProjectedGalerkin
import PDE.Hyperbolic.WeakWave.Compactness.WeakLimits
import PDE.Hyperbolic.WeakWave.Galerkin.DifferentiatedTrajectory
import PDE.Hyperbolic.WeakWave.Galerkin.IntegratedIdentities

/-!
# Paired weak limits for differentiated Galerkin systems

Evans, §7.2.3, passes an original Galerkin wave and its differentiated
system to weak limits along one subsequence; we use one common filter. We keep the
finite-dimensional derivative links at the limit, transfer the uniform
essential bounds, and prove the resulting paired existence theorems.
These existence theorems require exact common initial data for both
families. The finite-chain construction handles convergent projected data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, steps 2 and 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

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
  {B : V →L[ℝ] StrongDual ℝ V}
  {ell ellDot : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u velocityV : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q0 : V} {p0 : H}

/--
Evans, §7.2.3, Theorem 5(ii): identification of the differentiated Galerkin limits.

Suppose one common filter gives weak limits for an original Galerkin family
and its differentiated family.  The exact finite-dimensional identities

`J (duₘ) = velocityₘ`,

`J* (dvelocityₘ) = accelerationₘ`

then survive weak convergence.  If the coefficient derivative identity
`d uₘ/dt = duₘ` is also retained in the identity Gelfand triple, the limit
`du` is the `V`-valued weak derivative of `u`.

Uniform essential bounds on `duₘ` in `V` and `dvelocityₘ` in `H` pass to the
same limits by weak closedness of the almost-everywhere norm balls.  Finally,
for an autonomous operator and weakly differentiable forcing, the theorem
constructs `u_{ttt}` in `L²(a,b;V*)`.

This is the compactness/identification step that cannot be justified by
extracting unrelated subnets for the original and differentiated systems.
-/
theorem higherRegularity_of_paired_weak_limits {ι : Type*} {l : Filter ι} [l.NeBot]
    [CompleteSpace V] {ellDot : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {du : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {dvelocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (hOriginal : IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u velocity acceleration q0 p0)
    (uApprox : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ι → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (duApprox : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (dvelocityApprox : ι → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (huWeak : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (uApprox i)) l (nhds (toWeakSpace ℝ _ u)))
    (hvelocityWeak : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (velocityApprox i)) l
      (nhds (toWeakSpace ℝ _ velocity)))
    (haccelerationWeak : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _
      (rieszFromDualLp (accelerationApprox i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp acceleration))))
    (hduWeak : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (duApprox i)) l (nhds (toWeakSpace ℝ _ du)))
    (hdvelocityWeak : Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (dvelocityApprox i)) l
      (nhds (toWeakSpace ℝ _ dvelocity)))
    (hvelocityLink : ∀ i, T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (duApprox i) =
      velocityApprox i)
    (haccelerationLink : ∀ i, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
      (dvelocityApprox i) = accelerationApprox i)
    (huDerivativeApprox : ∀ i, HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity V) (uApprox i)
      ((GelfandTriple.identity V).energyToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
      (duApprox i)))
    (Cu Cv : ℝ) (hduEssential : ∀ᶠ i in l, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖duApprox i t‖ ≤ Cu)
    (hdvelocityEssential : ∀ᶠ i in l, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖dvelocityApprox i t‖ ≤ Cv)
    (hellDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b) (fun t ↦ ell t)
      (fun t ↦ ellDot t)) :
    T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = velocity ∧
      T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) dvelocity = acceleration ∧
      PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
        (Set.Ioo a b) (fun t ↦ u t) (fun t ↦ du t) ∧
      MemLp (fun t ↦ du t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      MemLp (fun t ↦ dvelocity t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖du t‖ ≤ Cu) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖dvelocity t‖ ≤ Cv) ∧
      ∃ third : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
        PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
            (Set.Ioo a b) (fun t ↦ acceleration t) (fun t ↦ third t) ∧
          ((fun t ↦ third t) =ᵐ[volume.restrict (Set.Ioc a b)]
            fun t ↦ ellDot t - B (du t)) ∧
          ‖third‖ ≤ ‖ellDot‖ + ‖B‖ * ‖du‖ := by
  let μ := volume.restrict (Set.Ioc a b)
  let P : Lp H 2 μ →L[ℝ] Lp V 2 μ := rieszFromDualLp.comp (T.pivotToDual.compLpL 2 μ)
  let J : Lp V 2 μ →L[ℝ] Lp (StrongDual ℝ V) 2 μ :=
    (GelfandTriple.identity V).energyToDual.compLpL 2 μ
  have hriesz : rieszFromDualLp acceleration = P dvelocity := (toWeakSpace ℝ _).injective <|
    tendsto_nhds_unique haccelerationWeak <|
      (((WeakSpace.map P).continuous.tendsto _).comp hdvelocityWeak).congr fun i ↦
        congrArg (fun z ↦ toWeakSpace ℝ _ (rieszFromDualLp z)) (haccelerationLink i)
  have huDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
      (Set.Ioo a b) (fun t ↦ u t) (fun t ↦ du t) := by
    simpa only [J, μ] using (hasGelfandWeakTimeDerivativeOn_of_weak_limits
      (GelfandTriple.identity V) uApprox (fun i ↦ J (duApprox i)) u (J du) huWeak
      (((WeakSpace.map (rieszFromDualLp.comp J)).continuous.tendsto _).comp hduWeak)
      huDerivativeApprox).identity_hasWeakTimeDerivativeOn
  obtain ⟨h1, h2, h3, h4⟩ := improvedRegularity_of_weak_L2_limits duApprox dvelocityApprox
    hduWeak hdvelocityWeak Cu Cv hduEssential hdvelocityEssential
  refine ⟨compLpL_eq_of_tendsto_weak T.inclusion duApprox velocityApprox du velocity hduWeak
    hvelocityWeak hvelocityLink, ?_, huDerivative, h1, h2, h3, h4,
    hOriginal.exists_thirdTimeDerivative_of_autonomous huDerivative hellDerivative⟩
  rw [← rieszToDualLp_rieszFromDualLp acceleration, hriesz]
  exact (rieszToDualLp_rieszFromDualLp _).symm

/--
Evans, §7.2.3, Theorem 5(ii): abstract Galerkin existence form with exact
common initial data.

This theorem combines the higher-regularity compactness argument for paired
families with exact common initial data.
The original and time-differentiated projected Galerkin families are assumed
bounded in their natural three Bochner spaces.  Their exact derivative links
are retained at every Galerkin level, and the differentiated energy estimate
provides common essential bounds for `duApprox` and `dvelocityApprox`.
Both integrated initial identities use the same `q0, p0` for the original
family and the same `dq0, dp0` for its derivative at every index. Convergence
of projected initial values alone does not meet these hypotheses; that case is
handled by the finite-chain theorems
`GelfandGalerkin.exists_finiteWeakWaveChain_of_compatibleData`
(`HigherRegularity.Galerkin.FiniteChain`) and its nonsymmetric variant in
`HigherRegularity.Galerkin.Nonsymmetric`.

One six-way ultrafilter refining `atTop` is selected internally.  Both
projected systems pass to ambient weak-wave equations along that
same filter.  The cross-identities therefore survive, the differentiated
displacement is identified as the `V`-valued weak derivative of the original
solution, and the essential bounds pass to the limits.  If the forcing has
weak derivative `ellDot`, the result also constructs
`u_{ttt} = ellDot - B u_t` in `L²(a,b;V*)`.

In the concrete Dirichlet wave equation, take
`V = H¹₀(Omega)`, `H = L²(Omega)`.  Combining the returned
`u_{tt} ∈ L∞_t H` bound with an `L∞_t H` forcing bound and the coefficient
and boundary-atlas hypotheses of
`DivergenceFormWave.exists_spatialH2Top_of_ae_weak_wave` gives
`u ∈ L∞_t H²_x`.
-/
theorem exists_of_bounded_paired_projected_galerkin_families [CompleteSpace V] [CompleteSpace H]
    (hab : a < b) (hBmeas : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc a b)))
    (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖(fun _ : ℝ ↦ B) t‖ ≤ MB)
    {Sseq : ℕ → Submodule ℝ V} {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {dq0 : V} {dp0 : H} (ellDot : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (uApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (duApprox : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (dvelocityApprox : ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (daccelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (huBounded : Bornology.IsBounded (Set.range uApprox))
    (hvelocityBounded : Bornology.IsBounded (Set.range velocityApprox))
    (haccelerationBounded : Bornology.IsBounded (Set.range accelerationApprox))
    (hduBounded : Bornology.IsBounded (Set.range duApprox))
    (hdvelocityBounded : Bornology.IsBounded (Set.range dvelocityApprox))
    (hdaccelerationBounded : Bornology.IsBounded (Set.range daccelerationApprox)) (Ru Rdu : ℝ)
    (huNorm : ∀ n, ‖uApprox n‖ ≤ Ru) (hduNorm : ∀ n, ‖duApprox n‖ ≤ Rdu)
    (hdisplacementApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox n t)) (uApprox n) (T.inclusion q0))
    (hvelocityApprox : ∀ n (w : V) (τ : TimeTest a b), -(∫ t,
      inner ℝ (velocityApprox n t) (T.inclusion w) * τ.derivToLp t
      ∂(volume.restrict (Set.Ioc a b))) = (∫ t, accelerationApprox n t w *
      τ.toLp t ∂(volume.restrict (Set.Ioc a b))) + inner ℝ p0 (T.inclusion w) * τ.toFun a)
    (hprojectedApprox : ∀ n, accelerationApprox n = (SecondOrderSolutionOn.projectedDual
      (P n)).compLpL 2 (volume.restrict (Set.Ioc a b)) (gelfandResidualLp (fun _ ↦ B) ell
      (uApprox n) (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound))
    (hdisplacementDerivativeApprox : ∀ n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (dvelocityApprox n t)) (duApprox n) (T.inclusion dq0))
    (hvelocityDerivativeApprox : ∀ n (w : V) (τ : TimeTest a b),
      -(∫ t, inner ℝ (dvelocityApprox n t) (T.inclusion w) *
      τ.derivToLp t ∂(volume.restrict (Set.Ioc a b))) = (∫ t,
      daccelerationApprox n t w * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
      inner ℝ dp0 (T.inclusion w) * τ.toFun a)
    (hprojectedDerivativeApprox : ∀ n, daccelerationApprox n =
      (SecondOrderSolutionOn.projectedDual (P n)).compLpL 2 (volume.restrict (Set.Ioc a b))
      (gelfandResidualLp (fun _ ↦ B) ellDot (duApprox n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound))
    (hvelocityLink : ∀ n, T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (duApprox n) =
      velocityApprox n)
    (haccelerationLink : ∀ n, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
      (dvelocityApprox n) = accelerationApprox n)
    (huDerivativeApprox : ∀ n, HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity V) (uApprox n)
      ((GelfandTriple.identity V).energyToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
      (duApprox n)))
    (Cu Cv : ℝ) (hduEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖duApprox n t‖ ≤ Cu)
    (hdvelocityEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖dvelocityApprox n t‖ ≤ Cv)
    (hellDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b) (fun t ↦ ell t)
      (fun t ↦ ellDot t)) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (dvelocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (dacceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u velocity acceleration q0 p0 ∧
        IsGelfandWeakWaveSolution T (fun _ ↦ B) ellDot du dvelocity dacceleration dq0 dp0 ∧
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = velocity ∧
        T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) dvelocity = acceleration ∧
        PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
          (Set.Ioo a b) (fun t ↦ u t) (fun t ↦ du t) ∧
        MemLp (fun t ↦ du t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        MemLp (fun t ↦ dvelocity t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖du t‖ ≤ Cu) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖dvelocity t‖ ≤ Cv) ∧
        ∃ third : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
          PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
              (Set.Ioo a b) (fun t ↦ acceleration t) (fun t ↦ third t) ∧
            ((fun t ↦ third t) =ᵐ[volume.restrict (Set.Ioc a b)]
              fun t ↦ ellDot t - B (du t)) ∧
            ‖third‖ ≤ ‖ellDot‖ + ‖B‖ * ‖du‖ := by
  open WeakCompactness in
  obtain ⟨u, U₁, hU₁, hu⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter .atTop uApprox huBounded
  obtain ⟨velocity, U₂, hU₂, hvelocity⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₁ : Filter ℕ) velocityApprox
      hvelocityBounded
  obtain ⟨acceleration, U₃, hU₃, hacceleration⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter (U₂ : Filter ℕ)
      accelerationApprox haccelerationBounded
  obtain ⟨du, U₄, hU₄, hdu⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₃ : Filter ℕ) duApprox hduBounded
  obtain ⟨dvelocity, U₅, hU₅, hdvelocity⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₄ : Filter ℕ) dvelocityApprox
      hdvelocityBounded
  obtain ⟨dacceleration, U, hU₆, hdaccelerationWeak⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter (U₅ : Filter ℕ)
      daccelerationApprox hdaccelerationBounded
  have h₅ := hU₆.trans hU₅
  have h₄ := h₅.trans hU₄
  have h₃ := h₄.trans hU₃
  have h₂ := h₃.trans hU₂
  have hU : (U : Filter ℕ) ≤ Filter.atTop := h₂.trans hU₁
  have hOriginal := of_projected_galerkin_weak_limits hab hBmeas MB hMB hBbound P hP hU
    uApprox velocityApprox accelerationApprox (hu.mono_left h₂) (hvelocity.mono_left h₃)
    (hacceleration.mono_left h₄) Ru huNorm hdisplacementApprox hvelocityApprox hprojectedApprox
  exact ⟨u, velocity, acceleration, du, dvelocity, dacceleration, hOriginal,
    of_projected_galerkin_weak_limits hab hBmeas MB hMB hBbound P hP hU duApprox
      dvelocityApprox daccelerationApprox (hdu.mono_left h₅) (hdvelocity.mono_left hU₆)
      hdaccelerationWeak Rdu hduNorm hdisplacementDerivativeApprox hvelocityDerivativeApprox
      hprojectedDerivativeApprox,
    higherRegularity_of_paired_weak_limits hOriginal uApprox velocityApprox accelerationApprox
      duApprox dvelocityApprox (hu.mono_left h₂) (hvelocity.mono_left h₃)
      (hacceleration.mono_left h₄) (hdu.mono_left h₅) (hdvelocity.mono_left hU₆) hvelocityLink
      haccelerationLink huDerivativeApprox Cu Cv (.of_forall hduEssential)
      (.of_forall hdvelocityEssential) hellDerivative⟩

/--
Evans, §7.2.3, Theorem 5(ii): autonomous Galerkin trajectories with exact
common initial data.

An autonomous Galerkin trajectory and its differentiated trajectory provide
all six approximation families required by
`exists_of_bounded_paired_projected_galerkin_families`.  The finite-dimensional
identities identify the differentiated displacement with the original
velocity, the differentiated pivot velocity with the original acceleration,
and the differentiated displacement as the energy-valued weak time
derivative of the original displacement.

The hypotheses are the forcing representatives, projection and convergence
data, exact common initial values, and uniform Galerkin bounds. In particular,
`hq0` and `hp0` require `(q0Approx n : V) = q0` and
`(p0Approx n : V) = dq0` at every index, so both `q0` and `dq0` lie in every
trial space. The initial differentiated pivot velocity is also fixed by
`hdp0`; convergent projections do not replace these exact equalities.
The canonical Bochner realizations supply the weak time identities,
projected residual equations, and all three cross-identities.
-/
theorem exists_of_bounded_autonomous_paired_galerkin_family [CompleteSpace V] [CompleteSpace H]
    (hBmeas : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc a b))) (MB : ℝ)
    (hMB : 0 ≤ MB) (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖(fun _ : ℝ ↦ B) t‖ ≤ MB)
    {Sseq : ℕ → Submodule ℝ V} [∀ n, FiniteDimensional ℝ (Sseq n)]
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    (forcing forcingDot : ℝ → StrongDual ℝ V)
    (hforcingAC : AbsolutelyContinuousOnInterval forcing a b)
    (hforcingDeriv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt forcing (forcingDot t) t)
    (hEll : (ell : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] forcing)
    (hEllDot : (ellDot : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] forcingDot) {dq0 : V}
    {dp0 : H} (q0Approx p0Approx : ∀ n, Sseq n)
    (U : ∀ n, SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T (Sseq n) B)
      (gelfandGalerkinForcing T (Sseq n) forcing) a b (q0Approx n) (p0Approx n))
    (hq0 : ∀ n, (q0Approx n : V) = q0) (hp0 : ∀ n, (p0Approx n : V) = dq0)
    (hp0Pivot : T.inclusion dq0 = p0)
    (hdp0 : ∀ n, T.inclusion ((-(gelfandGalerkinOperator T (Sseq n) B) (q0Approx n) +
      gelfandGalerkinForcing T (Sseq n) forcing a : Sseq n) : V) = dp0)
    (hab : a < b) (huBounded : Bornology.IsBounded (Set.range fun n ↦ (U n).displacementLp hab.le))
    (hvelocityBounded : Bornology.IsBounded (Set.range fun n ↦ (U n).velocityLp hab.le))
    (haccelerationBounded : Bornology.IsBounded
      (Set.range fun n ↦ (U n).accelerationLp (P n) hab.le ell hBmeas hBbound))
    (hduBounded : Bornology.IsBounded (Set.range fun n ↦ (GelfandGalerkin.timeDerivative T (Sseq n)
      B (U n) hforcingAC hforcingDeriv).displacementLp hab.le))
    (hdvelocityBounded : Bornology.IsBounded (Set.range fun n ↦
      (GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC hforcingDeriv).velocityLp
      hab.le))
    (hdaccelerationBounded : Bornology.IsBounded (Set.range fun n ↦
      (GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC hforcingDeriv).accelerationLp
      (P n) hab.le ellDot hBmeas hBbound))
    (Ru Rdu : ℝ) (huNorm : ∀ n, ‖(U n).displacementLp hab.le‖ ≤ Ru)
    (hduNorm : ∀ n, ‖(GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC
      hforcingDeriv).displacementLp hab.le‖ ≤ Rdu)
    (Cu Cv : ℝ)
    (hduEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC hforcingDeriv).displacementLp
      hab.le t‖ ≤ Cu)
    (hdvelocityEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC hforcingDeriv).velocityLp
      hab.le t‖ ≤ Cv)
    (hellDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b) (fun t ↦ ell t)
      (fun t ↦ ellDot t)) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (dvelocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (dacceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u velocity acceleration q0 p0 ∧
        IsGelfandWeakWaveSolution T (fun _ ↦ B) ellDot du dvelocity dacceleration dq0 dp0 ∧
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = velocity ∧
        T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) dvelocity = acceleration ∧
        PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
          (Set.Ioo a b) (fun t ↦ u t) (fun t ↦ du t) ∧
        MemLp (fun t ↦ du t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        MemLp (fun t ↦ dvelocity t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖du t‖ ≤ Cu) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖dvelocity t‖ ≤ Cv) ∧
        ∃ third : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
          PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
              (Set.Ioo a b) (fun t ↦ acceleration t) (fun t ↦ third t) ∧
            ((fun t ↦ third t) =ᵐ[volume.restrict (Set.Ioc a b)]
              fun t ↦ ellDot t - B (du t)) ∧
            ‖third‖ ≤ ‖ellDot‖ + ‖B‖ * ‖du‖ := by
  have hAC (n : ℕ) : AbsolutelyContinuousOnInterval
      (gelfandGalerkinForcing T (Sseq n) forcing) a b := by
    simpa only [Function.comp_apply, gelfandGalerkinForcing,
      gelfandGalerkinForcingMap_apply] using! (gelfandGalerkinForcingMap T
        (Sseq n)).lipschitzWith.comp_absolutelyContinuousOnInterval hforcingAC
  have hderiv (n : ℕ) : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt
      (gelfandGalerkinForcing T (Sseq n) forcing)
      (gelfandGalerkinForcing T (Sseq n) forcingDot t) t := by
    filter_upwards [hforcingDeriv] with t ht
    simpa only [gelfandGalerkinForcing, gelfandGalerkinForcingMap_apply] using!
      (gelfandGalerkinForcingMap T (Sseq n)).hasFDerivAt.comp_hasDerivAt t ht
  let D n := GelfandGalerkin.timeDerivative T (Sseq n) B (U n) hforcingAC hforcingDeriv
  exact exists_of_bounded_paired_projected_galerkin_families (dq0 := dq0) (dp0 := dp0)
    hab hBmeas MB hMB hBbound P hP ellDot _ _ _ _ _ _
    huBounded hvelocityBounded haccelerationBounded hduBounded hdvelocityBounded
    hdaccelerationBounded Ru Rdu huNorm hduNorm
    (fun n ↦ by simpa only [hq0 n] using (U n).displacementIdentity hab)
    (fun n w τ ↦ by
      simpa only [hp0 n, hp0Pivot] using (U n).velocityIdentity (P n) hab.le ell hEll hBmeas
        hBbound w τ) (fun _ ↦ rfl)
    (fun n ↦ by
      simpa only [D, GelfandGalerkin.timeDerivative, hp0 n] using (D n).displacementIdentity hab)
    (fun n w τ ↦ by
      simpa only [D, GelfandGalerkin.timeDerivative, hdp0 n] using (D n).velocityIdentity (P n)
        hab.le ellDot hEllDot hBmeas hBbound w τ) (fun _ ↦ rfl)
    (fun n ↦ by
      simpa only [GelfandGalerkin.timeDerivative] using
        (U n).inclusion_compLpL_timeDerivative_displacementLp hab.le (hAC n) (hderiv n))
    (fun n ↦ by
      simpa only [GelfandGalerkin.timeDerivative] using
        (U n).pivotToDual_compLpL_timeDerivative_velocityLp (P n) hab.le ell hEll hBmeas
          hBbound (hAC n) (hderiv n))
    (fun n ↦ by
      simpa only [GelfandGalerkin.timeDerivative] using
        (U n).hasIdentityGelfandWeakTimeDerivativeOn_timeDerivative_displacementLp hab.le
          (hAC n) (hderiv n)) Cu Cv hduEssential hdvelocityEssential hellDerivative

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
