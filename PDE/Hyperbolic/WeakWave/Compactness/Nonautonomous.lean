/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Nonautonomous
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PDE.Analysis.Evolution.Galerkin.Spectral
import PDE.Analysis.WeakCompactness
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Hyperbolic.WeakWave.Galerkin.EnergyBounds
import PDE.Hyperbolic.WeakWave.Galerkin.IntegratedIdentities
import PDE.Hyperbolic.WeakWave.Compactness.ProjectedGalerkin
import PDE.Hyperbolic.WeakWave.Compactness.WeakLimits

/-!
# Weak nonautonomous waves from square-integrable pivot forcing

Existence of a weak solution of the abstract second-order hyperbolic equation
`u'' + (A(t) + R(t)) u = J* f`, `u(a) = q₀`, `u'(a) = p₀` on a Gelfand triple `V ↪ H ↪ V*` with
compact inclusion, for forcing `f ∈ L²(a, b; H)` and arbitrary data `q₀ ∈ V`, `p₀ ∈ H`. The
principal form `A` is symmetric, coercive and absolutely continuous in time, with a one-sided
quadratic bound on its derivative. The lower-order form `R` has the `V × H` bound used in the
energy inequality, and the full operator is strongly measurable almost everywhere and uniformly
bounded on the closed time interval. The solution has `u ∈ L∞(V)` and `u' ∈ L∞(H)`.

## Main results

* `exists_uniform_energy_bound_of_compact_inclusion`: one constant `M`, chosen before the forcing
  and the data, such that every `f`, `q₀`, `p₀` has a weak solution with
  `‖u(t)‖ + ‖u'(t)‖ ≤ M (‖f‖ + ‖q₀‖ + ‖p₀‖)` almost everywhere.
* `exists_of_compact_inclusion_of_pivot_forcing`: the existence statement alone, with
  `u ∈ L∞(V)` and `u' ∈ L∞(H)`.

## How it works

This is Evans's Galerkin proof in abstract form. The spectral trial system of the compact
inclusion (`gramSpectralGalerkinSystem`) gives uniformly energy-stable, pivot-orthogonal
projections, and projecting `q₀` and `p₀` gives a common initial-energy bound and convergent
initial values. The finite-dimensional energy construction supplies the trajectories, whose
displacement, velocity and dual acceleration are bounded in the three Bochner `L²` spaces. We
refine one ultrafilter so that all three weak limits exist along it; then
`of_projected_galerkin_weak_limits_of_initial_tendsto` passes both time identities and the
spatial equation to the limit, and `improvedRegularity_of_weak_L2_limits` (closed convex
essential norm balls) gives the `L∞` bounds for that same weak solution. The existence theorems
take no approximation or limit as a hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorems 1-3, and §7.2.3, Theorem 5(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace Hyperbolic.Variational

open PDE.Analysis PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace IsGelfandWeakWaveSolution

variable [CompleteSpace V] [CompleteSpace H]

/-- Uniform energy of Galerkin trajectories bounds their three Bochner classes.
One common ultrafilter then gives a weak wave with the limits of both projected initial
values. The two time identities and the projected residual are derived from the trajectories. -/
private theorem exists_of_projected_trajectories_with_energy_bound
    (T : GelfandTriple (V := V) (H := H)) {Sseq : ℕ → Submodule ℝ V}
    [∀ m, FiniteDimensional ℝ (Sseq m)] {K : NNReal}
    (P : ∀ m, StableTrialProjection T (Sseq m) K)
    (hP : ∀ v : V, Filter.Tendsto (fun m ↦ ((P m).energyProjection v : V)) Filter.atTop (nhds v))
    (A R : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V) {a b : ℝ} (hab : a < b) (q₀ : V)
    (p₀ : H)
    (hp₀ : Filter.Tendsto (fun m ↦ T.inclusion ((P m).projection p₀ : V)) Filter.atTop (nhds p₀))
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)] ell)
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t) (volume.restrict (Ioc a b))) (MB : ℝ)
    (hMB : 0 ≤ MB) (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖A t + R t‖ ≤ MB) (c C : ℝ)
    (hc : 0 < c) (hcoercive : ∀ t ∈ Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (U : ∀ m, SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T (Sseq m) (A t + R t))
      (gelfandGalerkinForcing T (Sseq m) ell) a b ((P m).energyProjection q₀) ((P m).projection p₀))
    (henergy : ∀ m t, t ∈ Icc a b →
      gelfandWaveEnergy T (Sseq m) A (U m).displacement (U m).velocity t ≤ C) :
    ∃ (u : Lp V 2 (volume.restrict (Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      IsGelfandWeakWaveSolution T (fun t ↦ A t + R t)
          ellLp u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ‖u t‖ ≤ Real.sqrt ((2 / c) * C)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ‖velocity t‖ ≤ Real.sqrt (2 * C)) := by
  let μab := volume.restrict (Ioc a b)
  let uApprox : ℕ → Lp V 2 μab := fun m ↦ (U m).displacementLp hab.le
  let velocityApprox : ℕ → Lp H 2 μab := fun m ↦ (U m).velocityLp hab.le
  let accelerationApprox : ℕ → Lp (StrongDual ℝ V) 2 μab := fun m ↦
    (U m).accelerationLp (P m) hab.le ellLp hBmeas hBbound
  let Ru : ℝ := Real.sqrt (((2 / c) * C) * (b - a))
  let Rv : ℝ := Real.sqrt ((2 * C) * (b - a))
  have hco (m : ℕ) : ∀ t ∈ Icc a b, c * ‖((U m).displacement t : V)‖ ^ 2 ≤
      A t ((U m).displacement t : V) ((U m).displacement t : V) := fun t ht ↦ hcoercive t ht _
  have huR (m : ℕ) : ‖uApprox m‖ ≤ Ru := Real.le_sqrt_of_sq_le
    ((U m).norm_displacementLp_sq_le_of_gelfandWaveEnergy_le hab.le hc (hco m) (henergy m))
  have haR (m : ℕ) : ‖accelerationApprox m‖ ≤ (K : ℝ) * (‖ellLp‖ + MB * Ru) :=
    ((U m).norm_accelerationLp_le_stable (P m) hab.le ellLp hBmeas hMB hBbound).trans
      (by gcongr; exact huR m)
  -- Each refinement preserves the limits already extracted. No subsequence is presumed.
  obtain ⟨u, U₁, hU₁, hu₁⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter Filter.atTop
      uApprox (isBounded_iff_forall_norm_le.mpr ⟨Ru, forall_mem_range.2 huR⟩)
  obtain ⟨velocity, U₂, hU₂, hv₂⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₁ : Filter ℕ)
      velocityApprox (isBounded_iff_forall_norm_le.mpr ⟨Rv, forall_mem_range.2 fun m ↦
        Real.le_sqrt_of_sq_le ((U m).norm_velocityLp_sq_le_of_gelfandWaveEnergy_le hab.le hc
          (hco m) (henergy m))⟩)
  obtain ⟨acceleration, ultrafilter, hU₃, ha⟩ :=
    exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter (U₂ : Filter ℕ)
      accelerationApprox (isBounded_iff_forall_norm_le.mpr ⟨_, forall_mem_range.2 haR⟩)
  have hu := hu₁.mono_left (hU₃.trans hU₂)
  have hv := hv₂.mono_left hU₃
  -- Closed convex essential norm balls are preserved by this same weak limit.
  exact ⟨u, velocity, acceleration, of_projected_galerkin_weak_limits_of_initial_tendsto hab
    hBmeas MB hMB hBbound P hP (hU₃.trans (hU₂.trans hU₁)) uApprox velocityApprox
    accelerationApprox hu hv ha Ru huR (fun m ↦ ((P m).energyProjection q₀ : V))
    (fun m ↦ T.inclusion ((P m).projection p₀ : V)) (hP q₀) hp₀
    (fun m ↦ (U m).displacementIdentity hab)
    (fun m w τ ↦ (U m).velocityIdentity (P m) hab.le ellLp hEll hBmeas hBbound w τ)
    (fun _ ↦ rfl), improvedRegularity_of_weak_L2_limits uApprox velocityApprox hu hv
      (Real.sqrt ((2 / c) * C)) (Real.sqrt (2 * C))
      (.of_forall fun m ↦ (U m).ae_norm_displacementLp_le_of_gelfandWaveEnergy_le hab.le hc
        (hco m) (henergy m))
      (.of_forall fun m ↦ (U m).ae_norm_velocityLp_le_of_gelfandWaveEnergy_le hab.le hc
        (hco m) (henergy m))⟩

/-- Compactness of the Gelfand inclusion and natural `L²(H)` forcing construct a
nonautonomous weak wave with arbitrary energy-space displacement and pivot-space velocity.
One constant, chosen before the forcing and initial values, controls the sum of the
`L∞(V)` displacement norm and `L∞(H)` velocity norm by the natural data norms.
Both initial values occur in the integrated identities of the weak solution.

Only the principal form is symmetric. Its time derivative has a one-sided quadratic bound,
and the lower-order form satisfies the `V × H` energy estimate. Stable trial spaces, finite
trajectories, uniform bounds, and a common weak limit are all constructed in the proof. -/
theorem exists_uniform_energy_bound_of_compact_inclusion
    (T : GelfandTriple (V := V) (H := H))
    (hcompact : IsCompactOperator T.inclusion)
    (A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b : ℝ} (hab : a < b)
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Ioc a b)))
    (MB : NNReal) (hBbound : ∀ t ∈ Icc a b, ‖A t + R t‖ ≤ MB)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Icc a b, ∀ x y : V, A t x y = A t y x)
    (c LR LA : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA)
    (hcoercive : ∀ t ∈ Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ x y : V, |R t x y| ≤ LR * ‖x‖ * ‖T.inclusion y‖)
    (hAdotBound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ x : V, Adot t x x ≤ LA * ‖x‖ ^ 2)
    : ∃ M : ℝ, 0 < M ∧
      ∀ (f : Lp H 2 (volume.restrict (Ioc a b))) (q₀ : V) (p₀ : H),
    ∃ (u : Lp V 2 (volume.restrict (Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      IsGelfandWeakWaveSolution T (fun t ↦ A t + R t)
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
          u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) ∧
        ∀ᵐ t ∂volume.restrict (Ioc a b),
          ‖u t‖ + ‖velocity t‖ ≤ M * (‖f‖ + ‖q₀‖ + ‖p₀‖) := by
  classical
  let trials : StableTrialSystem T := gramSpectralGalerkinSystem T hcompact
  let Sseq : ℕ → Submodule ℝ V := trials.space
  let : ∀ m, FiniteDimensional ℝ (Sseq m) := trials.finiteDimensional
  let : ∀ m, CompleteSpace (Sseq m) := fun m ↦ FiniteDimensional.complete ℝ (Sseq m)
  let P : ∀ m, StableTrialProjection T (Sseq m) trials.stabilityConstant := trials.projection
  let K : NNReal := trials.stabilityConstant
  let D : ℝ := 2 + (LR ^ 2 + LA) / c
  let F : ℝ := (1 + ‖A a‖ * (K : ℝ) ^ 2) * Real.exp (D * (b - a))
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨Real.sqrt ((2 / c) * F) + Real.sqrt (2 * F) + 1, by positivity, fun f q₀ p₀ ↦ ?_⟩
  let S : ℝ := ‖f‖ + ‖q₀‖ + ‖p₀‖
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let initialEnergy : ℕ → ℝ := fun m ↦ (1 / 2 : ℝ) * ‖T.inclusion ((P m).projection p₀ : V)‖ ^ 2 +
      (1 / 2 : ℝ) * A a ((P m).energyProjection q₀ : V) ((P m).energyProjection q₀ : V)
  let C₀ : ℝ := (1 / 2 : ℝ) * ‖p₀‖ ^ 2 + (1 / 2 : ℝ) * ‖A a‖ * ((K : ℝ) * ‖q₀‖) ^ 2
  let budget : ℝ := C₀ + (1 / 2 : ℝ) * ∫ s in a..b, ‖f s‖ ^ 2
  let C : ℝ := budget * Real.exp (D * (b - a))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hbudget : 0 ≤ budget := by
    have hforce : 0 ≤ ∫ s in a..b, ‖f s‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab.le (fun s ↦ sq_nonneg ‖f s‖)
    dsimp only [budget, C₀]
    positivity
  have hinitial (m : ℕ) : initialEnergy m ≤ C₀ :=
    GelfandGalerkin.projected_initial_energy_le T (P m) (A a) q₀ p₀
  -- Existence is applied at each projected pair of initial values, with the same coefficients.
  have hfinite (m : ℕ) : ∃ U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T (Sseq m) (A t + R t))
      (gelfandGalerkinForcing T (Sseq m) (fun t ↦ T.pivotToDual (f t))) a b
      ((P m).energyProjection q₀) ((P m).projection p₀), ∀ t ∈ Icc a b,
        gelfandWaveEnergy T (Sseq m) A U.displacement U.velocity t ≤
          (initialEnergy m + (1 / 2 : ℝ) * ∫ s in a..b, ‖f s‖ ^ 2) * Real.exp (D * (t - a)) :=
    GelfandGalerkin.exists_with_energy_bound_of_memLp T (Sseq m) A R Adot f
      hab.le (Lp.memLp f) hBmeas MB hBbound hAAC hAderiv hAsymm c LR LA hc hLA
      hcoercive hRbound hAdotBound ((P m).energyProjection q₀) ((P m).projection p₀)
  choose U hU using hfinite
  have henergy (m : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      gelfandWaveEnergy T (Sseq m) A (U m).displacement (U m).velocity t ≤ C :=
    (hU m t ht).trans (mul_le_mul (add_le_add (hinitial m) le_rfl) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hD)) (Real.exp_pos _).le hbudget)
  have hP : ∀ v : V, Filter.Tendsto
      (fun m ↦ ((P m).energyProjection v : V)) Filter.atTop (nhds v) :=
    StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P trials.denseEnergy
  have hp : Filter.Tendsto (fun m ↦ T.inclusion ((P m).projection p₀ : V)) Filter.atTop (nhds p₀) :=
    StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable
      P trials.densePivot p₀
  let ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)) :=
    T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  have hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ T.pivotToDual (f t)) := T.pivotToDual.coeFn_compLpL f
  have hBboundAE : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖A t + R t‖ ≤ (MB : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hBbound t (Ioc_subset_Icc_self ht)
  obtain ⟨u, velocity, acceleration, hsol, hu, hv, hub, hvb⟩ :=
    exists_of_projected_trajectories_with_energy_bound T P hP A R
      (fun t ↦ T.pivotToDual (f t)) hab q₀ p₀ hp ellLp hEll hBmeas MB MB.coe_nonneg
      hBboundAE c C hc hcoercive U henergy
  have hforce : (∫ s in a..b, ‖f s‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le, Lp.norm_sq_eq_integral_norm_sq]
  have hf₀ := norm_nonneg f
  have hq₀ := norm_nonneg q₀
  have hp₀ := norm_nonneg p₀
  have hfS : ‖f‖ ^ 2 ≤ S ^ 2 := by dsimp only [S]; nlinarith
  have hqS : ‖q₀‖ ^ 2 ≤ S ^ 2 := by dsimp only [S]; nlinarith
  have hpS : ‖p₀‖ ^ 2 ≤ S ^ 2 := by dsimp only [S]; nlinarith
  have hbudgetBound : budget ≤ (1 + ‖A a‖ * (K : ℝ) ^ 2) * S ^ 2 := by
    dsimp only [budget, C₀]
    rw [hforce]
    nlinarith [mul_nonneg (norm_nonneg (A a)) (sq_nonneg (K : ℝ)), mul_le_mul_of_nonneg_left hqS
        (mul_nonneg (norm_nonneg (A a)) (sq_nonneg (K : ℝ)))]
  have hCF : C ≤ F * S ^ 2 := by
    simpa only [C, F, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hbudgetBound (Real.exp_pos (D * (b - a))).le
  have huS : Real.sqrt ((2 / c) * C) ≤ Real.sqrt ((2 / c) * F) * S := by
    calc
      _ ≤ Real.sqrt (((2 / c) * F) * S ^ 2) :=
        Real.sqrt_le_sqrt (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hCF
            (show 0 ≤ 2 / c by positivity))
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hS]
  have hvS : Real.sqrt (2 * C) ≤ Real.sqrt (2 * F) * S := by
    calc
      _ ≤ Real.sqrt ((2 * F) * S ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hCF])
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hS]
  refine ⟨u, velocity, acceleration, hsol, hu, hv, ?_⟩
  filter_upwards [hub, hvb] with t hut hvt
  change ‖u t‖ + ‖velocity t‖ ≤ _ * S
  nlinarith only [hut.trans huS, hvt.trans hvS, hS]


/-- Compactness of the Gelfand inclusion and natural `L²(H)` forcing construct a
nonautonomous weak wave with arbitrary energy-space displacement and pivot-space velocity.
The displacement belongs to `L∞(V)` and the velocity to `L∞(H)`; the acceleration lies in
`L²(V*)`. Both initial values occur in the integrated identities of the weak solution.

Only the principal form is symmetric. Its time derivative has a one-sided quadratic bound,
and the lower-order form satisfies the `V × H` energy estimate. Stable trial spaces, finite
trajectories, uniform bounds, and a common weak limit are all constructed in the proof. -/
theorem exists_of_compact_inclusion_of_pivot_forcing (T : GelfandTriple (V := V) (H := H))
    (hcompact : IsCompactOperator T.inclusion) (A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ}
    (hab : a < b) (f : Lp H 2 (volume.restrict (Ioc a b)))
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t) (volume.restrict (Ioc a b))) (MB : NNReal)
    (hBbound : ∀ t ∈ Icc a b, ‖A t + R t‖ ≤ MB) (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Icc a b, ∀ x y : V, A t x y = A t y x) (c LR LA : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA)
    (hcoercive : ∀ t ∈ Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x y : V, |R t x y| ≤ LR * ‖x‖ * ‖T.inclusion y‖)
    (hAdotBound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x : V, Adot t x x ≤ LA * ‖x‖ ^ 2) (q₀ : V)
    (p₀ : H) :
    ∃ (u : Lp V 2 (volume.restrict (Ioc a b)))
        (velocity : Lp H 2 (volume.restrict (Ioc a b)))
        (acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      IsGelfandWeakWaveSolution T (fun t ↦ A t + R t)
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
          u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) (⊤ : ENNReal) (volume.restrict (Ioc a b)) := by
  obtain ⟨M, _, hM⟩ := exists_uniform_energy_bound_of_compact_inclusion
    T hcompact A R Adot hab hBmeas MB hBbound hAAC hAderiv hAsymm c LR LA
    hc hLA hcoercive hRbound hAdotBound
  obtain ⟨u, v, w, hsol, hu, hv, _⟩ := hM f q₀ p₀
  exact ⟨u, v, w, hsol, hu, hv⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
