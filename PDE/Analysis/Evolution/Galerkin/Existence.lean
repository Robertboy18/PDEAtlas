/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.Lp.Galerkin
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.TimeDistribution
import PDE.Analysis.Evolution.Integrated.Uniqueness
import PDE.Analysis.Evolution.Integrated.WeakLimit
import PDE.Analysis.WeakCompactness
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Galerkin existence for integrated weak evolution

Let `V ↪ H` be a Gelfand triple and let `B(t) : V → V*` be continuous and bounded on
`[a, b]` and uniformly coercive, `C ‖w‖² ≤ B(t)(w, w)`. Take trial spaces with uniformly
energy-stable pivot-orthogonal projections, eventually dense in `V` (hence in `H`). For a
continuous bounded load `ℓ`, the Galerkin approximations started at the projections of
`u₀ ∈ H` are bounded in `L²(a, b; V)`. Along an ultrafilter they converge weakly, and the
integrated projected identities pass to the limit, so the limit is an integrated weak solution
with initial value `u₀`. It is unique, and it has a continuous pivot representative with the
coercive energy estimate. Density of bounded continuous loads in `L²(a, b; V*)` and coercive
continuous dependence then give existence and uniqueness for every load in `L²(a, b; V*)`.

For a Hilbert space `E`, a weak `L²` limit of integrated weak solutions with convergent
initial data is again an integrated weak solution.

## How it works

We follow the Galerkin proof of Evans (§7.1.2, Theorems 1 to 3), with an abstract Gelfand
triple in place of `H¹₀ ⊂ L² ⊂ H⁻¹`. `GelfandGalerkinApproximation.exists_nonauto_sequence_on_Icc`
solves the finite-dimensional problems, and `GelfandGalerkinApproximation.norm_trajectoryLp_sq_le`
bounds the trajectories in `L²(a, b; V)` uniformly in the dimension. Where Evans extracts a
weakly convergent subsequence, we take a weak limit along an ultrafilter refining `atTop`
(`PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter`). The
identities `gelfandGalerkin_projected_integrated_initial_identity_Lp`, tested against the energy
projections of a fixed `v ∈ V`, pass to that limit in
`IsGelfandIntegratedWeakSolution.exists_of_approximations`. Evans takes `f ∈ L²(0, T; L²(U))`
from the start. We first solve for bounded continuous loads and then reach every load in
`L²(a, b; V*)` by density and the coercive continuous-dependence estimate
(`existsUnique_of_boundedContinuous_forcing`, `existsUnique_of_nonauto_galerkin_L2`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorems 1-4 (construction of approximate
  solutions, energy estimates, existence and uniqueness of weak solutions).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- If integrated weak solutions `u n` with initial data `u₀ n → u_init` converge weakly in
`L²(a, b; E)` along a filter `l ≤ atTop`, the weak limit is an integrated weak solution with
initial value `u_init`. -/
theorem IsIntegratedWeakSolution.of_weak_L2_limit
    {a b : ℝ}
    {u : ℕ → Lp E 2 (volume.restrict (Set.Ioc a b))}
    {uw : WeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b)))}
    {l : Filter ℕ} [l.NeBot]
    (huweak : Filter.Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b))) (u n)) l
      (nhds uw))
    (hl : l ≤ Filter.atTop) (u₀ : ℕ → E) (uInit : E)
    (hu₀ : Filter.Tendsto u₀ Filter.atTop (nhds uInit))
    (B : E →L[ℝ] StrongDual ℝ E)
    (ell : Lp (StrongDual ℝ E) 2 (volume.restrict (Set.Ioc a b)))
    (hsolution : ∀ n, IsIntegratedWeakSolution (fun _ ↦ B) (fun t ↦ ell t)
      (u n) (u₀ n)) :
    IsIntegratedWeakSolution (fun _ ↦ B) (fun t ↦ ell t)
      ((toWeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b)))).symm uw) uInit := by
  refine {
    interval_nonempty := (hsolution 0).interval_nonempty
    integrable_form := fun v τ ↦
      integrable_timeDependentBilinearTimeTest (fun _ ↦ B) v τ.toLp
        (fun _ ↦ aestronglyMeasurable_const) ‖B‖ (Filter.Eventually.of_forall fun _ ↦ le_rfl) _
    integrable_forcing := fun v τ ↦ integrable_dualTimeTest v τ.toLp ell
    equation := ?_ }
  intro v τ
  exact integrated_initial_identity_of_weak_L2_limit
    huweak hl u₀ uInit hu₀ B v τ.toLp τ.derivToLp (τ.toFun a)
    (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)))
    (fun n ↦ (hsolution n).equation v τ)

/-- A bounded sequence of integrated weak solutions with initial data `u₀ n → u_init` has a
weak limit along an ultrafilter `U ≤ atTop`, and that limit is an integrated weak solution with
initial value `u_init`. -/
theorem IsIntegratedWeakSolution.exists_weak_limit_of_isBounded
    {a b : ℝ}
    (u : ℕ → Lp E 2 (volume.restrict (Set.Ioc a b)))
    (hu : Bornology.IsBounded (Set.range u))
    (u₀ : ℕ → E) (uInit : E)
    (hu₀ : Filter.Tendsto u₀ Filter.atTop (nhds uInit))
    (B : E →L[ℝ] StrongDual ℝ E)
    (ell : Lp (StrongDual ℝ E) 2 (volume.restrict (Set.Ioc a b)))
    (hsolution : ∀ n, IsIntegratedWeakSolution (fun _ ↦ B) (fun t ↦ ell t)
      (u n) (u₀ n)) :
    ∃ (uLimit : Lp E 2 (volume.restrict (Set.Ioc a b))) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b))) (u n)) U
        (nhds (toWeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b))) uLimit)) ∧
      IsIntegratedWeakSolution (fun _ ↦ B) (fun t ↦ ell t) uLimit uInit := by
  obtain ⟨uw, U, hU, huweak⟩ :=
    PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop u hu
  let uLimit : Lp E 2 (volume.restrict (Set.Ioc a b)) :=
    (toWeakSpace ℝ (Lp E 2 (volume.restrict (Set.Ioc a b)))).symm uw
  refine ⟨uLimit, U, hU, ?_, ?_⟩
  · simpa only [uLimit, LinearEquiv.apply_symm_apply] using huweak
  · exact IsIntegratedWeakSolution.of_weak_L2_limit
      huweak hU u₀ uInit hu₀ B ell hsolution

section GelfandGalerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Integrated initial-value identity for a Gelfand Galerkin trajectory `u`, a trial vector
`v ∈ S` and a time test `τ`:
`-∫_a^b ⟪ι u, ι v⟫_H τ' + ∫_a^b B(t)(u, v) τ = ∫_a^b ℓ(t)(v) τ + ⟪ι u₀, ι v⟫_H τ(a)`.
This is the finite-dimensional identity passed to the limit in the proof of Evans §7.1.2,
Theorem 3. -/
theorem gelfandGalerkin_integrated_initial_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Submodule ℝ V} {a b C M : ℝ}
    {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (v : S) (τ : TimeTest a b)
    (hBτ : IntervalIntegrable
      (fun t ↦ B t (G.trajectory t : V) (v : V) * τ.toFun t) volume a b) :
    -(∫ t in a..b,
        inner ℝ (T.inclusion (G.trajectory t : V)) (T.inclusion (v : V)) *
          τ.derivFun t) +
        ∫ t in a..b, B t (G.trajectory t : V) (v : V) * τ.toFun t =
      (∫ t in a..b, ell t (v : V) * τ.toFun t) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (v : V)) * τ.toFun a := by
  have hsub : Set.uIcc a b ⊆ Set.Icc a b := (Set.uIcc_of_le hab).subset
  have huH : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt (fun s ↦ T.inclusion (G.trajectory s : V))
        (T.inclusion (G.coefficientDerivative t : V)) (Set.uIcc a b) t := fun t ht ↦
    (T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivWithinAt t
      ((G.derivative t (hsub ht)).mono hsub)
  have hducont : ContinuousOn
      (fun t ↦ inner ℝ (T.inclusion (G.coefficientDerivative t : V))
        (T.inclusion (v : V))) (Set.uIcc a b) :=
    ((T.inclusion.comp S.subtypeL).continuous.comp_continuousOn
      (G.derivativeContinuous.mono hsub)).inner continuousOn_const
  have hparts := weak_time_integration_by_parts_initial (T.inclusion (v : V)) huH
    (fun t ht ↦ (τ.hasDerivAt t (hsub ht)).hasDerivWithinAt) hducont.intervalIntegrable
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (τ.derivMemLp.integrable (by norm_num))) τ.final_zero
  have heqint :
      (∫ t in a..b,
        inner ℝ (T.inclusion (G.coefficientDerivative t : V))
          (T.inclusion (v : V)) * τ.toFun t) +
          ∫ t in a..b, B t (G.trajectory t : V) (v : V) * τ.toFun t =
        ∫ t in a..b, ell t (v : V) * τ.toFun t := by
    rw [← intervalIntegral.integral_add (hducont.intervalIntegrable.mul_continuousOn
      ((HasDerivAt.continuousOn τ.hasDerivAt).mono hsub)) hBτ]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    simp only [← add_mul, G.equation t (hsub ht) v]
  rw [hparts, G.initial] at heqint
  linarith

/-- The integrated Galerkin identity written with the Bochner classes `trajectoryLp`,
`τ.toLp` and `τ.derivToLp`. -/
theorem gelfandGalerkin_integrated_initial_identity_Lp
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Submodule ℝ V} {a b C M : ℝ}
    {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (v : S) (τ : TimeTest a b)
    (hBτ : IntervalIntegrable
      (fun t ↦ B t (G.trajectory t : V) (v : V) * τ.toFun t) volume a b) :
    -(∫ t,
        inner ℝ (T.inclusion (G.trajectoryLp t)) (T.inclusion (v : V)) *
          τ.derivToLp t ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (G.trajectoryLp t) (v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t (v : V) * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (v : V)) * τ.toFun a := by
  have hτ : (τ.toLp : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc a b)] τ.toFun := τ.memLp.coeFn_toLp
  have hdτ : (τ.derivToLp : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc a b)] τ.derivFun :=
    τ.derivMemLp.coeFn_toLp
  convert gelfandGalerkin_integrated_initial_identity G hab v τ hBτ using 3 <;>
    rw [intervalIntegral.integral_of_le hab] <;> refine integral_congr_ae ?_ <;>
    filter_upwards [G.trajectoryLp_apply_ae, hτ, hdτ] with t hu hτt hdτt
  · rw [hu, hdτt]; rfl
  · rw [hu, hτt]; rfl
  · rw [hτt]

/-- The `L²` Galerkin identity tested against the energy projection `P(ι v)` of any `v ∈ V`,
when `B` is continuous on `[a, b]`. -/
theorem gelfandGalerkin_projected_integrated_initial_identity_Lp
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Submodule ℝ V} {a b C M : ℝ} {K : NNReal}
    {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b)) (v : V) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (T.inclusion (G.trajectoryLp t))
        (T.inclusion (P.energyProjection v : V)) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (G.trajectoryLp t) (P.energyProjection v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t (P.energyProjection v : V) * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (P.energyProjection v : V)) *
          τ.toFun a := by
  exact gelfandGalerkin_integrated_initial_identity_Lp G hab (P.energyProjection v) τ
    ((((hBcont.clm_apply G.continuousOn_ambientTrajectory).clm_apply continuousOn_const).mul
      (HasDerivAt.continuousOn τ.hasDerivAt)).intervalIntegrable_of_Icc hab)

/-- A family of forms continuous on `[a, b]`, applied to a fixed vector, is a.e. strongly
measurable on `(a, b]`. -/
private theorem aestronglyMeasurable_apply_of_continuousOn {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {a b : ℝ} (hBcont : ContinuousOn B (Set.Icc a b)) (v : V) :
    AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Set.Ioc a b)) := by
  have : TopologicalSpace.PseudoMetrizableSpace (V →L[ℝ] StrongDual ℝ V) :=
    PseudoEMetricSpace.pseudoMetrizableSpace (α := V →L[ℝ] StrongDual ℝ V)
  exact ((hBcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc).apply_continuousLinearMap v

/-- Weak limits of a given family of Gelfand Galerkin approximations are integrated weak
solutions.

Let the trial spaces `S n` carry pivot-orthogonal projections with one energy bound `K` and be
eventually dense in `V`, hence in `H`. Let `B` and `ℓ` be continuous on `[a, b]` with
`‖B(t)‖ ≤ MB`. If each `S n` carries a Gelfand Galerkin approximation started at the
projection of `uInit`, a weak `L²(a, b; V)` limit of these approximations is an integrated weak
solution with initial value `uInit`. This is the limit step in the proof of Evans §7.1.2,
Theorem 3. -/
theorem IsGelfandIntegratedWeakSolution.exists_of_approximations
    [CompleteSpace V]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C M MB : ℝ} (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hBbound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hell_cont : ContinuousOn ell (Set.Icc a b))
    (uInit : H)
    (G : ∀ n, GelfandGalerkinApproximation T (S n) B ell a b C M
      ((P n).projection uInit)) :
    ∃ uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit := by
  classical
  have hMB : 0 ≤ MB := (norm_nonneg (B b)).trans (hBbound b ⟨hab.le, le_rfl⟩)
  let u₀ : ∀ n, S n := fun n ↦ (P n).projection uInit
  let state : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)) := fun n ↦ (G n).trajectoryLp
  let D : ℝ := (2 / C) * ((1 / 2 : ℝ) * ‖uInit‖ ^ 2 + (M ^ 2 / (2 * C)) * (b - a))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hstateSq (n : ℕ) : ‖state n‖ ^ 2 ≤ D := by
    refine ((G n).norm_trajectoryLp_sq_le hab.le hC).trans ?_
    have := (P n).norm_inclusion_projection_le uInit
    dsimp only [D]
    gcongr
  obtain ⟨uw, U, hU, huweak⟩ :=
    PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop state (isBounded_range_of_norm_sq_le state hD hstateSq)
  let uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)) :=
    (toWeakSpace ℝ (Lp V 2 (volume.restrict (Set.Ioc a b)))).symm uw
  let ellMem : MemLp ell 2 (volume.restrict (Set.Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hell_cont
  let ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)) := ellMem.toLp ell
  have hellLp : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell :=
    ellMem.coeFn_toLp
  have happrox (n : ℕ) (v : V) (τ : TimeTest a b) :
      -(∫ t, inner ℝ (T.inclusion (state n t))
          (T.inclusion ((P n).energyProjection v : V)) * τ.derivToLp t
            ∂(volume.restrict (Set.Ioc a b))) +
          ∫ t, B t (state n t) ((P n).energyProjection v : V) * τ.toLp t
            ∂(volume.restrict (Set.Ioc a b)) =
        (∫ t, ellLp t ((P n).energyProjection v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b))) +
          inner ℝ (T.inclusion (u₀ n : V))
            (T.inclusion ((P n).energyProjection v : V)) * τ.toFun a := by
    have hforcing :
        (∫ t, ellLp t ((P n).energyProjection v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b))) =
        ∫ t, ell t ((P n).energyProjection v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) :=
      integral_congr_ae (hellLp.mono fun t ht ↦ by simp only [ht])
    rw [hforcing]
    simpa only [state, u₀] using gelfandGalerkin_projected_integrated_initial_identity_Lp
      (G n) (P n) hab.le hBcont v τ
  have hweak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (state n)) U
      (nhds (toWeakSpace ℝ _ uLimit)) := by
    simpa only [uLimit, LinearEquiv.apply_symm_apply] using huweak
  exact ⟨uLimit, (isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit T B
    (aestronglyMeasurable_apply_of_continuousOn hBcont) MB hMB
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBbound t (Set.Ioc_subset_Icc_self ht))
    hab ellLp state uLimit hweak hU (√D) (fun n ↦ Real.le_sqrt_of_sq_le (hstateSq n))
    (fun n v ↦ ((P n).energyProjection v : V))
    (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdenseEnergy)
    (fun n ↦ T.inclusion (u₀ n : V)) uInit
    (StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable P
      (eventually_approximable_pivot_of_energy T S hdenseEnergy) uInit)
    happrox).congr_forcing_ae hellLp⟩

/-- Galerkin existence of integrated weak solutions for a time-dependent form. If `B` and
`ℓ` are continuous and bounded on `[a, b]` and `C ‖w‖² ≤ B(t)(w, w)` with `C > 0`, then for
every `uInit ∈ H` there is an integrated weak solution with initial value `uInit`. The
Galerkin approximations are constructed from the trial spaces, and the bounds are uniform in
the trial dimension. This follows the proofs of Evans §7.1.2, Theorems 1 to 3. -/
theorem IsGelfandIntegratedWeakSolution.exists_of_nonauto_galerkin
    [CompleteSpace V]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V) (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃ uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit := by
  let u₀ : ∀ n, S n := fun n ↦ (P n).projection uInit
  obtain ⟨G⟩ := GelfandGalerkinApproximation.exists_nonauto_sequence_on_Icc
    T S hfinite B ell hab.le hBcont hellcont MB Mell hC
      hBnorm hellnorm hcoercive u₀
  apply IsGelfandIntegratedWeakSolution.exists_of_approximations
    (M := (Mell : ℝ)) (MB := (MB : ℝ)) T S P hdenseEnergy
      B ell hab hC hBcont hBnorm hellcont uInit
  simpa [u₀] using G

/--
Extension from bounded continuous loads to `L²(a, b; V*)` loads. Let `B` be measurable,
essentially bounded and uniformly coercive on `[a, b]`. If an integrated weak solution with
initial value `uInit` exists for every bounded continuous load, then for every
`ℓ ∈ L²(a, b; V*)` there is exactly one. The proof uses density of bounded continuous
functions in `L²`, the coercive continuous-dependence estimate, and completeness.
-/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_boundedContinuous_forcing
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : NNReal)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖B t‖ ≤ (MB : ℝ))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H)
    (hsolve : ∀ f : ℝ →ᵇ StrongDual ℝ V,
      ∃ u : Lp V 2 (volume.restrict (Set.Ioc a b)),
        IsGelfandIntegratedWeakSolution T B f u uInit) :
    ∃! u : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit := by
  classical
  let μab := volume.restrict (Set.Ioc a b)
  let toLp : (ℝ →ᵇ StrongDual ℝ V) →L[ℝ] Lp (StrongDual ℝ V) 2 μab :=
    BoundedContinuousFunction.toLp 2 μab ℝ
  obtain ⟨ellLp, hellLpRange, hellLpTendsto⟩ := mem_closure_iff_seq_limit.mp
    (BoundedContinuousFunction.toLp_denseRange (StrongDual ℝ V) μab ℝ (by norm_num) ell)
  choose ellCont hellCont using hellLpRange
  have hellContTendsto :
      Filter.Tendsto (fun n ↦ toLp (ellCont n)) Filter.atTop (nhds ell) :=
    funext hellCont ▸ hellLpTendsto
  choose u hu using fun n ↦ hsolve (ellCont n)
  have huLp (n : ℕ) :
      IsGelfandIntegratedWeakSolution T B (fun t ↦ toLp (ellCont n) t) (u n) uInit :=
    (hu n).congr_forcing_ae
      (BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := μab) (𝕜 := ℝ) (ellCont n)).symm
  have huCauchy : CauchySeq u := Metric.cauchySeq_iff.2 fun ε hε ↦ by
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.1 hellContTendsto.cauchySeq (C * ε) (mul_pos hC hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm]
    calc ‖u m - u n‖ ≤ (1 / C) * ‖toLp (ellCont m) - toLp (ellCont n)‖ :=
          (huLp m).norm_sub_le_of_coercive_L2 hBmeas MB hBbound hC hcoercive (huLp n) hab
      _ < (1 / C) * (C * ε) := by
          gcongr
          simpa only [dist_eq_norm] using hN m hm n hn
      _ = ε := by field_simp
  obtain ⟨uLimit, huTendsto⟩ := cauchySeq_tendsto_of_complete huCauchy
  have huLimit : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) uLimit uInit :=
    IsGelfandIntegratedWeakSolution.tendsto_L2 hBmeas MB hBbound hellContTendsto huTendsto huLp
  exact ⟨uLimit, huLimit, fun v hv ↦ hv.unique hBmeas MB hBbound
    (fun t ht w ↦ (mul_nonneg hC.le (sq_nonneg ‖w‖)).trans (hcoercive t ht w)) huLimit hab⟩

/-- Existence and uniqueness for every load `ℓ ∈ L²(a, b; V*)`, when `B` is
continuous, bounded and uniformly coercive on `[a, b]`.

The Galerkin theorem is first applied to bounded continuous loads. Such loads are dense in
Bochner `L²`, so choose `ellₙ → ell`. The coercive continuous-dependence estimate

`‖uₙ-uₘ‖_{L²(V)} ≤ C⁻¹ ‖ellₙ-ellₘ‖_{L²(V*)}`

makes the corresponding solutions Cauchy. Completeness produces a strong
`L²(V)` limit, and `IsGelfandIntegratedWeakSolution.tendsto_L2` passes the
integrated equation to that limit. -/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_nonauto_galerkin_L2
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V) (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (MB : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃! u : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit := by
  refine existsUnique_of_boundedContinuous_forcing T B ell hab hC
    (aestronglyMeasurable_apply_of_continuousOn hBcont) MB
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBnorm t (Set.Ioc_subset_Icc_self ht))
    hcoercive uInit fun f ↦ ?_
  exact exists_of_nonauto_galerkin T S hfinite P hdenseEnergy B f hab hC hBcont
    f.continuous.continuousOn MB ‖f‖₊ hBnorm (fun t _ ↦ by simpa using f.norm_coe_le_norm t)
    hcoercive uInit

/--
Galerkin existence with the Lions–Magenes representative and the coercive energy estimate.
Under the hypotheses of `exists_of_nonauto_galerkin`, there is an integrated weak solution `u`
with a weak time derivative `g ∈ L²(a, b; V*)` and a continuous pivot representative `ũ` with
`ũ(a) = uInit` and, for every `t ∈ [a, b]`,

`½ ‖ũ(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖uInit‖²_H + Mell² (t - a) / (2C)`.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_nonauto_galerkin_with_energy_bound
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V) (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃ uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit ∧
      ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
        ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ uLimit t) (fun t ↦ g t) a b,
          HasGelfandWeakTimeDerivativeOn T uLimit g ∧
          E.representative a = uInit ∧
          ∀ t ∈ Set.Icc a b,
            (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
                (C / 2) * ∫ s in a..t, ‖uLimit s‖ ^ 2 ≤
              (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
                ((Mell : ℝ) ^ 2 / (2 * C)) * (t - a) := by
  obtain ⟨uLimit, huLimit⟩ := exists_of_nonauto_galerkin T S hfinite P hdenseEnergy B ell hab hC
    hBcont hellcont MB Mell hBnorm hellnorm hcoercive uInit
  exact ⟨uLimit, huLimit, huLimit.exists_continuousPivotEvolutionOn_with_energy_bound
    (aestronglyMeasurable_apply_of_continuousOn hBcont) MB
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBnorm t (Set.Ioc_subset_Icc_self ht))
    hellcont hC Mell.2 hcoercive hellnorm hab⟩

/--
The solution of `exists_of_nonauto_galerkin_with_energy_bound` is the unique integrated weak
solution with initial value `uInit`, together with its continuous pivot representative and
energy estimate. Uniqueness is `IsGelfandIntegratedWeakSolution.unique`.
-/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_nonauto_galerkin_with_energy_bound
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V) (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃! uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit ∧
      ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
        ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ uLimit t) (fun t ↦ g t) a b,
          HasGelfandWeakTimeDerivativeOn T uLimit g ∧
          E.representative a = uInit ∧
          ∀ t ∈ Set.Icc a b,
            (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
                (C / 2) * ∫ s in a..t, ‖uLimit s‖ ^ 2 ≤
              (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
                ((Mell : ℝ) ^ 2 / (2 * C)) * (t - a) := by
  obtain ⟨uLimit, huLimit, henergyData⟩ := exists_of_nonauto_galerkin_with_energy_bound T S
    hfinite P hdenseEnergy B ell hab hC hBcont hellcont MB Mell hBnorm hellnorm hcoercive uInit
  exact ⟨uLimit, ⟨huLimit, henergyData⟩, fun v hv ↦ hv.1.unique
    (aestronglyMeasurable_apply_of_continuousOn hBcont) MB
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBnorm t (Set.Ioc_subset_Icc_self ht))
    (fun t ht w ↦ (mul_nonneg hC.le (sq_nonneg ‖w‖)).trans (hcoercive t ht w)) huLimit hab⟩

/-- Existence and uniqueness for the nonautonomous Galerkin problem: if `B` and `ℓ` are
continuous and bounded on `[a, b]` and `B` is uniformly coercive, there is exactly one
integrated weak solution with initial value `uInit ∈ H`. Existence is the Galerkin
construction of Evans §7.1.2; uniqueness is the energy argument of §7.1.2, Theorem 4, run
through the Lions–Magenes identity. -/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_nonauto_galerkin
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V) (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃! uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit := by
  obtain ⟨uLimit, huLimit⟩ := exists_of_nonauto_galerkin T S hfinite P hdenseEnergy B ell hab hC
    hBcont hellcont MB Mell hBnorm hellnorm hcoercive uInit
  exact ⟨uLimit, huLimit, fun v hv ↦ hv.unique
    (aestronglyMeasurable_apply_of_continuousOn hBcont) MB
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBnorm t (Set.Ioc_subset_Icc_self ht))
    (fun t ht w ↦ (mul_nonneg hC.le (sq_nonneg ‖w‖)).trans (hcoercive t ht w)) huLimit hab⟩

end GelfandGalerkin

end PDE.Analysis.Evolution
