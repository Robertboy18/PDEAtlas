/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Bochner.Duality
public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.WeakCompactness

/-!
# Weak-limit testing for Galerkin compactness

Bounded state and derivative sequences admit a common weakly convergent
ultrafilter subnet in Bochner `L²`. Dual-valued derivatives are transported
through the Hilbert-space Riesz isometry for compactness and returned as
intrinsic `L²(V*)` limits.

We also realize space-time duality pairings as continuous functionals.
These functionals pass Galerkin identities and initial pairings to weak
limits.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, (27) (weak limits in `L²(0, T;
  H⁻¹(U))`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction
open PDE.Analysis

namespace PDE.Analysis.Evolution

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section DualDerivativeTesting

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/--
A bounded dual-valued Bochner family has an intrinsic `L²(μ; W*)` weak
limit along an ultrafilter refining any prescribed filter.

Weak convergence is expressed after pointwise Riesz transport to
`L²(μ; W)`, while the returned limit remains dual-valued. Chaining this
theorem with the ordinary Hilbert-space refinement theorem handles arbitrary
finite mixtures of primal and dual trajectories without fixed-arity APIs.
-/
theorem exists_ultrafilter_tendsto_weak_dual_of_isBounded_range_filter
    [CompleteSpace W]
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (g : ι → Lp (StrongDual ℝ W) 2 μ)
    (hg : Bornology.IsBounded (Set.range g)) :
    ∃ (gLimit : Lp (StrongDual ℝ W) 2 μ) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      Filter.Tendsto
        (fun i ↦ toWeakSpace ℝ _ (rieszFromDualLp (g i))) U
        (nhds (toWeakSpace ℝ _ (rieszFromDualLp gLimit))) := by
  have hRiesz : Bornology.IsBounded
      (Set.range (fun i ↦ rieszFromDualLp (g i))) := by
    simpa only [← Set.range_comp, Function.comp_def] using
      hg.image rieszFromDualLp
  obtain ⟨gRieszLimit, U, hU, hgWeak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      l (fun i ↦ rieszFromDualLp (g i)) hRiesz
  let gLimit : Lp (StrongDual ℝ W) 2 μ := rieszToDualLp gRieszLimit
  exact ⟨gLimit, U, hU, by simpa [gLimit] using hgWeak⟩

/-- The fixed space-time test
`g ↦ ∫ g(t)(v) φ(t) dt` as a continuous linear functional on
`L²(μ; V*)`. This is the functional required to identify the weak limit of
Galerkin time derivatives in the proof of Evans §7.1.2, Theorem 3. -/
noncomputable def dualTimeTestFunctional (v : W) (φ : Lp ℝ 2 μ) :
    StrongDual ℝ (Lp (StrongDual ℝ W) 2 μ) :=
  (innerSL ℝ φ).comp
    ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ)

/-- Evaluation of `dualTimeTestFunctional` is the expected duality-pairing
integral. -/
theorem dualTimeTestFunctional_apply
    (v : W) (φ : Lp ℝ 2 μ) (g : Lp (StrongDual ℝ W) 2 μ) :
    dualTimeTestFunctional v φ g = ∫ t, g t v * φ t ∂μ := by
  rw [dualTimeTestFunctional, ContinuousLinearMap.comp_apply]
  change inner ℝ φ ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ g) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL g] with t ht
  simp only [ht]
  rw [real_inner_comm]
  exact mul_comm _ _

/-- A fixed spatial test of an `L²(V*)` trajectory, multiplied by an `L²`
scalar time test, is integrable. -/
theorem integrable_dualTimeTest
    (v : W) (φ : Lp ℝ 2 μ) (g : Lp (StrongDual ℝ W) 2 μ) :
    Integrable (fun t ↦ g t v * φ t) μ := by
  have hinner := L2.integrable_inner (𝕜 := ℝ) φ
    ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ g)
  apply hinner.congr
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL g] with t ht
  rw [ht]
  simp [mul_comm]

/-- Weak convergence of the Riesz representatives of a dual-valued
trajectory passes to every fixed spatial and scalar time test.  The explicit
Riesz map avoids conflating the intrinsic Banach structure on `V*` with the
definitionally distinct Hilbert structure transported from `V`. -/
theorem tendsto_rieszDualTimeTest_of_tendsto_weak
    [CompleteSpace W]
    {ι : Type*} {l : Filter ι}
    {g : ι → WeakSpace ℝ (Lp W 2 μ)} {gw : WeakSpace ℝ (Lp W 2 μ)}
    (hg : Filter.Tendsto g l (nhds gw)) (v : W) (φ : Lp ℝ 2 μ) :
    Filter.Tendsto
      (fun i ↦ ∫ t,
        InnerProductSpace.toDual ℝ W
          (((toWeakSpace ℝ (Lp W 2 μ)).symm (g i)) t) v * φ t ∂μ) l
      (nhds (∫ t,
        InnerProductSpace.toDual ℝ W
          (((toWeakSpace ℝ (Lp W 2 μ)).symm gw) t) v * φ t ∂μ)) := by
  simpa only [InnerProductSpace.toDual_apply_apply] using
    tendsto_timeTest_of_tendsto_weak hg v φ

/-- A fixed `L²(V*)` forcing trajectory may be paired against spatial tests
that converge strongly in `V`. -/
theorem tendsto_dualTimeTest_of_tendsto_test
    [CompleteSpace W]
    {ι : Type*} {l : Filter ι}
    (g : Lp (StrongDual ℝ W) 2 μ) {v : ι → W} {vLimit : W}
    (hv : Filter.Tendsto v l (nhds vLimit)) (φ : Lp ℝ 2 μ) :
    Filter.Tendsto (fun i ↦ ∫ t, g t (v i) * φ t ∂μ) l
      (nhds (∫ t, g t vLimit * φ t ∂μ)) := by
  let gr : Lp W 2 μ := rieszFromDualLp g
  have hu : Filter.Tendsto
      (fun _ : ι ↦ toWeakSpace ℝ (Lp W 2 μ) gr) l
      (nhds (toWeakSpace ℝ (Lp W 2 μ) gr)) := tendsto_const_nhds
  have h := tendsto_bilinearTimeTest_of_tendsto_weak_of_tendsto_test
    hu hv ‖gr‖ (fun _ ↦ le_rfl)
    (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv.toContinuousLinearMap φ
  convert h using 1
  · funext i
    exact integral_dual_pairing_eq_riesz g (v i) φ
  · exact congrArg nhds (integral_dual_pairing_eq_riesz g vLimit φ)

end DualDerivativeTesting

/-- An integrated variational identity is closed under convergence of its
three scalar terms.  This elementary topological step is used after weak
compactness and the fixed-test convergence lemmas identify the limits of the
time, form, and forcing integrals. -/
theorem limit_integrated_identity
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {timeTerm formTerm forcingTerm : ι → ℝ}
    {timeLimit formLimit forcingLimit : ℝ}
    (heq : ∀ i, -timeTerm i + formTerm i = forcingTerm i)
    (htime : Filter.Tendsto timeTerm l (nhds timeLimit))
    (hform : Filter.Tendsto formTerm l (nhds formLimit))
    (hforcing : Filter.Tendsto forcingTerm l (nhds forcingLimit)) :
    -timeLimit + formLimit = forcingLimit := by
  have hleft : Filter.Tendsto (fun i ↦ -timeTerm i + formTerm i) l
      (nhds (-timeLimit + formLimit)) :=
    htime.neg.add hform
  have hleft' : Filter.Tendsto forcingTerm l
      (nhds (-timeLimit + formLimit)) := by
    apply hleft.congr'
    exact Filter.Eventually.of_forall heq
  exact tendsto_nhds_unique hleft' hforcing

/-- The integrated identity with an initial boundary term is closed under
convergence of all four scalar terms. -/
theorem limit_integrated_initial_identity
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {timeTerm formTerm forcingTerm initialTerm : ι → ℝ}
    {timeLimit formLimit forcingLimit initialLimit : ℝ}
    (heq : ∀ i,
      -timeTerm i + formTerm i = forcingTerm i + initialTerm i)
    (htime : Filter.Tendsto timeTerm l (nhds timeLimit))
    (hform : Filter.Tendsto formTerm l (nhds formLimit))
    (hforcing : Filter.Tendsto forcingTerm l (nhds forcingLimit))
    (hinitial : Filter.Tendsto initialTerm l (nhds initialLimit)) :
    -timeLimit + formLimit = forcingLimit + initialLimit := by
  exact limit_integrated_identity
    (forcingTerm := fun i ↦ forcingTerm i + initialTerm i)
    heq htime hform (hforcing.add hinitial)

/-- Strong convergence of approximate initial data implies convergence of
all weak initial pairings along every filter refining the original one. -/
theorem tendsto_initial_pairing_of_tendsto
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {l l' : Filter ι} {u₀ : ι → V} {uInit : V}
    (hu₀ : Filter.Tendsto u₀ l (nhds uInit)) (hl : l' ≤ l) (v : V) :
    Filter.Tendsto (fun i ↦ inner ℝ (u₀ i) v) l'
      (nhds (inner ℝ uInit v)) := by
  have h := (innerSL ℝ v).continuous.continuousAt.tendsto.comp
    (hu₀.mono_left hl)
  convert h using 1
  · funext i
    exact real_inner_comm _ _
  · exact congrArg nhds (real_inner_comm _ _)

/-- Strong convergence of both the approximate initial data and the spatial
tests passes through the pivot-space pairing of a Gelfand triple. -/
theorem tendsto_gelfandInitialPairing_of_tendsto
    {ι V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H)) {l : Filter ι}
    {u₀ : ι → H} {uInit : H} (hu₀ : Filter.Tendsto u₀ l (nhds uInit))
    {v : ι → V} {vLimit : V} (hv : Filter.Tendsto v l (nhds vLimit)) :
    Filter.Tendsto
      (fun i ↦ inner ℝ (u₀ i) (T.inclusion (v i))) l
      (nhds (inner ℝ uInit (T.inclusion vLimit))) := by
  exact hu₀.inner
    (T.inclusion.continuous.continuousAt.tendsto.comp hv)

omit [CompleteSpace E] in
/-- Complete fixed-test Galerkin limit passage in Bochner `L²`.

If the approximate states converge weakly along a filter refining `atTop`,
their initial projections converge strongly to `uInit`, and every approximate
state satisfies the integrated identity for fixed tests `v`, `φ`, and `ψ`,
then the weak limit satisfies the same identity with initial datum `uInit`.
Here `ψ` represents the derivative of the scalar time test. -/
theorem integrated_initial_identity_of_weak_L2_limit
    {u : ℕ → Lp E 2 μ} {uw : WeakSpace ℝ (Lp E 2 μ)}
    {l : Filter ℕ} [l.NeBot]
    (huweak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 2 μ) (u n)) l (nhds uw))
    (hl : l ≤ Filter.atTop)
    (u₀ : ℕ → E) (uInit : E)
    (hu₀ : Filter.Tendsto u₀ Filter.atTop (nhds uInit))
    (B : E →L[ℝ] StrongDual ℝ E) (v : E)
    (φ ψ : Lp ℝ 2 μ) (φa forcingTerm : ℝ)
    (heq : ∀ n,
      -(∫ t, inner ℝ (u n t) v * ψ t ∂μ) +
          ∫ t, B (u n t) v * φ t ∂μ =
        forcingTerm + inner ℝ (u₀ n) v * φa) :
    -(∫ t, inner ℝ (((toWeakSpace ℝ (Lp E 2 μ)).symm uw) t) v * ψ t ∂μ) +
        ∫ t, B (((toWeakSpace ℝ (Lp E 2 μ)).symm uw) t) v * φ t ∂μ =
      forcingTerm + inner ℝ uInit v * φa := by
  apply limit_integrated_initial_identity (l := l) heq
  · exact tendsto_timeTest_of_tendsto_weak huweak v ψ
  · exact tendsto_bilinearTimeTest_of_tendsto_weak huweak B v φ
  · exact tendsto_const_nhds
  · exact (tendsto_initial_pairing_of_tendsto hu₀ hl v).mul_const φa

end PDE.Analysis.Evolution
