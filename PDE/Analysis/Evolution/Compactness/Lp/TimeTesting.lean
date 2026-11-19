/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import PDE.Analysis.Evolution.Integrated.TimeDependentForm
import PDE.Analysis.WeakCompactness

/-!
# Space-time tests for weak Bochner L² limits

To identify the weak limit of Galerkin approximations one tests the equation
against products `φ(t) v` of a scalar time test `φ ∈ L²(a, b)` and a spatial
vector `v ∈ V`. We realize the resulting space-time terms
`u ↦ ∫ B(u(t), v) φ(t) dt`, `u ↦ ∫ B(t)(u(t), v) φ(t) dt` and
`u ↦ ∫ ⟪u(t), v⟫ φ(t) dt` as continuous linear functionals on Bochner `L²`, by
composing bounded linear maps on Bochner spaces. A time-dependent form needs
only strong measurability on each fixed vector and an essential norm bound. Weak
convergence of the states then passes through each functional. We also prove
the weak–strong rules needed when the spatial test vectors themselves
converge strongly (as the projected tests `Pₘ v` do) while the states
converge only weakly.

## Main results

* `bilinearTimeTestFunctional`, `timeDependentBilinearTimeTestFunctional`,
  `timeTestFunctional`: the three functionals, with `_apply` lemmas
  identifying them with the intended integrals and norm bounds.
* `tendsto_bilinearTimeTest_of_tendsto_weak`,
  `tendsto_timeTest_of_tendsto_weak`: weak `L²` convergence passes through
  the tests.
* `tendsto_bilinearTimeTest_of_tendsto_weak_of_tendsto_test`,
  `tendsto_timeDependentBilinearTimeTest_of_tendsto_weak_of_tendsto_test`:
  weak states against strongly convergent, uniformly bounded spatial tests.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, equations (28)-(30)
  (passage to the limit against test functions `Σ_k d^k(t) w_k`).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

open InnerProductSpace

namespace PDE.Analysis.Evolution

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The integrated bilinear-form term with fixed spatial and temporal tests,
bundled as a continuous linear functional on Bochner `L²`. -/
noncomputable def bilinearTimeTestFunctional
    (B : E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ) :
    StrongDual ℝ (Lp E 2 μ) :=
  (innerSL ℝ φ).comp ((B.flip v).compLpL 2 μ)

omit [CompleteSpace E] in
/-- Evaluation of `bilinearTimeTestFunctional` is the expected Bochner
integral, up to the unavoidable almost-everywhere representative equality. -/
theorem bilinearTimeTestFunctional_apply
    (B : E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (u : Lp E 2 μ) :
    bilinearTimeTestFunctional B v φ u =
      ∫ t, B (u t) v * φ t ∂μ := by
  rw [bilinearTimeTestFunctional, ContinuousLinearMap.comp_apply]
  change inner ℝ φ ((B.flip v).compLpL 2 μ u) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(B.flip v).coeFn_compLpL u] with t ht
  simp only [ht, ContinuousLinearMap.flip_apply]
  rw [real_inner_comm]
  exact mul_comm _ _

omit [CompleteSpace E] in
/-- The bilinear space-time test has the expected product bound. -/
theorem norm_bilinearTimeTestFunctional_apply_le
    (B : E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (u : Lp E 2 μ) :
    ‖bilinearTimeTestFunctional B v φ u‖ ≤
      ‖φ‖ * ‖B‖ * ‖v‖ * ‖u‖ := by
  rw [bilinearTimeTestFunctional, ContinuousLinearMap.comp_apply]
  calc
    ‖innerSL ℝ φ ((B.flip v).compLpL 2 μ u)‖
        ≤ ‖φ‖ * ‖(B.flip v).compLpL 2 μ u‖ := by
          change ‖inner ℝ φ ((B.flip v).compLpL 2 μ u)‖ ≤ _
          exact norm_inner_le_norm φ ((B.flip v).compLpL 2 μ u)
    _ ≤ ‖φ‖ * (‖(B.flip v).compLpL 2 μ‖ * ‖u‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖φ‖ * (‖B.flip v‖ * ‖u‖) := by
          gcongr
          exact ContinuousLinearMap.norm_compLpL_le (B.flip v)
    _ ≤ ‖φ‖ * (‖B‖ * ‖v‖ * ‖u‖) := by
          gcongr
          simpa only [ContinuousLinearMap.opNorm_flip] using
            ContinuousLinearMap.le_opNorm B.flip v
    _ = ‖φ‖ * ‖B‖ * ‖v‖ * ‖u‖ := by ring

omit [CompleteSpace E] in
/-- A bilinear space-time test of two `L²` functions is integrable. -/
theorem integrable_bilinearTimeTest
    (B : E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (u : Lp E 2 μ) :
    Integrable (fun t ↦ B (u t) v * φ t) μ := by
  have hinner := L2.integrable_inner (𝕜 := ℝ) φ ((B.flip v).compLpL 2 μ u)
  apply hinner.congr
  filter_upwards [(B.flip v).coeFn_compLpL u] with t ht
  rw [ht]
  simp [mul_comm]

/-! ## Time-dependent form tests

For a nonautonomous form `B(t)`, the spatial term is still a fixed continuous
functional of the Bochner state once the spatial vector and time test are
fixed. Composing the form evaluation map with scalar testing constructs this
functional without an operator-valued measurability assumption.
-/

/-- Continuous functional on Bochner `L²` induced by a time-dependent
bilinear form and fixed space-time test. -/
noncomputable def timeDependentBilinearTimeTestFunctional
    (B : α → E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (hBmeas : ∀ w, AEStronglyMeasurable (fun t ↦ B t w) μ) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    StrongDual ℝ (Lp E 2 μ) :=
  ((innerSL ℝ φ).comp ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ)).comp
    (timeDependentFormLpCLM B hBmeas MB hBbound)

omit [CompleteSpace E] in
/-- Evaluation of the form functional is the intended space-time integral. -/
theorem timeDependentBilinearTimeTestFunctional_apply
    (B : α → E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (hBmeas : ∀ w, AEStronglyMeasurable (fun t ↦ B t w) μ) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) (u : Lp E 2 μ) :
    timeDependentBilinearTimeTestFunctional B v φ hBmeas MB hBbound u =
      ∫ t, B t (u t) v * φ t ∂μ := by
  change inner ℝ φ ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ
    (timeDependentFormLp B u hBmeas MB hBbound)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL
    (timeDependentFormLp B u hBmeas MB hBbound),
    timeDependentFormLp_apply_ae B u hBmeas MB hBbound] with t ht hBt
  simp [ht, hBt, mul_comm]

omit [CompleteSpace E] in
/-- Quantitative bound for the time-dependent bilinear space-time
functional. -/
theorem norm_timeDependentBilinearTimeTestFunctional_apply_le
    (B : α → E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (hBmeas : ∀ w, AEStronglyMeasurable (fun t ↦ B t w) μ) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) (u : Lp E 2 μ) :
    ‖timeDependentBilinearTimeTestFunctional B v φ hBmeas MB hBbound u‖ ≤
      ‖φ‖ * MB * ‖v‖ * ‖u‖ := by
  let w := timeDependentFormLp B u hBmeas MB hBbound
  have hw : ‖(ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ w‖ ≤ ‖v‖ * ‖w‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL w] with t ht
    simpa only [ht, ContinuousLinearMap.apply_apply, mul_comm] using (w t).le_opNorm v
  calc
    ‖timeDependentBilinearTimeTestFunctional B v φ hBmeas MB hBbound u‖ ≤
        ‖φ‖ * ‖(ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ w‖ := by
      change ‖inner ℝ φ ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ w)‖ ≤ _
      exact norm_inner_le_norm _ _
    _ ≤ ‖φ‖ * (‖v‖ * (MB * ‖u‖)) := by
      gcongr
      exact hw.trans (mul_le_mul_of_nonneg_left
        (norm_timeDependentFormLp_le B u hBmeas MB hBbound) (norm_nonneg v))
    _ = ‖φ‖ * MB * ‖v‖ * ‖u‖ := by ring

omit [CompleteSpace E] in
/-- The bilinear space-time test is integrable under measurability on each fixed vector. -/
theorem integrable_timeDependentBilinearTimeTest
    (B : α → E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ)
    (hBmeas : ∀ w, AEStronglyMeasurable (fun t ↦ B t w) μ) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) (u : Lp E 2 μ) :
    Integrable (fun t ↦ B t (u t) v * φ t) μ := by
  have hinner := L2.integrable_inner (𝕜 := ℝ) φ
    ((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 μ
      (timeDependentFormLp B u hBmeas MB hBbound))
  apply hinner.congr
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL
    (timeDependentFormLp B u hBmeas MB hBbound),
    timeDependentFormLp_apply_ae B u hBmeas MB hBbound] with t ht hBt
  simp [ht, hBt, mul_comm]

omit [CompleteSpace E] in
/-- Weak convergence of states and strong convergence of spatial tests pass
through an essentially bounded form whose evaluations are strongly measurable. -/
theorem tendsto_timeDependentBilinearTimeTest_of_tendsto_weak_of_tendsto_test
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp E 2 μ} {w : Lp E 2 μ}
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ (Lp E 2 μ) (u i)) l
      (nhds (toWeakSpace ℝ (Lp E 2 μ) w)))
    {v : ι → E} {vLimit : E} (hv : Filter.Tendsto v l (nhds vLimit))
    (R : ℝ) (huR : ∀ i, ‖u i‖ ≤ R)
    (B : α → E →L[ℝ] StrongDual ℝ E) (φ : Lp ℝ 2 μ)
    (hBmeas : ∀ w, AEStronglyMeasurable (fun t ↦ B t w) μ) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    Filter.Tendsto
      (fun i ↦ ∫ t, B t (u i t) (v i) * φ t ∂μ) l
      (nhds (∫ t, B t (w t) vLimit * φ t ∂μ)) := by
  let F : E → Lp E 2 μ → ℝ := fun z f ↦
    timeDependentBilinearTimeTestFunctional B z φ hBmeas MB hBbound f
  have herr : Filter.Tendsto (fun i ↦ F (v i - vLimit) (u i)) l (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun i ↦ (‖φ‖ * MB * R) * ‖v i - vLimit‖)
    · intro i
      exact (norm_timeDependentBilinearTimeTestFunctional_apply_le
        B (v i - vLimit) φ hBmeas MB hBbound (u i)).trans (by
          have hnonneg : 0 ≤ ‖φ‖ * MB * ‖v i - vLimit‖ := by positivity
          calc
            ‖φ‖ * MB * ‖v i - vLimit‖ * ‖u i‖ ≤
                ‖φ‖ * MB * ‖v i - vLimit‖ * R :=
              mul_le_mul_of_nonneg_left (huR i) hnonneg
            _ = (‖φ‖ * MB * R) * ‖v i - vLimit‖ := by ring)
    · have hvzero : Filter.Tendsto (fun i ↦ ‖v i - vLimit‖) l (nhds 0) := by
        have hconst : Filter.Tendsto (fun _ : ι ↦ vLimit) l (nhds vLimit) :=
          tendsto_const_nhds
        simpa using (hv.sub hconst).norm
      simpa using hvzero.const_mul (‖φ‖ * MB * R)
  have hfixed : Filter.Tendsto (fun i ↦ F vLimit (u i)) l
      (nhds (F vLimit w)) := by
    simpa [F] using PDE.Analysis.WeakCompactness.tendsto_evaluation hu
      (timeDependentBilinearTimeTestFunctional
        B vLimit φ hBmeas MB hBbound)
  have hsum := herr.add hfixed
  have hsum' : Filter.Tendsto (fun i ↦ F (v i) (u i)) l
      (nhds (F vLimit w)) := by
    convert hsum using 1
    · funext i
      simp only [F, timeDependentBilinearTimeTestFunctional_apply]
      rw [← integral_add
        (integrable_timeDependentBilinearTimeTest
          B (v i - vLimit) φ hBmeas MB hBbound (u i))
        (integrable_timeDependentBilinearTimeTest
          B vLimit φ hBmeas MB hBbound (u i))]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [map_sub]
      ring
    · simp
  simpa only [F, timeDependentBilinearTimeTestFunctional_apply] using hsum'

omit [CompleteSpace E] in
/-- A weakly convergent `L²(E)` family may be tested against spatial vectors
that converge strongly in `E`, provided the family has a uniform norm bound. -/
theorem tendsto_bilinearTimeTest_of_tendsto_weak_of_tendsto_test
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp E 2 μ} {w : Lp E 2 μ}
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ (Lp E 2 μ) (u i)) l
      (nhds (toWeakSpace ℝ (Lp E 2 μ) w)))
    {v : ι → E} {vLimit : E} (hv : Filter.Tendsto v l (nhds vLimit))
    (R : ℝ) (huR : ∀ i, ‖u i‖ ≤ R)
    (B : E →L[ℝ] StrongDual ℝ E) (φ : Lp ℝ 2 μ) :
    Filter.Tendsto
      (fun i ↦ ∫ t, B (u i t) (v i) * φ t ∂μ) l
      (nhds (∫ t, B (w t) vLimit * φ t ∂μ)) := by
  let F : E → Lp E 2 μ → ℝ := fun z f ↦ bilinearTimeTestFunctional B z φ f
  have herr : Filter.Tendsto (fun i ↦ F (v i - vLimit) (u i)) l (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun i ↦ (‖φ‖ * ‖B‖ * R) * ‖v i - vLimit‖)
    · intro i
      exact (norm_bilinearTimeTestFunctional_apply_le B (v i - vLimit) φ (u i)).trans
        (by
          have hnonneg : 0 ≤ ‖φ‖ * ‖B‖ * ‖v i - vLimit‖ := by positivity
          calc
            ‖φ‖ * ‖B‖ * ‖v i - vLimit‖ * ‖u i‖
                ≤ ‖φ‖ * ‖B‖ * ‖v i - vLimit‖ * R :=
              mul_le_mul_of_nonneg_left (huR i) hnonneg
            _ = (‖φ‖ * ‖B‖ * R) * ‖v i - vLimit‖ := by ring)
    · have hvzero : Filter.Tendsto (fun i ↦ ‖v i - vLimit‖) l (nhds 0) := by
        have hconst : Filter.Tendsto (fun _ : ι ↦ vLimit) l (nhds vLimit) :=
          tendsto_const_nhds
        simpa using (hv.sub hconst).norm
      simpa using hvzero.const_mul (‖φ‖ * ‖B‖ * R)
  have hfixed : Filter.Tendsto (fun i ↦ F vLimit (u i)) l (nhds (F vLimit w)) := by
    simpa [F] using
      PDE.Analysis.WeakCompactness.tendsto_evaluation hu
        (bilinearTimeTestFunctional B vLimit φ)
  have hsum := herr.add hfixed
  have hsum' : Filter.Tendsto (fun i ↦ F (v i) (u i)) l (nhds (F vLimit w)) := by
    convert hsum using 1
    · funext i
      simp only [F, bilinearTimeTestFunctional_apply]
      rw [← integral_add
        (integrable_bilinearTimeTest B (v i - vLimit) φ (u i))
        (integrable_bilinearTimeTest B vLimit φ (u i))]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [map_sub]
      ring
    · simp
  simpa only [F, bilinearTimeTestFunctional_apply] using hsum'

omit [CompleteSpace E] in
/-- The integrated spatial bilinear-form term passes to a weak Bochner `L²`
limit for every fixed spatial and temporal test. -/
theorem tendsto_bilinearTimeTest_of_tendsto_weak
    {ι : Type*} {l : Filter ι}
    {u : ι → WeakSpace ℝ (Lp E 2 μ)} {w : WeakSpace ℝ (Lp E 2 μ)}
    (hu : Filter.Tendsto u l (nhds w))
    (B : E →L[ℝ] StrongDual ℝ E) (v : E) (φ : Lp ℝ 2 μ) :
    Filter.Tendsto
      (fun i ↦ ∫ t,
        B (((toWeakSpace ℝ (Lp E 2 μ)).symm (u i)) t) v * φ t ∂μ) l
      (nhds (∫ t,
        B (((toWeakSpace ℝ (Lp E 2 μ)).symm w) t) v * φ t ∂μ)) := by
  simpa only [bilinearTimeTestFunctional_apply] using
    PDE.Analysis.WeakCompactness.tendsto_evaluation hu
      (bilinearTimeTestFunctional B v φ)

/-- The integrated time-test term with fixed spatial vector and scalar `L²`
test, bundled as a continuous functional on Bochner `L²`. -/
noncomputable def timeTestFunctional (v : E) (ψ : Lp ℝ 2 μ) :
    StrongDual ℝ (Lp E 2 μ) :=
  (innerSL ℝ ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL 2 μ ψ))

omit [CompleteSpace E] in
/-- Evaluation of `timeTestFunctional` is the expected integral
`∫ ⟪u(t),v⟫ ψ(t)`. -/
theorem timeTestFunctional_apply (v : E) (ψ : Lp ℝ 2 μ) (u : Lp E 2 μ) :
    timeTestFunctional v ψ u = ∫ t, inner ℝ (u t) v * ψ t ∂μ := by
  rw [timeTestFunctional]
  change inner ℝ ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL 2 μ ψ) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLpL ψ] with t ht
  simp only [ht, ContinuousLinearMap.toSpanSingleton_apply]
  rw [real_inner_comm, inner_smul_right]
  simp [mul_comm]

omit [CompleteSpace E] in
/-- The integrated time-test term passes to a weak Bochner `L²` limit. -/
theorem tendsto_timeTest_of_tendsto_weak
    {ι : Type*} {l : Filter ι}
    {u : ι → WeakSpace ℝ (Lp E 2 μ)} {w : WeakSpace ℝ (Lp E 2 μ)}
    (hu : Filter.Tendsto u l (nhds w)) (v : E) (ψ : Lp ℝ 2 μ) :
    Filter.Tendsto
      (fun i ↦ ∫ t, inner ℝ
        (((toWeakSpace ℝ (Lp E 2 μ)).symm (u i)) t) v * ψ t ∂μ) l
      (nhds (∫ t, inner ℝ
        (((toWeakSpace ℝ (Lp E 2 μ)).symm w) t) v * ψ t ∂μ)) := by
  simpa only [timeTestFunctional_apply] using
    PDE.Analysis.WeakCompactness.tendsto_evaluation hu
      (timeTestFunctional v ψ)

end PDE.Analysis.Evolution
