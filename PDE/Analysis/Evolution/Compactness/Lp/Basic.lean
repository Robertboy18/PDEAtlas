/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Analysis.WeakCompactness

/-!
# Basic Bochner L² compactness estimates

Generic facts about Bochner `L²` spaces of Hilbert-space-valued functions used
by the Galerkin compactness arguments.  A trajectory continuous on `[a, b]`
defines an `L²` class on `(a, b]`, and multiplying by a scalar function
continuous on `[a, b]` (the exponential weight of the Gårding change of
unknown) preserves `L²`.  A uniformly bounded, strongly convergent sequence of
operators `Qₙ → I` on `E` acts strongly on `L²(μ; E)`, by dominated
convergence of the pointwise errors; this is how trial projections are applied
to Bochner trajectories.  Finally, a weakly convergent bounded family can be
paired against a strongly convergent family of test vectors, the weak–strong
rule behind passing to the limit in Galerkin schemes, as in the passage from (29) to (30) in
step 2 of the proof of Evans, §7.1.2, Theorem 3, where the approximations converge weakly
by (27).

## Main results

* `memLp_restrict_Ioc_of_continuousOn`,
  `memLp_restrict_Ioc_smul_of_continuousOn`, `scalarMulLp`: `L²` classes from
  continuous trajectories and bounded multipliers.
* `tendsto_compLpL_of_tendsto_strongly`: strong operator convergence lifts to
  Bochner `L²`.
* `tendsto_inner_of_tendsto_weak_of_tendsto_strong`: `xᵢ ⇀ x`, `yᵢ → y` and
  `‖xᵢ‖ ≤ R` give `⟪yᵢ, xᵢ⟫ → ⟪y, x⟫`.
* `isBounded_range_of_norm_sq_le`: a uniform squared-norm bound gives a
  bounded range.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 3 (Existence of weak solution), steps 1
  and 2 of its proof, (27)-(30), pp. 378-379. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A norm-continuous trajectory on a compact interval defines a Bochner
`L²` class on its interior. -/
theorem memLp_restrict_Ioc_of_continuousOn
    {f : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    MemLp f 2 (volume.restrict (Set.Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply MemLp.of_bound
    ((hf.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Set.Ioc_subset_Icc_self hx)

/-- Multiplication by a scalar function continuous on the closed time
interval preserves Bochner `L²` on its interior.

This is the bounded-multiplier lemma used for the exponential change of
unknown in the Gårding case. Stating it once at the `MemLp` level avoids
choosing pointwise representatives in later evolution theorems. -/
theorem memLp_restrict_Ioc_smul_of_continuousOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (χ : ℝ → ℝ) (hχ : ContinuousOn χ (Set.Icc a b))
    (f : ℝ → X) (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) :
    MemLp (fun t ↦ χ t • f t) 2 (volume.restrict (Set.Ioc a b)) := by
  let μab := volume.restrict (Set.Ioc a b)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hχ
  have hmeas : AEStronglyMeasurable (fun t ↦ χ t • f t) μab :=
    (hχ.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc |>.smul hf.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μab, ‖χ t • f t‖ ≤ C * ‖f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (hC t (Set.Ioc_subset_Icc_self ht)) (norm_nonneg _)
  exact MemLp.of_le_mul hf hmeas hbound

/-- The Bochner `L²` trajectory obtained by multiplying by a scalar function
continuous on the closed time interval. -/
noncomputable def scalarMulLp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (χ : ℝ → ℝ) (hχ : ContinuousOn χ (Set.Icc a b))
    (u : Lp X 2 (volume.restrict (Set.Ioc a b))) :
    Lp X 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_smul_of_continuousOn χ hχ u
    (MeasureTheory.Lp.memLp u)).toLp (fun t ↦ χ t • u t)

/-- `scalarMulLp` agrees almost everywhere with pointwise scalar
multiplication. -/
theorem scalarMulLp_apply_ae
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (χ : ℝ → ℝ) (hχ : ContinuousOn χ (Set.Icc a b))
    (u : Lp X 2 (volume.restrict (Set.Ioc a b))) :
    (scalarMulLp χ hχ u : ℝ → X) =ᵐ[
      volume.restrict (Set.Ioc a b)] fun t ↦ χ t • u t :=
  (memLp_restrict_Ioc_smul_of_continuousOn χ hχ u
    (MeasureTheory.Lp.memLp u)).coeFn_toLp

omit [CompleteSpace E] in
/-- Strong operator convergence lifts pointwise to Bochner `L²`.

Let `Qₙ : E → E` be uniformly bounded continuous linear maps such that
`Qₙ x → x` for every `x : E`. Then the induced maps on `L²(μ;E)` satisfy
`Qₙ u → u` strongly for every Bochner class `u`.

The proof works directly with representatives: the squared pointwise errors
converge to zero and are dominated by `(C + 1)² ‖u(t)‖²`. -/
theorem tendsto_compLpL_of_tendsto_strongly
    (Q : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hQbound : ∀ n x, ‖Q n x‖ ≤ C * ‖x‖)
    (hQ : ∀ x, Filter.Tendsto (fun n ↦ Q n x)
      Filter.atTop (nhds x))
    (u : Lp E 2 μ) :
    Filter.Tendsto
      (fun n ↦ (Q n).compLpL 2 μ u)
      Filter.atTop (nhds u) := by
  have hdom (n : ℕ) : ∀ᵐ t ∂μ, ‖‖Q n (u t) - u t‖ ^ 2‖ ≤ (C + 1) ^ 2 * ‖u t‖ ^ 2 :=
    .of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).2
        (by linarith [norm_sub_le (Q n (u t)) (u t), hQbound n (u t)])
  have hpoint : ∀ᵐ t ∂μ, Filter.Tendsto (fun n ↦ ‖Q n (u t) - u t‖ ^ 2) Filter.atTop (nhds 0) :=
    .of_forall fun t ↦ by simpa using ((hQ (u t)).sub_const (u t)).norm.pow 2
  have hint := tendsto_integral_of_dominated_convergence (F := fun n t ↦ ‖Q n (u t) - u t‖ ^ 2) _
    (fun n ↦ (((Q n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      (Lp.aestronglyMeasurable u)).norm.pow 2)
    (((Lp.memLp u).integrable_norm_pow two_ne_zero).const_mul _) hdom hpoint
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := hint.sqrt
  rw [integral_zero, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n ↦ ?_
  rw [← Real.sqrt_sq (norm_nonneg ((Q n).compLpL 2 μ u - u)), Lp.norm_sq_eq_integral_norm_sq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(Q n).coeFn_compLpL u, Lp.coeFn_sub ((Q n).compLpL 2 μ u) u] with t hQn hsub
  rw [hsub, Pi.sub_apply, hQn]

omit [CompleteSpace E] in
/-- A weakly convergent Hilbert-space family can be paired with a strongly
convergent family of test vectors.

If `xᵢ ⇀ x`, `yᵢ → y`, and the `xᵢ` are uniformly bounded, then
`⟪yᵢ, xᵢ⟫ → ⟪y, x⟫`. -/
theorem tendsto_inner_of_tendsto_weak_of_tendsto_strong
    {ι : Type*} {l : Filter ι}
    {x : ι → E} {xLimit : E}
    (hx : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ E (x i)) l
      (nhds (toWeakSpace ℝ E xLimit)))
    {y : ι → E} {yLimit : E}
    (hy : Filter.Tendsto y l (nhds yLimit))
    (R : ℝ) (hxR : ∀ i, ‖x i‖ ≤ R) :
    Filter.Tendsto
      (fun i ↦ inner ℝ (y i) (x i)) l
      (nhds (inner ℝ yLimit xLimit)) := by
  simpa only [Function.comp_apply, innerSL_apply_apply] using
    PDE.Analysis.WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
      ((innerSL ℝ).continuous.continuousAt.tendsto.comp hy) hx R hxR

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A uniform squared-norm estimate gives a bounded range. -/
theorem isBounded_range_of_norm_sq_le
    (f : ℕ → E) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ^ 2 ≤ C) :
    Bornology.IsBounded (Set.range f) := by
  refine isBounded_iff_forall_norm_le.2
    ⟨√C, Set.forall_mem_range.2 fun n ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hC]
  exact hf n

end PDE.Analysis.Evolution
