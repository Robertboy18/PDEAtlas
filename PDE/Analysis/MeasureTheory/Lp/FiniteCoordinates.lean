/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Analysis.Normed.PiLp.CompareExp
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lp bounds and uniform convergence from finitely many coordinates

The Lp norm of a finite product is bounded by the sum of its coordinate Lp
norms. Coordinate bounds therefore give a bound for the product with a constant
chosen before the parameter, and uniform convergence of coordinate Lp distances
gives uniform convergence of the product distance. Both the integration exponent
and the finite product exponent may be any exponent at least one.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Filter
open scoped ENNReal

variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]
  {F : κ → Type*} [∀ i, NormedAddCommGroup (F i)]
  {μ : Measure X} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The Lp norm of a finite product is at most the sum of coordinate Lp norms. -/
theorem lpNorm_piLp_le_sum (f : X → PiLp q F)
    (hf : ∀ i, MemLp (fun x ↦ f x i) p μ) :
    lpNorm f p μ ≤ ∑ i, lpNorm (fun x ↦ f x i) p μ := by
  classical
  have hdom : MemLp (fun x ↦ ∑ i, ‖f x i‖) p μ :=
    memLp_finsetSum Finset.univ (fun i _ ↦ (hf i).norm)
  calc
    _ ≤ lpNorm (fun x ↦ ∑ i, ‖f x i‖) p μ :=
      lpNorm_mono_real hdom (fun x ↦ PiLp.norm_le_sum_norm (f x))
    _ ≤ ∑ i, lpNorm (fun x ↦ ‖f x i‖) p μ := by
      simpa only [Finset.sum_fn] using
        lpNorm_sum_le (fun i (_ : i ∈ Finset.univ) ↦ (hf i).norm) Fact.out
    _ = _ := Finset.sum_congr rfl fun i _ ↦ lpNorm_norm (hf i).aestronglyMeasurable p

/-- Bounds for finitely many coordinates give a product Lp bound with one
constant chosen before the parameter. This includes gradient bounds obtained
from estimates for each partial derivative. -/
theorem exists_lpNorm_piLp_bound_of_coordinate_bounds
    {E : Type*} [NormedAddCommGroup E] (f : E → X → PiLp q F)
    (hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ U : E,
      MemLp (fun x ↦ f U x i) p μ ∧
        lpNorm (fun x ↦ f U x i) p μ ≤ C * ‖U‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : E, MemLp (f U) p μ ∧
      lpNorm (f U) p μ ≤ C * ‖U‖ := by
  classical
  choose C hC hb using hbound
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ hC i), fun U ↦ ?_⟩
  have hm (i : κ) := (hb i U).1
  refine ⟨memLp_piLp_iff.mpr hm, (lpNorm_piLp_le_sum (f U) hm).trans ?_⟩
  exact (Finset.sum_le_sum (fun i _ ↦ (hb i U).2)).trans_eq
    (Finset.sum_mul _ _ _).symm

/-- Uniform convergence of the Lp distance in every coordinate gives uniform
convergence for the finite product, including an empty coordinate family. -/
theorem tendstoUniformly_piLp_lpNorm {ι T : Type*} {l : Filter ι}
    (f : ι → T → X → PiLp q F) (g : T → X → PiLp q F)
    (hf : ∀ k t i, MemLp (fun x ↦ f k t x i) p μ)
    (hg : ∀ t i, MemLp (fun x ↦ g t x i) p μ)
    (hconv : ∀ i, TendstoUniformly
      (fun k t ↦ lpNorm (fun x ↦ f k t x i - g t x i) p μ) (fun _ ↦ 0) l) :
    TendstoUniformly (fun k t ↦ lpNorm (fun x ↦ f k t x - g t x) p μ)
      (fun _ ↦ 0) l := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hden : 0 < (Fintype.card κ : ℝ) + 1 := by positivity
  let δ := ε / ((Fintype.card κ : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [Filter.eventually_all.2 (fun i ↦
    Metric.tendstoUniformly_iff.mp (hconv i) δ hδ)] with k hk
  intro t
  have hb := lpNorm_piLp_le_sum (fun x ↦ f k t x - g t x)
    (fun i ↦ (hf k t i).sub (hg t i))
  rw [dist_zero_left, Real.norm_of_nonneg lpNorm_nonneg]
  apply hb.trans_lt
  calc
    _ ≤ ∑ _i : κ, δ := Finset.sum_le_sum fun i _ ↦ by
      have hi := hk i t
      rw [dist_zero_left, Real.norm_of_nonneg lpNorm_nonneg] at hi
      exact hi.le
    _ = (Fintype.card κ : ℝ) * δ := by simp
    _ < ((Fintype.card κ : ℝ) + 1) * δ :=
      mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hden.ne'

end MeasureTheory
