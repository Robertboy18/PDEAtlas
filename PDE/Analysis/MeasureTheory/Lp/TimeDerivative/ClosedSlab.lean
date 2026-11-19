/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.ClosedSlab
public import PDE.Analysis.MeasureTheory.Lp.TimeDerivative
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Strong time derivatives of bounded spacetime fields

A bounded second differential on a closed time slab gives a uniform modulus
for its first time derivative, even on an unbounded spatial domain. The
uniform-derivative criterion `hasDerivWithinAt_lp_top_of_ae_uniform_derivative`
therefore differentiates any represented
L∞ curve in norm, including within derivatives at both time endpoints.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Filter Set PDE.Common
open scoped ENNReal NNReal ContDiff

variable {n : ℕ} {a b : ℝ} {μ : Measure (ℝ^n)}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A jointly C² field with bounded first and second differentials has a
Lipschitz L∞ time derivative. This identifies the strong within derivative
of any L∞ curve representing its spatial slices. No finite spatial measure,
extension across the endpoint, or differentiability of spatial derivative
rows as L∞ curves is assumed. -/
theorem exists_lp_top_timeDerivative_of_contDiffOn
    (hab : a < b) {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ 2 f {p | p 0 ∈ Icc a b}) (M : ℝ≥0)
    (hone : ∀ p, p 0 ∈ Icc a b →
      ‖fderivWithin ℝ f {q | q 0 ∈ Icc a b} p‖ ≤ M)
    (htwo : ∀ p, p 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 f {q | q 0 ∈ Icc a b} p‖ ≤ M)
    (F : ℝ → Lp E ∞ μ)
    (hF : ∀ t ∈ Icc a b, (F t : ℝ^n → E) =ᵐ[μ]
      fun x ↦ f (timeSpaceCons t x)) :
    ∃ D : ℝ → Lp E ∞ μ,
      LipschitzOnWith M D (Icc a b) ∧
      (∀ t ∈ Icc a b, ‖D t‖ ≤ M) ∧
      (∀ t ∈ Icc a b, (D t : ℝ^n → E) =ᵐ[μ] fun x ↦
        fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)
          (EuclideanSpace.single 0 1)) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt F (D t) (Icc a b) t) := by
  classical
  let d (t : ℝ) (x : ℝ^n) :=
    fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)
      (EuclideanSpace.single 0 1)
  have hfone : ContDiffOn ℝ 1 f {p | p 0 ∈ Icc a b} := hf.of_le (by norm_num)
  have hdcont (t : ℝ) (ht : t ∈ Icc a b) : Continuous (d t) := by
    have hfd := hf.fderivWithin (PDE.Analysis.uniqueDiffOn_closed_timeSlab hab)
      (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
    exact (hfd.contDiff_timeSlice ht).continuous.clm_apply continuous_const
  have hbound (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ^n) : ‖d t x‖ ≤ M := by
    calc
      _ ≤ ‖fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)‖ *
          ‖EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ M := by
        simpa only [PiLp.norm_single, norm_one, mul_one] using
          hone (timeSpaceCons t x) (by simpa using ht)
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : MemLp (d t) ∞ μ :=
    memLp_top_of_bound (hdcont t ht).aestronglyMeasurable M
      (Eventually.of_forall (hbound t ht))
  let D (t : ℝ) : Lp E ∞ μ := if ht : t ∈ Icc a b then (hmem t ht).toLp (d t) else 0
  have hrep (t : ℝ) (ht : t ∈ Icc a b) : (D t : ℝ^n → E) =ᵐ[μ] d t := by
    dsimp only [D]
    rw [dite_eq_left ht]
    exact (hmem t ht).coeFn_toLp
  have hdiff (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (x : ℝ^n) : ‖d s x - d t x‖ ≤ M * dist s t := by
    dsimp only [d]
    rw [← sub_apply]
    calc
      _ ≤ ‖fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons s x) -
          fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)‖ *
          ‖EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by
        simpa only [PiLp.norm_single, norm_one, mul_one, dist_eq_norm] using
          hf.norm_fderivWithin_timeSlice_sub_le hab htwo hs ht x
  refine ⟨D, ?_, ?_, hrep, ?_⟩
  · exact Lp.lipschitzOnWith_top_of_ae_norm_sub_le D d hrep
      (fun s hs t ht ↦ Eventually.of_forall (hdiff s hs t ht))
  · intro t ht
    apply Lp.norm_top_le_of_ae_bound M.coe_nonneg
    filter_upwards [hrep t ht] with x hx
    rw [hx]
    exact hbound t ht x
  · intro t ht
    apply hasDerivWithinAt_lp_top_of_ae_uniform_derivative ht F (D t)
      (fun s x ↦ f (timeSpaceCons s x)) d hF (hrep t ht)
    · apply Eventually.of_forall
      intro x s hs
      have hd := (hfone.differentiableOn_one (timeSpaceCons s x)
        (by simpa using hs)).hasFDerivWithinAt
      exact hd.comp_hasDerivWithinAt s
        (hasDerivAt_timeSpaceCons_time n s x).hasDerivWithinAt
        (fun r hr ↦ by simpa using hr)
    · intro ε hε
      refine ⟨ε / (M + 1), div_pos hε (by positivity), Eventually.of_forall ?_⟩
      intro x s hs hst
      calc
        ‖d s x - d t x‖ ≤ M * dist s t := hdiff s hs t ht x
        _ ≤ (M + 1) * dist s t :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
        _ ≤ ε := by
          exact (mul_comm (M + 1 : ℝ) (dist s t)).trans_le
            ((lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mp hst).le

end MeasureTheory
