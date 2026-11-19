/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import PDE.Analysis.MeasureTheory.Lp.CompactTimeCurve

/-!
# Finite families of time-dependent bounded coefficients

Apply the compact-cylinder construction to each entry of a finite family. The
finite product carries a common Lipschitz bound and the derivative obtained by
differentiating every entry. Summing the individual nonnegative bounds also
handles an empty family without a nonemptiness assumption.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open Set
open scoped ENNReal NNReal Topology

/-- Finitely many continuous coefficient fields and their time derivatives give a
single Lipschitz curve in the finite product of `L∞` spaces. The derivative is
identified in the product norm, and both curves have uniform bounds. -/
theorem exists_lp_top_family_with_derivative_of_continuousOn_compact
    {ι α E : Type*} [Fintype ι] [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    {a b : ℝ} (f fdot : ι → ℝ → α → E)
    (hf : ∀ i, ContinuousOn (Function.uncurry (f i)) (Icc a b ×ˢ K))
    (hfdot : ∀ i, ContinuousOn (Function.uncurry (fdot i)) (Icc a b ×ˢ K))
    (hderiv : ∀ i, ∀ x ∈ K, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ f i s x) (fdot i t x) (Icc a b) t) :
    ∃ (F D : ℝ → ι → Lp E ∞ μ) (M N : ℝ≥0),
      (∀ i t, t ∈ Icc a b → (F t i : α → E) =ᵐ[μ] f i t) ∧
      (∀ i t, t ∈ Icc a b → (D t i : α → E) =ᵐ[μ] fdot i t) ∧
      (∀ t ∈ Icc a b, ‖F t‖ ≤ M) ∧
      (∀ t ∈ Icc a b, ‖D t‖ ≤ N) ∧
      LipschitzOnWith N F (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt F (D t) (Icc a b) t) := by
  classical
  choose F D M N hF hD hLip hDeriv using fun i ↦
    exists_lp_top_curve_with_derivative_of_continuousOn_compact hK hμ
      (f i) (fdot i) (hf i) (hfdot i) (hderiv i)
  have hM (i : ι) : (M i : ℝ) ≤ ((∑ j, M j : ℝ≥0) : ℝ) := by
    exact NNReal.coe_mono
      (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  have hN (i : ι) : (N i : ℝ) ≤ ((∑ j, N j : ℝ≥0) : ℝ) := by
    exact NNReal.coe_mono
      (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  refine ⟨(fun t i ↦ F i t), (fun t i ↦ D i t), ∑ i, M i, ∑ i, N i,
    (fun i t ht ↦ (hF i t ht).1), (fun i t ht ↦ (hD i t ht).1), ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (pi_norm_le_iff_of_nonneg (NNReal.coe_nonneg _)).mpr
      fun i ↦ (hF i t ht).2.trans (hM i)
  · intro t ht
    exact (pi_norm_le_iff_of_nonneg (NNReal.coe_nonneg _)).mpr
      fun i ↦ (hD i t ht).2.trans (hN i)
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
    intro i
    simpa only [Pi.sub_apply, dist_eq_norm] using
      ((hLip i).dist_le_mul s hs t ht).trans
        (mul_le_mul_of_nonneg_right (hN i) dist_nonneg)
  · intro t ht
    exact hasDerivWithinAt_pi.mpr fun i ↦ hDeriv i t ht

/-- The compact-cylinder derivative construction applies to any represented finite
family of coefficient classes, and its derivative is itself norm continuous. -/
theorem exists_lp_top_family_derivative_of_representatives
    {ι α E : Type*} [Fintype ι] [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {K : Set α}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {a b : ℝ}
    (f fdot : ι → ℝ → α → E) (F : ℝ → ι → Lp E ∞ μ)
    (hf : ∀ i, ContinuousOn (Function.uncurry (f i)) (Icc a b ×ˢ K))
    (hfdot : ∀ i, ContinuousOn (Function.uncurry (fdot i)) (Icc a b ×ˢ K))
    (hderiv : ∀ i, ∀ x ∈ K, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ f i s x) (fdot i t x) (Icc a b) t)
    (hrep : ∀ i, ∀ t ∈ Icc a b, (F t i : α → E) =ᵐ[μ] f i t) :
    ∃ (D : ℝ → ι → Lp E ∞ μ) (N : ℝ≥0),
      ContinuousOn D (Icc a b) ∧
      (∀ t ∈ Icc a b, ‖D t‖ ≤ N) ∧
      LipschitzOnWith N F (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt F (D t) (Icc a b) t := by
  obtain ⟨G, D, _, N, hGrep, hDrep, _, hDbound, hGLip, hGderiv⟩ :=
    exists_lp_top_family_with_derivative_of_continuousOn_compact
      hK hμ f fdot hf hfdot hderiv
  have hFG : EqOn F G (Icc a b) := by
    intro t ht
    funext i
    exact Lp.ext ((hrep i t ht).trans (hGrep i t ht).symm)
  refine ⟨D, N, continuousOn_pi.mpr (fun i ↦ ?_), hDbound, ?_, ?_⟩
  · exact continuousOn_lp_top_of_continuousOn_compact hK hμ (fdot i)
      (fun t ↦ D t i) (hfdot i) (hDrep i)
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [hFG hs, hFG ht]
    exact hGLip.dist_le_mul s hs t ht
  · intro t ht
    exact (hGderiv t ht).congr_of_mem (fun s hs ↦ hFG hs) ht

end MeasureTheory
