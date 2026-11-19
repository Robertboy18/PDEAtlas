/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.Positive.LpComparison
public import PDE.Analysis.MeasureTheory.Lp.PositivePart
public import PDE.Analysis.FixedPoint.Schaefer

/-!
# Large positive perturbed eigenvectors

A compact positive operator with a nonzero positive subeigenvector has arbitrarily
large nonnegative perturbed eigenvectors. Applying Schaefer to the positive part
keeps the construction in the ambient `Lp` space. The parameter comparison excludes
fixed points of the rescaled map, so its homotopy solution set is unbounded.

This is step 4 of the proof of Evans, §6.5.2, Theorem 3: the set `S_ε` of his (28) is
unbounded. Evans works on the cone of nonnegative functions with the variant of Schaefer's
theorem for convex sets; we apply `PDE.FixedPoint.exists_isFixedPt_of_bounded_homotopy` on the
whole space to `u ↦ 2 M A (u⁺ + ε w)`, with the almost-everywhere order of Mathlib's `Lp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.2, Theorem 3, p. 361, step 4 of its proof, (28),
  p. 362. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory Set Bornology
open scoped ENNReal Topology

namespace ContinuousLinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive compactness and a positive subeigenvector produce perturbed eigenvectors
of arbitrarily large norm, with a uniformly bounded nonnegative parameter. -/
theorem exists_large_nonneg_perturbed_eigenvector
    (A : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (hcompact : IsCompactOperator A)
    (hA : ∀ v : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    {w : Lp ℝ p μ} {M ε : ℝ}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hw0 : w ≠ 0)
    (hM : 0 < M) (hsub : ∀ᵐ x ∂μ, w x ≤ M * A w x)
    (hε : 0 < ε) (R : ℝ) :
    ∃ (u : Lp ℝ p μ) (η : ℝ),
      R ≤ ‖u‖ ∧ (∀ᵐ x ∂μ, 0 ≤ u x) ∧ 0 ≤ η ∧ η < M ∧
        u = η • A (u + ε • w) := by
  let T : Lp ℝ p μ → Lp ℝ p μ := fun u ↦ (2 * M) • A (Lp.posPart u + ε • w)
  have hT : Continuous T :=
    (A.continuous.comp (Lp.continuous_posPart.add
      (continuous_const : Continuous (fun _ : Lp ℝ p μ ↦ ε • w)))).const_smul (2 * M)
  have hTC (s : Set (Lp ℝ p μ)) (hs : IsBounded s) :
      IsCompact (closure (T '' s)) := by
    obtain ⟨C, hC⟩ := hs.exists_norm_le
    have hs' : IsBounded ((fun u : Lp ℝ p μ ↦ Lp.posPart u + ε • w) '' s) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨C + ‖ε • w‖, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact (norm_add_le _ _).trans
        (add_le_add ((Lp.norm_posPart_le u).trans (hC u hu)) le_rfl)
    have hK := (hcompact.isCompact_closure_image_of_bounded
      (f := A.toLinearMap) hs').image
      (continuous_id.const_smul (2 * M))
    apply hK.closure_of_subset
    rintro _ ⟨u, hu, rfl⟩
    exact mem_image_of_mem _ (subset_closure
      (mem_image_of_mem A (mem_image_of_mem (fun v ↦ Lp.posPart v + ε • w) hu)))
  have hhom (u : Lp ℝ p μ) (t : ℝ) (ht : 0 ≤ t) (heq : u = t • T u) :
      (∀ᵐ x ∂μ, 0 ≤ u x) ∧ u = (t * (2 * M)) • A (u + ε • w) := by
    have hinput : ∀ᵐ x ∂μ, 0 ≤ (Lp.posPart u + ε • w) x := by
      filter_upwards [Lp.posPart_nonneg_ae u, hw, Lp.coeFn_add (Lp.posPart u) (ε • w),
        Lp.coeFn_smul ε w] with x hx hwx hadd hscale
      simpa only [hadd, hscale, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        add_nonneg hx (mul_nonneg hε.le hwx)
    have hAu := hA _ hinput
    have heq' : u = (t * (2 * M)) • A (Lp.posPart u + ε • w) := by
      simpa only [T, smul_smul] using heq
    have hu : ∀ᵐ x ∂μ, 0 ≤ u x := by
      filter_upwards [hAu, Lp.coeFn_smul (t * (2 * M)) (A (Lp.posPart u + ε • w))]
        with x hx hscale
      rw [congrArg (fun v : Lp ℝ p μ ↦ v x) heq', hscale]
      exact mul_nonneg (mul_nonneg ht (mul_nonneg zero_le_two hM.le)) hx
    exact ⟨hu, by rwa [(Lp.posPart_eq_self_iff u).mpr hu] at heq'⟩
  have hunbounded : ¬ IsBounded {u : Lp ℝ p μ | ∃ t ∈ Icc (0 : ℝ) 1, u = t • T u} := by
    intro hbound
    obtain ⟨u, hu⟩ := PDE.FixedPoint.exists_isFixedPt_of_bounded_homotopy hT hTC hbound
    have heq : u = (1 : ℝ) • T u := by simpa only [one_smul] using hu.symm
    obtain ⟨hnonneg, hperturbed⟩ := hhom u 1 zero_le_one heq
    have hlt := A.toLinearMap.parameter_lt_of_nonneg_perturbed_eigenvector hA
      hw hw0 hM hsub hε hnonneg hperturbed
    linarith
  have hex : ∃ u : Lp ℝ p μ,
      (∃ t ∈ Icc (0 : ℝ) 1, u = t • T u) ∧ R ≤ ‖u‖ := by
    by_contra hnot
    push Not at hnot
    exact hunbounded (isBounded_iff_forall_norm_le.mpr ⟨R, fun u hu ↦ (hnot u hu).le⟩)
  obtain ⟨u, ⟨t, ht, heq⟩, hnorm⟩ := hex
  obtain ⟨hu, hperturbed⟩ := hhom u t ht.1 heq
  refine ⟨u, t * (2 * M), hnorm, hu,
    mul_nonneg ht.1 (mul_nonneg zero_le_two hM.le), ?_, hperturbed⟩
  exact A.toLinearMap.parameter_lt_of_nonneg_perturbed_eigenvector hA
    hw hw0 hM hsub hε hu hperturbed

end ContinuousLinearMap
