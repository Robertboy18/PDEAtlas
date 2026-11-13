/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.Bounds
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Lipschitz
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.InfiniteExponent

/-!
# The full Lipschitz endpoint of Morrey embedding

The bounded weak-gradient theorem supplies a Lipschitz representative. Its essential
bound becomes a pointwise bound by continuity and positivity of Lebesgue measure on
open sets. Thus the full norm, including the uniform term, is bounded by the Sobolev
norm. No compact support or approximation in the W¹,∞ norm is required.

This is the case `p = ∞` of Morrey's inequality (Evans §5.6.2, Theorem 4), for all of
`W^{1,∞}(ℝ^n)` rather than `C¹(ℝ^n)`; it is the whole-space form of the case `p = ∞` of Theorem 5,
which Evans leaves as easy to prove directly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorems 4 and 5, pp. 280-284.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace

variable {n : ℕ}

/-- A continuous function with finite essential supremum obeys that bound everywhere. -/
theorem norm_apply_le_eLpNorm_top_of_continuous
    {f : ℝ^n → ℝ} (hf : Continuous f)
    (hfinite : eLpNorm f ∞ volume ≠ ∞) (x : ℝ^n) :
    ‖f x‖ ≤ (eLpNorm f ∞ volume).toReal := by
  have hae : ∀ᵐ y ∂volume, ‖f y‖ ≤ (eLpNorm f ∞ volume).toReal := by
    have hbound := ae_le_eLpNormEssSup (f := f) (μ := volume)
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable] at hbound
    filter_upwards [hbound] with y hy
    simpa using ENNReal.toReal_mono hfinite hy
  have hd := (volume : Measure (ℝ^n)).dense_of_ae hae
  exact (isClosed_le hf.norm continuous_const).closure_subset (hd x)

/-- If `f` is `C¹` on `ℝ^n` with `f` and `Df` essentially bounded, then `f` defines an element
`F` of `C^{0,1}(ℝ^n)` with `‖F‖ ≤ ‖f‖_{L∞} + ‖Df‖_{L∞}`. -/
theorem exists_holder_one_of_contDiff
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ 1 f)
    (hbase : MemLp f ∞ volume) (hderiv : MemLp (fderiv ℝ f) ∞ volume) :
    ∃ F : HolderSpace.C0GammaOn (ℝ^n) 1,
      (∀ x, F x = f x) ∧
      ‖F‖ ≤ (eLpNorm f ∞ volume).toReal +
        (eLpNorm (fderiv ℝ f) ∞ volume).toReal := by
  have hLip : LipschitzWith (eLpNorm (fderiv ℝ f) ∞ volume).toNNReal f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, Real.norm_eq_abs, ENNReal.coe_toNNReal_eq_toReal] using
      norm_sub_le_eLpNorm_fderiv_top_toReal_mul_norm f hf hderiv.eLpNorm_ne_top y x
  let F := HolderSpace.C0GammaOn.ofBound (γ := 1) f hLip.holderWith
    (eLpNorm f ∞ volume).toReal
    (norm_apply_le_eLpNorm_top_of_continuous hf.continuous hbase.eLpNorm_ne_top)
  refine ⟨F, fun _ ↦ rfl, ?_⟩
  simpa only [F, ENNReal.coe_toNNReal_eq_toReal] using
    HolderSpace.C0GammaOn.norm_ofBound_le (γ := 1) f hLip.holderWith ENNReal.toReal_nonneg
      (norm_apply_le_eLpNorm_top_of_continuous hf.continuous hbase.eLpNorm_ne_top)

namespace GraphSpace

/-- Every `U ∈ W^{1,∞}(ℝ^n)` has a representative `F ∈ C^{0,1}(ℝ^n)`, equal almost everywhere
to the base representative of `U`, with `‖F‖ ≤ (n + 1) ‖U‖`. -/
theorem WkpSpaceOn.exists_holder_one_representative (U : W^{1,∞}(ℝ^n)) :
    ∃ F : HolderSpace.C0GammaOn (ℝ^n) 1,
      (fun x ↦ F x) =ᵐ[volume] baseRepresentative U ∧
      ‖F‖ ≤ ((n : ℝ) + 1) * ‖U‖ := by
  obtain ⟨v, hv, heq⟩ := U.exists_lipschitzWith_baseRepresentative
  have hnorm :
      (eLpNorm v ∞ volume).toReal =
        ‖(U : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖ := by
    rw [eLpNorm_congr_ae heq, Lp.norm_def]
    simp only [baseRepresentative, domainMeasure, Measure.restrict_univ]
  have hmem : MemLp v ∞ volume := by
    apply (memLp_congr_ae heq).mpr
    simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using
      (Lp.memLp ((U : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)))
  have hbound (x : ℝ^n) : ‖v x‖ ≤ ‖U‖ := by
    calc
      ‖v x‖ ≤ (eLpNorm v ∞ volume).toReal :=
        norm_apply_le_eLpNorm_top_of_continuous hv.continuous hmem.eLpNorm_ne_top x
      _ = _ := hnorm
      _ ≤ ‖U‖ := PiLp.norm_apply_le _ _
  let F := HolderSpace.C0GammaOn.ofBound (γ := 1) v hv.holderWith ‖U‖ hbound
  refine ⟨F, heq, ?_⟩
  have hsum :
      ((∑ j : Fin n,
        ‖(U : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖₊ : ℝ≥0) : ℝ) ≤
        n * ‖U‖ := by
    rw [NNReal.coe_sum]
    calc
      ∑ j : Fin n, (‖(U : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖₊ : ℝ)
          ≤ ∑ _ : Fin n, ‖U‖ :=
        Finset.sum_le_sum fun _ _ ↦ PiLp.norm_apply_le _ _
      _ = n * ‖U‖ := by simp
  calc
    ‖F‖ ≤ ‖U‖ +
        ((∑ j : Fin n,
          ‖(U : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖₊ : ℝ≥0) : ℝ) :=
      HolderSpace.C0GammaOn.norm_ofBound_le v hv.holderWith (norm_nonneg U) hbound
    _ ≤ ‖U‖ + n * ‖U‖ := add_le_add (le_refl _) hsum
    _ = ((n : ℝ) + 1) * ‖U‖ := by ring

end GraphSpace

end SobolevSpace
