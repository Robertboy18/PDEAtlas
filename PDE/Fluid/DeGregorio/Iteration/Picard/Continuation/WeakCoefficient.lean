/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakLocalization
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Time-dependent compact transport coefficients

A compact C¹ real drift defines a W¹,∞ coefficient in the Euclidean model.
Uniform convergence of the real drifts on their common support gives continuity
of the L∞ base row. The spatial derivative row is only required to be uniformly
bounded.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace DeGregorio.Iteration

local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)

/-- The real derivative is the sole coordinate derivative after pullback. -/
theorem partialDeriv_comp_equivOfUnique {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 1) (x : ℝ^1) :
    (∂[i] (f ∘ (e))) x = deriv f ((e) x) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h := PDE.deriv_comp_equivOfUnique_symm (f ∘ (e)) ((e) x)
    ((hf.comp (e).contDiff).differentiable one_ne_zero _)
  have heq : (f ∘ (e)) ∘ (e).symm = f := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [heq, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- The derivative rows of a compact C¹ drift are bounded and measurable. -/
theorem memLp_compact_drift_rows {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (d : DerivIndex 1 1) :
    MemLp (iteratedPartialDeriv d.toList (f ∘ (e))) ∞ (domainMeasure 1 univ) := by
  have hb := hf.continuous.memLp_of_hasCompactSupport hc (p := ∞) (μ := volume)
  have hd := (hf.continuous_deriv le_rfl).memLp_of_hasCompactSupport hc.deriv
    (p := ∞) (μ := volume)
  have hmp : MeasurePreserving (e) (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    measurePreserving_equivOfUnique_symm.symm (e).symm.toHomeomorph.toMeasurableEquiv
  simp only [domainMeasure, Measure.restrict_univ]
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with h | ⟨i, h⟩
  · subst d
    simpa only [baseIndex_toList, iteratedPartialDeriv] using hb.comp_measurePreserving hmp
  · subst d
    simp only [singleDerivIndex_toList, iteratedPartialDeriv,
      partialDeriv_comp_equivOfUnique hf]
    exact hd.comp_measurePreserving hmp

/-- The Sobolev multiplier corresponding to a compact C¹ real drift. -/
def compactDriftW1Top (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    W^{1,∞}((univ : Set (ℝ^1))) :=
  mkWkpSpaceOnOfContDiffMemLpFinite (f ∘ (e)) (hf.comp (e).contDiff)
    (memLp_compact_drift_rows hf hc)

/-- The base row represents the original compact drift. -/
theorem compactDriftW1Top_base_ae (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ((compactDriftW1Top f hf hc : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) : ℝ^1 → ℝ)
      =ᵐ[domainMeasure 1 univ] f ∘ (e) := by
  simpa only [compactDriftW1Top, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae (f ∘ (e)) (hf.comp (e).contDiff)
      (memLp_compact_drift_rows hf hc) (baseIndex 1 1)

/-- The derivative row represents the real derivative. -/
theorem compactDriftW1Top_derivative_ae (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ((compactDriftW1Top f hf hc : WkpAmbientOn 1 1 ∞ univ)
      (singleDerivIndex 1 0) : ℝ^1 → ℝ)
      =ᵐ[domainMeasure 1 univ] deriv f ∘ (e) := by
  have h := mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae (f ∘ (e)) (hf.comp (e).contDiff)
    (memLp_compact_drift_rows hf hc) (singleDerivIndex 1 0)
  simp only [singleDerivIndex_toList, iteratedPartialDeriv] at h
  filter_upwards [h] with x hx
  exact hx.trans (partialDeriv_comp_equivOfUnique hf 0 x)

/-- A uniform bound on the real derivative bounds the weak coefficient row. -/
theorem norm_compactDriftW1Top_derivative_le (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {L : ℝ}
    (hbound : ∀ x, ‖deriv f x‖ ≤ L) :
    ‖(compactDriftW1Top f hf hc : WkpAmbientOn 1 1 ∞ univ)
      (singleDerivIndex 1 0)‖ ≤ L := by
  apply Lp.norm_top_le_of_ae_bound ((norm_nonneg _).trans (hbound 0))
  filter_upwards [compactDriftW1Top_derivative_ae f hf hc] with x hx
  rw [hx]
  exact hbound _

/-- A common spatial support and uniform convergence on that support imply
continuity of the corresponding L∞ classes, also for an infinite measure. -/
theorem continuousOn_lpTop_of_common_support
    {a b : ℝ} {K : Set ℝ} {f : ℝ → ℝ → ℝ}
    {A : ℝ → DerivLp 1 ∞ univ}
    (hrep : ∀ t ∈ Icc a b, (A t : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 univ] f t ∘ (e))
    (hsupp : ∀ t ∈ Icc a b, ∀ x ∉ K, f t x = 0)
    (hconv : ∀ t ∈ Icc a b, TendstoUniformlyOn f (f t) (𝓝[Icc a b] t) K) :
    ContinuousOn A (Icc a b) := by
  intro t ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp (hconv t ht) (ε / 2) (half_pos hε)
  filter_upwards [he, self_mem_nhdsWithin] with s hs hst
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply Lp.norm_top_le_of_ae_bound (half_pos hε).le
  filter_upwards [Lp.coeFn_sub (A s) (A t), hrep s hst, hrep t ht] with x hx hsx htx
  simp only [hx, Pi.sub_apply, hsx, htx, Function.comp_apply]
  by_cases hKx : (e) x ∈ K
  · apply le_of_lt
    rw [← dist_eq_norm, dist_comm]
    exact hs ((e) x) hKx
  · rw [hsupp s hst _ hKx, hsupp t ht _ hKx, sub_self, norm_zero]
    exact (half_pos hε).le

/-- A family of compact C¹ drifts with common support yields the exact
coefficient regularity required by the Bochner transport energy theorem. -/
theorem exists_compact_w1Top_curve
    {a b : ℝ} {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 1 (f t))
    (hsupp : ∀ t ∈ Icc a b, tsupport (f t) ⊆ K)
    (hconv : ∀ t ∈ Icc a b, TendstoUniformlyOn f (f t) (𝓝[Icc a b] t) K)
    (L : NNReal) (hL : ∀ t ∈ Icc a b, ∀ x, ‖deriv (f t) x‖ ≤ L) :
    ∃ A : ℝ → W^{1,∞}((univ : Set (ℝ^1))),
      ContinuousOn (fun t ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1)) (Icc a b) ∧
      ∀ t ∈ Icc a b,
        ‖(A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0)‖ ≤ L ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) ((e).symm x))
          =ᵐ[volume] f t ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
          =ᵐ[volume] deriv (f t) := by
  classical
  have hc (t : ℝ) (ht : t ∈ Icc a b) : HasCompactSupport (f t) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hsupp t ht)
  let A := fun t ↦ if ht : t ∈ Icc a b then compactDriftW1Top (f t) (hf t ht) (hc t ht)
    else 0
  have hbase (t : ℝ) (ht : t ∈ Icc a b) :
      ((A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) : ℝ^1 → ℝ)
        =ᵐ[domainMeasure 1 univ] f t ∘ (e) := by
    simpa only [A, dite_eq_left ht] using compactDriftW1Top_base_ae (f t) (hf t ht) (hc t ht)
  refine ⟨A, continuousOn_lpTop_of_common_support hbase
    (fun t ht x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp t ht h)) hconv, ?_⟩
  intro t ht
  have hd := compactDriftW1Top_derivative_ae (f t) (hf t ht) (hc t ht)
  have hb := hbase t ht
  simp only [domainMeasure, Measure.restrict_univ] at hb hd
  refine ⟨?_, ?_, ?_⟩
  · simpa only [A, dite_eq_left ht] using
      norm_compactDriftW1Top_derivative_le (f t) (hf t ht) (hc t ht) (hL t ht)
  · simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
      measurePreserving_equivOfUnique_symm.quasiMeasurePreserving.ae_eq_comp hb
  · simpa only [A, dite_eq_left ht, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply]
      using measurePreserving_equivOfUnique_symm.quasiMeasurePreserving.ae_eq_comp hd

/-- A single compact cutoff localizes a linearly growing transport drift for
an entire time slab. Local uniform time continuity of the drift gives L∞
continuity of the coefficient; the derivative needs only a uniform bound. -/
theorem exists_localized_w1Top_curve
    {a b : ℝ} {K : Set ℝ} (hK : IsCompact K) {V : ℝ → ℝ → ℝ}
    (hV : ∀ t ∈ Icc a b, ContDiff ℝ 1 (V t))
    (hconv : ∀ D : Set ℝ, IsCompact D → ∀ t ∈ Icc a b,
      TendstoUniformlyOn V (V t) (𝓝[Icc a b] t) D)
    (D : NNReal)
    (hbound : ∀ t ∈ Icc a b, ∀ x,
      ‖V t x‖ ≤ D * |x| ∧ ‖deriv (V t) x‖ ≤ D) :
    ∃ (f : ℝ → ℝ → ℝ) (L : NNReal)
      (A : ℝ → W^{1,∞}((univ : Set (ℝ^1)))),
      ContinuousOn (fun t ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1)) (Icc a b) ∧
      ∀ t ∈ Icc a b,
        ‖(A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0)‖ ≤ L ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) ((e).symm x))
          =ᵐ[volume] f t ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
          =ᵐ[volume] deriv (f t) ∧
        EqOn (f t) (V t) K ∧ EqOn (deriv (f t)) (deriv (V t)) K := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  let χ : ContDiffBump (0 : ℝ) := ⟨r, r + 1, hr, lt_add_one r⟩
  let f := fun t x ↦ χ x * V t x
  have hf (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (f t) :=
    χ.contDiff.mul (hV t ht)
  have heq (t x : ℝ) (hx : x ∈ K) : f t =ᶠ[𝓝 x] V t := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball (hKr hx)] with y hy
    change χ y * V t y = V t y
    rw [show χ y = 1 from hy, one_mul]
  let P := fun x ↦ ‖deriv χ x‖ * ((D : ℝ) * |x|) + ‖χ x‖ * D
  have hPc : Continuous P := by
    exact (((χ.contDiff (n := 1)).continuous_deriv le_rfl).norm.mul
      (continuous_const.mul continuous_abs)).add (χ.continuous.norm.mul continuous_const)
  have hPs : HasCompactSupport P :=
    (χ.hasCompactSupport.deriv.norm.mul_right).add (χ.hasCompactSupport.norm.mul_right)
  obtain ⟨M, hM⟩ := hPc.bounded_above_of_compact_support hPs
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      ‖deriv (f t) x‖ ≤ M.toNNReal := by
    have hd := (((χ.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt.mul
      ((hV t ht).differentiable one_ne_zero x).hasDerivAt).deriv
    change deriv (f t) x = deriv χ x * V t x + χ x * deriv (V t) x at hd
    rw [hd]
    calc
      ‖deriv χ x * V t x + χ x * deriv (V t) x‖ ≤
          ‖deriv χ x‖ * ‖V t x‖ + ‖χ x‖ * ‖deriv (V t) x‖ := by
        simpa only [norm_mul] using norm_add_le (deriv χ x * V t x) (χ x * deriv (V t) x)
      _ ≤ P x := add_le_add
        (mul_le_mul_of_nonneg_left (hbound t ht x).1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hbound t ht x).2 (norm_nonneg _))
      _ ≤ ‖P x‖ := le_abs_self _
      _ ≤ M.toNNReal := (hM x).trans (Real.le_coe_toNNReal M)
  have hfconv (t : ℝ) (ht : t ∈ Icc a b) :
      TendstoUniformlyOn f (f t) (𝓝[Icc a b] t) (tsupport χ) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hconv (tsupport χ) χ.hasCompactSupport t ht) ε hε] with s hs
    intro x hx
    rw [dist_eq_norm]
    change ‖χ x * V t x - χ x * V s x‖ < ε
    rw [← mul_sub, norm_mul]
    calc
      ‖χ x‖ * ‖V t x - V s x‖ ≤ 1 * ‖V t x - V s x‖ :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs, abs_of_nonneg χ.nonneg] using χ.le_one (x := x))
          (norm_nonneg _)
      _ < ε := by simpa only [one_mul, ← dist_eq_norm] using hs x hx
  obtain ⟨A, hAc, hA⟩ := exists_compact_w1Top_curve χ.hasCompactSupport hf
    (fun _ _ ↦ tsupport_mul_subset_left) hfconv M.toNNReal hderiv
  refine ⟨f, M.toNNReal, A, hAc, ?_⟩
  intro t ht
  exact ⟨(hA t ht).1, (hA t ht).2.1, (hA t ht).2.2,
    fun x hx ↦ (heq t x hx).eq_of_nhds, fun x hx ↦ (heq t x hx).deriv_eq⟩

end DeGregorio.Iteration
