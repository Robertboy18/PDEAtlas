/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Heat evolution in a Hilbert spectral basis

Nonnegative eigenvalues define a contraction evolution for every vector in a Hilbert
space. Its eigenfunction series converges in Hilbert norm and attains the initial vector
in that norm. The construction uses square summability furnished by the Hilbert basis;
absolute summability of coefficients is not an input.

All statements are in the norm topology of the Hilbert space.
-/

@[expose] public section

namespace HeatEquation

open Filter
open scoped Topology NNReal ENNReal lp

variable {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The damped coordinates of an arbitrary Hilbert-space vector. Nonnegative time is
encoded in the time type so that the coordinate map is always a contraction. -/
noncomputable def spectralHeatCoefficients (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (t : ℝ≥0) : ℓ²(ι, 𝕜) :=
  ⟨fun i ↦ (Real.exp (-lambda i * t) : 𝕜) * b.repr f i,
    (lp.memℓp (b.repr f)).mono' fun i ↦ by
      rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hlambda i)) t.2))⟩

/-- The heat evolution defined by damping Hilbert-basis coordinates and reconstructing. -/
noncomputable def spectralHeatEvolution (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (t : ℝ≥0) : H :=
  b.repr.symm (spectralHeatCoefficients b lambda hlambda f t)

/-- Each spectral coordinate is damped by its corresponding heat multiplier. -/
@[simp] theorem spectralHeatEvolution_repr (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (t : ℝ≥0) (i : ι) :
    b.repr (spectralHeatEvolution b lambda hlambda f t) i =
      (Real.exp (-lambda i * t) : 𝕜) * b.repr f i := by
  simp [spectralHeatEvolution, spectralHeatCoefficients]

/-- The heat series converges in the Hilbert norm for every initial vector, including
at time zero. No pointwise interpretation of the basis vectors is needed. -/
theorem hasSum_spectralHeatEvolution (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (t : ℝ≥0) :
    HasSum (fun i ↦ ((Real.exp (-lambda i * t) : 𝕜) * b.repr f i) • b i)
      (spectralHeatEvolution b lambda hlambda f t) :=
  b.hasSum_repr_symm (spectralHeatCoefficients b lambda hlambda f t)

/-- Heat damping decreases the Hilbert norm. -/
theorem norm_spectralHeatEvolution_le (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (t : ℝ≥0) :
    ‖spectralHeatEvolution b lambda hlambda f t‖ ≤ ‖f‖ := by
  rw [spectralHeatEvolution, b.repr.symm.norm_map, ← b.repr.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  change ‖(Real.exp (-lambda i * t) : 𝕜) * b.repr f i‖ ≤ ‖b.repr f i‖
  rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hlambda i)) t.2))

/-- At time zero the spectral construction is exactly the initial vector. -/
@[simp] theorem spectralHeatEvolution_zero (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) :
    spectralHeatEvolution b lambda hlambda f 0 = f := by
  apply b.repr.injective
  ext i
  simp

/-- The spectral evolution has the semigroup property. -/
theorem spectralHeatEvolution_add (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (s t : ℝ≥0) :
    spectralHeatEvolution b lambda hlambda f (s + t) =
      spectralHeatEvolution b lambda hlambda (spectralHeatEvolution b lambda hlambda f t) s := by
  apply b.repr.injective
  ext i
  simp only [spectralHeatEvolution_repr, NNReal.coe_add, mul_add, Real.exp_add,
    RCLike.ofReal_mul, mul_assoc]

/-- Parseval expresses the squared distance between two times as a summable scalar series. -/
theorem norm_spectralHeatEvolution_sub_sq (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) (s t : ℝ≥0) :
    ‖spectralHeatEvolution b lambda hlambda f t -
        spectralHeatEvolution b lambda hlambda f s‖ ^ 2 =
      ∑' i, ‖(Real.exp (-lambda i * t) : 𝕜) * b.repr f i -
        (Real.exp (-lambda i * s) : 𝕜) * b.repr f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (b.repr (spectralHeatEvolution b lambda hlambda f t -
      spectralHeatEvolution b lambda hlambda f s))
  rw [b.repr.norm_map] at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, map_sub,
    lp.coeFn_sub, Pi.sub_apply, spectralHeatEvolution_repr] using h

/-- The evolution is strongly continuous on nonnegative time, including at time zero.
The dominating series is supplied by square summability of the initial coordinates. -/
theorem continuous_spectralHeatEvolution (b : HilbertBasis ι 𝕜 H) (lambda : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (f : H) :
    Continuous (spectralHeatEvolution b lambda hlambda f) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hsum : Summable (fun i ↦ ‖b.repr f i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (b.repr f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hbound (t : ℝ≥0) (i : ι) :
      ‖‖(Real.exp (-lambda i * t) : 𝕜) * b.repr f i -
        (Real.exp (-lambda i * s) : 𝕜) * b.repr f i‖ ^ 2‖ ≤
        ‖b.repr f i‖ ^ 2 := by
    have he : Real.exp (-lambda i * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hlambda i)) t.2)
    have hes : Real.exp (-lambda i * s) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hlambda i)) s.2)
    have hnorm : ‖(Real.exp (-lambda i * t) : 𝕜) -
        (Real.exp (-lambda i * s) : 𝕜)‖ ≤ 1 := by
      rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
      exact abs_le.mpr ⟨by linarith [Real.exp_pos (-lambda i * t)],
        by linarith [Real.exp_pos (-lambda i * s)]⟩
    rw [Real.norm_of_nonneg (sq_nonneg _),
      ← sub_mul, norm_mul]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) hnorm) 2
  have ht : Tendsto
      (fun t : ℝ≥0 ↦ ∑' i, ‖(Real.exp (-lambda i * t) : 𝕜) * b.repr f i -
        (Real.exp (-lambda i * s) : 𝕜) * b.repr f i‖ ^ 2)
      (𝓝 s) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 s) hsum
      (fun i ↦ (show Continuous (fun t : ℝ≥0 ↦
        ‖(Real.exp (-lambda i * t) : 𝕜) * b.repr f i -
          (Real.exp (-lambda i * s) : 𝕜) * b.repr f i‖ ^ 2) from by
          fun_prop).continuousAt.tendsto)
      (Filter.Eventually.of_forall hbound)
    simpa using h
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have he := (tendsto_order.1 ht).2 (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [he] with t ht
  rw [← norm_spectralHeatEvolution_sub_sq b lambda hlambda f s t] at ht
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (spectralHeatEvolution b lambda hlambda f t -
    spectralHeatEvolution b lambda hlambda f s)]

end HeatEquation
