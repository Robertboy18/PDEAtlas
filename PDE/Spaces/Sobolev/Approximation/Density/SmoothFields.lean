/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.FDeriv.PartialDeriv.HigherNorm
import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeCoordinates

/-!
# Whole-space Sobolev elements from smooth functions

A smooth function on `ℝ^n` whose Fréchet derivatives of order at most `k` lie in `Lᵖ(ℝ^n)`
defines an element of `W^{k,p}(ℝ^n)`, because every coordinate word of partial derivatives is
bounded pointwise by the full derivative of the same order. For `p = ∞` it is enough that these
derivatives are bounded. The components of a smooth vector field on `ℝ^n` give coefficients for
the Sobolev multipliers and transport operators, with the values of the field and its classical
partial derivatives as base representatives.

## Main results

* `memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv`, `memLp_top_iteratedFDeriv_of_bound` and
  `norm_iteratedFDeriv_component_le`, facts about smooth functions on `ℝ^n`.
* `wkpOfContDiff`, with `wkpOfContDiff_apply_ae`, `baseRepresentative_wkpOfContDiff` and
  `baseRepresentative_partialDerivCLM_wkpOfContDiff`.
* `vectorWkpOfContDiff`, the components of a smooth vector field, with
  `baseRepresentative_vectorWkpOfContDiff` and
  `baseRepresentative_partialDerivCLM_vectorWkpOfContDiff`.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : ℝ≥0∞}

namespace PDE

/-- A coordinate word of partial derivatives of a smooth function inherits `Lᵖ` membership from
the full derivative of the same order. -/
theorem memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv {μ : Measure (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin n))
    (h : MemLp (iteratedFDeriv ℝ α.length f) p μ) :
    MemLp (fun x ↦ iteratedPartialDeriv α f x) p μ :=
  h.of_le (contDiff_top_iteratedPartialDeriv hf α).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦
      norm_iteratedPartialDeriv_le_norm_iteratedFDeriv α (hf.contDiffAt.of_le (by
        exact_mod_cast le_top)))

/-- If every derivative word of length `k` of a smooth function is in `Lᵖ`, so is the sum of
their norms. -/
theorem memLp_iteratedCoordinateNormSum {μ : Measure (ℝ^n)} :
    ∀ (k : ℕ) {f : ℝ^n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ α : List (Fin n), α.length = k → MemLp (fun x ↦ iteratedPartialDeriv α f x) p μ) →
      MemLp (iteratedCoordinateNormSum k f) p μ
  | 0, f, _, h => by
      simpa [iteratedCoordinateNormSum, iteratedPartialDeriv] using (h [] rfl).norm
  | k + 1, f, hf, h => by
      change MemLp (fun x ↦ ∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x) p μ
      refine memLp_finsetSum _ fun i _ ↦ ?_
      refine memLp_iteratedCoordinateNormSum k (contDiff_top_partialDeriv hf) fun α hα ↦ ?_
      have h' := h (α ++ [i]) (by simp [hα])
      simpa only [iteratedPartialDeriv_append_single] using h'

/-- Conversely to `memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv`, a smooth function whose
derivative words of length `k` are in `Lᵖ` has its `k`-th Fréchet derivative in `Lᵖ`. -/
theorem memLp_iteratedFDeriv_of_memLp_iteratedPartialDeriv {μ : Measure (ℝ^n)}
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ)
    (h : ∀ α : List (Fin n), α.length = k → MemLp (fun x ↦ iteratedPartialDeriv α f x) p μ) :
    MemLp (iteratedFDeriv ℝ k f) p μ :=
  (memLp_iteratedCoordinateNormSum k hf h).of_le
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (iteratedCoordinateNormSum_nonneg k f x)]
      exact norm_iteratedFDeriv_le_iteratedCoordinateNormSum k
        (hf.contDiffAt.of_le (by exact_mod_cast le_top)))

/-- Bounded derivatives of a smooth function are essentially bounded. -/
theorem memLp_top_iteratedFDeriv_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure (ℝ^n)} {f : ℝ^n → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) :
    MemLp (iteratedFDeriv ℝ m f) ⊤ μ :=
  memLp_top_of_bound (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
    C (Filter.Eventually.of_forall hC)

/-- The derivatives of a component of a smooth vector field are bounded by those of the field. -/
theorem norm_iteratedFDeriv_component_le {U : ℝ^n → ℝ^n} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (i : Fin n) (m : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (fun y ↦ U y i) x‖ ≤ ‖iteratedFDeriv ℝ m U x‖ := by
  have hproj : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      simpa using PiLp.norm_apply_le v i
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).norm_iteratedFDeriv_comp_left (x := x) (n := m)
    hU.contDiffAt (by exact_mod_cast le_top)
  calc
    _ = ‖iteratedFDeriv ℝ m (EuclideanSpace.proj (𝕜 := ℝ) i ∘ U) x‖ := rfl
    _ ≤ ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ * ‖iteratedFDeriv ℝ m U x‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ m U x‖ := by gcongr
    _ = _ := one_mul _

end PDE

namespace SobolevSpace.GraphSpace

/-- A smooth function on `ℝ^n` whose derivatives of order at most `k` lie in `Lᵖ(ℝ^n)`, as an
element of `W^{k,p}(ℝ^n)`. -/
def wkpOfContDiff (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p volume) : W^{k,p}(ℝ^n) :=
  mkWkpSpaceOnOfContDiffMemLp f hf fun a ↦
    PDE.memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv hf a.toList
      ((hmem a.toList.length a.toList_length_le).restrict Set.univ)

/-- Every derivative coordinate is the classical iterated partial derivative almost
everywhere. -/
theorem wkpOfContDiff_apply_ae (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p volume) (a : DerivIndex n k) :
    (((wkpOfContDiff f hf hmem : W^{k,p}(ℝ^n)) : WkpAmbientOn n k p Set.univ) a : ℝ^n → ℝ)
      =ᵐ[volume] fun x ↦ iteratedPartialDeriv a.toList f x := by
  have h := mkWkpSpaceOnOfContDiffMemLp_apply_ae (n := n) (k := k) (p := p) (Ω := Set.univ) f hf
    (fun a ↦ PDE.memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv hf a.toList
      ((hmem a.toList.length a.toList_length_le).restrict Set.univ)) a
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The base representative is the function almost everywhere. -/
theorem baseRepresentative_wkpOfContDiff (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p volume) :
    baseRepresentative (wkpOfContDiff f hf hmem) =ᵐ[volume] f := by
  have h := wkpOfContDiff_apply_ae f hf hmem (baseIndex n k)
  rw [baseIndex_toList] at h
  exact h

/-- The base representative of a weak partial derivative is the classical partial derivative
almost everywhere. -/
theorem baseRepresentative_partialDerivCLM_wkpOfContDiff [Fact (1 ≤ p)] (i : Fin n)
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m f) p volume) :
    baseRepresentative (partialDerivCLM i (wkpOfContDiff f hf hmem)) =ᵐ[volume]
      fun x ↦ PDE.partialDeriv i f x := by
  rw [baseRepresentative_partialDerivCLM]
  have h := wkpOfContDiff_apply_ae f hf hmem (firstDerivIndex n (k + 1) (Nat.succ_pos k) i)
  rw [firstDerivIndex_toList] at h
  exact h

/-- The components of a smooth vector field on `ℝ^n` whose derivatives of order at most `k`
lie in `Lᵖ(ℝ^n)`, as elements of `W^{k,p}(ℝ^n)`. -/
def vectorWkpOfContDiff (U : ℝ^n → ℝ^n) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m U) p volume) : Fin n → W^{k,p}(ℝ^n) :=
  fun i ↦ wkpOfContDiff (fun x ↦ U x i) ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hU)
    fun m hm ↦ (hmem m hm).of_le
      ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hU).continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le hU i m x)

/-- The base representatives of the components are the components of the field almost
everywhere. -/
theorem baseRepresentative_vectorWkpOfContDiff (U : ℝ^n → ℝ^n) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m U) p volume) (i : Fin n) :
    baseRepresentative (vectorWkpOfContDiff U hU hmem i) =ᵐ[volume] fun x ↦ U x i :=
  baseRepresentative_wkpOfContDiff _ _ _

/-- The base representative of `∂ⱼ` of the `i`-th component is the `i`-th component of the
classical partial derivative `∂ⱼU` almost everywhere. -/
theorem baseRepresentative_partialDerivCLM_vectorWkpOfContDiff [Fact (1 ≤ p)]
    (U : ℝ^n → ℝ^n) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m U) p volume) (i j : Fin n) :
    baseRepresentative (partialDerivCLM j (vectorWkpOfContDiff U hU hmem i)) =ᵐ[volume]
      fun x ↦ fderiv ℝ U x (EuclideanSpace.single j 1) i := by
  unfold vectorWkpOfContDiff
  refine (baseRepresentative_partialDerivCLM_wkpOfContDiff (p := p) j _ _ _).trans
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hd : HasFDerivAt (fun y ↦ U y i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ U x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
      ((hU.differentiable (by simp)) x).hasFDerivAt
  change fderiv ℝ (fun y ↦ U y i) x (EuclideanSpace.single j 1) = _
  rw [hd.fderiv]
  rfl

end SobolevSpace.GraphSpace
