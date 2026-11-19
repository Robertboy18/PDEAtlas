/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceClass
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.HilbertEmbedding
public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Canonical
public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrderAssembly
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeCoordinates
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.FDeriv.Euclidean.Components
import PDE.Spaces.Sobolev.Calculus.Product.SmoothInterpolation

/-!
# Regularity of whole-space Sobolev classes

An element `U` of `W^{k+1,p}(ℝⁿ)` integrates by parts against smooth compactly supported
functions with its weak partial derivatives `∂ⱼU` (`integral_baseRepresentative_mul_partialDeriv`).
If every `∂ⱼU` of an element of `W^{m+1,2}(ℝⁿ)` has a realization in `W^{m+1,2}(ℝⁿ)`, the class of
`U` has a realization in `W^{m+2,2}(ℝⁿ)` (`exists_wkpSpace_succ_of_partialDerivCLM`). Elements of
different orders in the same class have the same weak derivatives
(`baseRepresentative_partialDerivCLM_ae_eq`).

If the class of a function `f` on `ℝⁿ` lies in `W^{m,2}(ℝⁿ)` for every `m`, the Morrey embedding
gives a `C^k` member of the class for every `k`. Continuous members of a class coincide, so the
canonical continuous representative `continuousRepresentative volume f` is each of them, hence
smooth (`contDiff_continuousRepresentative_of_forall_wkpSpace`), and its derivatives are the weak
derivatives, hence square integrable. On `ℝ³` a smooth member of the class of an element of
`H^{k+3}(ℝ³)` has bounded derivatives of order `k`, by the inclusion `H^{k+3}(ℝ³) ⊂ W^{k,∞}(ℝ³)`
(`exists_bound_iteratedFDeriv_of_ae_eq_baseRepresentative`); in particular a smooth function or
vector field on `ℝ³` whose derivatives are square integrable has bounded derivatives
(`exists_bound_iteratedFDeriv_of_memLp_two`, `exists_bound_iteratedFDeriv_euclidean_of_memLp_two`),
also in `L⁴` (`memLp_four_iteratedFDeriv_of_memLp_two`,
`memLp_four_iteratedFDeriv_euclidean_of_memLp_two`).
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- The base representative of an element of `W^{k,p}(ℝⁿ)`, `p ≥ 1`, times a continuous
compactly supported function is integrable. -/
theorem integrable_baseRepresentative_mul {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{k,p}(ℝ^n)) {ψ : ℝ^n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ baseRepresentative U x * ψ x) volume := by
  have h : MemLp (baseRepresentative U) p volume := by
    have h0 := Lp.memLp (wkpBaseCoordinateCLM U)
    simp only [domainMeasure, Measure.restrict_univ] at h0
    exact h0
  exact (h.locallyIntegrable Fact.out).integrable_smul_right_of_hasCompactSupport hψ hc

/-- Integration by parts for an element of `W^{k+1,p}(ℝⁿ)` against a smooth compactly supported
function: `∫ U ∂ⱼψ = -∫ (∂ⱼU) ψ`. -/
theorem integral_baseRepresentative_mul_partialDeriv {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{k + 1,p}(ℝ^n)) (j : Fin n) {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, baseRepresentative U x * PDE.partialDeriv j ψ x =
      -∫ x, baseRepresentative (partialDerivCLM j U) x * ψ x := by
  have h := (U.property (firstDerivIndex n (k + 1) (Nat.succ_pos k) j)).integral_identity
    (_root_.TestFunction.mk ψ hψ hc (Set.subset_univ _)) (Set.subset_univ _)
  rw [baseRepresentative_partialDerivCLM]
  simp only [firstDerivIndex_toList, List.length_singleton, pow_one, neg_mul, one_mul,
    domainMeasure, Measure.restrict_univ] at h
  simpa [iteratedPartialDeriv, baseRepresentative] using h

/-- Elements of `W^{k+1,p}(ℝⁿ)` and `W^{l+1,p}(ℝⁿ)` in the same class have the same weak partial
derivatives. -/
theorem baseRepresentative_partialDerivCLM_ae_eq {k l : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {U : W^{k + 1,p}(ℝ^n)} {V : W^{l + 1,p}(ℝ^n)}
    (h : baseRepresentative U =ᵐ[volume] baseRepresentative V) (j : Fin n) :
    baseRepresentative (partialDerivCLM j U) =ᵐ[volume]
      baseRepresentative (partialDerivCLM j V) := by
  have hU := U.property (firstDerivIndex n (k + 1) (Nat.succ_pos k) j)
  have hV := V.property (firstDerivIndex n (l + 1) (Nat.succ_pos l) j)
  rw [firstDerivIndex_toList] at hU hV
  rw [baseRepresentative_partialDerivCLM, baseRepresentative_partialDerivCLM]
  have h' : baseRepresentative U =ᵐ[domainMeasure n Set.univ] baseRepresentative V := by
    simpa [domainMeasure] using h
  have h2 := (hU.congr_ae h' Filter.EventuallyEq.rfl).unique_ae isOpen_univ hV
  simpa [domainMeasure] using h2

/-- An element of `W^{m+1,2}(ℝⁿ)` whose first weak partial derivatives have realizations in
`W^{m+1,2}(ℝⁿ)` has a realization in `W^{m+2,2}(ℝⁿ)`. -/
theorem exists_wkpSpace_succ_of_partialDerivCLM {m : ℕ} (U : W^{m + 1,2}(ℝ^n))
    (hU : ∀ j : Fin n, ∃ V : W^{m + 1,2}(ℝ^n),
      baseRepresentative V =ᵐ[volume] baseRepresentative (partialDerivCLM j U)) :
    ∃ V : W^{m + 2,2}(ℝ^n), baseRepresentative V =ᵐ[volume] baseRepresentative U := by
  choose Y hY using hU
  have hf : MemLp (baseRepresentative U) 2 (domainMeasure n Set.univ) :=
    Lp.memLp (wkpBaseCoordinateCLM U)
  have hweak (j : Fin n) : HasWeakDerivativeOn Set.univ [j] (baseRepresentative U)
      (baseRepresentative (Y j)) := by
    have h := U.property (firstDerivIndex n (m + 1) (Nat.succ_pos m) j)
    rw [firstDerivIndex_toList] at h
    have hYj := (hY j).symm
    rw [baseRepresentative_partialDerivCLM] at hYj
    exact h.congr_ae Filter.EventuallyEq.rfl (by simpa [domainMeasure] using hYj)
  obtain ⟨V, hV, -⟩ := exists_succOrder_of_memLp_of_firstDerivatives (k := m + 1)
    (baseRepresentative U) hf Y hweak
  exact ⟨V, by simpa [domainMeasure] using hV⟩

/-- A function whose class lies in every `W^{m,2}(ℝⁿ)` has a smooth canonical continuous
representative. -/
theorem contDiff_continuousRepresentative_of_forall_wkpSpace [Fact (0 < n)] {f : ℝ^n → ℝ}
    (hf : ∀ m, ∃ V : W^{m,2}(ℝ^n), baseRepresentative V =ᵐ[volume] f) :
    ContDiff ℝ (⊤ : ℕ∞) (continuousRepresentative volume f) := by
  refine contDiff_infty.2 fun k ↦ ?_
  obtain ⟨V, hV⟩ := hf (k + 1 + n / 2)
  obtain ⟨g, hg, hgV⟩ := exists_contDiffAt_representative_of_order (k := k) Fact.out
    isOpen_univ V le_rfl
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x ↦
    (hg x (Set.mem_univ x)).continuousAt
  have hgf : g =ᵐ[volume] f := by
    have h := hgV
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h.trans hV
  rw [continuousRepresentative_eq hgc hgf]
  exact contDiff_iff_contDiffAt.2 fun x ↦ hg x (Set.mem_univ x)

/-- The derivatives of the smooth representative of a function whose class lies in every
`W^{m,2}(ℝⁿ)` are square integrable. -/
theorem memLp_iteratedFDeriv_continuousRepresentative_of_forall_wkpSpace [Fact (0 < n)]
    {f : ℝ^n → ℝ} (hf : ∀ m, ∃ V : W^{m,2}(ℝ^n), baseRepresentative V =ᵐ[volume] f) (k : ℕ) :
    MemLp (iteratedFDeriv ℝ k (continuousRepresentative volume f)) 2 volume := by
  obtain ⟨V, hV⟩ := hf k
  exact memLp_iteratedFDeriv_of_ae_eq_baseRepresentative V
    (contDiff_continuousRepresentative_of_forall_wkpSpace hf)
    ((continuousRepresentative_ae_eq volume f).trans hV.symm) le_rfl

/-- A smooth member of the class of an element of `H^{k+3}(ℝ³)` has bounded derivatives of
order `k`. -/
theorem exists_bound_iteratedFDeriv_of_ae_eq_baseRepresentative {k : ℕ}
    (V : W^{k + 3,2}(ℝ^3)) {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfV : f =ᵐ[volume] baseRepresentative V) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have hV : f =ᵐ[volume] baseRepresentative
      (hilbertEmbeddingCLM k memLp_top_baseRepresentative_three V) := by
    rw [baseRepresentative_hilbertEmbeddingCLM]
    exact hfV
  have hmem : MemLp (iteratedFDeriv ℝ k f) ∞ volume :=
    memLp_iteratedFDeriv_of_ae_eq_baseRepresentative _ hf hV le_rfl
  refine ⟨lpNorm (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) ∞ volume, fun x ↦ ?_⟩
  have h := SobolevSpace.Product.norm_le_lpNorm_top_of_continuous
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm hmem.norm x
  rwa [norm_norm] at h

/-- A smooth function on `ℝ³` whose derivatives of order at most `k + 3` are square integrable has
bounded derivatives of order `k`. -/
theorem exists_bound_iteratedFDeriv_of_memLp_two {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {k : ℕ} (h : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m f) 2 volume) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C :=
  exists_bound_iteratedFDeriv_of_ae_eq_baseRepresentative (wkpOfContDiff f hf h) hf
    (baseRepresentative_wkpOfContDiff f hf h).symm

/-- A smooth vector field on `ℝ³` whose derivatives of order at most `k + 3` are square
integrable has bounded derivatives of order `k`. -/
theorem exists_bound_iteratedFDeriv_euclidean_of_memLp_two {F : ℝ^3 → ℝ^3}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {k : ℕ}
    (h : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m F) 2 volume) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C := by
  refine PDE.exists_bound_iteratedFDeriv_of_component (hF.of_le (by exact_mod_cast le_top))
    fun i ↦ ?_
  have hFi : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ F x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  exact exists_bound_iteratedFDeriv_of_memLp_two hFi fun m hm ↦ (h m hm).of_le
    ((hFi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le hF i m x)

/-- A smooth function on `ℝ³` whose derivatives of order at most `k + 3` are square integrable has
its derivative of order `k` in `L⁴`. -/
theorem memLp_four_iteratedFDeriv_of_memLp_two {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {k : ℕ} (h : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m f) 2 volume) :
    MemLp (iteratedFDeriv ℝ k f) 4 volume := by
  have : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hV : f =ᵐ[volume] baseRepresentative
      (hilbertEmbeddingCLM k memLp_four_baseRepresentative_three (wkpOfContDiff f hf h)) := by
    rw [baseRepresentative_hilbertEmbeddingCLM]
    exact (baseRepresentative_wkpOfContDiff f hf h).symm
  exact memLp_iteratedFDeriv_of_ae_eq_baseRepresentative _ hf hV le_rfl

/-- A smooth vector field on `ℝ³` whose derivatives of order at most `k + 3` are square
integrable has its derivative of order `k` in `L⁴`. -/
theorem memLp_four_iteratedFDeriv_euclidean_of_memLp_two {F : ℝ^3 → ℝ^3}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {k : ℕ}
    (h : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m F) 2 volume) :
    MemLp (iteratedFDeriv ℝ k F) 4 volume := by
  refine PDE.memLp_iteratedFDeriv_of_component (hF.of_le (by exact_mod_cast le_top)) fun i ↦ ?_
  have hFi : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ F x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  exact memLp_four_iteratedFDeriv_of_memLp_two hFi fun m hm ↦ (h m hm).of_le
    ((hFi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le hF i m x)

end SobolevSpace.GraphSpace
