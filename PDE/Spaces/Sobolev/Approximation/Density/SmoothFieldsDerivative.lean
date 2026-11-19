/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFieldsContinuity
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Differentiable families of smooth Sobolev functions

A family `τ ↦ G τ` of smooth functions with derivatives in `Lᵖ` gives a path
`τ ↦ wkpOfContDiff (G τ)` in `W^{k,p}(ℝⁿ)`. If the difference quotients of every derivative of
order at most `k` converge in `Lᵖ` to the derivatives of `G' τ₀`, the path is differentiable at
`τ₀` with derivative `wkpOfContDiff (G' τ₀)` (`hasDerivAt_wkpOfContDiff`), since the Sobolev
norm of a smooth function is at most the sum of the `Lᵖ` norms of its derivatives. The same
holds for vector fields component by component (`hasDerivAt_vectorWkpOfContDiff`), and a sequence
of vector-field families, each the derivative of the previous one, gives a smooth path
(`contDiffOn_vectorWkpOfContDiff_of_hasDerivAt`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Sobolev Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSpace.GraphSpace

/-- `wkpOfContDiff` respects the linear combination `c • (f - g) - h`. -/
theorem wkpOfContDiff_smul_sub_sub (c : ℝ) {f g h : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmf : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p volume)
    (hmg : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m g) p volume)
    (hmh : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m h) p volume)
    (hd : ContDiff ℝ (⊤ : ℕ∞) (c • (f - g) - h))
    (hmd : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (c • (f - g) - h)) p volume) :
    wkpOfContDiff (c • (f - g) - h) hd hmd =
      c • (wkpOfContDiff f hf hmf - wkpOfContDiff g hg hmg) - wkpOfContDiff h hh hmh := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply Lp.ext
  have h₁ := baseRepresentative_sub_ae
    (c • (wkpOfContDiff f hf hmf - wkpOfContDiff g hg hmg)) (wkpOfContDiff h hh hmh)
  have h₂ := baseRepresentative_smul_ae c (wkpOfContDiff f hf hmf - wkpOfContDiff g hg hmg)
  have h₃ := baseRepresentative_sub_ae (wkpOfContDiff f hf hmf) (wkpOfContDiff g hg hmg)
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂ h₃
  have key : baseRepresentative (wkpOfContDiff (c • (f - g) - h) hd hmd) =ᵐ[volume]
      baseRepresentative (c • (wkpOfContDiff f hf hmf - wkpOfContDiff g hg hmg) -
        wkpOfContDiff h hh hmh) := by
    filter_upwards [baseRepresentative_wkpOfContDiff _ hd hmd, h₁, h₂, h₃,
      baseRepresentative_wkpOfContDiff f hf hmf, baseRepresentative_wkpOfContDiff g hg hmg,
      baseRepresentative_wkpOfContDiff h hh hmh] with x e₀ e₁ e₂ e₃ ef eg eh
    rw [e₀, e₁, e₂, e₃, ef, eg, eh]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
    wkpBaseCoordinateCLM_apply] using key

/-- **Differentiability of smooth families in `W^{k,p}`.** If for every order `m ≤ k` the
difference quotients of the `m`-th derivatives of `G` at `τ₀` converge in `Lᵖ` to the `m`-th
derivative of `G' τ₀`, then `τ ↦ wkpOfContDiff (G τ)` has derivative `wkpOfContDiff (G' τ₀)` at
`τ₀`. -/
theorem hasDerivAt_wkpOfContDiff {G G' : ℝ → ℝ^n → ℝ} (hG : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (G τ))
    (hG' : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (G' τ))
    (hmem : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (G τ)) p volume)
    (hmem' : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (G' τ)) p volume) {τ₀ : ℝ}
    (hlim : ∀ m ≤ k, Tendsto (fun h ↦ eLpNorm (h⁻¹ • (iteratedFDeriv ℝ m (G (τ₀ + h)) -
      iteratedFDeriv ℝ m (G τ₀)) - iteratedFDeriv ℝ m (G' τ₀)) p volume) (𝓝[≠] 0) (𝓝 0)) :
    HasDerivAt (fun τ ↦ (wkpOfContDiff (G τ) (hG τ) (hmem τ) : W^{k,p}(ℝ^n)))
      (wkpOfContDiff (G' τ₀) (hG' τ₀) (hmem' τ₀)) τ₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  -- the difference quotient as a smooth function
  have hdq : ∀ h : ℝ, ContDiff ℝ (⊤ : ℕ∞) (h⁻¹ • (G (τ₀ + h) - G τ₀) - G' τ₀) := fun h ↦
    (((hG (τ₀ + h)).sub (hG τ₀)).const_smul h⁻¹).sub (hG' τ₀)
  have hsb : ∀ h : ℝ, ContDiff ℝ (⊤ : ℕ∞) (G (τ₀ + h) - G τ₀) := fun h ↦
    (hG (τ₀ + h)).sub (hG τ₀)
  have hsm : ∀ h : ℝ, ContDiff ℝ (⊤ : ℕ∞) (h⁻¹ • (G (τ₀ + h) - G τ₀)) := fun h ↦
    (hsb h).const_smul h⁻¹
  have hit : ∀ h : ℝ, ∀ m : ℕ, iteratedFDeriv ℝ m (h⁻¹ • (G (τ₀ + h) - G τ₀) - G' τ₀) =
      h⁻¹ • (iteratedFDeriv ℝ m (G (τ₀ + h)) - iteratedFDeriv ℝ m (G τ₀)) -
        iteratedFDeriv ℝ m (G' τ₀) := fun h m ↦ by
    funext x
    have hc : ∀ F : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → ContDiffAt ℝ m F x := fun F hF ↦
      (hF.of_le (by exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDeriv_sub_apply (hc _ (hsm h)) (hc _ (hG' τ₀)),
      iteratedFDeriv_const_smul_apply (hc _ (hsb h)),
      iteratedFDeriv_sub_apply (hc _ (hG (τ₀ + h))) (hc _ (hG τ₀))]
    rfl
  have hmdq : ∀ h : ℝ, ∀ m ≤ k,
      MemLp (iteratedFDeriv ℝ m (h⁻¹ • (G (τ₀ + h) - G τ₀) - G' τ₀)) p volume := fun h m hm ↦ by
    rw [hit h m]
    exact (((hmem _ m hm).sub (hmem _ m hm)).const_smul _).sub (hmem' _ m hm)
  have hbound : ∀ h : ℝ, ‖h⁻¹ • ((wkpOfContDiff (G (τ₀ + h)) (hG _) (hmem _) : W^{k,p}(ℝ^n)) -
      wkpOfContDiff (G τ₀) (hG _) (hmem _)) - wkpOfContDiff (G' τ₀) (hG' τ₀) (hmem' τ₀)‖ ≤
      ∑ a : DerivIndex n k, (eLpNorm (h⁻¹ • (iteratedFDeriv ℝ a.toList.length (G (τ₀ + h)) -
        iteratedFDeriv ℝ a.toList.length (G τ₀)) - iteratedFDeriv ℝ a.toList.length (G' τ₀))
          p volume).toReal := fun h ↦ by
    rw [← wkpOfContDiff_smul_sub_sub h⁻¹ (hG _) (hG _) (hG' _) (hmem _) (hmem _) (hmem' _)
      (hdq h) (hmdq h)]
    refine (norm_wkpOfContDiff_le _ (hdq h) (hmdq h)).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun a _ ↦ by rw [hit h]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun h ↦ by simpa [zero_add] using hbound h) ?_
  have hsum := tendsto_finsetSum (Finset.univ : Finset (DerivIndex n k)) fun a _ ↦
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim a.toList.length a.toList_length_le)
  simpa using hsum

/-- The components of the derivatives of a smooth vector field are the derivatives of its
components. -/
theorem iteratedFDeriv_component {U : ℝ^n → ℝ^n} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (i : Fin n)
    (m : ℕ) (x : ℝ^n) :
    iteratedFDeriv ℝ m (fun y ↦ U y i) x =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m U x) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_left
    (hU.of_le (by exact_mod_cast le_top)).contDiffAt le_rfl

/-- **Differentiability of smooth vector families in `W^{k,p}`.** The vector form of
`hasDerivAt_wkpOfContDiff`, component by component. -/
theorem hasDerivAt_vectorWkpOfContDiff {U U' : ℝ → ℝ^n → ℝ^n}
    (hU : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (U τ)) (hU' : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (U' τ))
    (hmem : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (U τ)) p volume)
    (hmem' : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (U' τ)) p volume) {τ₀ : ℝ}
    (hlim : ∀ m ≤ k, Tendsto (fun h ↦ eLpNorm (h⁻¹ • (iteratedFDeriv ℝ m (U (τ₀ + h)) -
      iteratedFDeriv ℝ m (U τ₀)) - iteratedFDeriv ℝ m (U' τ₀)) p volume) (𝓝[≠] 0) (𝓝 0)) :
    HasDerivAt (fun τ ↦ (vectorWkpOfContDiff (U τ) (hU τ) (hmem τ) : Fin n → W^{k,p}(ℝ^n)))
      (vectorWkpOfContDiff (U' τ₀) (hU' τ₀) (hmem' τ₀)) τ₀ := by
  refine hasDerivAt_pi.mpr fun i ↦ ?_
  have hc : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ U τ y i) := fun τ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hU τ)
  have hc' : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ U' τ y i) := fun τ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hU' τ)
  have hm₁ : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m fun y ↦ U τ y i) p volume :=
    fun τ m hm ↦ (hmem τ m hm).of_le (((hc τ).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le (hU τ) i m x)
  have hm₂ : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m fun y ↦ U' τ y i) p volume :=
    fun τ m hm ↦ (hmem' τ m hm).of_le (((hc' τ).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le (hU' τ) i m x)
  refine hasDerivAt_wkpOfContDiff (G := fun τ y ↦ U τ y i) (G' := fun τ y ↦ U' τ y i) hc hc'
    hm₁ hm₂ fun m hm ↦ ?_
  have hproj : ‖EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      simpa using PiLp.norm_apply_le v i
  have h1 : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim m hm)
    (fun _ ↦ zero_le) fun h ↦ eLpNorm_mono ((((((hc _).continuous_iteratedFDeriv h1).sub
      ((hc _).continuous_iteratedFDeriv h1)).const_smul _).sub
        ((hc' _).continuous_iteratedFDeriv h1)).aestronglyMeasurable) fun x ↦ ?_
  simp only [Pi.sub_apply, Pi.smul_apply, iteratedFDeriv_component (hU _) i,
    iteratedFDeriv_component (hU' _) i]
  have heq : h⁻¹ • ((EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (U (τ₀ + h)) x) -
      (EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (U τ₀) x)) -
      (EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (U' τ₀) x) =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap
        (h⁻¹ • (iteratedFDeriv ℝ m (U (τ₀ + h)) x - iteratedFDeriv ℝ m (U τ₀) x) -
          iteratedFDeriv ℝ m (U' τ₀) x) := by
    ext v
    simp
  rw [heq]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hproj

/-- **Smooth families of smooth vector fields.** If each family in a sequence `U j` is
differentiable in the sense of `hasDerivAt_vectorWkpOfContDiff` on an open set, with the next
family as derivative, then every `τ ↦ vectorWkpOfContDiff (U j τ)` is smooth there. -/
theorem contDiffOn_vectorWkpOfContDiff_of_hasDerivAt {I : Set ℝ} (hI : IsOpen I)
    (U : ℕ → ℝ → ℝ^n → ℝ^n) (hU : ∀ j τ, ContDiff ℝ (⊤ : ℕ∞) (U j τ))
    (hmem : ∀ j τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (U j τ)) p volume)
    (hlim : ∀ j, ∀ τ₀ ∈ I, ∀ m ≤ k, Tendsto (fun h ↦ eLpNorm (h⁻¹ •
      (iteratedFDeriv ℝ m (U j (τ₀ + h)) - iteratedFDeriv ℝ m (U j τ₀)) -
        iteratedFDeriv ℝ m (U (j + 1) τ₀)) p volume) (𝓝[≠] 0) (𝓝 0)) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun τ ↦ (vectorWkpOfContDiff (U j τ) (hU j τ) (hmem j τ) : Fin n → W^{k,p}(ℝ^n))) I := by
  let _ : NormedSpace ℝ (Fin n → W^{k,p}(ℝ^n)) := Pi.normedSpace
  have hd : ∀ j, ∀ τ₀ ∈ I, HasDerivAt
      (fun τ ↦ (vectorWkpOfContDiff (U j τ) (hU j τ) (hmem j τ) : Fin n → W^{k,p}(ℝ^n)))
      (vectorWkpOfContDiff (U (j + 1) τ₀) (hU (j + 1) τ₀) (hmem (j + 1) τ₀)) τ₀ :=
    fun j τ₀ hτ₀ ↦ hasDerivAt_vectorWkpOfContDiff (hU j) (hU (j + 1)) (hmem j) (hmem (j + 1))
      (hlim j τ₀ hτ₀)
  have key : ∀ N : ℕ, ∀ j, ContDiffOn ℝ N
      (fun τ ↦ (vectorWkpOfContDiff (U j τ) (hU j τ) (hmem j τ) : Fin n → W^{k,p}(ℝ^n))) I := by
    intro N
    induction N with
    | zero =>
      intro j
      exact contDiffOn_zero.mpr fun τ hτ ↦ (hd j τ hτ).continuousAt.continuousWithinAt
    | succ N ih =>
      intro j
      rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by norm_cast,
        contDiffOn_succ_iff_deriv_of_isOpen hI]
      refine ⟨fun τ hτ ↦ (hd j τ hτ).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (j + 1)).congr fun τ hτ ↦ (hd j τ hτ).deriv
  exact contDiffOn_infty.mpr fun N ↦ key N j

end SobolevSpace.GraphSpace
