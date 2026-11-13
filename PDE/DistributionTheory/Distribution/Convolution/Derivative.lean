/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Convolution
import PDE.DistributionTheory.Distribution.Support.TensorProduct

/-!
# Differentiation of compact-carrier convolutions

For compactly carried scalar distributions `S` and `T` on `E` and a direction `v`, the
distributional directional derivative satisfies

`∂ᵥ (S * T) = (∂ᵥ S) * T = S * (∂ᵥ T)`.

This is the basic compatibility between differentiation and convolution; see Hörmander,
Chapter IV, or Friedlander and Joshi, Chapter 5. Together with `δ₀ * T = T` it gives
the solution formula `P(∂)(G * T) = T` for a fundamental solution `G`, which is carried out in
`PDE.DistributionTheory.Distribution.Convolution.ConstantCoefficient`.

## Main results

* `lineDerivCLM_convolution_left`: `∂ᵥ (S * T) = (∂ᵥ S) * T`.
* `lineDerivCLM_convolution_right`: `∂ᵥ (S * T) = S * (∂ᵥ T)`.

## Implementation notes

The convolution is defined through a cutoff `χ ⊗ ψ` equal to one near a product carrier
`K × L`, and the derivative of `χ ⊗ ψ` therefore vanishes near `K × L`. Testing `⟨S * T, φ⟩`
against a derivative of `φ` produces two terms by the product rule: the derivative of the pulled
back test function `φ ∘ (+)` in the direction `(v, 0)` (or `(0, v)`), which is the desired
term, and a term involving the derivative of the cutoff, which `S ⊗ T` annihilates because it
vanishes off `K × L`. The private lemma `tensorProduct_kills_cutoff_derivative` records this
second fact, and `lineDerivCLM_precompLocalized_addition` is the product rule for the localized
pullback along addition.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter IV, "Convolution".
  <https://doi.org/10.1007/978-3-642-61497-2_5>
* F. G. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, 2nd ed.,
  Cambridge University Press, 1998, Chapter 5, "Convolution".
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace Distribution

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem lineDerivCLM_precompLocalized_addition
    (w : E × E)
    (χ : 𝓓((⊤ : Opens (E × E)), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    TestFunction.lineDerivCLM ℝ w
        (TestFunction.precompLocalized addition addition_contDiff χ φ) =
      TestFunction.precompLocalized addition addition_contDiff χ
          (TestFunction.lineDerivCLM ℝ (w.1 + w.2) φ) +
        TestFunction.smoothMultiplierCLM
          (fun p ↦ φ (addition p))
          (φ.contDiff.comp addition_contDiff)
          (TestFunction.lineDerivCLM ℝ w χ) := by
  ext p
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  simp only [add_apply, TestFunction.precompLocalized_apply,
    TestFunction.smoothMultiplierCLM_apply, TestFunction.smoothMultiplier_apply]
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),
    TestFunction.lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ
      (fun q ↦ χ q * φ (addition q)) p w =
    χ p * lineDeriv ℝ (fun x ↦ φ x) (addition p) (w.1 + w.2) +
      φ (addition p) * lineDeriv ℝ (fun q ↦ χ q) p w
  rw [(χ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  have hχd : DifferentiableAt ℝ (fun q : E × E ↦ χ q) p :=
    (χ.contDiff.differentiable (by simp)).differentiableAt
  have hφd : DifferentiableAt ℝ (fun q : E × E ↦ φ (addition q)) p :=
    ((φ.contDiff.comp addition_contDiff).differentiable (by simp)).differentiableAt
  have hprod :
      DifferentiableAt ℝ (fun q ↦ χ q * φ (addition q)) p :=
    hχd.mul hφd
  rw [hprod.lineDeriv_eq_fderiv]
  rw [fderiv_fun_mul hχd hφd]
  rw [fderiv_fun_comp p
    (φ.contDiff.differentiable (by simp)).differentiableAt
    (addition_contDiff.differentiable (by simp)).differentiableAt]
  have hadd :
      fderiv ℝ addition p =
        ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    change fderiv ℝ (fun q : E × E ↦ q.1 + q.2) p = _
    exact (hasFDerivAt_fst.add hasFDerivAt_snd).fderiv
  rw [hadd]
  simp [addition]
  ring

omit [FiniteDimensional ℝ E] in
omit [FiniteDimensional ℝ E] in
private theorem tsupport_lineDerivCLM_cutoff_subset_compl
    {K L : Set E}
    (w : E × E)
    (χ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens E), ℝ))
    (hχ : ∀ x ∈ K, (χ : E → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ y ∈ L, (ψ : E → ℝ) =ᶠ[𝓝 y] 1) :
    tsupport
        ((TestFunction.lineDerivCLM ℝ w
          (TestFunction.tensorProduct χ ψ)) :
          𝓓((⊤ : Opens (E × E)), ℝ)) ⊆
      (K ×ˢ L)ᶜ := by
  intro p hp
  by_contra hpKL
  have hΘ :
      (TestFunction.tensorProduct χ ψ : E × E → ℝ) =ᶠ[𝓝 p] 1 :=
    tensorProduct_eq_one_near χ ψ hχ hψ p (by simpa using hpKL)
  have hzero :
      (((TestFunction.lineDerivCLM ℝ w
        (TestFunction.tensorProduct χ ψ)) :
          𝓓((⊤ : Opens (E × E)), ℝ)) : E × E → ℝ) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hΘ.eventuallyEq_nhds] with q hq
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [((TestFunction.tensorProduct χ ψ).contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rw [(hq.fderiv_eq : fderiv ℝ
      (fun z ↦ TestFunction.tensorProduct χ ψ z) q =
        fderiv ℝ (fun _ : E × E ↦ (1 : ℝ)) q)]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hp

private theorem tensorProduct_kills_cutoff_derivative
    {S T : 𝓓'((⊤ : Opens E), ℝ)}
    {K L : Set E}
    (hK : IsCompact K)
    (hL : IsCompact L)
    (hSK : IsVanishingOn S Kᶜ)
    (hTL : IsVanishingOn T Lᶜ)
    (w : E × E)
    (χ ψ : 𝓓((⊤ : Opens E), ℝ))
    (hχ : ∀ x ∈ K, (χ : E → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ y ∈ L, (ψ : E → ℝ) =ᶠ[𝓝 y] 1)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tensorProduct S T
        (TestFunction.smoothMultiplierCLM
          (fun p ↦ φ (addition p))
          (φ.contDiff.comp addition_contDiff)
          (TestFunction.lineDerivCLM ℝ w
            (TestFunction.tensorProduct χ ψ))) = 0 := by
  apply IsVanishingOn.tensorProduct_compl hK hL hSK hTL
  exact (TestFunction.tsupport_smoothMultiplier_subset _ _ _).trans
    (tsupport_lineDerivCLM_cutoff_subset_compl w χ ψ hχ hψ)

/-- Distributional directional differentiation commutes with convolution in
the left factor. -/
theorem lineDerivCLM_convolution_left
    (v : E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    lineDerivCLM v (convolution S T hS hT) =
      convolution (lineDerivCLM v S) T
        (by
          rcases hS with ⟨K, hK, hSK⟩
          exact ⟨K, hK, hSK.lineDerivOp v⟩)
        hT := by
  rcases hS with ⟨K, hK, hSK⟩
  rcases hT with ⟨L, hL, hTL⟩
  let hDS : HasCompactCarrier (lineDerivCLM v S) :=
    ⟨K, hK, hSK.lineDerivOp v⟩
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hK (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hL (subset_univ _)
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩
    hK hL hSK hTL χ ψ hχ hψ]
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    (lineDerivCLM v S) T hDS ⟨L, hL, hTL⟩
    hK hL (hSK.lineDerivOp v) hTL χ ψ hχ hψ]
  ext φ
  rw [lineDerivCLM_apply, convolutionWithCutoff_apply,
    convolutionWithCutoff_apply, ← lineDerivCLM_tensorProduct_left]
  rw [lineDerivCLM_apply]
  change
    -(tensorProduct S T)
        (TestFunction.precompLocalized addition addition_contDiff
          (TestFunction.tensorProduct χ ψ)
          (TestFunction.lineDerivCLM ℝ v φ)) =
      -(tensorProduct S T)
        (TestFunction.lineDerivCLM ℝ (v, (0 : E))
          (TestFunction.precompLocalized addition addition_contDiff
            (TestFunction.tensorProduct χ ψ) φ))
  rw [lineDerivCLM_precompLocalized_addition]
  simp only [add_zero]
  rw [map_add, tensorProduct_kills_cutoff_derivative
    hK hL hSK hTL (v, (0 : E)) χ ψ hχ hψ φ, add_zero]

/-- Distributional directional differentiation commutes with convolution in
the right factor. -/
theorem lineDerivCLM_convolution_right
    (v : E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    lineDerivCLM v (convolution S T hS hT) =
      convolution S (lineDerivCLM v T)
        hS
        (by
          rcases hT with ⟨L, hL, hTL⟩
          exact ⟨L, hL, hTL.lineDerivOp v⟩) := by
  rcases hS with ⟨K, hK, hSK⟩
  rcases hT with ⟨L, hL, hTL⟩
  let hDT : HasCompactCarrier (lineDerivCLM v T) :=
    ⟨L, hL, hTL.lineDerivOp v⟩
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hK (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hL (subset_univ _)
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩
    hK hL hSK hTL χ ψ hχ hψ]
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    S (lineDerivCLM v T) ⟨K, hK, hSK⟩ hDT
    hK hL hSK (hTL.lineDerivOp v) χ ψ hχ hψ]
  ext φ
  rw [lineDerivCLM_apply, convolutionWithCutoff_apply,
    convolutionWithCutoff_apply, ← lineDerivCLM_tensorProduct_right]
  rw [lineDerivCLM_apply]
  change
    -(tensorProduct S T)
        (TestFunction.precompLocalized addition addition_contDiff
          (TestFunction.tensorProduct χ ψ)
          (TestFunction.lineDerivCLM ℝ v φ)) =
      -(tensorProduct S T)
        (TestFunction.lineDerivCLM ℝ ((0 : E), v)
          (TestFunction.precompLocalized addition addition_contDiff
            (TestFunction.tensorProduct χ ψ) φ))
  rw [lineDerivCLM_precompLocalized_addition]
  simp only [zero_add]
  rw [map_add, tensorProduct_kills_cutoff_derivative
    hK hL hSK hTL ((0 : E), v) χ ψ hχ hψ φ, add_zero]

end Distribution
