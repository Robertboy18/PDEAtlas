/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Smooth multiplication and distributional derivatives

Multiplication by a Schwartz function obeys the usual product rule on tempered
distributions. The Laplacian identity has two useful forms: one contains first
derivatives of the distribution, while the divergence form differentiates the
products of the distribution with derivatives of the cutoff. The latter can be
used when the distribution is only locally L².
-/

@[expose] public noncomputable section

open scoped SchwartzMap LineDeriv Laplacian

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E]

section Normed

variable [NormedSpace ℝ E]

/-- Differentiating a Schwartz product gives the two classical product terms. -/
theorem lineDerivOp_smulLeftCLM (a φ : 𝓢(E, ℂ)) (v : E) :
    ∂_{v} (smulLeftCLM ℂ a φ) =
      smulLeftCLM ℂ (∂_{v} a : 𝓢(E, ℂ)) φ + smulLeftCLM ℂ a (∂_{v} φ) := by
  ext x
  change fderiv ℝ (smulLeftCLM ℂ a φ : E → ℂ) x v =
    (smulLeftCLM ℂ (∂_{v} a : 𝓢(E, ℂ)) φ) x + (smulLeftCLM ℂ a (∂_{v} φ)) x
  simp only [lineDerivOp_apply_eq_fderiv,
    smulLeftCLM_apply a.hasTemperateGrowth,
    smulLeftCLM_apply (∂_{v} a : 𝓢(E, ℂ)).hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

end Normed

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian does not enlarge the support of a Schwartz function. -/
theorem tsupport_laplacian_subset (φ : 𝓢(E, ℂ)) :
    tsupport (Δ φ : 𝓢(E, ℂ)) ⊆ tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport (φ : E → ℂ))
  intro x hx
  by_contra hnot
  have hzero (v : E) : (∂_{v} (∂_{v} φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hnot ((tsupport_lineDerivOp_subset v φ)
      ((tsupport_lineDerivOp_subset v (∂_{v} φ)) hmem))
  apply hx
  rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  simp [hzero]

end SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

section Normed

variable [NormedSpace ℝ E]

/-- A distributional first derivative satisfies the product rule for a Schwartz multiplier.
The signs follow by applying the classical rule to the test function. -/
theorem lineDerivOp_smulLeftCLM (a : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) (v : E) :
    ∂_{v} (smulLeftCLM F a T) =
      smulLeftCLM F (∂_{v} a : 𝓢(E, ℂ)) T + smulLeftCLM F a (∂_{v} T) := by
  ext φ
  change T (SchwartzMap.smulLeftCLM ℂ a (-∂_{v} φ)) =
    T (SchwartzMap.smulLeftCLM ℂ (∂_{v} a : 𝓢(E, ℂ)) φ) +
      T (-∂_{v} (SchwartzMap.smulLeftCLM ℂ a φ))
  rw [SchwartzMap.lineDerivOp_smulLeftCLM]
  simp only [map_neg, map_add]
  abel

end Normed

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of a localized distribution, expanded in any orthonormal basis. -/
theorem laplacian_smulLeftCLM {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (a : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) :
    Δ (smulLeftCLM F a T) = smulLeftCLM F a (Δ T) +
      ∑ i, (smulLeftCLM F (∂_{b i} (∂_{b i} a : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) T +
        (2 : ℂ) • smulLeftCLM F (∂_{b i} a : 𝓢(E, ℂ)) (∂_{b i} T)) := by
  rw [laplacian_eq_sum b, laplacian_eq_sum b, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [lineDerivOp_smulLeftCLM, LineDeriv.lineDerivOp_add,
    lineDerivOp_smulLeftCLM, lineDerivOp_smulLeftCLM]
  simp only [two_smul]
  abel

/-- The divergence form of the cutoff identity avoids assuming L² first derivatives of `T`.
For a complete complex Hilbert target, differentiating an L² product gives an H⁻¹ term. -/
theorem laplacian_smulLeftCLM_divergence {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (a : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) :
    Δ (smulLeftCLM F a T) = smulLeftCLM F a (Δ T) +
      ∑ i, ((2 : ℂ) • ∂_{b i} (smulLeftCLM F (∂_{b i} a : 𝓢(E, ℂ)) T) -
        smulLeftCLM F (∂_{b i} (∂_{b i} a : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) T) := by
  rw [laplacian_smulLeftCLM b]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [lineDerivOp_smulLeftCLM]
  simp only [smul_add, two_smul]
  abel

end TemperedDistribution
