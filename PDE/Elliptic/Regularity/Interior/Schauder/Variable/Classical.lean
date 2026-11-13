/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Interior
public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakToClassical
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Classical derivatives from interior Schauder regularity

The Hölder weak derivatives supplied by the interior estimate are classical
derivatives of any continuous representative of the solution. The weak to
classical implication uses the mollification reconstruction theorem.
This identifies the differentiated field needed in the nonlinear bootstrap.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Cᵐ first weak derivatives give Cᵐ⁺¹ regularity on an open set.
The derivative is reconstructed by mollification, rather than assumed. -/
theorem contDiffOn_succ_of_continuous_weakPartialDerivativesOn
    (m : ℕ)
    {Ω : Set ℝ^n} (hΩ : IsOpen Ω) {f : ℝ^n → ℝ}
    {g : Fin n → ℝ^n → ℝ} (hf : Continuous f)
    (hg : ∀ i, Continuous (g i))
    (hgm : ∀ i, ContDiffOn ℝ m (g i) Ω)
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] f (g i)) :
    ContDiffOn ℝ (m + 1) f Ω := by
  let D : ℝ^n → ℝ^n →L[ℝ] ℝ :=
    fun x ↦ innerSL ℝ (WithLp.toLp 2 fun i ↦ g i x)
  have hD : ContDiffOn ℝ m D Ω := by
    have hvec : ContDiffOn ℝ m (fun x ↦ (WithLp.toLp 2 fun i ↦ g i x : ℝ^n)) Ω :=
      contDiffOn_piLp' 2 hgm
    exact (innerSL ℝ).contDiff.comp_contDiffOn hvec
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := m) hΩ.uniqueDiffOn).2 ⟨by simp, D, hD, ?_⟩
  intro x hx
  exact (hasFDerivAt_of_continuous_weakPartialDerivativesOn hΩ hf hg hweak hx).hasFDerivWithinAt

end SobolevSpace.Approximation

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A continuous representative of an H¹ solution with Hölder
coefficients and Hölder divergence forcing is C¹. All regularity of its
weak gradient is derived by the interior Schauder estimate. -/
theorem contDiffOn_one_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : ∀ i j, HolderOnWith K γ (A i j) Ω)
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j)
    (hAbound : ∀ x ∈ Ω, ∀ i j, ‖A i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) Ω)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ)
    {v : ℝ^n → ℝ} (hv : Continuous v)
    (hvu : v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u) :
    ContDiffOn ℝ 1 v Ω := by
  intro x hx
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨r, hr, hrR, hreg⟩ :=
    exists_holder_gradient_of_holder_coefficients_same_exponent
      hq2 hq hα hΛ hΩ a A hγ0 hγ1 hA hrep hAbound hell
        u F f hf hF hu hR hball
  choose g N hg hgh hga using hreg
  have hsmall : ball x r ⊆ Ω := (ball_subset_ball (by linarith : r ≤ R)).trans hball
  have hweak (i : Fin n) : HasWeakDerivativeOn (ball x r) [i] v (g i) := by
    have hw : HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM u)
        (wkpCoordinateCLM (singleDerivIndex n i) u) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using u.property.hasWeakDerivativeOn_first (by norm_num) i
    exact (hw.mono isOpen_ball.measurableSet hsmall).congr_ae
      (hvu.symm.filter_mono (ae_mono (domainMeasure_le hsmall))) (hga i).symm
  have hc := Approximation.contDiffOn_succ_of_continuous_weakPartialDerivativesOn
    0 isOpen_ball hv hg (fun i ↦ contDiffOn_zero.mpr (hg i).continuousOn) hweak
  exact (hc.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt

end SobolevSpace.GraphSpace
