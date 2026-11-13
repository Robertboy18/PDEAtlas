/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Lipschitz representatives from bounded weak gradients

Suppose a locally integrable function on `ℝ^n` has weak coordinate derivatives
bounded almost everywhere by constants `C j`. Mollification turns these weak
derivatives into classical derivatives with the same bounds. The mean value
theorem therefore makes every mollification Lipschitz with constant `∑ j, C j`.

Normalized bump convolutions converge almost everywhere by Mathlib's
Lebesgue differentiation theorem. Their uniform Lipschitz estimate passes to
the limit on that full-measure set, and the real-valued Lipschitz extension
theorem supplies a representative on all of `ℝ^n`. Neither boundedness of the
original function nor continuity of its chosen representative is assumed.

This is the whole-space bounded-gradient implication behind the `p = ∞` case of Morrey's
inequality (Evans §5.6.2). Evans proves it for compactly supported `u ∈ W^{1,∞}(ℝ^n)` in step 1 of
the proof of §5.8.2, Theorem 4, where the mollifications converge uniformly; we need neither
compact support nor uniform convergence. The Mathlib inputs are `lipschitzWith_of_nnnorm_fderiv_le`,
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` and
`LipschitzOnWith.extend_real`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorems 4 and 5, pp. 280-284; and §5.8.2, Theorem 4,
  step 1 of the proof, p. 294.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped Convolution NNReal Topology

namespace SobolevSpace

variable {n : ℕ}

namespace Approximation

/-- Bounds on the weak coordinate derivatives give a uniform Lipschitz
constant for every mollification, including in dimension zero. For `ε ≤ 0` the
mollification is zero, and in positive dimension the weak derivatives make `f` locally
integrable. -/
theorem lipschitzWith_mollify_of_weak_derivative_bound
    (μ : Mollifier n) {ε : ℝ}
    {f : ℝ^n → ℝ}
    (g : Fin n → ℝ^n → ℝ)
    (hg : ∀ j, HasWeakDerivativeOn univ [j] f (g j))
    (C : Fin n → ℝ≥0)
    (hC : ∀ j, ∀ᵐ x ∂volume, ‖g j x‖ ≤ C j) :
    LipschitzWith (∑ j, C j) (mollify μ ε f) := by
  rcases le_or_gt ε 0 with hε | hε
  · rw [mollify, scaled, ite_eq_left hε, zero_convolution]
    exact LipschitzWith.const' 0
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨j₀⟩⟩
  · have : Subsingleton (ℝ^n) := ⟨fun x y ↦ PiLp.ext fun i ↦ isEmptyElim i⟩
    exact LipschitzWith.of_dist_le_mul fun x y ↦ by simp [Subsingleton.elim x y]
  have hf : LocallyIntegrable f volume :=
    locallyIntegrableOn_univ.mp (hg j₀).locallyIntegrable_f
  have hpartial (j : Fin n) (x : ℝ^n) :
      ‖(∂[j] (mollify μ ε f)) x‖ ≤ C j := by
    have hcomm :=
      iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
        μ hε (by simp : [j] ≠ []) hf (hg j)
    have hrow : (∂[j] (mollify μ ε f)) x = mollify μ ε (g j) x := by
      simpa only [iteratedPartialDeriv] using congrFun hcomm x
    rw [hrow]
    exact norm_mollify_le_of_ae_bound μ hε (hC j) x
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((mollify_contDiff_of_pos μ hε f hf).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (mollify μ ε f) x‖ ≤ ((∑ j, C j : ℝ≥0) : ℝ)
  refine ContinuousLinearMap.opNorm_le_bound _ (NNReal.coe_nonneg _) ?_
  intro v
  rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv]
  calc
    ‖∑ j : Fin n, v j • (∂[j] (mollify μ ε f)) x‖
        ≤ ∑ j : Fin n, ‖v j • (∂[j] (mollify μ ε f)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (C j : ℝ) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (hpartial j x) (PiLp.norm_apply_le v j)
        (norm_nonneg _) (NNReal.coe_nonneg _)
    _ = ((∑ j, C j : ℝ≥0) : ℝ) * ‖v‖ := by
      rw [NNReal.coe_sum, Finset.sum_mul]

end Approximation

/-- A locally integrable scalar function with bounded weak coordinate derivatives
has a globally Lipschitz representative. The constant is the sum of the coordinate
bounds; no boundedness or continuity of the initial representative is required. -/
theorem exists_lipschitzWith_ae_eq_of_weak_derivative_bound
    {f : ℝ^n → ℝ} (hf : LocallyIntegrable f volume)
    (g : Fin n → ℝ^n → ℝ)
    (hg : ∀ j, HasWeakDerivativeOn univ [j] f (g j))
    (C : Fin n → ℝ≥0)
    (hC : ∀ j, ∀ᵐ x ∂volume, ‖g j x‖ ≤ C j) :
    ∃ v : ℝ^n → ℝ, LipschitzWith (∑ j, C j) v ∧ v =ᵐ[volume] f := by
  let r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by
    dsimp only [r]
    positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ : ℕ → ContDiffBump (0 : ℝ^n) := fun k ↦
    { rIn := r k
      rOut := 2 * r k
      rIn_pos := hr k
      rIn_lt_rOut := by linarith [hr k] }
  let μ : ℕ → Approximation.Mollifier n := fun k ↦
    { ρ := (φ k).normed volume
      smooth := (φ k).contDiff_normed
      compactSupport := (φ k).hasCompactSupport_normed
      nonneg := (φ k).nonneg_normed
      integral_one := (φ k).integral_normed }
  let u : ℕ → ℝ^n → ℝ := fun k ↦
    ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
  have hu (k : ℕ) : u k = Approximation.mollify (μ k) 1 f := by
    have hscaled : Approximation.scaled (μ k) 1 = (φ k).normed volume := by
      rw [Approximation.scaled_of_pos (μ k) zero_lt_one]
      simp only [inv_one, one_pow, one_smul, one_mul, μ]
    simp only [u, Approximation.mollify, hscaled]
  have hLip (k : ℕ) : LipschitzWith (∑ j, C j) (u k) := by
    rw [hu k]
    exact Approximation.lipschitzWith_mollify_of_weak_derivative_bound (μ k) g hg C hC
  have hout : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_zero] using tendsto_const_nhds.mul hr0
  have hratio : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn :=
    Eventually.of_forall fun _ ↦ le_rfl
  have hae : ∀ᵐ x ∂volume, Tendsto (fun k ↦ u k x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hout hratio hf
  let good : Set (ℝ^n) :=
    {x | Tendsto (fun k ↦ u k x) atTop (𝓝 (f x))}
  have hgood : LipschitzOnWith (∑ j, C j) f good := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto (hx.dist hy)
      (Eventually.of_forall fun k ↦ (hLip k).dist_le_mul x y)
  obtain ⟨v, hv, heq⟩ := hgood.extend_real
  refine ⟨v, hv, ?_⟩
  filter_upwards [hae] with x hx
  exact (heq hx).symm

end SobolevSpace
