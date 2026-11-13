/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Existence.Weak
public import PDE.Analysis.Evolution.GradientFlow.Uniqueness.Weak
public import PDE.Analysis.Evolution.GradientFlow.Approximation.Error

/-!
# The global subdifferential gradient flow

Let `I : H → EReal` be proper, convex and lower semicontinuous on a real Hilbert space
`H`. From every `x₀` in the subdifferential domain, the gradient flow `u' ∈ -∂I(u)` has a
unique weak solution on `[0, ∞)`. Its speed is bounded by `‖p‖`, where `p` is the
least-norm element of `∂I(x₀)`, every `u(t)` with `t ≥ 0` lies in the subdifferential
domain, and the Yosida flows converge to `u` with `‖u_λ(t) - u(t)‖² ≤ (λ/2) t ‖p‖²`.
The domain need not be dense and `H` need not be separable.

This is Evans, §9.6.2, Theorem 3, whose proof constructs `u` as the limit of the Yosida flows
(17). The speed bound is his (25), and the convergence rate is his (23) in the limit
`μ → 0`. Evans assumes for the exposition that `D(∂I)` is dense; Remark (ii) after the proof
notes that this is not needed.

## Main results

* `exists_unique_subgradientFlow`: existence and uniqueness of the weak subgradient flow from a
  point of the subdifferential domain, with the speed bound, the invariance of the domain and
  the convergence rate of the Yosida flows.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, Theorem 3 (Solution of gradient flow) and its
  proof, (17)-(25), pp. 566-569, and Remark (ii) after the proof, p. 570.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Convex
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- Global existence and uniqueness of the weak subgradient flow from `x₀` in the
subdifferential domain. With `p` the least-norm element of `∂I(x₀)`, there is a weak
flow `(u, g)` with `u(0) = x₀` that is `‖p‖`-Lipschitz on `[0, ∞)`, has `‖g‖ ≤ ‖p‖`
and `u' = g` almost everywhere, stays in the subdifferential domain, is absolutely
continuous on every `[0, T]`, and satisfies `‖u_λ(t) - u(t)‖² ≤ (λ/2) t ‖p‖²`. The
Yosida flows converge to `u` uniformly on every `[0, T]`, and every weak flow from `x₀`
equals `u` on `[0, ∞)` with velocity equal to `g` almost everywhere. -/
theorem exists_unique_subgradientFlow (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {x₀ : H} (hx₀ : x₀ ∈ subdifferentialDomain I) :
    ∃ p ∈ subdifferential I x₀, (∀ q ∈ subdifferential I x₀, ‖p‖ ≤ ‖q‖) ∧
      ∃ u g : ℝ → H, u 0 = x₀ ∧ IsSubgradientFlow I u g ∧
        LipschitzOnWith ‖p‖₊ u (Ici 0) ∧
        eLpNorm g ∞ (volume.restrict (Ioi 0)) ≤ ENNReal.ofReal ‖p‖ ∧
        (∀ᵐ t ∂volume.restrict (Ioi 0), ‖g t‖ ≤ ‖p‖) ∧
        (∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt u (g t) t) ∧
        (∀ t, 0 ≤ t → u t ∈ subdifferentialDomain I) ∧
        (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T) ∧
        (∀ (lambda : ℝ) (hlambda : 0 < lambda) (t : ℝ), 0 ≤ t →
          ‖yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t - u t‖ ^ 2 ≤
            lambda / 2 * t * ‖p‖ ^ 2) ∧
        (∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn
          (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
            (by positivity) x₀) u atTop (Icc 0 T)) ∧
        (∀ w h : ℝ → H, w 0 = x₀ → IsSubgradientFlow I w h →
          EqOn w u (Ici 0) ∧ h =ᵐ[volume.restrict (Ioi 0)] g) := by
  obtain ⟨p, hp, hmin⟩ := exists_minimal_norm_subgradient hproper hx₀
  obtain ⟨u, hu0, hflow, hLip, hbound, hderiv, hdomain, hAC, hu⟩ :=
    exists_isSubgradientFlow_of_mem_subdifferential hproper hconvex hlsc hp
  refine ⟨p, hp, hmin, u, deriv u, hu0, hflow, hLip, ?_, hbound, hderiv, hdomain,
    hAC, fun _ hlambda _ ht ↦ norm_yosidaFlow_sub_limit_sq_le
      hproper hconvex hlsc hp hu hlambda ht, hu, ?_⟩
  · rw [eLpNorm_exponent_top hflow.velocity_memLp.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hbound
  · intro w h hw0 hw
    exact ⟨hw.eqOn_of_initial_eq hproper hflow (hw0.trans hu0.symm),
      hw.velocity_ae_eq_of_initial_eq hproper hflow (hw0.trans hu0.symm)⟩

end PDE.Analysis.Evolution
