/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.NonnegativeDecomposition
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak

/-!
# The weak equation from affine entropies

The convex affine entropies `r` and `-r` give both signs of the weak equation for
nonnegative tests. Decomposing a general compact C¹ test into two nonnegative tests
then gives the full weak equation. This is Remark (ii) after the definition of entropy solution
in Evans, §11.4.3, which takes `Φ(z) = ±z` and `Ψ(z) = ±F(z)` in (38).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, Remark (ii) after the definition of entropy
  solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The entropy inequality already contains the ordinary weak conservation law.
No weak equation is an additional hypothesis. -/
theorem SatisfiesEntropyInequality.isWeakSolution {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (h : SatisfiesEntropyInequality flux U u) (hf : ContDiff ℝ 1 flux) :
    IsWeakSolution flux U u := by
  let Epos : EntropyPair (deriv flux) :=
    { η := id
      q := flux
      eta_contDiff := contDiff_id
      entropyFlux_contDiff := hf
      hq := fun r ↦ by simp }
  let Eneg : EntropyPair (deriv flux) :=
    { η := fun r ↦ -r
      q := fun r ↦ -flux r
      eta_contDiff := contDiff_id.neg
      entropyFlux_contDiff := hf.neg
      hq := fun r ↦ by simp }
  have hp := h Epos (convexOn_id convex_univ)
  have hn := h Eneg (concaveOn_id (𝕜 := ℝ) convex_univ).neg
  have hzero (φ : 𝓓^{1}(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
      (∫ x, weakIntegrand flux u φ x) = 0 := by
    have hlo : 0 ≤ ∫ x, weakIntegrand flux u φ x := hp.2.2 φ hφ
    have hhi := hn.2.2 φ hφ
    have hneg : entropyWeakIntegrand u Eneg φ = fun x ↦ -weakIntegrand flux u φ x := by
      funext x
      simp only [entropyWeakIntegrand, Eneg, weakIntegrand, neg_mul, neg_add]
    rw [hneg, integral_neg] at hhi
    exact le_antisymm (neg_nonneg.mp hhi) hlo
  refine ⟨hp.1, hp.2.1, fun φ ↦ ?_⟩
  obtain ⟨a, b, ha, hb, rfl⟩ := φ.exists_sub_nonneg
  have hsub : weakIntegrand flux u (a - b) =
      fun x ↦ weakIntegrand flux u a x - weakIntegrand flux u b x := by
    funext x
    change u x * (∂[0] (fun y ↦ a y - b y)) x + flux (u x) * (∂[1] (fun y ↦ a y - b y)) x = _
    rw [partialDeriv_sub (a.contDiff.differentiable_one x) (b.contDiff.differentiable_one x),
      partialDeriv_sub (a.contDiff.differentiable_one x) (b.contDiff.differentiable_one x)]
    simp only [weakIntegrand, mul_sub]
    abel
  rw [hsub, integral_sub (integrable_weakIntegrand (flux := flux) (u := u) a hp.1 hp.2.1)
    (integrable_weakIntegrand (flux := flux) (u := u) b hp.1 hp.2.1),
    hzero a ha, hzero b hb, sub_self]

end PDE.Hyperbolic.ConservationLaw.Scalar
