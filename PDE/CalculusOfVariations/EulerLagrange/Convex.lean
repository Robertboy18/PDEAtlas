/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ConvexIntegralComparison
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# The weak Euler–Lagrange equation is sufficient for joint convexity

Suppose the density is jointly convex in the value and gradient. A Sobolev
function satisfying its weak Euler–Lagrange equation minimizes the shifted
extended energy in its prescribed affine class. The proof tests the equation
with the difference between a competitor and the solution, then integrates
the supporting inequality. Convexity in the gradient alone, which suffices for the
existence theorems, does not justify this comparison.

The weak equation includes integrability of each tested pairing. No growth bound
on the density or its derivative is imposed. The spatial shift is measurable
and makes the density nonnegative; it need not be integrable.

Boundary variations belong to the closure of supported smooth functions. This
is the defining `W¹ᵖ₀` class on open sets for finite `p`. The comparison also
applies to the same closure at `p = ∞`, without a trace-kernel identification.

The argument is the Remark after Theorem 4 in Evans, §8.2.3, which integrates the convexity
inequality for `(p, z) ↦ L(p, z, x)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, Remark after Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)

/-- A weak solution minimizes a jointly convex mixed density in its affine
Sobolev class. Here `D(x)` is the full derivative at `(u(x), ∇u(x))`, and the
weak equation tests its value and gradient components together.

Competitors may have infinite energy, and any finite-energy competitor forces the
solution's energy to be finite. The domain is arbitrary, the dimension may be zero,
and the Sobolev exponent may be `1` or `∞`. -/
theorem mixedWkpLIntegral_le_of_convex_of_weak_eulerLagrange
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → (ℝ × ℝ^n) →L[ℝ] ℝ}
    {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (g u : W^{1,p}(Ω)) (hu : u - g ∈ S)
    (hderiv : ∀ᵐ x ∂μ, HasFDerivAt (F x) (D x) (B u x, ∇ u x))
    (hweak : ∀ v : W^{1,p}(Ω), v ∈ S →
      Integrable (fun x ↦ D x (B v x, ∇ v x)) μ ∧
        (∫ x, D x (B v x, ∇ v x) ∂μ) = 0)
    (w : W^{1,p}(Ω)) (hw : w - g ∈ S) :
    (∫⁻ x, ENNReal.ofReal (F x (B u x, ∇ u x) + b x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (F x (B w x, ∇ w x) + b x) ∂μ := by
  have hvariation : w - u ∈ S := by
    have hm := (S).toSubmodule.sub_mem hw hu
    change (w - g) - (u - g) ∈ S at hm
    have heq : (w - g) - (u - g) = w - u := by abel
    rwa [heq] at hm
  obtain ⟨hpair, hzero⟩ := hweak (w - u) hvariation
  have hrepresentative :
      (fun x ↦ D x (B (w - u) x, ∇ (w - u) x)) =ᵐ[μ]
        fun x ↦ D x ((B w x, ∇ w x) - (B u x, ∇ u x)) := by
    filter_upwards [Lp.coeFn_sub (B w) (B u), Lp.coeFn_sub (∇ w) (∇ u)]
      with x hB hG
    change D x (B (w - u) x, ∇ (w - u) x) =
      D x (B w x - B u x, ∇ w x - ∇ u x)
    simp only [map_sub, hB, hG, Pi.sub_apply]
  have hmeas (v : W^{1,p}(Ω)) :
      AEStronglyMeasurable (fun x ↦ F x (B v x, ∇ v x) + b x) μ := by
    have hjet : AEMeasurable (fun x ↦ (B v x, ∇ v x)) μ :=
      ((Lp.memLp (B v)).aestronglyMeasurable.prodMk
        (Lp.memLp (∇ v)).aestronglyMeasurable).aemeasurable
    exact (hF.comp_aemeasurable
      (aemeasurable_id.prodMk hjet)).aestronglyMeasurable.add hb.aestronglyMeasurable
  have hnonneg (v : W^{1,p}(Ω)) : ∀ᵐ x ∂μ, 0 ≤ F x (B v x, ∇ v x) + b x := by
    filter_upwards [hlower] with x hx
    exact neg_le_iff_add_nonneg.mp (hx (B v x, ∇ v x))
  apply lintegral_le_of_convex_of_integral_derivative_sub_nonneg hconvex hderiv
    (hmeas u) (hmeas w) (hnonneg u) (hnonneg w) (hpair.congr hrepresentative)
  have hz := (integral_congr_ae hrepresentative).symm.trans hzero
  exact le_of_eq hz.symm

end PDE.CalculusOfVariations
