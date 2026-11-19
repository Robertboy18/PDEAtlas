/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Differentiable.ContinuousSupport
public import PDE.Analysis.Convex.Differentiable.Supporting
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax

/-!
# The derivative of the scalar Legendre transform

Surjectivity of the derivative of a differentiable convex flux makes its
conjugate finite. A continuous right inverse gives the maximizing point and
supports the conjugate at every velocity. The continuous-support theorem then
identifies its derivative.

The inverse itself is neither constructed nor differentiated.

In the notation of step 1 of the proof of Evans, §3.4.2, Theorem 1,
`legendreTransform_eq_of_rightInverse_deriv` is the formula `L(v) = vG(v) - F(G(v))` for a
right inverse `G` of `F'`, and `hasDerivAt_legendreTransform_of_continuous_rightInverse` is (30),
`L'(v) = G(v)`. Evans takes `F` smooth and uniformly convex, with `G = (F')^{-1}` as in (28), and
obtains (30) by differentiating `G`; here `F` is convex and differentiable, and `G` need only
be continuous at `v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equations (25) and (28), Theorem 1 and step 1 of
  its proof, equation (30).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set PDE.Analysis

namespace HopfLax1D

/-- A differentiable convex scalar function whose derivative is surjective
has a finite conjugate at every velocity. -/
theorem legendreFinite_of_surjective_deriv {F : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hsurj : Function.Surjective (deriv F)) :
    LegendreFinite F := by
  intro v
  obtain ⟨p, hp⟩ := hsurj v
  refine ⟨p * v - F p, ?_⟩
  rintro _ ⟨r, rfl⟩
  have hs := fderiv_apply_sub_le_sub_of_convex hconv
    (hF p).hasDerivAt.hasFDerivAt r (mem_univ _) (mem_univ _)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hp] at hs
  nlinarith only [hs]

/-- A right inverse of the flux derivative gives the exact attained conjugate
formula, including all affine and constant terms of the flux. -/
theorem legendreTransform_eq_of_rightInverse_deriv {F G : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F)) (v : ℝ) :
    legendreTransform F v = G v * v - F (G v) := by
  have hFin := legendreFinite_of_surjective_deriv hconv hF hG.surjective
  have h := legendreTransform_eq_of_convex_differentiable hFin hconv (hF (G v))
  simpa only [hG v] using h

/-- Continuous inversion of the flux derivative identifies the
derivative of its conjugate. -/
theorem hasDerivAt_legendreTransform_of_continuous_rightInverse {F G : ℝ → ℝ}
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F))
    {v : ℝ} (hcont : ContinuousAt G v) :
    HasDerivAt (legendreTransform F) (G v) v := by
  have hFin := legendreFinite_of_surjective_deriv hconv hF hG.surjective
  apply hasDerivAt_of_continuous_support (a := G) _ hcont
  intro u w
  have hs := le_legendreTransform (H := F) (q := w) (p := G u) (hFin w)
  rw [legendreTransform_eq_of_rightInverse_deriv hconv hF hG u]
  nlinarith only [hs]

end HopfLax1D
