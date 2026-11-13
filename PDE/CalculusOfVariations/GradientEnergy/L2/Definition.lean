/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.LinearImage.Basic
public import PDE.CalculusOfVariations.DirichletIntegral

/-!
# The signed Dirichlet gradient energy on L²

The Dirichlet integral on `H¹₀` is transported to `L²` through the base
coordinate. Every other `L²` function has energy `+∞`. On an open domain
the inclusion is injective, so the definition keeps the signed
integral rather than its positive part.

This is the functional `I` of Evans, §9.6.3, equation (27), whose
subdifferential is taken for the ambient `L²` inner product. The density
is arbitrary here; the growth bounds that make the integral finite on all
of `H¹₀` are assumed only in the later results.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, equation (27).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Extend the Dirichlet gradient integral by `+∞` outside
`H¹₀`. No sign normalization is made. -/
def l2DirichletGradientEnergy (L : ℝ^n → ℝ) : DerivLp n 2 Ω → EReal :=
  linearImageEnergy (baseCoordCLM (n := n) (Ω := Ω))
    (dirichletGradientIntegralEnergy (fun _ ↦ L))

/-- The finite value is the original signed Sobolev integral. -/
theorem l2DirichletGradientEnergy_base (hΩ : IsOpen Ω) (L : ℝ^n → ℝ)
    (u : H¹₀(Ω)) :
    l2DirichletGradientEnergy L (baseCoordCLM u) =
      (dirichletGradientIntegralEnergy (fun _ ↦ L) u : EReal) :=
  linearImageEnergy_apply _ (baseCoordCLM_injective hΩ) _ u

/-- Every point outside the zero-boundary Sobolev domain has
infinite energy. -/
theorem l2DirichletGradientEnergy_eq_top (L : ℝ^n → ℝ)
    {u : DerivLp n 2 Ω} (hu : u ∉ range (baseCoordCLM (n := n) (Ω := Ω))) :
    l2DirichletGradientEnergy L u = ⊤ :=
  linearImageEnergy_eq_top_of_notMem _ _ hu

/-- The finite-energy domain is exactly the image of `H¹₀`. -/
theorem l2DirichletGradientEnergy_ne_top_iff (hΩ : IsOpen Ω) (L : ℝ^n → ℝ)
    (u : DerivLp n 2 Ω) :
    l2DirichletGradientEnergy L u ≠ ⊤ ↔
      u ∈ range (baseCoordCLM (n := n) (Ω := Ω)) :=
  linearImageEnergy_ne_top_iff _ (baseCoordCLM_injective hΩ) _ u

/-- The signed extension is proper on every domain, including the empty one. -/
theorem isProper_l2DirichletGradientEnergy (L : ℝ^n → ℝ) :
    IsProper (l2DirichletGradientEnergy (Ω := Ω) L) :=
  isProper_linearImageEnergy _ _

end PDE.CalculusOfVariations
