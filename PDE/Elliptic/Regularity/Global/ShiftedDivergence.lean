/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
import PDE.Elliptic.Regularity.Global.H2

/-!
# Global `H²` regularity for the full shifted operator

A homogeneous Dirichlet weak solution of `-∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + cu + λu = f` with `f ∈ L²` has an
`H²` representative on a domain with a `C2BoundaryAtlas`
(`exists_global_h2_of_weak_shifted_full_divergence_solution`). The principal coefficients are
`W^{1,∞}` with globally `C¹` representatives, and the lower-order coefficients are `L^∞`. At `λ = 0`
this is the qualitative part of Evans's §6.3.2, Theorem 4 (Boundary `H²`-regularity).

As in step 2 of Evans's proof, (44)-(45), the lower-order terms move into an `L²` effective forcing
computed from the given `H¹₀` solution, and the principal theorem
`exists_global_h2_of_isWeakDivergenceSolution` applies. The reduction to the principal equation is
defined in `PDE.Elliptic.Variational.ShiftedDivergenceForm`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42),
  p. 334, and step 2 of its proof, (44)-(45), p. 335.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

variable [Fact (0 < n)]

/--
The qualitative part of Evans's §6.3.2, Theorem 4, for the full shifted
divergence-form operator.

On a domain equipped with the operational `C2BoundaryAtlas`, a homogeneous
Dirichlet weak solution of

`-∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + c u + λu = f`

has an `H²(Ω)` representative when the principal coefficients are
`W^{1,∞}` with global ambient `C¹` representatives, the lower-order
coefficients are `L∞`, and `f ∈ L²(Ω)`. The lower-order terms are absorbed
into the `L²` effective forcing using the given `H¹₀` solution.

Setting `λ = 0` gives the full operator of Evans's Theorem 4.
`Boundary.HasContDiffGraphBoundary.exists_c2BoundaryAtlas` derives the operational
atlas from a `C²` graph boundary.
-/
theorem exists_global_h2_of_weak_shifted_full_divergence_solution
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (b : Fin n → DerivLp n ∞ Omega)
    (c : DerivLp n ∞ Omega)
    (lambda : ℝ)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega))
      b c lambda f (0 : Fin n → DerivLp n 2 Omega) u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  let hOpen := hOmega.toC1ExtensionAtlas.isOpen
  let coeffA : Fin n → Fin n → DerivLp n ∞ Omega := fun i j ↦
    ((A i j : WkpAmbientOn n 1 ∞ Omega)
      (baseIndex n 1) : DerivLp n ∞ Omega)
  let g :=
    fullDivergencePrincipalForcing
      b c lambda f u
  have hprincipal :
      IsWeakDivergenceSolution
        (n := n) (Ω := Omega) coeffA g u := by
    simpa [coeffA, g, hOpen] using hu.toPrincipal
  exact
    exists_global_h2_of_isWeakDivergenceSolution
      hOmega A a haRep haC1 g u
        (by simpa [coeffA] using hprincipal)
      alpha halpha hElliptic

end SobolevSpace.GraphSpace.BoundaryRegularity
