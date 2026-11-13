/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.H2.ChartPiece
import PDE.Elliptic.Regularity.Interior.H2PartitionPiece
import PDE.Spaces.Sobolev.Localization.Assembly.Partition

/-!
# Global elliptic `H²` regularity for the principal divergence operator

On a bounded domain with a `C2BoundaryAtlas`, an `H¹₀` weak solution of `-∂ᵢ(aᵢⱼ ∂ⱼu) = f` with
`f ∈ L²` has an `H²` representative (`exists_global_h2_of_isWeakDivergenceSolution`). The principal
coefficients have globally `C¹` representatives and are uniformly elliptic on the domain. This is
the qualitative part of Evans's §6.3.2, Theorem 4 (Boundary `H²`-regularity), for an operator
without lower-order terms; `exists_global_h2_of_weak_shifted_full_divergence_solution` treats the
full operator.

The coefficient representative is globally `C¹`, but uniform ellipticity is assumed only on the
physical domain. The interior argument constructs its own globally Lipschitz and elliptic extension,
retaining half the ellipticity constant. Thus no whole-space ellipticity hypothesis appears in the
theorem.

## How it works

Evans flattens the boundary near each boundary point, bounds the tangential difference quotients of
`Du` on a half-ball with the test function `-D_k^{-h}(ζ² D_k^h u)`, recovers `u_{xₙxₙ}` from the
equation in nondivergence form, (52)-(56), and finally covers `∂U` by finitely many such sets and
sums the estimates with the interior estimate. We localize with the domain partition of unity
instead. The interior piece `exists_interior_h2_localized_piece` is handled by difference quotients.
Each boundary piece `exists_boundaryChart_h2_localized_piece` is flattened, estimated on the
half-space, extended by odd reflection, and pulled back through its `C²` chart. `partitionAssembly`
sums the pieces into one `H²` representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity) and its proof,
  (38)-(71), pp. 334-340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/-- Principal-part case of the qualitative `H²` regularity of Evans's §6.3.2,
Theorem 4.

On a bounded domain equipped with `C2BoundaryAtlas`, an `H¹₀` weak solution
of a uniformly elliptic divergence-form equation with principal coefficients
admitting global `C¹` representatives and with `L²` forcing has an
`H²(Ω)` representative. `Boundary.HasContDiffGraphBoundary.exists_c2BoundaryAtlas`
constructs this operational atlas from a `C²` graph boundary.

This declaration treats `b = 0` and `c = 0`. The full lower-order theorem,
including `L∞` first- and zeroth-order coefficients, is
`exists_global_h2_of_weak_shifted_full_divergence_solution`. -/
theorem exists_global_h2_of_isWeakDivergenceSolution
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  let ubase : ℝ^n → ℝ :=
    ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
      (baseIndex n 1) : DerivLp n 2 Omega)
  obtain ⟨Winterior, hWinterior⟩ :=
    exists_interior_h2_localized_piece
      hC1 A a haRep haC1 f u hu alpha halpha hElliptic
  choose Wboundary hWboundary using fun i ↦
    exists_boundaryChart_h2_localized_piece
      hOmega i A a haRep haC1 f u hu alpha halpha hElliptic
  let Wi : Fin hC1.N → W^{2,2}(Omega) :=
    fun i ↦ Wboundary i
  refine ⟨partitionAssembly Winterior Wi, ?_⟩
  simpa [baseRepresentative, ubase, hC1] using
    (partitionAssembly_base_ae hC1 ubase Winterior Wi
      (by simpa [baseRepresentative, ubase, hC1] using hWinterior)
      (fun i ↦ by
        simpa [baseRepresentative, ubase, hC1, Wi] using hWboundary i))

end SobolevSpace.GraphSpace.BoundaryRegularity
