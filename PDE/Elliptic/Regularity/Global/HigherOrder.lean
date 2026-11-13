/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.HigherOrder.ChartPiece
import PDE.Elliptic.Regularity.Global.H2
import PDE.Elliptic.Regularity.Interior.HigherOrderPartitionPiece
import PDE.Spaces.Sobolev.Localization.Assembly.Partition

/-!
# Global higher-order elliptic regularity for the principal divergence operator

Let the domain be bounded with a `C2BoundaryAtlas` whose charts are `C^{k+2}` with `C^{k+1}`
inverses. An `H¹₀` weak solution of the principal divergence-form equation with forcing in `W^{k,2}`
and principal coefficients in `W^{k+1,∞}` with globally `C^{k+1}` representatives has a `W^{k+2,2}`
representative (`exists_global_higherOrder_of_isWeakDivergenceSolution`). This is the qualitative
part of Evans's §6.3.2, Theorem 5 (Higher boundary regularity), for an operator without lower-order
terms.

## How it works

Evans argues by induction on `m` on a half-ball. The tangential derivatives `D^α u` with `αₙ = 0`
vanish on the flat boundary and solve an equation of the same form, so the proof of Theorem 4
applies to them, (85)-(90); the derivatives with more normal directions then come from the equation,
by induction on `βₙ`, (91)-(94), and straightening the boundary gives the general case. We also
induct on the order `k`, starting from `exists_global_h2_of_isWeakDivergenceSolution`. At each
successor, the preceding global theorem supplies the physical Sobolev representative and the
lower-order theorem needed by the interior differentiated equations.
`exists_interior_higherOrder_localized_piece` and `exists_boundaryChart_higherOrder_localized_piece`
give the interior and boundary pieces, and `partitionAssembly` assembles them into the next global
representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity) and its proof,
  (72)-(94), pp. 340-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/--
The qualitative part of Evans's §6.3.2, Theorem 5, for the principal operator.

On a bounded domain equipped with `C2BoundaryAtlas` and boundary charts of
the indicated orders, forcing in `W^{k,2}` and principal coefficients in
`W^{k+1,∞}` with global `C^{k+1}` representatives promote an `H¹₀` weak
solution to `W^{k+2,2}`.
`Boundary.HasContDiffGraphBoundary.exists_higherOrderBoundaryAtlas` constructs such an
atlas from a `C^{k+2}` graph boundary.
-/
theorem exists_global_higherOrder_of_isWeakDivergenceSolution
    (k : ℕ)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1)
        (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j,
      ContDiff ℝ (k + 1) (fun x ↦ a x i j))
    (F : W^{k,2}(Omega))
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega)
        (baseIndex n k) : DerivLp n 2 Omega)
      u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{k + 2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  induction k using Nat.strong_induction_on generalizing u with
  | h k ih =>
      rcases k with _ | r
      · simpa using exists_global_h2_of_isWeakDivergenceSolution hOmega A a haRep haContDiff
          _ u hu alpha halpha hElliptic
      · let Aprev : Fin n → Fin n → W^{r + 1,∞}(Omega) := fun i j ↦
          lowerOrderCLM (n := n) (k := r + 1) (m := r + 2) (p := ∞) (Ω := Omega) (by omega)
            (A i j)
        have hprev := ih r (by omega) (fun i ↦ (hChart i).of_le (by gcongr; omega))
          (fun i ↦ (hChartSymm i).of_le (by gcongr; omega)) Aprev
          (fun i j ↦ by simpa [Aprev] using haRep i j)
          (fun i j ↦ (haContDiff i j).of_le (by gcongr; omega))
        obtain ⟨U, hU⟩ := hprev (lowerOrderCLM (n := n) (k := r) (m := r + 1) (p := 2)
          (Ω := Omega) (by omega) F) u (by simpa [Aprev] using hu)
        obtain ⟨Winterior, hWinterior⟩ := exists_interior_higherOrder_localized_piece (r + 1)
          (by omega) hOmega A F u hu U hU fun G v hv ↦ hprev G v hv
        choose Wboundary hWboundary using fun i ↦
          exists_boundaryChart_higherOrder_localized_piece (r + 1) (by omega) hOmega i (hChart i)
            (hChartSymm i) A a haRep haContDiff F u hu alpha halpha hElliptic U hU
        refine ⟨partitionAssembly Winterior Wboundary, ?_⟩
        simpa [baseRepresentative] using partitionAssembly_base_ae hOmega.toC1ExtensionAtlas _
          Winterior Wboundary (by simpa [baseRepresentative] using hWinterior)
            fun i ↦ by simpa [baseRepresentative] using hWboundary i

end SobolevSpace.GraphSpace.BoundaryRegularity
