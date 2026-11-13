/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.AllOrders
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing.Components

/-!
# All-order parabolic estimate for finite forcing data

For every `m ≥ 0`, the data consist of `g ∈ H^{2m+1}` and the adjacent
weak forcing derivatives in `L²(H^{2(m-k)})`, `0 ≤ k ≤ m`. The compatibility
values are recursively computed as `g_{j+1} = f_j(a) - Lg_j`; their only extra
condition is zero spatial boundary trace through `j = m`.

The theorem constructs every solution derivative and bounds their full finite
sum. It applies to every original weak solution of the full smooth autonomous
operator on a domain with smooth boundary graphs. Its constant is chosen
before all data.
This is Evans's §7.1.3, Theorem 6 (Higher regularity), with the estimate (55).
The order `2((m+1)-k)` equals `2m+2-2k` on the stated finite index range.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 6 (Higher regularity), (55), and the remark
  after it, p. 386.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Full all-order parabolic regularity from a finite forcing family.
No higher initial datum or solution trajectory is assumed. Compatibility uses
only the recursively derived initial values, and every derivative norm appears
in the estimate, including the final `L²(L²)` term. -/
theorem exists_all_order_regularity_of_finite_family (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (k : Fin (m + 1)) →
        Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b)))
        (hf : ∀ k : Fin m, HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ wkpBaseCoordinateCLM (f k.castSucc t))
          (fun t ↦ wkpBaseCoordinateCLM (f k.succ t)))
        (g : W^{(2 * m + 1),2}(Ω)),
      Compatible (P.load hopen hbounded) hopen hbounded (hgraph 2) hab
        (ForcingJet.ofFamily f) (ForcingJet.hasWeakDerivatives_ofFamily hopen f hf) g →
      ∀ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
          ((wkpBaseCoordinateCLM (n := n) (m := 2 * m) (p := 2) (Ω := Ω)).compLpL
            2 (volume.restrict (Ioc a b)) (f 0))) u (wkpBaseCoordinateCLM g) →
      ∃ U : (k : Fin (m + 2)) →
        Lp (W^{(2 * (m + 1 - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b)),
        (∀ k : Fin (m + 1), HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ wkpBaseCoordinateCLM (U k.castSucc t))
          (fun t ↦ wkpBaseCoordinateCLM (U k.succ t))) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          wkpBaseCoordinateCLM (U 0 t) = baseCoordCLM (u t)) ∧
        (∑ k : Fin (m + 2), ‖U k‖) ≤ C * (‖g‖ + ∑ k : Fin (m + 1), ‖f k‖) := by
  obtain ⟨C, hC, hreg⟩ :=
    exists_all_order_regularity P hopen hbounded hgraph hab hsymm halpha hell m
  refine ⟨C, hC, ?_⟩
  intro f hf g hcompat u hu
  have hu' : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL
        2 (volume.restrict (Ioc a b)) (ForcingJet.ofFamily f).headBase) u
      (wkpBaseCoordinateCLM g) := by
    simpa only [ForcingJet.headBase, ForcingJet.head_ofFamily] using hu
  obtain ⟨U, hU, hUbase, hUnorm⟩ := hreg (ForcingJet.ofFamily f)
    (ForcingJet.hasWeakDerivatives_ofFamily hopen f hf) g hcompat u hu'
  refine ⟨U.component, hU.components, ?_, ?_⟩
  · filter_upwards [hUbase] with t ht
    rw [ForcingJet.base_component_zero]
    exact ht
  · rw [← U.normSum_eq_sum]
    simpa only [ForcingJet.normSum_ofFamily] using hUnorm

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
