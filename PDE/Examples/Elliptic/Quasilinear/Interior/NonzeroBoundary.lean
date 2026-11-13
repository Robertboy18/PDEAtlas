/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Examples.Elliptic.Quasilinear.Interior.Regularity
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary

/-!
# An interior solution outside `H¹₀`

By the trace theorem, the `H¹` function represented by `x²` on the unit interval is
not in `H¹₀`, since it equals one at the endpoints. The interior regularity theorem
still applies to it, so interior `H²` regularity does not need zero boundary values.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Quasilinear.Interior

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

local notation "Ω₀" => Boundary.Atlas.UnitBall.domain 1

/-- The `H¹` function represented by `x²` on the unit interval is not in `H¹₀`. -/
theorem quadratic_not_mem_h10SubmoduleOn (u : H¹(Ω₀))
    (hu : baseRepresentative u =ᵐ[domainMeasure 1 Ω₀] quadratic) :
    u ∉ h10SubmoduleOn (n := 1) (Ω := Ω₀) := by
  have hnon (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : ENNReal.ofReal 2 = p)
      (U : W^{1,p}(Ω₀))
      (hU : baseRepresentative U =ᵐ[domainMeasure 1 Ω₀] quadratic) :
      U ∉ (wkp0SubmoduleOn (n := 1) (k := 1) (p := p) (Ω := Ω₀)).toSubmodule := by
    subst p
    intro hz
    have hzero := (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
      (Boundary.Atlas.UnitBall.isOpen_domain 1)
      (Boundary.Atlas.UnitBall.bounded_domain 1)
      ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl)
      2 U quadratic_contDiff.continuous.continuousOn hU).mp hz
    have hfront : EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ frontier Ω₀ := by
      simp [Boundary.Atlas.UnitBall.domain, frontier_ball (0 : ℝ^1) one_ne_zero,
        PiLp.norm_single]
    have h := hzero _ hfront
    rw [quadratic_unit_endpoints.1] at h
    exact one_ne_zero h
  exact hnon 2 (ENNReal.ofReal_ofNat 2) u hu

/-- The signed nonlinear equation has a solution with nonzero boundary values that is
`H²` on every open `V` compactly contained in the unit interval, with the interior
estimate. -/
theorem exists_quadratic_nonzero_boundary_interior_H2 {V : Set (ℝ^1)}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω₀) :
    ∃ K : ℝ, 0 < K ∧
      ∃ (u : H¹(Ω₀)) (f : DerivLp 1 2 Ω₀) (W : W^{2,2}(V)),
        u ∉ h10SubmoduleOn (n := 1) (Ω := Ω₀) ∧
        baseRepresentative u =ᵐ[domainMeasure 1 Ω₀] quadratic ∧
        (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω₀] quadraticLoad ∧
        lowerOrderCLM (by omega : 1 ≤ 2) W =
          restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
        ‖W‖ ≤ K * (‖u‖ + ‖f‖) ∧
        (∑ i : Fin 1, ∑ j : Fin 1, ‖W.val (pairDerivIndex 1 i j)‖) ≤
          K * (‖∇ u‖ + ‖f‖) := by
  obtain ⟨K, hK, u, f, W, hu, hf, hW, hnorm, hsecond, _⟩ :=
    exists_quadratic_interior_H2 (Boundary.Atlas.UnitBall.isOpen_domain 1)
      (Boundary.Atlas.UnitBall.bounded_domain 1) hV hVc hVΩ
  exact ⟨K, hK, u, f, W, quadratic_not_mem_h10SubmoduleOn u hu,
    hu, hf, hW, hnorm, hsecond⟩

end PDE.Examples.Quasilinear.Interior
