/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.WeakBarrier
public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Truncation
import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Continuity

/-!
# Boundary continuity on C¹ domains

The intrinsic normal gives an explicit angular barrier at each boundary point.
Its small upper truncation is a weak supersolution and has a continuous
representative, vanishing only at that point. Weak comparison therefore gives
the boundary limit of a harmonic function with continuous trace data.

This is a continuity theorem. It does not assert a continuous boundary gradient
or a classical normal derivative on a merely C¹ domain.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.BoundaryContinuity

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open SobolevSpace.Trace.C1
open scoped ENNReal InnerProductSpace Topology

/-- Every boundary point of a bounded C¹ domain in dimension at least two
admits a continuous Dirichlet supersolution, positive away from its vertex. -/
theorem exists_continuous_dirichlet_barrier
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} [C1ExtensionAtlas n Ω]
    (hn : 2 ≤ n) (hbounded : Bornology.IsBounded Ω) (z : frontier Ω) :
    ∃ B : H¹(Ω), ∃ b : ℝ^n → ℝ,
      Continuous b ∧ baseRepresentative B =ᵐ[domainMeasure n Ω] b ∧
      b z = 0 ∧ (∀ x, 0 ≤ b x) ∧ (∀ x : ℝ^n, x ≠ (z : ℝ^n) → 0 < b x) ∧
      ∀ t : H¹₀(Ω),
        (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x) →
        0 ≤ ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) B)
          (derivCoordCLM i t) := by
  obtain ⟨c, hc, B, hB, hsuper⟩ := exists_truncated_angularPowerBarrier hn hbounded z
  let a : ℝ := 1 / (32 * (n : ℝ))
  let N : ℝ^n := -outwardUnitNormal (Ω := Ω) z
  let b : ℝ^n → ℝ := fun x ↦ min c (angularPowerBarrier a N (x - z))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hN : ‖N‖ = 1 := by simp only [N, norm_neg, norm_outwardUnitNormal]
  have hbz : b z = 0 := by
    simp only [b, sub_self, angularPowerBarrier_zero ha, min_eq_right hc.le]
  have hbpos (x : ℝ^n) (hx : x ≠ z) : 0 < b x := by
    have hne : x - (z : ℝ^n) ≠ 0 := sub_ne_zero.mpr hx
    exact lt_min hc ((mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) a)).trans_le
        (angularPowerBarrier_bounds a hN hne).1)
  refine ⟨B, b, continuous_const.min ((continuous_angularPowerBarrier ha hN).comp
    (continuous_id.sub continuous_const)), hB, hbz, ?_, hbpos, hsuper⟩
  intro x
  by_cases hx : x = z
  · simpa only [hx, hbz] using (le_refl (0 : ℝ))
  · exact (hbpos x hx).le

/-- Continuous trace data determine the boundary limits of an interior
continuous weak harmonic representative on a bounded C¹ domain. -/
theorem tendsto_at_boundary_of_c1Domain
    {m : ℕ} {Ω : Set ℝ^(m + 1)} [C1ExtensionAtlas (m + 1) Ω]
    (hn : 2 ≤ m + 1) (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (U : H¹(Ω)) {u g : ℝ^(m + 1) → ℝ}
    (hu : ContinuousOn u Ω) (hg : ContinuousOn g (closure Ω))
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] u)
    (htrace : (Trace.C1.trace U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] g)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0)
    (z : frontier Ω) :
    Tendsto u (𝓝[Ω] (z : ℝ^(m + 1))) (𝓝 (g z)) := by
  obtain ⟨B, b, hb, hB, hbz, hb0, hbpos, hsuper⟩ :=
    exists_continuous_dirichlet_barrier hn hbounded z
  exact tendsto_at_boundary_of_dirichlet_barrier P hbounded U B hu hg hb.continuousOn
    hU hB htrace hweak hsuper z hbz (fun x _ ↦ hb0 x) (fun x _ ↦ hbpos x)

end PDE.Elliptic.BoundaryContinuity
