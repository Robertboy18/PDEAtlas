/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PrincipalForms
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Lattice

/-!
# Unshifted weak comparison for the Dirichlet form

On a bounded domain the Poincaré inequality makes the Dirichlet form coercive without a
zeroth-order shift. Ordered traces make the positive part of the difference an admissible
zero-boundary test. Its gradient vanishes off the positive set, so testing the weak inequality
gives a nonpositive Dirichlet energy and forces the positive part to vanish.

The argument is specific to the Laplacian; comparison for operators with lower-order terms
uses the Gårding shift (`Comparison.BoundaryTrace`).
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal InnerProductSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [C1ExtensionAtlas (m + 1) Ω]

/-- Weak subsolutions with ordered traces are ordered almost everywhere. The unshifted
Dirichlet form is coercive by the bounded-domain Poincaré inequality. -/
theorem base_le_ae_of_trace_le_of_dirichlet_inequality
    (P : InwardPartition Ω) (hΩ : Bornology.IsBounded Ω)
    (u v : H¹(Ω))
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace u x ≤ Trace.C1.trace v x)
    (hweak : ∀ t : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x) →
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
        (derivCoordCLM i t)) ≤
      ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) v)
        (derivCoordCLM i t)) :
    ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      wkpBaseCoordinateCLM u x ≤ wkpBaseCoordinateCLM v x := by
  let w := u - v
  let t : H¹₀(Ω) :=
    ⟨lipschitzCompositionOn C1ExtensionAtlas.isOpen Lp.lipschitzWith_pos_part w,
      (Trace.C1.posPart_sub_mem_H10_iff_trace_le P u v).mpr htrace⟩
  have hbase : (baseCoordCLM t : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω]
      fun x ↦ max (wkpBaseCoordinateCLM w x) 0 :=
    lipschitzCompositionOn_base_ae C1ExtensionAtlas.isOpen Lp.lipschitzWith_pos_part w
  have ht : ∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x := by
    filter_upwards [hbase] with x hx
    rw [hx]
    exact le_max_right _ _
  have hloc (i : Fin (m + 1)) :
      inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) w)
        (derivCoordCLM i t) =
      inner ℝ (derivCoordCLM i t) (derivCoordCLM i t) := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    have hcoord := lipschitzCompositionOn_posPart_coordinate_ae w (singleDerivIndex (m + 1) i)
    filter_upwards [hcoord] with x hx
    change derivCoordCLM i t x =
      (if 0 < wkpBaseCoordinateCLM w x then
        wkpCoordinateCLM (singleDerivIndex (m + 1) i) w x else 0) at hx
    rw [hx]
    split_ifs <;> simp
  have hquad : dirichletForm t t ≤ 0 := by
    rw [dirichletForm_apply]
    simp_rw [← hloc]
    have hw := hweak t ht
    simpa only [w, map_sub, inner_sub_left, Finset.sum_sub_distrib, sub_nonpos] using hw
  obtain ⟨c, hc, hcoercive⟩ := dirichletForm_isCoercive (by omega) hΩ
  have htzero : t = 0 := by
    apply norm_eq_zero.mp
    have hsq : ‖t‖ * ‖t‖ ≤ 0 := by
      apply le_of_mul_le_mul_left ?_ hc
      simpa only [mul_assoc, mul_zero] using (hcoercive t).trans hquad
    exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))
  rw [htzero, map_zero] at hbase
  filter_upwards [hbase, Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
    (μ := domainMeasure (m + 1) Ω),
    Lp.coeFn_sub (wkpBaseCoordinateCLM u) (wkpBaseCoordinateCLM v)] with x hx hz hs
  change (0 : DerivLp (m + 1) 2 Ω) x =
    max (wkpBaseCoordinateCLM (u - v) x) 0 at hx
  rw [hz, map_sub, hs] at hx
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq hx.symm)

end SobolevSpace.GraphSpace
