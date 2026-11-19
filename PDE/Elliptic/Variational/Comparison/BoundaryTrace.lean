/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Comparison.Locality
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Lattice

/-!
# Weak comparison from ordered geometric traces

Ordered H¹ boundary traces make the positive part of the difference an
H¹₀ test. Locality and the Gårding shift then prove interior order
from the weak inequality. No comparison or truncation property is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal InnerProductSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [H : C1ExtensionAtlas (m + 1) Ω]

/-- Weak comparison for arbitrary H¹ states with ordered geometric boundary traces. -/
theorem base_le_ae_of_trace_le_of_shifted_interior_inequality
    (P : InwardPartition Ω)
    (a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω)
    (b : Fin (m + 1) → DerivLp (m + 1) ∞ Ω) (c : DerivLp (m + 1) ∞ Ω)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (hmu : coerciveShift (n := m + 1) alpha beta gamma ≤ mu)
    (u v : H¹(Ω))
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace u x ≤ Trace.C1.trace v x)
    (hweak : ∀ t : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x) →
      interiorFullDivergenceOperator a b c u t +
          mu * inner ℝ (wkpBaseCoordinateCLM u) (baseCoordCLM t) ≤
        interiorFullDivergenceOperator a b c v t +
          mu * inner ℝ (wkpBaseCoordinateCLM v) (baseCoordCLM t)) :
    ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      wkpBaseCoordinateCLM u x ≤ wkpBaseCoordinateCLM v x := by
  let w := u - v
  let t : H¹₀(Ω) :=
    ⟨lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part w,
      (Trace.C1.posPart_sub_mem_H10_iff_trace_le P u v).mpr htrace⟩
  have hbase : (baseCoordCLM t : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω]
      fun x ↦ max (wkpBaseCoordinateCLM w x) 0 :=
    lipschitzCompositionOn_base_ae H.isOpen Lp.lipschitzWith_pos_part w
  have ht : ∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x := by
    filter_upwards [hbase] with x hx
    rw [hx]
    exact le_max_right _ _
  have hquad : shiftedDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu t t ≤ 0 := by
    rw [← interiorFullDivergenceOperator_positivePart_right a b c mu w t
      (lipschitzCompositionOn_posPart_coordinate_ae w)]
    have hw := hweak t ht
    simp only [w, map_sub, sub_apply, inner_sub_left, mul_sub]
    linarith
  have hcoercive := shiftedDivergenceForm_coercive_bound_of_coerciveShift_le
    (multiplicationCoefficientOperator a) (multiplicationFirstOrderOperator b)
    (multiplicationZeroOrderOperator c) hA hbc hmu t
  have htzero : t = 0 := by
    apply norm_eq_zero.mp
    have hsq : ‖t‖ * ‖t‖ ≤ 0 := by
      apply le_of_mul_le_mul_left ?_ (half_pos hA.1)
      simpa only [mul_assoc, mul_zero] using hcoercive.trans hquad
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
