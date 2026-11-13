/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.EuclideanCoordinates
public import PDE.Analysis.MeasureTheory.Lp.ExponentLift
public import PDE.Analysis.MeasureTheory.Lp.FiniteRankTransport
public import PDE.Analysis.Normed.Operator.FiniteProduct

/-!
# Coordinates of `L²` fields on a subset

A Euclidean-valued `L²` field `f` on a measure space restricts to a set `s` and splits into its
scalar coordinates on `s`: `restrictCoordinates s f` in the finite Hilbert product of the scalar
`L²(s)` spaces. Its coordinates represent the components of `f` on `s`, its norm is at most that
of `f`, and its pairing with a coordinate tuple `g` is the integral over `s` of the pointwise
inner product of `f` with the assembled tuple.

On a finite measure the coordinatewise inclusion `piLpExponentInclusion` maps tuples of `Lᵖ`
functions to tuples of `L^q` functions for `q ≤ p`. The squared norm of a bounded-matrix
transport is the integral of the squared Euclidean norm of the pointwise matrix action.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace MeasureTheory.Lp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}

/-- The scalar `L²` coordinates on `s` of a Euclidean-valued `L²` field. -/
def restrictCoordinates (s : Set X) :
    Lp (ℝ^n) 2 μ →L[ℝ] PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 (μ.restrict s)) :=
  (euclideanTupleIsometry (n := n) (μ := μ.restrict s)).symm.toContinuousLinearEquiv
    |>.toContinuousLinearMap.comp (LpToLpRestrictCLM X (ℝ^n) ℝ μ 2 s)

/-- Assembling the restricted coordinates gives the restriction of the field. -/
theorem euclideanTupleIsometry_restrictCoordinates (s : Set X) (f : Lp (ℝ^n) 2 μ) :
    euclideanTupleIsometry (restrictCoordinates s f) = LpToLpRestrictCLM X (ℝ^n) ℝ μ 2 s f := by
  simp only [restrictCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]

/-- The restricted coordinates represent the components of the field on `s`. -/
theorem restrictCoordinates_apply_ae (s : Set X) (f : Lp (ℝ^n) 2 μ) (i : Fin n) :
    (restrictCoordinates s f i : X → ℝ) =ᵐ[μ.restrict s] fun x ↦ f x i := by
  have h := euclideanTupleIsometry_restrictCoordinates s f
  rw [euclideanTupleIsometry_apply] at h
  filter_upwards [euclideanTuple_apply_ae (fun i ↦ restrictCoordinates s f i),
    LpToLpRestrictCLM_coeFn ℝ s f] with x hx hr
  rw [← hx i, h, hr]

/-- Restricting to a subset does not increase the norm. -/
theorem norm_restrictCoordinates_le (s : Set X) (f : Lp (ℝ^n) 2 μ) :
    ‖restrictCoordinates s f‖ ≤ ‖f‖ := by
  rw [← LinearIsometryEquiv.norm_map euclideanTupleIsometry,
    euclideanTupleIsometry_restrictCoordinates]
  exact norm_Lp_toLp_restrict_le s f

/-- The pairing of the restricted coordinates with a coordinate tuple is the integral over `s`
of the pointwise inner product with the assembled tuple. -/
theorem inner_restrictCoordinates (s : Set X) (f : Lp (ℝ^n) 2 μ)
    (g : PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 (μ.restrict s))) :
    ⟪restrictCoordinates s f, g⟫ = ∫ x in s, ⟪f x, euclideanTupleIsometry g x⟫ ∂μ := by
  rw [← LinearIsometryEquiv.inner_map_map euclideanTupleIsometry,
    euclideanTupleIsometry_restrictCoordinates, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ s f] with x hx
  rw [hx]

/-- On a finite measure, the coordinatewise inclusion of `Lᵖ` tuples into `L^q` tuples for
`q ≤ p`. -/
def piLpExponentInclusion [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hqp : q ≤ p) (ι : Type*) :
    PiLp 2 (fun _ : ι ↦ Lp ℝ p μ) →L[ℝ] PiLp 2 (fun _ : ι ↦ Lp ℝ q μ) :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦
    (ContinuousLinearMap.id ℝ (Lp ℝ p μ)).liftLpExponent (q := q)
      (fun f ↦ (Lp.memLp f).mono_exponent hqp)

/-- The coordinatewise inclusion keeps the representatives. -/
theorem piLpExponentInclusion_apply_ae [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hqp : q ≤ p) {ι : Type*} (A : PiLp 2 (fun _ : ι ↦ Lp ℝ p μ))
    (i : ι) : (piLpExponentInclusion hqp ι A i : X → ℝ) =ᵐ[μ] A i := by
  rw [piLpExponentInclusion, ContinuousLinearMap.piLpMap_apply]
  exact (ContinuousLinearMap.id ℝ (Lp ℝ p μ)).coeFn_liftLpExponent (q := q)
    (fun f ↦ (Lp.memLp f).mono_exponent hqp) (A i)

end MeasureTheory.Lp

namespace ContinuousLinearMap

variable {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι] [Fintype κ]

/-- The squared norm of a bounded-matrix transport is the integral of the squared Euclidean norm
of the pointwise matrix action. -/
theorem norm_l2MatrixTransport_apply_sq (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ)) :
    ‖l2MatrixTransport D A‖ ^ 2 = ∫ x, ∑ k, (∑ i, D (k, i) x * A i x) ^ 2 ∂μ := by
  have hprod (k : κ) (i : ι) :
      ((D (k, i) • A i : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] fun x ↦ D (k, i) x * A i x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (D (k, i)) (A i)] with x hx
    simpa using hx
  have hpair (k : κ) (i j : ι) :
      ⟪D (k, i) • A i, D (k, j) • A j⟫ =
        ∫ x, D (k, i) x * A i x * (D (k, j) x * A j x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hprod k i, hprod k j] with x hi hj
    simp only [hi, hj, RCLike.inner_apply, conj_trivial]
    ring
  have hint (k : κ) (i j : ι) :
      Integrable (fun x ↦ D (k, i) x * A i x * (D (k, j) x * A j x)) μ := by
    refine (L2.integrable_inner (𝕜 := ℝ) (D (k, i) • A i) (D (k, j) • A j)).congr ?_
    filter_upwards [hprod k i, hprod k j] with x hi hj
    simp only [hi, hj, RCLike.inner_apply, conj_trivial]
    ring
  have hsq_int (k : κ) : Integrable (fun x ↦ (∑ i, D (k, i) x * A i x) ^ 2) μ := by
    simp_rw [sq, Finset.sum_mul_sum]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint k i j
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun k _ ↦ hsq_int k]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← real_inner_self_eq_norm_sq, l2MatrixTransport_apply, sum_inner]
  simp_rw [inner_sum, hpair, sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint k i j]
  exact Finset.sum_congr rfl fun i _ ↦ (integral_finsetSum _ fun j _ ↦ hint k i j).symm

end ContinuousLinearMap
