/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.Holder
public import PDE.Common.Euclidean

/-!
# Euclidean tuples of Lp functions

Finitely many scalar Lp functions assemble continuously into a Euclidean-valued Lp
function. This map transports weak limits of coordinate families without changing the
Euclidean norm used to bound the assembled functions.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Assemble scalar Lp coordinates as a Euclidean-valued Lp function. -/
def euclideanTuple :
    (Fin n → Lp ℝ p μ) →L[ℝ] Lp (ℝ^n) p μ :=
  ∑ i : Fin n,
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single i (1 : ℝ))).compLpL p μ).comp
        (ContinuousLinearMap.proj i)

/-- The assembled function has the prescribed scalar coordinates almost everywhere. -/
theorem euclideanTuple_apply_ae (f : Fin n → Lp ℝ p μ) :
    ∀ᵐ x ∂μ, ∀ i : Fin n, (euclideanTuple f x) i = f i x := by
  let L (i : Fin n) : ℝ →L[ℝ] ℝ^n :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))
  have hcomp : ∀ᵐ x ∂μ, ∀ i : Fin n,
      (L i).compLpL p μ (f i) x = L i (f i x) :=
    ae_all_iff.mpr fun i ↦ (L i).coeFn_compLpL _
  have hsum : euclideanTuple f = ∑ i : Fin n, (L i).compLpL p μ (f i) := by
    simp only [euclideanTuple, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, L]
  rw [hsum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ (L i).compLpL p μ (f i)), hcomp] with x hx hL
  intro j
  rw [hx]
  change EuclideanSpace.proj j (∑ i : Fin n, (L i).compLpL p μ (f i) x) = _
  rw [map_sum]
  simp only [hL]
  simp [L]

/-- Assembling the coordinates of a Euclidean-valued function recovers that Lp function. -/
theorem euclideanTuple_coordinates (f : Lp (ℝ^n) p μ) :
    euclideanTuple (fun i ↦
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL p μ f) = f := by
  apply Lp.ext
  have hcoord : ∀ᵐ x ∂μ, ∀ i : Fin n,
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL p μ f x = (f x) i :=
    ae_all_iff.mpr fun i ↦
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).coeFn_compLpL f
  filter_upwards [euclideanTuple_apply_ae
    (fun i ↦ (EuclideanSpace.proj i :
      ℝ^n →L[ℝ] ℝ).compLpL p μ f), hcoord] with x hx hy
  exact PiLp.ext fun i ↦ (hx i).trans (hy i)

/-- Euclidean-valued Lp is continuously linearly equivalent to the finite product of its
scalar coordinate spaces. This is an equivalence of topological vector spaces, not an
identification of the Euclidean norm with the product supremum norm. -/
def euclideanTupleEquiv :
    (Fin n → Lp ℝ p μ) ≃L[ℝ] Lp (ℝ^n) p μ := by
  let P (i : Fin n) : ℝ^n →L[ℝ] ℝ := EuclideanSpace.proj i
  let C : Lp (ℝ^n) p μ →L[ℝ] (Fin n → Lp ℝ p μ) :=
    ContinuousLinearMap.pi fun i ↦ (P i).compLpL p μ
  refine ContinuousLinearEquiv.equivOfInverse euclideanTuple C ?_ euclideanTuple_coordinates
  intro f
  funext i
  apply Lp.ext
  filter_upwards [(P i).coeFn_compLpL (euclideanTuple f),
    euclideanTuple_apply_ae f] with x hx hy
  exact hx.trans (hy i)

/-- A Euclidean tuple is bounded by the sum of its coordinate norms. -/
theorem norm_euclideanTuple_le (f : Fin n → Lp ℝ p μ) :
    ‖euclideanTuple f‖ ≤ ∑ i, ‖f i‖ := by
  simp only [euclideanTuple, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  change ‖(ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLp (f i)‖ ≤ _
  simpa using
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).norm_compLp_le
      (f i)

/-- The squared `L²` norm of a Euclidean tuple is the sum of the squared coordinate norms. -/
theorem norm_euclideanTuple_sq (f : Fin n → Lp ℝ 2 μ) :
    ‖euclideanTuple f‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [norm_sq_eq_integral_norm_sq]
  calc
    (∫ x, ‖euclideanTuple f x‖ ^ 2 ∂μ) = ∫ x, ∑ i, (f i x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [euclideanTuple_apply_ae f] with x hx
      simp only [EuclideanSpace.real_norm_sq_eq, hx]
    _ = ∑ i, ∫ x, (f i x) ^ 2 ∂μ :=
      integral_finsetSum _ fun i _ ↦ (Lp.memLp (f i)).integrable_sq
    _ = ∑ i, ‖f i‖ ^ 2 := by simp only [norm_sq_eq_integral_sq]

/-- Euclidean-valued `L²` is isometric to the finite Hilbert product of scalar `L²` spaces. -/
def euclideanTupleIsometry :
    PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 μ) ≃ₗᵢ[ℝ] Lp (ℝ^n) 2 μ where
  toLinearEquiv :=
    ((PiLp.continuousLinearEquiv 2 ℝ _).trans euclideanTupleEquiv).toLinearEquiv
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact (norm_euclideanTuple_sq (fun i ↦ f i)).trans (PiLp.norm_sq_eq_of_L2 _ f).symm

/-- The Hilbert-product isometry is the coordinate assembler `euclideanTuple`. -/
theorem euclideanTupleIsometry_apply
    (f : PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 μ)) :
    euclideanTupleIsometry f = euclideanTuple (fun i ↦ f i) :=
  rfl

/-- The `L²` pairing of Euclidean tuples is the sum of their scalar coordinate pairings. -/
theorem inner_euclideanTuple (f g : Fin n → Lp ℝ 2 μ) :
    inner ℝ (euclideanTuple f) (euclideanTuple g) = ∑ i, inner ℝ (f i) (g i) := by
  exact euclideanTupleIsometry.inner_map_map
    ((PiLp.continuousLinearEquiv 2 ℝ _).symm f)
    ((PiLp.continuousLinearEquiv 2 ℝ _).symm g)

/-- A scalar bounded multiplier commutes with assembling the Euclidean coordinates. -/
theorem euclideanTuple_lpSMul (a : Lp ℝ ∞ μ) (f : Fin n → Lp ℝ p μ) :
    euclideanTuple (fun i ↦ a • f i) = a • euclideanTuple f := by
  apply Lp.ext
  have hmul : ∀ᵐ x ∂μ, ∀ i : Fin n, (a • f i) x = a x * f i x :=
    ae_all_iff.mpr fun i ↦ coeFn_lpSMul (r := p) a (f i)
  filter_upwards [euclideanTuple_apply_ae (fun i ↦ a • f i),
    euclideanTuple_apply_ae f, coeFn_lpSMul (r := p) a (euclideanTuple f), hmul]
    with x hx hf ha hm
  change (a • euclideanTuple f) x = a x • euclideanTuple f x at ha
  rw [ha]
  apply PiLp.ext
  intro i
  change (euclideanTuple (fun i ↦ a • f i) x) i = a x * (euclideanTuple f x) i
  rw [hx i, hf i, hm i]

/-- Each coordinate's `L²` norm is bounded by the Euclidean tuple norm. -/
theorem norm_coordinate_le_norm_euclideanTuple (f : Fin n → Lp ℝ 2 μ) (i : Fin n) :
    ‖f i‖ ≤ ‖euclideanTuple f‖ := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg ‖f j‖)
    (Finset.mem_univ i)
  rw [← norm_euclideanTuple_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The `L²` pairing of flattened real matrices is the integral of all entrywise products. -/
theorem inner_eq_integral_prod_sum {m : ℕ}
    (f g : Lp (ℝ^(m * n)) 2 μ) :
    inner ℝ f g = ∫ x, ∑ i : Fin m, ∑ j : Fin n,
      f x (finProdFinEquiv (i, j)) * g x (finProdFinEquiv (i, j)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  change (∑ k : Fin (m * n), inner ℝ (f x k) (g x k)) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp [Fintype.sum_prod_type, RCLike.inner_apply, mul_comm]

end MeasureTheory.Lp
