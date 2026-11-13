/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarAncient
public import PDE.Analysis.Evolution.Semigroup.Duhamel.BoundedPerturbation
public import PDE.Analysis.Normed.ContinuousMap.Bounded.Bilinear

/-!
# Forced ancient evolution with a bounded first-order perturbation

Let `T : H¹ → L²` be a bounded linear perturbation of vector fields on `ℝ³` with
`‖T‖ ≤ B`. The half-order free projected self-similar heat mass decreases as the
inverse square root of the time weight, so an explicit weight depending only on
`B` makes the product of the free bound and `B` less than one half. At this weight
every bounded continuous forcing has a unique forced ancient mild path. The decoded
identity is a convergent Bochner integral and the physical output is divergence
free.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped Sobolev BoundedContinuousFunction

namespace NavierStokes.Selfsimilar

private local instance linearizedZeroPathNormedSpace (a : ℝ) :
    NormedSpace ℝ (Iic a →ᵇ VectorH 3 0) :=
  BoundedContinuousFunction.instNormedSpace

private local instance linearizedOnePathNormedSpace (a : ℝ) :
    NormedSpace ℝ (Iic a →ᵇ VectorH 3 1) :=
  BoundedContinuousFunction.instNormedSpace

section Weight

variable {B : ℝ} (hB : 0 ≤ B)

/-- The numerator in the product of the free heat bound and the perturbation bound. -/
def perturbedAncientNumerator (B : ℝ) : ℝ :=
  singularSelfsimilarConstant 3 0 0 * Real.sqrt Real.pi * B

include hB in
theorem perturbedAncientNumerator_nonneg : 0 ≤ perturbedAncientNumerator B :=
  mul_nonneg (mul_nonneg (singularSelfsimilarConstant_nonneg 3 0 0)
    (Real.sqrt_nonneg _)) hB

/-- An explicit positive weight that dominates the perturbation. -/
def perturbedAncientWeight (B : ℝ) : ℝ :=
  (2 * perturbedAncientNumerator B + 1) ^ 2

include hB in
theorem perturbedAncientWeight_pos : 0 < perturbedAncientWeight B := by
  have h := perturbedAncientNumerator_nonneg hB
  unfold perturbedAncientWeight
  positivity

/-- The free smoothing bound at the chosen weight. -/
def perturbedAncientConstant (B : ℝ) : ℝ :=
  singularSelfsimilarConstant 3 0 0 * Real.sqrt Real.pi /
    (2 * perturbedAncientNumerator B + 1)

include hB in
theorem perturbedAncientConstant_nonneg : 0 ≤ perturbedAncientConstant B := by
  unfold perturbedAncientConstant
  exact div_nonneg
    (mul_nonneg (singularSelfsimilarConstant_nonneg 3 0 0) (Real.sqrt_nonneg _))
    (by linarith [perturbedAncientNumerator_nonneg hB])

include hB in
/-- The exact Gamma mass at this weight is the explicit free smoothing constant. -/
theorem perturbedAncientConstant_eq_mass :
    perturbedAncientConstant B =
      singularSelfsimilarConstant 3 0 0 * smoothingMass (1 / 2) (perturbedAncientWeight B) := by
  rw [smoothingMass_one_half, perturbedAncientWeight,
    Real.sqrt_sq (by linarith [perturbedAncientNumerator_nonneg hB])]
  unfold perturbedAncientConstant
  ring

include hB in
/-- The perturbation budget at the chosen weight is strictly below one half. -/
theorem perturbedAncientConstant_mul_lt : perturbedAncientConstant B * B < 1 / 2 := by
  have hD := perturbedAncientNumerator_nonneg hB
  have hden : 0 < 2 * perturbedAncientNumerator B + 1 := by linarith
  have heq : perturbedAncientConstant B * B =
      perturbedAncientNumerator B / (2 * perturbedAncientNumerator B + 1) := by
    unfold perturbedAncientConstant perturbedAncientNumerator
    ring
  rw [heq]
  exact (div_lt_iff₀ hden).mpr (by linarith)

end Weight

variable (T : VectorH 3 1 →L[ℝ] VectorH 3 0) {B : ℝ} (hB : 0 ≤ B) (hT : ‖T‖ ≤ B)

/-- The perturbation acts pointwise on bounded continuous paths. -/
def perturbedTransportPath (a : ℝ) :
    (Iic a →ᵇ VectorH 3 1) →L[ℝ] (Iic a →ᵇ VectorH 3 0) :=
  T.compLeftContinuousBounded (Iic a)

@[simp]
theorem perturbedTransportPath_apply (a : ℝ) (v : Iic a →ᵇ VectorH 3 1) (t : Iic a) :
    perturbedTransportPath T a v t = T (v t) :=
  rfl

include hT in
theorem norm_perturbedTransportPath_le (a : ℝ) : ‖perturbedTransportPath T a‖ ≤ B :=
  (T.norm_compLeftContinuousBounded_le (Iic a)).trans hT

/-- The free projected Green map at the weight determined by the perturbation bound. -/
def perturbedFreeAncientOperator (a : ℝ) :
    (Iic a →ᵇ VectorH 3 0) →L[ℝ] (Iic a →ᵇ VectorH 3 1) :=
  ancientSelfsimilarDuhamelOperator 3 0 a
    (perturbedAncientWeight B) (perturbedAncientWeight B) 0
    (by norm_num) (perturbedAncientWeight_pos hB)
    (perturbedAncientWeight_pos hB).le le_rfl

theorem norm_perturbedFreeAncientOperator_le (a : ℝ) :
    ‖perturbedFreeAncientOperator hB a‖ ≤ perturbedAncientConstant B := by
  rw [perturbedAncientConstant_eq_mass hB]
  simpa only [perturbedFreeAncientOperator, sub_zero, sub_self, zero_mul, Real.exp_zero,
    mul_one] using
    norm_ancientSelfsimilarDuhamelOperator_le (n := 3) (k := 0) a
      (perturbedAncientWeight B) (perturbedAncientWeight B) 0
      (by norm_num) (perturbedAncientWeight_pos hB)
      (perturbedAncientWeight_pos hB).le le_rfl

include hT in
/-- Every bounded continuous forcing has exactly one ancient mild response
in the specified sufficiently rapidly decaying weighted class. -/
theorem existsUnique_perturbedLinearizedAncient (a : ℝ) (f : Iic a →ᵇ VectorH 3 0) :
    ∃! v : Iic a →ᵇ VectorH 3 1,
      v = perturbedFreeAncientOperator hB a (f - perturbedTransportPath T a v) :=
  @existsUnique_boundedPerturbation
    (Iic a →ᵇ VectorH 3 1) (Iic a →ᵇ VectorH 3 0)
    inferInstance (linearizedOnePathNormedSpace a)
    inferInstance (linearizedZeroPathNormedSpace a) inferInstance
    (perturbedFreeAncientOperator hB a) (perturbedTransportPath T a) _ _
    (perturbedAncientConstant_nonneg hB) hB
    (norm_perturbedFreeAncientOperator_le hB a)
    (norm_perturbedTransportPath_le T hT a)
    (lt_trans (perturbedAncientConstant_mul_lt hB) (by norm_num)) f

include hT in
/-- The perturbation costs at most twice the free bound. -/
theorem norm_perturbedLinearizedAncient_le (a : ℝ)
    {f : Iic a →ᵇ VectorH 3 0} {v : Iic a →ᵇ VectorH 3 1}
    (hv : v = perturbedFreeAncientOperator hB a (f - perturbedTransportPath T a v)) :
    ‖v‖ ≤ 2 * perturbedAncientConstant B * ‖f‖ :=
  @norm_boundedPerturbation_le_twice
    (Iic a →ᵇ VectorH 3 1) (Iic a →ᵇ VectorH 3 0)
    inferInstance (linearizedOnePathNormedSpace a)
    inferInstance (linearizedZeroPathNormedSpace a)
    (perturbedFreeAncientOperator hB a) (perturbedTransportPath T a) _ _
    (perturbedAncientConstant_nonneg hB)
    (norm_perturbedFreeAncientOperator_le hB a)
    (norm_perturbedTransportPath_le T hT a)
    (perturbedAncientConstant_mul_lt hB).le f v hv

/-- Decoding a constant linear perturbation commutes with the exponential time weight. -/
theorem ancientLift_perturbedTransportForcing (a β : ℝ)
    (f : Iic a →ᵇ VectorH 3 0) (v : Iic a →ᵇ VectorH 3 1) (t : ℝ) :
    ancientLift β (f - perturbedTransportPath T a v) t =
      ancientLift β f t - T (ancientLift β v t) := by
  simp only [ancientLift, ContinuousMap.coe_mk, BoundedContinuousFunction.sub_apply,
    perturbedTransportPath_apply, smul_sub, map_smul]

include hB in
/-- The perturbed forcing has a convergent free-kernel past integral. -/
theorem integrableOn_perturbedLinearizedAncient (a : ℝ)
    (f : Iic a →ᵇ VectorH 3 0) (v : Iic a →ᵇ VectorH 3 1) (t : ℝ) :
    IntegrableOn (fun r ↦ projectedSelfsimilarHeatGainKernel 3 0 r
      (ancientLift (perturbedAncientWeight B) f (t - r) -
        T (ancientLift (perturbedAncientWeight B) v (t - r)))) (Ioi 0) := by
  simpa only [ancientLift_perturbedTransportForcing] using
    integrableOn_selfsimilarAncientLift (n := 3) (k := 0) (ω := 0)
      (β := perturbedAncientWeight B) (by norm_num)
      (perturbedAncientWeight_pos hB) (f - perturbedTransportPath T a v) t

/-- The physical path solves the literal free-kernel integral equation with the
perturbation. -/
theorem perturbedLinearizedAncient_eq_integral (a : ℝ)
    {f : Iic a →ᵇ VectorH 3 0} {v : Iic a →ᵇ VectorH 3 1}
    (hv : v = perturbedFreeAncientOperator hB a (f - perturbedTransportPath T a v))
    {t : ℝ} (ht : t ≤ a) :
    ancientLift (perturbedAncientWeight B) v t =
      ∫ r in Ioi (0 : ℝ), projectedSelfsimilarHeatGainKernel 3 0 r
        (ancientLift (perturbedAncientWeight B) f (t - r) -
          T (ancientLift (perturbedAncientWeight B) v (t - r))) := by
  conv_lhs => rw [hv]
  simpa only [perturbedFreeAncientOperator, ancientLift_perturbedTransportForcing] using
    ancientLift_ancientSelfsimilarDuhamelOperator (n := 3) (k := 0) a
      (perturbedAncientWeight B) (perturbedAncientWeight B) 0
      (by norm_num) (perturbedAncientWeight_pos hB)
      (perturbedAncientWeight_pos hB).le le_rfl
      (f - perturbedTransportPath T a v) ht

/-- Every weighted path value has a divergence-free physical base field. -/
theorem perturbedLinearizedAncient_base_mem_solenoidal (a : ℝ)
    {f : Iic a →ᵇ VectorH 3 0} {v : Iic a →ᵇ VectorH 3 1}
    (hv : v = perturbedFreeAncientOperator hB a (f - perturbedTransportPath T a v))
    (t : Iic a) :
    l2SobolevRow (baseIndex 3 1) (v t) ∈ l2Solenoidal 3 := by
  rw [hv]
  exact ancientSelfsimilarDuhamelOperator_base_mem_solenoidal
    a (perturbedAncientWeight B) (perturbedAncientWeight B) 0
    (by norm_num) (perturbedAncientWeight_pos hB)
    (perturbedAncientWeight_pos hB).le le_rfl _
    t

/-- Exponential decoding preserves the divergence-free physical base field. -/
theorem ancientLift_perturbedLinearizedAncient_base_mem_solenoidal (a : ℝ)
    {f : Iic a →ᵇ VectorH 3 0} {v : Iic a →ᵇ VectorH 3 1}
    (hv : v = perturbedFreeAncientOperator hB a (f - perturbedTransportPath T a v))
    (t : ℝ) :
    l2SobolevRow (baseIndex 3 1) (ancientLift (perturbedAncientWeight B) v t)
      ∈ l2Solenoidal 3 := by
  change l2SobolevRow (baseIndex 3 1)
    (Real.exp (perturbedAncientWeight B * t) • v ⟨min t a, min_le_right _ _⟩) ∈ _
  rw [map_smul]
  exact (l2Solenoidal 3).smul_mem _
    (perturbedLinearizedAncient_base_mem_solenoidal T hB a hv _)

end NavierStokes.Selfsimilar
