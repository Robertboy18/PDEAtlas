/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation
public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientWeighted

/-!
# Physical initial traces of weighted ancient perturbations

The physical transformation at time `exp τ` is
`V ↦ exp (-τ / 2) • V (exp (-τ / 2) • ·)`. Its actual spatial L² norm
scales by `exp ((n - 2) * τ / 4)`, including the Euclidean volume factor.
A weighted ancient perturbation therefore has zero strong initial trace when
`η + (n - 2) / 4 > 0`. In dimension three, every positive weight suffices.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped Topology Sobolev BoundedContinuousFunction

namespace NavierStokes.Selfsimilar

variable {n : ℕ}

/-- The actual physical rescaling at physical time `exp τ`, on spatial L² classes. -/
def physicalL2Rescaling (n : ℕ) (τ : ℝ) : WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  Real.exp (-τ / 2) • l2Dilation (Real.exp (-τ / 2)) (Real.exp_ne_zero _)

/-- The rescaled equivalence class has the intended physical representative. -/
theorem physicalL2Rescaling_ae (τ : ℝ) (V : WholeSpaceL2 n) :
    physicalL2Rescaling n τ V =ᵐ[domainMeasure n univ]
      fun x ↦ Real.exp (-τ / 2) • V (Real.exp (-τ / 2) • x) := by
  filter_upwards [Lp.coeFn_smul (Real.exp (-τ / 2))
    (l2Dilation (Real.exp (-τ / 2)) (Real.exp_ne_zero _) V),
    l2Dilation_ae (Real.exp (-τ / 2)) (Real.exp_ne_zero _) V] with x hs hd
  exact hs.trans (congrArg (fun v : ℝ^n ↦ Real.exp (-τ / 2) • v) hd)

/-- The physical L² norm retains the full Euclidean spatial Jacobian. -/
theorem norm_physicalL2Rescaling (τ : ℝ) (V : WholeSpaceL2 n) :
    ‖physicalL2Rescaling n τ V‖ =
      Real.exp (((n : ℝ) - 2) * τ / 4) * ‖V‖ := by
  change ‖Real.exp (-τ / 2) • l2Dilation (Real.exp (-τ / 2))
    (Real.exp_ne_zero _) V‖ = _
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _), norm_l2Dilation,
    ← mul_assoc]
  congr 1
  have hexp (x : ℝ) : |Real.exp x| = Real.exp x := abs_of_pos (Real.exp_pos _)
  simp only [← Real.exp_nat_mul, ← Real.exp_neg, hexp]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  norm_num
  rw [← Real.exp_add]
  congr 1
  ring

/-- Physical rescaling preserves distributional divergence freedom. -/
theorem physicalL2Rescaling_mem_solenoidal (τ : ℝ) {V : WholeSpaceL2 n}
    (hV : V ∈ l2Solenoidal n) :
    physicalL2Rescaling n τ V ∈ l2Solenoidal n :=
  (l2Solenoidal n).smul_mem _ (l2Dilation_mem_solenoidal _ _ hV)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A decoded ancient perturbation, embedded into physical L² and rescaled in space. -/
def weightedPhysicalL2 (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ) {a : ℝ}
    (u : Iic a →ᵇ E) (τ : ℝ) : WholeSpaceL2 n :=
  physicalL2Rescaling n τ (T (ancientLift η u τ))

/-- The decay exponent combines the ancient weight and the physical spatial volume. -/
theorem norm_weightedPhysicalL2_le (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ) {a : ℝ}
    (u : Iic a →ᵇ E) (τ : ℝ) :
    ‖weightedPhysicalL2 T η u τ‖ ≤
      ‖T‖ * ‖u‖ * Real.exp ((η + ((n : ℝ) - 2) / 4) * τ) := by
  rw [weightedPhysicalL2, norm_physicalL2Rescaling]
  calc
    _ ≤ Real.exp (((n : ℝ) - 2) * τ / 4) *
        (‖T‖ * (‖u‖ * Real.exp (η * τ))) := by
      gcongr
      exact (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_ancientLift_le η u τ) (norm_nonneg T))
    _ = _ := by
      rw [show (η + ((n : ℝ) - 2) / 4) * τ =
        ((n : ℝ) - 2) * τ / 4 + η * τ by ring, Real.exp_add]
      ring

/-- A positive total exponent gives strong L² decay in ancient time. -/
theorem tendsto_weightedPhysicalL2_atBot (T : E →L[ℝ] WholeSpaceL2 n) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    Tendsto (weightedPhysicalL2 T η u) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun τ ↦ norm_nonneg _)
    (norm_weightedPhysicalL2_le T η u)
  simpa only [Function.comp_apply, id_eq, mul_zero] using
    (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hη)).const_mul (‖T‖ * ‖u‖)

/-- The physical-time perturbation has strong zero initial trace in spatial L². -/
theorem tendsto_weightedPhysicalL2_log_zero (T : E →L[ℝ] WholeSpaceL2 n) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    Tendsto (fun t ↦ weightedPhysicalL2 T η u (Real.log t)) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_weightedPhysicalL2_atBot T hη u).comp Real.tendsto_log_nhdsGT_zero

/-- Solenoidal decoded perturbations remain solenoidal in physical coordinates. -/
theorem weightedPhysicalL2_mem_solenoidal (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ) {a : ℝ}
    (u : Iic a →ᵇ E) (hu : ∀ τ, T (ancientLift η u τ) ∈ l2Solenoidal n) (τ : ℝ) :
    weightedPhysicalL2 T η u τ ∈ l2Solenoidal n :=
  physicalL2Rescaling_mem_solenoidal τ (hu τ)

/-- Every positive-weight three-dimensional Sobolev perturbation has zero physical trace. -/
theorem tendsto_sobolevPhysicalL2_log_zero {k : ℕ} {η a : ℝ}
    (hη : 0 < η) (u : Iic a →ᵇ VectorH 3 k) :
    Tendsto (fun t ↦ weightedPhysicalL2 (l2SobolevRow (baseIndex 3 k))
      η u (Real.log t)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_weightedPhysicalL2_log_zero
  norm_num
  linarith

end NavierStokes.Selfsimilar
