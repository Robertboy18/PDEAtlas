/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Abstract axisymmetric streamfunction inversion and Biot–Savart bounds

The Green kernel, weighted Sobolev spaces, and boundary conditions vary between axisymmetric
problems, so the inversion is stated for abstract normed spaces. A
`StreamfunctionInverseEstimate` is a bounded two-sided inverse `solve` of a stream operator with
an operator-norm constant, and a `VelocityReconstructionEstimate` is a bounded velocity
reconstruction with its constant. Their composition `biotSavart` is bounded by the product
`biotSavartConstant` (`biotSavart_opNorm_le`), hence Lipschitz with that constant
(`norm_biotSavart_sub_biotSavart_le`).
-/

@[expose] public section

noncomputable section

namespace AxisymmetricFlow

variable {Source Stream Velocity : Type*}
  [NormedAddCommGroup Source] [NormedSpace ℝ Source]
  [NormedAddCommGroup Stream] [NormedSpace ℝ Stream]
  [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]

/-- A two-sided inverse for an axisymmetric stream operator with an explicit norm constant. -/
structure StreamfunctionInverseEstimate
    (Source Stream : Type*)
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Stream] [NormedSpace ℝ Stream] where
  /-- Elliptic stream operator, including the selected boundary conditions in its domain. -/
  streamOperator : Stream →L[ℝ] Source
  /-- Bounded inverse streamfunction solver. -/
  solve : Source →L[ℝ] Stream
  /-- Solving and then applying the elliptic operator recovers the source. -/
  streamOperator_solve : ∀ source, streamOperator (solve source) = source
  /-- Applying the elliptic operator and then solving recovers the streamfunction. -/
  solve_streamOperator : ∀ stream, solve (streamOperator stream) = stream
  /-- Explicit source-to-stream norm constant. -/
  streamConstant : NNReal
  /-- Operator-norm bound for the inverse. -/
  solve_opNorm_le : ‖solve‖ ≤ streamConstant

namespace StreamfunctionInverseEstimate

variable (estimate : StreamfunctionInverseEstimate Source Stream)

/-- Explicit inverse elliptic estimate. -/
theorem norm_solve_le (source : Source) :
    ‖estimate.solve source‖ ≤
      estimate.streamConstant * ‖source‖ :=
  (estimate.solve.le_opNorm source).trans
    (mul_le_mul_of_nonneg_right estimate.solve_opNorm_le (norm_nonneg source))

/-- The selected streamfunction problem has at most one solution in the admitted space. -/
theorem eq_solve_of_streamOperator_eq
    {stream : Stream} {source : Source}
    (equation : estimate.streamOperator stream = source) :
    stream = estimate.solve source := by
  calc
    stream = estimate.solve (estimate.streamOperator stream) :=
      (estimate.solve_streamOperator stream).symm
    _ = estimate.solve source := congrArg estimate.solve equation

/-- The inverse elliptic estimate is Lipschitz with the same explicit constant. -/
theorem norm_solve_sub_solve_le (left right : Source) :
    ‖estimate.solve left - estimate.solve right‖ ≤
      estimate.streamConstant * ‖left - right‖ := by
  rw [← estimate.solve.map_sub]
  exact estimate.norm_solve_le (left - right)

end StreamfunctionInverseEstimate

/-- Bounded velocity reconstruction from an admitted axisymmetric streamfunction space. -/
structure VelocityReconstructionEstimate
    (Stream Velocity : Type*)
    [NormedAddCommGroup Stream] [NormedSpace ℝ Stream]
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity] where
  /-- Linear velocity reconstruction, for example
  `ψ ↦ (-∂z ψ / r, ∂r ψ / r)` in axisymmetric coordinates. -/
  reconstruct : Stream →L[ℝ] Velocity
  /-- Explicit stream-to-velocity norm constant. -/
  velocityConstant : NNReal
  /-- Operator-norm bound for the reconstruction. -/
  reconstruct_opNorm_le : ‖reconstruct‖ ≤ velocityConstant

namespace VelocityReconstructionEstimate

variable (estimate : VelocityReconstructionEstimate Stream Velocity)

/-- Explicit streamfunction-to-velocity estimate. -/
theorem norm_reconstruct_le (stream : Stream) :
    ‖estimate.reconstruct stream‖ ≤
      estimate.velocityConstant * ‖stream‖ :=
  (estimate.reconstruct.le_opNorm stream).trans
    (mul_le_mul_of_nonneg_right estimate.reconstruct_opNorm_le
      (norm_nonneg stream))

end VelocityReconstructionEstimate

/-- The axisymmetric Biot–Savart operator is velocity reconstruction after elliptic inversion. -/
def biotSavart
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity) :
    Source →L[ℝ] Velocity :=
  velocity.reconstruct.comp streamfunction.solve

/-- Explicit composed Biot–Savart constant. -/
def biotSavartConstant
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity) : NNReal :=
  velocity.velocityConstant * streamfunction.streamConstant

/-- Operator-norm bound for the composed axisymmetric Biot–Savart map. -/
theorem biotSavart_opNorm_le
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity) :
    ‖biotSavart streamfunction velocity‖ ≤
      biotSavartConstant streamfunction velocity := by
  calc
    ‖biotSavart streamfunction velocity‖ ≤
        ‖velocity.reconstruct‖ * ‖streamfunction.solve‖ :=
      velocity.reconstruct.opNorm_comp_le streamfunction.solve
    _ ≤
        velocity.velocityConstant * streamfunction.streamConstant :=
      mul_le_mul velocity.reconstruct_opNorm_le
        streamfunction.solve_opNorm_le
        streamfunction.solve.opNorm_nonneg
        velocity.velocityConstant.property
    _ = biotSavartConstant streamfunction velocity := rfl

/-- Explicit source-to-velocity Biot–Savart estimate. -/
theorem norm_biotSavart_le
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity)
    (source : Source) :
    ‖biotSavart streamfunction velocity source‖ ≤
      biotSavartConstant streamfunction velocity * ‖source‖ :=
  ((biotSavart streamfunction velocity).le_opNorm source).trans
    (mul_le_mul_of_nonneg_right
      (biotSavart_opNorm_le streamfunction velocity)
      (norm_nonneg source))

/-- The Biot–Savart map is Lipschitz with the same explicit constant. -/
theorem norm_biotSavart_sub_biotSavart_le
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity)
    (left right : Source) :
    ‖biotSavart streamfunction velocity left -
        biotSavart streamfunction velocity right‖ ≤
      biotSavartConstant streamfunction velocity * ‖left - right‖ := by
  rw [← (biotSavart streamfunction velocity).map_sub]
  exact norm_biotSavart_le streamfunction velocity (left - right)

/-- Velocity reconstructed from a source uses the unique admitted streamfunction solution. -/
theorem biotSavart_eq_reconstruct_of_streamOperator_eq
    (streamfunction : StreamfunctionInverseEstimate Source Stream)
    (velocity : VelocityReconstructionEstimate Stream Velocity)
    {source : Source} {stream : Stream}
    (equation : streamfunction.streamOperator stream = source) :
    biotSavart streamfunction velocity source =
      velocity.reconstruct stream := by
  rw [biotSavart]
  change
    velocity.reconstruct (streamfunction.solve source) =
      velocity.reconstruct stream
  congr 1
  exact
    (streamfunction.eq_solve_of_streamOperator_eq equation).symm

end AxisymmetricFlow
