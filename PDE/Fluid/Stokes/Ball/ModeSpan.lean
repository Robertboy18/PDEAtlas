/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.SphericalForm

/-!
# The modes of an eigenvalue as elements of `L²` of the ball

The modes are continuous on `ℝ³`, hence bounded on the ball `B(0, R)` and square integrable
there. `ballModes R μ odd` is the set of the `L²(B)` classes of the modes of eigenvalue `μ` in
the sector `odd`: the modes `mode R k l α` of admissible degree and of the parity of the
sector with `boundaryFunction k l α = 0` and `(α / R)² = μ`, together with `e_z` when `μ = 0`
in the odd sector. `sectorSign odd` is the parity `1` of the even sector and `-1` of the odd
sector under the equatorial reflection. The boundary functions of admissible degree have no
root at `α = 0` except the meridional one of degree one (`boundaryFunction_zero_ne`), whose
mode is `(4/5) e_z`, so `ballModes` has the same span as the modes with `0 < α` and `e_z`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Fluid.Stokes.Ball

/-- The parity of a sector under the equatorial reflection: `1` for the even sector and `-1`
for the odd one. -/
def sectorSign (odd : Bool) : ℝ :=
  if odd then -1 else 1

/-- The parity of a sector is a sign. -/
theorem sectorSign_sq (odd : Bool) : sectorSign odd ^ 2 = 1 := by
  cases odd <;> simp [sectorSign]

/-- Continuous functions on `ℝ³` are square integrable on every ball about the origin. -/
theorem memLp_ball_of_continuous {R : ℝ} {E : Type*} [NormedAddCommGroup E] {f : ℝ^3 → E}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^3) R).exists_bound_of_continuousOn
    hf.continuousOn
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
    ⟨by simpa using measure_ball_lt_top⟩
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

/-- The modes are square integrable on the ball. -/
theorem memLp_mode (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    MemLp (mode R k l α) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  memLp_ball_of_continuous (mode_contDiff R k l α).continuous

/-- The zero mode is square integrable on the ball. -/
theorem memLp_zeroMode (R : ℝ) :
    MemLp zeroMode 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  memLp_ball_of_continuous zeroMode_contDiff.continuous

/-- The `L²(B(0, R))` classes of the modes of eigenvalue `μ` in the sector `odd`: the modes of
admissible degree and of parity `sectorSign odd` whose root `α` satisfies `(α / R)² = μ`, and
`e_z` for `μ = 0` in the odd sector. -/
def ballModes (R μ : ℝ) (odd : Bool) :
    Set (Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R))) :=
  {f | ∃ k l α, boundaryFunction k l α = 0 ∧ (α / R) ^ 2 = μ ∧ Admissible k l ∧
      modeParity k l = sectorSign odd ∧ f = (memLp_mode R k l α).toLp (mode R k l α)} ∪
    (if μ = 0 ∧ odd = true then {(memLp_zeroMode R).toLp zeroMode} else ∅)

/-- A mode of eigenvalue `μ` and of the parity of the sector belongs to `ballModes R μ odd`. -/
theorem toLp_mode_mem_ballModes {R μ : ℝ} {odd : Bool} {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) (hμ : (α / R) ^ 2 = μ) (hl : Admissible k l)
    (hpar : modeParity k l = sectorSign odd) :
    (memLp_mode R k l α).toLp (mode R k l α) ∈ ballModes R μ odd :=
  Or.inl ⟨k, l, α, hα, hμ, hl, hpar, rfl⟩

end PDE.Fluid.Stokes.Ball
