/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.ChartTrace
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.RightInverse
public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Lifting fractional data through a boundary chart

The finite-exponent half-space lifting is reflected to the whole space and
transported through a prepared C¹ chart. Its physical boundary value is the chart
pullback of the datum, multiplied only by the auxiliary target cutoff.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

private theorem restrict_reflectionExtension
    (u : W^{1,ENNReal.ofReal p}(ℝ^(m + 1)₊)) :
    GraphSpace.restrictCLM (k := 1) (p := ENNReal.ofReal p)
      (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
        (Extension.GraphSpace.HalfSpace.extendCLM (n := m + 1) (p := ENNReal.ofReal p) u)
      = u := by
  apply GraphSpace.WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := m + 1))
  exact (GraphSpace.restrictCLM_apply_ae (HalfSpace.measurableSet_upper (n := m + 1))
    (subset_univ _) _ (GraphSpace.baseIndex (m + 1) 1)).trans
      ((Extension.GraphSpace.HalfSpace.operator
        (n := m + 1) (p := ENNReal.ofReal p)).agree_ae u)

/-- Bounded lifting of Euclidean fractional data through one prepared boundary chart. -/
def localLifting (hp : 1 < p) (i : Fin hΩ.N) :
    GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p) →L[ℝ]
      W^{1,ENNReal.ofReal p}(Ω) :=
  (chartTransport (ENNReal.ofReal p) i).comp
    ((Extension.GraphSpace.HalfSpace.extendCLM
      (n := m + 1) (p := ENNReal.ofReal p)).comp
        (HalfSpace.mollifiedLifting (Approximation.standardMollifier m) hp))

/-- The physical boundary law for the local lifting, for any chosen Lᵖ representative. -/
theorem traceLp_localLifting (hp : 1 < p) (i : Fin hΩ.N)
    (v : GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p))
    (g : Lp ℝ (ENNReal.ofReal p) (volume : Measure ℝ^m))
    (hg : (GagliardoSpace.toLp m (1 - 1 / p) univ v : ℝ^m → ℝ) =ᵐ[volume] g) :
    traceLp p (localLifting p hp i v) = chartPhysicalization (ENNReal.ofReal p) i
      (flatTargetCutoff (ENNReal.ofReal p) i (liftLp (ENNReal.ofReal p) g)) := by
  change traceLp p (chartTransport (ENNReal.ofReal p) i
    (Extension.GraphSpace.HalfSpace.extendCLM
      (n := m + 1) (p := ENNReal.ofReal p)
        (HalfSpace.mollifiedLifting (Approximation.standardMollifier m) hp v))) = _
  rw [traceLp_chartTransport, restrict_reflectionExtension]
  have hflat : HalfSpace.traceLp m p hp.le
      (HalfSpace.mollifiedLifting (Approximation.standardMollifier m) hp v) = g := by
    apply Lp.ext
    exact (HalfSpace.traceLp_mollifiedLifting_ae (Approximation.standardMollifier m) hp v).trans hg
  change chartPhysicalization (ENNReal.ofReal p) i
    (flatTargetCutoff (ENNReal.ofReal p) i (liftLp (ENNReal.ofReal p)
      (HalfSpace.traceLp m p hp.le
        (HalfSpace.mollifiedLifting (Approximation.standardMollifier m) hp v)))) = _
  rw [hflat]

/-- A lifting of a partitioned coordinate recovers exactly that partition of the surface datum. -/
theorem traceLp_localLifting_localizedBoundaryCoordinates (hp : 1 < p) (i : Fin hΩ.N)
    (g : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω))
    (v : GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p))
    (hv : (GagliardoSpace.toLp m (1 - 1 / p) univ v : ℝ^m → ℝ)
      =ᵐ[volume] localizedBoundaryCoordinates (ENNReal.ofReal p) i g) :
    traceLp p (localLifting p hp i v) = boundaryCutoff (ENNReal.ofReal p) i g := by
  rw [traceLp_localLifting p hp i v _ hv,
    flatTargetCutoff_lift_localizedBoundaryCoordinates,
    chartPhysicalization_lift_localizedBoundaryCoordinates]

/-- The chart, reflection and flat lifting norms give a bound in the Sobolev graph norm. -/
theorem norm_localLifting_le (hp : 1 < p) (i : Fin hΩ.N)
    (v : GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    ‖localLifting p hp i v‖ ≤
      (‖chartTransport (ENNReal.ofReal p) i‖ *
        ‖Extension.GraphSpace.HalfSpace.extendCLM
          (n := m + 1) (p := ENNReal.ofReal p)‖ *
        ‖HalfSpace.mollifiedLifting (Approximation.standardMollifier m) hp‖) * ‖v‖ := by
  calc
    ‖localLifting p hp i v‖ ≤ ‖localLifting p hp i‖ * ‖v‖ :=
      (localLifting p hp i).le_opNorm v
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      exact ((chartTransport (ENNReal.ofReal p) i).opNorm_comp_le _).trans
        ((mul_le_mul_of_nonneg_left
          ((Extension.GraphSpace.HalfSpace.extendCLM
            (n := m + 1) (p := ENNReal.ofReal p)).opNorm_comp_le _)
          (norm_nonneg (chartTransport (ENNReal.ofReal p) i))).trans_eq
            (mul_assoc _ _ _).symm)

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
