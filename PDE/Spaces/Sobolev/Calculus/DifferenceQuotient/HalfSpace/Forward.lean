/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalForward
public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator

/-!
# Inward normal difference quotients on a half-space

A nonnegative translation in the normal direction stays in the upper half-space. The
restricted quotient of the zero extension therefore agrees with the quotient of the
reflection extension. The latter is bounded by a whole-space weak derivative.
No zero trace is needed for the function being differenced.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich
open SobolevSpace.Extension.Lp
open scoped ENNReal Topology Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inward normal translations preserve the upper half-space, also in dimension one. -/
theorem mapsTo_add_normalStep_upper {h : ℝ} (hh : 0 ≤ h) :
    MapsTo (fun x : ℝ^n ↦ x + coordinateStep (PDE.Common.lastIndex (n := n)) h)
      (HalfSpace.upper n) (HalfSpace.upper n) := by
  intro x hx
  change 0 < (x + coordinateStep (PDE.Common.lastIndex (n := n)) h)
    (PDE.Common.lastIndex (n := n))
  have hx' : 0 < x (PDE.Common.lastIndex (n := n)) := hx
  simpa [coordinateStep] using add_pos_of_pos_of_nonneg hx' hh

/-- Almost-everywhere statements on the half-space remain valid after an inward
translation. Lebesgue translation preserves null sets and the translated point stays inside. -/
theorem ae_add_normalStep_upper {P : ℝ^n → Prop} {h : ℝ} (hh : 0 ≤ h)
    (hP : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), P x) :
    ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      P (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) := by
  have hglobal : ∀ᵐ x ∂volume, x ∈ HalfSpace.upper n → P x :=
    (ae_restrict_iff' (HalfSpace.measurableSet_upper n)).mp hP
  have htrans := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep (PDE.Common.lastIndex (n := n)) h)).quasiMeasurePreserving.ae hglobal
  filter_upwards [htrans.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (HalfSpace.measurableSet_upper n)] with x hx hxU
  exact hx (mapsTo_add_normalStep_upper hh hxU)

/-- Inside the half-space, the inward quotient of a zero extension has the expected
formula in terms of the original equivalence class. -/
theorem inward_differenceQuotient_apply_ae
    (u : DerivLp n p (HalfSpace.upper n)) {h : ℝ} (hh : 0 ≤ h) :
    (restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) u)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun x ↦ h⁻¹ * (u (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) - u x) := by
  let Z := zeroExtendLp (HalfSpace.measurableSet_upper n) u
  filter_upwards [
    restrictDerivLp_apply_ae (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h Z),
    (differenceQuotientLp_apply_ae p (PDE.Common.lastIndex (n := n)) h Z).filter_mono
      (ae_mono Measure.restrict_le_self),
    zeroExtendLp_agree_ae (HalfSpace.measurableSet_upper n) u,
    ae_add_normalStep_upper hh (zeroExtendLp_agree_ae (HalfSpace.measurableSet_upper n) u)]
    with x hr hd hu ht
  exact hr.trans (hd.trans (by rw [ht, hu]))

/-- A normal inward quotient is bounded by the normal derivative of the canonical
reflection extension. The bound is uniform in the step, with no boundary trace assumption. -/
theorem norm_inward_differenceQuotient_le
    (hp : p ≠ ∞) (U : W^{1,p}(HalfSpace.upper n))
    {h : ℝ} (hh : 0 ≤ h) :
    ‖restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) (wkpBaseCoordinateCLM U)))‖ ≤
      ‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
        ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap U)‖ := by
  let E := SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p
  let W := E.toContinuousLinearMap U
  let Z := zeroExtendLp (HalfSpace.measurableSet_upper n) (wkpBaseCoordinateCLM U)
  have hext : (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)] (wkpBaseCoordinateCLM U : ℝ^n → ℝ) :=
    E.agree_ae U
  have hag : (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)] Z :=
    hext.trans
      (zeroExtendLp_agree_ae (HalfSpace.measurableSet_upper n) (wkpBaseCoordinateCLM U)).symm
  have htrans := restrict_translateLp_congr
    (HalfSpace.measurableSet_upper n) (HalfSpace.measurableSet_upper n)
    (coordinateStep (PDE.Common.lastIndex (n := n)) h)
    (mapsTo_add_normalStep_upper hh) hag
  have hbase : restrictDerivLp (subset_univ (HalfSpace.upper n))
      (wkpBaseCoordinateCLM W) =
        restrictDerivLp (subset_univ (HalfSpace.upper n)) Z := by
    apply Lp.ext
    filter_upwards [
      restrictDerivLp_apply_ae (subset_univ (HalfSpace.upper n)) (wkpBaseCoordinateCLM W),
      restrictDerivLp_apply_ae (subset_univ (HalfSpace.upper n)) Z, hag] with x hx hy hz
    exact hx.trans (hz.trans hy.symm)
  have heq : restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (wkpBaseCoordinateCLM W)) =
        restrictDerivLp (subset_univ (HalfSpace.upper n))
          (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h Z) := by
    simp only [differenceQuotientLp_apply, map_smul, map_sub, htrans, hbase]
  rw [← heq]
  by_cases hh0 : h = 0
  · simp [hh0, differenceQuotientLp_apply]
  exact (norm_restrictDerivLp_le _ _).trans
    (norm_differenceQuotientLp_base_le_deriv_of_ne_top p hp
      (PDE.Common.lastIndex (n := n)) hh0 W)

end SobolevSpace.GraphSpace.DifferenceQuotient
