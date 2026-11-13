/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Fourier
public import PDE.Spaces.Sobolev.Fractional.Integer.Complexification

/-!
# Heat smoothing on the actual integer Sobolev graph spaces

The one-order Bessel heat multiplier restricts to real functions and transfers
through the established equivalence with the weak-derivative graph model.
The bound retains the low-frequency term and the explicit norm comparison constants.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open BesselPotentialSpace
open scoped ENNReal NNReal BesselPotentialSpace Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The gaining Fourier heat multiplier restricted to the real Bessel spaces. -/
def heatGainReal (n : ℕ) (s t : ℝ) (ht : 0 < t) :
    HsSpaceReal n s →L[ℝ] HsSpaceReal n (s + 1) :=
  (((heatGainBessel n s t ht).restrictScalars ℝ).comp
    (hsRealSubmodule n s).subtypeL).codRestrict (hsRealSubmodule n (s + 1))
      (fun u ↦ heatGainBessel_mem_real s ht u.val u.property)

/-- Restriction to real functions preserves the Bessel smoothing bound. -/
theorem norm_heatGainReal_le (s : ℝ) {t : ℝ} (ht : 0 < t) (u : HsSpaceReal n s) :
    ‖heatGainReal n s t ht u‖ ≤ gainBound t * ‖u‖ :=
  norm_heatGainBessel_le s ht u.val

/-- The same operator, with its target written as the next integer order. -/
def heatGainRealToOrder (n : ℕ) (s q t : ℝ) (hq : q = s + 1) (ht : 0 < t) :
    HsSpaceReal n s →L[ℝ] HsSpaceReal n q := by
  subst q
  exact heatGainReal n s t ht

/-- Changing the notation for the target order preserves the analytic bound. -/
theorem norm_heatGainRealToOrder_le (s q : ℝ) (hq : q = s + 1)
    {t : ℝ} (ht : 0 < t) (u : HsSpaceReal n s) :
    ‖heatGainRealToOrder n s q t hq ht u‖ ≤ gainBound t * ‖u‖ := by
  subst q
  exact norm_heatGainReal_le s ht u

/-- Rewriting the target order preserves the physical Fourier heat evolution. -/
theorem toL2Fun_heatGainRealToOrder (s q : ℝ) (hq : q = s + 1) (hs : 0 ≤ s)
    (hq₀ : 0 ≤ q) (t : ℝ≥0) (ht : 0 < (t : ℝ)) (u : HsSpaceReal n s) :
    toL2Fun hq₀ (heatGainRealToOrder n s q (t : ℝ) hq ht u).val =
      heatL2 n t (toL2Fun hs u.val) := by
  subst q
  exact toL2Fun_heatGainBessel hs t ht u.val

/-- The gaining operator between adjacent integer Bessel orders. -/
def heatGainIntegerBessel (n k : ℕ) (t : ℝ) (ht : 0 < t) :
    HsSpaceReal n (k : ℝ) →L[ℝ] HsSpaceReal n ((k + 1 : ℕ) : ℝ) :=
  heatGainRealToOrder n (k : ℝ) ((k + 1 : ℕ) : ℝ) t (by push_cast; rfl) ht

/-- The integer-order version has the same Bessel norm bound. -/
theorem norm_heatGainIntegerBessel_le {t : ℝ} (ht : 0 < t)
    (u : HsSpaceReal n (k : ℝ)) :
    ‖heatGainIntegerBessel n k t ht u‖ ≤ gainBound t * ‖u‖ := by
  exact norm_heatGainRealToOrder_le (k : ℝ) ((k + 1 : ℕ) : ℝ) _ ht u

/-- The actual whole-space graph Sobolev heat operator gains one weak derivative. -/
def heatGainSobolev (n k : ℕ) (t : ℝ) (ht : 0 < t) :
    W^{k,2}(ℝ^n) →L[ℝ] W^{k + 1,2}(ℝ^n) :=
  (toWkpSpaceCLM n (k + 1)).comp
    ((heatGainIntegerBessel n k t ht).comp (ofWkpSpaceRealCLM n k))

/-- The explicit comparison constant for graph Sobolev heat smoothing. -/
def graphGainConstant (n k : ℕ) : ℝ :=
  toWkpSpaceNormBound n (k + 1) *
    ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1))

theorem graphGainConstant_nonneg (n k : ℕ) : 0 ≤ graphGainConstant n k := by
  unfold graphGainConstant
  exact mul_nonneg toWkpSpaceNormBound_nonneg (by positivity)

/-- One-order smoothing on the literal weak-derivative graph norm. -/
theorem norm_heatGainSobolev_le {t : ℝ} (ht : 0 < t) (u : W^{k,2}(ℝ^n)) :
    ‖heatGainSobolev n k t ht u‖ ≤ graphGainConstant n k * gainBound t * ‖u‖ := by
  have hf := norm_toWkpSpace_le
    (heatGainIntegerBessel n k t ht (ofWkpSpaceRealCLM n k u)).val
    (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg (k + 1))
      (heatGainIntegerBessel n k t ht (ofWkpSpaceRealCLM n k u)))
  have hg := norm_heatGainIntegerBessel_le ht (ofWkpSpaceRealCLM n k u)
  have hr := norm_ofWkpSpace_le u
  change ‖toWkpSpaceCLM n (k + 1)
    (heatGainIntegerBessel n k t ht (ofWkpSpaceRealCLM n k u))‖ ≤ _
  calc
    _ ≤ toWkpSpaceNormBound n (k + 1) *
        ‖heatGainIntegerBessel n k t ht (ofWkpSpaceRealCLM n k u)‖ := hf
    _ ≤ toWkpSpaceNormBound n (k + 1) *
        (gainBound t * ‖ofWkpSpaceRealCLM n k u‖) :=
      mul_le_mul_of_nonneg_left hg toWkpSpaceNormBound_nonneg
    _ ≤ toWkpSpaceNormBound n (k + 1) *
        (gainBound t *
          (((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1)) * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hr (gainBound_nonneg t)) toWkpSpaceNormBound_nonneg
    _ = _ := by unfold graphGainConstant; ring

/-- The Sobolev gaining operator has the literal physical heat base function. -/
theorem baseL2_heatGainSobolev (t : ℝ≥0) (ht : 0 < (t : ℝ)) (u : W^{k,2}(ℝ^n)) :
    baseL2 (heatGainSobolev n k (t : ℝ) ht u) = heatL2 n t (baseL2 u) := by
  have hbase (v : HsSpaceReal n ((k + 1 : ℕ) : ℝ)) :
      baseL2 (toWkpSpaceCLM n (k + 1) v) = toL2Fun (Nat.cast_nonneg (k + 1)) v.val := by
    have h := toL2Fun_ofWkpSpace (toWkpSpaceCLM n (k + 1) v)
    simp only [toWkpSpaceCLM_apply, ofWkpSpace_toWkpSpace] at h
    exact h.symm
  simp only [heatGainSobolev, ContinuousLinearMap.comp_apply, hbase]
  rw [heatGainIntegerBessel, toL2Fun_heatGainRealToOrder _ _ _ (Nat.cast_nonneg k)]
  exact congrArg (heatL2 n t) (toL2Fun_ofWkpSpace u)

end HeatEquation.WholeSpace
