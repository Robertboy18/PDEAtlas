/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.ComplexParts
public import PDE.Spaces.Sobolev.GraphSpace.Model.Complex

/-!
# The complex weak-derivative and Bessel scales

The real equivalence applies separately to the real and imaginary parts. Recombination
produces the original complex function, with its complex weak derivatives. The
norm estimates use the complex graph norm, not the product norm of the two real graphs.
-/

@[expose] public section

noncomputable section

open MeasureTheory BesselPotentialSpace TemperedDistribution SobolevSpace.GraphSpace
open scoped BesselPotentialSpace SchwartzMap

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-- Convert an arbitrary complex Bessel element into its weak-derivative graph. -/
def toComplexWkSpace (u : H^{(k : ℝ)}(ℝ^n)) :
    ComplexWkSpaceOn n k Set.univ :=
  complexOfRealGraphs (toWkpSpaceCLE n k (reHs u)) (toWkpSpaceCLE n k (imHs u))

/-- The complex graph is bounded in the Bessel norm. -/
theorem norm_toComplexWkSpace_le (u : H^{(k : ℝ)}(ℝ^n)) :
    ‖toComplexWkSpace u‖ ≤ 2 * toWkpSpaceNormBound n k * ‖u‖ := by
  apply (norm_complexOfRealGraphs_le _ _).trans
  have hr := norm_toWkpSpace_le (reHs u).1
    (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) (reHs u))
  have hi := norm_toWkpSpace_le (imHs u).1
    (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) (imHs u))
  calc
    _ ≤ toWkpSpaceNormBound n k * ‖reHs u‖ +
        toWkpSpaceNormBound n k * ‖imHs u‖ := add_le_add hr hi
    _ ≤ toWkpSpaceNormBound n k * ‖u‖ + toWkpSpaceNormBound n k * ‖u‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left (norm_reHs_le u) toWkpSpaceNormBound_nonneg)
        (mul_le_mul_of_nonneg_left (norm_imHs_le u) toWkpSpaceNormBound_nonneg)
    _ = _ := by ring

/-- The base coordinate is the physical representative of the input, almost everywhere. -/
theorem coeFn_toComplexWkSpace_base (u : H^{(k : ℝ)}(ℝ^n)) :
    (toComplexWkSpace u).1 (baseIndex n k) =ᵐ[volume]
      (toL2Fun (Nat.cast_nonneg k) u : ℝ^n → ℂ) := by
  have hc := coeFn_complexLp
    ((toWkpSpaceCLE n k (reHs u)).1 (baseIndex n k))
    ((toWkpSpaceCLE n k (imHs u)).1 (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at hc
  have hr := coeFn_toDerivLp (toL2Fun (Nat.cast_nonneg k) (reHs u).1)
  have hi := coeFn_toDerivLp (toL2Fun (Nat.cast_nonneg k) (imHs u).1)
  simp only [domainMeasure, Measure.restrict_univ] at hr hi
  have hp := toL2Fun_reHs_imHs (Nat.cast_nonneg k) u
  filter_upwards [hc, hr, hi, hp.1, hp.2] with x hx hrx hix hpr hpi
  change _ = _ at hx
  change complexLp _ _ x = _
  rw [hx]
  have hb (v : HsSpaceReal n (k : ℝ)) :
      (toWkpSpaceCLE n k v).1 (baseIndex n k) =
        toDerivLp (toL2Fun (Nat.cast_nonneg k) v.1) :=
    graphTuple_baseIndex (Nat.cast_nonneg k) v.1
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) v)
  rw [hb, hb]
  change
    (toDerivLp (toL2Fun (Nat.cast_nonneg k) (reHs u).1) x : ℂ) +
      Complex.I * (toDerivLp (toL2Fun (Nat.cast_nonneg k) (imHs u).1) x : ℂ) = _
  rw [hrx, hix]
  change
    ((toL2Fun (Nat.cast_nonneg k) (reHs u).1 x).re : ℂ) +
      Complex.I * ((toL2Fun (Nat.cast_nonneg k) (imHs u).1 x).re : ℂ) = _
  rw [hpr, hpi, mul_comm]
  exact Complex.re_add_im _

/-- Recover a complex Bessel element from its real and imaginary weak-derivative graphs. -/
def ofComplexWkSpace (U : ComplexWkSpaceOn n k Set.univ) : H^{(k : ℝ)}(ℝ^n) :=
  ofWkpSpace U.re + Complex.I • ofWkpSpace U.im

/-- The reverse norm constant from the real theorem. -/
def ofComplexWkSpaceNormBound (n k : ℕ) : ℝ :=
  2 * ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1))

theorem ofComplexWkSpaceNormBound_nonneg (n k : ℕ) :
    0 ≤ ofComplexWkSpaceNormBound n k := by
  unfold ofComplexWkSpaceNormBound
  positivity

/-- The Bessel norm is bounded by the complex weak-derivative graph norm. -/
theorem norm_ofComplexWkSpace_le (U : ComplexWkSpaceOn n k Set.univ) :
    ‖ofComplexWkSpace U‖ ≤ ofComplexWkSpaceNormBound n k * ‖U‖ := by
  calc
    _ ≤ ‖ofWkpSpace U.re‖ + ‖Complex.I • ofWkpSpace U.im‖ := norm_add_le _ _
    _ = ‖ofWkpSpace U.re‖ + ‖ofWkpSpace U.im‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := by
      have hr := (norm_ofWkpSpace_le U.re).trans
        (mul_le_mul_of_nonneg_left U.norm_re_le (by positivity))
      have hi := (norm_ofWkpSpace_le U.im).trans
        (mul_le_mul_of_nonneg_left U.norm_im_le (by positivity))
      unfold ofComplexWkSpaceNormBound
      nlinarith

/-- Recombination recovers the base function of the complex graph. -/
theorem coeFn_toL2Fun_ofComplexWkSpace (U : ComplexWkSpaceOn n k Set.univ) :
    (toL2Fun (Nat.cast_nonneg k) (ofComplexWkSpace U) : ℝ^n → ℂ) =ᵐ[volume]
      U.1 (baseIndex n k) := by
  rw [ofComplexWkSpace, toL2Fun_add, toL2Fun_smul]
  have hr := reOfL2_toL2Fun_ofWkpSpace U.re
  have hi := reOfL2_toL2Fun_ofWkpSpace U.im
  have hpr := Complex.reCLM.coeFn_compLpL (U.1 (baseIndex n k))
  have hpi := Complex.imCLM.coeFn_compLpL (U.1 (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at hpr hpi
  filter_upwards
    [Lp.coeFn_add (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U.re))
      (Complex.I • toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U.im)),
      Lp.coeFn_smul Complex.I (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U.im)),
      hr, hi, hpr, hpi, isRealL2_toL2Fun_ofWkpSpace U.re,
      isRealL2_toL2Fun_ofWkpSpace U.im] with x ha hs hrx hix hprx hpix hrr hir
  rw [ha, Pi.add_apply, hs, Pi.smul_apply]
  apply Complex.ext
  · simpa [reOfL2, coordFun, ComplexWkSpaceOn.re, realCoordinateTuple,
      hprx, hir] using hrx
  · simpa [reOfL2, coordFun, ComplexWkSpaceOn.im, realCoordinateTuple,
      hpix, hrr] using hix

/-- The weak-derivative graph is unchanged by the round trip through the Bessel scale. -/
@[simp] theorem toComplexWkSpace_ofComplexWkSpace (U : ComplexWkSpaceOn n k Set.univ) :
    toComplexWkSpace (ofComplexWkSpace U) = U := by
  apply ComplexWkSpaceOn.ext_base_ae isOpen_univ
  simpa only [domainMeasure, Measure.restrict_univ] using
    (coeFn_toComplexWkSpace_base (ofComplexWkSpace U)).trans
      (coeFn_toL2Fun_ofComplexWkSpace U)

/-- The Bessel element is unchanged by the round trip through complex weak derivatives. -/
@[simp] theorem ofComplexWkSpace_toComplexWkSpace (u : H^{(k : ℝ)}(ℝ^n)) :
    ofComplexWkSpace (toComplexWkSpace u) = u := by
  apply toL2Fun_injective (Nat.cast_nonneg k)
  exact Lp.ext ((coeFn_toL2Fun_ofComplexWkSpace (toComplexWkSpace u)).trans
    (coeFn_toComplexWkSpace_base u))

/-- Uniqueness of weak derivatives makes the complex graph construction additive. -/
theorem toComplexWkSpace_add (u v : H^{(k : ℝ)}(ℝ^n)) :
    toComplexWkSpace (u + v) = toComplexWkSpace u + toComplexWkSpace v := by
  apply ComplexWkSpaceOn.ext_base_ae isOpen_univ
  simp only [domainMeasure, Measure.restrict_univ]
  have hsum := Lp.coeFn_add ((toComplexWkSpace u).1 (baseIndex n k))
    ((toComplexWkSpace v).1 (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at hsum
  have huv := coeFn_toComplexWkSpace_base (u + v)
  rw [toL2Fun_add] at huv
  filter_upwards [huv, coeFn_toComplexWkSpace_base u, coeFn_toComplexWkSpace_base v,
    hsum, Lp.coeFn_add (toL2Fun (Nat.cast_nonneg k) u) (toL2Fun (Nat.cast_nonneg k) v)]
    with x huvx hux hvx hs hl
  change (toComplexWkSpace (u + v)).1 (baseIndex n k) x =
    (((toComplexWkSpace u).1 (baseIndex n k) +
      (toComplexWkSpace v).1 (baseIndex n k)) : Lp ℂ 2 _) x
  simp only [huvx, hs, hl, Pi.add_apply, hux, hvx]

/-- The complex graph construction respects real scalars. -/
theorem toComplexWkSpace_smul (c : ℝ) (u : H^{(k : ℝ)}(ℝ^n)) :
    toComplexWkSpace (c • u) = c • toComplexWkSpace u := by
  apply ComplexWkSpaceOn.ext_base_ae isOpen_univ
  simp only [domainMeasure, Measure.restrict_univ]
  have hsmul := Lp.coeFn_smul c ((toComplexWkSpace u).1 (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at hsmul
  have hcu := coeFn_toComplexWkSpace_base (c • u)
  have hmap : toL2Fun (Nat.cast_nonneg k) (c • u) =
      c • toL2Fun (Nat.cast_nonneg k) u :=
    ((toL2FunCLM n (Nat.cast_nonneg k)).restrictScalars ℝ).map_smul c u
  rw [hmap] at hcu
  filter_upwards [hcu, coeFn_toComplexWkSpace_base u, hsmul,
    Lp.coeFn_smul c (toL2Fun (Nat.cast_nonneg k) u)] with x hc hu hs hl
  change (toComplexWkSpace (c • u)).1 (baseIndex n k) x =
    ((c • (toComplexWkSpace u).1 (baseIndex n k)) : Lp ℂ 2 _) x
  simp only [hc, hs, hl, Pi.smul_apply, hu]

/-- The complex Bessel and weak-derivative spaces are real-linearly equivalent. -/
def toComplexWkSpaceEquiv (n k : ℕ) :
    H^{(k : ℝ)}(ℝ^n) ≃ₗ[ℝ] ComplexWkSpaceOn n k Set.univ where
  toFun := toComplexWkSpace
  invFun := ofComplexWkSpace
  left_inv := ofComplexWkSpace_toComplexWkSpace
  right_inv := toComplexWkSpace_ofComplexWkSpace
  map_add' := toComplexWkSpace_add
  map_smul' := toComplexWkSpace_smul

/-- The complex Bessel and weak-derivative norms give the same real Banach topology. -/
def toComplexWkSpaceCLE (n k : ℕ) :
    H^{(k : ℝ)}(ℝ^n) ≃L[ℝ] ComplexWkSpaceOn n k Set.univ where
  __ := toComplexWkSpaceEquiv n k
  continuous_toFun :=
    ((toComplexWkSpaceEquiv n k).toLinearMap.mkContinuous
      (2 * toWkpSpaceNormBound n k) norm_toComplexWkSpace_le).continuous
  continuous_invFun :=
    ((toComplexWkSpaceEquiv n k).symm.toLinearMap.mkContinuous
      (ofComplexWkSpaceNormBound n k) norm_ofComplexWkSpace_le).continuous

/-- Weak complex Sobolev membership and Mathlib's Bessel distribution membership coincide. -/
theorem exists_complexWkSpace_iff_memSobolev (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ U : ComplexWkSpaceOn n k Set.univ, U.1 (baseIndex n k) =ᵐ[volume] u) ↔
      MemSobolev (k : ℝ) 2 (u : 𝓢'(ℝ^n, ℂ)) := by
  constructor
  · rintro ⟨U, hU⟩
    have heq : toL2Fun (Nat.cast_nonneg k) (ofComplexWkSpace U) = u :=
      Lp.ext ((coeFn_toL2Fun_ofComplexWkSpace U).trans hU)
    have h := (ofComplexWkSpace U).memSobolev_toDistr
    rwa [toDistr_eq_toL2Fun (Nat.cast_nonneg k), heq] at h
  · intro hu
    let v : H^{(k : ℝ)}(ℝ^n) := hu.toBesselPotentialSpace
    have heq : toL2Fun (Nat.cast_nonneg k) v = u := by
      apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
      change Lp.toTemperedDistributionCLM ℂ volume 2 (toL2Fun (Nat.cast_nonneg k) v) =
        Lp.toTemperedDistributionCLM ℂ volume 2 u
      rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply]
      simpa only [v, MemSobolev.toBesselPotentialSpace_toDistr] using
        (toDistr_eq_toL2Fun (Nat.cast_nonneg k) v).symm
    exact ⟨toComplexWkSpace v, by rw [← heq]; exact coeFn_toComplexWkSpace_base v⟩

end SobolevSpace.Fractional
