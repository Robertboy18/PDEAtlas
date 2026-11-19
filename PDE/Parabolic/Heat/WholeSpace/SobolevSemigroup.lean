/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Sobolev
public import PDE.Parabolic.Heat.WholeSpace.Semigroup
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Strongly continuous heat evolution on integer Sobolev spaces

Conjugating the physical heat multiplier by the Bessel representative isometry
defines heat evolution on every order. The integer equivalence transports this
to the actual weak-derivative graph spaces. Its physical base identity verifies
that the transferred operators describe the same heat solution.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Fractional BesselPotentialSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal BesselPotentialSpace Sobolev Topology

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Heat evolution on the Bessel scale, using the actual Gaussian multiplier. -/
def heatBessel (n : ℕ) (s : ℝ) (t : ℝ≥0) : H^{s}(ℝ^n) →L[ℂ] H^{s}(ℝ^n) :=
  ((toLpₗᵢ (ℝ^n) ℂ s 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((heatL2 n t).comp (toLpₗᵢ (ℝ^n) ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem toLp_heatBessel (s : ℝ) (t : ℝ≥0) (u : H^{s}(ℝ^n)) :
    toLp (heatBessel n s t u) = heatL2 n t (toLp u) := by
  simp only [heatBessel, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  simpa only [toLpₗᵢ_apply] using (toLpₗᵢ (ℝ^n) ℂ s 2).apply_symm_apply
    (heatL2 n t (toLp u))

theorem heatBessel_mem_real (s : ℝ) (t : ℝ≥0) (u : HsSpaceReal n s) :
    heatBessel n s t u.val ∈ hsRealSubmodule n s := by
  rw [mem_HsRealSubmodule_iff, toLp_heatBessel]
  exact heatL2_isReal t u.val.toLp (mem_HsRealSubmodule_iff.1 u.property)

/-- Heat evolution on the real Bessel subspace. -/
def heatBesselReal (n : ℕ) (s : ℝ) (t : ℝ≥0) : HsSpaceReal n s →L[ℝ] HsSpaceReal n s :=
  (((heatBessel n s t).restrictScalars ℝ).comp (hsRealSubmodule n s).subtypeL).codRestrict
    (hsRealSubmodule n s) (heatBessel_mem_real s t)

/-- The order-preserving Bessel operator is the same physical heat solution. -/
theorem toL2Fun_heatBessel {s : ℝ} (hs : 0 ≤ s) (t : ℝ≥0) (u : H^{s}(ℝ^n)) :
    toL2Fun hs (heatBessel n s t u) = heatL2 n t (toL2Fun hs u) := by
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toL2Fun hs (heatBessel n s t u)) = 𝓕 (heatL2 n t (toL2Fun hs u))
  rw [fourier_heatL2]
  apply Lp.ext
  have hrep := Lp.ext_iff.mp (congrArg
    (fun f : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦ 𝓕 f) (toLp_heatBessel s t u))
  rw [fourier_heatL2] at hrep
  have hAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  filter_upwards [coeFn_fourier_toLp hs (heatBessel n s t u), coeFn_fourier_toLp hs u,
    hrep, Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) (𝓕 (toLp u)),
    Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) (𝓕 (toL2Fun hs u)), hAE]
    with ξ hv hu hrep hmul hmul₀ hAE
  apply mul_left_cancel₀ (besselSymbol_ne_zero s ξ)
  rw [hmul₀, Pi.smul_apply', smul_eq_mul, hAE]
  calc
    _ = (𝓕 (toLp (heatBessel n s t u)) : Lp ℂ 2 volume) ξ := hv.symm
    _ = heatSymbol n t ξ * (besselSymbol n s ξ *
        (𝓕 (toL2Fun hs u) : Lp ℂ 2 volume) ξ) := by
      rw [hrep, hmul, Pi.smul_apply', smul_eq_mul, hAE, hu]
    _ = _ := by ring

theorem continuous_heatBesselReal (s : ℝ) (u : HsSpaceReal n s) :
    Continuous (fun t : ℝ≥0 ↦ heatBesselReal n s t u) := by
  apply Continuous.subtype_mk
  simpa only [heatBessel, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.coe_comp,
    Function.comp_def, Submodule.coe_subtypeL, Submodule.subtype_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    toLpₗᵢ_apply] using
    (toLpₗᵢ (ℝ^n) ℂ s 2).symm.continuous.comp (continuous_heatL2 u.val.toLp)

@[simp]
theorem heatBesselReal_zero (s : ℝ) (u : HsSpaceReal n s) : heatBesselReal n s 0 u = u := by
  apply Subtype.ext
  apply (injective_toLp (ℝ^n) ℂ s 2)
  rw [show (heatBesselReal n s 0 u).val = heatBessel n s 0 u.val from rfl,
    toLp_heatBessel, heatL2_zero]

theorem heatBesselReal_add (q : ℝ) (s t : ℝ≥0) (u : HsSpaceReal n q) :
    heatBesselReal n q (s + t) u = heatBesselReal n q s (heatBesselReal n q t u) := by
  apply Subtype.ext
  apply (injective_toLp (ℝ^n) ℂ q 2)
  change toLp (heatBessel n q (s + t) u.val) =
    toLp (heatBessel n q s (heatBessel n q t u.val))
  rw [toLp_heatBessel, toLp_heatBessel, toLp_heatBessel, heatL2_add]

/-- The physical heat operator on the actual integer weak-derivative graph space. -/
def heatSobolev (n k : ℕ) (t : ℝ≥0) : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  (toWkpSpaceCLE n k).toContinuousLinearMap.comp
    ((heatBesselReal n (k : ℝ) t).comp (toWkpSpaceCLE n k).symm.toContinuousLinearMap)

/-- The complexified physical base function determines an entire Sobolev graph element. -/
theorem baseL2_injective : Function.Injective (baseL2 (n := n) (k := k)) := by
  intro u v huv
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply Lp.ext
  rw [← complexifyL2CLM_base u, ← complexifyL2CLM_base v] at huv
  have hAE : ⇑(wkpBaseCoordinateCLM u) =ᵐ[volume] ⇑(wkpBaseCoordinateCLM v) := by
    filter_upwards [Lp.ext_iff.mp huv, complexifyL2CLM_ae (wkpBaseCoordinateCLM u),
      complexifyL2CLM_ae (wkpBaseCoordinateCLM v)] with x he hu hv
    exact Complex.ofReal_injective (hu.symm.trans (he.trans hv))
  simpa only [domainMeasure, Measure.restrict_univ] using hAE

/-- The transferred graph semigroup has the exact physical L² heat base function. -/
theorem baseL2_heatSobolev (t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    baseL2 (heatSobolev n k t u) = heatL2 n t (baseL2 u) := by
  have hbase (v : HsSpaceReal n (k : ℝ)) :
      baseL2 (toWkpSpaceCLM n k v) = toL2Fun (Nat.cast_nonneg k) v.val := by
    have h := toL2Fun_ofWkpSpace (toWkpSpaceCLM n k v)
    simp only [toWkpSpaceCLM_apply, ofWkpSpace_toWkpSpace] at h
    exact h.symm
  change baseL2 (toWkpSpaceCLM n k
    (heatBesselReal n (k : ℝ) t (ofWkpSpaceRealCLM n k u))) = _
  rw [hbase]
  change toL2Fun (Nat.cast_nonneg k) (heatBessel n (k : ℝ) t (ofWkpSpace u)) = _
  rw [toL2Fun_heatBessel, toL2Fun_ofWkpSpace]

theorem continuous_heatSobolev (u : W^{k,2}(ℝ^n)) :
    Continuous (fun t : ℝ≥0 ↦ heatSobolev n k t u) :=
  (toWkpSpaceCLE n k).continuous.comp
    (continuous_heatBesselReal (k : ℝ) ((toWkpSpaceCLE n k).symm u))

@[simp]
theorem heatSobolev_zero (u : W^{k,2}(ℝ^n)) : heatSobolev n k 0 u = u := by
  simp only [heatSobolev, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    heatBesselReal_zero, ContinuousLinearEquiv.apply_symm_apply]

theorem heatSobolev_add (s t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    heatSobolev n k (s + t) u = heatSobolev n k s (heatSobolev n k t u) := by
  simp only [heatSobolev, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, heatBesselReal_add]

/-- The integer graph heat evolution is a strongly continuous semigroup. -/
def heatSobolevSemigroup (n k : ℕ) : StronglyContinuousSemigroup (W^{k,2}(ℝ^n)) where
  toMonoidHom :=
    { toFun := fun t ↦ heatSobolev n k t.toAdd
      map_one' := by apply ContinuousLinearMap.ext; intro u; exact heatSobolev_zero u
      map_mul' := by
        intro s t
        apply ContinuousLinearMap.ext
        intro u
        exact heatSobolev_add s.toAdd t.toAdd u }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro u
    exact continuous_heatSobolev u

end HeatEquation.WholeSpace
