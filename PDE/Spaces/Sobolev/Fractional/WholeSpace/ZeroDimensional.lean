/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation

/-!
# The physical Bessel space in dimension zero

The only frequency in `ℝ^0` is zero, where every Bessel symbol is one.
Consequently, for nonnegative order, the physical representative agrees
with the Bessel representative. On the real subspace this identifies the
physical map with a linear isometry equivalence onto real `L²`.
-/

@[expose] public section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped Sobolev SchwartzMap

namespace SobolevSpace.Fractional

variable {s : ℝ}

/-- Every Bessel symbol is one in dimension zero, at every real order. -/
@[simp]
theorem besselSymbol_zero_dimensional (r : ℝ) (x : ℝ^0) :
    besselSymbol 0 r x = 1 := by
  rw [Subsingleton.elim x 0]
  exact besselSymbol_zero_eq_one

/-- Every Bessel potential operator is the identity in dimension zero. -/
@[simp]
theorem besselPotential_zero_dimensional (s : ℝ) :
    besselPotential (ℝ^0) ℂ s = ContinuousLinearMap.id ℂ 𝓢'(ℝ^0, ℂ) := by
  have hsymbol : (fun x : ℝ^0 ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) =
      fun _ ↦ 1 := by
    funext x
    rw [Subsingleton.elim x 0]
    simp
  simp [besselPotential, hsymbol]

/-- Every physical `L²` function on `ℝ^0` has every real Sobolev order. -/
theorem memSobolev_zero_dimensional (s : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^0))) :
    MemSobolev s 2 (u : 𝓢'(ℝ^0, ℂ)) := by
  exact ⟨u, by rw [besselPotential_zero_dimensional, ContinuousLinearMap.id_apply]⟩

/-- In dimension zero the physical and Bessel representatives coincide. -/
theorem toL2Fun_eq_toLp_zero_dimensional (hs : 0 ≤ s) (u : H^{s}(ℝ^0)) :
    toL2Fun hs u = toLp u := by
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
  rw [← toDistr_eq_toL2Fun hs]
  have h := u.bessel_toDistr_eq_toLp
  rwa [besselPotential_zero_dimensional, ContinuousLinearMap.id_apply] at h

namespace HsSpaceReal

/-- The physical real representative preserves the full Bessel norm in dimension zero. -/
theorem norm_toL2FunCLM_zero_dimensional (hs : 0 ≤ s) (u : H^{s}(ℝ^0; ℝ)) :
    ‖toL2FunCLM 0 hs u‖ = ‖u‖ := by
  rw [norm_toL2FunCLM_eq, toL2Fun_eq_toLp_zero_dimensional, norm_toLp_eq]
  rfl

/-- Every real `L²` function is the physical representative of a real Bessel element
in dimension zero. -/
theorem toL2FunCLM_surjective_zero_dimensional (hs : 0 ≤ s) :
    Function.Surjective (toL2FunCLM 0 hs) := by
  intro f
  let g := Complex.ofRealCLM.compLpL 2 (volume : Measure (ℝ^0)) f
  let v := (toLpₗᵢ (ℝ^0) ℂ s 2).symm g
  have hv : toLp v = g := by
    simpa only [toLpₗᵢ_apply] using (toLpₗᵢ (ℝ^0) ℂ s 2).apply_symm_apply g
  have hg : IsRealL2 g := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL f] with x hx
    simp [g, hx]
  let u : H^{s}(ℝ^0; ℝ) :=
    ⟨v, mem_HsRealSubmodule_iff.mpr (hv.symm ▸ hg)⟩
  refine ⟨u, ?_⟩
  apply Lp.ext
  have hu : SobolevSpace.Fractional.toL2Fun hs u.1 = g :=
    (toL2Fun_eq_toLp_zero_dimensional hs v).trans hv
  filter_upwards [toL2FunCLM_apply_ae hs u,
    Complex.ofRealCLM.coeFn_compLpL f] with x hr hc
  rw [hr, hu, hc]
  rfl

/-- In dimension zero the physical map is a real linear isometry
equivalence from the nonnegative-order Bessel space onto real `L²`. -/
noncomputable def equivLpZeroDimensional (hs : 0 ≤ s) :
    H^{s}(ℝ^0; ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (ℝ^0)) :=
  LinearIsometryEquiv.ofSurjective
    { (toL2FunCLM 0 hs).toLinearMap with
      norm_map' := norm_toL2FunCLM_zero_dimensional hs }
    (toL2FunCLM_surjective_zero_dimensional hs)

/-- The equivalence uses the physical representative as its forward map. -/
@[simp]
theorem equivLpZeroDimensional_apply (hs : 0 ≤ s)
    (u : H^{s}(ℝ^0; ℝ)) :
    equivLpZeroDimensional hs u = toL2FunCLM 0 hs u := rfl

/-- Forgetting the inverse and isometry recovers the physical continuous linear map. -/
@[simp]
theorem equivLpZeroDimensional_toContinuousLinearMap (hs : 0 ≤ s) :
    (equivLpZeroDimensional hs).toContinuousLinearEquiv.toContinuousLinearMap =
      toL2FunCLM 0 hs := rfl

end HsSpaceReal

end SobolevSpace.Fractional
