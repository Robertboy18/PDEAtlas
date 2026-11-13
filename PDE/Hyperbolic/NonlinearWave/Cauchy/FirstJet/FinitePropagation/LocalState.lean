/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.InteriorAgreement

/-!
# Restriction of the first-jet energy state

On an open set, equality of displacement and velocity representatives determines
all local energy coordinates. This identifies the vanishing-density conclusion
of finite propagation with equality in the usual local H¹ × L² spaces.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Restrict displacement and velocity to a measurable spatial set. -/
def restrictStateCLM (hΩ : MeasurableSet Ω) :
    (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ] (W^{1,2}(Ω) × DerivLp n 2 Ω) :=
  (restrictCLM hΩ (subset_univ Ω)).prodMap (restrictDerivLp (subset_univ Ω))

/-- Equality of local states is exactly equality of their two base functions.
Uniqueness of weak derivatives supplies equality of the gradient coordinates. -/
theorem restrictStateCLM_eq_iff (hΩ : IsOpen Ω) (x y : H¹(ℝ^n) × DerivLp n 2 univ) :
    restrictStateCLM hΩ.measurableSet x = restrictStateCLM hΩ.measurableSet y ↔
      baseRepresentative x.1 =ᵐ[domainMeasure n Ω] baseRepresentative y.1 ∧
      (x.2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] y.2 := by
  have hqx := restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) x.1 (baseIndex n 1)
  have hqy := restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) y.1 (baseIndex n 1)
  have hvx := restrictDerivLp_apply_ae (subset_univ Ω) x.2
  have hvy := restrictDerivLp_apply_ae (subset_univ Ω) y.2
  constructor
  · intro h
    have hq := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    change restrictCLM hΩ.measurableSet (subset_univ Ω) x.1 =
      restrictCLM hΩ.measurableSet (subset_univ Ω) y.1 at hq
    change restrictDerivLp (subset_univ Ω) x.2 = restrictDerivLp (subset_univ Ω) y.2 at hv
    exact ⟨hqx.symm.trans (hq ▸ hqy), hvx.symm.trans (hv ▸ hvy)⟩
  · rintro ⟨hq, hv⟩
    apply Prod.ext
    · apply wkpBaseCoordinateCLM_injective hΩ
      exact Lp.ext (hqx.trans (hq.trans hqy.symm))
    · exact Lp.ext (hvx.trans (hv.trans hvy.symm))

/-- A zero restricted L² element has a zero representative on that set. -/
theorem ae_zero_of_restrictDerivLp_eq_zero (z : DerivLp n 2 univ)
    (hz : restrictDerivLp (subset_univ Ω) z = 0) :
    ∀ᵐ y ∂domainMeasure n Ω, z y = 0 := by
  have h := (restrictDerivLp_apply_ae (subset_univ Ω) z).symm
  rw [hz] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω))

/-- A local zero state has zero energy density, including all weak derivatives. -/
theorem energyDensity_eq_zero_of_restrictStateCLM_eq_zero (hΩ : MeasurableSet Ω)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (hz : restrictStateCLM hΩ z = 0) :
    ∀ᵐ y ∂domainMeasure n Ω, energyDensity z y = 0 := by
  have hq : restrictCLM hΩ (subset_univ Ω) z.1 = 0 := congrArg Prod.fst hz
  have hv : restrictDerivLp (subset_univ Ω) z.2 = 0 := congrArg Prod.snd hz
  have hc (a : DerivIndex n 1) :
      ∀ᵐ y ∂domainMeasure n Ω, wkpCoordinateCLM a z.1 y = 0 := by
    apply ae_zero_of_restrictDerivLp_eq_zero
    change wkpCoordinateCLM a (restrictCLM hΩ (subset_univ Ω) z.1) = 0
    rw [hq, map_zero]
  filter_upwards [hc (baseIndex n 1), ae_zero_of_restrictDerivLp_eq_zero z.2 hv,
    MeasureTheory.ae_all_iff.mpr (fun i : Fin n ↦ hc (singleDerivIndex n i))] with y h0 hv hg
  simp only [energyDensity, wkpBaseCoordinateCLM, h0, hv, hg, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero]

/-- Vanishing energy density gives a zero local state on an open set. -/
theorem restrictStateCLM_eq_zero_of_energyDensity_eq_zero (hΩ : IsOpen Ω)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (hz : ∀ᵐ y ∂domainMeasure n Ω, energyDensity z y = 0) :
    restrictStateCLM hΩ.measurableSet z = 0 := by
  have hcoord : ∀ᵐ y ∂domainMeasure n Ω,
      baseRepresentative z.1 y = 0 ∧ z.2 y = 0 := by
    filter_upwards [hz] with y hy
    have hs : 0 ≤ ∑ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) z.1 y) ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hq : (wkpBaseCoordinateCLM z.1 y) ^ 2 = 0 := by
      unfold energyDensity at hy
      nlinarith [sq_nonneg (z.2 y), sq_nonneg (wkpBaseCoordinateCLM z.1 y)]
    have hv : (z.2 y) ^ 2 = 0 := by
      unfold energyDensity at hy
      nlinarith [sq_nonneg (z.2 y), sq_nonneg (wkpBaseCoordinateCLM z.1 y)]
    exact ⟨sq_eq_zero_iff.mp hq, sq_eq_zero_iff.mp hv⟩
  rw [← map_zero (restrictStateCLM hΩ.measurableSet)]
  apply (restrictStateCLM_eq_iff hΩ z 0).mpr
  have hzero : ∀ᵐ y ∂domainMeasure n Ω, (0 : DerivLp n 2 univ) y = 0 :=
    (Lp.coeFn_zero ℝ 2 (domainMeasure n univ)).filter_mono
      (ae_mono (domainMeasure_le (subset_univ Ω)))
  constructor
  · filter_upwards [hcoord, hzero] with y hy h0
    change baseRepresentative z.1 y = wkpBaseCoordinateCLM (0 : H¹(ℝ^n)) y
    rw [map_zero]
    exact hy.1.trans h0.symm
  · filter_upwards [hcoord, hzero] with y hy h0
    exact hy.2.trans h0.symm

/-- Local state agreement is equivalent to vanishing difference energy. -/
theorem restrictStateCLM_eq_iff_energyDensity (hΩ : IsOpen Ω) (x y : H¹(ℝ^n) × DerivLp n 2 univ) :
    restrictStateCLM hΩ.measurableSet x = restrictStateCLM hΩ.measurableSet y ↔
      ∀ᵐ z ∂domainMeasure n Ω, energyDensity (x - y) z = 0 := by
  rw [← sub_eq_zero, ← map_sub]
  exact ⟨energyDensity_eq_zero_of_restrictStateCLM_eq_zero hΩ.measurableSet (x - y),
    restrictStateCLM_eq_zero_of_energyDensity_eq_zero hΩ (x - y)⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
