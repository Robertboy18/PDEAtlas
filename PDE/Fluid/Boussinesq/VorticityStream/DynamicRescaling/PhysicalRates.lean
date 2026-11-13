/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A dynamic rescaling from rates in physical time

In the dynamic rescaling of Chen and Hou the rates are fixed by the rescaled solution. When the
physical solution is known first, the rates are functions of the physical time. Let `a` and `b` be
continuous on an open interval of physical times `J ∋ 0` and put

```text
C(t) = exp ∫₀ᵗ b,   Λ(t) = exp(-∫₀ᵗ a),   τ(t) = ∫₀ᵗ C⁻¹.
```

The rescaled time `τ` is strictly increasing on `J` with derivative `C⁻¹`; with its inverse
`t(τ)` on `τ(J)` the scales `C_ω = C ∘ t`, `C_l = Λ ∘ t`, `C_θ = C² Λ⁻¹ ∘ t`, the clock `t` and
the rates `c_ω = (C b) ∘ t`, `c_l = (C a) ∘ t`, `c_θ = c_l + 2 c_ω` satisfy the scale laws of
the dynamic rescaling at every rescaled time of the open interval `τ(J)`
(`satisfiesDynamicRescalingLawsAt_ofPhysicalRates`): `t' = C ∘ t = C_ω` because `τ' = C⁻¹`, and
`C_ω' = (C b ∘ t) t' = c_ω C_ω`, and similarly for the other scales.

## Main results

* `DynamicRescalingData.ofPhysicalRates`.
* `hasStrictDerivAt_rescaledClock`, `strictMonoOn_rescaledClock`, `isOpen_image_rescaledClock`.
* `physicalTime_ofPhysicalRates_rescaledClock`, `hasStrictDerivAt_physicalTime_ofPhysicalRates`.
* `satisfiesDynamicRescalingLawsAt_ofPhysicalRates`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.7).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Boussinesq.DynamicRescalingData

set_option linter.missingDocs true

/-- The vorticity scale `C(t) = exp ∫₀ᵗ b` as a function of the physical time. -/
def physicalVorticityScale (b : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, b s)

/-- The spatial scale `Λ(t) = exp(-∫₀ᵗ a)` as a function of the physical time. -/
def physicalSpatialScale (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..t, a s)

/-- The rescaled time `τ(t) = ∫₀ᵗ C⁻¹` as a function of the physical time. -/
def rescaledClock (b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (physicalVorticityScale b s)⁻¹

/-- The dynamic rescaling with the rates `a`, `b` of the physical time on `J`: the clock is the
inverse on `J` of the rescaled time `τ`, the scales are `C`, `Λ`, `C² Λ⁻¹` at the physical time,
and the rates are `C b`, `C a` and `C a + 2 C b` at the physical time. -/
def ofPhysicalRates (J : Set ℝ) (a b : ℝ → ℝ) : DynamicRescalingData where
  physicalTime := Function.invFunOn (rescaledClock b) J
  vorticityScale σ := physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ)
  spatialScale σ := physicalSpatialScale a (Function.invFunOn (rescaledClock b) J σ)
  temperatureScale σ := physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ) ^ 2 /
    physicalSpatialScale a (Function.invFunOn (rescaledClock b) J σ)
  vorticityRate σ := physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ) *
    b (Function.invFunOn (rescaledClock b) J σ)
  spatialRate σ := physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ) *
    a (Function.invFunOn (rescaledClock b) J σ)
  temperatureRate σ := physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ) *
      a (Function.invFunOn (rescaledClock b) J σ) +
    2 * (physicalVorticityScale b (Function.invFunOn (rescaledClock b) J σ) *
      b (Function.invFunOn (rescaledClock b) J σ))

/-- The vorticity scale `C(t)` is positive. -/
theorem physicalVorticityScale_pos (b : ℝ → ℝ) (t : ℝ) : 0 < physicalVorticityScale b t :=
  Real.exp_pos _

/-- The spatial scale `Λ(t)` is positive. -/
theorem physicalSpatialScale_pos (a : ℝ → ℝ) (t : ℝ) : 0 < physicalSpatialScale a t :=
  Real.exp_pos _

/-- The vorticity scale is `1` at `t = 0`. -/
@[simp]
theorem physicalVorticityScale_zero (b : ℝ → ℝ) : physicalVorticityScale b 0 = 1 := by
  simp [physicalVorticityScale]

/-- The spatial scale is `1` at `t = 0`. -/
@[simp]
theorem physicalSpatialScale_zero (a : ℝ → ℝ) : physicalSpatialScale a 0 = 1 := by
  simp [physicalSpatialScale]

/-- The rescaled time vanishes at `t = 0`. -/
@[simp]
theorem rescaledClock_zero (b : ℝ → ℝ) : rescaledClock b 0 = 0 := by
  simp [rescaledClock]

variable {J : Set ℝ} {a b : ℝ → ℝ}

section Interval

variable (hJ : IsOpen J) (hJc : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
include hJ hJc h0

/-- The integral from `0` of a function continuous on `J` has the function as strict derivative at
the points of `J`. -/
theorem hasStrictDerivAt_integral_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f J) {t : ℝ}
    (ht : t ∈ J) : HasStrictDerivAt (fun u ↦ ∫ s in (0 : ℝ)..u, f s) (f t) t :=
  intervalIntegral.integral_hasStrictDerivAt_right
    ((hf.mono (hJc.uIcc_subset h0 ht)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter hJ t ht) (hf.continuousAt (hJ.mem_nhds ht))

/-- `C' = b C` on `J`. -/
theorem hasDerivAt_physicalVorticityScale (hb : ContinuousOn b J) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (physicalVorticityScale b) (b t * physicalVorticityScale b t) t := by
  have h := ((hasStrictDerivAt_integral_of_continuousOn hJ hJc h0 hb ht).hasDerivAt).exp
  rw [mul_comm] at h
  exact h

/-- `Λ' = -a Λ` on `J`. -/
theorem hasDerivAt_physicalSpatialScale (ha : ContinuousOn a J) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (physicalSpatialScale a) (-a t * physicalSpatialScale a t) t := by
  have h := ((hasStrictDerivAt_integral_of_continuousOn hJ hJc h0 ha ht).hasDerivAt).neg.exp
  rw [mul_comm] at h
  exact h

/-- The vorticity scale is continuous on `J`. -/
theorem continuousOn_physicalVorticityScale (hb : ContinuousOn b J) :
    ContinuousOn (physicalVorticityScale b) J := fun _ ht ↦
  (hasDerivAt_physicalVorticityScale hJ hJc h0 hb ht).continuousAt.continuousWithinAt

/-- The spatial scale is continuous on `J`. -/
theorem continuousOn_physicalSpatialScale (ha : ContinuousOn a J) :
    ContinuousOn (physicalSpatialScale a) J := fun _ ht ↦
  (hasDerivAt_physicalSpatialScale hJ hJc h0 ha ht).continuousAt.continuousWithinAt

/-- `τ' = C⁻¹` on `J`, as a strict derivative. -/
theorem hasStrictDerivAt_rescaledClock (hb : ContinuousOn b J) {t : ℝ} (ht : t ∈ J) :
    HasStrictDerivAt (rescaledClock b) (physicalVorticityScale b t)⁻¹ t :=
  hasStrictDerivAt_integral_of_continuousOn hJ hJc h0
    ((continuousOn_physicalVorticityScale hJ hJc h0 hb).inv₀ fun s _ ↦
      (physicalVorticityScale_pos b s).ne') ht

/-- The rescaled time is strictly increasing on `J`. -/
theorem strictMonoOn_rescaledClock (hb : ContinuousOn b J) : StrictMonoOn (rescaledClock b) J :=
  strictMonoOn_of_hasDerivWithinAt_pos hJc.convex
    (fun _ ht ↦ (hasStrictDerivAt_rescaledClock hJ hJc h0 hb ht).hasDerivAt.continuousAt
      |>.continuousWithinAt)
    (fun _ ht ↦ (hasStrictDerivAt_rescaledClock hJ hJc h0 hb (interior_subset ht)).hasDerivAt
      |>.hasDerivWithinAt)
    fun t _ ↦ inv_pos.2 (physicalVorticityScale_pos b t)

/-- The rescaled times `τ(J)` form an open set. -/
theorem isOpen_image_rescaledClock (hb : ContinuousOn b J) : IsOpen (rescaledClock b '' J) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, ht, rfl⟩
  rw [← (hasStrictDerivAt_rescaledClock hJ hJc h0 hb ht).map_nhds_eq
    (inv_pos.2 (physicalVorticityScale_pos b t)).ne']
  exact image_mem_map (hJ.mem_nhds ht)

/-- The clock inverts the rescaled time on `J`. -/
theorem physicalTime_ofPhysicalRates_rescaledClock (hb : ContinuousOn b J) {t : ℝ} (ht : t ∈ J) :
    (ofPhysicalRates J a b).physicalTime (rescaledClock b t) = t :=
  (strictMonoOn_rescaledClock hJ hJc h0 hb).injOn.leftInvOn_invFunOn ht

/-- The clock starts at zero. -/
theorem physicalTime_ofPhysicalRates_zero (hb : ContinuousOn b J) :
    (ofPhysicalRates J a b).physicalTime 0 = 0 := by
  simpa using physicalTime_ofPhysicalRates_rescaledClock (a := a) hJ hJc h0 hb h0

omit hJ hJc h0 in
/-- The clock maps the rescaled times `τ(J)` into `J`. -/
theorem physicalTime_ofPhysicalRates_mem {σ : ℝ} (hσ : σ ∈ rescaledClock b '' J) :
    (ofPhysicalRates J a b).physicalTime σ ∈ J := by
  obtain ⟨t, ht, rfl⟩ := hσ
  exact Function.invFunOn_mem ⟨t, ht, rfl⟩

omit hJ hJc h0 in
/-- The rescaled time of the clock is the identity on `τ(J)`. -/
theorem rescaledClock_physicalTime_ofPhysicalRates {σ : ℝ} (hσ : σ ∈ rescaledClock b '' J) :
    rescaledClock b ((ofPhysicalRates J a b).physicalTime σ) = σ := by
  obtain ⟨t, ht, rfl⟩ := hσ
  exact Function.invFunOn_eq ⟨t, ht, rfl⟩

/-- `t' = C ∘ t` on `τ(J)`, as a strict derivative. -/
theorem hasStrictDerivAt_physicalTime_ofPhysicalRates (hb : ContinuousOn b J) {σ : ℝ}
    (hσ : σ ∈ rescaledClock b '' J) :
    HasStrictDerivAt (ofPhysicalRates J a b).physicalTime
      ((ofPhysicalRates J a b).vorticityScale σ) σ := by
  obtain ⟨t, ht, rfl⟩ := hσ
  have h := (hasStrictDerivAt_rescaledClock hJ hJc h0 hb ht).to_local_left_inverse
    (g := (ofPhysicalRates J a b).physicalTime)
    (inv_pos.2 (physicalVorticityScale_pos b t)).ne'
    (Filter.eventually_of_mem (hJ.mem_nhds ht) fun s hs ↦
      physicalTime_ofPhysicalRates_rescaledClock hJ hJc h0 hb hs)
  rw [inv_inv] at h
  change HasStrictDerivAt _ (physicalVorticityScale b
    ((ofPhysicalRates J a b).physicalTime (rescaledClock b t))) _
  rwa [physicalTime_ofPhysicalRates_rescaledClock hJ hJc h0 hb ht]

/-- The clock is continuous on `τ(J)`. -/
theorem continuousOn_physicalTime_ofPhysicalRates (hb : ContinuousOn b J) :
    ContinuousOn (ofPhysicalRates J a b).physicalTime (rescaledClock b '' J) := fun _ hσ ↦
  (hasStrictDerivAt_physicalTime_ofPhysicalRates (a := a) hJ hJc h0 hb hσ).hasDerivAt
    |>.continuousAt.continuousWithinAt

/-- **The scale laws.** For rates `a`, `b` continuous on `J`, the rescaling `ofPhysicalRates J a b`
satisfies the scale laws of the dynamic rescaling at every rescaled time of `τ(J)`. -/
theorem satisfiesDynamicRescalingLawsAt_ofPhysicalRates (ha : ContinuousOn a J)
    (hb : ContinuousOn b J) {σ : ℝ} (hσ : σ ∈ rescaledClock b '' J) :
    SatisfiesDynamicRescalingLawsAt (ofPhysicalRates J a b) σ := by
  set D := ofPhysicalRates J a b
  have ht := physicalTime_ofPhysicalRates_mem (a := a) hσ
  have hT := (hasStrictDerivAt_physicalTime_ofPhysicalRates (a := a) hJ hJc h0 hb hσ).hasDerivAt
  set t := D.physicalTime σ
  have hC := (hasDerivAt_physicalVorticityScale hJ hJc h0 hb ht).comp σ hT
  have hΛ := (hasDerivAt_physicalSpatialScale hJ hJc h0 ha ht).comp σ hT
  have hC0 := (physicalVorticityScale_pos b t).ne'
  have hΛ0 := (physicalSpatialScale_pos a t).ne'
  refine
    { vorticityScale_hasDerivAt := ?_
      spatialScale_hasDerivAt := ?_
      temperatureScale_hasDerivAt := ?_
      physicalTime_hasDerivAt := hT
      spatialScale_pos := physicalSpatialScale_pos a t
      sourceScale_eq := ?_
      temperatureRate_eq := rfl }
  · refine hC.congr_deriv ?_
    change _ = physicalVorticityScale b t * b t * physicalVorticityScale b t
    change b t * physicalVorticityScale b t * physicalVorticityScale b t = _
    ring
  · refine hΛ.congr_deriv ?_
    change -a t * physicalSpatialScale a t * physicalVorticityScale b t =
      -(physicalVorticityScale b t * a t) * physicalSpatialScale a t
    ring
  · have e1 : (ofPhysicalRates J a b).vorticityScale σ = physicalVorticityScale b t := rfl
    have e2 : (physicalVorticityScale b ∘ (ofPhysicalRates J a b).physicalTime) σ =
        physicalVorticityScale b t := rfl
    have e3 : (physicalSpatialScale a ∘ (ofPhysicalRates J a b).physicalTime) σ =
        physicalSpatialScale a t := rfl
    refine ((hC.pow 2).div hΛ hΛ0).congr_deriv ?_
    simp only [Pi.pow_apply, e1, e2, e3]
    change _ = (physicalVorticityScale b t * a t + 2 * (physicalVorticityScale b t * b t)) *
      (physicalVorticityScale b t ^ 2 / physicalSpatialScale a t)
    field_simp
    ring
  · change physicalVorticityScale b t ^ 2 / physicalSpatialScale a t * physicalSpatialScale a t =
      physicalVorticityScale b t ^ 2
    field_simp

/-- The vorticity rate of `ofPhysicalRates J a b` is continuous on `τ(J)`. -/
theorem continuousOn_vorticityRate_ofPhysicalRates (hb : ContinuousOn b J) :
    ContinuousOn (ofPhysicalRates J a b).vorticityRate (rescaledClock b '' J) := by
  have hT := continuousOn_physicalTime_ofPhysicalRates (a := a) hJ hJc h0 hb
  have hmaps : MapsTo (ofPhysicalRates J a b).physicalTime (rescaledClock b '' J) J :=
    fun _ hσ ↦ physicalTime_ofPhysicalRates_mem hσ
  exact ((continuousOn_physicalVorticityScale hJ hJc h0 hb).comp hT hmaps).mul
    (hb.comp hT hmaps)

/-- The spatial rate of `ofPhysicalRates J a b` is continuous on `τ(J)`. -/
theorem continuousOn_spatialRate_ofPhysicalRates (ha : ContinuousOn a J) (hb : ContinuousOn b J) :
    ContinuousOn (ofPhysicalRates J a b).spatialRate (rescaledClock b '' J) := by
  have hT := continuousOn_physicalTime_ofPhysicalRates (a := a) hJ hJc h0 hb
  have hmaps : MapsTo (ofPhysicalRates J a b).physicalTime (rescaledClock b '' J) J :=
    fun _ hσ ↦ physicalTime_ofPhysicalRates_mem hσ
  exact ((continuousOn_physicalVorticityScale hJ hJc h0 hb).comp hT hmaps).mul
    (ha.comp hT hmaps)

end Interval

end Boussinesq.DynamicRescalingData
