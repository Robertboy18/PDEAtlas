/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.CarriedFields
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Uniform bounds of the iteration for short times

The local existence proof iterates `ω ↦ carriedHistory ω₀ θ₀ (-T) T ω` on vorticity histories. For
data `IsHolderData ω₀ θ₀ α R N` we show that the class of `C^{1,α}` histories on `[-T, T]` supported
in the disc of radius `R + 1` with all bounds `2 N + 1` (the Hölder constant of the values
`2 (2 N + 1)`) contains the constant history of the extended datum and is mapped into itself when
`T` is small enough (`exists_mapsTo_isIterationClass`). For histories of the class the amplitude is
Lipschitz in the label and the carried fields at each time are again data (`isHolderData_carried`).

## Main definitions

* `IsIterationClass`: the class of `C^{1,α}` histories on `[-T, T]` supported in the disc of
  radius `R + 1` with all bounds `2 N + 1`.
* `iterationAmplitudeLipschitz`: the Lipschitz constant in the label of the amplitude for
  histories of the class.
* `iterationOutputBound`: the bound of the output data class of the local theorem.

## Main results

* `IsC1VorticityHistory.isBoundedFlowOn`: the flow bounds of the velocity field of a history
  `IsC1VorticityHistory ω a b α R B M B₁ M₁`. With `τ = b - a` and `K₁ = katoBound α R B M`, the
  first variation is at most `exp (K₁ τ)`, the second at most `secondVariationBound K₁ K₂ τ` and
  Hölder with constant `secondVariationHolderConst K₁ K₂ K₃ τ`, where `K₂` bounds the second
  derivative of the velocity and `K₃` its Hölder constant.
* `exists_iterationTime`: there is `T > 0` for which one step of the iteration keeps the values,
  the gradient and its Hölder constant below `2 N + 1` and moves the support by less than `1`.
* `isIterationClass_dataVorticity`: the constant history of the extended vorticity datum is in
  the class.
* `isIterationClass_carriedHistory`: one step of the iteration preserves the class.
* `exists_mapsTo_isIterationClass`: for `0 < α < 1`, `0 ≤ R`, `0 ≤ N` the iteration preserves the
  class for some `T > 0` depending only on `α`, `R` and `N`.
* `IsIterationClass.abs_amplitude_sub_le`: the amplitude is Lipschitz in the label for histories
  of the class.
* `isHolderData_carried`: the carried vorticity and temperature at every time of `[-T, T]` are
  data of the class `IsHolderData` with support radius `R + 1`.

## How it works

The flow bounds come from the general estimates for flows that keep a set invariant
(`IsC1FieldOn.norm_variationOn_le_of_invariant`,
`IsC2FieldOn.norm_secondVariationOn_le_of_invariant` and their Hölder versions), applied on the
closed half-plane with the bounds `K₁`, `K₂`, `K₃`; the flow preserves the closed half-plane because
the normal component of the velocity vanishes on the boundary
(`IsLipschitzFieldOn.mapsTo_flowOn_nonneg`). The constants of one step of the iteration are
continuous in `T`, and at `T = 0` the first-variation bound is `1` and the second-variation bounds
vanish (`iterationVariationBound_zero`, `iterationSecondBound_zero`,
`iterationSecondHolderConst_zero`). The bounds of the values, of the gradient and of its Hölder
constant are then `N < 2 N + 1` and the support moves by `0 < 1`, so they persist for some `T > 0`
(`exists_iterationTime`). The bounds `IsBoundedFlowOn.abs_carriedVorticity_le`,
`IsBoundedFlowOn.norm_fderiv_carriedVorticity_le` and
`IsBoundedFlowOn.norm_fderiv_carriedVorticity_sub_le` of the carried vorticity grow with `|t| ≤ T`,
so this choice keeps them below `2 N + 1` (`isIterationClass_carriedHistory`). The Hölder constant
`2 (2 N + 1)` of the values follows from the bound and the Lipschitz constant `2 N + 1`
(`norm_sub_le_max_mul_rpow`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The Hölder constant of the second variation is monotone in the time span. -/
theorem secondVariationHolderConst_mono {K₁ K₂ K₃ τ τ' : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hτ : 0 ≤ τ) (hττ' : τ ≤ τ') :
    secondVariationHolderConst K₁ K₂ K₃ τ ≤ secondVariationHolderConst K₁ K₂ K₃ τ' := by
  have hσ := secondVariationBound_mono hK₁ hK₂ hτ hττ'
  have hσ0 : 0 ≤ secondVariationBound K₁ K₂ τ := by
    unfold secondVariationBound; positivity
  have hτ' : 0 ≤ τ' := hτ.trans hττ'
  have he₁ : Real.exp (K₁ * τ) ≤ Real.exp (K₁ * τ') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hττ' hK₁)
  have he₃ : Real.exp (3 * K₁ * τ) ≤ Real.exp (3 * K₁ * τ') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hττ' (by positivity))
  unfold secondVariationHolderConst
  gcongr

namespace IsC1VorticityHistory

variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M B₁ M₁ : ℝ}

/-- On the closed half-plane the second derivative of the field of a history is the second
derivative within the closed half-plane of the half-plane velocity. -/
theorem historyFieldDeriv₂_eq (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α)
    (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    historyFieldDeriv₂ ω r y =
      fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity (ω r)) H̄) H̄ y :=
  fderiv_fderiv_extendedVelocity_of_nonneg (K := 2) le_rfl
    (hω.contDiffOn_halfPlaneVelocity_two hα hα1 hr) hy

/-- **The flow bounds of the velocity field of a `C^{1,α}` history** on `[a, b]`, with
`τ = b - a`, `K₁ = katoBound α R B M`, `K₂ = secondDerivBound α R B B₁ M₁` and
`K₃ = (844 / (α (1 - α)) + 1) M₁`. -/
theorem isBoundedFlowOn (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α)
    (hα1 : α < 1) (hR : 0 ≤ R) (hab : a ≤ b) :
    IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α
      ((1 + R ^ 2) * B) (katoBound α R B M) (Real.exp (katoBound α R B M * (b - a)))
      (Real.exp (katoBound α R B M * (b - a)) - 1)
      (secondVariationBound (katoBound α R B M) (secondDerivBound α R B B₁ M₁) (b - a))
      (secondVariationHolderConst (katoBound α R B M) (secondDerivBound α R B B₁ M₁)
        ((844 / (α * (1 - α)) + 1) * M₁) (b - a)) := by
  have hmax : max R 0 = R := max_eq_left hR
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have hv1 := hv.toIsC1FieldOn
  set K₁ := katoBound α R B M
  set K₂ := secondDerivBound α R B B₁ M₁
  set K₃ := (844 / (α * (1 - α)) + 1) * M₁
  have hta : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have htan : ∀ r ∈ Icc a b, ∀ x : ℝ^2, x 1 = 0 → historyField ω r x 1 = 0 := fun r hr x hx ↦
    extendedVelocity_normal_eq_zero 2 (hω.continuousOn r hr) (hω.eq_zero r hr) hx
  have hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn (historyField ω) a b s t) H̄ H̄ :=
    fun s hs t ht ↦ hv1.isLipschitzFieldOn.mapsTo_flowOn_nonneg (j := 1) htan hs ht
  have hDv : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ‖historyFieldDeriv ω r y‖ ≤ K₁ := fun r hr y hy ↦ by
    rw [IsC1VorticityHistory.historyFieldDeriv_eq hω hα hα1 hr hy]
    have h := hω.toIsVorticityHistory.norm_fderivWithin_le hα hα1 hr hy
    rwa [hmax] at h
  have hD2v : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ‖historyFieldDeriv₂ ω r y‖ ≤ K₂ := fun r hr y hy ↦ by
    rw [IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hr hy]
    have h := hω.norm_fderivWithin_fderivWithin_le hα hα1 hr hy
    rwa [hmax] at h
  have hD2vH : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖historyFieldDeriv₂ ω r y - historyFieldDeriv₂ ω r z‖ ≤ K₃ * ‖y - z‖ ^ α :=
    fun r hr y hy z hz ↦ by
      rw [IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hr hy,
        IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hr hz]
      exact hω.norm_fderivWithin_fderivWithin_sub_le hα hα1 hr hy hz
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv a hta 0 (by simp))
  have hK₂ : 0 ≤ K₂ :=
    (ContinuousLinearMap.opNorm_nonneg _).trans (hD2v a hta 0 (by simp))
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans ((hω.holder_fderivWithin a hta 0
    (EuclideanSpace.single 1 1) (le_refl _) (by simp)).trans (by simp))
  have hK₃ : 0 ≤ K₃ := by
    have : 0 < α * (1 - α) := mul_pos hα (by linarith)
    positivity
  have hst {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : |s - t| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have he {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
      Real.exp (K₁ * |s - t|) ≤ Real.exp (K₁ * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hst hs ht) hK₁)
  refine
    { mapsTo := hS
      norm_le := fun r hr y hy ↦ ?_
      norm_deriv_le := hDv
      norm_variationOn_le := fun s hs t ht x hx ↦
        (hv1.norm_variationOn_le_of_invariant hS hDv hs ht hx).trans (he hs ht)
      norm_variationOn_sub_id_le := fun s hs t ht x hx ↦
        (hv1.norm_variationOn_sub_id_le_of_invariant hS hDv hs ht hx).trans
          (by linarith [he hs ht])
      norm_secondVariationOn_le := fun s hs t ht x hx ↦
        (hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v hs ht hx).trans
          (secondVariationBound_mono hK₁ hK₂ (abs_nonneg _) (hst hs ht))
      holder_secondVariationOn := fun s hs t ht x y hx hy ↦
        (hv.norm_secondVariationOn_sub_le_rpow_of_invariant
          PDE.Analysis.convex_closedUpperHalfPlane hS hDv hD2v hα.le hα1.le hK₃ hD2vH hs ht hx
          hy).trans (mul_le_mul_of_nonneg_right
            (secondVariationHolderConst_mono hK₁ hK₂ hK₃ (abs_nonneg _) (hst hs ht))
            (Real.rpow_nonneg (norm_nonneg _) α)) }
  rw [historyField_of_nonneg ω r hy]
  exact norm_halfPlaneVelocity_le_of_abs_le (hω.continuousOn r hr) (hω.eq_zero r hr) hR
    (hω.abs_le r hr) y

end IsC1VorticityHistory

/-! ### The class of the iteration and the choice of the time -/

/-- The class of the iteration on `[-T, T]` for data of size `N` and support radius `R`: `C^{1,α}`
histories supported on the closed half-plane in the disc of radius `R + 1`, with values,
gradients and the Hölder constant of the gradient at most `2 N + 1` and the Hölder constant of the
values at most `2 (2 N + 1)`. -/
def IsIterationClass (T α R N : ℝ) (ω : ℝ → ℝ^2 → ℝ) : Prop :=
  IsC1VorticityHistory ω (-T) T α (R + 1) (2 * N + 1) (2 * (2 * N + 1)) (2 * N + 1) (2 * N + 1)

/-- The first-variation bound `exp (K₁ (T - (-T)))` over `[-T, T]` for the class. -/
def iterationVariationBound (α R N T : ℝ) : ℝ :=
  Real.exp (katoBound α (R + 1) (2 * N + 1) (2 * (2 * N + 1)) * (T - -T))

/-- The second-variation bound over `[-T, T]` for the class. -/
def iterationSecondBound (α R N T : ℝ) : ℝ :=
  secondVariationBound (katoBound α (R + 1) (2 * N + 1) (2 * (2 * N + 1)))
    (secondDerivBound α (R + 1) (2 * N + 1) (2 * N + 1) (2 * N + 1)) (T - -T)

/-- The Hölder constant of the second variation over `[-T, T]` for the class. -/
def iterationSecondHolderConst (α R N T : ℝ) : ℝ :=
  secondVariationHolderConst (katoBound α (R + 1) (2 * N + 1) (2 * (2 * N + 1)))
    (secondDerivBound α (R + 1) (2 * N + 1) (2 * N + 1) (2 * N + 1))
    ((844 / (α * (1 - α)) + 1) * (2 * N + 1)) (T - -T)

/-- The velocity bound of the class. -/
def iterationVelocityBound (R N : ℝ) : ℝ :=
  (1 + (R + 1) ^ 2) * (2 * N + 1)

/-- The bound of the gradient of the carried vorticity after one step of the iteration. -/
def iterationGradientBound (α R N T : ℝ) : ℝ :=
  (N + T * forcingDerivBound N (iterationVariationBound α R N T) (iterationSecondBound α R N T)) *
    iterationVariationBound α R N T

/-- The Hölder constant of the gradient of the carried vorticity after one step. -/
def iterationHolderBound (α R N T : ℝ) : ℝ :=
  (N + T * forcingDerivHolderConst N (iterationVariationBound α R N T)
      (iterationSecondBound α R N T) (iterationSecondHolderConst α R N T)) *
      iterationVariationBound α R N T ^ α * iterationVariationBound α R N T +
    (N + T * forcingDerivBound N (iterationVariationBound α R N T)
      (iterationSecondBound α R N T)) *
      max (iterationSecondBound α R N T) (2 * (iterationVariationBound α R N T - 1))

/-- The first-variation bound depends continuously on the time. -/
theorem continuous_iterationVariationBound (α R N : ℝ) :
    Continuous (iterationVariationBound α R N) := by
  unfold iterationVariationBound; fun_prop

/-- The second-variation bound depends continuously on the time. -/
theorem continuous_iterationSecondBound (α R N : ℝ) :
    Continuous (iterationSecondBound α R N) := by
  unfold iterationSecondBound secondVariationBound; fun_prop

/-- The Hölder constant of the second variation depends continuously on the time. -/
theorem continuous_iterationSecondHolderConst (α R N : ℝ) :
    Continuous (iterationSecondHolderConst α R N) := by
  unfold iterationSecondHolderConst secondVariationHolderConst secondVariationBound; fun_prop

/-- At time zero the first-variation bound is `1`. -/
theorem iterationVariationBound_zero (α R N : ℝ) : iterationVariationBound α R N 0 = 1 := by
  simp [iterationVariationBound]

/-- At time zero the second-variation bound is `0`. -/
theorem iterationSecondBound_zero (α R N : ℝ) : iterationSecondBound α R N 0 = 0 := by
  simp [iterationSecondBound, secondVariationBound]

/-- At time zero the Hölder constant of the second variation is `0`. -/
theorem iterationSecondHolderConst_zero (α R N : ℝ) :
    iterationSecondHolderConst α R N 0 = 0 := by
  simp [iterationSecondHolderConst, secondVariationHolderConst, secondVariationBound]

/-- **The time of the iteration.** For `0 < α`, `0 ≤ N`, there is `T > 0` for which one step of
the iteration keeps the values, the gradient and its Hölder constant below `2 N + 1` and moves
the support by less than `1`. -/
theorem exists_iterationTime {α R N : ℝ} (hα : 0 < α) (hN : 0 ≤ N) :
    ∃ T > 0, N + T * (N * iterationVariationBound α R N T) ≤ 2 * N + 1 ∧
      iterationGradientBound α R N T ≤ 2 * N + 1 ∧ iterationHolderBound α R N T ≤ 2 * N + 1 ∧
      iterationVelocityBound R N * T ≤ 1 := by
  have hL := continuous_iterationVariationBound α R N
  have hσ := continuous_iterationSecondBound α R N
  have hη := continuous_iterationSecondHolderConst α R N
  have hc₀ : Continuous fun T ↦ forcingDerivBound N (iterationVariationBound α R N T)
      (iterationSecondBound α R N T) := by
    unfold forcingDerivBound; fun_prop
  have hcα : Continuous fun T ↦ forcingDerivHolderConst N (iterationVariationBound α R N T)
      (iterationSecondBound α R N T) (iterationSecondHolderConst α R N T) := by
    unfold forcingDerivHolderConst forcingDerivBound; fun_prop
  have hLα : Continuous fun T ↦ iterationVariationBound α R N T ^ α :=
    (Real.continuous_rpow_const hα.le).comp hL
  have h₁ : Continuous fun T ↦ N + T * (N * iterationVariationBound α R N T) := by fun_prop
  have h₂ : Continuous (iterationGradientBound α R N) := by
    unfold iterationGradientBound; fun_prop
  have h₃ : Continuous (iterationHolderBound α R N) := by
    unfold iterationHolderBound
    exact ((continuous_const.add (continuous_id.mul hcα)).mul hLα |>.mul hL).add
      ((continuous_const.add (continuous_id.mul hc₀)).mul
        (hσ.max (continuous_const.mul (hL.sub continuous_const))))
  have h₄ : Continuous fun T ↦ iterationVelocityBound R N * T := by fun_prop
  have hlt : N < 2 * N + 1 := by linarith
  have e₁ : ∀ᶠ T in 𝓝 0, N + T * (N * iterationVariationBound α R N T) < 2 * N + 1 :=
    h₁.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
  have e₂ : ∀ᶠ T in 𝓝 0, iterationGradientBound α R N T < 2 * N + 1 :=
    h₂.continuousAt.eventually_lt continuousAt_const (by
      simpa [iterationGradientBound, iterationVariationBound_zero] using hlt)
  have e₃ : ∀ᶠ T in 𝓝 0, iterationHolderBound α R N T < 2 * N + 1 :=
    h₃.continuousAt.eventually_lt continuousAt_const (by
      simpa [iterationHolderBound, iterationVariationBound_zero, iterationSecondBound_zero]
        using hlt)
  have e₄ : ∀ᶠ T in 𝓝 0, iterationVelocityBound R N * T < 1 :=
    h₄.continuousAt.eventually_lt continuousAt_const (by simp)
  have hev : ∀ᶠ T in 𝓝[>] (0 : ℝ), T ∈ Ioi 0 ∧
      (N + T * (N * iterationVariationBound α R N T) < 2 * N + 1 ∧
        iterationGradientBound α R N T < 2 * N + 1 ∧
        iterationHolderBound α R N T < 2 * N + 1 ∧ iterationVelocityBound R N * T < 1) :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (e₁.and (e₂.and (e₃.and e₄))))
  obtain ⟨T, hT, h1, h2, h3, h4⟩ := hev.exists
  exact ⟨T, hT, h1.le, h2.le, h3.le, h4.le⟩

/-! ### The invariance of the class -/

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R N T : ℝ}

/-- The flow bounds of the field of a history in the class of the iteration. -/
theorem IsIterationClass.isBoundedFlowOn {ω : ℝ → ℝ^2 → ℝ} (hω : IsIterationClass T α R N ω)
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) (-T) T α
      (iterationVelocityBound R N) (katoBound α (R + 1) (2 * N + 1) (2 * (2 * N + 1)))
      (iterationVariationBound α R N T) (iterationVariationBound α R N T - 1)
      (iterationSecondBound α R N T) (iterationSecondHolderConst α R N T) :=
  IsC1VorticityHistory.isBoundedFlowOn hω hα hα1 (by linarith) (by linarith)

/-- A real `x` with `x ∈ [-T, T]` has `|x| ≤ T`. -/
theorem abs_le_of_mem_Icc_neg {T t : ℝ} (ht : t ∈ Icc (-T) T) : |t| ≤ T :=
  abs_le.mpr ⟨ht.1, ht.2⟩

/-- The constant history of the extended vorticity datum is in the class of the iteration. -/
theorem isIterationClass_dataVorticity (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : IsIterationClass T α R N (fun _ ↦ dataVorticity ω₀) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hc := hd.contDiff_dataVorticity
  have hfd {y : ℝ^2} (hy : 0 ≤ y 1) :
      fderivWithin ℝ (dataVorticity ω₀) H̄ y = fderiv ℝ (dataVorticity ω₀) y :=
    fderivWithin_closedUpper_eq (hc.differentiable one_ne_zero) hy
  have hLip : ∀ x ∈ H̄, ∀ y ∈ H̄, ‖dataVorticity ω₀ x - dataVorticity ω₀ y‖ ≤ N * dist x y :=
    fun x hx y hy ↦ by
      rw [dist_eq_norm]
      exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ ↦ ((hc.differentiable one_ne_zero) z).hasFDerivAt.hasFDerivWithinAt)
        (fun z hz ↦ hd.norm_fderiv_dataVorticity_le hz) hy hx
  refine
    { continuousOn := fun _ _ ↦ hc.continuous.continuousOn
      eq_zero := fun _ _ y hy hyR ↦ (hd.data_eq_zero hy (by linarith)).1
      abs_le := fun _ _ y hy ↦ (hd.abs_dataVorticity_le hy).trans (by linarith)
      holder := fun _ _ y z hy hz ↦ ?_
      uniform := fun _ _ ε hε ↦ ⟨1, one_pos, fun _ _ _ _ _ ↦ by simp [hε.le]⟩
      contDiffOn := fun _ _ ↦ hc.contDiffOn
      norm_fderivWithin_le := fun _ _ y hy ↦ by
        rw [hfd hy]; exact (hd.norm_fderiv_dataVorticity_le hy).trans (by linarith)
      holder_fderivWithin := fun _ _ y z hy hz ↦ by
        rw [hfd hy, hfd hz]
        exact (hd.norm_fderiv_dataVorticity_sub_le hy hz).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) α))
      uniform_fderivWithin := fun _ _ ε hε ↦ ⟨1, one_pos, fun _ _ _ _ _ ↦ by simp [hε.le]⟩ }
  have h := PDE.Analysis.norm_sub_le_max_mul_rpow (f := dataVorticity ω₀) (S := H̄) hLip
    (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hd.abs_dataVorticity_le hx) hα0 hα1 hy hz
  rw [Real.norm_eq_abs, dist_eq_norm, max_eq_right (by linarith)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) α))

/-- **One step of the iteration preserves the class** when the time `T` satisfies the bounds of
`exists_iterationTime`. -/
theorem isIterationClass_carriedHistory (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α)
    (hα1 : α < 1) (hR : 0 ≤ R) (hT : 0 < T)
    (h₁ : N + T * (N * iterationVariationBound α R N T) ≤ 2 * N + 1)
    (h₂ : iterationGradientBound α R N T ≤ 2 * N + 1)
    (h₃ : iterationHolderBound α R N T ≤ 2 * N + 1) (h₄ : iterationVelocityBound R N * T ≤ 1)
    {ω : ℝ → ℝ^2 → ℝ} (hω : IsIterationClass T α R N ω) :
    IsIterationClass T α R N (carriedHistory ω₀ θ₀ (-T) T ω) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hα hα1 hR hT.le
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := forcingDerivBound_nonneg hN hL0 hσ0
  have hcα := forcingDerivHolderConst_nonneg hN hL0 hσ0 (hb.zero_le_η h0)
  set N₁ := 2 * N + 1
  have hfd {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      fderivWithin ℝ (carriedHistory ω₀ θ₀ (-T) T ω t) H̄ y =
        fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω (-T) T z t) y :=
    IsBoundedFlowOn.fderivWithin_carriedVorticity hv h0 hd ht hy
  have hgrad {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      ‖fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω (-T) T z t) y‖ ≤ N₁ := by
    refine (hb.norm_fderiv_carriedVorticity_le hv h0 hd ht hy).trans (le_trans ?_ h₂)
    unfold iterationGradientBound
    gcongr
    exact abs_le_of_mem_Icc_neg ht
  have hLip {t : ℝ} (ht : t ∈ Icc (-T) T) : ∀ x ∈ H̄, ∀ y ∈ H̄,
      ‖carriedVorticity ω₀ θ₀ ω (-T) T x t - carriedVorticity ω₀ θ₀ ω (-T) T y t‖ ≤
        N₁ * dist x y := fun x hx y hy ↦ by
    rw [dist_eq_norm]
    exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ ↦ (IsBoundedFlowOn.hasFDerivAt_carriedVorticity hv h0 hd ht z).differentiableAt
        |>.hasFDerivAt.hasFDerivWithinAt) (fun z hz ↦ hgrad ht hz) hy hx
  have habs {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      |carriedVorticity ω₀ θ₀ ω (-T) T y t| ≤ N₁ := by
    refine (hb.abs_carriedVorticity_le h0 hd ht hy).trans (le_trans ?_ h₁)
    gcongr
    exact abs_le_of_mem_Icc_neg ht
  refine
    { continuousOn := fun t ht ↦
        (IsBoundedFlowOn.contDiff_carriedVorticity hv h0 hd ht).continuous.continuousOn
      eq_zero := fun t ht y hy hyR ↦ ?_
      abs_le := fun t ht y hy ↦ habs ht hy
      holder := fun t ht y z hy hz ↦ ?_
      uniform := fun t ht ε hε ↦ hb.exists_abs_carriedVorticity_sub_le hv h0 hd ht hε
      contDiffOn := fun t ht ↦ (IsBoundedFlowOn.contDiff_carriedVorticity hv h0 hd ht).contDiffOn
      norm_fderivWithin_le := fun t ht y hy ↦ by rw [hfd ht hy]; exact hgrad ht hy
      holder_fderivWithin := fun t ht y z hy hz ↦ ?_
      uniform_fderivWithin := fun t ht ε hε ↦ ?_ }
  · have hV : iterationVelocityBound R N * T ≤ 1 := h₄
    exact (hb.carried_eq_zero h0 hd ht (abs_le_of_mem_Icc_neg ht) hy
      (by linarith)).1
  · have h := PDE.Analysis.norm_sub_le_max_mul_rpow
      (f := fun x ↦ carriedVorticity ω₀ θ₀ ω (-T) T x t) (S := H̄) (hLip ht)
      (fun x hx ↦ by rw [Real.norm_eq_abs]; exact habs ht hx) hα.le hα1.le hy hz
    rw [Real.norm_eq_abs, dist_eq_norm, max_eq_right (by linarith)] at h
    exact h
  · rw [hfd ht hy, hfd ht hz]
    refine (hb.norm_fderiv_carriedVorticity_sub_le hv h0 hd hα.le hα1.le ht hy hz).trans
      (mul_le_mul_of_nonneg_right (le_trans ?_ h₃) (Real.rpow_nonneg (norm_nonneg _) α))
    have htT := abs_le_of_mem_Icc_neg ht
    unfold iterationHolderBound
    gcongr
  · obtain ⟨δ', hδ', h⟩ := hb.exists_norm_fderiv_carriedVorticity_sub_le hv h0 hd hα hα1.le ht hε
    refine ⟨δ', hδ', fun s hs hst y hy ↦ ?_⟩
    rw [hfd hs hy, hfd ht hy]
    exact h s hs hst y hy

/-- **The iteration preserves a class for short times.** For `0 < α < 1` and `0 ≤ R`, `0 ≤ N`
there is `T > 0`, depending only on `α`, `R` and `N`, such that for all data
`IsHolderData ω₀ θ₀ α R N` the class `IsIterationClass T α R N` contains the constant history of
the extended vorticity datum and is mapped into itself by `carriedHistory ω₀ θ₀ (-T) T`. -/
theorem exists_mapsTo_isIterationClass (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N →
      IsIterationClass T α R N (fun _ ↦ dataVorticity ω₀) ∧
      ∀ ω, IsIterationClass T α R N ω →
        IsIterationClass T α R N (carriedHistory ω₀ θ₀ (-T) T ω) := by
  obtain ⟨T, hT, h₁, h₂, h₃, h₄⟩ := exists_iterationTime (R := R) hα hN
  exact ⟨T, hT, fun ω₀ θ₀ hd ↦ ⟨isIterationClass_dataVorticity hd hα.le hα1.le,
    fun ω hω ↦ isIterationClass_carriedHistory hd hα hα1 hR hT h₁ h₂ h₃ h₄ hω⟩⟩

/-! ### Outputs for the local theorem -/

/-- The Lipschitz constant in the label of the amplitude for histories of the class. -/
def iterationAmplitudeLipschitz (α R N T : ℝ) : ℝ :=
  N + T * forcingDerivBound N (iterationVariationBound α R N T) (iterationSecondBound α R N T)

/-- **The amplitude is Lipschitz in the label** for histories of the class, on the closed
half-plane and at every time of `[-T, T]`. -/
theorem IsIterationClass.abs_amplitude_sub_le {ω : ℝ → ℝ^2 → ℝ}
    (hω : IsIterationClass T α R N ω) (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α)
    (hα1 : α < 1) (hR : 0 ≤ R) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) {y y' : ℝ^2}
    (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (labelForcing (historyField ω) (historyFieldDeriv ω) (-T) T (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) y t -
      forcedAmplitude (dataVorticity ω₀)
        (labelForcing (historyField ω) (historyFieldDeriv ω) (-T) T (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) y' t| ≤
      iterationAmplitudeLipschitz α R N T * ‖y - y'‖ := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hα hα1 hR hT
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hc₀ := forcingDerivBound_nonneg hN (hb.zero_le_L h0) (hb.zero_le_σ h0)
  refine (hb.abs_amplitude_sub_le hv h0 hd ht hy hy').trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  unfold iterationAmplitudeLipschitz
  gcongr
  exact abs_le_of_mem_Icc_neg ht

/-- The bound of the output data class of the local theorem: the class bound `2 N + 1` and the
bounds of the carried temperature after one step. -/
def iterationOutputBound (α R N T : ℝ) : ℝ :=
  max (2 * N + 1) (max (N * iterationVariationBound α R N T)
    (max (N * iterationSecondBound α R N T + N * iterationVariationBound α R N T ^ 2)
      (N * iterationSecondHolderConst α R N T +
        N * iterationVariationBound α R N T ^ α * iterationVariationBound α R N T ^ 2 +
        max (3 * N * iterationVariationBound α R N T * iterationSecondBound α R N T)
          (2 * (N * iterationSecondBound α R N T +
            N * iterationVariationBound α R N T ^ 2)))))

/-- **The output data class.** For a time `T` as in `exists_iterationTime` and a history `ω` of
the class, the carried vorticity and the carried temperature at every time of `[-T, T]` are data
of the class `IsHolderData` with support radius `R + 1` and bound `iterationOutputBound`. -/
theorem isHolderData_carried (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1)
    (hR : 0 ≤ R) (hT : 0 < T) (h₄ : iterationVelocityBound R N * T ≤ 1)
    {ω : ℝ → ℝ^2 → ℝ} (hω : IsIterationClass T α R N ω)
    (hc : IsIterationClass T α R N (carriedHistory ω₀ θ₀ (-T) T ω)) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    IsHolderData (fun x ↦ carriedVorticity ω₀ θ₀ ω (-T) T x t)
      (fun x ↦ carriedTemperature θ₀ ω (-T) T x t) α (R + 1) (iterationOutputBound α R N T) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hα hα1 hR hT.le
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hθ := IsBoundedFlowOn.contDiff_carriedTemperature hv h0 hd ht
  set B := iterationOutputBound α R N T
  have hB₁ : 2 * N + 1 ≤ B := le_max_left _ _
  have hB₂ : N * iterationVariationBound α R N T ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB₃ : N * iterationSecondBound α R N T + N * iterationVariationBound α R N T ^ 2 ≤ B :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hB₄ : N * iterationSecondHolderConst α R N T +
      N * iterationVariationBound α R N T ^ α * iterationVariationBound α R N T ^ 2 +
      max (3 * N * iterationVariationBound α R N T * iterationSecondBound α R N T)
        (2 * (N * iterationSecondBound α R N T + N * iterationVariationBound α R N T ^ 2)) ≤ B :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine
    { vorticity_contDiffOn := hc.contDiffOn t ht
      temperature_contDiffOn := hθ.contDiffOn
      eq_zero := fun x hx hxR ↦ hb.carried_eq_zero h0 hd ht
        (abs_le_of_mem_Icc_neg ht) hx (by linarith)
      abs_vorticity_le := fun x hx ↦ (hc.abs_le t ht x hx).trans hB₁
      norm_fderivWithin_vorticity_le := fun x hx ↦ (hc.norm_fderivWithin_le t ht x hx).trans hB₁
      holder_vorticity := fun x y hx hy ↦ (hc.holder_fderivWithin t ht x y hx hy).trans
        (mul_le_mul_of_nonneg_right hB₁ (Real.rpow_nonneg (norm_nonneg _) α))
      abs_temperature_le := fun x hx ↦
        (hb.carriedTemperature_bounds hv h0 hd ht hx).1.trans (by linarith [hB₁])
      norm_fderivWithin_temperature_le := fun x hx ↦ by
        rw [fderivWithin_closedUpper_eq (hθ.differentiable two_ne_zero) hx]
        exact (hb.carriedTemperature_bounds hv h0 hd ht hx).2.1.trans hB₂
      norm_fderivWithin_fderivWithin_temperature_le := fun x hx ↦ by
        rw [fderivWithin_fderivWithin_closedUpper_eq hθ hx]
        exact (hb.carriedTemperature_bounds hv h0 hd ht hx).2.2.trans hB₃
      holder_temperature := fun x y hx hy ↦ by
        rw [fderivWithin_fderivWithin_closedUpper_eq hθ hx,
          fderivWithin_fderivWithin_closedUpper_eq hθ hy]
        exact (hb.norm_fderiv_fderiv_carriedTemperature_sub_le hv h0 hd hα.le hα1.le ht hx
          hy).trans (mul_le_mul_of_nonneg_right hB₄ (Real.rpow_nonneg (norm_nonneg _) α)) }

/-- `c + s Φ ≤ |c| + |s| Φ'` for `0 ≤ Φ ≤ Φ'`. -/
theorem add_mul_le_abs_add_abs_mul {c s Φ Φ' : ℝ} (hΦ : 0 ≤ Φ) (hΦ' : Φ ≤ Φ') :
    c + s * Φ ≤ |c| + |s| * Φ' := by
  have h1 : s * Φ ≤ |s| * Φ := mul_le_mul_of_nonneg_right (le_abs_self s) hΦ
  have h2 : |s| * Φ ≤ |s| * Φ' := mul_le_mul_of_nonneg_left hΦ' (abs_nonneg s)
  linarith [le_abs_self c]

end Boussinesq.HalfPlane
