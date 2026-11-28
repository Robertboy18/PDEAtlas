/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.CarriedTemperature
public import PDE.Fluid.Boussinesq.HalfPlane.IterationBounds
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Uniform bounds of the iteration for short times

The local existence proof for a half-plane system with the velocity law `U` and the forcing
coefficient `κ` iterates `ω ↦ carriedHistory U κ ω₀ θ₀ (-T) T ω` on vorticity histories. This module
finds a class of histories that the map keeps for a short time `T`, so that all iterates have the
same support radius and the same `C^{1,α}` bounds. This fixes the time of local existence in terms
of the size of the data and of the constants of the law.

For data `IsHolderData ω₀ θ₀ α R N`, `0 < α < 1`, and a radius `R'` with `R < R' ≤ R₀`, the class of
`C^{1,α}` histories on `[-T, T]` supported in the disc of radius `R'` with all bounds `2 N + 1` (the
Hölder constant of the values `2 (2 N + 1)`) is mapped into itself when `T` is small enough, and
contains the constant history of the extended datum. The time `T` comes from the continuity of the
bounds at `T = 0`; it is not computed.

The flow bounds of the field of a history of the class come from the law and the flow estimates of
`PDE.Analysis.ODE`: with `τ = b - a`, the first variation is at most `exp (K₁ τ)`, the second at
most `secondVariationBound K₁ K₂ τ` and Hölder with constant
`secondVariationHolderConst K₁ K₂ K₂ τ`, where `K₁ = C 0 α (1 + B log (2 + M) + B)` and
`K₂ = C 1 α max B (max B₁ M₁)`. As `τ → 0` these tend to `1`, `0` and `0`, so the bounds of the
carried vorticity tend to the data bounds `N`. The supports move by at most `C 0 0 (2 N + 1) T`,
which is kept below `R' - R`. The area of the support never enters: the field of the law need not be
divergence free.

## Main results

* `isBoundedFlowOn_lawField`: the flow bounds `Boussinesq.HalfPlane.IsBoundedFlowOn` of the field of
  a `C^{1,α}` history on `[a, b]`, with the constants above.
* `lawFieldDeriv_eq`, `lawFieldDeriv₂_eq`, `lawField_normal_eq_zero`, `norm_lawField_le`: on the
  closed half-plane the derivatives of the field of a history are those of the law within the
  half-plane, the field is tangent to the boundary and bounded by `C 0 0 B`.
* `IsIterationClass`: the class of the iteration.
* `exists_iterationTime`: for a margin `d > 0` there is `T > 0` for which one step keeps the values,
  the gradient and its Hölder constant below `2 N + 1` and moves the support by at most `d`.
* `isIterationClass_dataVorticity`: the constant history of the extended datum is in the class.
* `isIterationClass_carriedHistory`: one step of the iteration preserves the class, for a time `T`
  with the four inequalities of `exists_iterationTime` and the margin `R' - R`.
* `IsIterationClass.abs_amplitude_sub_le`: for a history of the class the amplitude is Lipschitz in
  the label with the constant `iterationAmplitudeLipschitz`.
* `isHolderData_carried`: the carried vorticity and the carried temperature at every time of
  `[-T, T]` are data of the class `IsHolderData` with support radius `R'` and the bound
  `iterationOutputBound C α N T`.

`LocalExistence.lean` combines the invariance of the class with the difference estimate of
`Convergence.lean` and obtains a solution on `(-T, T)`; `IterationHigher.lean` repeats the argument
at level `k`. `Maximal.lean` and `Persistence.lean` use the bound `iterationOutputBound` of the
slices of the local solution.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-! ### The flow of the field of a history -/

section Flow

variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M B₁ M₁ : ℝ}

/-- On the closed half-plane the derivative of the field of a history is the derivative within
the closed half-plane of the field of the law. -/
theorem lawFieldDeriv_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    lawFieldDeriv U ω r y = fderivWithin ℝ (U (ω r)) H̄ y :=
  fderiv_extendedField_of_nonneg (K := 2) (by norm_num)
    (hω.contDiffOn_law_two hU hR hα hα1 hr) hy

/-- On the closed half-plane the second derivative of the field of a history is the second
derivative within the closed half-plane of the field of the law. -/
theorem lawFieldDeriv₂_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    lawFieldDeriv₂ U ω r y = fderivWithin ℝ (fderivWithin ℝ (U (ω r)) H̄) H̄ y :=
  fderiv_fderiv_extendedField_of_nonneg (K := 2) le_rfl
    (hω.contDiffOn_law_two hU hR hα hα1 hr) hy

/-- The field of a history is tangent to the boundary line at the times of the history. -/
theorem lawField_normal_eq_zero (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) {r : ℝ} (hr : r ∈ Icc a b)
    {x : ℝ^2} (hx : x 1 = 0) : lawField U ω r x 1 = 0 :=
  extendedField_normal_eq_zero 2 hx (hω.law_normal_eq_zero hU hR hr hx)

/-- On the closed half-plane the field of a history is bounded by `C 0 0 B`. -/
theorem norm_lawField_le (hU : IsVelocityLaw U R₀ C) (hω : IsVorticityHistory ω a b α R B M)
    (hR : R ≤ R₀) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖lawField U ω r y‖ ≤ C 0 0 * B := by
  rw [lawField_of_nonneg U ω r hy]
  exact hω.norm_law_le hU hR hr hy

/-- **The flow bounds of the field of a `C^{1,α}` history** on `[a, b]` under the law `U`, with
`τ = b - a`, `K₁ = C 0 α (1 + B log (2 + M) + B)` and `K₂ = C 1 α max B (max B₁ M₁)`: the field
is bounded by `C 0 0 B`, its flows preserve the closed half-plane, the first variation is at
most `exp (K₁ τ)`, and the second variation is bounded and Hölder with constants that vanish
as `τ → 0`. All bounds of the carried fields are expressed through these constants. Proof: the
Kato bound and the `C²` bound of the law give `K₁` and `K₂`, and the estimates of the
variations of a flow apply to the `C²` field `lawField U ω`. -/
theorem isBoundedFlowOn_lawField (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    (hab : a ≤ b) :
    IsBoundedFlowOn (lawField U ω) (lawFieldDeriv U ω) (lawFieldDeriv₂ U ω) a b α
      (C 0 0 * B) (C 0 α * (1 + B * Real.log (2 + M) + B))
      (Real.exp (C 0 α * (1 + B * Real.log (2 + M) + B) * (b - a)))
      (Real.exp (C 0 α * (1 + B * Real.log (2 + M) + B) * (b - a)) - 1)
      (secondVariationBound (C 0 α * (1 + B * Real.log (2 + M) + B))
        (C 1 α * max B (max B₁ M₁)) (b - a))
      (secondVariationHolderConst (C 0 α * (1 + B * Real.log (2 + M) + B))
        (C 1 α * max B (max B₁ M₁)) (C 1 α * max B (max B₁ M₁)) (b - a)) := by
  have hv := hω.isC2FieldOn_lawField hU hR hα hα1
  have hv1 := hv.toIsC1FieldOn
  set K₁ := C 0 α * (1 + B * Real.log (2 + M) + B)
  set K₂ := C 1 α * max B (max B₁ M₁)
  have hta : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn (lawField U ω) a b s t) H̄ H̄ :=
    fun s hs t ht ↦ hv1.isLipschitzFieldOn.mapsTo_flowOn_nonneg (j := 1)
      (fun r hr x hx ↦ lawField_normal_eq_zero hU hω.toIsVorticityHistory hR hr hx) hs ht
  have hDv : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ‖lawFieldDeriv U ω r y‖ ≤ K₁ := fun r hr y hy ↦ by
    rw [lawFieldDeriv_eq hU hω hR hα hα1 hr hy]
    exact hω.toIsVorticityHistory.norm_fderivWithin_law_le hU hR hα hα1 hr hy
  have hD2v : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ‖lawFieldDeriv₂ U ω r y‖ ≤ K₂ := fun r hr y hy ↦ by
    rw [lawFieldDeriv₂_eq hU hω hR hα hα1 hr hy]
    exact hω.norm_fderivWithin_fderivWithin_law_le hU hR hα hα1 hr hy
  have hD2vH : ∀ r ∈ Icc a b, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖lawFieldDeriv₂ U ω r y - lawFieldDeriv₂ U ω r z‖ ≤ K₂ * ‖y - z‖ ^ α :=
    fun r hr y hy z hz ↦ by
      rw [lawFieldDeriv₂_eq hU hω hR hα hα1 hr hy, lawFieldDeriv₂_eq hU hω hR hα hα1 hr hz]
      exact hω.norm_fderivWithin_fderivWithin_law_sub_le hU hR hα hα1 hr hy hz
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv a hta 0 (by simp))
  have hK₂ : 0 ≤ K₂ :=
    (ContinuousLinearMap.opNorm_nonneg _).trans (hD2v a hta 0 (by simp))
  have hst {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : |s - t| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have he {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
      Real.exp (K₁ * |s - t|) ≤ Real.exp (K₁ * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hst hs ht) hK₁)
  exact
    { mapsTo := hS
      norm_le := fun r hr y hy ↦ norm_lawField_le hU hω.toIsVorticityHistory hR hr hy
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
          PDE.Analysis.convex_closedUpperHalfPlane hS hDv hD2v hα.le hα1.le hK₂ hD2vH hs ht hx
          hy).trans (mul_le_mul_of_nonneg_right
            (secondVariationHolderConst_mono hK₁ hK₂ hK₂ (abs_nonneg _) (hst hs ht))
            (Real.rpow_nonneg (norm_nonneg _) α)) }

end Flow

/-! ### The class of the iteration and the choice of the time -/

/-- The class of the iteration on `[-T, T]` for data of size `N`: `C^{1,α}` histories supported
on the closed half-plane in the disc of radius `R'`, with values, gradients and the Hölder
constant of the gradient at most `2 N + 1` and the Hölder constant of the values at most
`2 (2 N + 1)`. -/
def IsIterationClass (T α R' N : ℝ) (ω : ℝ → ℝ^2 → ℝ) : Prop :=
  IsC1VorticityHistory ω (-T) T α R' (2 * N + 1) (2 * (2 * N + 1)) (2 * N + 1) (2 * N + 1)

/-- The bound `K₁` of the derivative of the field for the class. -/
def iterationKato (C : ℕ → ℝ → ℝ) (α N : ℝ) : ℝ :=
  C 0 α * (1 + (2 * N + 1) * Real.log (2 + 2 * (2 * N + 1)) + (2 * N + 1))

/-- The bound `K₂` of the second derivative of the field for the class. -/
def iterationSecondDeriv (C : ℕ → ℝ → ℝ) (α N : ℝ) : ℝ :=
  C 1 α * max (2 * N + 1) (max (2 * N + 1) (2 * N + 1))

/-- The first-variation bound `exp (K₁ (T - (-T)))` over `[-T, T]` for the class. -/
def iterationVariationBound (C : ℕ → ℝ → ℝ) (α N T : ℝ) : ℝ :=
  Real.exp (iterationKato C α N * (T - -T))

/-- The second-variation bound over `[-T, T]` for the class. -/
def iterationSecondBound (C : ℕ → ℝ → ℝ) (α N T : ℝ) : ℝ :=
  secondVariationBound (iterationKato C α N) (iterationSecondDeriv C α N) (T - -T)

/-- The Hölder constant of the second variation over `[-T, T]` for the class. -/
def iterationSecondHolderConst (C : ℕ → ℝ → ℝ) (α N T : ℝ) : ℝ :=
  secondVariationHolderConst (iterationKato C α N) (iterationSecondDeriv C α N)
    (iterationSecondDeriv C α N) (T - -T)

/-- The velocity bound `C 0 0 (2 N + 1)` of the class. -/
def iterationVelocityBound (C : ℕ → ℝ → ℝ) (N : ℝ) : ℝ :=
  C 0 0 * (2 * N + 1)

/-- The bound of the gradient of the carried vorticity after one step of the iteration. -/
def iterationGradientBound (C : ℕ → ℝ → ℝ) (Bκ : ℕ → ℝ) (α N T : ℝ) : ℝ :=
  (N + T * weightedForcingDerivBound Bκ N (iterationVariationBound C α N T)
      (iterationSecondBound C α N T)) * iterationVariationBound C α N T

/-- The Hölder constant of the gradient of the carried vorticity after one step. -/
def iterationHolderBound (C : ℕ → ℝ → ℝ) (Bκ : ℕ → ℝ) (α N T : ℝ) : ℝ :=
  (N + T * weightedForcingDerivHolderConst Bκ N (iterationVariationBound C α N T)
      (iterationSecondBound C α N T) (iterationSecondHolderConst C α N T)) *
      iterationVariationBound C α N T ^ α * iterationVariationBound C α N T +
    (N + T * weightedForcingDerivBound Bκ N (iterationVariationBound C α N T)
      (iterationSecondBound C α N T)) *
      max (iterationSecondBound C α N T) (2 * (iterationVariationBound C α N T - 1))

/-- The first-variation bound depends continuously on the time. -/
theorem continuous_iterationVariationBound (C : ℕ → ℝ → ℝ) (α N : ℝ) :
    Continuous (iterationVariationBound C α N) := by
  unfold iterationVariationBound; fun_prop

/-- The second-variation bound depends continuously on the time. -/
theorem continuous_iterationSecondBound (C : ℕ → ℝ → ℝ) (α N : ℝ) :
    Continuous (iterationSecondBound C α N) := by
  unfold iterationSecondBound secondVariationBound; fun_prop

/-- The Hölder constant of the second variation depends continuously on the time. -/
theorem continuous_iterationSecondHolderConst (C : ℕ → ℝ → ℝ) (α N : ℝ) :
    Continuous (iterationSecondHolderConst C α N) := by
  unfold iterationSecondHolderConst secondVariationHolderConst secondVariationBound; fun_prop

/-- At time zero the first-variation bound is `1`. -/
theorem iterationVariationBound_zero (C : ℕ → ℝ → ℝ) (α N : ℝ) :
    iterationVariationBound C α N 0 = 1 := by
  simp [iterationVariationBound]

/-- At time zero the second-variation bound is `0`. -/
theorem iterationSecondBound_zero (C : ℕ → ℝ → ℝ) (α N : ℝ) :
    iterationSecondBound C α N 0 = 0 := by
  simp [iterationSecondBound, secondVariationBound]

/-- **The time of the iteration.** For `0 < α`, `0 ≤ N` and a margin `d > 0`, there is `T > 0`
for which one step of the iteration keeps the values, the gradient and its Hölder constant below
`2 N + 1` and moves the support by at most `d`. -/
theorem exists_iterationTime {α N d : ℝ} (C : ℕ → ℝ → ℝ) (Bκ : ℕ → ℝ) (hα : 0 < α)
    (hN : 0 ≤ N) (hd : 0 < d) :
    ∃ T > 0, N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) ≤ 2 * N + 1 ∧
      iterationGradientBound C Bκ α N T ≤ 2 * N + 1 ∧
      iterationHolderBound C Bκ α N T ≤ 2 * N + 1 ∧ iterationVelocityBound C N * T ≤ d := by
  have hL := continuous_iterationVariationBound C α N
  have hσ := continuous_iterationSecondBound C α N
  have hη := continuous_iterationSecondHolderConst C α N
  have hc₀ : Continuous fun T ↦ weightedForcingDerivBound Bκ N (iterationVariationBound C α N T)
      (iterationSecondBound C α N T) := by
    unfold weightedForcingDerivBound forcingDerivBound; fun_prop
  have hcα : Continuous fun T ↦ weightedForcingDerivHolderConst Bκ N
      (iterationVariationBound C α N T) (iterationSecondBound C α N T)
      (iterationSecondHolderConst C α N T) := by
    unfold weightedForcingDerivHolderConst weightedForcingDerivLipschitz weightedForcingDerivBound
      forcingDerivHolderConst forcingDerivBound
    fun_prop
  have hLα : Continuous fun T ↦ iterationVariationBound C α N T ^ α :=
    (Real.continuous_rpow_const hα.le).comp hL
  have h₁ : Continuous fun T ↦
      N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) := by
    unfold weightedForcingBound; fun_prop
  have h₂ : Continuous (iterationGradientBound C Bκ α N) := by
    unfold iterationGradientBound; fun_prop
  have h₃ : Continuous (iterationHolderBound C Bκ α N) := by
    unfold iterationHolderBound
    exact ((continuous_const.add (continuous_id.mul hcα)).mul hLα |>.mul hL).add
      ((continuous_const.add (continuous_id.mul hc₀)).mul
        (hσ.max (continuous_const.mul (hL.sub continuous_const))))
  have h₄ : Continuous fun T ↦ iterationVelocityBound C N * T := by fun_prop
  have hlt : N < 2 * N + 1 := by linarith
  have e₁ : ∀ᶠ T in 𝓝 0, N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) <
      2 * N + 1 :=
    h₁.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
  have e₂ : ∀ᶠ T in 𝓝 0, iterationGradientBound C Bκ α N T < 2 * N + 1 :=
    h₂.continuousAt.eventually_lt continuousAt_const (by
      simpa [iterationGradientBound, iterationVariationBound_zero] using hlt)
  have e₃ : ∀ᶠ T in 𝓝 0, iterationHolderBound C Bκ α N T < 2 * N + 1 :=
    h₃.continuousAt.eventually_lt continuousAt_const (by
      simpa [iterationHolderBound, iterationVariationBound_zero, iterationSecondBound_zero]
        using hlt)
  have e₄ : ∀ᶠ T in 𝓝 0, iterationVelocityBound C N * T < d :=
    h₄.continuousAt.eventually_lt continuousAt_const (by simpa using hd)
  have hev : ∀ᶠ T in 𝓝[>] (0 : ℝ), T ∈ Ioi 0 ∧
      (N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) < 2 * N + 1 ∧
        iterationGradientBound C Bκ α N T < 2 * N + 1 ∧
        iterationHolderBound C Bκ α N T < 2 * N + 1 ∧ iterationVelocityBound C N * T < d) :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (e₁.and (e₂.and (e₃.and e₄))))
  obtain ⟨T, hT, h1, h2, h3, h4⟩ := hev.exists
  exact ⟨T, hT, h1.le, h2.le, h3.le, h4.le⟩

/-! ### The invariance of the class -/

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R R' N T : ℝ}

/-- The fields of the histories of the class are `C²` fields. -/
theorem IsIterationClass.isC2FieldOn {ω : ℝ → ℝ^2 → ℝ} (hω : IsIterationClass T α R' N ω)
    (hU : IsVelocityLaw U R₀ C) (hR' : R' ≤ R₀) (hα : 0 < α) (hα1 : α < 1) :
    IsC2FieldOn (lawField U ω) (lawFieldDeriv U ω) (lawFieldDeriv₂ U ω) (-T) T
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 * iterationKato C α N))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 * iterationSecondDeriv C α N)) :=
  IsC1VorticityHistory.isC2FieldOn_lawField hU hω hR' hα hα1

/-- The flow bounds of the field of a history of the class. -/
theorem IsIterationClass.isBoundedFlowOn {ω : ℝ → ℝ^2 → ℝ} (hω : IsIterationClass T α R' N ω)
    (hU : IsVelocityLaw U R₀ C) (hR' : R' ≤ R₀) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    IsBoundedFlowOn (lawField U ω) (lawFieldDeriv U ω) (lawFieldDeriv₂ U ω) (-T) T α
      (iterationVelocityBound C N) (iterationKato C α N) (iterationVariationBound C α N T)
      (iterationVariationBound C α N T - 1) (iterationSecondBound C α N T)
      (iterationSecondHolderConst C α N T) :=
  isBoundedFlowOn_lawField hU hω hR' hα hα1 (by linarith)

/-- The constant history of the extended vorticity datum is in the class of the iteration when
the support radius `R` of the data is at most `R'`. -/
theorem isIterationClass_dataVorticity (hd : IsHolderData ω₀ θ₀ α R N) (hRR' : R ≤ R')
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : IsIterationClass T α R' N (fun _ ↦ dataVorticity ω₀) := by
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
`exists_iterationTime` with the margin `R' - R`. So all iterates have the same support radius
and the same `C^{1,α}` bounds. Proof: the bounds of the carried vorticity, of its gradient and
of the Hölder constant of the gradient are the left sides of the hypotheses, the support moves
by at most the velocity bound times `T`, and the continuity in time is that of the carried
vorticity. -/
theorem isIterationClass_carriedHistory (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α)
    (hα1 : α < 1) (hR' : R' ≤ R₀) (hT : 0 < T)
    (h₁ : N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) ≤ 2 * N + 1)
    (h₂ : iterationGradientBound C Bκ α N T ≤ 2 * N + 1)
    (h₃ : iterationHolderBound C Bκ α N T ≤ 2 * N + 1)
    (h₄ : iterationVelocityBound C N * T ≤ R' - R) {ω : ℝ → ℝ^2 → ℝ}
    (hω : IsIterationClass T α R' N ω) :
    IsIterationClass T α R' N (carriedHistory U κ ω₀ θ₀ (-T) T ω) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hU hR' hα hα1 hT.le
  have hv := hω.isC2FieldOn hU hR' hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := weightedForcingDerivBound_nonneg hκ hN hL0 hσ0
  have hcα := weightedForcingDerivHolderConst_nonneg hκ hN hL0 hσ0 (hb.zero_le_η h0)
  have hwB := weightedForcingBound_nonneg hκ hN hL0
  set N₁ := 2 * N + 1
  have hfd {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      fderivWithin ℝ (carriedHistory U κ ω₀ θ₀ (-T) T ω t) H̄ y =
        fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T z t)
          y :=
    fderivWithin_carriedVorticity hv h0 hd hκ ht hy
  have hgrad {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      ‖fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T z t)
        y‖ ≤ N₁ := by
    refine (norm_fderiv_carriedVorticity_le hb hv h0 hd hκ ht hy).trans (le_trans ?_ h₂)
    unfold iterationGradientBound
    gcongr
    exact abs_le_of_mem_Icc_neg ht
  have hLip {t : ℝ} (ht : t ∈ Icc (-T) T) : ∀ x ∈ H̄, ∀ y ∈ H̄,
      ‖carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t -
        carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T y t‖ ≤
        N₁ * dist x y := fun x hx y hy ↦ by
    rw [dist_eq_norm]
    exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ ↦ (hasFDerivAt_carriedVorticity hv h0 hd hκ ht z).differentiableAt
        |>.hasFDerivAt.hasFDerivWithinAt) (fun z hz ↦ hgrad ht hz) hy hx
  have habs {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
      |carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T y t| ≤ N₁ := by
    refine (abs_carriedVorticity_le hb h0 hd hκ ht hy).trans (le_trans ?_ h₁)
    gcongr
    exact abs_le_of_mem_Icc_neg ht
  refine
    { continuousOn := fun t ht ↦ (contDiff_carriedVorticity hv h0 hd hκ ht).continuous.continuousOn
      eq_zero := fun t ht y hy hyR ↦ ?_
      abs_le := fun t ht y hy ↦ habs ht hy
      holder := fun t ht y z hy hz ↦ ?_
      uniform := fun t ht ε hε ↦ exists_abs_carriedVorticity_sub_le hb hv h0 hd hκ ht hε
      contDiffOn := fun t ht ↦ (contDiff_carriedVorticity hv h0 hd hκ ht).contDiffOn
      norm_fderivWithin_le := fun t ht y hy ↦ by rw [hfd ht hy]; exact hgrad ht hy
      holder_fderivWithin := fun t ht y z hy hz ↦ ?_
      uniform_fderivWithin := fun t ht ε hε ↦ ?_ }
  · exact (carried_eq_zero hb h0 hd ht (abs_le_of_mem_Icc_neg ht) hy
      (by linarith)).1
  · have h := PDE.Analysis.norm_sub_le_max_mul_rpow
      (f := fun x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t)
      (S := H̄) (hLip ht) (fun x hx ↦ by rw [Real.norm_eq_abs]; exact habs ht hx) hα.le hα1.le
      hy hz
    rw [Real.norm_eq_abs, dist_eq_norm, max_eq_right (by linarith)] at h
    exact h
  · rw [hfd ht hy, hfd ht hz]
    refine (norm_fderiv_carriedVorticity_sub_le hb hv h0 hd hκ hα.le hα1.le ht hy hz).trans
      (mul_le_mul_of_nonneg_right (le_trans ?_ h₃) (Real.rpow_nonneg (norm_nonneg _) α))
    have htT := abs_le_of_mem_Icc_neg ht
    unfold iterationHolderBound
    gcongr
  · obtain ⟨δ', hδ', h⟩ :=
      exists_norm_fderiv_carriedVorticity_sub_le hb hv h0 hd hκ hα hα1.le ht hε
    refine ⟨δ', hδ', fun s hs hst y hy ↦ ?_⟩
    rw [hfd hs hy, hfd ht hy]
    exact h s hs hst y hy

/-! ### Outputs for the local theorem -/

/-- The Lipschitz constant in the label of the amplitude for histories of the class. -/
def iterationAmplitudeLipschitz (C : ℕ → ℝ → ℝ) (Bκ : ℕ → ℝ) (α N T : ℝ) : ℝ :=
  N + T * weightedForcingDerivBound Bκ N (iterationVariationBound C α N T)
    (iterationSecondBound C α N T)

/-- **The amplitude is Lipschitz in the label** for histories of the class, on the closed
half-plane and at every time of `[-T, T]`. -/
theorem IsIterationClass.abs_amplitude_sub_le {ω : ℝ → ℝ^2 → ℝ}
    (hω : IsIterationClass T α R' N ω) (hU : IsVelocityLaw U R₀ C) (hR' : R' ≤ R₀)
    (hκ : IsForcingCoefficient κ Bκ) (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) {y y' : ℝ^2}
    (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (weightedForcing (lawField U ω) (lawFieldDeriv U ω) (-T) T κ (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) y t -
      forcedAmplitude (dataVorticity ω₀)
        (weightedForcing (lawField U ω) (lawFieldDeriv U ω) (-T) T κ (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) y' t| ≤
      iterationAmplitudeLipschitz C Bκ α N T * ‖y - y'‖ := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hU hR' hα hα1 hT
  have hv := hω.isC2FieldOn hU hR' hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hc₀ := weightedForcingDerivBound_nonneg hκ hN (hb.zero_le_L h0) (hb.zero_le_σ h0)
  refine (hb.abs_weightedAmplitude_sub_le hv h0 hd hκ ht hy hy').trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  unfold iterationAmplitudeLipschitz
  gcongr
  exact abs_le_of_mem_Icc_neg ht

/-- The bound of the output data class of the local theorem: the class bound `2 N + 1` and the
bounds of the carried temperature after one step. -/
def iterationOutputBound (C : ℕ → ℝ → ℝ) (α N T : ℝ) : ℝ :=
  max (2 * N + 1) (max (N * iterationVariationBound C α N T)
    (max (N * iterationSecondBound C α N T + N * iterationVariationBound C α N T ^ 2)
      (N * iterationSecondHolderConst C α N T +
        N * iterationVariationBound C α N T ^ α * iterationVariationBound C α N T ^ 2 +
        max (3 * N * iterationVariationBound C α N T * iterationSecondBound C α N T)
          (2 * (N * iterationSecondBound C α N T +
            N * iterationVariationBound C α N T ^ 2)))))

/-- **The output data class.** For a time `T` with `C 0 0 (2 N + 1) T ≤ R' - R` and a history
`ω` of the class whose image is in the class, the carried vorticity and the carried temperature
at every time of `[-T, T]` are data of the class `IsHolderData` with support radius `R'` and
bound `iterationOutputBound C α N T`. -/
theorem isHolderData_carried (hU : IsVelocityLaw U R₀ C) (hd : IsHolderData ω₀ θ₀ α R N)
    (hα : 0 < α) (hα1 : α < 1) (hR' : R' ≤ R₀) (hT : 0 < T)
    (h₄ : iterationVelocityBound C N * T ≤ R' - R) {ω : ℝ → ℝ^2 → ℝ}
    (hω : IsIterationClass T α R' N ω)
    (hc : IsIterationClass T α R' N (carriedHistory U κ ω₀ θ₀ (-T) T ω)) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    IsHolderData (fun x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t)
      (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x t) α R'
      (iterationOutputBound C α N T) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hb := hω.isBoundedFlowOn hU hR' hα hα1 hT.le
  have hv := hω.isC2FieldOn hU hR' hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hθ := contDiff_carriedTemperature hv h0 hd ht
  set B := iterationOutputBound C α N T
  have hB₁ : 2 * N + 1 ≤ B := le_max_left _ _
  have hB₂ : N * iterationVariationBound C α N T ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB₃ : N * iterationSecondBound C α N T + N * iterationVariationBound C α N T ^ 2 ≤ B :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hB₄ : N * iterationSecondHolderConst C α N T +
      N * iterationVariationBound C α N T ^ α * iterationVariationBound C α N T ^ 2 +
      max (3 * N * iterationVariationBound C α N T * iterationSecondBound C α N T)
        (2 * (N * iterationSecondBound C α N T + N * iterationVariationBound C α N T ^ 2)) ≤
      B :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine
    { vorticity_contDiffOn := hc.contDiffOn t ht
      temperature_contDiffOn := hθ.contDiffOn
      eq_zero := fun x hx hxR ↦ carried_eq_zero hb h0 hd ht
        (abs_le_of_mem_Icc_neg ht) hx (by linarith)
      abs_vorticity_le := fun x hx ↦ (hc.abs_le t ht x hx).trans hB₁
      norm_fderivWithin_vorticity_le := fun x hx ↦ (hc.norm_fderivWithin_le t ht x hx).trans hB₁
      holder_vorticity := fun x y hx hy ↦ (hc.holder_fderivWithin t ht x y hx hy).trans
        (mul_le_mul_of_nonneg_right hB₁ (Real.rpow_nonneg (norm_nonneg _) α))
      abs_temperature_le := fun x hx ↦
        (carriedTemperature_bounds hb hv h0 hd ht hx).1.trans (by linarith [hB₁])
      norm_fderivWithin_temperature_le := fun x hx ↦ by
        rw [fderivWithin_closedUpper_eq (hθ.differentiable two_ne_zero) hx]
        exact (carriedTemperature_bounds hb hv h0 hd ht hx).2.1.trans hB₂
      norm_fderivWithin_fderivWithin_temperature_le := fun x hx ↦ by
        rw [fderivWithin_fderivWithin_closedUpper_eq hθ hx]
        exact (carriedTemperature_bounds hb hv h0 hd ht hx).2.2.trans hB₃
      holder_temperature := fun x y hx hy ↦ by
        rw [fderivWithin_fderivWithin_closedUpper_eq hθ hx,
          fderivWithin_fderivWithin_closedUpper_eq hθ hy]
        exact (norm_fderiv_fderiv_carriedTemperature_sub_le hb hv h0 hd hα.le hα1.le ht hx
          hy).trans (mul_le_mul_of_nonneg_right hB₄ (Real.rpow_nonneg (norm_nonneg _) α)) }

end HalfPlaneSystem
