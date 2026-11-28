/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APrioriEstimate
public import PDE.Fluid.HalfPlaneSystem.Maximal

/-!
# The continuation criterion for a half-plane system

A solution of a half-plane system with Hölder data exists on a maximal interval of times. This
module proves the continuation criterion: if the interval is finite and the supports stay in a
common disc, the time integral of the sup norms of the velocity gradient and of the temperature
gradient is infinite.

For a velocity law `U` up to the radius `R₀` with the bounds `IsVelocityLaw` and the Schauder
estimate `IsHolderVelocityLaw U R₀ Ch`, a forcing coefficient `κ`, `0 < α < 1` and data
`ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` of the class `IsHolderData … α R N` with support radius `R < R₀`, the
regular solution on the maximal life span `[0, T*)` (`exists_maximal`) satisfies: if `T* < ∞` and
the supports on `[0, T*)` lie in a common disc of radius less than `R₀`, then
`∫₀^{T*} (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt = ∞`, with the sup norms over the closed half-plane
(`continuationIntegral`). If the integral were finite, the velocity gradient `A(t)`, the supremum
over the closed half-plane of the derivative of the velocity, would have finite integral `Λ` on
every `[0, t₁] ⊂ [0, T*)`; the a priori estimate `exists_holderData_bound` bounds all slices in the
data class by constants depending only on the data, `Λ` and `T*`, and with the common support disc
this contradicts the blow-up alternative `not_forall_isHolderData`.

The support condition cannot be dropped in this generality: the law is only assumed to act on data
supported in the disc of radius `R₀`, and the solution class asks the supports to stay in a disc of
radius less than `R₀`. When they leave it, nothing is claimed. The theorem does not say which of the
two gradients has an infinite integral. For the Biot-Savart law the library has the criterion
without the support condition (`Boussinesq.HalfPlane.continuationIntegral_eq_top`).

## Main results

* `continuationIntegral`: the continuation quantity `∫₀^T (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt`, as an
  extended nonnegative number.
* `velocityGradientSup`, `velocityGradientSup_spec`: the supremum of the velocity gradient over the
  closed half-plane at a time; on a compact interval on which the vorticity is a vorticity history
  it bounds the gradient, it is continuous in time, and it is at most the velocity part of the
  integrand of the continuation quantity.
* `continuationIntegral_eq_top`: the criterion for the maximal solution.

`exists_maximalSolutionOf` (`PersistenceMaximal.lean`) states the criterion together with existence,
uniqueness and the propagation of regularity.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open IncompressibleFlow Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The continuation quantity `∫₀^T (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt`, with `u(t) = U (ω t)` and the
sup norms of the derivatives within the closed half-plane over the closed half-plane. -/
def continuationIntegral (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (sol : Fields) (T : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in lifeSpan T,
    (⨆ x ∈ H̄, ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ₑ) +
      ⨆ x ∈ H̄, ‖fderivWithin ℝ (fun y ↦ sol.temperature y t) H̄ x‖ₑ

/-- The supremum over the closed half-plane of the derivative within it of the velocity of the
vorticity slice at time `t`. -/
def velocityGradientSup (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (sol : Fields) (t : ℝ) : ℝ :=
  sSup ((fun x ↦ ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖) '' H̄)

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ} {sol : Fields} {α : ℝ}

/-- On a compact interval of times on which the vorticity is a vorticity history, the velocity
gradient supremum is a bound, it is continuous, and it is bounded by the velocity part of the
continuation quantity. -/
theorem velocityGradientSup_spec (hU : IsVelocityLaw U R₀ C) {a b R B M : ℝ}
    (hω : IsVorticityHistory (fun s x ↦ sol.vorticity x s) a b α R B M) (hR : R ≤ R₀)
    (hα : 0 < α) (hα1 : α < 1) :
    (∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ ≤ velocityGradientSup U sol t) ∧
    ContinuousOn (velocityGradientSup U sol) (Icc a b) ∧
    ∀ t ∈ Icc a b, 0 ≤ velocityGradientSup U sol t ∧
      ENNReal.ofReal (velocityGradientSup U sol t) ≤
        ⨆ x ∈ H̄, ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ₑ := by
  set D : ℝ → ℝ^2 → ℝ := fun t x ↦ ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖
  have hne : (H̄).Nonempty := ⟨0, by simp⟩
  have hbdd (t : ℝ) (ht : t ∈ Icc a b) : BddAbove (D t '' H̄) :=
    ⟨_, by rintro _ ⟨x, hx, rfl⟩; exact hω.norm_fderivWithin_law_le hU hR hα hα1 ht hx⟩
  have hle (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      D t x ≤ velocityGradientSup U sol t :=
    le_csSup (hbdd t ht) ⟨x, hx, rfl⟩
  have hnn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ velocityGradientSup U sol t :=
    (norm_nonneg _).trans (hle t ht (x := 0) (by simp))
  refine ⟨fun t ht x hx ↦ hle t ht hx, ?_, fun t ht ↦ ⟨hnn t ht, ?_⟩⟩
  · refine Metric.continuousOn_iff.mpr fun t ht ε hε ↦ ?_
    obtain ⟨δ, hδ, hδε⟩ := hω.exists_norm_fderivWithin_law_sub_le hU hR hα hα1 ht (half_pos hε)
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    rw [Real.dist_eq] at hst ⊢
    have h1 : velocityGradientSup U sol s ≤ velocityGradientSup U sol t + ε / 2 := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := hδε s hs hst x hx
      have h2 := norm_sub_norm_le
        (fderivWithin ℝ (U (fun y ↦ sol.vorticity y s)) H̄ x)
        (fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x)
      have h3 := hle t ht hx
      simp only [D] at h3 ⊢
      linarith
    have h2 : velocityGradientSup U sol t ≤ velocityGradientSup U sol s + ε / 2 := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := hδε s hs hst x hx
      have h2 := norm_sub_norm_le
        (fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x)
        (fderivWithin ℝ (U (fun y ↦ sol.vorticity y s)) H̄ x)
      rw [norm_sub_rev] at h2
      have h3 := hle s hs hx
      simp only [D] at h3 ⊢
      linarith
    rw [abs_lt]
    constructor <;> linarith
  · set S := ⨆ x ∈ H̄, ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ₑ
    by_cases hS : S = ⊤
    · rw [hS]; exact le_top
    rw [ENNReal.ofReal_le_iff_le_toReal hS]
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have := le_iSup₂ (f := fun x (_ : x ∈ H̄) ↦
      ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ₑ) x hx
    rw [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal hS] at this
    exact this

/-- **The continuation criterion.** If the maximal time of data of the class with support radius
`R < R₀` is finite and the supports of the maximal solution on `[0, maximalTime)` lie in a common
disc of radius less than `R₀`, the continuation quantity of the maximal solution is infinite. So
a solution can be continued as long as the gradients of the velocity and of the temperature are
integrable in time and the support stays in the domain of the law. Proof: if the quantity were
finite, the a priori estimate `exists_holderData_bound` would keep all slices in one class of
data up to the maximal time, against the blow-up alternative `not_forall_isHolderData`. -/
theorem continuationIntegral_eq_top (hU : IsVelocityLaw U R₀ C)
    (hUh : IsHolderVelocityLaw U R₀ Ch) (hκ : IsForcingCoefficient κ Bκ) {ω₀ θ₀ : ℝ^2 → ℝ}
    {R N : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : R < R₀) (hdata : IsHolderData ω₀ θ₀ α R N)
    (hT : maximalTime U κ R₀ α ω₀ θ₀ ≠ ⊤)
    (hsol : IsRegularSolutionOn U κ R₀ sol (lifeSpan (maximalTime U κ R₀ α ω₀ θ₀)) α)
    (hd : HasDataAt sol 0 ω₀ θ₀)
    (hsupp : ∃ R' < R₀, ∀ t ∈ lifeSpan (maximalTime U κ R₀ α ω₀ θ₀), ∀ x : ℝ^2, 0 ≤ x 1 →
      R' < ‖x‖ → sol.vorticity x t = 0 ∧ sol.temperature x t = 0) :
    continuationIntegral U sol (maximalTime U κ R₀ α ω₀ θ₀) = ⊤ := by
  by_contra hfin
  obtain ⟨R', hR', hz⟩ := hsupp
  set Tstar := maximalTime U κ R₀ α ω₀ θ₀
  set T := Tstar.toReal
  have hpos : 0 < Tstar := maximalTime_pos hU hκ hα hα1 hR hdata
  have hTpos : 0 < T := ENNReal.toReal_pos hpos.ne' hT
  have hspan : lifeSpan Tstar = Ico 0 T := lifeSpan_of_ne_top hT
  set Λ := (continuationIntegral U sol Tstar).toReal
  obtain ⟨R'', N', hb⟩ := exists_holderData_bound hU hUh hκ hα hα1 R N Λ T
  have hd₀ : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N :=
    hdata.congr (fun x hx ↦ (hd x hx).1) (fun x hx ↦ (hd x hx).2)
  -- It is enough to bound every slice in the class with the constants of the a priori estimate.
  apply not_forall_isHolderData hU hκ hα hα1 hR hdata (lt_top_iff_ne_top.mpr hT) hsol hd hR' N'
  intro t ht
  have ht' := ht
  rw [hspan] at ht'
  set t₁ := (t + T) / 2
  have ht₁ : 0 < t₁ := by simp only [t₁]; linarith [ht'.1]
  have ht₁T : t₁ < T := by simp only [t₁]; linarith [ht'.2]
  have hsub : Icc 0 t₁ ⊆ lifeSpan Tstar := by
    rw [hspan]; exact fun r hr ↦ ⟨hr.1, hr.2.trans_lt ht₁T⟩
  have h := hsol.toIsSolutionOn
  obtain ⟨Rω, hRω, Bω, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) ht₁ hsub (by norm_num) (by norm_num)
  obtain ⟨hA, hAc, hAle⟩ :=
    velocityGradientSup_spec hU hω hRω.le (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  -- On `[0, t₁]`, `t < t₁ < T*`, the integral of the supremum of the velocity gradient is at
  -- most the continuation quantity `Λ`.
  have hint : ∫ r in (0)..t₁, velocityGradientSup U sol r ≤ Λ := by
    rw [intervalIntegral.integral_of_le ht₁.le]
    have hmeas : AEStronglyMeasurable (velocityGradientSup U sol)
        (volume.restrict (Ioc 0 t₁)) :=
      (hAc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      fun r hr ↦ (hAle r (Ioc_subset_Icc_self hr)).1) hmeas]
    refine ENNReal.toReal_mono hfin ?_
    calc ∫⁻ r in Ioc 0 t₁, ENNReal.ofReal (velocityGradientSup U sol r)
        ≤ ∫⁻ r in Ioc 0 t₁,
            ((⨆ x ∈ H̄, ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y r)) H̄ x‖ₑ) +
              ⨆ x ∈ H̄, ‖fderivWithin ℝ (fun y ↦ sol.temperature y r) H̄ x‖ₑ) :=
          setLIntegral_mono' measurableSet_Ioc fun r hr ↦
            (hAle r (Ioc_subset_Icc_self hr)).2.trans le_self_add
      _ ≤ continuationIntegral U sol Tstar :=
          lintegral_mono_set fun r hr ↦ hsub (Ioc_subset_Icc_self hr)
  -- The a priori estimate on `[0, t₁]`, and the common support disc.
  have hbt := hb sol (lifeSpan Tstar) (velocityGradientSup U sol) hsol t₁ ht₁ ht₁T.le hsub hd₀
    (fun r hr x hx ↦ hA r hr x hx) hAc hint t ⟨ht'.1, by simp only [t₁]; linarith [ht'.2]⟩
  exact { hbt with eq_zero := fun x hx hxR ↦ hz t ht x hx hxR }

end HalfPlaneSystem
