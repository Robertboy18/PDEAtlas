/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Persistence

/-!
# Well-posedness at level `k` for half-plane systems

This module states the result of the whole folder as one theorem: the half-plane system with a
general velocity law is locally well posed for data with `k ≥ 2` derivatives and a Hölder condition,
with one solution on a maximal interval of times, in the class of the data, and a criterion for the
end of this interval.

For a velocity law `U` up to the radius `R₀` with the bounds `IsVelocityLaw` and the Schauder
estimate `IsHolderVelocityLaw` and a coefficient satisfying `IsForcingCoefficient`, assume
`0 < α < 1` and take data `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` within the closed half-plane,
vanishing there outside a disc of radius `R < R₀`. There is a regular solution of order `k` on the
maximal life span of the local theory (`exists_maximalSolutionOf`). The maximal solution at level
one is regular of order `k` by persistence; its representative of order `k` gives global
`C^k × C^{k+1}` slices with compact support and jointly continuous spatial jets. The blow-up
alternative, the continuation criterion with the support alternative, maximality and uniqueness
are those of the local theory at level one (`exists_maximal`, `not_forall_isHolderData`,
`continuationIntegral_eq_top`, `le_maximalTime`, `IsSolutionOn.eq_of_hasDataAt_lifeSpan`).

## Main results

* `exists_maximalSolutionOf`: local well-posedness at level `k ≥ 2`. There are a life span
  `T ∈ (0, ∞]` and a regular solution of order `k` on `[0, T)` with the data such that: if `T < ∞`,
  the slices stay in no class `IsHolderData α R' N'` with `R' < R₀`; if `T < ∞` and the supports
  stay in a disc of radius less than `R₀`, the continuation integral is infinite; no regular
  solution with the data lives longer; every solution with the data agrees with it on the closed
  half-plane on the common life span; its slices are globally `C^k` and `C^{k+1}` with compact
  support and Hölder top derivatives; and its spatial derivatives of orders at most `k` and `k + 1`
  are continuous on `ℝ² × [0, T)`.

The life span `T` is not estimated from below. At the regularity `C^{1,α} × C^{2,α}` the statements
are `exists_maximal` and `continuationIntegral_eq_top`.

The half-plane Biot-Savart law with the coefficient `1` is an instance of the hypotheses
(`exists_maximalSolutionOf_halfPlaneVelocity` in `BoussinesqInstance.lean`). The library also proves
the theorem for that law directly (`Boussinesq.HalfPlane.exists_maximalSolutionOf`); no theorem
derives one of the two from the other. In BlowupZoo, `wallWellPosedness`, the local theory of the
Euler equations near the wall of the cylinder, is proved from this theorem for the velocity law of
the wall and the coefficient `r⁻⁴`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology
open Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ} {α : ℝ}

/-- **Local well-posedness at level `k`.** Let `U` be a velocity law up to the radius `R₀` with
the Schauder estimate `IsHolderVelocityLaw` and `κ` a forcing coefficient. For data
`ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` within the closed half-plane, vanishing there outside the disc of
radius `R < R₀` (`IsHolderDataOf k`), `k ≥ 2`, `0 < α < 1`, there are a life span `T ∈ (0, ∞]` and
a regular solution of order `k` on `[0, T)` with these data, such that:
* if `T < ∞`, for no radius `R' < R₀` and no bound `N'` are all slices data of the class
  `IsHolderData α R' N'` (the norms are unbounded or the supports reach the radius `R₀`);
* if `T < ∞` and the supports lie in a common disc of radius less than `R₀`, then
  `∫₀^T (‖∇u‖_∞ + ‖∇θ‖_∞) = ∞`;
* no regular solution with these data lives longer;
* every solution in the class `IsSolutionOn` from the same data on a life span `T'` agrees with it
  on the closed half-plane up to `min T T'`;
* its slices are globally `C^k` and `C^{k+1}` with compact support, and on every compact interval
  of times the derivatives of orders `k` and `k + 1` are `α`-Hölder on the plane with one constant;
* the spatial derivatives of order at most `k` of the vorticity and at most `k + 1` of the
  temperature are continuous on `ℝ² × [0, T)`.

This is the theorem that a system with a velocity law is locally well posed; the local theory
of the Euler equations near the wall of a cylinder is an instance, proved in BlowupZoo. Proof:
the maximal solution of the local theory is regular of order `k` by persistence, and its
representative of order `k` has the global regularity; the alternatives, maximality and
uniqueness are those of the local theory. -/
theorem exists_maximalSolutionOf (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
    (hκ : IsForcingCoefficient κ Bκ) {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hk : 2 ≤ k)
    (hα : 0 < α) (hα1 : α < 1) (hR : R < R₀) (hdata : IsHolderDataOf k ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (sol : Fields), 0 < T ∧
      IsRegularSolutionOfOn U κ R₀ k sol (lifeSpan T) α ∧ HasDataAt sol 0 ω₀ θ₀ ∧
      (T ≠ ⊤ → ∀ R' < R₀, ∀ N' : ℝ, ¬ ∀ t ∈ lifeSpan T,
        IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N') ∧
      (T ≠ ⊤ → (∃ R' < R₀, ∀ t ∈ lifeSpan T, ∀ x : ℝ^2, 0 ≤ x 1 → R' < ‖x‖ →
        sol.vorticity x t = 0 ∧ sol.temperature x t = 0) → continuationIntegral U sol T = ⊤) ∧
      (∀ (T' : ℝ≥0∞) (sol' : Fields), IsRegularSolutionOn U κ R₀ sol' (lifeSpan T') α →
        HasDataAt sol' 0 ω₀ θ₀ → T' ≤ T) ∧
      (∀ (T' : ℝ≥0∞) (sol' : Fields), IsSolutionOn U κ R₀ sol' (lifeSpan T') →
        HasDataAt sol' 0 ω₀ θ₀ → ∀ t ∈ lifeSpan (min T T'), ∀ x : ℝ^2, 0 ≤ x 1 →
          sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t) ∧
      (∀ t ∈ lifeSpan T, ContDiff ℝ k (fun x ↦ sol.vorticity x t) ∧
        ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ sol.temperature x t) ∧
        HasCompactSupport (fun x ↦ sol.vorticity x t) ∧
        HasCompactSupport (fun x ↦ sol.temperature x t)) ∧
      (∀ a b : ℝ, Icc a b ⊆ lifeSpan T → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x x' : ℝ^2,
        ‖iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x -
            iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x'‖ ≤ C * ‖x - x'‖ ^ α ∧
          ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x -
            iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x'‖ ≤ C * ‖x - x'‖ ^ α) ∧
      (∀ j ≤ k, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.vorticity y p.2) p.1)
        (univ ×ˢ lifeSpan T)) ∧
      (∀ j ≤ k + 1, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.temperature y p.2) p.1)
        (univ ×ˢ lifeSpan T)) := by
  have hk1 : 1 ≤ k := by omega
  have hd1 : IsHolderData ω₀ θ₀ α R (2 * N) := hdata.toIsHolderData hk1 hα.le hα1.le
  -- The maximal solution of the local theory for the data, read in the class of that theory.
  obtain ⟨sol₀, hsol₀, hd₀⟩ := exists_maximal hU hκ hα hα1 hR hd1
  set T := maximalTime U κ R₀ α ω₀ θ₀
  -- It is regular of order `k` by persistence, and so is its representative of order `k`.
  have hreg₀ : IsRegularSolutionOfOn U κ R₀ k sol₀ (lifeSpan T) α :=
    hsol₀.isRegularSolutionOfOn hU hκ hk hα hα1
      (hdata.congr (fun x hx ↦ (hd₀ x hx).1) fun x hx ↦ (hd₀ x hx).2)
  have hreg : IsRegularSolutionOfOn U κ R₀ k (canonicalOf k sol₀) (lifeSpan T) α :=
    hreg₀.canonicalOf hU hk1 (uniqueDiffOn_lifeSpan T)
  have hregL : IsRegularSolutionOn U κ R₀ (canonicalOf k sol₀) (lifeSpan T) α :=
    hreg.toIsRegularSolutionOn hk1 hα.le hα1.le
  have hd : HasDataAt (canonicalOf k sol₀) 0 ω₀ θ₀ := fun x hx ↦ by
    rw [canonicalOf_vorticity_of_nonneg hx, canonicalOf_temperature_of_nonneg hx]
    exact hd₀ x hx
  have hswap {F : Type} [TopologicalSpace F] {G : ℝ × ℝ^2 → F}
      (hG : ContinuousOn G (lifeSpan T ×ˢ univ)) :
      ContinuousOn (fun p : ℝ^2 × ℝ ↦ G (p.2, p.1)) (univ ×ˢ lifeSpan T) :=
    hG.comp continuous_swap.continuousOn fun p hp ↦ ⟨hp.2, mem_univ _⟩
  -- The two alternatives, maximality and uniqueness are those of the local theory; the last
  -- four items are the regularity of the representative.
  refine ⟨T, canonicalOf k sol₀, maximalTime_pos hU hκ hα hα1 hR hd1, hreg, hd,
    fun hT R' hR' N' ↦ not_forall_isHolderData hU hκ hα hα1 hR hd1 (lt_top_iff_ne_top.mpr hT)
      hregL hd hR' N',
    fun hT hsupp ↦ continuationIntegral_eq_top hU hUh hκ hα hα1 hR hd1 hT hregL hd hsupp,
    fun T' sol' h' hd' ↦ le_maximalTime h' hd',
    fun T' sol' h' hd' t ht x hx ↦
      hreg.toIsSolutionOn.eq_of_hasDataAt_lifeSpan hU hκ h' hd hd' ht hx,
    fun t ht ↦ ?_, fun a b hab ↦ ?_,
    fun j hj ↦ hswap (G := fun p : ℝ × ℝ^2 ↦
      iteratedFDeriv ℝ j (fun x ↦ (canonicalOf k sol₀).vorticity x p.1) p.2)
      (hreg₀.continuousOn_iteratedFDeriv_canonicalOf_vorticity hk1 hj),
    fun j hj ↦ hswap (G := fun p : ℝ × ℝ^2 ↦
      iteratedFDeriv ℝ j (fun x ↦ (canonicalOf k sol₀).temperature x p.1) p.2)
      (hreg₀.continuousOn_iteratedFDeriv_canonicalOf_temperature hj)⟩
  · obtain ⟨R', -, N', hRN⟩ := hreg₀.exists_isHolderDataOf ht
    exact ⟨HalfPlaneSystem.IsHolderDataOf.contDiff_canonicalOf_vorticity hRN hk1,
      HalfPlaneSystem.IsHolderDataOf.contDiff_canonicalOf_temperature hRN,
      HalfPlaneSystem.IsHolderDataOf.hasCompactSupport_canonicalOf_vorticity hRN,
      HalfPlaneSystem.IsHolderDataOf.hasCompactSupport_canonicalOf_temperature hRN⟩
  · obtain ⟨R', -, N', hRN⟩ := hreg₀.holderData a b hab
    refine ⟨max ((PDE.Analysis.reflectionBound k (k + 1) + 1) * N')
      ((PDE.Analysis.reflectionBound (k + 1) (k + 2) + 1) * N'), fun t ht x x' ↦ ⟨?_, ?_⟩⟩
    · exact (HalfPlaneSystem.IsHolderDataOf.norm_iteratedFDeriv_canonicalOf_vorticity_sub_le
        (hRN t ht) hk1 hα.le hα1.le x x').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg _) α))
    · exact (HalfPlaneSystem.IsHolderDataOf.norm_iteratedFDeriv_canonicalOf_temperature_sub_le
        (hRN t ht) hα.le hα1.le x x').trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) α))

end HalfPlaneSystem
