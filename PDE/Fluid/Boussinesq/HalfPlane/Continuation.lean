/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.APriori
public import PDE.Fluid.Boussinesq.HalfPlane.Maximal

/-!
# The continuation criterion for the half-plane Boussinesq system

For data `ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` within the closed half-plane with compact support, the
regular solution on the maximal life span `[0, T*)` (`exists_maximal`) satisfies: if `T* < ∞`
then `∫₀^{T*} (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt = ∞`, with the sup norms over the open upper half-plane
(`continuationIntegral`).

This is a criterion of Beale, Kato and Majda type for the 2D Boussinesq system on the half-plane
with the Biot-Savart law of the Dirichlet problem (cf. Chae and Nam for the whole plane), where
the velocity estimates carry the vorticity mass (`katoBound`).

## Main results

* `continuationIntegral` (from `HalfPlane.LifeSpan`): the continuation quantity.
* `continuationIntegral_eq_top`: the criterion for the maximal solution.
* `exists_maximalSolution`: existence, uniqueness and maximality of the solution, with the
  criterion.

## How it works

We argue by contradiction in `continuationIntegral_eq_top`. If the integral were finite, the
velocity gradient `A(t)` (`velocityGradientSup`), the supremum over the closed half-plane of the
derivative of the velocity, would have finite integral `Λ` on every `[0, t₁] ⊂ [0, T*)`, since
`velocityGradientSup_spec` shows that `A` is continuous and bounded by the supremum over the open
half-plane that enters the continuation integral. The a priori estimate
`exists_holderData_bound` then bounds all slices in the data class by constants depending only
on the data, `Λ` and `T*`, which contradicts the blow-up alternative `not_forall_isHolderData`.

## References

* J. T. Beale, T. Kato and A. Majda, "Remarks on the breakdown of smooth solutions for the 3-D Euler
  equations", *Comm. Math. Phys.* 94 (1984), no. 1, 61-66.
  <https://doi.org/10.1007/BF01212349>
* D. Chae and H.-S. Nam, "Local existence and blow-up criterion for the Boussinesq equations",
  *Proc. Roy. Soc. Edinburgh Sect. A* 127 (1997), no. 5, 935-946.
  <https://doi.org/10.1017/S0308210500026810>
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open IncompressibleFlow

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The supremum over the closed half-plane of the derivative within it of the velocity of the
vorticity slice at time `t`. -/
def velocityGradientSup (sol : VorticityStreamFields) (t : ℝ) : ℝ :=
  sSup ((fun x ↦ ‖fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x‖) '' H̄)

variable {sol : VorticityStreamFields} {I : Set ℝ} {α : ℝ}

/-- On the closed half-plane the derivative within it of the velocity is bounded by the supremum
over the open half-plane of the derivative of the velocity of the solution. -/
theorem enorm_fderivWithin_le_iSup (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I)
    {a b R B M : ℝ} (hω : IsVorticityHistory (fun s x ↦ sol.vorticity x s) a b α R B M)
    (htab : t ∈ Icc a b) (hα : 0 < α) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x‖ₑ ≤
      ⨆ y ∈ upperHalfPlane, ‖fderiv ℝ (fun z ↦ vorticityStreamVelocity sol z t) y‖ₑ := by
  set u := halfPlaneVelocity (fun y ↦ sol.vorticity y t)
  set S := ⨆ y ∈ upperHalfPlane, ‖fderiv ℝ (fun z ↦ vorticityStreamVelocity sol z t) y‖ₑ
  have hopen : ∀ y ∈ upperHalfPlane, ‖fderivWithin ℝ u H̄ y‖ₑ ≤ S := by
    intro y hy
    have hnhds : H̄ ∈ 𝓝 y := Filter.mem_of_superset (isOpen_upperHalfPlane.mem_nhds hy)
      fun z (hz : 0 < z 1) ↦ hz.le
    have hev : (fun z ↦ vorticityStreamVelocity sol z t) =ᶠ[𝓝 y] u := by
      filter_upwards [hnhds] with z hz
      exact h.velocity_eq ht hz
    rw [fderivWithin_of_mem_nhds hnhds, ← hev.fderiv_eq]
    exact le_iSup₂ (f := fun y _ ↦ ‖fderiv ℝ (fun z ↦ vorticityStreamVelocity sol z t) y‖ₑ) y hy
  have hc : ContinuousOn (fun y ↦ ‖fderivWithin ℝ u H̄ y‖ₑ) H̄ :=
    continuous_enorm.comp_continuousOn
      ((hω.contDiffOn_halfPlaneVelocity hα htab).continuousOn_fderivWithin
        uniqueDiffOn_closedUpper le_rfl)
  have hcl : x ∈ closure upperHalfPlane := by rw [closure_upperHalfPlane]; exact hx
  have : (𝓝[upperHalfPlane] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hsub : upperHalfPlane ⊆ H̄ := fun z (hz : 0 < z 1) ↦ hz.le
  have htend := ((hc x hx).mono hsub).tendsto
  exact le_of_tendsto htend (eventually_nhdsWithin_of_forall hopen)

/-- On a compact interval the velocity gradient supremum is a bound, it is continuous, and its
integral is bounded by the continuation quantity. -/
theorem velocityGradientSup_spec (h : IsSolutionOn sol I) {a b R B M : ℝ}
    (hI : Icc a b ⊆ I) (hω : IsVorticityHistory (fun s x ↦ sol.vorticity x s) a b α R B M)
    (hα : 0 < α) (hα1 : α < 1) :
    (∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x‖ ≤
        velocityGradientSup sol t) ∧
    ContinuousOn (velocityGradientSup sol) (Icc a b) ∧
    ∀ t ∈ Icc a b, 0 ≤ velocityGradientSup sol t ∧
      ENNReal.ofReal (velocityGradientSup sol t) ≤
        ⨆ y ∈ upperHalfPlane, ‖fderiv ℝ (fun z ↦ vorticityStreamVelocity sol z t) y‖ₑ := by
  set D : ℝ → ℝ^2 → ℝ := fun t x ↦
    ‖fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x‖
  have hne : (H̄).Nonempty := ⟨0, by simp⟩
  have hbdd (t : ℝ) (ht : t ∈ Icc a b) : BddAbove (D t '' H̄) :=
    ⟨_, by rintro _ ⟨x, hx, rfl⟩; exact hω.norm_fderivWithin_le hα hα1 ht hx⟩
  have hle (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      D t x ≤ velocityGradientSup sol t :=
    le_csSup (hbdd t ht) ⟨x, hx, rfl⟩
  have hnn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ velocityGradientSup sol t :=
    (norm_nonneg _).trans (hle t ht (x := 0) (by simp))
  refine ⟨fun t ht x hx ↦ hle t ht hx, ?_, fun t ht ↦ ⟨hnn t ht, ?_⟩⟩
  · refine Metric.continuousOn_iff.mpr fun t ht ε hε ↦ ?_
    obtain ⟨δ, hδ, hδε⟩ := hω.exists_norm_fderivWithin_sub_le hα hα1 ht (half_pos hε)
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    rw [Real.dist_eq] at hst ⊢
    have h1 : velocityGradientSup sol s ≤ velocityGradientSup sol t + ε / 2 := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := hδε s hs hst x hx
      have h2 := norm_sub_norm_le
        (fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y s)) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x)
      have h3 := hle t ht hx
      simp only [D] at h3
      linarith
    have h2 : velocityGradientSup sol t ≤ velocityGradientSup sol s + ε / 2 := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := hδε s hs hst x hx
      have h2 := norm_sub_norm_le
        (fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y s)) H̄ x)
      rw [norm_sub_rev] at h2
      have h3 := hle s hs hx
      simp only [D] at h3
      linarith
    rw [abs_lt]
    constructor <;> linarith
  · set S := ⨆ y ∈ upperHalfPlane, ‖fderiv ℝ (fun z ↦ vorticityStreamVelocity sol z t) y‖ₑ
    by_cases hS : S = ⊤
    · rw [hS]; exact le_top
    rw [ENNReal.ofReal_le_iff_le_toReal hS]
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have := enorm_fderivWithin_le_iSup h (hI ht) hω ht hα hx
    rw [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal hS] at this
    exact this

/-- **The continuation criterion.** If the maximal time of data of the class is finite, the
continuation quantity of the maximal solution is infinite. -/
theorem continuationIntegral_eq_top {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hdata : IsHolderData ω₀ θ₀ α R N) (hT : maximalTime α ω₀ θ₀ ≠ ⊤)
    (hsol : IsRegularSolutionOn sol (lifeSpan (maximalTime α ω₀ θ₀)) α)
    (hd : HasDataAt sol 0 ω₀ θ₀) : continuationIntegral sol (maximalTime α ω₀ θ₀) = ⊤ := by
  by_contra hfin
  set Tstar := maximalTime α ω₀ θ₀
  set T := Tstar.toReal
  have hpos : 0 < Tstar := maximalTime_pos hα hα1 hdata
  have hTpos : 0 < T := ENNReal.toReal_pos hpos.ne' hT
  have hspan : lifeSpan Tstar = Ico 0 T := lifeSpan_of_ne_top hT
  set Λ := (continuationIntegral sol Tstar).toReal
  obtain ⟨R', N', hb⟩ := exists_holderData_bound hα hα1 R N Λ T
  have hd₀ : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N :=
    hdata.congr (fun x hx ↦ (hd x hx).1) (fun x hx ↦ (hd x hx).2)
  apply not_forall_isHolderData hα hα1 hdata (lt_top_iff_ne_top.mpr hT) hsol hd R' N'
  intro t ht
  rw [hspan] at ht
  set t₁ := (t + T) / 2
  have ht₁ : 0 < t₁ := by simp only [t₁]; linarith [ht.1]
  have ht₁T : t₁ < T := by simp only [t₁]; linarith [ht.2]
  have hsub : Icc 0 t₁ ⊆ lifeSpan Tstar := by
    rw [hspan]; exact fun r hr ↦ ⟨hr.1, hr.2.trans_lt ht₁T⟩
  have h := hsol.toIsSolutionOn
  obtain ⟨Rω, Bω, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) ht₁ hsub (by norm_num) (by norm_num)
  obtain ⟨hA, hAc, hAle⟩ := velocityGradientSup_spec h hsub hω (by norm_num) (by norm_num)
  have hint : ∫ r in (0)..t₁, velocityGradientSup sol r ≤ Λ := by
    rw [intervalIntegral.integral_of_le ht₁.le]
    have hmeas : AEStronglyMeasurable (velocityGradientSup sol) (volume.restrict (Ioc 0 t₁)) :=
      (hAc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      fun r hr ↦ (hAle r (Ioc_subset_Icc_self hr)).1) hmeas]
    refine ENNReal.toReal_mono hfin ?_
    calc ∫⁻ r in Ioc 0 t₁, ENNReal.ofReal (velocityGradientSup sol r)
        ≤ ∫⁻ r in Ioc 0 t₁,
            ((⨆ x ∈ upperHalfPlane,
              ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity sol y r) x‖ₑ) +
              ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ sol.temperature y r) x‖ₑ) :=
          setLIntegral_mono' measurableSet_Ioc fun r hr ↦
            (hAle r (Ioc_subset_Icc_self hr)).2.trans le_self_add
      _ ≤ continuationIntegral sol Tstar :=
          lintegral_mono_set fun r hr ↦ hsub (Ioc_subset_Icc_self hr)
  have := hb sol (lifeSpan Tstar) (velocityGradientSup sol) hsol t₁ ht₁ ht₁T.le hsub hd₀
    (fun r hr x hx ↦ hA r hr x hx) hAc hint t ⟨ht.1, by simp only [t₁]; linarith [ht.2]⟩
  exact this

/-- **Local well-posedness and continuation** for the half-plane Boussinesq system. For data
`ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` within the closed half-plane, vanishing there outside a disc
(`IsHolderData`), `0 < α < 1`, there is a life span `T ∈ (0, ∞]` and a regular solution on
`[0, T)` with these data, such that every solution in the class `IsSolutionOn` from the same data
on a life span `T'` agrees with it on the closed half-plane up to `min T T'`, no regular solution
lives longer, and if `T < ∞` then `∫₀^T (‖∇u‖_∞ + ‖∇θ‖_∞) = ∞`. -/
theorem exists_maximalSolution {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hdata : IsHolderData ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (sol : VorticityStreamFields), 0 < T ∧
      IsRegularSolutionOn sol (lifeSpan T) α ∧ HasDataAt sol 0 ω₀ θ₀ ∧
      (T ≠ ⊤ → continuationIntegral sol T = ⊤) ∧
      (∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsRegularSolutionOn sol' (lifeSpan T') α →
        HasDataAt sol' 0 ω₀ θ₀ → T' ≤ T) ∧
      ∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsSolutionOn sol' (lifeSpan T') →
        HasDataAt sol' 0 ω₀ θ₀ → ∀ t ∈ lifeSpan (min T T'), ∀ x : ℝ^2, 0 ≤ x 1 →
          sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  obtain ⟨sol, hsol, hd⟩ := exists_maximal hα hα1 hdata
  refine ⟨maximalTime α ω₀ θ₀, sol, maximalTime_pos hα hα1 hdata, hsol, hd,
    fun hT ↦ continuationIntegral_eq_top hα hα1 hdata hT hsol hd,
    fun T' sol' h' hd' ↦ le_maximalTime h' hd', fun T' sol' h' hd' t ht x hx ↦ ?_⟩
  exact hsol.toIsSolutionOn.eq_of_hasDataAt_lifeSpan h' hd hd' ht hx

end Boussinesq.HalfPlane
