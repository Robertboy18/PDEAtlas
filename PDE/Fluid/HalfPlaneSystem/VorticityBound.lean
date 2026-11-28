/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Lagrangian
public import PDE.Fluid.Boussinesq.HalfPlane.Maximal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The vorticity of a half-plane system is bounded by the integral of the temperature gradient

This module bounds the sup norm of the vorticity of a half-plane system by the time integral of the
temperature gradient alone, whatever the velocity. The continuation criterion has the gradients of
the velocity and of the temperature, and in an application the velocity gradient may be controlled
only near a part of the domain.

Along a trajectory `ω(X(s, a), s) = ω(a, 0) + ∫₀ˢ κ(X) ∂₀θ(X) dr`, so on `[0, T)`

```text
|ω(x, s)| ≤ sup |ω(·, 0)| + Bκ₀ ∫₀ᵀ sup |∇θ(·, r)| dr
```

with the supremum of the temperature gradient over the open upper half-plane. Only this integral
enters, not the velocity: on `[0, s]` the velocity field is Lipschitz, which is all the Lagrangian
form needs. At a point of the closed half-plane a continuous function is bounded by its supremum
over the open half-plane near the point (`enorm_le_iSup_of_continuousAt`). The bound is for the sup
norm of the vorticity only; its derivatives are bounded in the modules of the a priori estimate,
under a bound of the velocity gradient.

## Main results

* `IsSolutionOn.abs_vorticity_le_add_lintegral`: for a solution on `[0, T)` for which the integral
  is finite, `|ω(x, s)| ≤ N₀ + Bκ₀ ∫₀ᵀ G` on the closed half-plane, where `|ω(·, 0)| ≤ N₀` there and
  `G r` is the supremum of `‖∇θ(·, r)‖` over a set that contains the open upper half-plane.
* `enorm_le_iSup_of_continuousAt`: at a point of the closed half-plane in an open set where a
  function with values in a normed group is continuous, its norm is at most the supremum of the norm
  over the points of the open set in the open half-plane.
* `volume_lifeSpan_ne_top`: a finite life span has finite measure.

No other module of this folder uses this module. BlowupZoo uses the three results to pass from a
finite continuation integral of the Euler equations near the wall of the cylinder to a finite
continuation integral of the half-plane system.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE Boussinesq.HalfPlane
open scoped Topology ENNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- At a point `y` of `H̄` in an open set `U` where `g` is continuous, `‖g y‖ₑ` is at most the
supremum of `‖g‖ₑ` over any set `S` containing the points of `U` in the open upper half-plane. -/
theorem enorm_le_iSup_of_continuousAt {E : Type*} [NormedAddCommGroup E] {g : ℝ^2 → E}
    {U S : Set (ℝ^2)} (hU : IsOpen U) (hS : ∀ z ∈ U, 0 < z 1 → z ∈ S) {y : ℝ^2} (hyU : y ∈ U)
    (hy : 0 ≤ y 1) (hg : ContinuousAt g y) : ‖g y‖ₑ ≤ ⨆ x ∈ S, ‖g x‖ₑ := by
  set e : ℝ^2 := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have ht : Tendsto (fun s : ℝ ↦ y + s • e) (𝓝[>] 0) (𝓝 y) := by
    have : Tendsto (fun s : ℝ ↦ y + s • e) (𝓝 0) (𝓝 (y + (0 : ℝ) • e)) :=
      tendsto_const_nhds.add (tendsto_id.smul_const e)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ ↦ ‖g (y + s • e)‖ₑ) (𝓝[>] 0) (𝓝 ‖g y‖ₑ) :=
    (continuous_eNorm.tendsto _).comp (hg.tendsto.comp ht)
  refine le_of_tendsto hlim ?_
  filter_upwards [ht.eventually (hU.mem_nhds hyU), self_mem_nhdsWithin] with s hs hs0
  have h1 : 0 < (y + s • e) 1 := by
    have : (y + s • e) 1 = y 1 + s := by simp [e]
    rw [this]
    exact add_pos_of_nonneg_of_pos hy hs0
  exact le_iSup₂ (f := fun x _ ↦ ‖g x‖ₑ) _ (hS _ hs h1)

/-- A finite life span has finite measure. -/
theorem volume_lifeSpan_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) : volume (lifeSpan T) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := T.toReal)).ne
    (measure_mono fun t ht ↦ ⟨ht.1, ?_⟩)
  exact ((ENNReal.ofReal_lt_iff_lt_toReal ht.1 hT).mp ht.2).le

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-- **The vorticity is bounded by the integral of the temperature gradient**: for a solution on
`[0, T)`, `|ω(x, s)| ≤ N₀ + Bκ₀ ∫₀ᵀ G` on `H̄`, where `|ω(·, 0)| ≤ N₀` on `H̄` and `G r` is the
supremum of `‖∇θ(·, r)‖` over a set `S` containing the open upper half-plane. It bounds the
vorticity without any bound of the velocity. Proof: along the trajectory through `x` the
vorticity is the datum at the label plus the time integral of `κ ∂₀θ`; the integrand is at most
`Bκ₀` times the supremum of the temperature gradient, at boundary points by continuity. -/
theorem IsSolutionOn.abs_vorticity_le_add_lintegral {sol : Fields} {T : ℝ≥0∞}
    (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (h : IsSolutionOn U κ R₀ sol (lifeSpan T)) {N₀ : ℝ}
    (hN₀ : ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x 0| ≤ N₀) {S : Set (ℝ^2)}
    (hS : ∀ z : ℝ^2, 0 < z 1 → z ∈ S)
    (hG : ∫⁻ r in lifeSpan T, ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ ≠ ⊤)
    {s : ℝ} (hs : s ∈ lifeSpan T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.vorticity x s| ≤ N₀ + Bκ 0 *
      (∫⁻ r in lifeSpan T, ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ).toReal := by
  set I := ∫⁻ r in lifeSpan T, ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hI0 : 0 ≤ Bκ 0 * I.toReal := mul_nonneg hB0 ENNReal.toReal_nonneg
  rcases hs.1.eq_or_lt with h0 | hpos
  · subst h0
    exact (hN₀ x hx).trans (le_add_of_nonneg_right hI0)
  have hI : Icc 0 s ⊆ lifeSpan T := fun r hr ↦
    ⟨hr.1, (ENNReal.ofReal_le_ofReal hr.2).trans_lt hs.2⟩
  obtain ⟨K, hv⟩ := h.exists_isC1FieldOn hU hpos hI
  have hL := hv.isLipschitzFieldOn
  have hsI : s ∈ Icc 0 s := ⟨hpos.le, le_rfl⟩
  -- The vorticity at `(x, s)` in Lagrangian form, with the label `a` of `x`.
  set a := label U sol s x s
  have ha : 0 ≤ a 1 := h.label_mem hU hI hL hpos.le hsI hx
  have hrep := h.vorticity_trajectory hU hκ.contDiff_one.continuous hpos hI hv ha hsI
  rw [trajectory_label hL hpos.le hsI] at hrep
  set F : ℝ → ℝ := fun r ↦ κ (trajectory U sol s r a) *
    (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol s r a)
  -- The forcing along the trajectory is at most `Bκ₀` times the supremum of the temperature
  -- gradient; the particle may be on the boundary, where the supremum bounds by continuity.
  have hpt : ∀ r ∈ Ioc 0 s, ‖F r‖ₑ ≤ ENNReal.ofReal (Bκ 0) *
      ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ := by
    intro r hr
    have hr' : r ∈ Icc 0 s := ⟨hr.1.le, hr.2⟩
    have hX : 0 ≤ trajectory U sol s r a 1 := h.trajectory_mem hU hI hL hpos.le hr' ha
    have hθ := h.contDiff_temperature (hI hr')
    have hk : ‖κ (trajectory U sol s r a)‖ₑ ≤ ENNReal.ofReal (Bκ 0) := by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (hκ.abs_le _)
    have hd : ‖(∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol s r a)‖ₑ ≤
        ‖fderiv ℝ (fun z ↦ sol.temperature z r) (trajectory U sol s r a)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [PDE.partialDeriv]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      simp
    have hsup := enorm_le_iSup_of_continuousAt isOpen_univ (fun z _ hz ↦ hS z hz) (mem_univ _) hX
      ((hθ.continuous_fderiv one_ne_zero).continuousAt)
    simp only [F, eNorm_mul]
    exact mul_le_mul' hk (hd.trans hsup)
  -- Integrate in time over `[0, s] ⊆ [0, T)`.
  have hint : ‖∫ r in (0)..s, F r‖ₑ ≤ ENNReal.ofReal (Bκ 0) * I := by
    rw [intervalIntegral.integral_of_le hpos.le]
    calc _ ≤ ∫⁻ r in Ioc 0 s, ‖F r‖ₑ := eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ r in Ioc 0 s, ENNReal.ofReal (Bκ 0) *
          ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ :=
        setLIntegral_mono' measurableSet_Ioc hpt
      _ ≤ ∫⁻ r in lifeSpan T, ENNReal.ofReal (Bκ 0) *
          ⨆ y ∈ S, ‖fderiv ℝ (fun z ↦ sol.temperature z r) y‖ₑ :=
        lintegral_mono_set fun r hr ↦ hI ⟨hr.1.le, hr.2⟩
      _ = ENNReal.ofReal (Bκ 0) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hint' : ‖∫ r in (0)..s, F r‖ ≤ Bκ 0 * I.toReal := by
    rw [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      hG)] at hint
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0] at hint
  rw [hrep]
  calc |sol.vorticity a 0 + ∫ r in (0)..s, F r| ≤ |sol.vorticity a 0| + ‖∫ r in (0)..s, F r‖ :=
        abs_add_le _ _
    _ ≤ N₀ + Bκ 0 * I.toReal := add_le_add (hN₀ a ha) hint'

end HalfPlaneSystem
