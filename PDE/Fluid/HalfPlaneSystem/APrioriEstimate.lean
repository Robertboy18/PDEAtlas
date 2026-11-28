/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APriori

/-!
# The a priori estimate of the continuation criterion

This module proves the a priori estimate of a half-plane system: a bound of the time integral of the
velocity gradient keeps a regular solution in a bounded set of the class of the data, with a bound
that depends on the data and on the integral but not on the solution. The estimate turns the blow-up
alternative of the maximal solution into a continuation criterion.

The running supremum `Y` of the gradient of the vorticity, the Hessian of the temperature and their
`α`-Hölder quotients satisfies `Y ≤ c + C ∫ Y` by the bounds of `APriori.lean`, hence is bounded by
Grönwall's inequality for monotone functions (`IsSolutionOn.top_bound`). The running supremum is
monotone in time, and it is finite because the slices of a regular solution are of the class
`IsHolderData` with bounds that are uniform on compact intervals of times; for this reason the
estimate is stated for regular solutions, a hypothesis that the local existence theorem provides.
Together with the lower-order bounds this gives `exists_holderData_bound`. All constants are those
of `[0, b]`, so the same radius and bound serve every `t₁ ≤ b`; they are explicit in the proof but
not named.

## Main results

* `IsSolutionOn.top_bound`: for a velocity law with the bounds `IsVelocityLaw` and
  `IsHolderVelocityLaw` and a solution on `[0, b]` whose vorticity is a `C^{1,α}` history with
  slices of the class `IsHolderData`, under the lower-order bounds `Bω`, `Mω`, `Gθ`, `Qθ`, at every
  time of `[0, b]`, `b ≤ L`, the gradient of the vorticity, the Hessian of the temperature and their
  `α`-Hölder constants on the closed half-plane are at most
  `topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ`.
* `exists_holderData_bound`: for all `α ∈ (0, 1)` and all numbers `R`, `N`, `Λ`, `b` there are `R'`
  and `N'` such that every regular solution on `[0, t₁]`, `t₁ ≤ b`, with data of the class
  `IsHolderData … α R N` and velocity gradient bounded by a continuous `A` with `∫₀^{t₁} A ≤ Λ` has
  all its slices in the class `IsHolderData … α R' N'`.

`continuationIntegral_eq_top` (`Continuation.lean`) is proved from `exists_holderData_bound`: if the
continuation integral were finite, the slices would stay in one class of data up to the maximal
time. The library has the same theorem for the Biot-Savart law of the half-plane
(`Boussinesq.HalfPlane.exists_holderData_bound`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
  Boussinesq.HalfPlane
open scoped Topology NNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b : ℝ}
  {α R B M B₁ M₁ Λ Rd N Rq Nq Bω Mω Gθ Qθ L : ℝ} {K K₁ K₂ : ℝ≥0} {A : ℝ → ℝ}

/-- **The top-order a priori bound.** Under the lower-order bounds `Bω`, `Mω`, `Gθ`, `Qθ` of the
vorticity and its Hölder constant, the temperature gradient and its Hölder constant, at every
time of `[0, b]`, `b ≤ L`, the gradient of the vorticity, the Hessian of the temperature and
their `α`-Hölder constants on the closed half-plane are at most
`topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ`. It closes the top-order estimate. Proof: the
running supremum `P` of the four quantities is monotone and satisfies `P ≤ c + C ∫ P` by the
four inequalities of `APriori.lean`, so Grönwall's inequality for monotone functions bounds
it. -/
theorem top_bound (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b)
    (hI : Icc 0 b ⊆ I) (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
    (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
    (hα : 0 < α) (hα1 : α < 1)
    (hv₂ : IsC2FieldOn (lawField U fun t x ↦ sol.vorticity x t)
      (lawFieldDeriv U fun t x ↦ sol.vorticity x t)
      (lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
    (hreg : ∀ t ∈ Icc 0 b,
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
    (hA : ContinuousOn A (Icc 0 b))
    (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
    (hΛ : ∫ t in (0)..b, A t ≤ Λ)
    (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α Rd N)
    (hBω : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x t| ≤ Bω)
    (hMω : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y t - sol.vorticity z t| ≤ Mω * ‖y - z‖ ^ α)
    (hGθ : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ x‖ ≤ Gθ)
    (hQθ : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ z‖ ≤ Qθ * ‖y - z‖ ^ α)
    (hbL : b ≤ L) {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y‖ ≤
        topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ ∧
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y‖ ≤
        topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ ∧
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y -
          fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ z‖ ≤
        topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ * ‖y - z‖ ^ α ∧
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y -
          fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ z‖ ≤
        topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ * ‖y - z‖ ^ α := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set E := Real.exp Λ
  have hk : 0 ≤ C 1 α := hU.const_nonneg 1 α
  have hc : 0 ≤ Ch α := hUh.const_nonneg hα hα1
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hMω0 : 0 ≤ Mω := nonneg_of_norm_sub_le (F := fun x ↦ sol.vorticity x 0) (α := α)
    fun y z hy hz ↦ by rw [Real.norm_eq_abs]; exact hMω 0 h0 y z hy hz
  have hQθ0 : 0 ≤ Qθ := nonneg_of_norm_sub_le (hQθ 0 h0)
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hB1 : 0 ≤ Bκ 1 := hκ.bound_nonneg 1
  have hHκ : 0 ≤ forcingHolderConst Bκ 0 := hκ.forcingHolderConst_nonneg 0
  have hHκ' : 0 ≤ forcingHolderConst Bκ 1 := hκ.forcingHolderConst_nonneg 1
  have hL0 : 0 ≤ L := hb.le.trans hbL
  have he1 : Real.exp (1 * Λ) = E := by rw [one_mul]
  have he2 : Real.exp (2 * Λ) = E ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  -- The four quantities and their running supremum.
  set q : ℝ → ℝ^2 → ℝ^2 → ℝ := fun ρ y z ↦
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y‖ +
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y‖ +
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ z‖ / ‖y - z‖ ^ α +
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ z‖ / ‖y - z‖ ^ α
    with hqdef
  have hdiv {u v : ℝ} {y z : ℝ^2} (hyz : y ≠ z) (huv : u ≤ v * ‖y - z‖ ^ α) :
      u / ‖y - z‖ ^ α ≤ v :=
    (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α)).mpr huv
  have hq0 : ∀ ρ y z, 0 ≤ q ρ y z := fun _ _ _ ↦ by positivity
  have hqb : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z →
      q ρ y z ≤ Nq + Nq + Nq + Nq := fun ρ hρ y z hy hz hyz ↦
    add_le_add (add_le_add (add_le_add ((hreg ρ hρ).norm_fderivWithin_vorticity_le y hy)
      ((hreg ρ hρ).norm_fderivWithin_fderivWithin_temperature_le y hy))
      (hdiv hyz ((hreg ρ hρ).holder_vorticity y z hy hz)))
      (hdiv hyz ((hreg ρ hρ).holder_temperature y z hy hz))
  set P := holderSup q
  have hPm : MonotoneOn P (Icc 0 b) := monotoneOn_holderSup hqb
  have hP0 : ∀ ρ ∈ Icc 0 b, 0 ≤ P ρ := fun ρ hρ ↦ holderSup_nonneg hq0 hqb hρ
  have hle (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) (hyz : y ≠ z) :
      q ρ y z ≤ P ρ := le_holderSup hqb hρ.2 ⟨hρ.1, le_rfl⟩ hy hz hyz
  have hshift (y : ℝ^2) (hy : 0 ≤ y 1) :
      0 ≤ (y + EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 ∧
        y ≠ y + EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    have h1 : (y + EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 = y 1 + 1 := by simp
    refine ⟨by rw [h1]; linarith, fun hyy ↦ ?_⟩
    have := congrArg (fun x : ℝ^2 ↦ x 1) hyy
    simp only [h1] at this
    linarith
  have hP₁ : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x‖ ≤ P ρ := fun ρ hρ x hx ↦ by
    obtain ⟨hz, hxz⟩ := hshift x hx
    refine le_trans ?_ (hle ρ hρ hx hz hxz)
    simp only [hqdef]
    have h2 := norm_nonneg (fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x)
    have h3 : 0 ≤ ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (x + EuclideanSpace.single 1 1)‖ /
          ‖x - (x + EuclideanSpace.single 1 1)‖ ^ α := by positivity
    have h4 : 0 ≤ ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄
          (x + EuclideanSpace.single 1 1)‖ / ‖x - (x + EuclideanSpace.single 1 1)‖ ^ α := by
      positivity
    linarith
  have hP₂ : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x‖ ≤ P ρ :=
    fun ρ hρ x hx ↦ by
    obtain ⟨hz, hxz⟩ := hshift x hx
    refine le_trans ?_ (hle ρ hρ hx hz hxz)
    simp only [hqdef]
    have h1 := norm_nonneg (fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x)
    have h3 : 0 ≤ ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (x + EuclideanSpace.single 1 1)‖ /
          ‖x - (x + EuclideanSpace.single 1 1)‖ ^ α := by positivity
    have h4 : 0 ≤ ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄
          (x + EuclideanSpace.single 1 1)‖ / ‖x - (x + EuclideanSpace.single 1 1)‖ ^ α := by
      positivity
    linarith
  have hP₃ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ z‖ ≤ P ρ * ‖y - z‖ ^ α :=
    fun ρ hρ y z hy hz ↦ norm_sub_le_of_div_le (F := fun x ↦
      fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x) hα fun hyz ↦ by
      refine le_trans ?_ (hle ρ hρ hy hz hyz)
      simp only [hqdef]
      have h1 := norm_nonneg (fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y)
      have h2 := norm_nonneg
        (fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y)
      have h4 : 0 ≤ ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y -
          fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ z‖ /
            ‖y - z‖ ^ α := by positivity
      linarith
  have hP₄ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ z‖ ≤
          P ρ * ‖y - z‖ ^ α :=
    fun ρ hρ y z hy hz ↦ norm_sub_le_of_div_le (F := fun x ↦
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x) hα fun hyz ↦ by
      refine le_trans ?_ (hle ρ hρ hy hz hyz)
      simp only [hqdef]
      have h1 := norm_nonneg (fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y)
      have h2 := norm_nonneg
        (fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y)
      have h3 : 0 ≤ ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y -
          fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ z‖ / ‖y - z‖ ^ α := by positivity
      linarith
  -- The closed inequality.
  set c := topConst (C 1 α) Bκ N Λ L Bω Gθ Qθ
  set C' := topRate (C 1 α) (Ch α) Bκ Λ Bω Mω Gθ Qθ
  have hc0 : 0 ≤ c := by simp only [c, topConst]; positivity
  have hC0 : 0 ≤ C' := by simp only [C', topRate]; positivity
  have hstep : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z →
      q ρ y z ≤ c + C' * ∫ σ in (0)..ρ, P σ := by
    intro ρ hρ y z hy hz hyz
    have hpos : 0 < ‖y - z‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α
    have b1 := h.norm_vorticityGradient_le hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hGθ
      hbL hPm hP₂ hρ hy
    have b2 := h.norm_hessian_le hU hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hBω hGθ hbL hPm
      hP₁ hP₃ hρ hy
    have b3 := h.norm_vorticityGradient_sub_le hU hUh hκ hb hI hv hω hR hα hα1 hv₂ hreg hA hDu
      hΛ hd hBω hMω hGθ hQθ hbL hPm hP0 hP₁ hP₂ hP₄ hρ hy hz
    have b4 := h.norm_hessian_sub_le hU hUh hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hBω hMω
      hGθ hQθ hbL hPm hP0 hP₁ hP₂ hP₃ hρ hy hz
    rw [← mul_assoc, ← div_le_iff₀ hpos] at b3 b4
    calc q ρ y z ≤ _ := add_le_add (add_le_add (add_le_add b1 b2) b3) b4
      _ = c + C' * ∫ σ in (0)..ρ, P σ := by
        simp only [c, C', topConst, topRate, he1, he2]
        ring
  have hclosed : ∀ s ∈ Icc 0 b, P s ≤ c + C' * ∫ σ in (0)..s, P σ := fun s hs ↦
    holderSup_le hs.1 fun ρ hρ y z hy hz hyz ↦ by
      have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1, hρ.2.trans hs.2⟩
      refine (hstep ρ hρ' y z hy hz hyz).trans (add_le_add le_rfl ?_)
      exact mul_le_mul_of_nonneg_left
        (integral_le_integral_of_monotoneOn hPm hP0 hρ.1 hρ.2 hs.2) hC0
  have hgron := le_of_le_add_integral_of_monotoneOn hc0 hC0 hPm hclosed r hr
  have hT : P r ≤ topBound (C 1 α) (Ch α) Bκ N Λ L Bω Mω Gθ Qθ := by
    refine hgron.trans (mul_le_mul_of_nonneg_left ?_ hc0)
    have hrL : r ≤ L := hr.2.trans hbL
    have : C' * r * Real.exp (C' * r) ≤ C' * L * Real.exp (C' * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrL hC0)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrL hC0)) (Real.exp_pos _).le
        (mul_nonneg hC0 hL0)
    linarith
  have hα0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact ⟨(hP₁ r hr y hy).trans hT, (hP₂ r hr y hy).trans hT,
    (hP₃ r hr y z hy hz).trans (mul_le_mul_of_nonneg_right hT hα0),
    (hP₄ r hr y z hy hz).trans (mul_le_mul_of_nonneg_right hT hα0)⟩

end IsSolutionOn

/-- **The a priori estimate of the continuation criterion.** For data of the class
`IsHolderData … α R N` and a bound `A` of the velocity gradient with `∫₀^{t₁} A ≤ Λ`, every
time slice of a regular solution on `[0, t₁]`, `t₁ ≤ b`, is of the class `IsHolderData … α R' N'`
with `R'` and `N'` depending only on the constants of the law and of the coefficient, on `α`,
`R`, `N`, `Λ` and `b`. It is the estimate behind the continuation criterion: a finite integral
of the velocity gradient keeps the solution in one class of data. Proof: the lower-order bounds
from the transport of the data, then `IsSolutionOn.top_bound`, all with the constants of the
interval `[0, b]`. -/
theorem exists_holderData_bound (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
    (hκ : IsForcingCoefficient κ Bκ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R N Λ b : ℝ) :
    ∃ R' N' : ℝ, ∀ (sol : Fields) (I : Set ℝ) (A : ℝ → ℝ),
      IsRegularSolutionOn U κ R₀ sol I α → ∀ t₁, 0 < t₁ → t₁ ≤ b → Icc 0 t₁ ⊆ I →
      IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N →
      (∀ t ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 →
        ‖fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x‖ ≤ A t) →
      ContinuousOn A (Icc 0 t₁) → ∫ t in (0)..t₁, A t ≤ Λ →
      ∀ t ∈ Icc 0 t₁,
        IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  set E := Real.exp Λ
  set Rd := max R 0
  set Bω := vorticityBound Bκ N Λ b
  set R₁ := Rd + C 0 0 * Bω * b
  set T := topBound (C 1 α) (Ch α) Bκ N Λ b Bω (vorticityHolderBound (Ch α) Bκ N Λ b) (N * E)
    (gradientHolderBound (Ch α) Bκ N Λ b)
  refine ⟨R₁, max (max Bω (N * E)) (max N T), ?_⟩
  intro sol I A hsol t₁ ht₁ ht₁b hI hd₀ hDu' hA hΛ t ht
  have h := hsol.toIsSolutionOn
  have hd := hd₀.mono_radius (le_max_left R 0)
  have hRd : 0 ≤ Rd := le_max_right R 0
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hC00 : 0 ≤ C 0 0 := hU.const_nonneg 0 0
  obtain ⟨K, hv⟩ := h.exists_isC1FieldOn hU ht₁ hI
  have hDu : ∀ t ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t :=
    fun t ht x hx ↦ by rw [h.velocityFieldDeriv_eq hU ht₁ hI ht hx]; exact hDu' t ht x hx
  obtain ⟨Rq, Nq, hreg⟩ := hsol.holderData 0 t₁ hI
  obtain ⟨Rω, hRω, B, M, B₁, hω⟩ := h.exists_isC1VorticityHistory (M₁ := Nq) ht₁ hI hα.le hα1.le
    fun t ht y z hy hz ↦ (hreg t ht).holder_vorticity y z hy hz
  have hv₂ := hω.isC2FieldOn_lawField hU hRω.le hα hα1
  -- The lower-order bounds on `[0, t₁]`, with the constants of `[0, b]`.
  have hBt : N + t₁ * (Bκ 0 * (N * E)) ≤ Bω := by
    have : t₁ * (Bκ 0 * (N * E)) ≤ b * (Bκ 0 * (N * E)) :=
      mul_le_mul_of_nonneg_right ht₁b (by positivity)
    simp only [Bω, vorticityBound, E]
    linarith
  have hBω : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x s| ≤ Bω := fun s hs x hx ↦
    (h.abs_vorticity_le hU hκ ht₁ hI hv hA hDu hΛ hd hs hx).trans (by
      have : s * (Bκ 0 * (N * E)) ≤ t₁ * (Bκ 0 * (N * E)) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      linarith)
  have hBt0 : 0 ≤ N + t₁ * (Bκ 0 * (N * E)) := by positivity
  have hsupp : Rd + C 0 0 * (N + t₁ * (Bκ 0 * (N * E))) * t₁ ≤ R₁ := by
    have hBω0 : 0 ≤ Bω := hBt0.trans hBt
    simp only [R₁]
    gcongr
  have hR₁ : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → R₁ < ‖x‖ →
      sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := fun s hs x hx hxR ↦
    h.eq_zero_of_norm hU hκ ht₁ hI hv hA hDu hΛ hd hs hx (hsupp.trans_lt hxR)
  have hfd (s : ℝ) (hs : s ∈ Icc 0 t₁) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderiv ℝ (fun y ↦ sol.temperature y s) x =
        fderivWithin ℝ (fun y ↦ sol.temperature y s) H̄ x :=
    ((((h.contDiff_temperature (hI hs)).differentiable one_ne_zero) x).fderivWithin
      (uniqueDiffOn_closedUpper x hx)).symm
  have hGθ : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ x‖ ≤ N * E := fun s hs x hx ↦ by
    rw [← hfd s hs hx]
    exact h.norm_fderiv_temperature_le hU ht₁ hI hv hA hDu hΛ hd hs hx
  have hMω : ∀ s ∈ Icc 0 t₁, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y s - sol.vorticity z s| ≤
        vorticityHolderBound (Ch α) Bκ N Λ b * ‖y - z‖ ^ α :=
    fun s hs y z hy hz ↦
      (h.holder_bound hU hUh hκ ht₁ hI hv hA hDu hΛ hα hα1 hd hreg ht₁b hs hy hz).1
  have hQθ : ∀ s ∈ Icc 0 t₁, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ z‖ ≤
          gradientHolderBound (Ch α) Bκ N Λ b * ‖y - z‖ ^ α := fun s hs y z hy hz ↦ by
    rw [← hfd s hs hy, ← hfd s hs hz]
    exact (h.holder_bound hU hUh hκ ht₁ hI hv hA hDu hΛ hα hα1 hd hreg ht₁b hs hy hz).2
  -- The top-order bounds.
  have htop (y z : ℝ^2) (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :=
    h.top_bound hU hUh hκ ht₁ hI hv hω hRω.le hα hα1 hv₂ hreg hA hDu hΛ hd hBω hMω hGθ hQθ ht₁b
      ht hy hz
  have hT : T ≤ max (max Bω (N * E)) (max N T) := (le_max_right _ _).trans (le_max_right _ _)
  have hα0 (y z : ℝ^2) : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact
    { vorticity_contDiffOn := (hreg t ht).vorticity_contDiffOn
      temperature_contDiffOn := (hreg t ht).temperature_contDiffOn
      eq_zero := fun x hx hxR ↦ hR₁ t ht x hx hxR
      abs_vorticity_le := fun x hx ↦
        (hBω t ht x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
      norm_fderivWithin_vorticity_le := fun x hx ↦ (htop x x hx hx).1.trans hT
      holder_vorticity := fun y z hy hz ↦
        (htop y z hy hz).2.2.1.trans (mul_le_mul_of_nonneg_right hT (hα0 y z))
      abs_temperature_le := fun x hx ↦
        (h.abs_temperature_le hU ht₁ hI hv hd ht hx).trans
          ((le_max_left _ _).trans (le_max_right _ _))
      norm_fderivWithin_temperature_le := fun x hx ↦
        (hGθ t ht x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
      norm_fderivWithin_fderivWithin_temperature_le := fun x hx ↦ (htop x x hx hx).2.1.trans hT
      holder_temperature := fun y z hy hz ↦
        (htop y z hy hz).2.2.2.trans (mul_le_mul_of_nonneg_right hT (hα0 y z)) }

end HalfPlaneSystem
