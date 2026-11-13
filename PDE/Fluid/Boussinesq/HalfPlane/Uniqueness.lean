/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Lagrangian
public import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison
public import PDE.Analysis.ODE.Flow.Inverse
public import PDE.Analysis.ODE.Flow.Comparison
import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.SliceDerivative

/-!
# Uniqueness of half-plane Boussinesq solutions

Two solutions in the class `IsSolutionOn` with the same data at time `0` agree on the closed
half-plane at every later time of a common interval (`IsSolutionOn.eqOn_of_hasDataAt`,
`IsSolutionOn.eq_of_hasDataAt`).

## Main results

* `IsSolutionOn.eqOn_of_hasDataAt`: agreement on `[0, b] × H̄` for solutions on `I ⊇ [0, b]` with
  the same data at time `0` on the closed half-plane.
* `IsSolutionOn.eq_of_hasDataAt`: agreement at every time `t ≥ 0` of an order-connected `I ∋ 0`.
* `VorticityStreamFields.shiftTime`, `IsSolutionOn.shiftTime`: the class is invariant under
  shifts of the time.
* `IsSolutionOn.eq_of_eq_at_of_le`: two solutions on an order-connected `I` that agree at a time
  `t₀ ∈ I` agree at every later time of `I`.

## How it works

We argue in Lagrangian variables and close with Osgood's lemma. With `X, X'` the trajectories and
`J, J'` their first variations (the derivatives in the label) on `[0, b]`, let `E(s)` be the
supremum over `r ∈ [0, s]` and labels `a` in the closed half-plane of
`‖X(r, a) - X'(r, a)‖ + ‖J(r, a) - J'(r, a)‖`. The vorticities then differ by at most `c₃ E(s)` at
time `s` (`abs_vorticity_sub_le_of_le`): the Lagrangian vorticity of the first solution is Lipschitz
in the label, the labels differ by the difference of the trajectories, and the vorticity forcing
`∂₀θ` along a trajectory is `Dθ₀(a)(J⁻¹ e₀)`, whose difference is controlled by `J - J'`. So the
velocities differ by `C E(s)` (`norm_halfPlaneVelocity_sub_le_of_abs_sub_le`) and, by the
homogeneous Kato bound of the difference (`norm_sub_fderivWithin_halfPlaneVelocity_le`), their
derivatives by `C φ(E(s))`, with `φ(r) = r (1 + log (A / r))` the Osgood modulus; the derivative of
the first velocity is log-Lipschitz with modulus `C φ(min q A)`
(`norm_fderivWithin_halfPlaneVelocity_sub_le_osgood`). The comparison of the flows and of their
variations (`PDE.Analysis.ODE.IsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant`,
`PDE.Analysis.ODE.IsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant`) then gives
`E(s) ≤ C ∫₀ˢ φ(E)`, so `E = 0` by Osgood's lemma in the form
`PDE.Analysis.eq_zero_of_le_integral_osgoodModulus`. The supports, bounded uniformly in time on
`[0, b]` as part of `IsSolutionOn`, give the uniform bounds of the vorticity, its gradient and the
velocity used throughout.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace Boussinesq.HalfPlane

open IncompressibleFlow PDE.Analysis.ODE

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- Two functions differentiable at a point of the closed half-plane that agree on the closed
half-plane have the same derivative there. -/
theorem fderiv_eq_of_eqOn_closedUpper {f g : ℝ^2 → ℝ} {a : ℝ^2} (ha : 0 ≤ a 1)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a)
    (heq : ∀ y : ℝ^2, 0 ≤ y 1 → f y = g y) : fderiv ℝ f a = fderiv ℝ g a :=
  (uniqueDiffOn_closedUpper a ha).eq hf.hasFDerivAt.hasFDerivWithinAt
    (hg.hasFDerivAt.hasFDerivWithinAt.congr (fun y hy ↦ heq y hy) (heq a ha))

variable {sol sol' : VorticityStreamFields} {I : Set ℝ} {b : ℝ} {K₀ K₀' : ℝ≥0}

/-- **The vorticities differ by the Lagrangian differences.** If on `[0, q]` the trajectories and
the first variations of two solutions with the same data differ by at most `E` on the closed
half-plane, then at time `q` their vorticities differ by at most
`(B₁ e^{2K₀ b} + b N₀ e^{K₁ b} e^{K₁' b}) E` on the closed half-plane, where `B₁` bounds the
gradient of the first vorticity, `N₀` the gradient of the initial temperature, `K₀` is the global
derivative bound of the first velocity field and `K₁, K₁'` bound the derivatives of the two
velocity fields on the closed half-plane. -/
theorem abs_vorticity_sub_le_of_le (h : IsSolutionOn sol I) (h' : IsSolutionOn sol' I)
    (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K₀)
    (hv' : IsC1FieldOn (velocityField sol') (velocityFieldDeriv sol') 0 b K₀')
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0)
    {B₁ N₀ K₁ K₁' E : ℝ}
    (hB₁ : ∀ s ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderiv ℝ (fun y ↦ sol.vorticity y s) x‖ ≤ B₁)
    (hN₀ : ∀ a : ℝ^2, 0 ≤ a 1 → ‖fderiv ℝ (fun y ↦ sol.temperature y 0) a‖ ≤ N₀)
    (hK₁ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv sol r y‖ ≤ K₁)
    (hK₁' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv sol' r y‖ ≤ K₁')
    {q : ℝ} (hq : q ∈ Icc 0 b)
    (hE : ∀ r ∈ Icc 0 q, ∀ a : ℝ^2, 0 ≤ a 1 →
      ‖trajectory sol b r a - trajectory sol' b r a‖ +
        ‖variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b r 0 a -
          variationOn (velocityField sol') (velocityFieldDeriv sol') 0 b r 0 a‖ ≤ E)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.vorticity x q - sol'.vorticity x q| ≤
      (B₁ * Real.exp (K₀ * b) * Real.exp (K₀ * b) +
        b * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b))) * E := by
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hqq : q ∈ Icc 0 q := ⟨hq.1, le_rfl⟩
  have hE0 : 0 ≤ E := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hE q hqq 0 (by simp))
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ q hq 0 (by simp))
  have hN₀0 : 0 ≤ N₀ := (norm_nonneg _).trans (hN₀ 0 (by simp))
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0 h0 0 (by simp))
  have hK₁0' : 0 ≤ K₁' := (norm_nonneg _).trans (hK₁' 0 h0 0 (by simp))
  have hq0 : |q - 0| ≤ b := by rw [sub_zero, abs_of_nonneg hq.1]; exact hq.2
  set a' := label sol' b x q
  have ha' : 0 ≤ a' 1 := h'.label_mem hI hL' hq hx
  -- the labels differ by at most `e^{K₀ b} E`, and the Lagrangian vorticity is Lipschitz in them
  have hlab : ‖label sol b x q - a'‖ ≤ Real.exp (K₀ * b) * E := by
    refine (hL.norm_flowOn_sub_flowOn_le_of_inverse hL' hq h0 x).trans ?_
    gcongr
    · rwa [abs_sub_comm]
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hE q hqq a' ha')
  have hlip := h.abs_vorticity_trajectory_sub_le hb hI hv hB₁ hq (h.label_mem hI hL hq hx) ha'
  rw [trajectory_label hL hq x] at hlip
  -- the forcing integrals
  have hω := h.vorticity_trajectory hb hI hv ha' hq
  have hω' := h'.vorticity_trajectory hb hI hv' ha' hq
  rw [trajectory_label hL' hq x] at hω'
  have hsub : Icc 0 q ⊆ Icc 0 b := Icc_subset_Icc_right hq.2
  have hgrad : fderiv ℝ (fun y ↦ sol.temperature y 0) a' =
      fderiv ℝ (fun y ↦ sol'.temperature y 0) a' :=
    fderiv_eq_of_eqOn_closedUpper ha'
      ((h.contDiff_temperature (hI h0)).differentiable (by norm_num) a')
      ((h'.contDiff_temperature (hI h0)).differentiable (by norm_num) a')
      fun y hy ↦ (hdata y hy).2
  have hint : ‖(∫ r in (0)..q, (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r))
        (trajectory sol b r a')) -
      ∫ r in (0)..q, (∂[(0 : Fin 2)] (fun y ↦ sol'.temperature y r))
        (trajectory sol' b r a')‖ ≤
      N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b) * E * |q - 0| := by
    rw [← intervalIntegral.integral_sub
      (((h.continuousOn_partialDeriv_temperature_trajectory hb hI hv a').mono hsub
        ).intervalIntegrable_of_Icc hq.1)
      (((h'.continuousOn_partialDeriv_temperature_trajectory hb hI hv' a').mono hsub
        ).intervalIntegrable_of_Icc hq.1)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hr' : r ∈ Icc 0 q := Ioc_subset_Icc_self (uIoc_of_le hq.1 ▸ hr)
    have hrb := hsub hr'
    have hexp (K : ℝ) (hK : 0 ≤ K) : Real.exp (K * |0 - r|) ≤ Real.exp (K * b) := by
      gcongr; rw [zero_sub, abs_neg, abs_of_nonneg hr'.1]; exact hrb.2
    have hWW : ‖_‖ ≤ Real.exp (K₁ * b) * E * Real.exp (K₁' * b) :=
      (hv.norm_variationOn_inverse_sub_le hv' hrb h0 a').trans <| by
        gcongr
        · exact (hv.norm_variationOn_le_of_invariant
            (fun s hs t ht ↦ (h.bijOn_flowOn hI hL hs ht).mapsTo) hK₁ h0 hrb
            ((h.bijOn_flowOn hI hL hrb h0).mapsTo ha')).trans (hexp K₁ hK₁0)
        · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hE r hr' a' ha')
        · exact (hv'.norm_variationOn_le_of_invariant
            (fun s hs t ht ↦ (h'.bijOn_flowOn hI hL' hs ht).mapsTo) hK₁' h0 hrb
            ((h'.bijOn_flowOn hI hL' hrb h0).mapsTo ha')).trans (hexp K₁' hK₁0')
    rw [h.partialDeriv_temperature_trajectory hb hI hv ha' hrb,
      h'.partialDeriv_temperature_trajectory hb hI hv' ha' hrb, ← hgrad, ← map_sub, ← sub_apply]
    exact (ContinuousLinearMap.le_of_opNorm_le_of_le _ (hN₀ a' ha')
      (ContinuousLinearMap.le_of_opNorm_le_of_le _ hWW
        (by simp : ‖(EuclideanSpace.single 0 1 : ℝ^2)‖ ≤ 1))).trans_eq (by ring)
  have hdiff : sol.vorticity x q - sol'.vorticity x q =
      (sol.vorticity x q - sol.vorticity (trajectory sol b q a') q) +
      ((∫ r in (0)..q, (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r))
          (trajectory sol b r a')) -
        ∫ r in (0)..q, (∂[(0 : Fin 2)] (fun y ↦ sol'.temperature y r))
          (trajectory sol' b r a')) := by
    rw [hω, hω', (hdata a' ha').1]; ring
  rw [hdiff]
  calc _ ≤ |sol.vorticity x q - sol.vorticity (trajectory sol b q a') q| + |_| := abs_add_le _ _
    _ ≤ B₁ * Real.exp (K₀ * b) * (Real.exp (K₀ * b) * E) +
        N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b) * E * b := by
        gcongr
        · exact hlip.trans (by gcongr)
        · exact hint.trans (by gcongr)
    _ = _ := by ring

/-- **Uniqueness.** Two solutions on `I ⊇ [0, b]`, `0 < b`, with the same vorticity and
temperature at time `0` on the closed half-plane agree on the closed half-plane at every time of
`[0, b]`. -/
theorem IsSolutionOn.eqOn_of_hasDataAt (h : IsSolutionOn sol I) (h' : IsSolutionOn sol' I)
    (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0) :
    ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  obtain ⟨K₀, hv⟩ := h.exists_isC1FieldOn hb hI
  obtain ⟨K₀', hv'⟩ := h'.exists_isC1FieldOn hb hI
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hS : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, MapsTo (flowOn (velocityField sol) 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h.bijOn_flowOn hI hL hs ht).mapsTo
  have hS' : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, MapsTo (flowOn (velocityField sol') 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h'.bijOn_flowOn hI hL' hs ht).mapsTo
  have h0H : (0 : ℝ^2) ∈ H̄ := by simp
  -- uniform bounds of the two vorticities
  obtain ⟨R, B, B₁, hB0, hB₁0, hω, hB₁⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  obtain ⟨R', B', B₁', hB0', hB₁0', hω', hB₁'⟩ :=
    h'.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  set M := max B₁ (2 * B)
  set M' := max B₁' (2 * B')
  have hM0 : 0 ≤ M := hω.holder_nonneg h0
  have hM0' : 0 ≤ M' := hω'.holder_nonneg h0
  obtain ⟨Rθ, hRθ⟩ := h.support 0 b hI
  obtain ⟨-, N₀, -, hN₀0, -, hN₀, -, -⟩ := PDE.Analysis.exists_bounds_of_contDiffOn
    (f := sol.temperature) hb hI h.classical.regularity.temperature_contDiffOn
    fun t ht x hx hxR ↦ (hRθ t ht x hx hxR).2
  set R₀ := max (max R R') 0
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  have hsupp (r : ℝ) (hr : r ∈ Icc 0 b) : ∀ y : ℝ^2, 0 ≤ y 1 → R₀ < ‖y‖ →
      (fun x ↦ sol.vorticity x r) y = 0 := fun y hy hyR ↦
    hω.eq_zero r hr y hy (((le_max_left R R').trans (le_max_left _ _)).trans_lt hyR)
  have hsupp' (r : ℝ) (hr : r ∈ Icc 0 b) : ∀ y : ℝ^2, 0 ≤ y 1 → R₀ < ‖y‖ →
      (fun x ↦ sol'.vorticity x r) y = 0 := fun y hy hyR ↦
    hω'.eq_zero r hr y hy (((le_max_right R R').trans (le_max_left _ _)).trans_lt hyR)
  -- the velocity fields on the closed half-plane
  have hvel (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityField sol r y = halfPlaneVelocity (fun x ↦ sol.vorticity x r) y :=
    extendedVelocity_of_nonneg 1 _ hy
  have hvel' (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityField sol' r y = halfPlaneVelocity (fun x ↦ sol'.vorticity x r) y :=
    extendedVelocity_of_nonneg 1 _ hy
  have hDvel {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityFieldDeriv sol r y =
        fderivWithin ℝ (halfPlaneVelocity (fun x ↦ sol.vorticity x r)) H̄ y :=
    fderiv_extendedVelocity_of_nonneg le_rfl
      (hω.contDiffOn_halfPlaneVelocity_one (by norm_num) hr) hy
  have hDvel' {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityFieldDeriv sol' r y =
        fderivWithin ℝ (halfPlaneVelocity (fun x ↦ sol'.vorticity x r)) H̄ y :=
    fderiv_extendedVelocity_of_nonneg le_rfl
      (hω'.contDiffOn_halfPlaneVelocity_one (by norm_num) hr) hy
  set K₁ := katoBound (1 / 2) (max R 0) B M
  set K₁' := katoBound (1 / 2) (max R' 0) B' M'
  have hK₁ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv sol r y‖ ≤ K₁ := fun r hr y hy ↦ by
    rw [hDvel hr hy]; exact hω.norm_fderivWithin_le (by norm_num) (by norm_num) hr hy
  have hK₁' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv sol' r y‖ ≤ K₁' := fun r hr y hy ↦ by
    rw [hDvel' hr hy]; exact hω'.norm_fderivWithin_le (by norm_num) (by norm_num) hr hy
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0 h0 0 h0H)
  have hK₁0' : 0 ≤ K₁' := (norm_nonneg _).trans (hK₁' 0 h0 0 h0H)
  set V := (1 + R₀ ^ 2) * B
  set V' := (1 + R₀ ^ 2) * B'
  have hV : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField sol r y‖ ≤ V := fun r hr y hy ↦
    hvel r hy ▸ norm_halfPlaneVelocity_le_of_abs_le (hω.continuousOn r hr) (hsupp r hr) hR₀
      (hω.abs_le r hr) y
  have hV' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField sol' r y‖ ≤ V' := fun r hr y hy ↦
    hvel' r hy ▸ norm_halfPlaneVelocity_le_of_abs_le (hω'.continuousOn r hr) (hsupp' r hr) hR₀
      (hω'.abs_le r hr) y
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 h0 0 h0H)
  have hV0' : 0 ≤ V' := (norm_nonneg _).trans (hV' 0 h0 0 h0H)
  -- the Lagrangian differences and their running supremum
  set G : ℝ → ℝ^2 → ℝ := fun r a ↦ ‖trajectory sol b r a - trajectory sol' b r a‖ +
    ‖variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b r 0 a -
      variationOn (velocityField sol') (velocityFieldDeriv sol') 0 b r 0 a‖ with hGdef
  set A₀ := (V + V') * b + Real.exp (K₁ * b) + Real.exp (K₁' * b) with hA₀def
  have hGA : ∀ r ∈ Icc 0 b, ∀ a ∈ H̄, G r a ≤ A₀ := by
    intro r hr a ha
    have hr0 : |r - 0| ≤ b := by rw [sub_zero, abs_of_nonneg hr.1]; exact hr.2
    have hX : ‖trajectory sol b r a - trajectory sol' b r a‖ ≤ V * |r - 0| + V' * |r - 0| := by
      rw [← sub_sub_sub_cancel_right _ _ a]
      exact (norm_sub_le _ _).trans (add_le_add
        (IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS hV hr h0 ha)
        (IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS' hV' hr h0 ha))
    have e₁ : Real.exp (K₁ * |r - 0|) ≤ Real.exp (K₁ * b) := by gcongr
    have e₂ : Real.exp (K₁' * |r - 0|) ≤ Real.exp (K₁' * b) := by gcongr
    simp only [hGdef, hA₀def]
    linarith [norm_sub_le (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b r 0 a)
      (variationOn (velocityField sol') (velocityFieldDeriv sol') 0 b r 0 a),
      hv.norm_variationOn_le_of_invariant hS hK₁ hr h0 ha,
      hv'.norm_variationOn_le_of_invariant hS' hK₁' hr h0 ha,
      mul_le_mul_of_nonneg_left hr0 hV0, mul_le_mul_of_nonneg_left hr0 hV0']
  set E : ℝ → ℝ := fun s ↦ sSup ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄))
  have hbdd {s : ℝ} (hs : s ≤ b) :
      BddAbove ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄)) :=
    ⟨A₀, forall_mem_image.2 fun p hp ↦ hGA p.1 ⟨hp.1.1, hp.1.2.trans hs⟩ p.2 hp.2⟩
  have hne {s : ℝ} (hs : 0 ≤ s) :
      ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄)).Nonempty :=
    ⟨_, ⟨(0, 0), ⟨⟨le_rfl, hs⟩, h0H⟩, rfl⟩⟩
  have hGE {s : ℝ} (hs : s ∈ Icc 0 b) : ∀ r ∈ Icc 0 s, ∀ a ∈ H̄, G r a ≤ E s :=
    fun r hr a ha ↦ le_csSup (hbdd hs.2) ⟨(r, a), ⟨hr, ha⟩, rfl⟩
  have hEle {s c : ℝ} (hs : 0 ≤ s) (hc : ∀ r ∈ Icc 0 s, ∀ a ∈ H̄, G r a ≤ c) : E s ≤ c :=
    csSup_le (hne hs) (forall_mem_image.2 fun p hp ↦ hc p.1 hp.1 p.2 hp.2)
  have hEmono : MonotoneOn E (Icc 0 b) := fun s hs s' hs' hss' ↦
    csSup_le_csSup (hbdd hs'.2) (hne hs.1)
      (image_mono (prod_mono (Icc_subset_Icc_right hss') subset_rfl))
  have hE0 : ∀ s ∈ Icc 0 b, 0 ≤ E s := fun s hs ↦
    (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hGE hs 0 ⟨le_rfl, hs.1⟩ 0 h0H)
  have hEA : ∀ s ∈ Icc 0 b, E s ≤ A₀ := fun s hs ↦
    hEle hs.1 fun r hr a ha ↦ hGA r ⟨hr.1, hr.2.trans hs.2⟩ a ha
  -- step 1: the vorticities differ by `c₃ E`
  set c₃ := max (B₁ * Real.exp (K₀ * b) * Real.exp (K₀ * b) +
    b * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b))) 1
  have hc₃ : 1 ≤ c₃ := le_max_right _ _
  have hstep₁ : ∀ q ∈ Icc 0 b, ∀ y : ℝ^2, 0 ≤ y 1 →
      |(fun x ↦ sol.vorticity x q) y - (fun x ↦ sol'.vorticity x q) y| ≤ c₃ * E q :=
    fun q hq y hy ↦ (abs_vorticity_sub_le_of_le h h' hb hI hv hv' hdata hB₁
      (fun a ha ↦ hN₀ 0 h0 a ha) hK₁ hK₁' hq (E := E q) (fun r hr a ha ↦ hGE hq r hr a ha)
      hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE0 q hq))
  -- the Osgood parameter
  have hA₀pos : 0 < A₀ := by rw [hA₀def]; positivity
  have hc₃0 : 0 ≤ c₃ := zero_le_one.trans hc₃
  set A₁ := 2 * (c₃ * A₀) + (M + M') with hA₁def
  set A := max (max A₁ 1) (max A₀ (c₃ * A₀))
  have hA1 : 1 ≤ A := (le_max_right A₁ 1).trans (le_max_left _ _)
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hA₁A : A₁ ≤ A := (le_max_left A₁ 1).trans (le_max_left _ _)
  have hA₀A : A₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hcA₀A : c₃ * A₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA₁0 : 0 < A₁ := by rw [hA₁def]; positivity
  have hEmemA {q : ℝ} (hq : q ∈ Icc 0 b) : E q ∈ Icc 0 A := ⟨hE0 q hq, (hEA q hq).trans hA₀A⟩
  have hcEmemA {q : ℝ} (hq : q ∈ Icc 0 b) : c₃ * E q ∈ Icc 0 A :=
    ⟨mul_nonneg hc₃0 (hE0 q hq), (mul_le_mul_of_nonneg_left (hEA q hq) hc₃0).trans hcA₀A⟩
  -- step 2: the velocity fields differ by `C E` and their derivatives by `C φ(E)`
  have hvd : ∀ q ∈ Icc 0 b, ∀ y ∈ H̄,
      ‖velocityField sol q y - velocityField sol' q y‖ ≤ (1 + R₀ ^ 2) * (c₃ * E q) := by
    intro q hq y hy
    rw [hvel q hy, hvel' q hy]
    exact norm_halfPlaneVelocity_sub_le_of_abs_sub_le (hω.continuousOn q hq) (hsupp q hq)
      (hω'.continuousOn q hq) (hsupp' q hq) hR₀ (hstep₁ q hq) y
  set Cκ := 4 * (50 / (1 / 2) + 8 + 10 * (Real.pi * R₀ ^ 2)) with hCκdef
  have hCκ0 : 0 ≤ Cκ := by positivity
  have hDvd : ∀ q ∈ Icc 0 b, ∀ y ∈ H̄,
      ‖velocityFieldDeriv sol q y - velocityFieldDeriv sol' q y‖ ≤
        Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q) := by
    intro q hq y hy
    rw [hDvel hq hy, hDvel' hq hy]
    obtain ⟨hβ0, hβA⟩ := hcEmemA hq
    have h1 := norm_sub_fderivWithin_halfPlaneVelocity_le (hω.continuousOn q hq) (hsupp q hq)
      (hω'.continuousOn q hq) (hsupp' q hq) hR₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (hω.holder q hq) (hω'.holder q hq) hM0 hM0' (hstep₁ q hq)
      (mul_le_mul_of_nonneg_left (hEA q hq) hc₃0) hy
    rw [← hA₁def] at h1
    have h2 := PDE.Analysis.osgoodModulus_le_osgoodModulus (r := c₃ * E q) hA₁0 hA₁A hβ0
    have h3 := PDE.Analysis.le_osgoodModulus hβ0 hβA
    refine h1.trans ?_
    rw [hCκdef]
    linarith [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ Real.pi * R₀ ^ 2)]
  set Cψ := (11 + 4 * (Real.pi * R₀ ^ 2) + 4) * B₁ + 2 * K₁ / A with hCψdef
  have hCψ0 : 0 ≤ Cψ := by rw [hCψdef]; positivity
  have hψ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖velocityFieldDeriv sol r y - velocityFieldDeriv sol r z‖ ≤
        Cψ * PDE.Analysis.osgoodModulus A (min ‖y - z‖ A) := by
    intro r hr y hy z hz
    rw [hDvel hr hy, hDvel hr hz]
    refine norm_fderivWithin_halfPlaneVelocity_sub_le_osgood
      (h.contDiff_vorticity (hI hr)).contDiffOn (hsupp r hr) hR₀ (fun w hw ↦ ?_)
      (fun w hw ↦ hω.norm_fderivWithin_le (by norm_num) (by norm_num) hr hw) hA1 hy hz
    rw [((h.contDiff_vorticity (hI hr)).differentiable (by norm_num) w).fderivWithin
      (uniqueDiffOn_closedUpper w hw)]
    exact hB₁ r hr w hw
  -- monotone majorants
  set Φ : ℝ → ℝ := fun q ↦ PDE.Analysis.osgoodModulus A (E q)
  have hΦmono : MonotoneOn Φ (Icc 0 b) := fun q hq q' hq' hqq' ↦
    PDE.Analysis.monotoneOn_osgoodModulus hA0 (hEmemA hq) (hEmemA hq') (hEmono hq hq' hqq')
  have hΦ0 : ∀ q ∈ Icc 0 b, 0 ≤ Φ q := fun q hq ↦
    PDE.Analysis.osgoodModulus_nonneg (hEmemA hq).1 (hEmemA hq).2
  have hε₀mono : MonotoneOn (fun q ↦ (1 + R₀ ^ 2) * (c₃ * E q)) (Icc 0 b) :=
    fun q hq q' hq' hqq' ↦ by dsimp only; gcongr; exact hEmono hq hq' hqq'
  have hε₁mono : MonotoneOn (fun q ↦ Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q))
      (Icc 0 b) := fun q hq q' hq' hqq' ↦ mul_le_mul_of_nonneg_left
    (PDE.Analysis.monotoneOn_osgoodModulus hA0 (hcEmemA hq) (hcEmemA hq')
      (mul_le_mul_of_nonneg_left (hEmono hq hq' hqq') hc₃0)) hCκ0
  have hmonoSub {u : ℝ → ℝ} (hu : MonotoneOn u (Icc 0 b)) {r : ℝ} (hr : r ∈ Icc 0 b) :
      IntervalIntegrable u volume 0 r :=
    (hu.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc_right hr.2)).intervalIntegrable
  set Ctot := Real.exp (K₁ * b) * ((1 + R₀ ^ 2) * c₃) +
    Real.exp ((K₁ + K₁') * b) * (Cψ + Cκ * c₃) with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by positivity
  -- step 3: comparison of the flows and the variations
  have hGbound : ∀ s ∈ Icc 0 b, ∀ r ∈ Icc 0 s, ∀ a ∈ H̄,
      G r a ≤ Ctot * ∫ q in (0)..s, Φ q := by
    intro s hs r hr a ha
    have hrb : r ∈ Icc 0 b := ⟨hr.1, hr.2.trans hs.2⟩
    have hX := hv.norm_flowOn_sub_flowOn_le_of_invariant hv'
      PDE.Analysis.convex_closedUpperHalfPlane hS hS' hK₁ h0 hε₀mono
      (fun q hq ↦ by have := hE0 q hq; positivity) hvd ha hrb
    have hJ := hv.norm_variationOn_sub_variationOn_le_of_invariant hv' hS hS' hK₁ hK₁'
      (monotoneOn_osgoodModulus_min hA0 hCψ0)
      (fun q hq ↦ osgoodModulus_min_nonneg hA0 hCψ0 hq) hψ h0 hε₁mono
      (fun q hq ↦ mul_nonneg hCκ0
        (PDE.Analysis.osgoodModulus_nonneg (hcEmemA hq).1 (hcEmemA hq).2))
      hDvd ha hEmono (fun q hq ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans
        (hGE hq q ⟨hq.1, le_rfl⟩ a ha)) hrb
    have hΦi := hmonoSub hΦmono hrb
    have hI₁ : ∫ q in (0)..r, (1 + R₀ ^ 2) * (c₃ * E q) ≤
        (1 + R₀ ^ 2) * c₃ * ∫ q in (0)..r, Φ q := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hr.1 (hmonoSub hε₀mono hrb)
        (hΦi.const_mul _) fun q hq ↦ ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (PDE.Analysis.le_osgoodModulus
        (hEmemA ⟨hq.1, hq.2.trans hrb.2⟩).1 (hEmemA ⟨hq.1, hq.2.trans hrb.2⟩).2) (by positivity)
    have hI₂ : ∫ q in (0)..r, (Cψ * PDE.Analysis.osgoodModulus A (min (E q) A) +
          Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q)) ≤
        (Cψ + Cκ * c₃) * ∫ q in (0)..r, Φ q := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hr.1 (hmonoSub (fun q hq q' hq' hqq' ↦
        add_le_add (monotoneOn_osgoodModulus_min hA0 hCψ0 (hE0 q hq) (hE0 q' hq')
          (hEmono hq hq' hqq')) (hε₁mono hq hq' hqq')) hrb) (hΦi.const_mul _) fun q hq ↦ ?_
      have hqb : q ∈ Icc 0 b := ⟨hq.1, hq.2.trans hrb.2⟩
      rw [min_eq_left (hEmemA hqb).2, add_mul Cψ, mul_assoc Cκ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (PDE.Analysis.osgoodModulus_mul_le hA0 hc₃ (hE0 q hqb)) hCκ0)
    have hrs : ∫ q in (0)..r, Φ q ≤ ∫ q in (0)..s, Φ q :=
      intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
          exact hΦ0 q ⟨hq.1.le, hq.2.trans hs.2⟩)
        (hmonoSub hΦmono hs)
    have hIr0 : 0 ≤ ∫ q in (0)..r, Φ q :=
      intervalIntegral.integral_nonneg hr.1 fun q hq ↦ hΦ0 q ⟨hq.1, hq.2.trans hrb.2⟩
    have he₁ : Real.exp (K₁ * (r - 0)) ≤ Real.exp (K₁ * b) := by gcongr; linarith [hrb.2]
    have he₂ : Real.exp ((K₁ + K₁') * (r - 0)) ≤ Real.exp ((K₁ + K₁') * b) := by
      gcongr; linarith [hrb.2]
    calc G r a ≤ Real.exp (K₁ * b) * ((1 + R₀ ^ 2) * c₃ * ∫ q in (0)..r, Φ q) +
          Real.exp ((K₁ + K₁') * b) * ((Cψ + Cκ * c₃) * ∫ q in (0)..r, Φ q) :=
        add_le_add
          (hX.trans ((mul_le_mul_of_nonneg_left hI₁ (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_right he₁ (by positivity))))
          (hJ.trans ((mul_le_mul_of_nonneg_left hI₂ (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_right he₂ (by positivity))))
      _ = Ctot * ∫ q in (0)..r, Φ q := by rw [hCtotdef]; ring
      _ ≤ Ctot * ∫ q in (0)..s, Φ q := mul_le_mul_of_nonneg_left hrs hCtot0
  -- the Osgood lemma
  have hEz := PDE.Analysis.eq_zero_of_le_integral_osgoodModulus hA0 hCtot0 hEmono hE0
    (fun s hs ↦ (hEA s hs).trans hA₀A) (fun s hs ↦ hEle hs.1 (hGbound s hs))
  intro t ht x hx
  refine ⟨by simpa [hEz t ht, sub_eq_zero] using hstep₁ t ht x hx, ?_⟩
  have ha' := h'.label_mem hI hL' ht hx
  have hXE : ‖trajectory sol b t (label sol' b x t) - trajectory sol' b t (label sol' b x t)‖ ≤ 0 :=
    hEz t ht ▸ (le_add_of_nonneg_right (norm_nonneg _)).trans (hGE ht t ⟨ht.1, le_rfl⟩ _ ha')
  have hlab0 : label sol b x t = label sol' b x t := sub_eq_zero.mp <| norm_le_zero_iff.mp <|
    (hL.norm_flowOn_sub_flowOn_le_of_inverse hL' ht h0 x).trans
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hXE)
  rw [h.temperature_eq_label hI hv ht hx, h'.temperature_eq_label hI hv' ht hx,
    hlab0, (hdata _ ha').2]

/-- **Uniqueness on an interval.** Two solutions on an order-connected set of times `I ∋ 0` with
the same vorticity and temperature at time `0` on the closed half-plane agree on the closed
half-plane at every time `t ∈ I` with `0 ≤ t`. -/
theorem IsSolutionOn.eq_of_hasDataAt (h : IsSolutionOn sol I) (h' : IsSolutionOn sol' I)
    (hI : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hdata x hx
  · exact h.eqOn_of_hasDataAt h' htpos (hI.out h0 ht) hdata t ⟨ht0, le_rfl⟩ x hx

end Boussinesq.HalfPlane

namespace Boussinesq

/-! ### Shifting the time -/

/-- The fields of `sol` with the time shifted by `t₀`: the value at `(x, t)` is the value of
`sol` at `(x, t + t₀)`. -/
def VorticityStreamFields.shiftTime (sol : VorticityStreamFields) (t₀ : ℝ) :
    VorticityStreamFields where
  vorticity x t := sol.vorticity x (t + t₀)
  temperature x t := sol.temperature x (t + t₀)
  streamFunction x t := sol.streamFunction x (t + t₀)

/-- The classical class is invariant under shifts of the time. -/
theorem IsClassicalVorticityStreamSolutionOn.shiftTime {sol : VorticityStreamFields}
    {I : Set ℝ} (h : IsClassicalVorticityStreamSolutionOn sol I) (t₀ : ℝ) :
    IsClassicalVorticityStreamSolutionOn (sol.shiftTime t₀) ((· + t₀) ⁻¹' I) := by
  have hφ : ContDiff ℝ 1 (fun xt : ℝ^2 × ℝ ↦ (xt.1, xt.2 + t₀)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hmaps : MapsTo (fun xt : ℝ^2 × ℝ ↦ (xt.1, xt.2 + t₀)) (univ ×ˢ ((· + t₀) ⁻¹' I))
      (univ ×ˢ I) := fun xt hxt ↦ ⟨mem_univ _, hxt.2⟩
  refine
    { regularity :=
        { vorticity_contDiffOn :=
            h.regularity.vorticity_contDiffOn.comp hφ.contDiffOn hmaps
          temperature_contDiffOn :=
            h.regularity.temperature_contDiffOn.comp hφ.contDiffOn hmaps
          vorticity_differentiableAt_time := fun {x t} ht ↦
            DifferentiableAt.comp (g := fun s ↦ sol.vorticity x s) (f := fun s ↦ s + t₀) t
              (h.regularity.vorticity_differentiableAt_time ht)
              ((differentiableAt_id (x := t)).add_const t₀)
          temperature_differentiableAt_time := fun {x t} ht ↦
            DifferentiableAt.comp (g := fun s ↦ sol.temperature x s) (f := fun s ↦ s + t₀) t
              (h.regularity.temperature_differentiableAt_time ht)
              ((differentiableAt_id (x := t)).add_const t₀)
          streamFunction_spatial_contDiff := fun ht ↦
            h.regularity.streamFunction_spatial_contDiff ht }
      vorticity_equation := fun x t hx ht ↦ ?_
      temperature_equation := fun x t hx ht ↦ ?_
      streamFunction_equation := fun x t hx ht ↦ h.streamFunction_equation hx ht
      zero_streamFunction_boundary := fun x₁ t ht ↦ h.zero_streamFunction_boundary x₁ ht }
  · have heq := h.vorticity_equation hx ht
    change deriv (fun s ↦ sol.vorticity x (s + t₀)) t + _ = _
    rw [deriv_comp_add_const]
    exact heq
  · have heq := h.temperature_equation hx ht
    change deriv (fun s ↦ sol.temperature x (s + t₀)) t + _ = _
    rw [deriv_comp_add_const]
    exact heq

namespace HalfPlane

/-- Solutions are invariant under shifts of the time. -/
theorem IsSolutionOn.shiftTime {sol : VorticityStreamFields} {I : Set ℝ}
    (h : IsSolutionOn sol I) (t₀ : ℝ) :
    IsSolutionOn (sol.shiftTime t₀) ((· + t₀) ⁻¹' I) where
  classical := h.classical.shiftTime t₀
  stream t ht x hx := h.stream (t + t₀) ht x hx
  support a b hab := by
    have hsub : Icc (a + t₀) (b + t₀) ⊆ I := fun s hs ↦ by
      have := hab (show s - t₀ ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa using this
    obtain ⟨R, hR⟩ := h.support (a + t₀) (b + t₀) hsub
    exact ⟨R, fun t ht x hx hxR ↦
      hR (t + t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx hxR⟩

variable {sol sol' : VorticityStreamFields} {I : Set ℝ}

/-- **Uniqueness from any time.** Two solutions on an order-connected set of times `I` that agree
on the closed half-plane at a time `t₀ ∈ I` agree on the closed half-plane at every later time of
`I`. -/
theorem IsSolutionOn.eq_of_eq_at_of_le (h : IsSolutionOn sol I) (h' : IsSolutionOn sol' I)
    (hI : I.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t₀ = sol'.vorticity x t₀ ∧ sol.temperature x t₀ = sol'.temperature x t₀)
    {t : ℝ} (ht : t ∈ I) (htt₀ : t₀ ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  have hJ : ((· + t₀) ⁻¹' I).OrdConnected := ⟨fun p hp q hq r hr ↦
    hI.out hp hq ⟨by simpa using hr.1, by simpa using hr.2⟩⟩
  have h0 : (0 : ℝ) ∈ (· + t₀) ⁻¹' I := by simpa using ht₀
  have hd : ∀ y : ℝ^2, 0 ≤ y 1 → (sol.shiftTime t₀).vorticity y 0 =
      (sol'.shiftTime t₀).vorticity y 0 ∧
      (sol.shiftTime t₀).temperature y 0 = (sol'.shiftTime t₀).temperature y 0 := by
    intro y hy
    simpa [VorticityStreamFields.shiftTime] using hdata y hy
  have hmem : t - t₀ ∈ (· + t₀) ⁻¹' I := by simpa using ht
  have := (h.shiftTime t₀).eq_of_hasDataAt (h'.shiftTime t₀) hJ h0 hd hmem
    (sub_nonneg.mpr htt₀) hx
  simpa [VorticityStreamFields.shiftTime] using this

end HalfPlane

end Boussinesq
