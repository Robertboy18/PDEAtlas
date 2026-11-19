/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.APrioriHolder
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Integration.Primitive.Local
import PDE.Fluid.Boussinesq.HalfPlane.CarriedFields

/-!
# The top-order derivatives of half-plane Boussinesq solutions along trajectories

For a regular solution on `[0, b]` the vorticity is a `C^{1,α}` history, so its velocity field
`historyField` is a `C²` field whose flow and first variation agree on the closed half-plane `H̄`
with those of the solution's velocity (`flowOn_eq_historyField`, `variationOn_eq_historyField`).
Along a trajectory `X(r, a)` of this flow, with first variation `J`, inverse first variation `W`
and second variation `S`, the Hessian of the temperature `H(r, a) = D²θ_r(X(r, a))` and the
gradient of the vorticity `Z(r, a) = Dω_r(X(r, a))` solve transported equations.

These equations need no second derivative of the vorticity and no third derivative of the
temperature. Their coefficients involve `Du` only through its size and `D²u` only linearly.

## Main results

* `IsSolutionOn.exists_isC1VorticityHistory`: the vorticity of a solution is a `C^{1,α}` history
  on compact intervals of times.
* `IsSolutionOn.hessian_flowOn_comp`: the Hessian of the temperature satisfies
  `D²θ_r(X)[J u, J w] + Dθ_r(X)(S[u, w]) = D²θ₀(a)[u, w]`.
* `IsSolutionOn.hessian_flowOn_eq`: `H` has the closed form
  `H[u, w] = D²θ₀(a)[W u, W w] - Dθ₀(a)(W S[W u, W w])`.
* `IsSolutionOn.hasDerivWithinAt_hessian`: `∂ᵣ H = -H[Du ·, ·] - H[·, Du ·] - Dθ_r(X) ∘ D²u`, in
  which the second variation has cancelled.
* `IsSolutionOn.vorticity_eq_forcedAmplitude`: the vorticity is the forced amplitude of the
  extended data at the label.
* `IsSolutionOn.fderivWithin_vorticity_eq`: the gradient of the vorticity in label form.
* `IsSolutionOn.hasDerivWithinAt_vorticityGradient`: `∂ᵣ Z = H[·, e₀] - Z ∘ Du`, with
  `e₀ = EuclideanSpace.single 0 1`.

## How it works

We differentiate the identity `θ_r(X(r, y)) = θ₀(y)` (`temperature_flowOn_historyField`) in the
label within `H̄`, once for `Dθ_r(X) ∘ J = Dθ₀` (`fderivWithin_temperature_flowOn_comp`) and twice
for `hessian_flowOn_comp`. Applying the second identity to `W u` and `W w`, where `J W = id`, gives
the closed form of `H` (`hessian_flowOn_eq`). We differentiate the closed form in time with the
equations of `W` and of `S`, and the terms with `S` cancel (`hasDerivWithinAt_hessian`). For the
vorticity, differentiating the label form `vorticity_eq_forcedAmplitude` in the label gives
`Z(r) = P(r) ∘ W(r)` with `P(r) = Dω̃₀(a) + ∫₀ʳ G`, where `ω̃₀` is the extended vorticity datum and
`G` the label derivative of the forcing (`fderivWithin_vorticity_eq`). The product rule then gives
`∂ᵣ Z`, and the closed form of `H` turns `G(r) ∘ W(r)` into `H[·, e₀]`
(`hasDerivWithinAt_vorticityGradient`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
open scoped Topology NNReal
open SobolevSpace

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The velocity field of the vorticity history. -/
local notation "𝐯" => historyField fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => historyFieldDeriv fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => historyFieldDeriv₂ fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- The position at time `ρ` of the particle of label `a` for the flow of the history. -/
local notation "𝐗 " ρ:max a:max => flowOn 𝐯 0 b ρ 0 a

set_option quotPrecheck false in
/-- The temperature gradient along the particle of label `a`. -/
local notation "𝐆 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The Hessian of the temperature along the particle of label `a`. -/
local notation "𝐇 " ρ:max a:max =>
  fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The vorticity gradient along the particle of label `a`. -/
local notation "𝐙 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (𝐗 ρ a)

/-- **The vorticity of a solution is a `C^{1,α}` history** on compact intervals of times on which
its gradient within the closed half-plane is `α`-Hölder with a common constant `M₁`. -/
theorem exists_isC1VorticityHistory (h : IsSolutionOn sol I) {a α M₁ : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ I) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hM₁ : ∀ t ∈ Icc a b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ z‖ ≤ M₁ * ‖y - z‖ ^ α) :
    ∃ R B M B₁ : ℝ,
      IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) a b α R B M B₁ M₁ := by
  obtain ⟨R, hR⟩ := h.support a b hI
  obtain ⟨B, B₁, -, -, hB, hB₁, hu, hu₁⟩ :=
    PDE.Analysis.exists_bounds_of_contDiffOn (f := sol.vorticity) hab hI
      h.classical.regularity.vorticity_contDiffOn fun t ht x hx hxR ↦ (hR t ht x hx hxR).1
  have hc (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) :=
    h.contDiff_vorticity (hI ht)
  have hfd (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderivWithin ℝ (fun y ↦ sol.vorticity y t) H̄ x =
        fderiv ℝ (fun y ↦ sol.vorticity y t) x :=
    ((hc t ht).differentiable (by norm_num) x).fderivWithin (uniqueDiffOn_closedUpper x hx)
  refine ⟨R, B, max B₁ (2 * B), B₁,
    { toIsVorticityHistory := IsVorticityHistory.of_fderivWithin_le
        (fun t ht ↦ (hc t ht).contDiffOn) (fun t ht x hx hxR ↦ (hR t ht x hx hxR).1) hB
        (fun t ht x hx ↦ by rw [hfd t ht hx]; exact hB₁ t ht x hx) hu hα0 hα1
      contDiffOn := fun t ht ↦ (hc t ht).contDiffOn
      norm_fderivWithin_le := fun t ht x hx ↦ by rw [hfd t ht hx]; exact hB₁ t ht x hx
      holder_fderivWithin := hM₁
      uniform_fderivWithin := fun t ht ε hε ↦ ?_ }⟩
  obtain ⟨δ, hδ, hδε⟩ := hu₁ t ht ε hε
  exact ⟨δ, hδ, fun s hs hst x hx ↦ by rw [hfd s hs hx, hfd t ht hx]; exact hδε s hs hst x hx⟩

section Bridge

variable {α R₀ B M B₁ M₁ : ℝ} {K : ℝ≥0}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R₀ B M B₁ M₁)
  (hα : 0 < α) (hα1 : α < 1)

omit h hb hI hv in
include hω hα hα1 in
/-- The velocity field of the vorticity history is a `C²` field. -/
theorem isC2FieldOn_historyField :
    ∃ K₁ K₂ : ℝ≥0, IsC2FieldOn (historyField fun t x ↦ sol.vorticity x t)
      (historyFieldDeriv fun t x ↦ sol.vorticity x t)
      (historyFieldDeriv₂ fun t x ↦ sol.vorticity x t) 0 b K₁ K₂ :=
  ⟨_, _, hω.isC2FieldOn hα hα1⟩

omit h hb hI hv hα hα1 in
include hω in
/-- The flow of the velocity field of the history keeps the closed half-plane. -/
theorem mapsTo_flowOn_historyField {K₁ : ℝ≥0}
    (hv₁ : IsLipschitzFieldOn (historyField fun t x ↦ sol.vorticity x t) 0 b K₁) :
    ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      MapsTo (flowOn (historyField fun t x ↦ sol.vorticity x t) 0 b s t) H̄ H̄ :=
  fun _ hs _ ht ↦ (hv₁.bijOn_flowOn_nonneg (j := 1)
    (fun _ hr _ hx ↦ historyField_normal_eq_zero hω.toIsVorticityHistory hr hx) hs ht).mapsTo

omit h hb hI hv hω hα hα1 in
/-- On the closed half-plane the velocity field of the solution is the velocity field of its
vorticity history. -/
theorem velocityField_eq_historyField (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
    velocityField sol r y = historyField (fun t x ↦ sol.vorticity x t) r y := by
  rw [velocityField, extendedVelocity_of_nonneg 1 _ hy, historyField_of_nonneg _ r hy]

include h hb hI hω hα hα1 in
/-- On the closed half-plane the derivatives of the two velocity fields agree. -/
theorem velocityFieldDeriv_eq_historyFieldDeriv {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    velocityFieldDeriv sol r y = historyFieldDeriv (fun t x ↦ sol.vorticity x t) r y := by
  rw [h.velocityFieldDeriv_eq hb hI hr hy]
  exact (fderiv_extendedVelocity_of_nonneg (by norm_num)
    (hω.contDiffOn_halfPlaneVelocity_two hα hα1 hr) hy).symm

omit h hb hI hα hα1 in
include hv hω in
/-- **The two flows agree** on the closed half-plane. -/
theorem flowOn_eq_historyField {K₁ : ℝ≥0}
    (hv₁ : IsLipschitzFieldOn (historyField fun t x ↦ sol.vorticity x t) 0 b K₁) {s t : ℝ}
    (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    flowOn (velocityField sol) 0 b s t x =
      flowOn (historyField fun t x ↦ sol.vorticity x t) 0 b s t x :=
  flowOn_eq_of_eqOn hv.isLipschitzFieldOn hv₁ (mapsTo_flowOn_historyField hω hv₁)
    (fun r _ _ hy ↦ velocityField_eq_historyField r hy) hs ht hx

include h hb hI hv hω hα hα1 in
/-- **The two first variations agree** on the closed half-plane. -/
theorem variationOn_eq_historyField {K₁ : ℝ≥0}
    (hv₁ : IsC1FieldOn (historyField fun t x ↦ sol.vorticity x t)
      (historyFieldDeriv fun t x ↦ sol.vorticity x t) 0 b K₁) {s t : ℝ}
    (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s t x =
      variationOn (historyField fun t x ↦ sol.vorticity x t)
        (historyFieldDeriv fun t x ↦ sol.vorticity x t) 0 b s t x :=
  hv.variationOn_eq_of_eqOn hv₁ (mapsTo_flowOn_historyField hω hv₁.isLipschitzFieldOn)
    (fun r _ _ hy ↦ velocityField_eq_historyField r hy)
    (fun _ hr _ hy ↦ h.velocityFieldDeriv_eq_historyFieldDeriv hb hI hω hα hα1 hr hy) hs ht hx

end Bridge

section Hessian

variable {α R₀ B M B₁ M₁ Rq Nq : ℝ} {K K₁ K₂ : ℝ≥0}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R₀ B M B₁ M₁)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (historyField fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv₂ fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)

omit hα hα1 in
include h hb hI hv hω hv₂ in
/-- The temperature is carried by the flow of the velocity field of the history. -/
theorem temperature_flowOn_historyField {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    sol.temperature (flowOn 𝐯 0 b r 0 a) r = sol.temperature a 0 := by
  rw [← flowOn_eq_historyField hv hω hv₂.toIsC1FieldOn.isLipschitzFieldOn hr ⟨le_rfl, hb.le⟩ ha]
  exact h.temperature_trajectory hb hI hv ha hr

omit hα hα1 in
include h hb hI hv hω hv₂ in
/-- **The gradient identity within the closed half-plane** along the flow of the history:
`Dθ_r(Φ(r, y)) ∘ J(r, y) = Dθ₀(y)` for derivatives within `H̄`. -/
theorem fderivWithin_temperature_flowOn_comp {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y)).comp
        (variationOn 𝐯 𝐃𝐯 0 b r 0 y) =
      fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ y := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hΦH := mapsTo_flowOn_historyField hω hv₂.toIsC1FieldOn.isLipschitzFieldOn r hr 0 h0
  have hθr := (h.contDiff_temperature (hI hr)).contDiffOn (s := H̄)
  have hθ0 := (h.contDiff_temperature (hI h0)).contDiffOn (s := H̄)
  have hc : HasFDerivWithinAt (fun x ↦ sol.temperature (flowOn 𝐯 0 b r 0 x) r)
      ((fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y)).comp
        (variationOn 𝐯 𝐃𝐯 0 b r 0 y)) H̄ y :=
    ((hθr.differentiableOn (by norm_num) _ (hΦH hy)).hasFDerivWithinAt).comp y
      (hv₂.toIsC1FieldOn.hasFDerivAt_flowOn hr h0 y).hasFDerivWithinAt hΦH
  have hc' := hc.congr (fun z hz ↦ (h.temperature_flowOn_historyField hb hI hv hω hv₂ hr hz).symm)
    (h.temperature_flowOn_historyField hb hI hv hω hv₂ hr hy).symm
  exact (uniqueDiffOn_closedUpper y hy).eq hc'
    (hθ0.differentiableOn (by norm_num) y hy).hasFDerivWithinAt

include h hb hI hv hω hv₂ hreg in
omit hα hα1 in
/-- **The Hessian identity along the flow of the history:**
`D²θ_r(Φ)[J u, J w] + Dθ_r(Φ)(S[u, w]) = D²θ₀(a)[u, w]`, for derivatives within the closed
half-plane, with `J` and `S` the first and second variations of `Φ = Φ(r, ·)` at `a`. -/
theorem hessian_flowOn_comp {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1)
    (u w : ℝ^2) :
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ (flowOn 𝐯 0 b r 0 a)
        (variationOn 𝐯 𝐃𝐯 0 b r 0 a u) (variationOn 𝐯 𝐃𝐯 0 b r 0 a w) +
      fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 a)
        (secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b r 0 a u w) =
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a u w := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hΦH := mapsTo_flowOn_historyField hω hv₂.toIsC1FieldOn.isLipschitzFieldOn r hr 0 h0
  have hθr := (hreg r hr).temperature_contDiffOn
  have hθ0 := (hreg 0 h0).temperature_contDiffOn
  have hDθr : ContDiffOn ℝ 1 (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ :=
    hθr.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hDθ0 : ContDiffOn ℝ 1 (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ :=
    hθ0.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hc2 : HasFDerivWithinAt
      (fun y ↦ fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y))
      ((fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄
        (flowOn 𝐯 0 b r 0 a)).comp (variationOn 𝐯 𝐃𝐯 0 b r 0 a)) H̄ a :=
    ((hDθr.differentiableOn one_ne_zero _ (hΦH ha)).hasFDerivWithinAt).comp a
      (hv₂.toIsC1FieldOn.hasFDerivAt_flowOn hr h0 a).hasFDerivWithinAt hΦH
  have hd2 := (hv₂.hasFDerivAt_variationOn hr h0 a).hasFDerivWithinAt (s := H̄)
  have hprod := hc2.clm_comp hd2
  have hprod' := hprod.congr
    (fun y hy ↦ (h.fderivWithin_temperature_flowOn_comp hb hI hv hω hv₂ hr hy).symm)
    (h.fderivWithin_temperature_flowOn_comp hb hI hv hω hv₂ hr ha).symm
  have heq := (uniqueDiffOn_closedUpper a ha).eq hprod'
    (hDθ0.differentiableOn one_ne_zero a ha).hasFDerivWithinAt
  have happ := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ ↦ L u w) heq
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] at happ
  rw [← happ, add_comm]

omit hα hα1 in
include h hb hI hv hω hv₂ in
/-- The gradient of the temperature at `Φ(r, a)` is `Dθ₀(a) ∘ W`, with `W` the inverse first
variation. -/
theorem fderivWithin_temperature_flowOn {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 a) =
      (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a).comp
        (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  rw [← h.fderivWithin_temperature_flowOn_comp hb hI hv hω hv₂ hr ha,
    ContinuousLinearMap.comp_assoc, hv₂.toIsC1FieldOn.variationOn_comp_variationOn_flowOn hr h0 a,
    ContinuousLinearMap.comp_id]

omit hα hα1 in
include h hb hI hv hω hv₂ hreg in
/-- **The closed form of the Hessian along the flow:** with `W` the inverse first variation and
`S` the second variation, `H[u, w] = D²θ₀(a)[W u, W w] - Dθ₀(a)(W S[W u, W w])`. -/
theorem hessian_flowOn_eq {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) (u w : ℝ^2) :
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ (flowOn 𝐯 0 b r 0 a) u w =
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) u)
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) w) -
        fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)
            (secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b r 0 a
              (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) u)
              (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) w))) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set W := variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)
  have hJW (x : ℝ^2) : variationOn 𝐯 𝐃𝐯 0 b r 0 a (W x) = x := by
    have := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L x)
      (hv₂.toIsC1FieldOn.variationOn_comp_variationOn_flowOn hr h0 a)
    simpa using this
  have hH := h.hessian_flowOn_comp hb hI hv hω hv₂ hreg hr ha (W u) (W w)
  rw [hJW, hJW, h.fderivWithin_temperature_flowOn hb hI hv hω hv₂ hr ha] at hH
  rw [← hH, ContinuousLinearMap.comp_apply]
  ring

omit hα hα1 in
include h hI hv hω hv₂ hreg in
/-- **The equation of the Hessian of the temperature along the flow:**
`∂ᵣ H = -H[Du ·, ·] - H[·, Du ·] - Dθ_r(Φ) ∘ D²u` with `H(r) = D²θ_r(Φ(r, a))`,
`Du = Dv(r, Φ(r, a))` and `D²u = D²v(r, Φ(r, a))`. The second variation has cancelled. -/
theorem hasDerivWithinAt_hessian {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt (fun ρ ↦ 𝐇 ρ a)
      (hessianTransport (𝐇 r a) (𝐃𝐯 r (𝐗 r a)) (𝐆 r a) (𝐃²𝐯 r (𝐗 r a))) (Icc 0 b) r := by
  rcases (hr.1.trans hr.2).eq_or_lt with hb0 | hb
  · exact HasFDerivWithinAt.of_subsingleton (by rw [← hb0, Icc_self]; exact subsingleton_singleton)
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  set W : ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (flowOn 𝐯 0 b ρ 0 a)
  set S : ℝ → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b ρ 0 a
  set J : ℝ^2 →L[ℝ] ℝ^2 := variationOn 𝐯 𝐃𝐯 0 b r 0 a
  set T := fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a
  set Q := fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a
  set Dv := 𝐃𝐯 r (flowOn 𝐯 0 b r 0 a)
  set D2v := 𝐃²𝐯 r (flowOn 𝐯 0 b r 0 a)
  have hJW (x : ℝ^2) : J (W r x) = x := by
    have := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L x)
      (hv₁.variationOn_comp_variationOn_flowOn hr h0 a)
    simpa using this
  have hW : HasDerivWithinAt W (-(W r).comp Dv) (Icc 0 b) r :=
    hv₁.hasDerivWithinAt_variationOn_inverse hr h0 a
  have hS : HasDerivWithinAt S ((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2) (ℝ^2) Dv).comp (S r) +
      secondVariationForcing D2v J) (Icc 0 b) r := hv₂.hasDerivWithinAt_secondVariationOn hr h0 a
  refine hasDerivWithinAt_of_forall_apply_apply fun u w ↦ ?_
  have hWu := hW.clm_apply (hasDerivWithinAt_const r (Icc 0 b) u)
  have hWw := hW.clm_apply (hasDerivWithinAt_const r (Icc 0 b) w)
  have hQ := (Q.hasFDerivAt.comp_hasDerivWithinAt r hWu).clm_apply hWw
  have hSm := (hS.clm_apply hWu).clm_apply hWw
  have hT := T.hasFDerivAt.comp_hasDerivWithinAt r (hW.clm_apply hSm)
  have hf := hQ.sub hT
  have hcongr : ∀ ρ ∈ Icc 0 b,
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (flowOn 𝐯 0 b ρ 0 a) u w =
        Q (W ρ u) (W ρ w) - T (W ρ (S ρ (W ρ u) (W ρ w))) := fun ρ hρ ↦
    h.hessian_flowOn_eq hb hI hv hω hv₂ hreg hρ ha u w
  have hf' : HasDerivWithinAt (fun ρ ↦ fderivWithin ℝ
      (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (flowOn 𝐯 0 b ρ 0 a) u w) _
      (Icc 0 b) r :=
    hf.congr_of_mem (fun ρ hρ ↦ by rw [hcongr ρ hρ]; rfl) hr
  convert hf' using 1
  rw [h.fderivWithin_temperature_flowOn hb hI hv hω hv₂ hr ha]
  simp only [hessianTransport, sub_apply, neg_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    h.hessian_flowOn_eq hb hI hv hω hv₂ hreg hr ha, add_apply, map_add, map_neg, map_zero,
    add_zero, secondVariationForcing_apply, hJW]
  ring

include h hb hI hv hω hα hα1 hv₂ hreg in
/-- **The vorticity in label form along the flow of the history.** On the closed half-plane the
vorticity at time `r` is the amplitude `ω̃₀(Y) + ∫₀ʳ Dθ̃₀(Y)(W e₀) dρ` at the label
`Y = Φ(0, r, x)`, with `ω̃₀`, `θ̃₀` the extended data. -/
theorem vorticity_eq_forcedAmplitude {r : ℝ} (hr : r ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x r = forcedAmplitude (dataVorticity fun y ↦ sol.vorticity y 0)
      (labelForcing 𝐯 𝐃𝐯 0 b (dataTemperature fun y ↦ sol.temperature y 0)
        (EuclideanSpace.single 0 1)) (flowOn 𝐯 0 b 0 r x) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv.isLipschitzFieldOn
  have hθ₀d : Differentiable ℝ (fun y ↦ sol.temperature y 0) :=
    (h.contDiff_temperature (hI h0)).differentiable one_ne_zero
  have hY : label sol b x r = flowOn 𝐯 0 b 0 r x :=
    flowOn_eq_historyField hv hω hv₁.isLipschitzFieldOn h0 hr hx
  have hYm : 0 ≤ label sol b x r 1 := h.label_mem hI hL hr hx
  rw [h.vorticity_eq_label hb hI hv hr hx, forcedAmplitude, ← hY, dataVorticity_of_nonneg _ hYm]
  congr 1
  refine intervalIntegral.integral_congr fun ρ hρ ↦ ?_
  have hρ' : ρ ∈ Icc 0 b := by
    rw [uIcc_of_le hr.1] at hρ
    exact ⟨hρ.1, hρ.2.trans hr.2⟩
  have hX : trajectory sol b ρ (label sol b x r) = flowOn 𝐯 0 b ρ 0 (label sol b x r) :=
    flowOn_eq_historyField hv hω hv₁.isLipschitzFieldOn hρ' h0 hYm
  have hXm := h.trajectory_mem hI hL hρ' hYm
  simp only [labelForcing]
  rw [h.variationOn_eq_historyField hb hI hv hω hα hα1 hv₁ h0 hρ' hXm, hX,
    (hreg 0 h0).fderiv_dataTemperature hYm, fderiv_eq_fderivWithin hθ₀d hYm]

include h hb hI hv hω hα hα1 hv₂ hreg in
/-- **The gradient of the vorticity in label form:** on the closed half-plane,
`Dω_r(x) = (Dω̃₀(Y) + ∫₀ʳ ∂_Y labelForcing(Y, ρ) dρ) ∘ D_x Y` with `Y = Φ(0, r, x)`. -/
theorem fderivWithin_vorticity_eq {r : ℝ} (hr : r ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (fun y ↦ sol.vorticity y r) H̄ x =
      (fderiv ℝ (dataVorticity fun y ↦ sol.vorticity y 0) (flowOn 𝐯 0 b 0 r x) +
        ∫ ρ in (0)..r, labelForcingDeriv 𝐯 𝐃𝐯 𝐃²𝐯 0 b
          (dataTemperature fun y ↦ sol.temperature y 0) (EuclideanSpace.single 0 1)
          (flowOn 𝐯 0 b 0 r x) ρ).comp (variationOn 𝐯 𝐃𝐯 0 b 0 r x) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hd := hreg 0 h0
  have hθ := hd.contDiff_dataTemperature
  have hF := (hasFDerivAt_forcedAmplitude
      (G := labelForcing 𝐯 𝐃𝐯 0 b (dataTemperature fun y ↦ sol.temperature y 0)
        (EuclideanSpace.single 0 1))
      hd.contDiff_dataVorticity.differentiable_one
      (continuousOn_labelForcing hv₁ h0 (hθ.of_le (by norm_num)))
      (fun ρ hρ y ↦ hasFDerivAt_labelForcing hv₂ h0 hθ hρ y)
      (continuousOn_labelForcingDeriv hv₂ h0 hθ) h0 hr (flowOn 𝐯 0 b 0 r x)).comp x
    (hv₁.hasFDerivAt_flowOn h0 hr x)
  exact (hF.hasFDerivWithinAt.congr
    (fun y hy ↦ h.vorticity_eq_forcedAmplitude hb hI hv hω hα hα1 hv₂ hreg hr hy)
    (h.vorticity_eq_forcedAmplitude hb hI hv hω hα hα1 hv₂ hreg hr hx)).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

include h hb hI hv hω hα hα1 hv₂ hreg in
/-- **The equation of the gradient of the vorticity along the flow:** with
`Z(r) = Dω_r(Φ(r, a))`, `H(r) = D²θ_r(Φ(r, a))` and `Du = Dv(r, Φ(r, a))`,
`∂ᵣ Z = H[·, e₀] - Z ∘ Du`. -/
theorem hasDerivWithinAt_vorticityGradient {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt
      (fun ρ ↦ fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (flowOn 𝐯 0 b ρ 0 a))
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2)).comp
          (fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄
            (flowOn 𝐯 0 b r 0 a)) -
        (fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ (flowOn 𝐯 0 b r 0 a)).comp
          (𝐃𝐯 r (flowOn 𝐯 0 b r 0 a))) (Icc 0 b) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv₁.isLipschitzFieldOn
  have hd := hreg 0 h0
  have hθ := hd.contDiff_dataTemperature
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set G : ℝ → ℝ^2 →L[ℝ] ℝ := fun ρ ↦ labelForcingDeriv 𝐯 𝐃𝐯 𝐃²𝐯 0 b
    (dataTemperature fun y ↦ sol.temperature y 0) e a ρ
  set P : ℝ → ℝ^2 →L[ℝ] ℝ := fun ρ ↦
    fderiv ℝ (dataVorticity fun y ↦ sol.vorticity y 0) a + ∫ σ in (0)..ρ, G σ
  set W : ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (flowOn 𝐯 0 b ρ 0 a)
  have hGc : ContinuousOn G (Icc 0 b) :=
    (continuousOn_labelForcingDeriv (e := e) hv₂ h0 hθ).comp (f := fun ρ : ℝ ↦ (a, ρ))
      (continuousOn_const.prodMk continuousOn_id) fun ρ hρ ↦ ⟨mem_univ _, hρ⟩
  have hP : HasDerivWithinAt P (G r) (Icc 0 b) r := by
    have hu : uIcc (0 : ℝ) b = Icc 0 b := uIcc_of_le hb.le
    have := PDE.Analysis.hasDerivWithinAt_intervalIntegral_uIcc (f := G) (c := 0) (x := r)
      (by rwa [hu]) left_mem_uIcc (by rwa [hu])
    rw [hu] at this
    exact this.const_add _
  have hW : HasDerivWithinAt W (-(W r).comp (𝐃𝐯 r (flowOn 𝐯 0 b r 0 a))) (Icc 0 b) r :=
    hv₁.hasDerivWithinAt_variationOn_inverse hr h0 a
  have hZ : ∀ ρ ∈ Icc 0 b,
      fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (flowOn 𝐯 0 b ρ 0 a) = (P ρ).comp (W ρ) := by
    intro ρ hρ
    have hΦ := mapsTo_flowOn_historyField hω hL ρ hρ 0 h0 ha
    simp only [P, W, G]
    rw [h.fderivWithin_vorticity_eq hb hI hv hω hα hα1 hv₂ hreg hρ hΦ, flowOn_zero_flowOn hL h0 hρ]
  have hPW := (hP.clm_comp hW).congr_of_mem (fun ρ hρ ↦ hZ ρ hρ) hr
  convert hPW using 1
  have hGW : (G r).comp (W r) = (ContinuousLinearMap.apply ℝ ℝ e).comp
      (fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄
        (flowOn 𝐯 0 b r 0 a)) := by
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [G, W, labelForcingDeriv, sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.apply_apply,
      h.hessian_flowOn_eq hb hI hv hω hv₂ hreg hr ha u e, hd.fderiv_fderiv_dataTemperature ha,
      hd.fderiv_dataTemperature ha]
  rw [hZ r hr, hGW, ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc]
  abel

omit hα hα1 in
include h hb hI hv hω hv₂ in
/-- The temperature gradient along a trajectory is continuous in time. -/
theorem continuousOn_gradient_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐆 ρ a) (Icc 0 b) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hW : ContinuousOn (fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (𝐗 ρ a)) (Icc 0 b) := fun ρ hρ ↦
    (hv₂.toIsC1FieldOn.hasDerivWithinAt_variationOn_inverse hρ h0 a).hasFDerivWithinAt
      |>.continuousWithinAt
  have hc : ContinuousOn (fun ρ ↦ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a).comp
      (variationOn 𝐯 𝐃𝐯 0 b 0 ρ (𝐗 ρ a))) (Icc 0 b) := continuousOn_const.clm_comp hW
  intro ρ hρ
  have heq := h.fderivWithin_temperature_flowOn hb hI hv hω hv₂ hρ ha
  exact (hc ρ hρ).congr (fun σ hσ ↦ h.fderivWithin_temperature_flowOn hb hI hv hω hv₂ hσ ha)
    heq

omit h hb hI hv hω hreg hα hα1 in
include hb hv₂ in
/-- The second derivative of the field along a trajectory is continuous in time. -/
theorem continuousOn_deriv₂_flowOn (a : ℝ^2) :
    ContinuousOn (fun ρ ↦ 𝐃²𝐯 ρ (𝐗 ρ a)) (Icc 0 b) :=
  hv₂.continuousOn_deriv₂.comp (f := fun ρ ↦ (ρ, 𝐗 ρ a)) (continuousOn_id.prodMk
    (hv₂.toIsC1FieldOn.isLipschitzFieldOn.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a))
    fun _ hρ ↦ ⟨hρ, mem_univ _⟩

omit hα hα1 in
include h hI hv hω hv₂ hreg in
/-- The Hessian of the temperature along a trajectory is continuous in time. -/
theorem continuousOn_hessian_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐇 ρ a) (Icc 0 b) := by
  intro ρ hρ
  exact (h.hasDerivWithinAt_hessian hI hv hω hv₂ hreg ha hρ).hasFDerivWithinAt
    |>.continuousWithinAt

include h hb hI hv hω hα hα1 hv₂ hreg in
/-- The vorticity gradient along a trajectory is continuous in time. -/
theorem continuousOn_vorticityGradient_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐙 ρ a) (Icc 0 b) := by
  intro ρ hρ
  exact (h.hasDerivWithinAt_vorticityGradient hb hI hv hω hα hα1 hv₂ hreg ha hρ).hasFDerivWithinAt
    |>.continuousWithinAt

end Hessian

end IsSolutionOn

end Boussinesq.HalfPlane
