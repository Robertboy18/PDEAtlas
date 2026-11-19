/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ImplicitFunction
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Regular local characteristic flows

Evans solves `F(Du, u, x) = 0` near a noncharacteristic boundary point by
integrating the characteristic system

`ẋ = D_pF`, `ż = ⟪D_pF, p⟫`, `ṗ = -D_xF - F_z p`

from compatible boundary data `(boundary y, data y, initialGradient y)`. The
structure `LocalCharacteristicFlow` describes such a family: `C¹`
maps `xmap`, `pmap`, `zmap` on a flow box `W × (-ε, ε)` that satisfy the
three characteristic equations, take the prescribed initial values, and obey
the linearized contact ODE together with a uniform bound on its coefficient
`F_z`.

Two identities are derived from these fields. The
contact defect `∂_y z - ⟪p, ∂_y x⟫` vanishes identically: it is zero at
`s = 0` by the compatibility conditions and solves a homogeneous linear ODE,
so ODE uniqueness forces it to stay zero. The residual `F(p, z, x)` vanishes
along the flow for the same reason. Together they give `dz = ⟪p, dx⟫` on the
flow box, which is the statement that `p` is the gradient of the solution
once `xmap` has been inverted. These are steps 2 and 3 of the proof of Theorem 2 in Evans,
§3.2.4, equations (39)-(40) and (42)-(48).

## Main results

* `contactDefect`, `contactDefect_initial_eq_zero`, `contactDefect_eq_zero`:
  the contact defect vanishes on the whole flow box.
* `residual_eq_zero`: the residual `F(p, z, x)` vanishes on the flow box.
* `fderiv_zmap_eq_inner_fderiv_xmap`: the differential of `zmap` is the
  pullback of the covector `pmap` through `xmap`.
* `hasFDerivAt_xmap_initial`: at `s = 0` the derivative of `xmap` is the
  boundary-tangent/characteristic-direction map
  `characteristicInitialDerivative`, whose invertibility is the
  noncharacteristic condition fed to the inverse function theorem.

## Implementation notes

The flow maps are total functions on `ℝ^k × ℝ`; every analytic hypothesis and
conclusion is restricted to the open box `W ×ˢ Ioo (-ε) ε`. The domain is
`SpaceTime k`, of dimension `k + 1`, so the boundary parameter `y ∈ ℝ^k` has
one fewer dimension than the position `x`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, equations (31)-(36); §3.2.4, Lemma 2 and the proof of
  Theorem 2, equations (39)-(48).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open scoped Topology RealInnerProductSpace NNReal
open Set

variable {k : ℕ}

/-- The contact defect of a characteristic family in a boundary direction.

For a solution this is
`∂_y z - p · ∂_y x`.  Evans proves that it satisfies a homogeneous
linear ODE and therefore remains zero when the initial compatibility
condition holds. -/
noncomputable def contactDefect
    (xmap : (ℝ^k × ℝ) → SpaceTime k) (pmap : (ℝ^k × ℝ) → SpaceTime k) (zmap : (ℝ^k × ℝ) → ℝ)
    (y : ℝ^k) (s : ℝ) (dy : ℝ^k) : ℝ :=
  fderiv ℝ zmap (y, s) (dy, 0) -
    (innerSL ℝ (pmap (y, s))) (fderiv ℝ xmap (y, s) (dy, 0))

/-- A regular local characteristic flow box for Evans's system (11),
repeated as (31) in the boundary-data construction.

The fields `xmap`, `pmap`, and `zmap` are defined on all of `ℝ^k × ℝ`,
as is customary for total Lean functions, while every analytic assertion
is restricted to the open box `W × (-ε,ε)`.

`contact_evolution` is not the desired gradient identity.  It is the
homogeneous linearized characteristic ODE

`d/ds (z_y - p · x_y) = -F_z (z_y - p · x_y)`,

for a characteristic family whose initial residual vanishes throughout the
boundary-parameter neighborhood.  The constructor
`ofContDiffOneCharacteristicFamily` proves it from compatible data,
residual preservation, and the boundary variation's ODE. The uniform
coefficient bound is the local boundedness needed by ODE uniqueness; the
main theorem obtains it automatically after shrinking the box. -/
structure LocalCharacteristicFlow
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (initialGradient : ℝ^k → SpaceTime k) where
  /-- Open boundary-parameter neighborhood. -/
  W : Set (ℝ^k)
  /-- The base boundary parameter belongs to `W`. -/
  isOpen_W : IsOpen W
  /-- Symmetric lifespan of the flow. -/
  ε : Set.Ioi (0 : ℝ)
  /-- Characteristic position. -/
  xmap : (ℝ^k × ℝ) → SpaceTime k
  /-- Characteristic momentum. -/
  pmap : (ℝ^k × ℝ) → SpaceTime k
  /-- Characteristic height. -/
  zmap : (ℝ^k × ℝ) → ℝ
  /-- Position is `C¹` on the flow box. -/
  x_contDiff : ContDiffOn ℝ 1 xmap (W ×ˢ Ioo (-(ε : ℝ)) (ε : ℝ))
  /-- Momentum is `C¹` on the flow box. -/
  p_contDiff : ContDiffOn ℝ 1 pmap (W ×ˢ Ioo (-(ε : ℝ)) (ε : ℝ))
  /-- Height is `C¹` on the flow box. -/
  z_contDiff : ContDiffOn ℝ 1 zmap (W ×ˢ Ioo (-(ε : ℝ)) (ε : ℝ))
  /-- Initial position is the prescribed boundary. -/
  x_initial : ∀ y ∈ W, xmap (y, 0) = boundary y
  /-- Initial momentum is the compatible gradient selected on the boundary. -/
  p_initial : ∀ y ∈ W, pmap (y, 0) = initialGradient y
  /-- Initial height is the prescribed boundary value. -/
  z_initial : ∀ y ∈ W, zmap (y, 0) = data y
  /-- Position equation in Evans (11), repeated in (31): `x_s = D_p F`. -/
  x_time :
    ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      fderiv ℝ xmap (y, s) (0, 1) =
        momentumGradient (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s))
  /-- Height equation in Evans (11), repeated in (31): `z_s = p · D_p F`. -/
  z_time :
    ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      fderiv ℝ zmap (y, s) (0, 1) =
        ⟪momentumGradient (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s)),
          pmap (y, s)⟫
  /-- Momentum equation in Evans (11), repeated in (31): `p_s = -D_xF-F_zp`. -/
  p_time :
    ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      fderiv ℝ pmap (y, s) (0, 1) =
        -positionGradient (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s)) -
          valueDerivative (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s)) •
            pmap (y, s)
  /-- First-variation/contact ODE obtained by differentiating system (31) in `y`. -/
  contact_evolution :
    ∀ y ∈ W, ∀ dy : ℝ^k, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt
        (fun τ ↦ contactDefect xmap pmap zmap y τ dy)
        (-valueDerivative (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s)) *
          contactDefect xmap pmap zmap y s dy) s
  /-- A uniform local bound for the coefficient in the contact ODE. -/
  contactBound : ℝ≥0
  /-- The coefficient bound on the flow box. -/
  norm_DzF_le :
    ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      ‖valueDerivative (n := k + 1) F (pmap (y, s)) (zmap (y, s)) (xmap (y, s))‖ ≤
        contactBound

namespace LocalCharacteristicFlow

variable {F : SpaceTime k → ℝ → SpaceTime k → ℝ}
  {boundary : ℝ^k → SpaceTime k} {data : ℝ^k → ℝ}
  {initialGradient : ℝ^k → SpaceTime k}

/-- Time zero lies in the symmetric lifespan `(-ε, ε)` of the flow. -/
theorem zero_mem_time (flow : LocalCharacteristicFlow F boundary data initialGradient) :
    (0 : ℝ) ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ) :=
  ⟨neg_lt_zero.mpr flow.ε.property, flow.ε.property⟩

/-- The flow box `W × (-ε, ε)` is open. -/
theorem box_open (flow : LocalCharacteristicFlow F boundary data initialGradient) :
    IsOpen (flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :=
  flow.isOpen_W.prod isOpen_Ioo

/-- The flow maps are differentiable at every point of the open flow box. -/
theorem differentiableAt_xmap (flow : LocalCharacteristicFlow F boundary data initialGradient)
    {q : (ℝ^k × ℝ)} (hq : q ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    DifferentiableAt ℝ flow.xmap q :=
  (flow.x_contDiff.contDiffAt (flow.box_open.mem_nhds hq)).differentiableAt (by simp)

/-- The momentum map is differentiable throughout the flow box. -/
theorem differentiableAt_pmap (flow : LocalCharacteristicFlow F boundary data initialGradient)
    {q : (ℝ^k × ℝ)} (hq : q ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    DifferentiableAt ℝ flow.pmap q :=
  (flow.p_contDiff.contDiffAt (flow.box_open.mem_nhds hq)).differentiableAt (by simp)

/-- The height map is differentiable throughout the flow box. -/
theorem differentiableAt_zmap (flow : LocalCharacteristicFlow F boundary data initialGradient)
    {q : (ℝ^k × ℝ)} (hq : q ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    DifferentiableAt ℝ flow.zmap q :=
  (flow.z_contDiff.contDiffAt (flow.box_open.mem_nhds hq)).differentiableAt (by simp)

/-- On the initial slice, the boundary derivative of a flow map is the derivative of the
initial data it restricts to. -/
private theorem fderiv_initial_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (flow : LocalCharacteristicFlow F boundary data initialGradient) {g : (ℝ^k × ℝ) → G}
    {b : ℝ^k → G} {y : ℝ^k} (hy : y ∈ flow.W) (hg : DifferentiableAt ℝ g (y, 0))
    (hgb : ∀ η ∈ flow.W, g (η, 0) = b η) (dy : ℝ^k) :
    fderiv ℝ g (y, 0) (dy, 0) = fderiv ℝ b y dy := by
  rw [← fderiv_boundary_slice g y 0 hg dy]
  have h : (fun η ↦ g (η, 0)) =ᶠ[nhds y] b := (flow.isOpen_W.eventually_mem hy).mono hgb
  exact congrArg (· dy) (h.fderiv_eq (𝕜 := ℝ))

/-- Evans's compatibility equations make the initial contact defect vanish. -/
theorem contactDefect_initial_eq_zero
    (flow : LocalCharacteristicFlow F boundary data initialGradient) {y : ℝ^k} (hy : y ∈ flow.W)
    (hcompat : IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) (dy : ℝ^k) :
    contactDefect flow.xmap flow.pmap flow.zmap y 0 dy = 0 := by
  have hq : (y, (0 : ℝ)) ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ) := ⟨hy, flow.zero_mem_time⟩
  simp only [contactDefect, flow.p_initial y hy,
    flow.fderiv_initial_slice hy (flow.differentiableAt_xmap hq) flow.x_initial,
    flow.fderiv_initial_slice hy (flow.differentiableAt_zmap hq) flow.z_initial]
  exact sub_eq_zero.mpr (hcompat.2 dy)

/-- The contact defect remains zero throughout the characteristic flow box.

This is the ODE-uniqueness step in Evans, §3.2.4.  It proves the pulled-back
differential identity needed to recover `Du=p`. -/
theorem contactDefect_eq_zero (flow : LocalCharacteristicFlow F boundary data initialGradient)
    {y : ℝ^k} (hy : y ∈ flow.W)
    (hcompat : IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) (dy : ℝ^k)
    {s : ℝ} (hs : s ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    contactDefect flow.xmap flow.pmap flow.zmap y s dy = 0 := by
  let coefficient : ℝ → ℝ := fun τ ↦
    valueDerivative (n := k + 1) F (flow.pmap (y, τ)) (flow.zmap (y, τ)) (flow.xmap (y, τ))
  have hLip (τ) (hτ : τ ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
      LipschitzOnWith flow.contactBound (fun r ↦ -coefficient τ * r) (Set.univ : Set ℝ) := by
    refine LipschitzWith.lipschitzOnWith (lipschitzWith_iff_dist_le_mul.2 fun a b ↦ ?_)
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (flow.norm_DzF_le y hy τ hτ) (abs_nonneg _)
  have hUnique := ODE_solution_unique_of_mem_Ioo (v := fun τ r ↦ -coefficient τ * r)
    (s := fun _ ↦ (Set.univ : Set ℝ)) (g := fun _ ↦ (0 : ℝ)) hLip flow.zero_mem_time
    (fun τ hτ ↦ ⟨flow.contact_evolution y hy dy τ hτ, trivial⟩)
    (fun τ _ ↦ ⟨by simpa using hasDerivAt_const τ (0 : ℝ), trivial⟩)
    (flow.contactDefect_initial_eq_zero hy hcompat dy)
  exact hUnique hs

/-- The residual has zero derivative along every characteristic. -/
theorem hasDerivAt_residual_zero (flow : LocalCharacteristicFlow F boundary data initialGradient)
    (hF : ContDiff ℝ 1 (phaseFunction (n := k + 1) F)) {y : ℝ^k} (hy : y ∈ flow.W) {s : ℝ}
    (hs : s ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    HasDerivAt (fun τ ↦ F (flow.pmap (y, τ)) (flow.zmap (y, τ)) (flow.xmap (y, τ))) 0 s := by
  have hq : (y, s) ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ) := ⟨hy, hs⟩
  have hins : DifferentiableAt ℝ (fun τ : ℝ ↦ (y, τ)) s :=
    (differentiableAt_const y).prodMk differentiableAt_id
  have hpDiff := (flow.differentiableAt_pmap hq).comp s hins
  have hzDiff := (flow.differentiableAt_zmap hq).comp s hins
  have hxDiff := (flow.differentiableAt_xmap hq).comp s hins
  have hzero := deriv_residual_along_characteristic_eq_zero (n := k + 1) (F := F)
    (p := fun τ ↦ flow.pmap (y, τ)) (xcurve := fun τ ↦ flow.xmap (y, τ))
    (z := fun τ ↦ flow.zmap (y, τ)) s (hF.contDiffAt.differentiableAt (by norm_num)) hpDiff hzDiff
    hxDiff ((deriv_time_slice flow.pmap y s (flow.differentiableAt_pmap hq)).trans
      (flow.p_time y hy s hs)) ((deriv_time_slice flow.zmap y s
        (flow.differentiableAt_zmap hq)).trans (flow.z_time y hy s hs))
    ((deriv_time_slice flow.xmap y s (flow.differentiableAt_xmap hq)).trans (flow.x_time y hy s hs))
  exact (((hF.contDiffAt.differentiableAt (by norm_num)).comp s
    (hpDiff.prodMk (hzDiff.prodMk hxDiff))).hasDerivAt :
      HasDerivAt (fun τ ↦ F (flow.pmap (y, τ)) (flow.zmap (y, τ)) (flow.xmap (y, τ))) _ s
    ).congr_deriv hzero

/-- Compatible initial residual data remain on `F=0` along the flow. -/
theorem residual_eq_zero (flow : LocalCharacteristicFlow F boundary data initialGradient)
    (hF : ContDiff ℝ 1 (phaseFunction (n := k + 1) F)) {y : ℝ^k} (hy : y ∈ flow.W)
    (hcompat : IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) {s : ℝ}
    (hs : s ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) :
    F (flow.pmap (y, s)) (flow.zmap (y, s)) (flow.xmap (y, s)) = 0 := by
  have hd (τ) (hτ : τ ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) := flow.hasDerivAt_residual_zero hF hy hτ
  rw [isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun τ hτ ↦ (hd τ hτ).differentiableAt.differentiableWithinAt) (fun τ hτ ↦ (hd τ hτ).deriv) hs
    flow.zero_mem_time, flow.p_initial y hy, flow.z_initial y hy, flow.x_initial y hy]
  exact hcompat.1

/-- The differential of `z` is the pullback of the covector represented by
`p` through the characteristic position map.

This is proved from the tangential contact ODE and the time component of
the characteristic system; it is not a field of the flow structure. -/
theorem fderiv_zmap_eq_inner_fderiv_xmap
    (flow : LocalCharacteristicFlow F boundary data initialGradient) {y : ℝ^k} (hy : y ∈ flow.W)
    (hcompat : IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) {s : ℝ}
    (hs : s ∈ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ)) (dq : (ℝ^k × ℝ)) :
    fderiv ℝ flow.zmap (y, s) dq =
      (innerSL ℝ (flow.pmap (y, s))) (fderiv ℝ flow.xmap (y, s) dq) := by
  rcases dq with ⟨dy, ds⟩
  have htangent : fderiv ℝ flow.zmap (y, s) (dy, 0) =
      (innerSL ℝ (flow.pmap (y, s))) (fderiv ℝ flow.xmap (y, s) (dy, 0)) :=
    sub_eq_zero.mp (by simpa [contactDefect] using flow.contactDefect_eq_zero hy hcompat dy hs)
  have htime : fderiv ℝ flow.zmap (y, s) (0, 1) =
      (innerSL ℝ (flow.pmap (y, s))) (fderiv ℝ flow.xmap (y, s) (0, 1)) := by
    rw [flow.z_time y hy s hs, flow.x_time y hy s hs]
    exact real_inner_comm _ _
  rw [show (dy, ds) = (dy, (0 : ℝ)) + ds • ((0 : ℝ^k), (1 : ℝ)) by ext <;> simp]
  simp only [map_add, map_smul, htangent, htime]

/-- At time zero the derivative of the characteristic position map is
exactly Evans's boundary-tangent/characteristic-direction map. -/
theorem hasFDerivAt_xmap_initial (flow : LocalCharacteristicFlow F boundary data initialGradient)
    {y : ℝ^k} (hy : y ∈ flow.W) :
    HasFDerivAt flow.xmap
      (characteristicInitialDerivative F boundary y (initialGradient y) (data y)) (y, 0) := by
  have hq : (y, (0 : ℝ)) ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ) := ⟨hy, flow.zero_mem_time⟩
  have hxDiff := flow.differentiableAt_xmap hq
  have htime : fderiv ℝ flow.xmap (y, 0) (0, 1) =
      momentumGradient (n := k + 1) F (initialGradient y) (data y) (boundary y) := by
    simpa [flow.p_initial y hy, flow.z_initial y hy, flow.x_initial y hy] using
      flow.x_time y hy 0 flow.zero_mem_time
  refine hxDiff.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun ⟨dy, ds⟩ ↦ ?_)
  rw [show (dy, ds) = (dy, (0 : ℝ)) + ds • ((0 : ℝ^k), (1 : ℝ)) by ext <;> simp]
  simp only [map_add, map_smul, flow.fderiv_initial_slice hy hxDiff flow.x_initial, htime,
    characteristicInitialDerivative_apply]
  simp

end LocalCharacteristicFlow

end

end NonlinearFirstOrder
