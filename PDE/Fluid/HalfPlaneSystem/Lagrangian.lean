/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Solution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.Fluid.Boussinesq.HalfPlane.Lagrangian
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Lagrangian form of solutions of a half-plane system

A classical solution of a half-plane system satisfies its two transport equations pointwise in the
open half-plane. This module turns them into identities along the particle trajectories of its own
velocity: the temperature is constant on them, its gradient moves with the first variation, and the
vorticity is the datum plus the time integral of the forcing. All estimates of the folder use the
solution in this form.

Let `sol` solve the half-plane system with the velocity law `U` and a continuous forcing coefficient
`κ` on the times `I` (`IsSolutionOn U κ R₀ sol I`) and let `[0, b] ⊆ I` with `0 < b`. The velocity
field `velocityField U sol t` is the field `U (ω t)` of the law at the vorticity of the solution,
extended across the boundary by first-order weighted reflection; it is a `C¹` field on `[0, b]`
(`IsSolutionOn.exists_isC1FieldOn`), tangent to the boundary, and on the closed half-plane
`H̄ = {x₂ ≥ 0}` it is the velocity of the solution. Its flow maps `H̄` onto itself. With
`X s a = trajectory U sol b s a` the position at time `s` of the particle with label `a`:

* `IsSolutionOn.temperature_trajectory`: the temperature is carried, `θ(X(s, a), s) = θ(a, 0)`;
* `IsSolutionOn.fderiv_temperature_trajectory_comp`: `Dθ_s(X(s, a)) ∘ D_a X(s, a) = Dθ_0(a)`;
* `IsSolutionOn.partialDeriv_temperature_trajectory`:
  `∂₁θ(X(r, a), r) = Dθ_0(a) (D_a X(r, a)⁻¹ e₁)`, where `D_a X(r, a)⁻¹` is the first variation of
  the flow from time `r` back to time `0`;
* `IsSolutionOn.vorticity_trajectory`:
  `ω(X(s, a), s) = ω(a, 0) + ∫₀ˢ κ(X(r, a)) ∂₁θ(X(r, a), r) dr`.

The equations hold on the open half-plane only; trajectories that start on the boundary stay on it,
and there the transport identities come from the continuity of all terms up to the boundary. The
velocity is never assumed divergence free. The identities are stated on `[0, b]` with the base time
`0`. In this module the coordinates are written `(x₁, x₂)`: `∂₁` is the derivative along the
boundary and `e₁` its direction. The other modules of the folder write `∂₀` and `e₀` for the same
objects.

## Main results

* `velocityField`, `velocityFieldDeriv`, `trajectory`, `label`: the velocity field of a solution on
  the plane, its derivative, the position of a particle and its label.
* `IsSolutionOn.exists_isC1FieldOn`: on a compact interval the velocity field is a `C¹` field.
* `IsSolutionOn.velocityField_eq`, `IsSolutionOn.velocityField_normal_eq_zero`,
  `IsSolutionOn.bijOn_flowOn`, `IsSolutionOn.trajectory_mem`, `IsSolutionOn.label_mem`: on `H̄` the
  field is the velocity of the law, it is tangent to the boundary, and its flow maps `H̄` onto
  itself.
* `IsSolutionOn.temperature_trajectory`, `IsSolutionOn.fderiv_temperature_trajectory_comp`,
  `IsSolutionOn.partialDeriv_temperature_trajectory`, `IsSolutionOn.vorticity_trajectory`: the four
  identities along a trajectory.
* `IsSolutionOn.temperature_eq_label`, `IsSolutionOn.vorticity_eq_label`: the same identities in
  Eulerian form at a point `x ∈ H̄`, with the label of `x` at time `s`.
* `IsSolutionOn.abs_vorticity_trajectory_sub_le`: the Lagrangian vorticity is Lipschitz in the label
  with the gradient bound of the vorticity times `exp (K b)`.
* `IsSolutionOn.exists_vorticity_eq_zero`: at every time the vorticity vanishes on `H̄` outside a
  disc of radius less than `R₀`.

`Uniqueness.lean`, `VorticityBound.lean` and the modules of the a priori estimate are built on these
identities, and `RegularField.lean` uses the support of the vorticity. The library has the same
identities for the Boussinesq system (`Boussinesq.HalfPlane.IsSolutionOn.vorticity_trajectory`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow Boussinesq.HalfPlane
open scoped Topology

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (sol : Fields)

/-- The velocity field of `sol` on the plane: at every time the field of the law at the vorticity,
extended across the boundary by first-order weighted reflection. -/
def velocityField (t : ℝ) : ℝ^2 → ℝ^2 :=
  extendedField 1 (U (fun x ↦ sol.vorticity x t))

/-- The spatial derivative of `velocityField`. -/
def velocityFieldDeriv (t : ℝ) (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (velocityField U sol t) x

/-- The position at time `s` of the particle with label `a` (its position at time `0`), for the
flow of `velocityField U sol` on `[0, b]`. -/
def trajectory (b s : ℝ) (a : ℝ^2) : ℝ^2 :=
  flowOn (velocityField U sol) 0 b s 0 a

/-- The label (the position at time `0`) of the particle at `x` at time `s`. -/
def label (b : ℝ) (x : ℝ^2) (s : ℝ) : ℝ^2 :=
  flowOn (velocityField U sol) 0 b 0 s x

variable {U sol}

/-! ### Trajectories and labels -/

section Trajectory

variable {b : ℝ} {K : NNReal}

/-- The particle with the label of `x` at time `s` is at `x` at time `s`. -/
theorem trajectory_label (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K) (hb : 0 ≤ b)
    {s : ℝ} (hs : s ∈ Icc 0 b) (x : ℝ^2) : trajectory U sol b s (label U sol b x s) = x :=
  hv.flowOn_flowOn_self ⟨le_rfl, hb⟩ hs x

/-- Trajectories solve the equation of the velocity field. -/
theorem hasDerivAt_trajectory (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K)
    (hb : 0 ≤ b) {s : ℝ} (hs : s ∈ Icc 0 b) (a : ℝ^2) :
    HasDerivAt (fun r ↦ trajectory U sol b r a)
      (velocityField U sol s (trajectory U sol b s a)) s :=
  hv.hasDerivAt_flowOn hs ⟨le_rfl, hb⟩ a

/-- Trajectories start at their labels. -/
theorem trajectory_zero (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K) (hb : 0 ≤ b)
    (a : ℝ^2) : trajectory U sol b 0 a = a :=
  hv.flowOn_self ⟨le_rfl, hb⟩ a

end Trajectory

namespace IsSolutionOn

variable {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {I : Set ℝ} {b : ℝ}

/-- At every time of `I` the vorticity vanishes on the closed half-plane outside a disc of radius
less than `R₀`. -/
theorem exists_vorticity_eq_zero (h : IsSolutionOn U κ R₀ sol I) {t : ℝ} (ht : t ∈ I) :
    ∃ R < R₀, ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → sol.vorticity y t = 0 := by
  obtain ⟨R, hR, hz⟩ := h.support t t (by simpa using ht)
  exact ⟨R, hR, fun y hy hyR ↦ (hz t ⟨le_rfl, le_rfl⟩ y hy hyR).1⟩

/-- On compact intervals the velocity field of a solution is a `C¹` field. -/
theorem exists_isC1FieldOn (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hb : 0 < b) (hI : Icc 0 b ⊆ I) :
    ∃ K, IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K := by
  obtain ⟨R, hR, B, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  exact ⟨_, hω.isC1FieldOn_extendedField_law hU hR.le (by norm_num) (by norm_num) le_rfl
    fun t ht ↦ by
      simpa using hω.contDiffOn_law hU hR.le (by norm_num) (by norm_num) ht⟩

/-- The velocity field is tangent to the boundary. -/
theorem velocityField_normal_eq_zero (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    {t : ℝ} (ht : t ∈ I) {x : ℝ^2} (hx : x 1 = 0) : velocityField U sol t x 1 = 0 := by
  obtain ⟨R, hR, hz⟩ := h.exists_vorticity_eq_zero ht
  exact extendedField_normal_eq_zero 1 hx
    (hU.normal_eq_zero hR.le (h.contDiff_vorticity ht).continuous.continuousOn hz x hx)

/-- On the closed half-plane the velocity field is the field of the law at the vorticity. -/
theorem velocityField_eq {t : ℝ} {x : ℝ^2} (hx : 0 ≤ x 1) :
    velocityField U sol t x = U (fun y ↦ sol.vorticity y t) x :=
  extendedField_of_nonneg 1 _ hx

variable {Du : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2} {K : NNReal}

/-- The flow of the velocity field maps the closed half-plane onto itself. -/
theorem bijOn_flowOn (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hI : Icc 0 b ⊆ I) (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K) {s t : ℝ}
    (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    BijOn (flowOn (velocityField U sol) 0 b s t) H̄ H̄ :=
  hv.bijOn_flowOn_nonneg (j := 1)
    (fun _ hr _ hx ↦ h.velocityField_normal_eq_zero hU (hI hr) hx) hs ht

/-- Trajectories from the closed half-plane stay in it. -/
theorem trajectory_mem (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hI : Icc 0 b ⊆ I) (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K) (hb : 0 ≤ b)
    {s : ℝ} (hs : s ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) : 0 ≤ trajectory U sol b s a 1 :=
  (h.bijOn_flowOn hU hI hv hs ⟨le_rfl, hb⟩).mapsTo ha

/-- Labels of points of the closed half-plane lie in it. -/
theorem label_mem (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I) (hI : Icc 0 b ⊆ I)
    (hv : IsLipschitzFieldOn (velocityField U sol) 0 b K) (hb : 0 ≤ b) {s : ℝ}
    (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) : 0 ≤ label U sol b x s 1 :=
  (h.bijOn_flowOn hU hI hv ⟨le_rfl, hb⟩ hs).mapsTo hx

/-! ### Transport along trajectories -/

variable (hU : IsVelocityLaw U R₀ C) (hκ : Continuous κ) (h : IsSolutionOn U κ R₀ sol I)
  (hb : 0 < b) (hI : Icc 0 b ⊆ I) (hv : IsC1FieldOn (velocityField U sol) Du 0 b K)
include h hb hI hv

/-- On the closed half-plane the temperature equation reads `θ_t = -Dθ(u)` with the velocity
field. -/
theorem deriv_temperature_eq {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    deriv (fun s ↦ sol.temperature x s) t +
      fderiv ℝ (fun y ↦ sol.temperature y t) x (velocityField U sol t x) = 0 := by
  refine deriv_time_add_eq_of_upperHalfPlane (f := sol.temperature) hb hI
    h.temperature_contDiffOn h.temperature_differentiableAt_time ht
    (h.contDiff_temperature (hI ht))
    (continuous_iff_continuousAt.mpr fun y ↦ (hv.hasFDerivAt t ht y).continuousAt)
    continuous_const (fun y hy ↦ ?_) hx
  have heq := h.temperature_equation (x := y) hy (hI ht)
  rw [velocityField_eq (le_of_lt hy)]
  exact heq

include hκ in
/-- On the closed half-plane the vorticity equation reads `ω_t + Dω(u) = κ ∂₁θ` with the
velocity field. -/
theorem deriv_vorticity_eq {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    deriv (fun s ↦ sol.vorticity x s) t +
      fderiv ℝ (fun y ↦ sol.vorticity y t) x (velocityField U sol t x) =
        κ x * (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y t)) x := by
  refine deriv_time_add_eq_of_upperHalfPlane (f := sol.vorticity) hb hI
    h.vorticity_contDiffOn h.vorticity_differentiableAt_time ht
    (h.contDiff_vorticity (hI ht))
    (continuous_iff_continuousAt.mpr fun y ↦ (hv.hasFDerivAt t ht y).continuousAt)
    (hκ.mul (((h.contDiff_temperature (hI ht)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)) (fun y hy ↦ ?_) hx
  have heq := h.vorticity_equation (x := y) hy (hI ht)
  rw [velocityField_eq (le_of_lt hy)]
  exact heq

include hU in
/-- **The temperature is carried by the flow**: `θ(X(s, a), s) = θ(a, 0)` for every label `a` of
the closed half-plane and every time `s ∈ [0, b]`. It is the Lagrangian form of the temperature
equation. Proof: the derivative in time of the temperature along a trajectory vanishes by the
equation, which holds on the closed half-plane by continuity. -/
theorem temperature_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ} (hs : s ∈ Icc 0 b) :
    sol.temperature (trajectory U sol b s a) s = sol.temperature a 0 := by
  have hL := hv.isLipschitzFieldOn
  have hderiv (r : ℝ) (hr : r ∈ Icc 0 b) :
      HasDerivWithinAt (fun r ↦ sol.temperature (trajectory U sol b r a) r) 0 (Icc 0 b) r := by
    have hd := hasDerivWithinAt_comp_path (f := sol.temperature) hb hI
      h.temperature_contDiffOn h.temperature_differentiableAt_time hr
      (hasDerivAt_trajectory hL hb.le hr a).hasDerivWithinAt
    have hzero := h.deriv_temperature_eq hb hI hv hr (h.trajectory_mem hU hI hL hb.le hr ha)
    rw [add_comm] at hzero
    rwa [hzero] at hd
  have heq := sub_eq_integral_of_hasDerivWithinAt hderiv continuousOn_const hs
  simp only [intervalIntegral.integral_zero, sub_eq_zero] at heq
  rw [heq, trajectory_zero hL hb.le]

include hU in
/-- **The gradient identity.** Along a trajectory from the closed half-plane,
`Dθ_s(X(s, a)) ∘ D_a X(s, a) = Dθ_0(a)`. -/
theorem fderiv_temperature_trajectory_comp {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ}
    (hs : s ∈ Icc 0 b) :
    (fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a)).comp
        (variationOn (velocityField U sol) Du 0 b s 0 a) =
      fderiv ℝ (fun y ↦ sol.temperature y 0) a := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have h1 : HasFDerivAt (fun a ↦ sol.temperature (trajectory U sol b s a) s)
      ((fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a)).comp
        (variationOn (velocityField U sol) Du 0 b s 0 a)) a :=
    (((h.contDiff_temperature (hI hs)).differentiable (by norm_num) _).hasFDerivAt).comp a
      (hv.hasFDerivAt_flowOn hs h0 a)
  have h2 : HasFDerivAt (fun y ↦ sol.temperature y 0)
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a) a :=
    ((h.contDiff_temperature (hI h0)).differentiable (by norm_num) a).hasFDerivAt
  have h2' : HasFDerivWithinAt (fun a ↦ sol.temperature (trajectory U sol b s a) s)
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a) H̄ a :=
    h2.hasFDerivWithinAt.congr (fun y hy ↦ h.temperature_trajectory hU hb hI hv hy hs)
      (h.temperature_trajectory hU hb hI hv ha hs)
  exact (uniqueDiffOn_closedUpper a ha).eq h1.hasFDerivWithinAt h2'

include hU in
/-- **The derivative of the temperature in label form.** `∂₁θ_r(X(r, a)) = Dθ_0(a)(W e₁)` with
`W` the first variation of the flow from time `r` back to time `0` at `X(r, a)`, the inverse of
`D_a X(r, a)`. -/
theorem partialDeriv_temperature_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) :
    (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a) =
      fderiv ℝ (fun y ↦ sol.temperature y 0) a
        (variationOn (velocityField U sol) Du 0 b 0 r (trajectory U sol b r a)
          (EuclideanSpace.single 0 1)) := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hinv := hv.variationOn_flowOn_comp_variationOn h0 hr (trajectory U sol b r a)
  have hback : flowOn (velocityField U sol) 0 b 0 r (trajectory U sol b r a) = a :=
    hL.flowOn_flowOn_self hr h0 a
  rw [hback] at hinv
  have hgrad := h.fderiv_temperature_trajectory_comp hU hb hI hv ha hr
  have happ := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L (EuclideanSpace.single 0 1)) hinv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at happ
  rw [← hgrad, ContinuousLinearMap.comp_apply, happ]
  rfl

/-- The derivative of the temperature along a trajectory is continuous in time. -/
theorem continuousOn_partialDeriv_temperature_trajectory (a : ℝ^2) :
    ContinuousOn (fun r ↦ (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r))
      (trajectory U sol b r a)) (Icc 0 b) := by
  have hL := hv.isLipschitzFieldOn
  have hfJ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) (univ ×ˢ Icc 0 b) :=
    h.temperature_contDiffOn.mono (prod_mono subset_rfl hI)
  have hc := PDE.Analysis.continuousOn_fderiv_slice hfJ (uniqueDiffOn_Icc hb)
  have hpath : ContinuousOn (fun r ↦ (trajectory U sol b r a, r)) (Icc 0 b) :=
    (hL.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a).prodMk continuousOn_id
  have hcomp := hc.comp hpath (fun r hr ↦ (⟨mem_univ _, hr⟩ : (_, r) ∈ univ ×ˢ Icc 0 b))
  exact hcomp.clm_apply continuousOn_const

include hκ in
/-- The forcing `κ ∂₁θ` along a trajectory is continuous in time. -/
theorem continuousOn_forcing_trajectory (a : ℝ^2) :
    ContinuousOn (fun r ↦ κ (trajectory U sol b r a) *
      (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a)) (Icc 0 b) :=
  (hκ.comp_continuousOn (hv.isLipschitzFieldOn.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a)).mul
    (h.continuousOn_partialDeriv_temperature_trajectory hb hI hv a)

include hU hκ in
/-- **The vorticity along a trajectory.**
`ω(X(s, a), s) = ω(a, 0) + ∫₀ˢ κ(X(r, a)) ∂₁θ(X(r, a), r) dr`. It is the Lagrangian form of the
vorticity equation, on which the bounds of the vorticity rest. Proof: the derivative in time of
the vorticity along a trajectory is the forcing `κ ∂₁θ` at the particle, which is continuous in
time, and the fundamental theorem of calculus applies. -/
theorem vorticity_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ} (hs : s ∈ Icc 0 b) :
    sol.vorticity (trajectory U sol b s a) s = sol.vorticity a 0 +
      ∫ r in (0)..s, κ (trajectory U sol b r a) *
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a) := by
  have hL := hv.isLipschitzFieldOn
  have hderiv (r : ℝ) (hr : r ∈ Icc 0 b) :
      HasDerivWithinAt (fun r ↦ sol.vorticity (trajectory U sol b r a) r)
        (κ (trajectory U sol b r a) *
          (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a))
        (Icc 0 b) r := by
    have hd := hasDerivWithinAt_comp_path (f := sol.vorticity) hb hI
      h.vorticity_contDiffOn h.vorticity_differentiableAt_time hr
      (hasDerivAt_trajectory hL hb.le hr a).hasDerivWithinAt
    have heq := h.deriv_vorticity_eq hκ hb hI hv hr (h.trajectory_mem hU hI hL hb.le hr ha)
    rw [add_comm] at heq
    rwa [heq] at hd
  have heq := sub_eq_integral_of_hasDerivWithinAt hderiv
    (h.continuousOn_forcing_trajectory hκ hb hI hv a) hs
  rw [trajectory_zero hL hb.le] at heq
  linarith

include hU in
/-- **The temperature in Eulerian form.** At a point of the closed half-plane the temperature
is the initial temperature at the label. -/
theorem temperature_eq_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.temperature x s = sol.temperature (label U sol b x s) 0 := by
  have hL := hv.isLipschitzFieldOn
  have hlab := h.label_mem hU hI hL hb.le hs hx
  have h1 := h.temperature_trajectory hU hb hI hv hlab hs
  rwa [trajectory_label hL hb.le hs] at h1

include hU hκ in
/-- **The vorticity in Eulerian form.** At a point `x` of the closed half-plane, with the label
`a` of `x` at time `s`, `ω(x, s) = ω(a, 0) + ∫₀ˢ κ(X(r, a)) Dθ_0(a)(W_r e₁) dr`, where `W_r` is
the first variation of the flow from time `r` back to time `0` at `X(r, a)`. -/
theorem vorticity_eq_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x s = sol.vorticity (label U sol b x s) 0 +
      ∫ r in (0)..s, κ (trajectory U sol b r (label U sol b x s)) *
        fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s)
          (variationOn (velocityField U sol) Du 0 b 0 r
            (trajectory U sol b r (label U sol b x s)) (EuclideanSpace.single 0 1)) := by
  have hL := hv.isLipschitzFieldOn
  have hlab := h.label_mem hU hI hL hb.le hs hx
  have h1 := h.vorticity_trajectory hU hκ hb hI hv hlab hs
  rw [trajectory_label hL hb.le hs] at h1
  rw [h1]
  congr 1
  refine intervalIntegral.integral_congr fun r hr ↦ ?_
  have hr' : r ∈ Icc 0 b := by
    rw [uIcc_of_le hs.1] at hr
    exact ⟨hr.1, hr.2.trans hs.2⟩
  rw [h.partialDeriv_temperature_trajectory hU hb hI hv hlab hr']

include hU in
/-- **The Lagrangian vorticity is Lipschitz on the closed half-plane**, with the gradient bound
of the vorticity times the Lipschitz constant `exp (K b)` of the flow. -/
theorem abs_vorticity_trajectory_sub_le {B₁ : ℝ}
    (hB₁ : ∀ s ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderiv ℝ (fun y ↦ sol.vorticity y s) x‖ ≤ B₁)
    {s : ℝ} (hs : s ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) :
    |sol.vorticity (trajectory U sol b s a) s - sol.vorticity (trajectory U sol b s a') s| ≤
      B₁ * Real.exp (K * b) * ‖a - a'‖ := by
  have hL := hv.isLipschitzFieldOn
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ s hs 0 (by simp))
  have hlip := PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ ((h.contDiff_vorticity (hI hs)).differentiable (by norm_num) y))
    (hB₁ s hs) (h.trajectory_mem hU hI hL hb.le hs ha') (h.trajectory_mem hU hI hL hb.le hs ha)
  have hflow : ‖trajectory U sol b s a - trajectory U sol b s a'‖ ≤
      Real.exp (K * b) * ‖a - a'‖ := by
    have h1 := hL.norm_flowOn_sub_le hs ⟨le_rfl, hb.le⟩ a a'
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [sub_zero, abs_of_nonneg hs.1]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 K.2)
  rw [← Real.norm_eq_abs]
  calc _ ≤ B₁ * ‖trajectory U sol b s a - trajectory U sol b s a'‖ := hlip
    _ ≤ B₁ * (Real.exp (K * b) * ‖a - a'‖) := mul_le_mul_of_nonneg_left hflow hB₁0
    _ = B₁ * Real.exp (K * b) * ‖a - a'‖ := by ring

end IsSolutionOn

end HalfPlaneSystem
