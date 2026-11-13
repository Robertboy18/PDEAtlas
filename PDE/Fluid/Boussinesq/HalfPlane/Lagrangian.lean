/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Solution
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The Lagrangian form of half-plane Boussinesq solutions

Let `sol` solve the half-plane Boussinesq system on the times `I` (`IsSolutionOn sol I`) and let
`[0, b] ⊆ I` with `0 < b`. The velocity field `velocityField sol` is a `C¹` field on `[0, b]`
(`IsSolutionOn.exists_isC1FieldOn`), tangent to the boundary, and on the closed half-plane
`H̄ = {x₁ ≥ 0}` it is the velocity of the solution. Its flow maps `H̄` onto itself
(`IsSolutionOn.bijOn_flowOn`). Along its trajectories the temperature is carried and the vorticity
changes by the integrated forcing `∂₀θ = Dθ e₀`, with `e₀ = EuclideanSpace.single 0 1`.

## Main definitions

* `velocityField`: the half-plane Biot-Savart velocity of the vorticity, extended across the
  boundary by first-order weighted reflection.
* `trajectory`: the position `X(s, a) = trajectory sol b s a` at time `s` of the particle with label
  `a`, its position at time `0`.
* `label`: the label of the particle at `x` at time `s`.

## Main results

* `temperature_trajectory`: the temperature is carried, `θ(X(s, a), s) = θ(a, 0)`.
* `fderiv_temperature_trajectory_comp`: `Dθ_s(X(s, a)) ∘ D_a X(s, a) = Dθ_0(a)`.
* `vorticity_trajectory`: `ω(X(s, a), s) = ω(a, 0) + ∫₀ˢ ∂₀θ(X(r, a), r) dr`.
* `partialDeriv_temperature_trajectory`: the forcing in label form
  `∂₀θ(X(r, a), r) = Dθ_0(a) (D_a X(r, a)⁻¹ e₀)`, where `D_a X(r, a)⁻¹` is the first variation
  of the flow from time `r` back to time `0` at `X(r, a)`.
* `temperature_eq_label`: the carried temperature in Eulerian form at a point `x ∈ H̄`, with the
  label `label sol b x s` of the particle at `x` at time `s`.
* `vorticity_eq_label`: the vorticity identity in Eulerian form at a point `x ∈ H̄`.
* `abs_vorticity_trajectory_sub_le`: the Lagrangian vorticity is Lipschitz on `H̄`.

## How it works

The equations of the classical class hold on the open half-plane only. On the closed half-plane we
read them as `θ_t + Dθ(u) = 0` and `ω_t + Dω(u) = ∂₀θ` with the velocity field
(`IsSolutionOn.deriv_temperature_eq`, `IsSolutionOn.deriv_vorticity_eq`); all terms are continuous,
so the identities pass from the open half-plane to its closure
(`deriv_time_add_eq_of_upperHalfPlane`). The field is tangent to the boundary, so trajectories from
`H̄` stay in `H̄` (`IsSolutionOn.trajectory_mem`), and the chain rule along a trajectory
(`hasDerivWithinAt_comp_path`) shows that the derivative of `θ(X(r, a), r)` in `r` vanishes and that
of `ω(X(r, a), r)` is the forcing. The fundamental theorem of calculus on `[0, s]` gives
`IsSolutionOn.temperature_trajectory` and `IsSolutionOn.vorticity_trajectory`. The gradient identity
holds because both sides are derivatives within `H̄` of `a ↦ θ(X(s, a), s)`, which equals `θ(a, 0)`
there, and derivatives within `H̄` are unique. Composing it with the first variation from time `r`
back to time `0`, which inverts `D_a X(r, a)`, gives the forcing in label form, and evaluating at
the label gives the Eulerian forms. The Lipschitz bound is the mean value inequality on the convex
set `H̄`, with the gradient bound `B₁` of the vorticity and the Lipschitz constant `exp (K b)` of
the flow.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow
open scoped Topology

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable (sol : VorticityStreamFields)

/-- The velocity field of `sol` on the plane: at every time the half-plane Biot-Savart velocity of
the vorticity, extended across the boundary by first-order weighted reflection. -/
def velocityField (t : ℝ) : ℝ^2 → ℝ^2 :=
  extendedVelocity 1 (fun x ↦ sol.vorticity x t)

/-- The spatial derivative of `velocityField`. -/
def velocityFieldDeriv (t : ℝ) (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (velocityField sol t) x

/-- The position at time `s` of the particle with label `a` (its position at time `0`), for the
flow of `velocityField sol` on `[0, b]`. -/
def trajectory (b s : ℝ) (a : ℝ^2) : ℝ^2 :=
  flowOn (velocityField sol) 0 b s 0 a

/-- The label (the position at time `0`) of the particle at `x` at time `s`. -/
def label (b : ℝ) (x : ℝ^2) (s : ℝ) : ℝ^2 :=
  flowOn (velocityField sol) 0 b 0 s x

variable {sol}

/-! ### Derivatives along paths -/

section Path

variable {f : ℝ^2 → ℝ → ℝ} {I : Set ℝ} {b : ℝ}

/-- **Chain rule along a path.** For a field jointly `C¹` on `univ ×ˢ I` whose time slices are
differentiable, the derivative within `[0, b] ⊆ I` of `r ↦ f(γ r, r)` is the spatial derivative
applied to `γ'` plus the time derivative. -/
theorem hasDerivWithinAt_comp_path (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ I))
    (htime : ∀ {x : ℝ^2} {t : ℝ}, t ∈ I → DifferentiableAt ℝ (fun s ↦ f x s) t)
    {γ : ℝ → ℝ^2} {γ' : ℝ^2} {s : ℝ} (hs : s ∈ Icc 0 b)
    (hγ : HasDerivWithinAt γ γ' (Icc 0 b) s) :
    HasDerivWithinAt (fun r ↦ f (γ r) r)
      (fderiv ℝ (fun y ↦ f y s) (γ s) γ' + deriv (fun r ↦ f (γ s) r) s) (Icc 0 b) s := by
  set J : Set ℝ := Icc 0 b
  have hfJ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ J) :=
    hf.mono (prod_mono subset_rfl hI)
  set L := fderivWithin ℝ (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ J) (γ s, s)
  have hL : HasFDerivWithinAt (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) L (univ ×ˢ J) (γ s, s) :=
    ((hfJ.differentiableOn one_ne_zero) _ ⟨mem_univ _, hs⟩).hasFDerivWithinAt
  have hmaps : MapsTo (fun r ↦ (γ r, r)) J (univ ×ˢ J) := fun r hr ↦ ⟨mem_univ _, hr⟩
  have hp : HasDerivWithinAt (fun r ↦ (γ r, r)) (γ', (1 : ℝ)) J s :=
    hγ.prodMk (hasDerivWithinAt_id s J)
  have hcomp := hL.comp_hasDerivWithinAt (f := fun r ↦ (γ r, r)) s hp hmaps
  have hspace : L (γ', 0) = fderiv ℝ (fun y ↦ f y s) (γ s) γ' := by
    have hsl := PDE.Analysis.fderiv_slice_of_contDiffOn hfJ hs (x := γ s)
    simp only at hsl
    rw [hsl]
    rfl
  have htime' : L (0, 1) = deriv (fun r ↦ f (γ s) r) s := by
    have hmaps' : MapsTo (fun r ↦ (γ s, r)) J (univ ×ˢ J) := fun r hr ↦ ⟨mem_univ _, hr⟩
    have hp' : HasDerivWithinAt (fun r ↦ (γ s, r)) ((0 : ℝ^2), (1 : ℝ)) J s :=
      (hasDerivWithinAt_const s J (γ s)).prodMk (hasDerivWithinAt_id s J)
    have h1 : HasDerivWithinAt (fun r ↦ f (γ s) r) (L (0, 1)) J s :=
      hL.comp_hasDerivWithinAt s hp' hmaps'
    exact (uniqueDiffOn_Icc hb s hs).eq_deriv _ h1
      ((htime (hI hs)).hasDerivAt.hasDerivWithinAt)
  have hsplit : L (γ', 1) = L (γ', 0) + L (0, 1) := by
    rw [← map_add]
    simp
  rw [hsplit, hspace, htime'] at hcomp
  exact hcomp

/-- The time derivative of a jointly `C¹` field at a time of `[0, b] ⊆ I` is continuous in
space. -/
theorem continuous_deriv_time (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ I))
    (htime : ∀ {x : ℝ^2} {t : ℝ}, t ∈ I → DifferentiableAt ℝ (fun s ↦ f x s) t)
    {t : ℝ} (ht : t ∈ Icc 0 b) : Continuous fun x ↦ deriv (fun s ↦ f x s) t := by
  set J : Set ℝ := Icc 0 b
  have hfJ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ J) :=
    hf.mono (prod_mono subset_rfl hI)
  set L := fderivWithin ℝ (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ J)
  have hLc : ContinuousOn L (univ ×ˢ J) :=
    hfJ.continuousOn_fderivWithin (UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hb))
      le_rfl
  have heq (x : ℝ^2) : deriv (fun s ↦ f x s) t = L (x, t) (0, 1) := by
    have hL : HasFDerivWithinAt (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (L (x, t)) (univ ×ˢ J) (x, t) :=
      ((hfJ.differentiableOn one_ne_zero) _ ⟨mem_univ _, ht⟩).hasFDerivWithinAt
    have hmaps' : MapsTo (fun r ↦ (x, r)) J (univ ×ˢ J) := fun r hr ↦ ⟨mem_univ _, hr⟩
    have hp' : HasDerivWithinAt (fun r ↦ (x, r)) ((0 : ℝ^2), (1 : ℝ)) J t :=
      (hasDerivWithinAt_const t J x).prodMk (hasDerivWithinAt_id t J)
    have h1 : HasDerivWithinAt (fun r ↦ f x r) (L (x, t) (0, 1)) J t :=
      hL.comp_hasDerivWithinAt t hp' hmaps'
    exact ((uniqueDiffOn_Icc hb t ht).eq_deriv _ h1
      ((htime (hI ht)).hasDerivAt.hasDerivWithinAt)).symm
  simp only [heq]
  have hc : Continuous fun x : ℝ^2 ↦ L (x, t) :=
    hLc.comp_continuous (continuous_id.prodMk continuous_const)
      (fun y ↦ (⟨mem_univ y, ht⟩ : (y, t) ∈ univ ×ˢ J))
  exact hc.clm_apply continuous_const

/-- An identity `f_t + Df(w) = g` with continuous terms that holds on the open upper half-plane
holds on the closed half-plane. -/
theorem deriv_time_add_eq_of_upperHalfPlane (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ I))
    (htime : ∀ {x : ℝ^2} {t : ℝ}, t ∈ I → DifferentiableAt ℝ (fun s ↦ f x s) t)
    {t : ℝ} (ht : t ∈ Icc 0 b) (hft : ContDiff ℝ 1 (fun y ↦ f y t))
    {w : ℝ^2 → ℝ^2} (hw : Continuous w) {g : ℝ^2 → ℝ} (hg : Continuous g)
    (heq : ∀ x ∈ upperHalfPlane,
      deriv (fun s ↦ f x s) t + fderiv ℝ (fun y ↦ f y t) x (w x) = g x)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    deriv (fun s ↦ f x s) t + fderiv ℝ (fun y ↦ f y t) x (w x) = g x := by
  have hcont : Continuous fun x ↦
      deriv (fun s ↦ f x s) t + fderiv ℝ (fun y ↦ f y t) x (w x) :=
    (continuous_deriv_time hb hI hf htime ht).add
      ((hft.continuous_fderiv one_ne_zero).clm_apply hw)
  have hclosed : IsClosed {x : ℝ^2 |
      deriv (fun s ↦ f x s) t + fderiv ℝ (fun y ↦ f y t) x (w x) = g x} :=
    isClosed_eq hcont hg
  have hsub : closure upperHalfPlane ⊆ {x : ℝ^2 |
      deriv (fun s ↦ f x s) t + fderiv ℝ (fun y ↦ f y t) x (w x) = g x} :=
    hclosed.closure_subset_iff.mpr fun y hy ↦ heq y hy
  rw [closure_upperHalfPlane] at hsub
  exact hsub hx

/-- The difference of the values at `s` and `0` of a function whose derivative within `[0, b]`
is a continuous function along `[0, s]` is the integral of the derivative. -/
theorem sub_eq_integral_of_hasDerivWithinAt {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Icc 0 b, HasDerivWithinAt φ (φ' r) (Icc 0 b) r)
    (hφ' : ContinuousOn φ' (Icc 0 b)) {s : ℝ} (hs : s ∈ Icc 0 b) :
    φ s - φ 0 = ∫ r in (0)..s, φ' r := by
  have hsub : Icc 0 s ⊆ Icc 0 b := Icc_subset_Icc_right hs.2
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 ?_ ?_ ?_).symm
  · exact fun r hr ↦ (hφ r (hsub hr)).continuousWithinAt.mono hsub
  · intro r hr
    have hrb : r ∈ Ioo 0 b := ⟨hr.1, hr.2.trans_le hs.2⟩
    exact (hφ r (Ioo_subset_Icc_self hrb)).hasDerivAt (Icc_mem_nhds hrb.1 hrb.2)
  · exact (hφ'.mono hsub).intervalIntegrable_of_Icc hs.1

end Path

/-! ### The velocity field and its flow -/

/-! ### Trajectories and labels -/

section Trajectory

variable {b : ℝ} {K : NNReal}

/-- The particle with the label of `x` at time `s` is at `x` at time `s`. -/
theorem trajectory_label (hv : IsLipschitzFieldOn (velocityField sol) 0 b K)
    {s : ℝ} (hs : s ∈ Icc 0 b) (x : ℝ^2) : trajectory sol b s (label sol b x s) = x :=
  hv.flowOn_flowOn_self ⟨le_rfl, hs.1.trans hs.2⟩ hs x

/-- Trajectories solve the equation of the velocity field. -/
theorem hasDerivAt_trajectory (hv : IsLipschitzFieldOn (velocityField sol) 0 b K)
    {s : ℝ} (hs : s ∈ Icc 0 b) (a : ℝ^2) :
    HasDerivAt (fun r ↦ trajectory sol b r a) (velocityField sol s (trajectory sol b s a)) s :=
  hv.hasDerivAt_flowOn hs ⟨le_rfl, hs.1.trans hs.2⟩ a

/-- Trajectories start at their labels. -/
theorem trajectory_zero (hv : IsLipschitzFieldOn (velocityField sol) 0 b K) (hb : 0 ≤ b)
    (a : ℝ^2) : trajectory sol b 0 a = a :=
  hv.flowOn_self ⟨le_rfl, hb⟩ a

end Trajectory

namespace IsSolutionOn

variable {I : Set ℝ} {b : ℝ}

/-- On compact intervals the velocity field of a solution is a `C¹` field. -/
theorem exists_isC1FieldOn (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I) :
    ∃ K, IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K := by
  obtain ⟨R, B, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  exact ⟨_, hω.isC1FieldOn (by norm_num) (by norm_num)⟩

/-- The velocity field is tangent to the boundary. -/
theorem velocityField_normal_eq_zero (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) {x : ℝ^2}
    (hx : x 1 = 0) : velocityField sol t x 1 = 0 := by
  obtain ⟨R, hR⟩ := h.exists_vorticity_eq_zero ht
  exact extendedVelocity_normal_eq_zero 1 (h.contDiff_vorticity ht).continuous.continuousOn hR hx

/-- On the closed half-plane the velocity field is the velocity of the solution. -/
theorem velocityField_eq (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) {x : ℝ^2}
    (hx : 0 ≤ x 1) : velocityField sol t x = vorticityStreamVelocity sol x t := by
  rw [velocityField, extendedVelocity_of_nonneg 1 _ hx, h.velocity_eq ht hx]

variable {Du : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2} {K : NNReal}

/-- The flow of the velocity field maps the closed half-plane onto itself. -/
theorem bijOn_flowOn (h : IsSolutionOn sol I) (hI : Icc 0 b ⊆ I)
    (hv : IsLipschitzFieldOn (velocityField sol) 0 b K) {s t : ℝ} (hs : s ∈ Icc 0 b)
    (ht : t ∈ Icc 0 b) : BijOn (flowOn (velocityField sol) 0 b s t) H̄ H̄ :=
  hv.bijOn_flowOn_nonneg (j := 1)
    (fun _ hr _ hx ↦ h.velocityField_normal_eq_zero (hI hr) hx) hs ht

/-- Trajectories from the closed half-plane stay in it. -/
theorem trajectory_mem (h : IsSolutionOn sol I) (hI : Icc 0 b ⊆ I)
    (hv : IsLipschitzFieldOn (velocityField sol) 0 b K) {s : ℝ} (hs : s ∈ Icc 0 b)
    {a : ℝ^2} (ha : 0 ≤ a 1) : 0 ≤ trajectory sol b s a 1 :=
  (h.bijOn_flowOn hI hv hs ⟨le_rfl, hs.1.trans hs.2⟩).mapsTo ha

/-- Labels of points of the closed half-plane lie in it. -/
theorem label_mem (h : IsSolutionOn sol I) (hI : Icc 0 b ⊆ I)
    (hv : IsLipschitzFieldOn (velocityField sol) 0 b K) {s : ℝ} (hs : s ∈ Icc 0 b)
    {x : ℝ^2} (hx : 0 ≤ x 1) : 0 ≤ label sol b x s 1 :=
  (h.bijOn_flowOn hI hv ⟨le_rfl, hs.1.trans hs.2⟩ hs).mapsTo hx

/-! ### Transport along trajectories -/

variable (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) Du 0 b K)
include h hb hI hv

/-- On the closed half-plane the temperature equation reads `θ_t = -Dθ(u)` with the velocity
field. -/
theorem deriv_temperature_eq {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    deriv (fun s ↦ sol.temperature x s) t +
      fderiv ℝ (fun y ↦ sol.temperature y t) x (velocityField sol t x) = 0 := by
  refine deriv_time_add_eq_of_upperHalfPlane (f := sol.temperature) hb hI
    h.classical.regularity.temperature_contDiffOn
    h.classical.regularity.temperature_differentiableAt_time ht
    (h.contDiff_temperature (hI ht))
    (continuous_iff_continuousAt.mpr fun y ↦ (hv.hasFDerivAt t ht y).continuousAt)
    continuous_const (fun y hy ↦ ?_) hx
  have heq := h.classical.temperature_equation hy (hI ht)
  rw [h.velocityField_eq (hI ht) (le_of_lt hy)]
  exact heq

/-- On the closed half-plane the vorticity equation reads `ω_t + Dω(u) = ∂₀θ` with the velocity
field. -/
theorem deriv_vorticity_eq {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    deriv (fun s ↦ sol.vorticity x s) t +
      fderiv ℝ (fun y ↦ sol.vorticity y t) x (velocityField sol t x) =
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y t)) x := by
  refine deriv_time_add_eq_of_upperHalfPlane (f := sol.vorticity) hb hI
    h.classical.regularity.vorticity_contDiffOn
    h.classical.regularity.vorticity_differentiableAt_time ht
    (h.contDiff_vorticity (hI ht))
    (continuous_iff_continuousAt.mpr fun y ↦ (hv.hasFDerivAt t ht y).continuousAt)
    (((h.contDiff_temperature (hI ht)).continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (fun y hy ↦ ?_) hx
  have heq := h.classical.vorticity_equation hy (hI ht)
  rw [h.velocityField_eq (hI ht) (le_of_lt hy)]
  exact heq

/-- **The temperature is carried by the flow.** -/
theorem temperature_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ} (hs : s ∈ Icc 0 b) :
    sol.temperature (trajectory sol b s a) s = sol.temperature a 0 := by
  have hL := hv.isLipschitzFieldOn
  have hderiv (r : ℝ) (hr : r ∈ Icc 0 b) :
      HasDerivWithinAt (fun r ↦ sol.temperature (trajectory sol b r a) r) 0 (Icc 0 b) r := by
    have hd := hasDerivWithinAt_comp_path (f := sol.temperature) hb hI
      h.classical.regularity.temperature_contDiffOn
      h.classical.regularity.temperature_differentiableAt_time hr
      (hasDerivAt_trajectory hL hr a).hasDerivWithinAt
    have hzero := h.deriv_temperature_eq hb hI hv hr (h.trajectory_mem hI hL hr ha)
    rw [add_comm] at hzero
    rwa [hzero] at hd
  have heq := sub_eq_integral_of_hasDerivWithinAt hderiv continuousOn_const hs
  simp only [intervalIntegral.integral_zero, sub_eq_zero] at heq
  rw [heq, trajectory_zero hL hb.le]

/-- **The gradient identity.** Along a trajectory from the closed half-plane,
`Dθ_s(X(s, a)) ∘ D_a X(s, a) = Dθ_0(a)`. -/
theorem fderiv_temperature_trajectory_comp {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ}
    (hs : s ∈ Icc 0 b) :
    (fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a)).comp
        (variationOn (velocityField sol) Du 0 b s 0 a) =
      fderiv ℝ (fun y ↦ sol.temperature y 0) a := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have h1 : HasFDerivAt (fun a ↦ sol.temperature (trajectory sol b s a) s)
      ((fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a)).comp
        (variationOn (velocityField sol) Du 0 b s 0 a)) a :=
    (((h.contDiff_temperature (hI hs)).differentiable (by norm_num) _).hasFDerivAt).comp a
      (hv.hasFDerivAt_flowOn hs h0 a)
  have h2 : HasFDerivAt (fun y ↦ sol.temperature y 0)
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a) a :=
    ((h.contDiff_temperature (hI h0)).differentiable (by norm_num) a).hasFDerivAt
  have h2' : HasFDerivWithinAt (fun a ↦ sol.temperature (trajectory sol b s a) s)
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a) H̄ a :=
    h2.hasFDerivWithinAt.congr (fun y hy ↦ h.temperature_trajectory hb hI hv hy hs)
      (h.temperature_trajectory hb hI hv ha hs)
  exact (uniqueDiffOn_closedUpper a ha).eq h1.hasFDerivWithinAt h2'

/-- **The forcing in label form.** `∂₀θ_r(X(r, a)) = Dθ_0(a)(W e₀)` with `W` the first variation
of the flow from time `r` back to time `0` at `X(r, a)`, the inverse of `D_a X(r, a)`. -/
theorem partialDeriv_temperature_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) :
    (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory sol b r a) =
      fderiv ℝ (fun y ↦ sol.temperature y 0) a
        (variationOn (velocityField sol) Du 0 b 0 r (trajectory sol b r a)
          (EuclideanSpace.single 0 1)) := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hinv := hv.variationOn_flowOn_comp_variationOn h0 hr (trajectory sol b r a)
  have hback : flowOn (velocityField sol) 0 b 0 r (trajectory sol b r a) = a :=
    hL.flowOn_flowOn_self hr h0 a
  rw [hback] at hinv
  have hgrad := h.fderiv_temperature_trajectory_comp hb hI hv ha hr
  have happ := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L (EuclideanSpace.single 0 1)) hinv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at happ
  rw [← hgrad, ContinuousLinearMap.comp_apply, happ]
  rfl

/-- The forcing along a trajectory is continuous in time. -/
theorem continuousOn_partialDeriv_temperature_trajectory (a : ℝ^2) :
    ContinuousOn (fun r ↦ (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r))
      (trajectory sol b r a)) (Icc 0 b) := by
  have hL := hv.isLipschitzFieldOn
  have hfJ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) (univ ×ˢ Icc 0 b) :=
    h.classical.regularity.temperature_contDiffOn.mono (prod_mono subset_rfl hI)
  have hc := PDE.Analysis.continuousOn_fderiv_slice hfJ (uniqueDiffOn_Icc hb)
  have hpath : ContinuousOn (fun r ↦ (trajectory sol b r a, r)) (Icc 0 b) :=
    (hL.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a).prodMk continuousOn_id
  have hcomp := hc.comp hpath (fun r hr ↦ (⟨mem_univ _, hr⟩ : (_, r) ∈ univ ×ˢ Icc 0 b))
  exact hcomp.clm_apply continuousOn_const

/-- **The vorticity along a trajectory.**
`ω(X(s, a), s) = ω(a, 0) + ∫₀ˢ ∂₀θ(X(r, a), r) dr`. -/
theorem vorticity_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) {s : ℝ} (hs : s ∈ Icc 0 b) :
    sol.vorticity (trajectory sol b s a) s = sol.vorticity a 0 +
      ∫ r in (0)..s, (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory sol b r a) := by
  have hL := hv.isLipschitzFieldOn
  have hderiv (r : ℝ) (hr : r ∈ Icc 0 b) :
      HasDerivWithinAt (fun r ↦ sol.vorticity (trajectory sol b r a) r)
        ((∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory sol b r a))
        (Icc 0 b) r := by
    have hd := hasDerivWithinAt_comp_path (f := sol.vorticity) hb hI
      h.classical.regularity.vorticity_contDiffOn
      h.classical.regularity.vorticity_differentiableAt_time hr
      (hasDerivAt_trajectory hL hr a).hasDerivWithinAt
    have heq := h.deriv_vorticity_eq hb hI hv hr (h.trajectory_mem hI hL hr ha)
    rw [add_comm] at heq
    rwa [heq] at hd
  have heq := sub_eq_integral_of_hasDerivWithinAt hderiv
    (h.continuousOn_partialDeriv_temperature_trajectory hb hI hv a) hs
  rw [trajectory_zero hL hb.le] at heq
  linarith

omit hb in
/-- **The temperature in Eulerian form.** At a point of the closed half-plane the temperature
is the initial temperature at the label. -/
theorem temperature_eq_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.temperature x s = sol.temperature (label sol b x s) 0 := by
  have hL := hv.isLipschitzFieldOn
  rcases (hs.1.trans hs.2).eq_or_lt with hb0 | hb
  · obtain rfl : s = 0 := le_antisymm (hs.2.trans hb0.ge) hs.1
    rw [label, hL.flowOn_self hs]
  have hlab := h.label_mem hI hL hs hx
  have h1 := h.temperature_trajectory hb hI hv hlab hs
  rwa [trajectory_label hL hs] at h1

/-- **The vorticity in Eulerian form.** At a point `x` of the closed half-plane, with the label
`a` of `x` at time `s`, `ω(x, s) = ω(a, 0) + ∫₀ˢ Dθ_0(a)(W_r e₀) dr`, where `W_r` is the first
variation of the flow from time `r` back to time `0` at `X(r, a)`. -/
theorem vorticity_eq_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x s = sol.vorticity (label sol b x s) 0 +
      ∫ r in (0)..s, fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)
        (variationOn (velocityField sol) Du 0 b 0 r
          (trajectory sol b r (label sol b x s)) (EuclideanSpace.single 0 1)) := by
  have hL := hv.isLipschitzFieldOn
  have hlab := h.label_mem hI hL hs hx
  have h1 := h.vorticity_trajectory hb hI hv hlab hs
  rw [trajectory_label hL hs] at h1
  rw [h1]
  congr 1
  refine intervalIntegral.integral_congr fun r hr ↦ ?_
  have hr' : r ∈ Icc 0 b := by
    rw [uIcc_of_le hs.1] at hr
    exact ⟨hr.1, hr.2.trans hs.2⟩
  exact h.partialDeriv_temperature_trajectory hb hI hv hlab hr'

/-- **The Lagrangian vorticity is Lipschitz on the closed half-plane**, with the gradient bound
of the vorticity times the Lipschitz constant `exp (K b)` of the flow. -/
theorem abs_vorticity_trajectory_sub_le {B₁ : ℝ}
    (hB₁ : ∀ s ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderiv ℝ (fun y ↦ sol.vorticity y s) x‖ ≤ B₁)
    {s : ℝ} (hs : s ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) :
    |sol.vorticity (trajectory sol b s a) s - sol.vorticity (trajectory sol b s a') s| ≤
      B₁ * Real.exp (K * b) * ‖a - a'‖ := by
  have hL := hv.isLipschitzFieldOn
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ s hs 0 (by simp))
  have hlip := PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ ((h.contDiff_vorticity (hI hs)).differentiable (by norm_num) y))
    (hB₁ s hs) (h.trajectory_mem hI hL hs ha') (h.trajectory_mem hI hL hs ha)
  have hflow : ‖trajectory sol b s a - trajectory sol b s a'‖ ≤ Real.exp (K * b) * ‖a - a'‖ := by
    have h1 := hL.norm_flowOn_sub_le hs ⟨le_rfl, hb.le⟩ a a'
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [sub_zero, abs_of_nonneg hs.1]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 K.2)
  rw [← Real.norm_eq_abs]
  calc _ ≤ B₁ * ‖trajectory sol b s a - trajectory sol b s a'‖ := hlip
    _ ≤ B₁ * (Real.exp (K * b) * ‖a - a'‖) := mul_le_mul_of_nonneg_left hflow hB₁0
    _ = B₁ * Real.exp (K * b) * ‖a - a'‖ := by ring

end IsSolutionOn

end Boussinesq.HalfPlane
