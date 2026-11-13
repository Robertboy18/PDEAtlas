/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.OriginJets
public import PDE.Analysis.Calculus.Taylor.RayJet
import PDE.Analysis.Calculus.HalfSpaceGluing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Origin jets from bounds on the upper half-plane

A function smooth up to the boundary near the origin (`Boussinesq.IsSmoothToBoundary`) and
`o(|x|²)` on the open upper half-plane has first and second derivatives tending to zero at the
origin (`IsSmoothToBoundary.tendsto_jets_of_isLittleO`). Along the rays `s ↦ s v` with
`v ∈ {(0, 1), (1, 1), (-1, 1)}`, which lie in the half-plane, the one-dimensional statement
`PDE.Analysis.tendsto_fderiv_eq_zero_of_isLittleO_sq` gives the directional jets, and these
three directions determine a symmetric bilinear form on the plane. The directions `(1, 1)`,
`(1, 2)`, `(2, 1)` do the same for a bound on the open quadrant
(`IsSmoothToBoundary.tendsto_jets_of_isLittleO_quadrant`). This identifies the jets of fields
known only through value bounds, such as the residuals of the approximate solutions.

The class `IsSmoothToBoundary` is closed under sums, products and multiples, and a function `C¹`
up to the boundary with zero limit at the origin is `O(|x|)` there.

## Main results

* `IsSmoothToBoundary.tendsto_jets_of_isLittleO`: if `h` is `C²` up to the boundary near the
  origin and `h = o(|x|²)` on the upper half-plane, then `h` and its first and second derivatives
  tend to zero at the origin.
* `IsSmoothToBoundary.tendsto_jets_of_isLittleO_quadrant`: the same from a bound on the open
  quadrant.
* `IsSmoothToBoundary.partialDeriv_partialDeriv_eq_of_isBigO`: if `g - L = O(|x|³)` on the upper
  half-plane, each second derivative of `g` at the origin is the limit of that of `L`.
* `IsSmoothToBoundary.directional_jets_eq_zero`: the directional jets along one ray in a set `S`
  vanish when `h = o(|x|²)` on `S`.
* `IsSmoothToBoundary.isBigO_of_tendsto_zero`: a function `C¹` up to the boundary with limit zero
  at the origin is `O(|x|)` there.
* `IsSmoothToBoundary.mul`: products of functions `C^k` up to the boundary are `C^k` up to the
  boundary.
-/

@[expose] public section

noncomputable section

open Filter Set PDE PDE.Common Asymptotics
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

namespace IsSmoothToBoundary

variable {k : ℕ} {f g : ℝ^2 → ℝ}

/-- A function `C^k` on the plane is `C^k` up to the boundary. -/
theorem of_contDiff (hf : ContDiff ℝ k f) : IsSmoothToBoundary k f :=
  of_contDiffOn hf.contDiffOn

/-- Sums of functions `C^k` up to the boundary are `C^k` up to the boundary. -/
theorem add (hf : IsSmoothToBoundary k f) (hg : IsSmoothToBoundary k g) :
    IsSmoothToBoundary k (fun x ↦ f x + g x) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  exact ⟨fun x ↦ F x + G x, hF.add hG, fun x hx ↦ by simp only [hfF hx, hgG hx]⟩

/-- Differences of functions `C^k` up to the boundary are `C^k` up to the boundary. -/
theorem sub (hf : IsSmoothToBoundary k f) (hg : IsSmoothToBoundary k g) :
    IsSmoothToBoundary k (fun x ↦ f x - g x) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  exact ⟨fun x ↦ F x - G x, hF.sub hG, fun x hx ↦ by simp only [hfF hx, hgG hx]⟩

/-- Products of functions `C^k` up to the boundary are `C^k` up to the boundary. -/
theorem mul (hf : IsSmoothToBoundary k f) (hg : IsSmoothToBoundary k g) :
    IsSmoothToBoundary k (fun x ↦ f x * g x) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  exact ⟨fun x ↦ F x * G x, hF.mul hG, fun x hx ↦ by simp only [hfF hx, hgG hx]⟩

/-- Constant multiples of functions `C^k` up to the boundary are `C^k` up to the boundary. -/
theorem const_mul (c : ℝ) (hf : IsSmoothToBoundary k f) :
    IsSmoothToBoundary k (fun x ↦ c * f x) := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact ⟨fun x ↦ c * F x, contDiffOn_const.mul hF, fun x hx ↦ by simp only [hfF hx]⟩

/-- The negation of a function `C^k` up to the boundary is `C^k` up to the boundary. -/
theorem neg (hf : IsSmoothToBoundary k f) : IsSmoothToBoundary k (fun x ↦ -f x) := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact ⟨fun x ↦ -F x, hF.neg, fun x hx ↦ by simp only [hfF hx]⟩

/-- Constants are `C^k` up to the boundary. -/
theorem const (c : ℝ) : IsSmoothToBoundary k (fun _ ↦ c) := of_contDiff contDiff_const

/-- The coordinates `x ↦ x i` are `C^k` up to the boundary. -/
theorem coord (i : Fin 2) : IsSmoothToBoundary k (fun x : ℝ^2 ↦ x i) :=
  of_contDiff (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).contDiff

/-- Being `C^k` up to the boundary only depends on the values on the open upper half-plane. -/
theorem congr (hf : IsSmoothToBoundary k f) (hfg : EqOn f g upperHalfPlane) :
    IsSmoothToBoundary k g := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact ⟨F, hF, fun x hx ↦ (hfg hx).symm.trans (hfF hx)⟩

/-- A function `C¹` up to the boundary with limit zero at the origin is `O(|x|)` there. -/
theorem isBigO_of_tendsto_zero (hf : IsSmoothToBoundary 1 f)
    (h0 : Tendsto f (𝓝[upperHalfPlane] 0) (𝓝 0)) :
    f =O[𝓝[upperHalfPlane] 0] fun x ↦ ‖x‖ := by
  obtain ⟨F, hF, hfF⟩ := hf
  set H : Set (ℝ^2) := {x | 0 ≤ x 1}
  have hU : UniqueDiffOn ℝ H := PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1
  have hconv : Convex ℝ (H ∩ Metric.closedBall 0 1) :=
    (convex_halfSpace_ge (EuclideanSpace.proj (1 : Fin 2)).isLinear 0).inter
      (convex_closedBall _ _)
  have hcpt : IsCompact (H ∩ Metric.closedBall (0 : ℝ^2) 1) :=
    (isCompact_closedBall _ _).inter_left
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hcont : ContinuousOn (fderivWithin ℝ F H) H := hF.continuousOn_fderivWithin hU le_rfl
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hcont.mono inter_subset_left)
  have hF0 : F 0 = 0 := by
    have ht : Tendsto F (𝓝[upperHalfPlane] 0) (𝓝 (F 0)) :=
      ((hF.continuousOn 0 (by simp [H])).mono upperHalfPlane_subset_closed).tendsto
    have := neBot_upperHalfPlane_axis.mono (nhdsWithin_mono _ inter_subset_left)
    exact tendsto_nhds_unique ht (h0.congr' (eventuallyEq_nhdsWithin_of_eqOn hfF))
  have hd : ∀ x ∈ H ∩ Metric.closedBall 0 1,
      HasFDerivWithinAt F (fderivWithin ℝ F H x) (H ∩ Metric.closedBall 0 1) x := fun x hx ↦
    ((hF.differentiableOn (by norm_num) x hx.1).hasFDerivWithinAt).mono inter_subset_left
  refine IsBigO.of_bound C ?_
  have hball : Metric.ball (0 : ℝ^2) 1 ∈ 𝓝[upperHalfPlane] (0 : ℝ^2) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hball, self_mem_nhdsWithin] with x hxb hxH
  have hxs : x ∈ H ∩ Metric.closedBall 0 1 :=
    ⟨upperHalfPlane_subset_closed hxH, Metric.ball_subset_closedBall hxb⟩
  have h0s : (0 : ℝ^2) ∈ H ∩ Metric.closedBall 0 1 := ⟨by simp [H], by simp⟩
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd (fun y hy ↦ hC y hy) hconv
    h0s hxs
  rw [hF0, sub_zero, sub_zero] at this
  rw [hfF hxH, Real.norm_eq_abs, norm_norm]
  simpa using this

end IsSmoothToBoundary

/-- The ray `s ↦ s v`, for `v` with positive second coordinate, tends to the origin within the
upper half-plane as `s → 0⁺`. -/
theorem tendsto_smul_upperHalfPlane {v : ℝ^2} (hv : 0 < v 1) :
    Tendsto (fun s : ℝ ↦ s • v) (𝓝[>] 0) (𝓝[upperHalfPlane] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun s : ℝ ↦ s • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
      (continuous_id.smul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    change 0 < (s • v) 1
    simpa using mul_pos hs hv

/-- Positive multiples of a point of the open upper half-plane lie in it. -/
theorem smul_mem_upperHalfPlane {v : ℝ^2} (hv : 0 < v 1) {s : ℝ} (hs : 0 < s) :
    s • v ∈ upperHalfPlane := by
  change 0 < (s • v) 1
  simpa using mul_pos hs hv

/-- The chain rule along a ray in coordinates. -/
theorem hasDerivAt_comp_smul {g : ℝ^2 → ℝ} {v : ℝ^2} {s : ℝ}
    (hg : DifferentiableAt ℝ g (s • v)) :
    HasDerivAt (fun r : ℝ ↦ g (r • v)) (∑ a : Fin 2, (∂[a] g) (s • v) * v a) s := by
  have hray : HasDerivAt (fun r : ℝ ↦ r • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have := hg.hasFDerivAt.comp_hasDerivAt s hray
  rwa [fderiv_apply_eq_sum_partialDeriv_mul] at this

namespace IsSmoothToBoundary

variable {h : ℝ^2 → ℝ}

/-- The directional jets along one ray in a subset `S` of the half-plane vanish when
`h = o(|x|²)` on `S`. -/
theorem directional_jets_eq_zero (hh : IsSmoothToBoundary 2 h) {S : Set (ℝ^2)}
    (hS : S ⊆ upperHalfPlane) (ho : h =o[𝓝[S] 0] fun x ↦ ‖x‖ ^ 2) {ℓ : Fin 2 → ℝ}
    {L : Fin 2 → Fin 2 → ℝ} (hℓ : ∀ a, Tendsto (∂[a] h) (𝓝[upperHalfPlane] 0) (𝓝 (ℓ a)))
    (hL : ∀ a b, Tendsto (∂[b] (∂[a] h)) (𝓝[upperHalfPlane] 0) (𝓝 (L a b)))
    {v : ℝ^2} (hv : ∀ s : ℝ, 0 < s → s • v ∈ S) :
    ℓ 0 * v 0 + ℓ 1 * v 1 = 0 ∧
      (L 0 0 * v 0 + L 0 1 * v 1) * v 0 + (L 1 0 * v 0 + L 1 1 * v 1) * v 1 = 0 := by
  simp only [← Fin.sum_univ_two (f := fun a ↦ ℓ a * v a),
    ← Fin.sum_univ_two (f := fun b ↦ L 0 b * v b), ← Fin.sum_univ_two (f := fun b ↦ L 1 b * v b),
    ← Fin.sum_univ_two (f := fun a ↦ (∑ b : Fin 2, L a b * v b) * v a)]
  have hraS : Tendsto (fun s : ℝ ↦ s • v) (𝓝[>] 0) (𝓝[S] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
        (continuous_id.smul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s) using hv s hs
  have hray : Tendsto (fun s : ℝ ↦ s • v) (𝓝[>] 0) (𝓝[upperHalfPlane] 0) :=
    hraS.mono_right (nhdsWithin_mono _ hS)
  have hmem : ∀ s : ℝ, 0 < s → s • v ∈ upperHalfPlane := fun s hs ↦ hS (hv s hs)
  have hd0 : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ h (s • v) := fun s hs ↦
    hh.differentiableAt [] (by norm_num) (hmem s hs)
  have hd1 : ∀ a : Fin 2, ∀ s : ℝ, 0 < s → DifferentiableAt ℝ (∂[a] h) (s • v) :=
    fun a s hs ↦ hh.differentiableAt [a] (by norm_num) (hmem s hs)
  have hodd : (fun s : ℝ ↦ h (s • v)) =o[𝓝[>] 0] fun s ↦ s ^ 2 := by
    have h1 := ho.comp_tendsto hraS
    refine h1.trans_isBigO (IsBigO.of_bound (‖v‖ ^ 2) ?_)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hs, norm_pow]
    have : |s * ‖v‖| ^ 2 = ‖v‖ ^ 2 * s ^ 2 := by rw [sq_abs]; ring
    exact this.le
  refine PDE.Analysis.tendsto_deriv_eq_zero_of_isLittleO_sq (δ := 1) one_pos
    (h' := fun s ↦ ∑ a : Fin 2, (∂[a] h) (s • v) * v a)
    (h'' := fun s ↦ ∑ a : Fin 2, (∑ b : Fin 2, (∂[b] (∂[a] h)) (s • v) * v b) * v a)
    (fun s hs ↦ hasDerivAt_comp_smul (hd0 s hs.1)) (fun s hs ↦ ?_) ?_ ?_ hodd
  · exact HasDerivAt.fun_sum fun a _ ↦ (hasDerivAt_comp_smul (hd1 a s hs.1)).mul_const (v a)
  · exact tendsto_finsetSum _ fun a _ ↦ ((hℓ a).comp hray).mul_const (v a)
  · exact tendsto_finsetSum _ fun a _ ↦
      (tendsto_finsetSum _ fun b _ ↦ ((hL a b).comp hray).mul_const (v b)).mul_const (v a)

/-- **Jets from a little-o bound**: if `h` is `C²` up to the boundary near the origin and
`h = o(|x|²)` on the upper half-plane, then `h`, its first and its second derivatives tend to
zero at the origin. -/
theorem tendsto_jets_of_isLittleO (hh : IsSmoothToBoundary 2 h)
    (ho : h =o[𝓝[upperHalfPlane] 0] fun x ↦ ‖x‖ ^ 2) :
    Tendsto h (𝓝[upperHalfPlane] 0) (𝓝 0) ∧
      (∀ a, Tendsto (∂[a] h) (𝓝[upperHalfPlane] 0) (𝓝 0)) ∧
      ∀ a b, Tendsto (∂[b] (∂[a] h)) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  choose ℓ hℓ using fun a : Fin 2 ↦ hh.exists_tendsto [a] (by norm_num)
  choose L hL using fun a b : Fin 2 ↦ hh.exists_tendsto [b, a] (by norm_num)
  have hsq : Tendsto (fun x : ℝ^2 ↦ ‖x‖ ^ 2) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ^2 ↦ ‖x‖ ^ 2) (𝓝 0) (𝓝 (‖(0 : ℝ^2)‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have := neBot_upperHalfPlane_axis.mono (nhdsWithin_mono _ inter_subset_left)
  have hc := eqOn_partialDeriv_comm (hh.contDiffOn.of_le (by norm_num))
  have h01 : L 0 1 = L 1 0 :=
    tendsto_nhds_unique (hL 0 1) ((hL 1 0).congr' (eventuallyEq_nhdsWithin_of_eqOn hc.symm))
  set v₁ : ℝ^2 := EuclideanSpace.single 1 1
  set v₂ : ℝ^2 := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  set v₃ : ℝ^2 := -EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  have h10 : v₁ 0 = 0 := by simp [v₁]
  have h11 : v₁ 1 = 1 := by simp [v₁]
  have h20 : v₂ 0 = 1 := by simp [v₂]
  have h21 : v₂ 1 = 1 := by simp [v₂]
  have h30 : v₃ 0 = -1 := by simp [v₃]
  have h31 : v₃ 1 = 1 := by simp [v₃]
  have e1 := hh.directional_jets_eq_zero subset_rfl ho hℓ hL (v := v₁) fun s hs ↦
    smul_mem_upperHalfPlane (by rw [h11]; norm_num) hs
  have e2 := hh.directional_jets_eq_zero subset_rfl ho hℓ hL (v := v₂) fun s hs ↦
    smul_mem_upperHalfPlane (by rw [h21]; norm_num) hs
  have e3 := hh.directional_jets_eq_zero subset_rfl ho hℓ hL (v := v₃) fun s hs ↦
    smul_mem_upperHalfPlane (by rw [h31]; norm_num) hs
  rw [h10, h11] at e1
  rw [h20, h21] at e2
  rw [h30, h31] at e3
  have hℓ0 : ℓ 0 = 0 := by linarith [e1.1, e2.1, e3.1]
  have hℓ1 : ℓ 1 = 0 := by linarith [e1.1, e2.1, e3.1]
  have hL11 : L 1 1 = 0 := by linarith [e1.2]
  have hL01 : L 0 1 = 0 := by nlinarith [e1.2, e2.2, e3.2]
  have hL10 : L 1 0 = 0 := by rw [← h01, hL01]
  have hL00 : L 0 0 = 0 := by nlinarith [e1.2, e2.2, e3.2]
  refine ⟨ho.trans_tendsto hsq, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩⟩
  · have := hℓ 0; rw [hℓ0] at this; exact this
  · have := hℓ 1; rw [hℓ1] at this; exact this
  · have := hL 0 0; rw [hL00] at this; exact this
  · have := hL 0 1; rw [hL01] at this; exact this
  · have := hL 1 0; rw [hL10] at this; exact this
  · have := hL 1 1; rw [hL11] at this; exact this

/-- **Jets from a little-o bound on the quadrant**: if `h` is `C²` up to the boundary near the
origin and `h = o(|x|²)` on the open quadrant, then `h`, its first and its second derivatives tend
to zero at the origin from the upper half-plane. The rays in the directions `(1, 1)`, `(1, 2)` and
`(2, 1)` determine the jets. -/
theorem tendsto_jets_of_isLittleO_quadrant (hh : IsSmoothToBoundary 2 h)
    (ho : h =o[𝓝[{x : ℝ^2 | 0 < x 0 ∧ 0 < x 1}] 0] fun x ↦ ‖x‖ ^ 2) :
    Tendsto h (𝓝[upperHalfPlane] 0) (𝓝 0) ∧
      (∀ a, Tendsto (∂[a] h) (𝓝[upperHalfPlane] 0) (𝓝 0)) ∧
      ∀ a b, Tendsto (∂[b] (∂[a] h)) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  set Q : Set (ℝ^2) := {x | 0 < x 0 ∧ 0 < x 1}
  have hQ : Q ⊆ upperHalfPlane := fun x hx ↦ hx.2
  choose L₀ hL₀ using hh.exists_tendsto [] (by norm_num)
  choose ℓ hℓ using fun a : Fin 2 ↦ hh.exists_tendsto [a] (by norm_num)
  choose L hL using fun a b : Fin 2 ↦ hh.exists_tendsto [b, a] (by norm_num)
  have := neBot_upperHalfPlane_axis.mono (nhdsWithin_mono _ inter_subset_left)
  have hc := eqOn_partialDeriv_comm (hh.contDiffOn.of_le (by norm_num))
  have h01 : L 0 1 = L 1 0 :=
    tendsto_nhds_unique (hL 0 1) ((hL 1 0).congr' (eventuallyEq_nhdsWithin_of_eqOn hc.symm))
  set v₁ : ℝ^2 := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  set v₂ : ℝ^2 := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 2
  set v₃ : ℝ^2 := EuclideanSpace.single 0 2 + EuclideanSpace.single 1 1
  have h10 : v₁ 0 = 1 := by simp [v₁]
  have h11 : v₁ 1 = 1 := by simp [v₁]
  have h20 : v₂ 0 = 1 := by simp [v₂]
  have h21 : v₂ 1 = 2 := by simp [v₂]
  have h30 : v₃ 0 = 2 := by simp [v₃]
  have h31 : v₃ 1 = 1 := by simp [v₃]
  have hmem : ∀ v : ℝ^2, 0 < v 0 → 0 < v 1 → ∀ s : ℝ, 0 < s → s • v ∈ Q := fun v h0 h1 s hs ↦
    ⟨by simpa using mul_pos hs h0, by simpa using mul_pos hs h1⟩
  have e1 := hh.directional_jets_eq_zero hQ ho hℓ hL (v := v₁)
    (hmem v₁ (by rw [h10]; norm_num) (by rw [h11]; norm_num))
  have e2 := hh.directional_jets_eq_zero hQ ho hℓ hL (v := v₂)
    (hmem v₂ (by rw [h20]; norm_num) (by rw [h21]; norm_num))
  have e3 := hh.directional_jets_eq_zero hQ ho hℓ hL (v := v₃)
    (hmem v₃ (by rw [h30]; norm_num) (by rw [h31]; norm_num))
  rw [h10, h11] at e1
  rw [h20, h21] at e2
  rw [h30, h31] at e3
  have hℓ0 : ℓ 0 = 0 := by linarith [e1.1, e2.1]
  have hℓ1 : ℓ 1 = 0 := by linarith [e1.1, e2.1]
  have hL01 : L 0 1 = 0 := by linarith [e1.2, e2.2, e3.2]
  have hL10 : L 1 0 = 0 := by rw [← h01, hL01]
  have hL00 : L 0 0 = 0 := by linarith [e1.2, e2.2, e3.2]
  have hL11 : L 1 1 = 0 := by linarith [e1.2, e2.2, e3.2]
  have hray : Tendsto (fun s : ℝ ↦ s • v₁) (𝓝[>] 0) (𝓝[Q] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s • v₁) (𝓝 0) (𝓝 ((0 : ℝ) • v₁)) :=
        (continuous_id.smul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      exact hmem v₁ (by rw [h10]; norm_num) (by rw [h11]; norm_num) s hs
  have : (𝓝[Q] (0 : ℝ^2)).NeBot := hray.neBot
  have hsq : Tendsto (fun x : ℝ^2 ↦ ‖x‖ ^ 2) (𝓝[Q] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ^2 ↦ ‖x‖ ^ 2) (𝓝 0) (𝓝 (‖(0 : ℝ^2)‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hL₀0 : L₀ = 0 :=
    tendsto_nhds_unique ((hL₀.mono_left (nhdsWithin_mono _ hQ))) (ho.trans_tendsto hsq)
  refine ⟨?_, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩⟩
  · rw [hL₀0] at hL₀; exact hL₀
  · have := hℓ 0; rw [hℓ0] at this; exact this
  · have := hℓ 1; rw [hℓ1] at this; exact this
  · have := hL 0 0; rw [hL00] at this; exact this
  · have := hL 0 1; rw [hL01] at this; exact this
  · have := hL 1 0; rw [hL10] at this; exact this
  · have := hL 1 1; rw [hL11] at this; exact this

/-- **Second-order jets from a cubic bound**: if `g` is `C²` on the plane, `L` is `C²` up to the
boundary near the origin and `g - L = O(|x|³)` on the upper half-plane, then each second
derivative of `g` at the origin is the limit of that of `L`. -/
theorem partialDeriv_partialDeriv_eq_of_isBigO {g L : ℝ^2 → ℝ} (hg : ContDiff ℝ 2 g)
    (hL : IsSmoothToBoundary 2 L)
    (ho : (fun x ↦ g x - L x) =O[𝓝[upperHalfPlane] 0] fun x ↦ ‖x‖ ^ 3) (a b : Fin 2) {ℓ : ℝ}
    (hℓ : Tendsto (∂[b] (∂[a] L)) (𝓝[upperHalfPlane] 0) (𝓝 ℓ)) :
    (∂[b] (∂[a] g)) 0 = ℓ := by
  have hh : IsSmoothToBoundary 2 (fun x ↦ g x - L x) := (of_contDiff hg).sub hL
  have ho' : (fun x ↦ g x - L x) =o[𝓝[upperHalfPlane] 0] fun x ↦ ‖x‖ ^ 2 :=
    ho.trans_isLittleO ((isLittleO_norm_pow_norm_pow (by norm_num : 2 < 3)).mono
      nhdsWithin_le_nhds)
  obtain ⟨-, -, h2⟩ := hh.tendsto_jets_of_isLittleO ho'
  have hgc : ContinuousAt (∂[b] (∂[a] g)) 0 :=
    ((contDiff_partialDeriv_of_succ (m := 0) (contDiff_partialDeriv_of_succ (m := 1)
      hg)).continuous).continuousAt
  have hsub := eqOn_partialDeriv_partialDeriv_sub isOpen_upperHalfPlane
    (hg.contDiffOn) hL.contDiffOn b a
  have hdiff : Tendsto (fun x ↦ (∂[b] (∂[a] g)) x - (∂[b] (∂[a] L)) x) (𝓝[upperHalfPlane] 0)
      (𝓝 0) := (h2 a b).congr' (eventuallyEq_nhdsWithin_of_eqOn hsub)
  have hg' := hgc.tendsto.mono_left (nhdsWithin_le_nhds (s := upperHalfPlane))
  have := neBot_upperHalfPlane_axis.mono (nhdsWithin_mono _ inter_subset_left)
  have hlim := tendsto_nhds_unique (hg'.sub hℓ) hdiff
  linarith

end IsSmoothToBoundary

end Boussinesq
