/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.OriginJetUniqueness
import PDE.FDeriv.Laplacian.Product

/-!
# Origin jets of products

For functions `f`, `g` smooth up to the boundary near the origin (`IsSmoothToBoundary 2`), the
second derivatives of `f g` on the open upper half-plane tend to the value of the Leibniz rule
`∂_b∂_a(fg) = (∂_b∂_a f) g + ∂_a f ∂_b g + ∂_b f ∂_a g + f ∂_b∂_a g` at the limits of the jets of
`f` and `g`. The first derivatives behave in the same way. These rules compute the jets at the
origin of the bilinear transport and stretching terms of the Boussinesq equations from the jets of
their factors, as limits from the interior.

A function `C¹` up to the boundary that is `o(|x|)` on the open upper half-plane has value and
first derivatives tending to zero at the origin
(`IsSmoothToBoundary.tendsto_jets_of_isLittleO_norm`, by l'Hôpital's rule along the rays in the
directions `(0, 1)` and `(1, 1)`); in particular this holds for functions vanishing to second
order.

## Main results

* `IsSmoothToBoundary.tendsto_partialDeriv_mul`: the first-order Leibniz rule at the origin.
* `IsSmoothToBoundary.tendsto_partialDeriv_partialDeriv_mul`: the second-order Leibniz rule at
  the origin, `∂_b∂_a(fg) → f_{ab} g₀ + f_a g_b + f_b g_a + f₀ g_{ab}`.
* `IsSmoothToBoundary.tendsto_jets_of_isLittleO_norm`: if `h` is `C¹` up to the boundary and
  `h = o(|x|)` on the upper half-plane, then `h` and its first derivatives tend to zero at the
  origin.
-/

@[expose] public section

noncomputable section

open Filter Set PDE Asymptotics
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

namespace IsSmoothToBoundary

variable {f g : ℝ^2 → ℝ}

/-- A function `C^k` up to the boundary is `C^k` at every point of the open upper half-plane. -/
private theorem contDiffAt_of_mem {k : ℕ} (hf : IsSmoothToBoundary k f) {x : ℝ^2}
    (hx : x ∈ upperHalfPlane) : ContDiffAt ℝ k f x :=
  hf.contDiffOn.contDiffAt (isOpen_upperHalfPlane.mem_nhds hx)

/-- **The first-order Leibniz rule at the origin.** -/
theorem tendsto_partialDeriv_mul (hf : IsSmoothToBoundary 1 f) (hg : IsSmoothToBoundary 1 g)
    (a : Fin 2) {f₀ fa g₀ ga : ℝ} (h₀ : Tendsto f (𝓝[upperHalfPlane] 0) (𝓝 f₀))
    (ha : Tendsto (∂[a] f) (𝓝[upperHalfPlane] 0) (𝓝 fa))
    (k₀ : Tendsto g (𝓝[upperHalfPlane] 0) (𝓝 g₀))
    (ka : Tendsto (∂[a] g) (𝓝[upperHalfPlane] 0) (𝓝 ga)) :
    Tendsto (∂[a] (fun x ↦ f x * g x)) (𝓝[upperHalfPlane] 0) (𝓝 (fa * g₀ + f₀ * ga)) := by
  refine ((ha.mul k₀).add (h₀.mul ka)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (partialDeriv_mul ((contDiffAt_of_mem hf hx).differentiableAt one_ne_zero)
    ((contDiffAt_of_mem hg hx).differentiableAt one_ne_zero)).symm

/-- **The second-order Leibniz rule at the origin**: if `f`, `g` are `C²` up to the boundary and
their jets of order at most two along `a`, `b` have the stated limits, then
`∂_b∂_a(fg) → f_{ab} g₀ + f_a g_b + f_b g_a + f₀ g_{ab}`. -/
theorem tendsto_partialDeriv_partialDeriv_mul (hf : IsSmoothToBoundary 2 f)
    (hg : IsSmoothToBoundary 2 g) (a b : Fin 2) {f₀ fa fb fab g₀ ga gb gab : ℝ}
    (h₀ : Tendsto f (𝓝[upperHalfPlane] 0) (𝓝 f₀))
    (ha : Tendsto (∂[a] f) (𝓝[upperHalfPlane] 0) (𝓝 fa))
    (hb : Tendsto (∂[b] f) (𝓝[upperHalfPlane] 0) (𝓝 fb))
    (hab : Tendsto (∂[b] (∂[a] f)) (𝓝[upperHalfPlane] 0) (𝓝 fab))
    (k₀ : Tendsto g (𝓝[upperHalfPlane] 0) (𝓝 g₀))
    (ka : Tendsto (∂[a] g) (𝓝[upperHalfPlane] 0) (𝓝 ga))
    (kb : Tendsto (∂[b] g) (𝓝[upperHalfPlane] 0) (𝓝 gb))
    (kab : Tendsto (∂[b] (∂[a] g)) (𝓝[upperHalfPlane] 0) (𝓝 gab)) :
    Tendsto (∂[b] (∂[a] (fun x ↦ f x * g x))) (𝓝[upperHalfPlane] 0)
      (𝓝 (fab * g₀ + fa * gb + fb * ga + f₀ * gab)) := by
  refine ((((hab.mul k₀).add (ha.mul kb)).add (hb.mul ka)).add (h₀.mul kab)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (secondPartialDeriv_mul b a (contDiffAt_of_mem hf hx) (contDiffAt_of_mem hg hx)).symm

/-- **First-order jets from a little-o bound**: if `h` is `C¹` up to the boundary near the origin
and `h = o(|x|)` on the upper half-plane, then `h` and its first derivatives tend to zero at the
origin. -/
theorem tendsto_jets_of_isLittleO_norm {h : ℝ^2 → ℝ} (hh : IsSmoothToBoundary 1 h)
    (ho : h =o[𝓝[upperHalfPlane] 0] fun x ↦ ‖x‖) :
    Tendsto h (𝓝[upperHalfPlane] 0) (𝓝 0) ∧
      ∀ a, Tendsto (∂[a] h) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  have hn : Tendsto (fun x : ℝ^2 ↦ ‖x‖) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ^2 ↦ ‖x‖) (𝓝 0) (𝓝 ‖(0 : ℝ^2)‖) := continuous_norm.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto h (𝓝[upperHalfPlane] 0) (𝓝 0) := ho.trans_tendsto hn
  choose ℓ hℓ' using fun a : Fin 2 ↦ hh.exists_tendsto [a] (by norm_num)
  have hℓ : ∀ a : Fin 2, Tendsto (∂[a] h) (𝓝[upperHalfPlane] 0) (𝓝 (ℓ a)) := hℓ'
  -- along a ray in the open half-plane, the directional derivative has limit zero
  have ray : ∀ v : ℝ^2, 0 < v 1 → ℓ 0 * v 0 + ℓ 1 * v 1 = 0 := by
    intro v hv
    have hray := tendsto_smul_upperHalfPlane hv
    have hd : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ h (s • v) := fun s hs ↦
      hh.differentiableAt [] (by norm_num) (smul_mem_upperHalfPlane hv hs)
    have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hq1 : Tendsto (fun s ↦ h (s • v) / s) (𝓝[>] 0) (𝓝 (∑ a : Fin 2, ℓ a * v a)) := by
      refine HasDerivAt.lhopital_zero_nhdsGT (f' := fun s ↦ ∑ a : Fin 2, (∂[a] h) (s • v) * v a)
        (g' := fun _ ↦ 1) ?_ (Eventually.of_forall fun s ↦ hasDerivAt_id s)
        (Eventually.of_forall fun _ ↦ one_ne_zero) (h0.comp hray) hid ?_
      · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        exact hasDerivAt_comp_smul (hd s hs)
      · simpa using tendsto_finsetSum Finset.univ fun a _ ↦ ((hℓ a).comp hray).mul_const (v a)
    have hq0 : Tendsto (fun s ↦ h (s • v) / s) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ho.comp_tendsto hray
      have h2 : (fun s : ℝ ↦ h (s • v)) =o[𝓝[>] 0] fun s ↦ s := by
        refine h1.trans_isBigO (IsBigO.of_bound ‖v‖ ?_)
        filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
        rw [mul_comm, abs_of_nonneg (by positivity)]
      exact h2.tendsto_div_nhds_zero
    have := tendsto_nhds_unique hq1 hq0
    simpa [Fin.sum_univ_two] using this
  set v₁ : ℝ^2 := EuclideanSpace.single 1 1
  set v₂ : ℝ^2 := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  have h10 : v₁ 0 = 0 := by simp [v₁]
  have h11 : v₁ 1 = 1 := by simp [v₁]
  have h20 : v₂ 0 = 1 := by simp [v₂]
  have h21 : v₂ 1 = 1 := by simp [v₂]
  have e1 := ray v₁ (by rw [h11]; norm_num)
  have e2 := ray v₂ (by rw [h21]; norm_num)
  rw [h10, h11] at e1
  rw [h20, h21] at e2
  have hℓ1 : ℓ 1 = 0 := by linarith
  have hℓ0 : ℓ 0 = 0 := by linarith
  refine ⟨h0, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · simpa [hℓ0] using hℓ 0
  · simpa [hℓ1] using hℓ 1

end IsSmoothToBoundary

end Boussinesq
