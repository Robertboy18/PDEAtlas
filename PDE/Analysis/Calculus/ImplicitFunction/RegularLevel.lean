/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Regular level graphs on one open neighborhood

Mathlib's implicit function theorem supplies a graph germ. If the defining function
is `C^m` on an open set, the graph is `C^m` on one open neighborhood, including when
`m = ∞`. A fixed `C¹` graph is first chosen. At each nearby graph point, uniqueness
identifies it with the implicit function supplied at that point at order `m`.
No passage from pointwise infinite differentiability to an infinite-order germ is used.
-/

@[expose] public section

open Filter Set
open scoped Topology ContDiff

private theorem isInvertible_of_apply_one_ne_zero
    (ℓ : ℝ →L[ℝ] ℝ) (hℓ : ℓ 1 ≠ 0) : ℓ.IsInvertible := by
  have happ (t : ℝ) : ℓ t = t * ℓ 1 := by
    simpa only [smul_eq_mul, mul_one] using ℓ.map_smul t (1 : ℝ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (ℓ 1)⁻¹)
  · apply ContinuousLinearMap.ext
    intro t
    change ℓ (t * (ℓ 1)⁻¹) = t
    rw [happ, mul_assoc, inv_mul_cancel₀ hℓ, mul_one]
  · apply ContinuousLinearMap.ext
    intro t
    change ℓ t * (ℓ 1)⁻¹ = t
    rw [happ, mul_assoc, mul_inv_cancel₀ hℓ, mul_one]

/-- A regular scalar level in a product space admits one graph that is `C^m` on
an open neighborhood. The statement retains a common neighborhood at infinite order. -/
theorem ContDiffOn.exists_implicitFunction_of_fderiv_snd_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : ℕ∞} {f : E × ℝ → ℝ} {U : Set (E × ℝ)} {x : E × ℝ}
    (hf : ContDiffOn ℝ m f U) (hU : IsOpen U) (hm : 1 ≤ m) (hx : x ∈ U)
    (hpartial : fderiv ℝ f x (0, 1) ≠ 0) :
    ∃ g : E → ℝ, ∃ s : Set E,
      IsOpen s ∧ x.1 ∈ s ∧ ContDiffOn ℝ m g s ∧ g x.1 = x.2 ∧
        (∀ q ∈ s, (q, g q) ∈ U ∧ f (q, g q) = f x) ∧
        ∀ᶠ y in 𝓝 x, f y = f x ↔ g y.1 = y.2 := by
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hmne : (m : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one hm').ne'
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  have hf1 : ContDiffAt ℝ 1 f x := hfx.of_le hm'
  have hinv : (fderiv ℝ f x ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible :=
    isInvertible_of_apply_one_ne_zero _ hpartial
  let g := hf1.implicitFunction one_ne_zero hinv
  have hg1 : ContDiffAt ℝ 1 g x.1 :=
    hf1.contDiffAt_implicitFunction one_ne_zero hinv
  have hgx : g x.1 = x.2 := hf1.implicitFunction_apply_self one_ne_zero hinv
  have hgraph : ∀ᶠ q in 𝓝 x.1, f (q, g q) = f x :=
    hf1.eventually_apply_implicitFunction one_ne_zero hinv
  have hmap : Tendsto (fun q ↦ (q, g q)) (𝓝 x.1) (𝓝 x) := by
    simpa only [id_eq, hgx, Prod.eta] using
      (continuousAt_id.prodMk hg1.continuousAt).tendsto
  have hne : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (0, 1) ≠ 0 :=
    ((hf1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).eventually_ne
      hpartial
  have hnear : ∀ᶠ q in 𝓝 x.1,
      ContDiffAt ℝ 1 g q ∧ (q, g q) ∈ U ∧
        f (q, g q) = f x ∧ fderiv ℝ f (q, g q) (0, 1) ≠ 0 := by
    filter_upwards [hg1.eventually (by simp), hmap (hU.mem_nhds hx), hgraph, hmap hne]
      with q hqg hqU hqeq hqne
    exact ⟨hqg, hqU, hqeq, hqne⟩
  obtain ⟨s, hsnear, hsopen, hxs⟩ := mem_nhds_iff.mp hnear
  refine ⟨g, s, hsopen, hxs, ?_, hgx,
    fun q hq ↦ ⟨(hsnear hq).2.1, (hsnear hq).2.2.1⟩,
    hf1.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv⟩
  intro q hq
  obtain ⟨hqg, hqU, hqeq, hqne⟩ := hsnear hq
  have hfq := hf.contDiffAt (hU.mem_nhds hqU)
  have hiq : (fderiv ℝ f (q, g q) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible :=
    isInvertible_of_apply_one_ne_zero _ hqne
  have hmapq : Tendsto (fun r ↦ (r, g r)) (𝓝 q) (𝓝 (q, g q)) :=
    (continuousAt_id.prodMk hqg.continuousAt).tendsto
  have heq : g =ᶠ[𝓝 q] hfq.implicitFunction hmne hiq := by
    filter_upwards [hmapq (hfq.eventually_apply_eq_iff_implicitFunction hmne hiq),
      hsopen.mem_nhds hq] with r hr hrs
    exact (hr.mp ((hsnear hrs).2.2.1.trans hqeq.symm)).symm
  exact ((hfq.contDiffAt_implicitFunction hmne hiq).congr_of_eventuallyEq heq).contDiffWithinAt
