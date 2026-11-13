/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Backward invariance of a region with an outgoing boundary

If a transport field points out of a region `{g < c}` on its boundary `{g = c}`, a characteristic
that ends inside the region was inside it at all earlier times: the last time at which it was on
the boundary or outside would be a time where `g` crosses the level `c` downwards along the path,
while the outgoing condition makes `g` increase there. For the disc `|x| < r` this is the backward
invariance of the inner region of Chen and Hou, Part I, Section 6.5, under their Assumption 2: the
solution in `|x| < ν/2` does not depend on its values outside.

## Main results

* `lt_of_hasDerivWithinAt_pos_of_eq`: a continuous function on `[t₀, t]` below `c` at `t` whose
  right derivative is positive at every time where it equals `c` stays below `c` on `[t₀, t]`.
* `norm_lt_of_inner_pos`: a path with `γ' = w` that ends in the open ball of radius `r` and has
  `⟪w, γ⟫ > 0` whenever `‖γ‖ = r` stays in that ball.

## References

* J. Chen and T. Y. Hou, *Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis*, arXiv:2210.07191v4, Assumption 2 and Section 6.5.
  <https://arxiv.org/abs/2210.07191>
-/

@[expose] public section

open Set Filter Topology

namespace PDE.Hyperbolic.Transport

/-- **No downward crossing of a level with a positive right derivative.** Let `φ` be continuous
on `[t₀, t]` with `φ t < c`, and at every time `s ∈ [t₀, t)` with `φ s = c` let `φ` have a positive
right derivative. Then `φ < c` on `[t₀, t]`. -/
theorem lt_of_hasDerivWithinAt_pos_of_eq {φ φ' : ℝ → ℝ} {t₀ t c : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ t))
    (hd : ∀ s ∈ Ico t₀ t, φ s = c → HasDerivWithinAt φ (φ' s) (Ioi s) s ∧ 0 < φ' s)
    (ht : φ t < c) : ∀ s ∈ Icc t₀ t, φ s < c := by
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨s₀, hs₀, hc₀⟩ := hcon
  set A := Icc t₀ t ∩ φ ⁻¹' Ici c with hA
  have hAc : IsClosed A := hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAb : BddAbove A := ⟨t, fun s hs ↦ hs.1.2⟩
  have hne : A.Nonempty := ⟨s₀, hs₀, hc₀⟩
  have hmem : sSup A ∈ A := hAc.csSup_mem hne hAb
  set s := sSup A with hs
  -- the last time in `A` is before `t`
  have hst : s < t := by
    rcases eq_or_lt_of_le hmem.1.2 with h | h
    · exact absurd hmem.2 (by rw [h]; exact not_le.mpr ht)
    · exact h
  -- after the last time the function is below `c`
  have hafter : ∀ u ∈ Ioc s t, φ u < c := fun u hu ↦ by
    by_contra hle
    exact absurd (le_csSup hAb ⟨⟨hmem.1.1.trans hu.1.le, hu.2⟩, not_lt.mp hle⟩) (not_le.mpr hu.1)
  -- so the value at the last time is `c`
  have hcl : ContinuousWithinAt φ (Ioc s t) s :=
    (hφ s hmem.1).mono fun u hu ↦ ⟨hmem.1.1.trans hu.1.le, hu.2⟩
  have hnb : (𝓝[Ioc s t] s).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hst.ne]
    exact left_mem_Icc.mpr hst.le
  have hle : φ s ≤ c :=
    le_of_tendsto hcl (eventually_nhdsWithin_of_forall fun u hu ↦ (hafter u hu).le)
  have heq : φ s = c := le_antisymm hle hmem.2
  obtain ⟨hder, hpos⟩ := hd s ⟨hmem.1.1, hst⟩ heq
  -- the positive right derivative pushes `φ` above `c` just after `s`
  have hslope : Tendsto (slope φ s) (𝓝[>] s) (𝓝 (φ' s)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mp hder
  have hev : ∀ᶠ u in 𝓝[>] s, 0 < slope φ s u := hslope.eventually (lt_mem_nhds hpos)
  obtain ⟨u, hu, huI⟩ := (hev.and (Ioo_mem_nhdsGT hst)).exists
  have hsu : 0 < u - s := sub_pos.mpr huI.1
  rw [slope_def_field] at hu
  have hφu : c < φ u := by
    have := (div_pos_iff_of_pos_right hsu).mp hu
    linarith
  exact absurd (hafter u ⟨huI.1, huI.2.le⟩) (not_lt.mpr hφu.le)

/-- **Backward invariance of a ball under an outgoing field.** Let `γ' = w` on `[t₀, t]` in a real
inner product space, `‖γ t‖ < r`, and `⟪w s, γ s⟫ > 0` at every time `s ∈ [t₀, t)` with
`‖γ s‖ = r`. Then `‖γ s‖ < r` on `[t₀, t]`. -/
theorem norm_lt_of_inner_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ w : ℝ → E} {t₀ t r : ℝ} (hγ : ∀ s ∈ Icc t₀ t, HasDerivAt γ (w s) s)
    (hout : ∀ s ∈ Ico t₀ t, ‖γ s‖ = r → 0 < inner ℝ (w s) (γ s)) (ht : ‖γ t‖ < r) :
    ∀ s ∈ Icc t₀ t, ‖γ s‖ < r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans ht.le
  have hcont : ContinuousOn (fun s ↦ ‖γ s‖ ^ 2) (Icc t₀ t) := fun s hs ↦
    ((hγ s hs).continuousAt.norm.pow 2).continuousWithinAt
  have h := lt_of_hasDerivWithinAt_pos_of_eq (c := r ^ 2)
    (φ' := fun s ↦ 2 * inner ℝ (w s) (γ s)) hcont (fun s hs hsr ↦ ?_)
    (by gcongr)
  · intro s hs
    have := h s hs
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).mp this
  · have hn : ‖γ s‖ = r := (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp hsr
    refine ⟨?_, by linarith [hout s hs hn]⟩
    have hd := ((hγ s (Ico_subset_Icc_self hs)).norm_sq).hasDerivWithinAt (s := Ioi s)
    exact hd.congr_deriv (by rw [real_inner_comm])

end PDE.Hyperbolic.Transport
