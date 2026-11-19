/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local bounds for derivatives of a composition

Mathlib's quantitative Faà di Bruno estimate applies on sets with unique derivatives.
Localizing to open neighborhoods gives a pointwise estimate under finite `C^n`
hypotheses. A second estimate controls the whole finite jet by one constant, as needed
when composing a profile with a coordinate map.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace PDE.Analysis

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A pointwise Faà di Bruno estimate needs only finite local regularity. -/
theorem norm_iteratedFDeriv_comp_le_of_contDiffAt
    {f : E → F} {g : F → G} {x : E} {n : ℕ} {B D : ℝ}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g (f x))
    (hB : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ n.factorial * B * D ^ n := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, htv, ht, hxt⟩ := mem_nhds_iff.mp hv
  obtain ⟨s, hsu, hs, hxs⟩ :=
    mem_nhds_iff.mp (inter_mem hu (hf.continuousAt.preimage_mem_nhds (ht.mem_nhds hxt)))
  have hst : MapsTo f s t := fun _ hy ↦ (hsu hy).2
  have hbound := norm_iteratedFDerivWithin_comp_le (hgv.mono htv)
    (hfu.mono (fun y hy ↦ (hsu hy).1)) le_rfl ht.uniqueDiffOn hs.uniqueDiffOn hst hxs
    (C := B) (D := D)
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv ht.uniqueDiffOn
        (hg.of_le (Nat.cast_le.mpr hi)) hxt]
      exact hB i hi)
    (fun i hi hin ↦ by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
        (hf.of_le (Nat.cast_le.mpr hin)) hxs]
      exact hD i hi hin)
  rwa [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hg.comp x hf) hxs] at hbound

/-- If positive derivatives of the inner map are bounded by `D ≥ 1`, all derivatives of
the composition through order `m` have the common bound `m! * B * D^m`. -/
theorem norm_iteratedFDeriv_comp_le_uniform
    {f : E → F} {g : F → G} {x : E} {m : ℕ} {B D : ℝ}
    (hf : ContDiffAt 𝕜 m f x) (hg : ContDiffAt 𝕜 m g (f x)) (hD : 1 ≤ D)
    (hB : ∀ i ≤ m, ‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ B)
    (hfD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D)
    {k : ℕ} (hk : k ≤ m) :
    ‖iteratedFDeriv 𝕜 k (g ∘ f) x‖ ≤ m.factorial * B * D ^ m := by
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le m))
  have hbound := norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hf.of_le (Nat.cast_le.mpr hk)) (hg.of_le (Nat.cast_le.mpr hk))
    (fun i hi ↦ hB i (hi.trans hk))
    (fun i hi hik ↦ (hfD i hi (hik.trans hk)).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by
    exact_mod_cast Nat.factorial_le hk
  exact hbound.trans (mul_le_mul (mul_le_mul_of_nonneg_right hfac hBnonneg)
    (pow_le_pow_right₀ hD hk) (by positivity) (by positivity))

end PDE.Analysis
