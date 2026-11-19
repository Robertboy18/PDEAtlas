/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Spatial
import PDE.Analysis.Calculus.SpaceTime.Regularity
import PDE.Analysis.Calculus.MixedDerivative

/-!
# Time derivatives of spatially smooth families

`IsTimeSmooth T n f` says that `f` is spatially smooth on `[0, T]` (`IsSpatiallySmooth`) and has
`n` successive time derivatives within `[0, T]`, each again spatially smooth. A family with this
property for every `n` is `C^∞` on `ℝ × [0, T]`, with one-sided time derivatives at the
endpoints. The class is closed under sums and products, under spatial differentiation
(mixed derivatives commute by `hasDerivWithinAt_spatial_deriv_of_continuous_transport`) and the
spatial primitive (differentiation under the integral). At the endpoints of `[0, T]` the time
derivatives come from the fundamental theorem of calculus (`hasDerivWithinAt_Icc_of_interior`).
The spatial Hilbert transform is in `PDE.Analysis.Fourier.HilbertTransform.Parametric.Smooth`.

## Main results

* `IsTimeSmooth`: the classes, with their closure properties.
* `IsTimeSmooth.contDiffOn`: `IsTimeSmooth T n f` gives `C^n` regularity on `ℝ × [0, T]`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff NNReal

namespace PDE.Analysis

/-- `f` is spatially smooth on `[0, T]` and has `n` successive time derivatives within `[0, T]`,
each of them spatially smooth. -/
def IsTimeSmooth (T : ℝ) : ℕ → (ℝ → ℝ → ℝ) → Prop
  | 0, f => IsSpatiallySmooth T f
  | n + 1, f => IsSpatiallySmooth T f ∧ ∃ g, IsTimeSmooth T n g ∧
      ∀ x, ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (f x) (g x t) (Icc 0 T) t

/-- A function continuous on `[0, T]` whose derivative in `(0, T)` extends continuously to
`[0, T]` has this extension as derivative within `[0, T]` at every point. -/
theorem hasDerivWithinAt_Icc_of_interior {T : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) (hψ : ContinuousOn ψ (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt φ (ψ t) t) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt φ (ψ t) (Icc 0 T) t := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  let Ψ : ℝ → ℝ := fun s ↦ ψ (projIcc 0 T hT s)
  have hΨ : Continuous Ψ := (continuousOn_iff_continuous_domRestrict.mp hψ).comp
    (continuous_projIcc (h := hT))
  have hformula (s : ℝ) (hs : s ∈ Icc 0 T) : φ s = φ 0 + ∫ r in 0..s, Ψ r := by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (hφ.mono (Icc_subset_Icc_right hs.2))
      (fun r hr ↦ by
        have := hd r ⟨hr.1, hr.2.trans_le hs.2⟩
        simpa only [Ψ, projIcc_of_mem hT ⟨hr.1.le, hr.2.le.trans hs.2⟩] using this)
      (hΨ.intervalIntegrable 0 s)
    linarith
  have hp : HasDerivWithinAt (fun s ↦ φ 0 + ∫ r in 0..s, Ψ r) (Ψ t) (Icc 0 T) t :=
    ((hΨ.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (φ 0)).hasDerivWithinAt
  have hq := hp.congr_of_mem hformula ht
  simpa only [Ψ, projIcc_of_mem hT ht] using hq

/-- The time derivative of a family of bounded support has bounded support. -/
theorem HasBoundedSupport.of_hasDerivWithinAt {T : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : HasBoundedSupport T f) (hT : 0 < T)
    (hd : ∀ x, ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (f x) (g x t) (Icc 0 T) t) :
    HasBoundedSupport T g := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L, fun t ht x hx ↦ ?_⟩
  have hzero : HasDerivWithinAt (f x) 0 (Icc 0 T) t :=
    (hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)).congr (fun s hs ↦ hL s hs x hx) (hL t ht x hx)
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hd x t ht) hzero

namespace IsTimeSmooth

variable {T : ℝ} {f g : ℝ → ℝ → ℝ}

/-- The underlying spatial smoothness. -/
theorem spatial : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T n f → IsSpatiallySmooth T f
  | 0, _, h => h
  | _ + 1, _, h => h.1

/-- Fewer time derivatives. -/
theorem mono : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T (n + 1) f → IsTimeSmooth T n f
  | 0, _, h => h.1
  | n + 1, _, h => by
    obtain ⟨hs, g, hg, hd⟩ := h
    exact ⟨hs, g, mono hg, hd⟩

/-- Sums of families with `n` time derivatives have `n` time derivatives. -/
theorem add : ∀ {n : ℕ} {f g : ℝ → ℝ → ℝ}, IsTimeSmooth T n f → IsTimeSmooth T n g →
    IsTimeSmooth T n (fun x t ↦ f x t + g x t)
  | 0, _, _, hf, hg => IsSpatiallySmooth.add hf hg
  | n + 1, _, _, hf, hg => by
    obtain ⟨hfs, f', hf', hfd⟩ := hf
    obtain ⟨hgs, g', hg', hgd⟩ := hg
    exact ⟨hfs.add hgs, _, add hf' hg', fun x t ht ↦ (hfd x t ht).add (hgd x t ht)⟩

/-- Constants have every number of time derivatives. -/
theorem const (a : ℝ) : ∀ n : ℕ, IsTimeSmooth T n (fun _ _ ↦ a)
  | 0 => IsSpatiallySmooth.const T a
  | n + 1 => ⟨IsSpatiallySmooth.const T a, _, const 0 n,
      fun _ _ _ ↦ hasDerivWithinAt_const _ _ a⟩

/-- Products of families with `n` time derivatives have `n` time derivatives. -/
theorem mul : ∀ {n : ℕ} {f g : ℝ → ℝ → ℝ}, IsTimeSmooth T n f → IsTimeSmooth T n g →
    IsTimeSmooth T n (fun x t ↦ f x t * g x t)
  | 0, _, _, hf, hg => IsSpatiallySmooth.mul hf hg
  | n + 1, f, g, hf, hg => by
    have hfn := mono hf
    have hgn := mono hg
    obtain ⟨hfs, f', hf', hfd⟩ := hf
    obtain ⟨hgs, g', hg', hgd⟩ := hg
    exact ⟨hfs.mul hgs, _, add (mul hf' hgn) (mul hfn hg'),
      fun x t ht ↦ (hfd x t ht).mul (hgd x t ht)⟩

/-- Spatial differentiation preserves the number of time derivatives: mixed derivatives commute
on `ℝ × [0, T]`, including the one-sided endpoint derivatives. -/
theorem derivX (hT : 0 < T) : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T n f →
    IsTimeSmooth T n (PDE.Analysis.derivX f)
  | 0, _, h => IsSpatiallySmooth.derivX h
  | n + 1, f, h => by
    obtain ⟨hs, g, hg, hd⟩ := h
    have hgs := spatial hg
    refine ⟨hs.derivX, PDE.Analysis.derivX g, derivX hT hg, fun x t ht ↦ ?_⟩
    exact hasDerivWithinAt_spatial_deriv_of_continuous_transport hT
      (by simpa only [Function.iterate_zero, id] using hs.continuous 0)
      (by simpa only [Function.iterate_zero, id] using hgs.continuous 0)
      (by simpa only [Function.iterate_one] using hgs.continuous 1)
      (fun t ht ↦ (hs.contDiff t ht).differentiable (by simp))
      (fun x t ht ↦ ((hgs.contDiff t ht).differentiable (by simp) x).hasDerivAt)
      (fun x t ht ↦ (hd x t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      x ht

/-- The spatial primitive preserves the number of time derivatives. -/
theorem primitiveX (hT : 0 < T) : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T n f →
    IsTimeSmooth T n (PDE.Analysis.primitiveX f)
  | 0, _, h => IsSpatiallySmooth.primitiveX h
  | n + 1, f, h => by
    obtain ⟨hs, g, hg, hd⟩ := h
    have hgs := spatial hg
    refine ⟨hs.primitiveX, PDE.Analysis.primitiveX g, primitiveX hT hg,
      fun x ↦ hasDerivWithinAt_Icc_of_interior (hs.primitiveX.continuousOn_time x)
        (hgs.primitiveX.continuousOn_time x) fun t ht ↦ ?_⟩
    obtain ⟨C, hC⟩ := (isCompact_uIcc.prod
      (isCompact_univ (X := Icc (0 : ℝ) T))).exists_bound_of_continuousOn
      (s := uIcc 0 x ×ˢ univ) (by simpa only [Function.iterate_zero, id] using
        (hgs.continuous 0).continuousOn)
    have hnhds : Ioo (0 : ℝ) T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    have hcont (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) T) : Continuous (fun y ↦ f y s) :=
      (hs.contDiff s hs').continuous
    have hgcont : Continuous (fun y ↦ g y t) := (hgs.contDiff t (Ioo_subset_Icc_self ht)).continuous
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := x) (x₀ := t) (s := Ioo 0 T)
      (F := fun s y ↦ f y s) (F' := fun s y ↦ g y s) (bound := fun _ ↦ C) hnhds
      (Filter.mem_of_superset hnhds fun s hs' ↦
        (hcont s (Ioo_subset_Icc_self hs')).aestronglyMeasurable)
      ((hcont t (Ioo_subset_Icc_self ht)).intervalIntegrable 0 x)
      hgcont.aestronglyMeasurable
      (Eventually.of_forall fun y hy s hs' ↦ by
        have := hC (y, ⟨s, Ioo_subset_Icc_self hs'⟩) ⟨uIoc_subset_uIcc hy, mem_univ _⟩
        simpa only [Function.iterate_zero, id] using this)
      intervalIntegrable_const
      (Eventually.of_forall fun y _ s hs' ↦
        (hd y s (Ioo_subset_Icc_self hs')).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2))).2

/-- A family with `n` time derivatives is `C^n` on `ℝ × [0, T]`. -/
theorem contDiffOn (hT : 0 < T) : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T n f →
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ f p.1 p.2) (univ ×ˢ Icc 0 T)
  | 0, f, h => by
    apply contDiffOn_zero.mpr
    exact continuousOn_of_continuous_slab (f := fun p : ℝ × ℝ ↦ f p.1 p.2)
      (by simpa only [Function.iterate_zero, id] using (spatial (n := 0) h).continuous 0)
  | n + 1, f, h => by
    have hs := spatial h
    obtain ⟨_, g, hg, hd⟩ := h
    have hx : IsTimeSmooth T n (PDE.Analysis.derivX f) :=
      mono (derivX hT ⟨hs, g, hg, hd⟩)
    have hdx := contDiffOn hT hx
    have hdt := contDiffOn hT hg
    exact_mod_cast contDiffOn_succ_of_space_time_derivatives (f := fun p : ℝ × ℝ ↦ f p.1 p.2)
      (convex_Icc 0 T) (uniqueDiffOn_Icc hT) hdx hdt
      (fun z hz ↦ ((hs.contDiff z.2 hz.2).differentiable (by simp) z.1).hasDerivAt)
      (fun z hz ↦ hd z.1 z.2 hz.2)

end IsTimeSmooth

end PDE.Analysis
