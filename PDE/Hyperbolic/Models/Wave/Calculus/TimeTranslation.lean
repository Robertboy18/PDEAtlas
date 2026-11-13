/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Classical traces after an interior time translation

Fixing an interior start in a smooth open band produces all closed first
traces and interior derivatives used in the classical Fourier representation.
The residual is unchanged by translation. Neither endpoint of the
original band requires an extension.
-/

@[expose] public noncomputable section

open Set PDE PDE.Common
open scoped ContDiff

namespace WaveEquation

/-- Freezing an interior start gives the closed-strip classical traces.
Only smoothness inside the original open time band is used. -/
theorem shifted_classical_traces {n : ℕ} {v : ℝ^(n + 1) → ℝ} {s₀ T s b : ℝ}
    (hv : ContDiffOn ℝ ∞ v {p | s₀ < p 0 ∧ p 0 < T}) (hs : s₀ < s) (hb : b + s < T) :
    ContinuousOn (fun z : ℝ × ℝ^n ↦ v (timeSpaceCons (z.1 + s) z.2))
      (Icc 0 b ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × ℝ^n ↦ (∂[0] v) (timeSpaceCons (z.1 + s) z.2))
      (Icc 0 b ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × ℝ^n ↦ (∂[0] (∂[0] v))
      (timeSpaceCons (z.1 + s) z.2)) (Ioo 0 b ×ˢ univ) ∧
    (∀ q ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ v (timeSpaceCons (r + s) x))
      ((∂[0] v) (timeSpaceCons (q + s) x)) q) ∧
    (∀ q ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ (∂[0] v) (timeSpaceCons (r + s) x))
      ((∂[0] (∂[0] v)) (timeSpaceCons (q + s) x)) q) ∧
    (∀ q ∈ Icc 0 b, ContDiff ℝ 2 (fun x ↦ v (timeSpaceCons (q + s) x))) ∧
    ∀ q ∈ Icc 0 b, ∀ x,
      (∂[0] (∂[0] v)) (timeSpaceCons (q + s) x) -
        laplacian (fun y ↦ v (timeSpaceCons (q + s) y)) x =
          waveOperator v (timeSpaceCons (q + s) x) := by
  have hopen : IsOpen {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv₁ : ContDiffOn ℝ ∞ (∂[0] v) {p | s₀ < p 0 ∧ p 0 < T} :=
    hv.partialDeriv 0 hopen (by simp)
  have hv₂ : ContDiffOn ℝ ∞ (∂[0] (∂[0] v)) {p | s₀ < p 0 ∧ p 0 < T} :=
    hv₁.partialDeriv 0 hopen (by simp)
  have hmem (q : ℝ) (hq : q ∈ Icc 0 b) (x : ℝ^n) :
      timeSpaceCons (q + s) x ∈ {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} := by
    change s₀ < q + s ∧ q + s < T
    constructor <;> linarith [hq.1, hq.2]
  have hmap : Continuous (fun z : ℝ × ℝ^n ↦ timeSpaceCons (z.1 + s) z.2) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      ((continuous_fst.add_const s).prodMk continuous_snd)
  have hcont {f : ℝ^(n + 1) → ℝ} (hf : ContinuousOn f {p | s₀ < p 0 ∧ p 0 < T}) :
      ContinuousOn (fun z : ℝ × ℝ^n ↦ f (timeSpaceCons (z.1 + s) z.2)) (Icc 0 b ×ˢ univ) :=
    hf.comp hmap.continuousOn (fun z hz ↦ hmem z.1 hz.1 z.2)
  have hderiv {f : ℝ^(n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f {p | s₀ < p 0 ∧ p 0 < T})
      (q : ℝ) (hq : q ∈ Ioo 0 b) (x : ℝ^n) : HasDerivAt (fun r ↦ f (timeSpaceCons (r + s) x))
        ((∂[0] f) (timeSpaceCons (q + s) x)) q := by
    have hd := (hf.contDiffAt (hopen.mem_nhds
      (hmem q ⟨hq.1.le, hq.2.le⟩ x))).differentiableAt (by simp)
    simpa only [mul_one, Function.comp_def, id_eq] using
      (hasDerivAt_timeSpaceCons f (q + s) x hd).comp q ((hasDerivAt_id q).add_const s)
  refine ⟨hcont hv.continuousOn, hcont hv₁.continuousOn,
    (hcont hv₂.continuousOn).mono (prod_mono_left Ioo_subset_Icc_self),
    hderiv hv, hderiv hv₁, ?_, ?_⟩
  · exact fun q hq ↦ (hv.comp_contDiff (contDiff_timeSpaceCons_spatial n (q + s))
      (hmem q hq)).of_le (by simp)
  · intro q hq x
    have hd := (hv.contDiffAt (hopen.mem_nhds (hmem q hq x))).of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)
    rw [laplacian_timeSlice_of_contDiffAt v (q + s) x hd]
    rfl

end WaveEquation
