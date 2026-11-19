/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitRay.Transversality
import CAS.ExactTactic

/-!
# Uniform compression and expansion of local wave curves

The shock speed has half the derivative of the characteristic speed along
the shock curve at zero strength. Both speed differences consequently have
positive strength derivative. Joint `C¹` regularity turns these infinitesimal
facts into compression on one common interval for all nearby left states.
The same argument gives expansion along the rarefaction curve.

Applied to the shock curves and characteristic speeds of Evans, §11.2,
`exists_uniform_shock_compression` puts the negative branch of the shock curve of every left
state `q` near `q₀` in `S_k^-(q)`, where the Lax entropy condition (42) of §11.2.3 holds; its
half-speed hypothesis is the derivative form of §11.2.3, Theorem 2(iii). Applied to the
rarefaction curves, `exists_uniform_speed_expansion` makes `λ_k` strictly increasing along
them, so that their positive branches lie in `R_k^+(q)` of §11.2.1, as the `k`-rarefaction
waves of §11.2.2, Theorem 1, require.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, the notation `R_k^±(z₀)`; §11.2.2, Theorem 1;
  §11.2.3, Theorem 2(iii), equation (42) and the definition of `S_k^-(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Strictly ordered base speeds give the remaining Lax inequalities near
zero strength. Finiteness supplies one common neighborhood for all families. -/
theorem eventually_lax_separation {m : ℕ} {E : Type*} [TopologicalSpace E] {q₀ : E}
    {eig : Fin m → E → ℝ} {S : Fin m → ℝ × E → E} {speed : Fin m → ℝ × E → ℝ}
    (heig : ∀ k, ContinuousAt (eig k) q₀) (hS : ∀ k, ContinuousAt (S k) (0, q₀))
    (hspeed : ∀ k, ContinuousAt (speed k) (0, q₀))
    (hzero : ∀ k, S k (0, q₀) = q₀ ∧ speed k (0, q₀) = eig k q₀)
    (horder : StrictMono (fun k ↦ eig k q₀)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k, (∀ j, j < k → eig j p.2 < speed k p) ∧
      (∀ j, k < j → speed k p < eig j (S k p)) := by
  refine eventually_all.mpr fun k ↦ ?_
  refine (eventually_all.mpr fun j ↦ ?_).and (eventually_all.mpr fun j ↦ ?_)
  · by_cases hj : j < k
    · have hnear := ((heig j).comp (continuousAt_snd :
        ContinuousAt (Prod.snd : ℝ × E → E) (0, q₀))).eventually_lt
        (hspeed k) (by simpa only [Function.comp_def, (hzero k).2] using horder hj)
      exact hnear.mono fun _ hp _ ↦ hp
    · exact Filter.Eventually.of_forall fun _ h ↦ (hj h).elim
  · by_cases hj : k < j
    · have heig' : ContinuousAt (eig j) (S k (0, q₀)) := by
        simpa only [(hzero k).1] using heig j
      have hnear := (hspeed k).eventually_lt (heig'.comp (hS k))
        (by simpa only [Function.comp_def, (hzero k).1, (hzero k).2] using horder hj)
      exact hnear.mono fun _ hp _ ↦ hp
    · exact Filter.Eventually.of_forall fun _ h ↦ (hj h).elim

/-- A joint curve with positively oriented characteristic speed has uniformly
increasing speed for every nearby initial state. -/
theorem exists_uniform_speed_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q₀ v : E} {eig : E → ℝ} {R : ℝ × E → E} (heig : ContDiffAt ℝ 1 eig q₀)
    (hR : ContDiffAt ℝ 1 R (0, q₀)) (hR₀ : R (0, q₀) = q₀)
    (htan : HasDerivAt (fun s ↦ R (s, q₀)) v 0) (hpos : 0 < fderiv ℝ eig q₀ v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ, StrictMonoOn (fun s ↦ eig (R (s, q))) (Ioo (-δ) δ) := by
  have heig' : ContDiffAt ℝ 1 eig (R (0, q₀)) := hR₀.symm ▸ heig
  apply PDE.Analysis.Calculus.exists_uniform_strictMonoOn_of_hasDerivAt
    (heig'.comp (0, q₀) hR) _ hpos
  have hd : HasFDerivAt eig (fderiv ℝ eig q₀) (R (0, q₀)) :=
    hR₀.symm ▸ heig.differentiableAt_one.hasFDerivAt
  simpa only [Function.comp_def] using hd.comp_hasDerivAt (0 : ℝ) htan

/-- The half-factor in the shock-speed derivative forces strict compression for
negative strength, uniformly over nearby left states. The two inequalities are
derived from the derivatives, rather than assumed for the curve. -/
theorem exists_uniform_shock_compression {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q₀ v : E} {eig : E → ℝ} {S : ℝ × E → E} {speed : ℝ × E → ℝ} (heig : ContDiffAt ℝ 1 eig q₀)
    (hS : ContDiffAt ℝ 1 S (0, q₀)) (hspeed : ContDiffAt ℝ 1 speed (0, q₀))
    (hzero : ∀ᶠ q in 𝓝 q₀, S (0, q) = q ∧ speed (0, q) = eig q)
    (htan : HasDerivAt (fun s ↦ S (s, q₀)) v 0)
    (hhalf : HasDerivAt (fun s ↦ speed (s, q₀)) ((1 / 2 : ℝ) * fderiv ℝ eig q₀ v) 0)
    (hpos : 0 < fderiv ℝ eig q₀ v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ, ∀ s ∈ Ioo (-δ) 0,
      eig (S (s, q)) < speed (s, q) ∧ speed (s, q) < eig q := by
  have hS₀ := hzero.self_of_nhds |>.1
  let a : ℝ := (1 / 2 : ℝ) * fderiv ℝ eig q₀ v
  have ha : 0 < a := mul_pos (by norm_num) hpos
  have hleft : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ speed p - eig p.2) (0, q₀) :=
    hspeed.sub (heig.comp (0, q₀) contDiffAt_snd)
  have hdleft : HasDerivAt (fun s ↦ speed (s, q₀) - eig q₀) a 0 := hhalf.sub_const (eig q₀)
  obtain ⟨δ₁, hδ₁, hmono₁⟩ :=
    PDE.Analysis.Calculus.exists_uniform_strictMonoOn_of_hasDerivAt hleft hdleft ha
  have heig' : ContDiffAt ℝ 1 eig (S (0, q₀)) := hS₀.symm ▸ heig
  have hright : ContDiffAt ℝ 1 (fun p ↦ eig (S p) - speed p) (0, q₀) :=
    (heig'.comp (0, q₀) hS).sub hspeed
  have hd : HasFDerivAt eig (fderiv ℝ eig q₀) (S (0, q₀)) :=
    hS₀.symm ▸ heig.differentiableAt_one.hasFDerivAt
  have hdright : HasDerivAt (fun s ↦ eig (S (s, q₀)) - speed (s, q₀)) a 0 := by
    convert (hd.comp_hasDerivAt (0 : ℝ) htan).sub hhalf using 1
    · rfl
    · dsimp [a]
      cas
  obtain ⟨δ₂, hδ₂, hmono₂⟩ :=
    PDE.Analysis.Calculus.exists_uniform_strictMonoOn_of_hasDerivAt hright hdright ha
  obtain ⟨δ₀, hδ₀, hzero₀⟩ := Metric.mem_nhds_iff.mp hzero
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hle₀ : δ ≤ δ₀ := min_le_left _ _
  have hle₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, fun q hq s hs ↦ ?_⟩
  obtain ⟨hSq, hspeedq⟩ := hzero₀ (ball_subset_ball hle₀ hq)
  have hs₁ : s ∈ Ioo (-δ₁) δ₁ := ⟨lt_of_le_of_lt (neg_le_neg hle₁) hs.1, hs.2.trans hδ₁⟩
  have hs₂ : s ∈ Ioo (-δ₂) δ₂ := ⟨lt_of_le_of_lt (neg_le_neg hle₂) hs.1, hs.2.trans hδ₂⟩
  have hlt₁ := hmono₁ q (ball_subset_ball hle₁ hq) hs₁ ⟨neg_lt_zero.mpr hδ₁, hδ₁⟩ hs.2
  have hlt₂ := hmono₂ q (ball_subset_ball hle₂ hq) hs₂ ⟨neg_lt_zero.mpr hδ₂, hδ₂⟩ hs.2
  simp only [hSq, hspeedq, sub_self, sub_lt_zero] at hlt₁ hlt₂
  exact ⟨hlt₂, hlt₁⟩

end PDE.Hyperbolic.ConservationLaw.System
