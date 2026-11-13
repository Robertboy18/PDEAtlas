/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
public import PDE.Analysis.Calculus.LocalExtension
import CAS.IntegrationTactic

/-!
# The derivative averaged along a segment

The operator `averagedFDeriv f x₀ x` is the integral of `Df` along the segment
from `x₀` to `x`. For a `C¹` function, applying it to the displacement gives
`f x - f x₀` by the fundamental theorem of calculus. At zero displacement it is
exactly `Df x₀`.

The average loses one derivative, as does `Df` itself. Local smoothness suffices:
extend the flux near the base point, integrate its derivative, and restrict to a
ball whose segments stay in the region where the extension agrees with the flux.
The extension is only a proof device; the result concerns the original function.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Metric Set
open scoped ContDiff Interval Topology

universe u v

variable {X : Type u} {Y : Type (max u v)} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Average of the actual Fréchet derivative along the segment from `x₀` to `x`. -/
def averagedFDeriv (f : X → Y) (x₀ x : X) : X →L[ℝ] Y :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (x₀ + t • (x - x₀))

/-- The zero-length segment has average derivative `Df x₀`. No regularity
assumption is needed for this identity of totalized derivatives. -/
@[simp]
theorem averagedFDeriv_self (f : X → Y) (x₀ : X) :
    averagedFDeriv f x₀ x₀ = fderiv ℝ f x₀ := by
  simp [averagedFDeriv]

/-- Applying the average derivative to the displacement gives the exact increment
of a `C¹` function, including the zero-displacement case. -/
theorem averagedFDeriv_apply_sub
    {f : X → Y} (hf : ContDiff ℝ 1 f) (x₀ x : X) :
    averagedFDeriv f x₀ x (x - x₀) = f x - f x₀ := by
  have hsegment : Continuous (fun t : ℝ ↦ x₀ + t • (x - x₀)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous (fun t : ℝ ↦ fderiv ℝ f (x₀ + t • (x - x₀))) :=
    (hf.continuous_fderiv one_ne_zero).comp hsegment
  rw [averagedFDeriv, ContinuousLinearMap.intervalIntegral_apply
    (hD.intervalIntegrable 0 1)]
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ f (x₀ + s • (x - x₀)))
        (fderiv ℝ f (x₀ + t • (x - x₀)) (x - x₀)) t := by
    have hline : HasDerivAt (fun s : ℝ ↦ x₀ + s • (x - x₀)) (x - x₀) t := by
      simpa only [Pi.add_def, id, one_smul, zero_add] using
        (hasDerivAt_const t x₀).add ((hasDerivAt_id t).smul_const (x - x₀))
    exact ((hf.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t hline
  simpa using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      ((hD.clm_apply continuous_const).intervalIntegrable 0 1)

/-- A globally `C^(n+1)` map has a `C^n` average derivative in its moving endpoint.
The order `n` may be finite or infinite. -/
theorem contDiff_averagedFDeriv
    {n : ℕ∞} {f : X → Y} (hf : ContDiff ℝ ((n : ℕ∞ω) + 1) f) (x₀ : X) :
    ContDiff ℝ n (averagedFDeriv f x₀) := by
  have hD : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hsegment : ContDiff ℝ n (fun z : X × ℝ ↦ x₀ + z.2 • (z.1 - x₀)) :=
    contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  exact contDiff_intervalIntegral (hD.comp hsegment) 0 1

/-- The average derivative is jointly smooth in both endpoints. Moving the base
point and the endpoint together requires no more regularity than moving either one. -/
theorem contDiff_averagedFDeriv_joint
    {n : ℕ∞} {f : X → Y} (hf : ContDiff ℝ ((n : ℕ∞ω) + 1) f) :
    ContDiff ℝ n (fun z : X × X ↦ averagedFDeriv f z.1 z.2) := by
  have hD : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hsegment :
      ContDiff ℝ n (fun z : (X × X) × ℝ ↦ z.1.1 + z.2 • (z.1.2 - z.1.1)) :=
    contDiff_fst.fst.add
      (contDiff_snd.smul (contDiff_fst.snd.sub contDiff_fst.fst))
  exact contDiff_intervalIntegral (hD.comp hsegment) 0 1

/-- At a collapsed segment, differentiating its moving endpoint gives half the
derivative of `Df`. The factor is the integral of the affine segment parameter. -/
theorem hasFDerivAt_averagedFDeriv_self
    {f : X → Y} (hf : ContDiff ℝ 2 f) (x₀ : X) :
    HasFDerivAt (averagedFDeriv f x₀)
      ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x₀) x₀ := by
  let H : X × ℝ → X →L[ℝ] Y := fun z ↦ fderiv ℝ f (x₀ + z.2 • (z.1 - x₀))
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hH : ContDiff ℝ 1 H :=
    hD.comp (contDiff_const.add
      (contDiff_snd.smul (contDiff_fst.sub contDiff_const)))
  have hpartial (t : ℝ) :
      (fderiv ℝ H (x₀, t)).comp (ContinuousLinearMap.inl ℝ X ℝ) =
        t • fderiv ℝ (fderiv ℝ f) x₀ := by
    have hline :
        HasFDerivAt (fun x : X ↦ x₀ + t • (x - x₀))
          (t • ContinuousLinearMap.id ℝ X) x₀ := by
      simpa using (((hasFDerivAt_id x₀).sub_const x₀).const_smul t).const_add x₀
    have hbase : x₀ + t • (x₀ - x₀) = x₀ := by simp
    have hd := ((hD.differentiable one_ne_zero) (x₀ + t • (x₀ - x₀))).hasFDerivAt.comp
      x₀ hline
    have hin := ((hH.differentiable one_ne_zero) (x₀, t)).hasFDerivAt.comp x₀
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x₀ t)
    simpa only [hbase, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
      hin.unique hd
  have hhalf : ∫ t in (0 : ℝ)..1, t = (1 / 2 : ℝ) := by cas
  have havg := hasFDerivAt_intervalIntegral_of_contDiff hH 0 1 x₀
  simp only [hpartial, intervalIntegral.integral_smul_const, hhalf] at havg
  convert havg using 1
  rfl

/-- A differentiable scalar function of the averaged derivative has half the
diagonal derivative of the same scalar function of `Df`. This applies in particular
to a locally smooth eigenvalue branch on the space of operators. -/
theorem hasFDerivAt_comp_averagedFDeriv_self
    {f : X → Y} (hf : ContDiff ℝ 2 f) {a : (X →L[ℝ] Y) → ℝ} {x₀ : X}
    (ha : DifferentiableAt ℝ a (fderiv ℝ f x₀)) :
    HasFDerivAt (fun x ↦ a (averagedFDeriv f x₀ x))
      ((1 / 2 : ℝ) • fderiv ℝ (fun x ↦ a (fderiv ℝ f x)) x₀) x₀ := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hdiag := ha.hasFDerivAt.comp x₀
    ((hD.differentiable one_ne_zero) x₀).hasFDerivAt
  have ha' : DifferentiableAt ℝ a (averagedFDeriv f x₀ x₀) := by simpa using ha
  have hcomp := ha'.hasFDerivAt.comp x₀ (hasFDerivAt_averagedFDeriv_self hf x₀)
  change HasFDerivAt (a ∘ averagedFDeriv f x₀)
    ((1 / 2 : ℝ) • fderiv ℝ (a ∘ fderiv ℝ f) x₀) x₀
  rw [hdiag.fderiv]
  simpa only [averagedFDeriv_self, ContinuousLinearMap.comp_smul] using hcomp

omit [CompleteSpace Y] in
/-- The moving-endpoint average derivative depends only on the germ at its
fixed endpoint. A small convex ball keeps every averaging segment in that germ. -/
theorem averagedFDeriv_eventuallyEq_of_eventuallyEq
    {f g : X → Y} {x₀ : X} (hfg : f =ᶠ[𝓝 x₀] g) :
    averagedFDeriv f x₀ =ᶠ[𝓝 x₀] averagedFDeriv g x₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hfg.fderiv (𝕜 := ℝ))
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using ht
  exact hball ((convex_ball x₀ r).add_smul_sub_mem (mem_ball_self hr) hx ht')

/-- A function of class `C^(n+1)` near `x₀` has a `C^n` averaged derivative on a
smaller open neighborhood, with the exact flux-increment identity there. The order may
be infinite. In particular, local `C²` regularity suffices for a `C¹` average;
no global extension is an assumption. -/
theorem exists_local_contDiff_averagedFDeriv
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {d : ℕ} {n : ℕ∞} {f : ℝ^d → Y} {U : Set (ℝ^d)} {x₀ : ℝ^d}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hf : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f U) :
    ∃ V : Set (ℝ^d), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ n (averagedFDeriv f x₀) V ∧
      ∀ x ∈ V, averagedFDeriv f x₀ x (x - x₀) = f x - f x₀ := by
  have hf' : ContDiffOn ℝ (n + 1 : ℕ∞) f U := by simpa using hf
  obtain ⟨g, hg, _hcompact, heq⟩ :=
    hf'.exists_contDiff_compactSupport_eventuallyEq hU hx₀
  have hnear :
      {x | x ∈ U ∧ f x = g x ∧ averagedFDeriv f x₀ x = averagedFDeriv g x₀ x}
        ∈ 𝓝 x₀ :=
    Filter.inter_mem (hU.mem_nhds hx₀)
      (heq.and (averagedFDeriv_eventuallyEq_of_eventuallyEq heq))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hbase : x₀ ∈ ball x₀ r := mem_ball_self hr
  have havg : EqOn (averagedFDeriv f x₀) (averagedFDeriv g x₀) (ball x₀ r) :=
    fun _ hx ↦ (hball hx).2.2
  have hgavg : ContDiff ℝ n (averagedFDeriv g x₀) :=
    contDiff_averagedFDeriv (by simpa using hg) x₀
  refine ⟨ball x₀ r, isOpen_ball, hbase, fun _ hx ↦ (hball hx).1, ?_, ?_⟩
  · exact hgavg.contDiffOn.congr fun x hx ↦ havg hx
  · intro x hx
    rw [havg hx, averagedFDeriv_apply_sub (hg.of_le (by simp)),
      ← (hball hx).2.1, ← heq.self_of_nhds]

end PDE.Analysis
