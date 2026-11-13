/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.SpaceTime
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of cut-off time derivatives

Let `χ` be continuous with compact support on `ℝⁿ` and let `ν` be finite on
compact sets. A function continuous on the compact cylinder `[a, b] × tsupport χ`,
multiplied by `χ`, is integrable on `(a, b] × ℝⁿ`. If `F(x, t)` is `C¹` near every
point of `tsupport χ × [a, b]`, its time derivative is continuous there, so every
`G` that agrees with `∂ₜF` on that set gives an integrable product `χ G`. An
evolution equation `∂ₜF = G` can therefore be tested against `χ` with no
integrability assumption on `G` itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {n : ℕ} {ν : Measure (ℝ^n)} [IsFiniteMeasureOnCompacts ν]

/-- If `F` is continuous on `[a, b] × tsupport χ`, then `χ(x) F(t, x)` is
integrable on `(a, b] × ℝⁿ`. -/
theorem integrable_spatial_cutoff_of_continuousOn
    (χ : ℝ^n → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (F : ℝ × ℝ^n → ℝ) {a b : ℝ}
    (hF : ContinuousOn F (Icc a b ×ˢ tsupport χ)) :
    Integrable (fun q : ℝ × ℝ^n ↦ χ q.2 * F q)
      ((volume.restrict (Ioc a b)).prod ν) := by
  let τ : Measure ℝ := volume.restrict (Ioc a b)
  have hlocal : IntegrableOn (fun q : ℝ × ℝ^n ↦ χ q.2 * F q)
      (Icc a b ×ˢ tsupport χ) (τ.prod ν) :=
    ((hχ.comp continuous_snd).continuousOn.mul hF).integrableOn_compact
      (isCompact_Icc.prod hc)
  have hfst : QuasiMeasurePreserving
      (Prod.fst : ℝ × ℝ^n → ℝ) (τ.prod ν) τ :=
    Measure.quasiMeasurePreserving_fst
  have ht : ∀ᵐ q : ℝ × ℝ^n ∂τ.prod ν, q.1 ∈ Ioc a b :=
    hfst.ae (ae_restrict_mem measurableSet_Ioc)
  apply hlocal.integrable_of_ae_notMem_eq_zero
  filter_upwards [ht] with q hq
  intro hnot
  have hx : q.2 ∉ tsupport χ := fun hx ↦ hnot ⟨⟨hq.1.le, hq.2⟩, hx⟩
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- If `F` is `C¹` at every point of `tsupport χ × [a, b]` and `G(s, x)` is the
time derivative of `F(x, ·)` at `s` there, then `χ(x) G(s, x)` is integrable on
`(a, b] × ℝⁿ`. Nothing is assumed about `G` off `[a, b] × tsupport χ`. -/
theorem integrable_cutoff_time_work_of_contDiffAt
    (χ : ℝ^n → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (F : ℝ^n × ℝ → ℝ) (G : ℝ × ℝ^n → ℝ) {a b : ℝ}
    (hF : ∀ x ∈ tsupport χ, ∀ s ∈ Icc a b, ContDiffAt ℝ 1 F (x, s))
    (hG : ∀ x ∈ tsupport χ, ∀ s ∈ Icc a b,
      HasDerivAt (fun t ↦ F (x, t)) (G (s, x)) s) :
    Integrable (fun q : ℝ × ℝ^n ↦ χ q.2 * G q)
      ((volume.restrict (Ioc a b)).prod ν) := by
  let D (q : ℝ × ℝ^n) : ℝ := fderiv ℝ F (q.2, q.1) (0, 1)
  have hD : ContinuousOn D (Icc a b ×ˢ tsupport χ) := by
    intro q hq
    have hd : ContinuousAt (fun p : ℝ^n × ℝ ↦ fderiv ℝ F p (0, 1))
        (q.2, q.1) :=
      (((hF q.2 hq.2 q.1 hq.1).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt
    have hswap : ContinuousAt (fun p : ℝ × ℝ^n ↦ (p.2, p.1)) q :=
      continuousAt_snd.prodMk continuousAt_fst
    exact (hd.comp (f := fun p : ℝ × ℝ^n ↦ (p.2, p.1)) hswap).continuousWithinAt
  have hint := integrable_spatial_cutoff_of_continuousOn (ν := ν) χ hχ hc D hD
  have hfst : QuasiMeasurePreserving
      (Prod.fst : ℝ × ℝ^n → ℝ) ((volume.restrict (Ioc a b)).prod ν)
      (volume.restrict (Ioc a b)) :=
    Measure.quasiMeasurePreserving_fst
  have ht : ∀ᵐ q : ℝ × ℝ^n ∂(volume.restrict (Ioc a b)).prod ν,
      q.1 ∈ Ioc a b := hfst.ae (ae_restrict_mem measurableSet_Ioc)
  apply hint.congr
  filter_upwards [ht] with q hq
  by_cases hx : q.2 ∈ tsupport χ
  · have hs : q.1 ∈ Icc a b := ⟨hq.1.le, hq.2⟩
    have hd : G q = D q :=
      (hG q.2 hx q.1 hs).deriv.symm.trans
        (deriv_prod_timeSlice F q.2 q.1 ((hF q.2 hx q.1 hs).differentiableAt_one))
    rw [hd]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end PDE.Analysis.Evolution
