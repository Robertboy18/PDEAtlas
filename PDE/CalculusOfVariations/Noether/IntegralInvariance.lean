/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.DomainInvariance
public import PDE.Analysis.Calculus.Jacobian.Determinant

/-!
# From action invariance to density invariance

Change of variables turns invariance on open sets into equality of integrals of
continuous densities. Localization gives pointwise equality. At parameter zero the
spatial Jacobian is the identity, so continuity removes the absolute value of its
determinant near zero. The hypothesis is the invariance (6) of Evans, §8.6.1, tested
only on bounded open sets, and the conclusion is the finite density premise of the
Noether identity in `divergence_noetherCurrent_of_domain_invariance`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1, equation (6).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

private theorem eq_of_integral_eq_on_bounded_open {n : ℕ} {f g : ℝ^n → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ V : Set (ℝ^n), IsOpen V → Bornology.IsBounded V →
      (∫ y in V, f y) = ∫ y in V, g y) (x : ℝ^n) : f x = g x := by
  suffices hle : ∀ (f g : ℝ^n → ℝ), Continuous f → Continuous g →
      (∀ V : Set (ℝ^n), IsOpen V → Bornology.IsBounded V →
        (∫ y in V, f y) = ∫ y in V, g y) → f x ≤ g x from
    le_antisymm (hle f g hf hg h) (hle g f hg hf (fun V ho hb ↦ (h V ho hb).symm))
  intro f g hf hg heq
  by_contra! hlt
  let V := Metric.ball x 1 ∩ {y | g y < f y}
  have ho : IsOpen V := Metric.isOpen_ball.inter (isOpen_lt hg hf)
  have hb : Bornology.IsBounded V := Metric.isBounded_ball.subset inter_subset_left
  have hx : x ∈ V := ⟨Metric.mem_ball_self zero_lt_one, hlt⟩
  have hi : IntegrableOn (fun y ↦ f y - g y) V :=
    ((hf.sub hg).continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hpos : 0 < ∫ y in V, f y - g y := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).2
    · have hs : Function.support (fun y ↦ f y - g y) ∩ V = V :=
        inter_eq_right.mpr (fun y hy ↦ ne_of_gt (sub_pos.mpr hy.2))
      rw [hs]
      exact ho.measure_pos volume ⟨x, hx⟩
    · filter_upwards [ae_restrict_mem ho.measurableSet] with y hy
      exact (sub_pos.mpr hy.2).le
  have hfi := hf.continuousOn.integrableOn_compact (μ := volume) hb.isCompact_closure
  have hgi := hg.continuousOn.integrableOn_compact (μ := volume) hb.isCompact_closure
  rw [integral_sub (hfi.mono_set subset_closure) (hgi.mono_set subset_closure),
    heq V ho hb, sub_self] at hpos
  exact lt_irrefl _ hpos

variable {n m : ℕ}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n}

/-- Invariance of the action on bounded open sets implies the finite density law.
The sign of the Jacobian is derived near the identity, and no infinitesimal
invariance equation is assumed. Injectivity suffices for change of variables. -/
theorem fieldDensity_eventually_eq_of_integral_invariance
    (hL : ContDiff ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2))
    (hU : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y,
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, y))
    (hΦ : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y,
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (t, y))
    (hΦ₀ : Φ 0 = id)
    (hinj : ∀ᶠ t in 𝓝 0, Function.Injective (Φ t))
    (hinvariant : ∀ᶠ t in 𝓝 0, ∀ V : Set (ℝ^n), IsOpen V → Bornology.IsBounded V →
      (∫ y in V, fieldDensity L (U t) y) = ∫ y in Φ t '' V, fieldDensity L (U 0) y)
    (x : ℝ^n) :
    (fun t ↦ fieldDensity L (U t) x) =ᶠ[𝓝 0]
      (fun t ↦ transformedDensity L (fun _ ↦ U 0) Φ t x) := by
  have hdensity (t : ℝ)
      (ht : ∀ y, ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, y)) :
      Continuous (fieldDensity L (U t)) := by
    exact continuous_iff_continuousAt.mpr fun y ↦
      (contDiffAt_fieldDensity hL.contDiffAt
        ((ht y).comp y (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
  have hdet : ContinuousAt (fun t ↦ (jacobianMatrix (Φ t) x).det) 0 :=
    (hasDerivAt_spatial_volume (hΦ.self_of_nhds x)
      (Eventually.of_forall (congrFun hΦ₀))).continuousAt
  have hpos : ∀ᶠ t in 𝓝 0, 0 < (jacobianMatrix (Φ t) x).det := by
    apply hdet.eventually (lt_mem_nhds ?_)
    change 0 < (jacobianMatrix (Φ 0) x).det
    rw [hΦ₀]
    change 0 < (jacobianMatrix (fun y : ℝ^n ↦ y) x).det
    rw [jacobianMatrix_id, Matrix.det_one]
    exact zero_lt_one
  filter_upwards [hinj, hinvariant, hpos, hU, hΦ] with t ht hi hp hUt hΦt
  have hΦslice : ContDiff ℝ 2 (Φ t) :=
    contDiff_iff_contDiffAt.mpr fun y ↦
      (hΦt y).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hchange (V : Set (ℝ^n)) (ho : IsOpen V) (hb : Bornology.IsBounded V) :
      (∫ y in V, fieldDensity L (U t) y) =
        ∫ y in V, |(jacobianMatrix (Φ t) y).det| * fieldDensity L (U 0) (Φ t y) := by
    rw [hi V ho hb, integral_image_eq_integral_abs_det_fderiv_smul volume ho.measurableSet
      (fun y _ ↦ (hΦslice.differentiable (by norm_num) y).hasFDerivAt.hasFDerivWithinAt)
      ht.injOn]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [det_jacobianMatrix (hΦslice.differentiable (by norm_num) y)]
    rfl
  have hc : Continuous (fun y ↦
      |(jacobianMatrix (Φ t) y).det| * fieldDensity L (U 0) (Φ t y)) :=
    ((contDiff_jacobianMatrix hΦslice).continuous.matrix_det.abs).mul
      ((hdensity 0 hU.self_of_nhds).comp hΦslice.continuous)
  have heq := eq_of_integral_eq_on_bounded_open (hdensity t hUt) hc hchange x
  simpa only [abs_of_pos hp, transformedDensity, mul_comm] using heq

end PDE.CalculusOfVariations.Noether
