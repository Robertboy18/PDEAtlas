/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.LinearizedEquation
public import PDE.Hyperbolic.Models.Wave.Strichartz.ConeSobolev
import PDE.Hyperbolic.Models.Wave.Strichartz.ConeSobolev.CompactForcing
import PDE.Hyperbolic.Models.Wave.Calculus.TimeTranslation
import PDE.FDeriv.PartialDeriv.Regularity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The differentiated quintic cone estimate

On each proper prefix of an open forward band, the derivative satisfies the linearized equation with
forcing `-5u⁴` times that derivative. Smoothness and forward support construct the forcing classes.
The cone may have an enlarged tip.

This is the L⁶ part of the estimate (4) of Evans, §12.4, Theorem 1, on a backward cone, for the
derivatives of the solution, as used in steps 2 and 4 of the proof of Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4); Theorem 3, steps 2 and 4 of
  its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter Set Metric PDE PDE.Common
open scoped ENNReal SchwartzMap

open PDE.Analysis
open scoped ContDiff

namespace WaveEquation.Critical

/-- The differentiated PDE has its cone L6 estimate on every proper
prefix, with restart data fixed before the prefix. -/
theorem lpNorm_partialDeriv_cone_le_of_forward_support {u : ℝ^4 → ℝ} {T R s r A : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupp : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^ 5 = 0)
    (hs : s ∈ Ioo 0 T) (hr : r ∈ Ico s T) (hA : T ≤ A) (c : ℝ^3) (i : Fin 4) (g h : 𝓢(ℝ^3, ℝ))
    (hpos : ∀ x, (∂[i] u) (timeSpaceCons s x) = g x)
    (hvel : ∀ x, (∂[0] (∂[i] u)) (timeSpaceCons s x) = h x) :
    lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
        (volume.restrict (ball c (A - r))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ) * 3 *
        (‖(Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).fst‖ +
        ‖(Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).snd‖ +
        5 * ∫ q in Icc s r,
          lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2
            (volume.restrict (ball c (A - q)))) := by
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContDiffOn ℝ ∞ (∂[i] u) {p | 0 < p 0 ∧ p 0 < T} :=
    hu.partialDeriv i hopen (by simp)
  obtain ⟨hcont, hcont₁, hcont₂, hd, hd₁, hspatial, hop⟩ :=
    shifted_classical_traces hv hs.1 (b := r - s) (by linarith [hr.2])
  have htime (q : ℝ) (hq : q ∈ Icc 0 (r - s)) : q + s ∈ Ioo 0 T := by
    constructor <;> linarith [hq.1, hq.2, hs.1, hr.2]
  have hucont : ContinuousOn (fun z : ℝ × ℝ^3 ↦ u (timeSpaceCons (z.1 + s) z.2))
      (Icc 0 (r - s) ×ˢ univ) :=
    (shifted_classical_traces hu hs.1 (b := r - s) (by linarith [hr.2])).1
  let F : ℝ × ℝ^3 → ℝ := fun z ↦
    -(5 * u (timeSpaceCons (z.1 + s) z.2) ^ 4 * (∂[i] u) (timeSpaceCons (z.1 + s) z.2))
  have hF : ContinuousOn F (Icc 0 (r - s) ×ˢ univ) :=
    ((continuousOn_const.mul (hucont.pow 4)).mul hcont).neg
  have hzero : ∀ q ∈ Icc 0 (r - s), ∀ x : ℝ^3,
      x ∉ closedBall 0 (R + T) → F (q, x) = 0 := by
    intro q hq x hx
    have hx' : R + T < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    have hz := hsupp (q + s) (htime q hq) x (by linarith [(htime q hq).2])
    simp only [F, hz, zero_pow (by norm_num : 4 ≠ 0), mul_zero, zero_mul, neg_zero]
  have hw : ∀ p : ℝ^4, 0 < p 0 → p 0 < T → waveOperator u p + u p ^ 5 = 0 := by
    intro p hp hpt
    simpa only [timeSpaceCons_spatialPart] using hwave (p 0) ⟨hp, hpt⟩ (spatialPart p)
  have hres : ∀ q ∈ Icc 0 (r - s), ∀ x, (∂[0] (∂[0] (∂[i] u))) (timeSpaceCons (q + s) x) -
        laplacian (fun y ↦ (∂[i] u) (timeSpaceCons (q + s) y)) x = F (q, x) := by
    intro q hq x
    rw [hop q hq x]
    exact waveOperator_partialDeriv_quintic_on_band (hu.of_le (by simp)) hw i
      (by simpa only [timeSpaceCons_zero, mem_Ioo] using htime q hq)
  have he := Strichartz.lpNorm_classicalWave_cone_six_le_of_compact_forcing
    (b := r - s) (T := A - s) (by linarith [hr.2]) c g h
    (u := fun q x ↦ (∂[i] u) (timeSpaceCons (q + s) x))
    (U := fun q x ↦ (∂[0] (∂[i] u)) (timeSpaceCons (q + s) x))
    (U₂ := fun q x ↦ (∂[0] (∂[0] (∂[i] u))) (timeSpaceCons (q + s) x))
    (isCompact_closedBall (0 : ℝ^3) (R + T)) hF hzero
    hcont hcont₁ hcont₂ hd hd₁ (fun q hq ↦ hspatial q ⟨hq.1.le, hq.2.le⟩)
    (by simpa only [zero_add] using hpos) (by simpa only [zero_add] using hvel)
    hres (r - s) ⟨sub_nonneg.mpr hr.1, le_rfl⟩
  have hnorm (q : ℝ) : lpNorm (fun x ↦ F (q, x)) 2 (volume.restrict (ball c ((A - s) - q))) =
      5 * lpNorm (fun x ↦ u (timeSpaceCons (q + s) x) ^ 4 * (∂[i] u) (timeSpaceCons (q + s) x)) 2
          (volume.restrict (ball c (A - (q + s)))) := by
    simp only [F, lpNorm_fun_neg, mul_assoc, sub_sub, add_comm s]
    exact lpNorm_fun_natCast_mul 5 _ _ _
  have hpre : (fun q : ℝ ↦ q + s) ⁻¹' Icc s r = Icc 0 (r - s) := by
    ext q
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hm : MeasurePreserving (fun q : ℝ ↦ q + s)
      (volume.restrict (Icc 0 (r - s))) (volume.restrict (Icc s r)) := by
    simpa only [hpre] using (measurePreserving_add_right (volume : Measure ℝ) s).restrict_preimage
        (s := Icc s r) measurableSet_Icc
  have hI := hm.integral_comp (MeasurableEquiv.addRight s).measurableEmbedding
    (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (ball c (A - q))))
  simp_rw [hnorm] at he
  rw [integral_const_mul, hI] at he
  simpa only [sub_add_cancel, sub_sub_sub_cancel_right] using he

end WaveEquation.Critical
