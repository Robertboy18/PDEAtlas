/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.HolderRange
public import Mathlib.Topology.MetricSpace.Holder
import PDE.Elliptic.Regularity.Interior.DeGiorgi.LocalL2Bound
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.MeanSquare
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Quadratic

/-!
# De Giorgi Hölder regularity from the H¹ weak equation

The local L² estimate first bounds the essential range. The oscillation contraction then gives power
decay at every centre and radius. The Campanato representative theorem converts this decay into a
Hölder representative of the original Sobolev class.

The coefficients are merely measurable and essentially bounded, with a uniform positive ellipticity
constant. Neither boundedness nor continuity of the solution is a hypothesis. This is the interior
De Giorgi-Nash theorem for homogeneous scalar equations in divergence form, in every positive
dimension (`exists_holder_representative_of_homogeneous_weak_equation`). Evans states it for the
equation (17) of §8.3.2 without proof and refers to Gilbarg-Trudinger, Chapter 8.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3.2, the De Giorgi-Nash theorem for the linear equation
  (17), stated without proof, p. 487.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity).
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

open PDE.Elliptic.Regularity.Campanato

variable {n : ℕ}

private theorem meanSquare_le_of_essential_range
    {v : ℝ^n → ℝ} {x : ℝ^n} {r : ℝ} (hr : 0 < r)
    (hv : MemLp v 2 (volume.restrict (ball x r))) {c M : ℝ}
    (hbound : ∀ᵐ y ∂volume.restrict (ball x r), |v y - c| ≤ M) :
    (⨍ y in ball x r, ‖v y - ⨍ w in ball x r, v w‖ ^ 2) ≤ M ^ 2 := by
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply (setAverage_norm_sub_average_sq_le hv c).trans
  calc
    _ ≤ ⨍ _y in ball x r, M ^ 2 := by
      simp only [setAverage_eq, smul_eq_mul]
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr measureReal_nonneg)
      apply integral_mono_ae (hv.sub (memLp_const c)).norm.integrable_sq
        (integrable_const _)
      filter_upwards [hbound] with y hy
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    _ = _ := setAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne _

variable [Fact (0 < n)]

/-- An H¹-to-Hölder interior regularity theorem for the homogeneous
scalar divergence equation with measurable uniformly elliptic coefficients.
The exponent is uniform over the coefficient and solution classes. -/
theorem exists_holder_representative_of_homogeneous_weak_equation
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧
      ∀ (W : Set (ℝ^n)), IsOpen W → Bornology.IsBounded W →
      ∀ (A : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ W →
        ∃ (g : ℝ^n → ℝ) (K : ℝ≥0), Continuous g ∧
          HolderOnWith K γ g (ball z (R / 64)) ∧
          g =ᵐ[volume.restrict (ball z (R / 64))] wkpBaseCoordinateCLM u := by
  obtain ⟨γ, C, hγ, hγ1, hC, hdecay⟩ :=
    exists_holder_essential_range_decay hq2 hq hα hΛ
  refine ⟨γ, hγ, hγ1, fun W hW hWb A hAΛ hA u hu z R hR hball ↦ ?_⟩
  let : NeZero n := ⟨(Fact.out : 0 < n).ne'⟩
  obtain ⟨D, hD, hlocal⟩ := exists_local_norm_le_sqrt_integral_sq hW hWb
    hq2 hq hα hΛ (by linarith : 0 < R / 2) (by linarith : R / 2 < R)
  let M := D * Real.sqrt (∫ y in ball z R, wkpBaseCoordinateCLM u y ^ 2) + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hbound : ∀ᵐ y ∂volume.restrict (ball z (R / 2)),
      |wkpBaseCoordinateCLM u y| ≤ M :=
    (hlocal A hAΛ hA u hu z hball).mono fun _ hy ↦ hy.trans (by dsimp only [M]; linarith)
  let v : ℝ^n → ℝ := W.indicator (wkpBaseCoordinateCLM u)
  have hv : MemLp v 2 volume :=
    (memLp_indicator_iff_restrict hW.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hrep {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ W) :
      v =ᵐ[volume.restrict (ball x s)] wkpBaseCoordinateCLM u :=
    (ae_restrict_mem isOpen_ball.measurableSet).mono
      (fun y hy ↦ indicator_of_mem (hxs hy) _)
  let ρ := R / 8
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let N : ℝ≥0 := ⟨C * M / ρ ^ (γ : ℝ), by positivity⟩
  have hcamp (x : ℝ^n) (hx : x ∈ ball z ρ) (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      (⨍ y in closedBall x s, ‖v y - ⨍ w in closedBall x s, v w‖ ^ 2) ≤
        (N * s ^ (γ : ℝ)) ^ 2 := by
    have hxhalf : ball x ρ ⊆ ball z (R / 2) := ball_subset_ball' (by
      have hx' := mem_ball.mp hx
      dsimp only [ρ] at *
      linarith)
    have hxW : ball x ρ ⊆ W :=
      hxhalf.trans ((ball_subset_ball (by linarith)).trans hball)
    have hxbound : ∀ᵐ y ∂volume.restrict (ball x ρ),
        |wkpBaseCoordinateCLM u y - 0| ≤ M := by
      simpa only [sub_zero] using hbound.filter_mono (ae_mono (domainMeasure_le hxhalf))
    obtain ⟨d, hd⟩ := hdecay W A hAΛ hA u hu x ρ hρ hxW 0 M hM hxbound s hs hsρ
    have hvbound : ∀ᵐ y ∂volume.restrict (ball x s),
        |v y - d| ≤ C * (s / ρ) ^ (γ : ℝ) * M := by
      filter_upwards [hd, hrep ((ball_subset_ball hsρ).trans hxW)] with y hy heq
      rwa [heq]
    have hmean := meanSquare_le_of_essential_range hs
      (hv.mono_measure Measure.restrict_le_self) hvbound
    have hballs : closedBall x s =ᵐ[volume] ball x s :=
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume x s).le
        isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simp_rw [setAverage_congr hballs]
    apply hmean.trans_eq
    congr 1
    rw [Real.div_rpow hs.le hρ.le]
    change C * (s ^ (γ : ℝ) / ρ ^ (γ : ℝ)) * M =
      (C * M / ρ ^ (γ : ℝ)) * s ^ (γ : ℝ)
    ring
  obtain ⟨K, _, hholder⟩ := exists_holderOnWith_representative_of_meanSquare (n := n) hγ
  obtain ⟨g, hg, hgh, hga⟩ := hholder v N
    (fun _ _ ↦ hv.mono_measure Measure.restrict_le_self) z ρ hρ hcamp
  rw [show ρ / 8 = R / 64 by dsimp only [ρ]; ring] at hgh hga
  exact ⟨g, K * N, hg, hgh, hga.trans (hrep ((ball_subset_ball (by linarith)).trans hball))⟩

end SobolevSpace.GraphSpace
