/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalAcceleration
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoffUniqueness
public import PDE.DistributionTheory.TestFunction.CompactCutoff
import CAS.ExactTactic

/-!
# Local weak well-posedness for globally Lipschitz first-jet waves

The comparison cylinder may be enlarged to cover any prescribed finite time.
Compact localization and the exterior-forcing estimate give uniqueness for
arbitrary square-integrable local weak energy curves. Together with local-data
patching this gives the local Sobolev statement of Evans, §12.2.1, Theorem 1, including
the H²/H¹/L² bounds of part (ii) for the more regular data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0} {g h : ℝ^n → ℝ}

/-- The local weak equation on a fixed finite time strip. Competitors need
not exist after the specified terminal time. -/
def IsLocalBochnerWeakSolutionOn (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (T : ℝ) (w : ℝ → ℝ^n → ℝ × ℝ) : Prop :=
  ∀ Ω : Set (ℝ^n), IsOpen Ω → Bornology.IsBounded Ω →
    ∃ (x : H¹(Ω) × DerivLp n 2 Ω) (u : ℝ → H¹(Ω) × DerivLp n 2 Ω),
      (baseRepresentative x.1 =ᵐ[domainMeasure n Ω] g) ∧
      ((x.2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] h) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        w t =ᵐ[domainMeasure n Ω] fun y ↦ (baseRepresentative (u t).1 y, (u t).2 y)) ∧
      IsLocalBochnerWeakCurveOn hf hf0 x T u

/-- The initial traces determine an arbitrary local Bochner weak solution on
all bounded spatial sets and all finite forward time intervals. -/
theorem IsLocalBochnerWeakSolutionOn.eq_ae_on_bounded {u v : ℝ → ℝ^n → ℝ × ℝ} {T : ℝ}
    (hu : IsLocalBochnerWeakSolutionOn hf hf0 g h T u)
    (hv : IsLocalBochnerWeakSolutionOn hf hf0 g h T v) {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    (hT : 0 < T) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), u t =ᵐ[domainMeasure n Ω] v t := by
  obtain ⟨c, hc, hgrad⟩ := exists_cutoff_gradient_bound n
  obtain ⟨i, _, hi⟩ := exists_exhaustion_cylinder hΩ T
  let R : ℝ := (i : ℝ) + 2 + (n : ℝ) * c * T
  have hNC : 0 ≤ (n : ℝ) * c * T := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hc) hT.le
  have hR : 0 < R := by dsimp only [R]; positivity
  have hiR : (i : ℝ) + 1 < R := by dsimp only [R]; linarith
  have hspeed : (n : ℝ) * (c / R) * T < 1 := by
    have he : (n : ℝ) * (c / R) * T = ((n : ℝ) * c * T) / R := by cas using hR.ne'
    rw [he]
    apply (div_lt_one hR).mpr
    dsimp only [R]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  let S : Set (ℝ^n) := ball 0 (4 * R)
  have hS : IsOpen S := isOpen_ball
  have hball : ball (0 : ℝ^n) (3 * R) ⊆ S := ball_subset_ball (by linarith)
  have hsub : ball (0 : ℝ^n) R ⊆ S := ball_subset_ball (by linarith)
  obtain ⟨η, hη, hone, _, _⟩ := TestFunction.exists_eq_one_on_compact hS
    (isCompact_closedBall (0 : ℝ^n) (3 * R))
    (closedBall_subset_ball (by linarith : 3 * R < 4 * R))
  obtain ⟨xu, U, hug, huh, huU, hU⟩ := hu S hS isBounded_ball
  obtain ⟨xv, V, hvg, hvh, hvV, hV⟩ := hv S hS isBounded_ball
  have hx : xu = xv := by
    apply Prod.ext
    · exact wkpBaseCoordinateCLM_injective hS (Lp.ext (hug.trans hvg.symm))
    · exact Lp.ext (huh.trans hvh.symm)
  rw [← hx] at hV
  have he := hU.restrict_eq_ae hS hR hball η hη
    (fun y hy ↦ hone y (ball_subset_closedBall hy)) hV hc (hgrad R hR) hspeed
  have hΩR : Ω ⊆ ball (0 : ℝ^n) R := hi.trans (ball_subset_ball hiR.le)
  have hRS := domainMeasure_le hsub
  filter_upwards [he, huU, hvV] with t ht htu htv
  have hq : baseRepresentative (U t).1 =ᵐ[domainMeasure n (ball 0 R)]
      baseRepresentative (V t).1 := by
    have h := congrArg Prod.fst ht
    have huq := restrictCLM_apply_ae isOpen_ball.measurableSet hsub (U t).1 (baseIndex n 1)
    have hvq := restrictCLM_apply_ae isOpen_ball.measurableSet hsub (V t).1 (baseIndex n 1)
    change restrictCLM isOpen_ball.measurableSet hsub (U t).1 =
      restrictCLM isOpen_ball.measurableSet hsub (V t).1 at h
    rw [h] at huq
    exact huq.symm.trans hvq
  have hp : ((U t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 R)] (V t).2 := by
    have h := congrArg Prod.snd ht
    have hup := restrictDerivLp_apply_ae hsub (U t).2
    have hvp := restrictDerivLp_apply_ae hsub (V t).2
    change restrictDerivLp hsub (U t).2 = restrictDerivLp hsub (V t).2 at h
    rw [h] at hup
    exact hup.symm.trans hvp
  have hfield : u t =ᵐ[domainMeasure n (ball 0 R)] v t := by
    filter_upwards [htu.filter_mono (ae_mono hRS), htv.filter_mono (ae_mono hRS), hq, hp]
      with y hyu hyv hyq hyp
    exact hyu.trans ((Prod.ext hyq hyp).trans hyv.symm)
  exact hfield.filter_mono (ae_mono (domainMeasure_le hΩR))

/-- Exact local H¹ × L² data give a unique Bochner weak wave for a globally
Lipschitz full first-jet reaction fixing zero. Uniqueness is on bounded cylinders. -/
theorem exists_unique_localBochnerWeakSolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hg : IsLocallyWkpOn 1 2 univ g) (hh : IsLocallyWkpOn 0 2 univ h) :
    ∃ u : ℝ → ℝ^n → ℝ × ℝ,
      IsLocalBochnerWeakSolution hf hf0 g h u ∧
      ∀ T : ℝ, 0 < T → ∀ v, IsLocalBochnerWeakSolutionOn hf hf0 g h T v →
        ∀ Ω : Set (ℝ^n), Bornology.IsBounded Ω →
          ∀ᵐ t ∂volume.restrict (Ioc 0 T), v t =ᵐ[domainMeasure n Ω] u t := by
  obtain ⟨u, hu⟩ := exists_localBochnerWeakSolution hf hf0 hg hh
  refine ⟨u, hu, fun T hT v hv Ω hb ↦ ?_⟩
  exact hv.eq_ae_on_bounded (fun Ω hΩ hb ↦ hu Ω hΩ hb T hT) hb hT

/-- The unique local weak wave retains H²/H¹/L² regularity when the data have local H²/H¹
regularity. -/
theorem exists_unique_localBochnerWeakSolution_h2 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hg : IsLocallyWkpOn 2 2 univ g) (hh : IsLocallyWkpOn 1 2 univ h) :
    ∃ u : ℝ → ℝ^n → ℝ × ℝ,
      IsLocalBochnerWeakSolution hf hf0 g h u ∧ HasLocalH2Regularity hf hf0 u ∧
      ∀ T : ℝ, 0 < T → ∀ v, IsLocalBochnerWeakSolutionOn hf hf0 g h T v →
        ∀ Ω : Set (ℝ^n), Bornology.IsBounded Ω →
          ∀ᵐ t ∂volume.restrict (Ioc 0 T), v t =ᵐ[domainMeasure n Ω] u t := by
  obtain ⟨u, hu, hreg⟩ := exists_localBochnerWeakSolution_h2 hf hf0 hg hh
  refine ⟨u, hu, hreg, fun T hT v hv Ω hb ↦ ?_⟩
  exact hv.eq_ae_on_bounded (fun Ω hΩ hb ↦ hu Ω hΩ hb T hT) hb hT

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
