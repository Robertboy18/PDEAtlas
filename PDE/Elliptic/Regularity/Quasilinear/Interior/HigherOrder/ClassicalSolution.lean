/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.ClassicalGradient
import PDE.Elliptic.Regularity.Interior.Schauder.Reconstruction.HigherOrder
import PDE.Analysis.MeasureTheory.LocalRepresentative

/-!
# Classical representatives of nonlinear H¹ solutions

De Giorgi and Schauder give a C¹ representative of the weak gradient.
Local reconstruction then supplies a C² representative of the original
H¹ solution. Continuous representatives agree on open overlaps, so the local
representatives glue on the whole domain.

This proves the first classical stage of the nonlinear interior bootstrap
in Evans, §8.3.2, for homogeneous autonomous gradient densities in dimension
greater than two. The density is C³ with bounded uniformly positive Hessian.
Neither continuity nor higher integrability of the solution is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ} [Fact (0 < n)] {Ω V : Set ℝ^n}

/-- A raw H¹ homogeneous Euler–Lagrange solution has a local C²
representative. Both its continuous gradient and its continuous base
representative are derived from the equation. -/
theorem exists_contDiffOn_two_representative_ball_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ V) :
    ∃ v : ℝ^n → ℝ, Continuous v ∧ ContDiffOn ℝ 2 v (ball z (R / 256)) ∧
      v =ᵐ[volume.restrict (ball z (R / 256))] wkpBaseCoordinateCLM u := by
  obtain ⟨G, hG, hGc, hGa⟩ := exists_contDiffOn_one_weakGradient_of_gradientDensity
    hq2 hq hΩ hb hV hVc hVΩ hL hbound hθ hpos u hu hR hball
  let T := ball z (R / 64)
  have hTΩ : T ⊆ Ω := (ball_subset_ball (by linarith : R / 64 ≤ R)).trans
    (hball.trans (subset_closure.trans hVΩ))
  have : IsFiniteMeasure (volume.restrict T) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hf : IntegrableOn (wkpBaseCoordinateCLM u) T :=
    ((Lp.memLp (wkpBaseCoordinateCLM u)).mono_measure
      (domainMeasure_le hTΩ)).integrable (by norm_num)
  have hweak (i : Fin n) :
      HasWeakDerivativeOn T [i] (wkpBaseCoordinateCLM u) (fun x ↦ G x i) := by
    have hw : HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM u)
        (wkpCoordinateCLM (singleDerivIndex n i) u) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using u.property.hasWeakDerivativeOn_first (by norm_num) i
    refine (hw.mono isOpen_ball.measurableSet hTΩ).congr_ae Filter.EventuallyEq.rfl ?_
    filter_upwards [hGa,
      (wkpGradientCLM_apply_ae u).filter_mono (ae_mono (domainMeasure_le hTΩ))]
      with x hGx hux
    exact (hux i).symm.trans (congrArg (fun p : ℝ^n ↦ p i) hGx.symm)
  obtain ⟨v, hv, hvc, hva, _hderiv⟩ := exists_contDiffOn_representative_of_weakGradient
    1 hf hG hGc hweak (by positivity : 0 < R / 64) Subset.rfl
  have hrad : R / 64 / 4 = R / 256 := by ring
  refine ⟨v, hv, ?_, by simpa only [hrad] using hva⟩
  simpa only [hrad, Nat.cast_one, one_add_one_eq_two] using hvc

/-- The local nonlinear De Giorgi–Schauder representatives glue to a C²
representative on the entire open domain. The input solution is only H¹. -/
theorem exists_contDiffOn_two_representative_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 2 v Ω ∧
      v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u := by
  obtain ⟨v, hv, hva⟩ := MeasureTheory.exists_contDiffAt_ae_eq_of_locally
    (𝕜 := ℝ) (μ := volume) (Ω := Ω) (f := wkpBaseCoordinateCLM u) (k := 2) (by
      intro x hx
      obtain ⟨V, hV, hxV, hVΩ, hVc⟩ :=
        exists_open_between_and_isCompact_closure isCompact_singleton hΩ
          (by simpa using hx : {x} ⊆ Ω)
      obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hV x (hxV (mem_singleton x))
      obtain ⟨v, _hv, hvc, hva⟩ :=
        exists_contDiffOn_two_representative_ball_of_gradientDensity
          hq2 hq hΩ hb hV hVc hVΩ hL hbound hθ hpos u hu hR hball
      refine ⟨ball x (R / 256), isOpen_ball, mem_ball_self (by positivity), ?_, v, hvc, hva⟩
      exact (ball_subset_ball (by linarith : R / 256 ≤ R)).trans
        (hball.trans (subset_closure.trans hVΩ)))
  exact ⟨v, fun x hx ↦ (hv x hx).contDiffWithinAt, hva⟩

end PDE.Elliptic.Regularity.Quasilinear
