/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Reconstruction.HigherOrder
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative
import PDE.FDeriv.Calculus

/-!
# Classical derivatives retain the Schauder exponent

The interior estimate constructs Hölder representatives of the weak gradient.
Weak derivative uniqueness identifies them with the derivatives of a given
C¹ representative. This keeps the Hölder information needed when the equation
is differentiated again.

For the reconstruction step, continuity only on the open domain suffices.
There is no regularity requirement on a representative outside that domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} [Fact (0 < n)]

/-- The classical first derivatives of a C¹ weak solution inherit the
same local Hölder exponent as the coefficients and divergence forcing. -/
theorem exists_holder_partialDeriv_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : ∀ i j, HolderOnWith K γ (A i j) Ω)
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j)
    (hAbound : ∀ x ∈ Ω, ∀ i j, ‖A i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) Ω)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ w : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u w =
        ∑ i, ⟪F i, derivCoordCLM i w⟫_ℝ)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hvu : v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Ω) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R / 32 ∧
      ∀ i : Fin n, ∃ N : ℝ≥0, HolderOnWith N γ (∂[i] v) (ball z r) := by
  obtain ⟨r, hr, hrR, hreg⟩ :=
    exists_holder_gradient_of_holder_coefficients_same_exponent
      hq2 hq hα hΛ hΩ a A hγ0 hγ1 hA hrep hAbound hell
      u F f hf hF hu hR hball
  have hsub : ball z r ⊆ Ω := (ball_subset_ball (by linarith : r ≤ R)).trans hball
  refine ⟨r, hr, hrR, fun i ↦ ?_⟩
  obtain ⟨g, N, hg, hgh, hga⟩ := hreg i
  have hda := wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ u hv hvu.symm i
  have heq : EqOn g (∂[i] v) (ball z r) :=
    Measure.eqOn_open_of_ae_eq (μ := volume)
      (hga.trans (ae_mono (domainMeasure_le hsub) hda)) isOpen_ball hg.continuousOn
      (fun x hx ↦ (contDiffAt_partialDeriv 0
        (hv.contDiffAt (hΩ.mem_nhds (hsub hx))) i).continuousAt.continuousWithinAt)
  refine ⟨N, fun x hx y hy ↦ ?_⟩
  rw [← heq hx, ← heq hy]
  exact hgh x hx y hy

/-- Schauder regularity applies to a representative continuous only on its
domain. Local weak-gradient reconstruction removes the need for an extension. -/
theorem contDiffOn_one_of_holder_coefficients_continuousOn
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : ∀ i j, HolderOnWith K γ (A i j) Ω)
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j)
    (hAbound : ∀ x ∈ Ω, ∀ i j, ‖A i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) Ω)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ w : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u w =
        ∑ i, ⟪F i, derivCoordCLM i w⟫_ℝ)
    {v : ℝ^n → ℝ} (hv : ContinuousOn v Ω)
    (hvu : v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u) :
    ContDiffOn ℝ 1 v Ω := by
  intro x hx
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨r, hr, hrR, hreg⟩ :=
    exists_holder_gradient_of_holder_coefficients_same_exponent
      hq2 hq hα hΛ hΩ a A hγ0 hγ1 hA hrep hAbound hell
      u F f hf hF hu hR hball
  choose g N hg hgh hga using hreg
  have hsub : ball x r ⊆ Ω := (ball_subset_ball (by linarith : r ≤ R)).trans hball
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hi : IntegrableOn (wkpBaseCoordinateCLM u) (ball x r) :=
    ((Lp.memLp (wkpBaseCoordinateCLM u)).mono_measure
      (domainMeasure_le hsub)).integrable (by norm_num)
  let G : ℝ^n → ℝ^n := fun y ↦ WithLp.toLp 2 (fun i ↦ g i y)
  have hG : Continuous G := by fun_prop
  have hw (i : Fin n) : HasWeakDerivativeOn (ball x r) [i]
      (wkpBaseCoordinateCLM u) (fun y ↦ G y i) := by
    have hd : HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM u)
        (wkpCoordinateCLM (singleDerivIndex n i) u) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using u.property.hasWeakDerivativeOn_first (by norm_num) i
    exact (hd.mono isOpen_ball.measurableSet hsub).congr_ae
      Filter.EventuallyEq.rfl (hga i).symm
  obtain ⟨w, hwc, hwd, hwa, _⟩ :=
    exists_contDiffOn_representative_of_weakGradient 0 hi hG
      (contDiffOn_zero.mpr hG.continuousOn) hw hr Subset.rfl
  have hsmall : ball x (r / 4) ⊆ Ω :=
    (ball_subset_ball (by linarith : r / 4 ≤ r)).trans hsub
  have heq : EqOn w v (ball x (r / 4)) :=
    Measure.eqOn_open_of_ae_eq (μ := volume)
      (hwa.trans (ae_mono (domainMeasure_le hsmall) hvu.symm)) isOpen_ball
      hwc.continuousOn (hv.mono hsmall)
  exact ((hwd.congr heq.symm).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < r / 4)))).contDiffWithinAt

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
