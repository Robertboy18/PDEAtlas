/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Nonautonomous.EllipticFamily
public import PDE.Parabolic.Regularity.SpatialH2.WeakResidual

/-!
# Bochner `H²` regularity for a time-dependent elliptic residual

The continuous family of elliptic inverses acts on the `L²` load `f - uₜ`.
Its compact-time operator bound proves that the resulting spatial representatives
belong to `L²_t H²_x`. Weak elliptic uniqueness identifies their entire first-order
Sobolev restriction with the original energy-space solution.
-/

@[expose] public noncomputable section

open scoped Sobolev
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Parabolic.DivergenceFormHeat

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A time-dependent elliptic residual gives a Bochner `H²` lift, with a constant
depending only on the domain, coefficient family and time interval.

In particular the hypotheses do not supply a measurable selection of spatial
solutions or assume a uniform elliptic estimate; both are constructed. -/
theorem exists_nonautonomous_spatial_h2_lp_of_ae_weak_residual_identity
    [Fact (0 < n)] (hΩ : C2BoundaryAtlas n Ω)
    {t₀ t₁ : ℝ} (htime : t₀ ≤ t₁)
    (A : ℝ → Fin n → Fin n → W^{1,∞}(Ω))
    (hA : ContinuousOn A (Icc t₀ t₁))
    (a : ℝ → ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ t ∈ Icc t₀ t₁, ∀ i j,
      ⇑((A t i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a t x i j)
    (haC1 : ∀ t ∈ Icc t₀ t₁, ∀ i j, ContDiff ℝ 1 (fun x ↦ a t x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω,
      MatrixEllipticLowerBound (a t x) alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
        (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ∀ v : H¹₀(Ω),
          ⟪ut t, baseCoordCLM v⟫_ℝ +
            variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t)))
              (u t) v = ⟪f t, baseCoordCLM v⟫_ℝ) →
        ∃ U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁)),
          ((fun t ↦ lowerOrderCLM (k := 1) (m := 2) (by omega) (U t))
            =ᵐ[volume.restrict (Ioc t₀ t₁)] fun t ↦ h10SubtypeL (u t)) ∧
          ‖U‖ ≤ C * ‖f - ut‖ := by
  obtain ⟨S, C, hC, hS, hbound, hsolve⟩ :=
    exists_continuous_spatial_h2_solution_family hΩ htime A hA a haRep haC1
      alpha halpha hElliptic
  refine ⟨C, hC, ?_⟩
  intro f ut u hresidual
  let μ := volume.restrict (Ioc t₀ t₁)
  let r := f - ut
  let lift := fun t ↦ S t (r t)
  have hSmeas : AEStronglyMeasurable S μ := by
    let : TopologicalSpace.PseudoMetrizableSpace (DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω)) :=
      PseudoEMetricSpace.pseudoMetrizableSpace (α := DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω))
    let : SecondCountableTopologyEither ℝ (DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω)) :=
      ⟨Or.inl inferInstance⟩
    exact (hS.aestronglyMeasurable (μ := volume) measurableSet_Icc).mono_set Ioc_subset_Icc_self
  have hliftMeas : AEStronglyMeasurable lift μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      hSmeas (Lp.aestronglyMeasurable r)
  have hliftBound : ∀ᵐ t ∂μ, ‖lift t‖ ≤ C * ‖r t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((S t).le_opNorm (r t)).trans
      (mul_le_mul_of_nonneg_right (hbound t (Ioc_subset_Icc_self ht)) (norm_nonneg _))
  have hlift : MemLp lift 2 μ := (Lp.memLp r).of_le_mul hliftMeas hliftBound
  refine ⟨hlift.toLp lift, ?_, ?_⟩
  · filter_upwards [hlift.coeFn_toLp, hresidual, Lp.coeFn_sub f ut,
      ae_restrict_mem measurableSet_Ioc] with t hl ht hr htime
    rw [hl]
    apply hsolve t (Ioc_subset_Icc_self htime)
    change IsWeakDivergenceSolution (coefficientBase (A t)) ((f - ut) t) (u t)
    rw [hr]
    exact is_weak_divergence_solution_of_weak_residual_identity
      hΩ.toC1ExtensionAtlas.isOpen (A t) (f t) (ut t) (u t) ht
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hlift.coeFn_toLp, hliftBound] with t ht hb
    simpa only [ht] using hb

end PDE.Parabolic.DivergenceFormHeat
