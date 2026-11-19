/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.ConservativePair
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder

/-!
# Weak partials of a conservative primitive

The product-coordinate integral identities are transported through the
measure-preserving plane coordinates. Tests are pulled back by
the continuous linear equivalence, so their derivatives transform
by the chain rule. The resulting derivatives use the Sobolev
weak-derivative predicate.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Distributions NNReal

namespace SobolevSpace

private theorem hasWeakDerivativeOn_of_planePair
    {f g : ℝ × ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (i : Fin 2)
    (hweak : ∀ φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ),
      (∫ p, f p * (TestFunction.lineDerivCLM (k := ⊤) ℝ
        (PDE.Analysis.planeEquiv (EuclideanSpace.single i 1)) φ) p) =
        -(∫ p, g p * φ p)) :
    HasWeakDerivativeOn univ [i]
      (fun p : ℝ^2 ↦ f (p 0, p 1)) (fun p : ℝ^2 ↦ g (p 0, p 1)) := by
  let e : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hmp : MeasurePreserving e volume volume :=
    PDE.Analysis.measurePreserving_planeEquiv
  have hlocal {v : ℝ × ℝ → ℝ} (hv : LocallyIntegrable v volume) :
      LocallyIntegrable (v ∘ e) volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact (hmp.integrableOn_image e.toHomeomorph.measurableEmbedding).mp
      (hv.integrableOn_isCompact (hK.image e.continuous))
  refine ⟨(hlocal hf).locallyIntegrableOn univ, (hlocal hg).locallyIntegrableOn univ, ?_⟩
  intro φ _hφ
  let ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) :=
    TestFunction.precompProper e.symm e.symm.contDiff e.symm.toHomeomorph.isProperMap φ
  have hderiv (x : ℝ^2) :
      (TestFunction.lineDerivCLM (k := ⊤) ℝ
        (PDE.Analysis.planeEquiv (EuclideanSpace.single i 1)) ψ) (e x) =
        iteratedPartialDeriv [i] (φ : ℝ^2 → ℝ) x := by
    rw [TestFunction.lineDerivCLM_apply_eq_fderiv]
    change fderiv ℝ ((φ : ℝ^2 → ℝ) ∘ e.symm) (e x)
      (e (EuclideanSpace.single i 1)) = _
    rw [fderiv_comp _ (φ.contDiff.differentiable (by simp)).differentiableAt
      e.symm.differentiableAt, e.symm.fderiv, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
    rfl
  have heq := hweak ψ
  have hleft := hmp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun p ↦ f p * (TestFunction.lineDerivCLM (k := ⊤) ℝ
      (PDE.Analysis.planeEquiv (EuclideanSpace.single i 1)) ψ) p)
  have hright := hmp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun p ↦ g p * ψ p)
  rw [← hleft, ← hright] at heq
  have hψ (x : ℝ^2) : ψ (e x) = φ x := by
    change φ (e.symm (e x)) = φ x
    rw [e.symm_apply_apply]
  have hcoords (x : ℝ^2) : e x = (x 0, x 1) := rfl
  simp only [hderiv, hψ] at heq
  simp only [hcoords] at heq
  simpa only [domainMeasure, Measure.restrict_univ, List.length_singleton,
    pow_one, neg_mul, one_mul, TestFunction.toFun_eq_coe] using heq

/-- The weak time partial of the conservative primitive. -/
theorem hasWeakDerivativeOn_conservativePrimitive_time
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {q : ℝ × ℝ → ℝ} (hq : StronglyMeasurable q)
    (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B) :
    HasWeakDerivativeOn univ [0]
      (fun p : ℝ^2 ↦ PDE.Analysis.conservativePrimitive g q (p 0, p 1))
      (fun p : ℝ^2 ↦ -({p : ℝ × ℝ | 0 < p.1}.indicator q) (p 0, p 1)) := by
  have hq' : LocallyIntegrable q volume :=
    locallyIntegrable_of_aestronglyMeasurable_norm_le_const hq.aestronglyMeasurable
      B.coe_nonneg (Filter.Eventually.of_forall hB)
  apply hasWeakDerivativeOn_of_planePair
    (PDE.Analysis.locallyIntegrable_conservativePrimitive hg hq B hB)
    (hq'.indicator (measurableSet_lt measurable_const measurable_fst)).neg 0
  intro φ
  change (∫ p, PDE.Analysis.conservativePrimitive g q p *
      (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) φ) p) =
    -(∫ p, -({p : ℝ × ℝ | 0 < p.1}.indicator q) p * φ p)
  simpa only [neg_mul, integral_neg, neg_neg] using
    PDE.Analysis.integral_conservativePrimitive_mul_timeDeriv hg hq B hB φ

/-- Initial weak conservation gives the spatial weak partial,
with the constant extension of the initial primitive at negative time. -/
theorem hasWeakDerivativeOn_conservativePrimitive_space
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {r q : ℝ × ℝ → ℝ} (hr : LocallyIntegrable r volume)
    (hrzero : ∀ p : ℝ × ℝ, p.1 ≤ 0 → r p = 0)
    (hq : StronglyMeasurable q) (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ),
      (∫ p, r p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p) +
        (∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator q) p *
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) ψ) p) +
        (∫ x, g x * ψ (0, x)) = 0) :
    HasWeakDerivativeOn univ [1]
      (fun p : ℝ^2 ↦ PDE.Analysis.conservativePrimitive g q (p 0, p 1))
      (fun p : ℝ^2 ↦ r (p 0, p 1) +
        ({p : ℝ × ℝ | p.1 ≤ 0}.indicator (fun p ↦ g p.2)) (p 0, p 1)) := by
  have hg' : LocallyIntegrable (fun p : ℝ × ℝ ↦ g p.2) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact hg.comp_snd
  apply hasWeakDerivativeOn_of_planePair
    (PDE.Analysis.locallyIntegrable_conservativePrimitive hg hq B hB)
    (hr.add (hg'.indicator (measurableSet_le measurable_fst measurable_const))) 1
  intro φ
  simpa using
    PDE.Analysis.integral_conservativePrimitive_mul_spaceDeriv hg hr hrzero hq B hB hweak φ

end SobolevSpace
