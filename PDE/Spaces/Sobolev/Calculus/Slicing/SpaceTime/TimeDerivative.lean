/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.Spatial
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner
import PDE.Analysis.MeasureTheory.Lp.RealL2.Testing
import PDE.Analysis.MeasureTheory.Lp.SectionReconstruction

/-!
# Weak time derivatives of spacetime Sobolev slices

The raw time weak derivative, tested against time-space tensors, determines
the Bochner weak derivative of the reconstructed L² curve. Spatial scalar
tests distinguish the Bochner integrals, so no exceptional set indexed by
all spatial tests is needed. Together with spatial graph recovery this gives
the L²(H¹) and H¹(L²) regularity of raw H¹ spacetime data.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Slices

open MeasureTheory Set TopologicalSpace PDE.Common GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Distributions Sobolev

variable {n : ℕ} {I : Set ℝ}

/-- The raw spacetime time derivative is the Bochner weak derivative
of any integrable L² slice representatives. -/
theorem hasWeakTimeDerivativeOn_of_timeSlices
    {f g : ℝ^(n + 1) → ℝ}
    (hweak : HasWeakDerivativeOn {p | p 0 ∈ I} [0] f g)
    {u v : ℝ → DerivLp n 2 univ}
    (hu : IntegrableOn u I) (hv : IntegrableOn v I)
    (huf : ∀ᵐ t ∂volume.restrict I,
      (u t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ f (timeSpaceCons t x))
    (hvg : ∀ᵐ t ∂volume.restrict I,
      (v t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ g (timeSpaceCons t x)) :
    HasWeakTimeDerivativeOn I u v := by
  apply HasWeakTimeDerivativeOn.of_integral_smul_eq
    hu.locallyIntegrableOn hv.locallyIntegrableOn
  intro ψ hψ hc hs
  have hdψ := (contDiff_infty_iff_deriv.mp hψ).2
  have hupsi : IntegrableOn (fun t ↦ deriv ψ t • u t) I :=
    hu.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hdψ.continuous hc.deriv
  have hvpsi : IntegrableOn (fun t ↦ ψ t • v t) I :=
    hv.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
  apply Lp.eq_of_integral_contDiff_mul_eq
  intro φ hφ hφc
  have hφlp : MemLp φ 2 (domainMeasure n univ) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hpair {w : ℝ → DerivLp n 2 univ} {r : ℝ^(n + 1) → ℝ}
      (hr : ∀ᵐ t ∂volume.restrict I,
        (w t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ r (timeSpaceCons t x))
      (χ : ℝ → ℝ) (hint : IntegrableOn (fun t ↦ χ t • w t) I) :
      (∫ x, (∫ t in I, χ t • w t) x * φ x ∂domainMeasure n univ) =
        ∫ t in I, χ t * ∫ x, r (timeSpaceCons t x) * φ x := by
    rw [Lp.integral_mul_integral hint hφlp]
    apply integral_congr_ae
    filter_upwards [hr] with t ht
    simp only [domainMeasure, Measure.restrict_univ]
    rw [← integral_const_mul]
    apply integral_congr_ae
    have hs := Lp.coeFn_smul (χ t) (w t)
    simp only [domainMeasure, Measure.restrict_univ] at hs
    filter_upwards [hs, ht] with x hx hrx
    simp only [hx, Pi.smul_apply, smul_eq_mul, hrx, mul_assoc]
  have hneg (w : DerivLp n 2 univ) :
      (∫ x, (-w) x * φ x ∂domainMeasure n univ) =
        -(∫ x, w x * φ x ∂domainMeasure n univ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg w] with x hx
    simp only [hx, Pi.neg_apply, neg_mul]
  rw [hpair huf _ hupsi, hneg, hpair hvg _ hvpsi]
  let ψT : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨ψ, hψ, hc, subset_univ _⟩
  let φT : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := ⟨φ, hφ, hφc, subset_univ _⟩
  simpa only [TestFunction.toFun_eq_coe, ψT, φT, TestFunction.coe_mk] using
    hweak.integral_timeSpaceTensor_time ψT hs φT

/-- Raw square-integrable spatial and time weak derivatives give
L²(H¹) slices with an L²(L²) Bochner weak time derivative. -/
theorem exists_hOne_timeSlices_with_timeDerivative
    (hI : IsOpen I) [IsFiniteMeasure (volume.restrict I)]
    {f : ℝ^(n + 1) → ℝ} {g : Fin (n + 1) → ℝ^(n + 1) → ℝ}
    (hf : MemLp f 2 (volume.restrict {p | p 0 ∈ I}))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict {p | p 0 ∈ I}))
    (hweak : ∀ i, HasWeakDerivativeOn {p | p 0 ∈ I} [i] f (g i)) :
    ∃ F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict I),
      ∃ G : Lp (DerivLp n 2 univ) 2 (volume.restrict I),
        HasWeakTimeDerivativeOn I (fun t ↦ wkpBaseCoordinateCLM (F t)) G ∧
        (∀ᵐ t ∂volume.restrict I,
          (wkpBaseCoordinateCLM (F t) : ℝ^n → ℝ) =ᵐ[volume]
            fun x ↦ f (timeSpaceCons t x)) ∧
        (∀ i, ∀ᵐ t ∂volume.restrict I,
          (wkpCoordinateCLM (singleDerivIndex n i) (F t) : ℝ^n → ℝ) =ᵐ[volume]
            fun x ↦ g i.succ (timeSpaceCons t x)) ∧
        (∀ᵐ t ∂volume.restrict I,
          (G t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ g 0 (timeSpaceCons t x)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨F, hF, hFD⟩ := exists_hOne_timeSlices hI hf
    (fun i ↦ hg i.succ) (fun i ↦ hweak i.succ)
  have hgt : MemLp (fun p : ℝ × ℝ^n ↦ g 0 (timeSpaceCons p.1 p.2))
      2 ((volume.restrict I).prod (domainMeasure n univ)) := by
    simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
      domainMeasure, Measure.restrict_univ] using
        (hg 0).comp_measurePreserving (measurePreserving_timeSpaceCons_restrict I)
  obtain ⟨G, hG, _hGnorm⟩ := hgt.exists_L2_sections
  have hGrep : ∀ᵐ t ∂volume.restrict I,
      (G t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ g 0 (timeSpaceCons t x) := by
    filter_upwards [hG] with t ht
    simpa only [domainMeasure, Measure.restrict_univ] using ht.symm
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  refine ⟨F, G, ?_, hF, hFD, hGrep⟩
  exact hasWeakTimeDerivativeOn_of_timeSlices (hweak 0)
    (P.integrable_comp ((Lp.memLp F).integrable (by norm_num)))
    ((Lp.memLp G).integrable (by norm_num)) hF hGrep

/-- A member of the raw spacetime H¹ graph has Bochner spatial H¹
slices and the time-coordinate weak derivative. This extracts all
hypotheses from the graph rather than requiring slice certificates. -/
theorem exists_timeSlices_of_wkpSpaceOn
    (hI : IsOpen I) [IsFiniteMeasure (volume.restrict I)]
    (u : W^{1,2}(({p | p 0 ∈ I} : Set (ℝ^(n + 1))))) :
    ∃ F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict I),
      ∃ G : Lp (DerivLp n 2 univ) 2 (volume.restrict I),
        HasWeakTimeDerivativeOn I (fun t ↦ wkpBaseCoordinateCLM (F t)) G ∧
        (∀ᵐ t ∂volume.restrict I,
          (wkpBaseCoordinateCLM (F t) : ℝ^n → ℝ) =ᵐ[volume]
            fun x ↦ wkpBaseCoordinateCLM u (timeSpaceCons t x)) ∧
        (∀ i, ∀ᵐ t ∂volume.restrict I,
          (wkpCoordinateCLM (singleDerivIndex n i) (F t) : ℝ^n → ℝ) =ᵐ[volume]
            fun x ↦ wkpCoordinateCLM (singleDerivIndex (n + 1) i.succ) u
              (timeSpaceCons t x)) ∧
        (∀ᵐ t ∂volume.restrict I,
          (G t : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
            wkpCoordinateCLM (singleDerivIndex (n + 1) 0) u (timeSpaceCons t x)) := by
  apply exists_hOne_timeSlices_with_timeDerivative hI (Lp.memLp _)
    (fun i ↦ Lp.memLp (wkpCoordinateCLM (singleDerivIndex (n + 1) i) u))
  intro i
  simpa only [wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply,
    singleDerivIndex_toList] using u.property (singleDerivIndex (n + 1) i)

end SobolevSpace.Slices
