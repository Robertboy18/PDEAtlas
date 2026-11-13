/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakSource
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ContinuousRepresentative

/-!
# The Bochner source of the normalized trajectory

The endpoint rate is a continuous functional of the L² vorticity curve:
take its Hilbert transform, its normalized primitive, and evaluate at the
normalizing endpoint. The measurable H² graph therefore constructs the
nonlinear second-derivative source in Bochner L² on each interior time slab.
Its spatial formula is identified with the velocity derivatives of the solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped ENNReal Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The canonical graph row is the weak second derivative of every
continuous representative of its base. -/
theorem hasWeakTimeDerivativeOn_realSecondDerivativeCLM
    (W : W^{2,2}(ℝ^1)) {w : ℝ → ℝ} (hw : Continuous w)
    (hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] w) :
    HasWeakTimeDerivativeOn univ (deriv w) (realSecondDerivativeCLM W) := by
  have heq : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) = w :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) hw).mp
      ((realLineRepresentative_lowerOrder_ae W).symm.trans hrep)
  have hq : realLineRepresentative (∂[0] W) = deriv w := by
    rw [← heq]
    exact (deriv_realLineRepresentative_lowerOrder W).symm
  exact hq ▸ hasWeakTimeDerivativeOn_realLineRepresentative (∂[0] W)

/-- The canonical L² source is the source of the differentiated De Gregorio
equation. The third velocity derivative is its spectral L² representative. -/
theorem secondDerivativeSource_ae_of_representative
    (W : W^{2,2}(ℝ^1)) (ρ : ℝ) {w u : ℝ → ℝ} (hw : Continuous w)
    (hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] w)
    (hu : ContDiff ℝ 1 u) (hpair : IsHilbertPair w (deriv u)) :
    (secondDerivativeSource ρ W : ℝ → ℝ) =ᵐ[volume] fun x ↦
      -(ρ + deriv u x) * realSecondDerivativeCLM W x +
        realHilbertTransformL2 (realSecondDerivativeCLM W) x * w x +
          deriv (deriv u) x * deriv w x := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let Q := partialDerivCLM 0 W
  have heq : realLineRepresentative U = w :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) hw).mp
      ((realLineRepresentative_lowerOrder_ae W).symm.trans hrep)
  have hq : realLineRepresentative Q = deriv w := by
    rw [← heq]
    exact (deriv_realLineRepresentative_lowerOrder W).symm
  have hwbase : (realLineCoordinateCLM (baseIndex 1 1) U : ℝ → ℝ) =ᵐ[volume] w :=
    (realLineCoordinate_ae_representative U).trans (.of_forall fun x ↦ congrFun heq x)
  have hqbase : (realLineCoordinateCLM (baseIndex 1 1) Q : ℝ → ℝ) =ᵐ[volume] deriv w :=
    (realLineCoordinate_ae_representative Q).trans (.of_forall fun x ↦ congrFun hq x)
  obtain ⟨r, _, hqLp, hwq, hqr⟩ := exists_weak_secondDerivative_of_h2 W hw hrep
  obtain ⟨_, hpair₁, _⟩ := IsHilbertPair.exists_weak_velocity_jet
    hpair hu hqLp (Lp.memLp r) hwq hqr
  have hH := PDE.Analysis.IsHilbertPair.ae_eq_right
    (PDE.Analysis.IsHilbertPair.congr_ae (isHilbertPair_realHilbertH1 U)
      hwbase EventuallyEq.rfl) hpair
  have hD := PDE.Analysis.IsHilbertPair.ae_eq_right
    (PDE.Analysis.IsHilbertPair.congr_ae (isHilbertPair_realHilbertTransformL2
      (realLineCoordinateCLM (baseIndex 1 1) Q)) hqbase EventuallyEq.rfl) hpair₁
  filter_upwards [secondDerivativeSource_ae ρ W, hH, hD] with x hx hHx hDx
  change _ = -(ρ + realLineRepresentative (realHilbertH1 U) x) *
    realSecondDerivativeCLM W x +
      realLineRepresentative U x * realHilbertTransformL2 (realSecondDerivativeCLM W) x +
        realLineRepresentative Q x *
          realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q) x at hx
  rw [hx, hHx, hDx, heq, hq, mul_comm (w x), mul_comm (deriv w x)]

end DeGregorio.Iteration

namespace DeGregorio

variable {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
  (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
  (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
  {F : ℝ → DerivLp 1 2 univ}
  (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
  (hrep : ∀ t ∈ Ioo a T,
    (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
      (fun x ↦ fields.vorticity x t))
  (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
  (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)

include hsol hR hK hbound hrep hzero hnormalized in
/-- Endpoint normalization determines a continuous rate from the PDE
and the supported H² bound. -/
theorem IsClassicalRescaledSolutionOn.continuousOn_rate_of_supported_h2 :
    ContinuousOn ρ (Ioo a T) := by
  obtain ⟨C, hC⟩ :=
    hsol.exists_lipschitzOnWith_base_of_supported_h2 hR hK hbound hrep hzero hnormalized
  have hc := ((continuous_l2Primitive_apply R).comp
    (realHilbertTransformL2.continuous.comp
      oneDimensionalPushforwardL2.continuous)).comp_continuousOn hC.continuousOn
  apply (hc.neg.div_const R).congr
  intro t ht
  have hw : Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  have hreg := (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 hw (hrep t ht)).1
  have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
    hK.of_isClosed_subset (isClosed_tsupport _)
      (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed (hbound t ht) hw
        (hrep t ht))
  rw [hnormalized t ht,
    congrFun (hsol.velocity_eq_hilbertPVVelocity ht hreg hs (hzero t ht)) R,
    Iteration.hilbertPVVelocity_eq_l2Primitive_of_ae hreg hs (hrep t ht)]
  rfl

include hsol hR hK hbound hrep hzero hnormalized in
/-- The normalized trajectory has a measurable H² graph and a Bochner L² nonlinear
source on every closed interior slab. The forcing integrability needed for the
transport energy identity follows from the local graph bound. -/
theorem IsClassicalRescaledSolutionOn.exists_bochner_secondDerivative_source :
    ∃ W : ℝ → W^{2,2}(ℝ^1),
      (∀ t ∈ Ioo a T, ‖W t‖ ≤ B ∧ wkpBaseCoordinateCLM (W t) = F t) ∧
      (∀ c d : ℝ, Icc c d ⊆ Ioo a T →
        MemLp (fun t ↦ Iteration.secondDerivativeSource (ρ t) (W t)) 2
          (volume.restrict (Ioc c d))) ∧
      ∀ t ∈ Ioo a T,
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t))
          (Iteration.realSecondDerivativeCLM (W t)) ∧
        (Iteration.secondDerivativeSource (ρ t) (W t) : ℝ → ℝ) =ᵐ[volume] fun x ↦
          -(ρ t + deriv (fun y ↦ fields.velocity y t) x) *
              Iteration.realSecondDerivativeCLM (W t) x +
            realHilbertTransformL2 (Iteration.realSecondDerivativeCLM (W t)) x *
              fields.vorticity x t +
            deriv (deriv (fun y ↦ fields.velocity y t)) x *
              deriv (fun y ↦ fields.vorticity y t) x := by
  classical
  have hex (t : Ioo a T) : ∃ W : W^{2,2}(ℝ^1),
      ‖W‖ ≤ B ∧ wkpBaseCoordinateCLM W = F t := (hbound t t.property).1
  choose W₀ hW₀ using hex
  let W : ℝ → W^{2,2}(ℝ^1) := fun t ↦ if ht : t ∈ Ioo a T then W₀ ⟨t, ht⟩ else 0
  have hW (t : ℝ) (ht : t ∈ Ioo a T) :
      ‖W t‖ ≤ B ∧ wkpBaseCoordinateCLM (W t) = F t := by
    simpa only [W, dite_eq_left ht] using hW₀ ⟨t, ht⟩
  obtain ⟨C, hC⟩ :=
    hsol.exists_lipschitzOnWith_base_of_supported_h2 hR hK hbound hrep hzero hnormalized
  have hρ := hsol.continuousOn_rate_of_supported_h2 hR hK hbound hrep hzero hnormalized
  refine ⟨W, hW, ?_, ?_⟩
  · intro c d hcd
    refine Iteration.memLp_secondDerivativeSource_of_base (B := B) (D := 2 * B)
      ((hρ.mono (Ioc_subset_Icc_self.trans hcd)).aestronglyMeasurable measurableSet_Ioc)
      ?_ B.coe_nonneg (mul_nonneg (by norm_num) B.coe_nonneg) ?_
    · apply ((hC.continuousOn.mono (Ioc_subset_Icc_self.trans hcd)).aestronglyMeasurable
        measurableSet_Ioc).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hW t (hcd (Ioc_subset_Icc_self ht))).2.symm
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hi := hcd (Ioc_subset_Icc_self ht)
      exact ⟨(hW t hi).1, (hsol.norm_velocity_and_rate_le_of_h2 hi hR hK
        (hbound t hi) (hrep t hi) (hzero t hi) (hnormalized t hi)).1⟩
  · intro t ht
    have hw : Continuous (fun x ↦ fields.vorticity x t) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
    have hrepW : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (W t)) : ℝ → ℝ)
        =ᵐ[volume] fun x ↦ fields.vorticity x t := (hW t ht).2 ▸ hrep t ht
    have hreg := (contDiff_and_bounds_of_h2_representative (W t) hw hrepW).1
    have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      hK.of_isClosed_subset (isClosed_tsupport _)
        (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed (hbound t ht) hw
          (hrep t ht))
    have hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t) := by
      rw [hsol.velocity_eq_hilbertPVVelocity ht hreg hs (hzero t ht)]
      obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hreg one_ne_zero
      exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hD hs
    exact ⟨Iteration.hasWeakTimeDerivativeOn_realSecondDerivativeCLM (W t) hw hrepW,
      Iteration.secondDerivativeSource_ae_of_representative (W t) (ρ t) hw hrepW hu
        (hsol.biotSavart ht)⟩

include hsol hR hK hbound hrep hzero hnormalized in
/-- The weak second derivative satisfies the nonconservative Bochner transport
formulation on every interior slab. Both the state and source are constructed, and
their time integrability follows from the supported H² bound. -/
theorem IsClassicalRescaledSolutionOn.exists_bochner_secondDerivative_transport :
    ∃ r G : ℝ → Lp ℝ 2 (volume : Measure ℝ),
      (∀ t ∈ Ioo a T, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      (∀ ℓ : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ,
        ContinuousOn (fun t ↦ ℓ (r t)) (Ioo a T)) ∧
      (∀ c d : ℝ, Icc c d ⊆ Ioo a T →
        MemLp r 2 (volume.restrict (Ioc c d)) ∧
        MemLp G 2 (volume.restrict (Ioc c d))) ∧
      (∀ t ∈ Ioo a T, (G t : ℝ → ℝ) =ᵐ[volume] fun x ↦
        -(ρ t + deriv (fun y ↦ fields.velocity y t) x) * r t x +
          realHilbertTransformL2 (r t) x * fields.vorticity x t +
            deriv (deriv (fun y ↦ fields.velocity y t)) x *
              deriv (fun y ↦ fields.vorticity y t) x) ∧
      ∀ t ∈ Ioo a T, ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        HasDerivAt (fun τ ↦ ∫ x, r τ x * ψ x)
          ((∫ x, (ρ t * x + fields.velocity x t) * r t x * deriv ψ x) +
            ∫ x, ((ρ t + deriv (fun y ↦ fields.velocity y t) x) * r t x +
              G t x) * ψ x) t := by
  obtain ⟨r, hr, hc, hmem, he⟩ :=
    hsol.exists_bochner_secondDerivative_evolution hR hK hbound hrep hzero hnormalized
  obtain ⟨W, _, hGmem, hGrep⟩ :=
    hsol.exists_bochner_secondDerivative_source hR hK hbound hrep hzero hnormalized
  let G := fun t ↦ Iteration.secondDerivativeSource (ρ t) (W t)
  have heq (t : ℝ) (ht : t ∈ Ioo a T) :
      Iteration.realSecondDerivativeCLM (W t) = r t := by
    have hw : Continuous (fun x ↦ fields.vorticity x t) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
    have hq := (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 hw (hrep t ht)).1
      |>.continuous_deriv le_rfl
    apply Lp.ext
    filter_upwards [(hGrep t ht).1.ae_hasDerivAt_of_continuous hq,
      (hr t ht).2.2.ae_hasDerivAt_of_continuous hq] with x hx hy
    exact hx.unique hy
  have hG (t : ℝ) (ht : t ∈ Ioo a T) :
      (G t : ℝ → ℝ) =ᵐ[volume] fun x ↦
        -(ρ t + deriv (fun y ↦ fields.velocity y t) x) * r t x +
          realHilbertTransformL2 (r t) x * fields.vorticity x t +
            deriv (deriv (fun y ↦ fields.velocity y t)) x *
              deriv (fun y ↦ fields.vorticity y t) x := by
    simpa only [heq t ht] using (hGrep t ht).2
  refine ⟨r, G, hr, hc, fun c d hcd ↦ ⟨(hmem c d hcd).1, hGmem c d hcd⟩, hG, ?_⟩
  intro t ht ψ hψ hψc
  apply (he t ht ψ hψ hψc).congr_deriv
  congr 1
  apply integral_congr_ae
  filter_upwards [hG t ht] with x hx
  rw [hx]
  ring

end DeGregorio
