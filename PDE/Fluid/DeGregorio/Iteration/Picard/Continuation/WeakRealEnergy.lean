/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakEnergy
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative

/-!
# Real-line transport energy in the Euclidean Sobolev model

The scalar real-line test formulation is transported isometrically to the
one-dimensional, one-component system used by the Bochner commutator theorem.
The highest derivative remains an L² state throughout this identification.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open PDE.Hyperbolic.FirstOrder
open scoped ENNReal InnerProductSpace Topology Distributions Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

namespace DeGregorio.Iteration

local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
local notation "H" => PiLp 2 (fun _ : Fin 1 ↦ DerivLp 1 2 univ)
local notation "V" => PiLp 2 (fun _ : Fin 1 ↦ H¹(ℝ^1))
local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

/-- A scalar real L² state as a one-component Euclidean L² state. -/
def realTransportStateCLM : L₂ →L[ℝ] H :=
  (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ DerivLp 1 2 univ)).symm.toContinuousLinearMap.comp
    oneDimensionalPullbackL2.toContinuousLinearMap

/-- The sole component is the measure-preserving pullback. -/
@[simp] theorem realTransportStateCLM_apply (r : L₂) (i : Fin 1) :
    realTransportStateCLM r i = oneDimensionalPullbackL2 r := by
  rfl

/-- The embedding of a real state into the transport space is an isometry. -/
@[simp] theorem norm_realTransportStateCLM (r : L₂) :
    ‖realTransportStateCLM r‖ = ‖r‖ := by
  have h := PiLp.norm_sq_eq_of_L2 _ (realTransportStateCLM r)
  simp only [Fin.sum_univ_one, realTransportStateCLM_apply,
    oneDimensionalPullbackL2.norm_map] at h
  nlinarith only [h, norm_nonneg (realTransportStateCLM r), norm_nonneg r]

/-- Pairings are unchanged under the real-line transport embedding. -/
@[simp] theorem inner_realTransportStateCLM (r s : L₂) :
    ⟪realTransportStateCLM r, realTransportStateCLM s⟫_ℝ = ⟪r, s⟫_ℝ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_one, realTransportStateCLM_apply]
  exact oneDimensionalPullbackL2.inner_map_map r s

/-- A mixed Euclidean/real L² pairing is the ordinary real-line integral. -/
theorem inner_pullback_eq_integral (r : L₂) (g : DerivLp 1 2 univ)
    {ψ : ℝ → ℝ} (hg : (oneDimensionalPushforwardL2 g : ℝ → ℝ) =ᵐ[volume] ψ) :
    ⟪oneDimensionalPullbackL2 r, g⟫_ℝ = ∫ x, r x * ψ x := by
  rw [← oneDimensionalPushforwardL2.inner_map_map, oneDimensionalPushforwardL2_pullback,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  simp only [Real.inner_apply, hx, mul_comm]

/-- A bounded multiplier commutes almost everywhere with the real-coordinate
identification. -/
theorem pushforward_mul_ae
    (b : DerivLp 1 ∞ univ) (g : DerivLp 1 2 univ)
    {v ψ : ℝ → ℝ}
    (hb : (fun x ↦ b ((e).symm x)) =ᵐ[volume] v)
    (hg : (oneDimensionalPushforwardL2 g : ℝ → ℝ) =ᵐ[volume] ψ) :
    (oneDimensionalPushforwardL2 (b • g) : ℝ → ℝ) =ᵐ[volume]
      fun x ↦ v x * ψ x := by
  have hm := Lp.coeFn_lpSMul (r := 2) b g
  simp only [domainMeasure, Measure.restrict_univ] at hm
  have hcomp := measurePreserving_equivOfUnique_symm.quasiMeasurePreserving.ae_eq_comp hm
  filter_upwards [oneDimensionalPushforwardL2_ae (b • g),
    oneDimensionalPushforwardL2_ae g, hcomp, hb, hg] with x hx hgx hmx hbx hψx
  change _ = b ((e).symm x) * g ((e).symm x) at hmx
  exact hx.trans (hmx.trans (congrArg₂ (· * ·) hbx (hgx.symm.trans hψx)))

/-- A compact smooth spatial test has the expected base and derivative
representatives on the real line. -/
theorem real_transport_test_coordinates (ψ : 𝓓((⊤ : Opens (ℝ^1)), ℝ)) :
    let φ := globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) ψ
    (oneDimensionalPushforwardL2 (wkpCoordinateCLM (baseIndex 1 1) φ) : ℝ → ℝ)
        =ᵐ[volume] ψ ∘ (e).symm ∧
      (oneDimensionalPushforwardL2 (wkpCoordinateCLM (singleDerivIndex 1 0) φ) : ℝ → ℝ)
        =ᵐ[volume] deriv (ψ ∘ (e).symm) := by
  intro φ
  have hcoord (d : DerivIndex 1 1) :=
    globalTestFunctionToWkpOn_coordinate_ae (p := 2) (Ω := univ) ψ d
  have hreal (d : DerivIndex 1 1) :
      (oneDimensionalPushforwardL2 (wkpCoordinateCLM d φ) : ℝ → ℝ) =ᵐ[volume]
        fun x ↦ iteratedPartialDeriv d.toList ψ ((e).symm x) := by
    have hd := hcoord d
    simp only [domainMeasure, Measure.restrict_univ] at hd
    exact (oneDimensionalPushforwardL2_ae _).trans
      (measurePreserving_equivOfUnique_symm.quasiMeasurePreserving.ae_eq_comp hd)
  constructor
  · simpa only [baseIndex_toList, iteratedPartialDeriv, Function.comp_def] using
      hreal (baseIndex 1 1)
  · filter_upwards [hreal (singleDerivIndex 1 0)] with x hx
    rw [PDE.deriv_comp_equivOfUnique_symm ψ x (ψ.contDiff.differentiable (by simp) _)]
    simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hx

/-- The scalar transport test pairing, with both integration-by-parts terms
written as real-line integrals. -/
theorem real_transport_test_pairing
    (A : W^{1,∞}((univ : Set (ℝ^1)))) {v d : ℝ → ℝ}
    (hv : (fun x ↦ (A : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) ((e).symm x))
      =ᵐ[volume] v)
    (hd : (fun x ↦ (A : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
      =ᵐ[volume] d)
    (ψ : 𝓓((⊤ : Opens (ℝ^1)), ℝ)) (r : L₂) :
    let φ : V := WithLp.toLp 2 (fun _ ↦
      globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) ψ)
    transportTestFunctional (fun _ _ _ ↦ A) φ (realTransportStateCLM r) =
      (∫ x, v x * r x * deriv (ψ ∘ (e).symm) x) +
        ∫ x, d x * r x * (ψ ∘ (e).symm) x := by
  intro φ
  obtain ⟨hb, hs⟩ := real_transport_test_coordinates ψ
  rw [transportTestFunctional_apply]
  simp only [Fin.sum_univ_one, realTransportStateCLM_apply, inner_add_right]
  rw [inner_pullback_eq_integral r _ (pushforward_mul_ae _ _ hv hs),
    inner_pullback_eq_integral r _ (pushforward_mul_ae _ _ hd hb)]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards with x <;> ring

/-- The divergence production is the coefficient derivative times the square
of the real L² state. -/
theorem real_transport_divergence_pairing
    (A : W^{1,∞}((univ : Set (ℝ^1)))) {d : ℝ → ℝ}
    (hd : (fun x ↦ (A : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
      =ᵐ[volume] d) (r : L₂) :
    transportDivergencePairing (fun _ _ _ ↦ A) (realTransportStateCLM r) =
      ∫ x, d x * (r x) ^ 2 := by
  simp only [transportDivergencePairing, Fin.sum_univ_one, realTransportStateCLM_apply]
  rw [real_inner_comm]
  have hr : (oneDimensionalPushforwardL2 (oneDimensionalPullbackL2 r) : ℝ → ℝ)
      =ᵐ[volume] r := by rw [oneDimensionalPushforwardL2_pullback]
  rw [inner_pullback_eq_integral r _ (pushforward_mul_ae _ _ hd hr)]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The real-line divergence and forcing production is time-integrable
under the same Bochner hypotheses as the transport energy identity. -/
theorem integrable_real_transport_production
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → W^{1,∞}((univ : Set (ℝ^1))))
    (hA : ContinuousOn (fun t ↦
      (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1)) (Icc a b))
    (L : NNReal)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0)‖ ≤ L)
    {d : ℝ → ℝ → ℝ}
    (hd : ∀ t ∈ Icc a b,
      (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
        =ᵐ[volume] d t)
    {r G : ℝ → L₂}
    (hr2 : MemLp r 2 (volume.restrict (Ioc a b)))
    (hG : MemLp G 2 (volume.restrict (Ioc a b))) :
    Integrable
      (fun t ↦ (∫ x, d t x * (r t x) ^ 2) + 2 * ⟪G t, r t⟫_ℝ)
      (volume.restrict (Ioc a b)) := by
  have hi := integrable_transportDivergencePairing hab (fun t _ _ _ ↦ A t)
    (fun _ _ _ ↦ hA) L (fun t ht j _ _ ↦ by
      simpa only [show j = 0 from Subsingleton.elim _ _] using hL t ht)
    (hr2.continuousLinearMap_comp realTransportStateCLM)
  have heq :
      (fun t ↦ transportDivergencePairing (fun _ _ _ ↦ A t)
        (realTransportStateCLM (r t))) =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ ∫ x, d t x * (r t x) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact real_transport_divergence_pairing (A t) (hd t (Ioc_subset_Icc_self ht)) (r t)
  have hforce : Integrable (fun t ↦ ⟪G t, r t⟫_ℝ) (volume.restrict (Ioc a b)) :=
    (hG.norm.integrable_mul hr2.norm).mono'
      (hG.aestronglyMeasurable.inner hr2.aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ norm_inner_le_norm (G t) (r t))
  exact (hi.congr heq).add (hforce.const_mul 2)

/-- The scalar real-line weak transport equation gives exact L² energy.
The state and source are Bochner L² in time. The bounded coefficient may be a
localization of the original drift. -/
theorem real_energy_sub_eq_integral_of_smooth_test_derivative
    {a b : ℝ} (hab : a < b)
    (A : ℝ → W^{1,∞}((univ : Set (ℝ^1))))
    (hA : ContinuousOn (fun t ↦
      (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1)) (Icc a b))
    (L : NNReal)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0)‖ ≤ L)
    {v d : ℝ → ℝ → ℝ}
    (hv : ∀ t ∈ Icc a b,
      (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) ((e).symm x))
        =ᵐ[volume] v t)
    (hd : ∀ t ∈ Icc a b,
      (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
        =ᵐ[volume] d t)
    {r G : ℝ → L₂}
    (hr : ∀ ℓ : L₂ →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (r t)) (Icc a b))
    (hr2 : MemLp r 2 (volume.restrict (Ioc a b)))
    (hG : MemLp G 2 (volume.restrict (Ioc a b)))
    (htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ t ∈ Icc a b, HasDerivAt (fun τ ↦ ∫ x, r τ x * ψ x)
        ((∫ x, v t x * r t x * deriv ψ x) +
          ∫ x, (d t x * r t x + G t x) * ψ x) t) :
    ‖r b‖ ^ 2 - ‖r a‖ ^ 2 =
      ∫ t in Ioc a b, (∫ x, d t x * (r t x) ^ 2) + 2 * ⟪G t, r t⟫_ℝ := by
  have htest' (Ψ : Fin 1 → 𝓓((⊤ : Opens (ℝ^1)), ℝ)) :
      let φ : V := WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (Ψ p))
      ∀ t ∈ Icc a b, HasDerivAt
        (fun τ ↦ ⟪realTransportStateCLM (r τ), transportBaseCLM φ⟫_ℝ)
        (transportTestFunctional (fun _ _ _ ↦ A t) φ (realTransportStateCLM (r t)) +
          ⟪realTransportStateCLM (G t), transportBaseCLM φ⟫_ℝ) t := by
    intro φ t ht
    let ψ : ℝ → ℝ := Ψ 0 ∘ (e).symm
    have hψ : ContDiff ℝ 2 ψ :=
      ((Ψ 0).contDiff.of_le (by simp)).comp (e).symm.contDiff
    have hcψ : HasCompactSupport ψ := (Ψ 0).hasCompactSupport.comp_homeomorph
      (e).symm.toHomeomorph
    have hb := (real_transport_test_coordinates (Ψ 0)).1
    have hp (z : L₂) :
        ⟪realTransportStateCLM z, transportBaseCLM φ⟫_ℝ = ∫ x, z x * ψ x := by
      simp only [PiLp.inner_apply, Fin.sum_univ_one, realTransportStateCLM_apply,
        transportBaseCLM_apply]
      exact inner_pullback_eq_integral z _ hb
    have heqφ : φ = WithLp.toLp 2 (fun _ : Fin 1 ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (Ψ 0)) := by
      apply PiLp.ext
      intro i
      exact congrArg (fun p ↦ globalTestFunctionToWkpOn (k := 1) (p := 2)
        (Ω := univ) (Ψ p)) (Subsingleton.elim i 0)
    have hdm := pushforward_mul_ae _ _ (hd t ht) hb
    have hi : Integrable (fun x ↦ d t x * r t x * ψ x) volume := by
      apply ((Lp.memLp (r t)).integrable_mul (Lp.memLp
        (oneDimensionalPushforwardL2
          ((A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) •
            wkpCoordinateCLM (baseIndex 1 1)
              (globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (Ψ 0)))))).congr
      filter_upwards [hdm] with x hx
      simp only [Pi.mul_apply]
      rw [hx]
      ring
    have hgi := (Lp.memLp (G t)).integrable_mul
      (hψ.continuous.memLp_of_hasCompactSupport hcψ (p := 2))
    simpa only [hp] using (htest ψ hψ hcψ t ht).congr_deriv (by
      rw [heqφ, real_transport_test_pairing (A t) (hv t ht) (hd t ht)]
      have hs :
          (∫ x, (d t x * r t x + G t x) * ψ x) =
            (∫ x, d t x * r t x * ψ x) + ∫ x, G t x * ψ x := by
        simp_rw [add_mul]
        exact integral_add hi hgi
      rw [hs]
      ring)
  have hE := energy_sub_eq_integral_of_smooth_test_derivative
    (fun t _ _ _ ↦ A t) (fun _ _ _ ↦ hA) hab (fun _ _ _ _ _ ↦ rfl) L
    (fun t ht _ _ _ ↦ by simpa only [Fin.sum_univ_one] using hL t ht)
    (fun ℓ ↦ hr (ℓ.comp realTransportStateCLM))
    (hr2.continuousLinearMap_comp realTransportStateCLM)
    (hG.continuousLinearMap_comp realTransportStateCLM) htest'
  change ‖realTransportStateCLM (r b)‖ ^ 2 - ‖realTransportStateCLM (r a)‖ ^ 2 =
    ∫ t in Ioc a b, transportDivergencePairing (fun _ _ _ ↦ A t)
      (realTransportStateCLM (r t)) +
        2 * ⟪realTransportStateCLM (G t), realTransportStateCLM (r t)⟫_ℝ at hE
  simp only [norm_realTransportStateCLM, inner_realTransportStateCLM] at hE
  rw [hE]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [real_transport_divergence_pairing (A t) (hd t (Ioc_subset_Icc_self ht))]

end DeGregorio.Iteration
