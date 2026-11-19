/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakTransport
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakContinuity

/-!
# Time evolution of the second spatial distribution

On an interval with a bounded supported H² trajectory, the normalized
equation supplies an L² majorant for the time derivative. Differentiation
against an L² test therefore commutes with spatial integration.

Combined with the weak spatial commutator identity, this gives the evolution
of the second spatial distribution, tested against compact spatial functions. The H²
bound is local in time; `WeakH2Bound` propagates it by the transport energy argument.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- An L² majorant of pointwise time derivatives justifies differentiating
every fixed L² spatial pairing. -/
theorem hasDerivAt_integral_mul_of_memLp_majorant
    {w z : ℝ → ℝ → ℝ} {M ψ : ℝ → ℝ} {t : ℝ} {I : Set ℝ}
    (hI : I ∈ 𝓝 t)
    (hw : ∀ τ ∈ I, MemLp (fun x ↦ w x τ) 2 volume)
    (hz : AEStronglyMeasurable (fun x ↦ z x t) volume)
    (hψ : MemLp ψ 2 volume) (hM : MemLp M 2 volume)
    (hbound : ∀ᵐ x ∂volume, ∀ τ ∈ I, ‖z x τ‖ ≤ M x)
    (hderiv : ∀ᵐ x ∂volume, ∀ τ ∈ I, HasDerivAt (w x) (z x τ) τ) :
    HasDerivAt (fun τ ↦ ∫ x, w x τ * ψ x) (∫ x, z x t * ψ x) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ x ↦ w x τ * ψ x) (F' := fun τ x ↦ z x τ * ψ x)
    (bound := fun x ↦ ‖M x‖ * ‖ψ x‖) hI ?_
    ((hw t (mem_of_mem_nhds hI)).integrable_mul hψ)
    (hz.mul hψ.aestronglyMeasurable) ?_
    (hM.norm.integrable_mul hψ.norm) ?_).2
  · filter_upwards [hI] with τ hτ
    exact (hw τ hτ).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    intro τ hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hx τ hτ).trans (le_abs_self _)) (norm_nonneg _)
  · filter_upwards [hderiv] with x hx
    intro τ hτ
    exact (hx τ hτ).mul_const (ψ x)

end DeGregorio.Iteration

namespace DeGregorio

/-- The equal-rate equation evolves its second spatial distribution on every locally
H²-bounded supported interval. The weak highest derivatives are constructed, and the
normalization hypotheses are `u(0, t) = 0` and the endpoint formula for the rate. -/
theorem IsClassicalRescaledSolutionOn.hasDerivAt_secondDistribution_of_supported_h2
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ τ ∈ Ioo a T, F τ ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ τ ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F τ) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x τ))
    (hzero : ∀ τ ∈ Ioo a T, fields.velocity 0 τ = 0)
    (hnormalized : ∀ τ ∈ Ioo a T, ρ τ = -fields.velocity R τ / R)
    {t : ℝ} (ht : t ∈ Ioo a T) :
    ∃ (r : Lp ℝ 2 (volume : Measure ℝ)) (s : ℝ → ℝ),
      HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) r ∧
      IsHilbertPair r s ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        HasDerivAt (fun τ ↦ ∫ x, fields.vorticity x τ * deriv (deriv ψ) x)
          ((∫ x, (ρ t * x + fields.velocity x t) * r x * deriv ψ x) +
            ∫ x, (s x * fields.vorticity x t +
              deriv (deriv (fun y ↦ fields.velocity y t)) x *
                deriv (fun y ↦ fields.vorticity y t) x) * ψ x) t := by
  have hw : Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  have hw₁ := (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 hw (hrep t ht)).1
  have hsupp : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
    hK.of_isClosed_subset (isClosed_tsupport _)
      (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed
        (hbound t ht) hw (hrep t ht))
  obtain ⟨W, _, hW⟩ := (hbound t ht).1
  have hWrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] fun x ↦ fields.vorticity x t := hW ▸ hrep t ht
  obtain ⟨r, s, hqr, hrs, hu₂, _, htest⟩ :=
    hsol.exists_weak_secondDerivative_transport ht W hWrep hsupp (hzero t ht)
  have hz : Continuous (fun x ↦ deriv (fields.vorticity x) t) := by
    have heq : (fun x ↦ deriv (fields.vorticity x) t) =
        fun x ↦ (ρ t + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t -
          (ρ t * x + fields.velocity x t) * deriv (fun y ↦ fields.vorticity y t) x :=
      funext fun x ↦ by
        simpa only [one_mul] using eq_sub_of_add_eq (hsol.transport (x := x) ht)
    rw [heq]
    exact ((continuous_const.add (hu₂.continuous_deriv (by norm_num))).mul hw).sub
      (((continuous_const.mul continuous_id).add hu₂.continuous).mul
        (hw₁.continuous_deriv le_rfl))
  obtain ⟨M, hM, hmajorant⟩ :=
    hsol.exists_timeDerivative_majorant_of_supported_h2 hR hK hbound hrep hzero hnormalized
  refine ⟨r, s, hqr, hrs, fun ψ hψ hc ↦ ?_⟩
  have hψLp : MemLp (deriv (deriv ψ)) 2 volume :=
    (hψ.deriv' (n := 1)).continuous_deriv le_rfl |>.memLp_of_hasCompactSupport hc.deriv.deriv
  have hd := Iteration.hasDerivAt_integral_mul_of_memLp_majorant
    (Ioo_mem_nhds ht.1 ht.2)
    (fun τ hτ ↦ (hsol.biotSavart hτ).memLp_left)
    hz.aestronglyMeasurable hψLp hM (Eventually.of_forall hmajorant)
    (Eventually.of_forall fun _ _ hτ ↦
      (hsol.regularity.vorticity_time_differentiableAt hτ).hasDerivAt)
  exact hd.congr_deriv (htest ψ hψ hc)

/-- The normalized equation has a single weakly continuous L² second-derivative
trajectory satisfying the differentiated weak evolution. The derivative is taken
after pairing with a compact C² spatial test.
The trajectory is extended by zero outside the given open time interval. -/
theorem IsClassicalRescaledSolutionOn.exists_weak_secondDerivative_evolution
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R) :
    ∃ r : ℝ → Lp ℝ 2 (volume : Measure ℝ),
      (∀ t ∈ Ioo a T, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      (∀ ℓ : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ,
        ContinuousOn (fun t ↦ ℓ (r t)) (Ioo a T)) ∧
      ∀ t ∈ Ioo a T, ∃ s : ℝ → ℝ, IsHilbertPair (r t) s ∧
        ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
          HasDerivAt (fun τ ↦ ∫ x, r τ x * ψ x)
            ((∫ x, (ρ t * x + fields.velocity x t) * r t x * deriv ψ x) +
              ∫ x, (s x * fields.vorticity x t +
                deriv (deriv (fun y ↦ fields.velocity y t)) x *
                  deriv (fun y ↦ fields.vorticity y t) x) * ψ x) t := by
  classical
  obtain ⟨r₀, hr₀, hc₀⟩ :=
    hsol.exists_weaklyContinuous_secondDerivative hR hK hbound hrep hzero hnormalized
  let r : ℝ → Lp ℝ 2 (volume : Measure ℝ) :=
    fun t ↦ if ht : t ∈ Ioo a T then r₀ ⟨t, ht⟩ else 0
  have heq (t : ℝ) (ht : t ∈ Ioo a T) : r t = r₀ ⟨t, ht⟩ := dite_eq_left ht
  have hr (t : ℝ) (ht : t ∈ Ioo a T) :
      ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t) := by
    rw [heq t ht]
    exact hr₀ ⟨t, ht⟩
  have hw (t : ℝ) (ht : t ∈ Ioo a T) :
      Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  have hq (t : ℝ) (ht : t ∈ Ioo a T) :
      Continuous (deriv (fun x ↦ fields.vorticity x t)) :=
    (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 (hw t ht) (hrep t ht)).1
      |>.continuous_deriv le_rfl
  refine ⟨r, hr, fun ℓ ↦ ?_, fun t ht ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (hc₀ ℓ).congr fun t ↦ congrArg ℓ (heq t t.property).symm
  · obtain ⟨v, s, hqv, hvs, htest⟩ :=
      hsol.hasDerivAt_secondDistribution_of_supported_h2
        hR hK hbound hrep hzero hnormalized ht
    have hv : v = r t := by
      apply Lp.ext
      filter_upwards [hqv.ae_hasDerivAt_of_continuous (hq t ht),
        (hr t ht).2.2.ae_hasDerivAt_of_continuous (hq t ht)] with x hx hy
      exact hx.unique hy
    rw [hv] at hvs htest
    refine ⟨s, hvs, fun ψ hψ hψc ↦ ?_⟩
    apply (htest ψ hψ hψc).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact Iteration.integral_weak_secondDerivative_test
      (hr τ hτ).2.1 (hr τ hτ).2.2 (hw τ hτ) (hq τ hτ) hψ hψc

end DeGregorio
