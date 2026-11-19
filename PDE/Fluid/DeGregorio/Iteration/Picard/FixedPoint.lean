/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Contraction

/-!
# The frozen transport fixed point

Compactly supported weak H² data generate a coupled classical solution of the De Gregorio equation
(`a = 1`) on a positive time interval constructed from the datum (`exists_hkCurve_local_solution`).
The solution is the fixed point of the frozen transport map on the complete supported H² base ball
of L²-continuous curves.

## How it works

We freeze the velocity. An input curve `f` in the complete class of L²-continuous curves in the
supported H² ball (`completeSpace_supportedHkCurves`) gives the Hilbert velocity
`hkCurveHilbertVelocity`, and the output solves the linear transport and stretching equation with
that velocity (`exists_hkFrozenOutput`, with the properties listed in `IsHkFrozenOutput`). The
squared L² distance of two outputs is bounded by that of the inputs times a Grönwall factor
(`IsHkFrozenOutput.dist_sq_le`, through
`differenceEnergy_le_gronwallBound_of_frozen_transport_interior` and Mathlib's `gronwallBound`); for
small time the factor is at most `1/2`, so the map is a contraction with constant `√(1/2)`
(`exists_hkFrozen_contraction`). The Banach fixed point theorem of Mathlib
(`ContractingWith.fixedPoint`) gives a fixed point (`exists_hkFrozen_fixedPoint`), at which the
Hilbert input and the transported output are the same L² class, so the frozen equation becomes the
coupled one (`IsHkFrozenOutput.isClassicalSolutionOn`). In `exists_hkCurve_local_solution` the ball
budget `B`, the support radius `S * Real.exp 2` and the time `T` are chosen from the datum alone
(`hkTransportH2Bound_explicit_budget`, `exists_pos_frozen_transport_factor_le_half`).
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- Numerical invariant-ball and time-factor bounds construct a
frozen transport operator and prove its contraction property. -/
theorem exists_hkFrozen_contraction
    {B : NNReal} {T S R L : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hBT : (B : ℝ) * T ≤ 1) (hR : S * Real.exp 2 ≤ R)
    (hL : 0 ≤ L) (hRL : R < L)
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0)
    (hbudget : hkTransportH2Bound 1 * ‖W₀‖ ≤ B)
    (hsmall : ∀ s ∈ Icc 0 T,
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) s ≤ 1 / 2) :
    ∃ Φ : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B) →
      C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B),
      (∀ f, ∃ c w : ℝ → ℝ → ℝ, IsHkFrozenOutput hT f (Φ f) W₀ w₀ c w) ∧
      ContractingWith ⟨Real.sqrt (1 / 2), Real.sqrt_nonneg _⟩ Φ := by
  classical
  have hout := fun f ↦ exists_hkFrozenOutput hT hS hBT hR f W₀ hw₀ hW₀ hsupp₀ hbudget
  choose Φ c w hΦ using hout
  refine ⟨Φ, fun f ↦ ⟨c f, w f, hΦ f⟩, ?_, ?_⟩
  · change Real.sqrt (1 / 2) < 1
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    exact (hΦ f).dist_le_sqrt_half (hΦ g) hL hRL hsmall

/-- At a frozen fixed point, the Hilbert input and transported output are the
same L² class, giving the coupled classical equation in the interior. -/
theorem IsHkFrozenOutput.isClassicalSolutionOn
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {F : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) :
    IsClassicalSolutionOn 1 ⟨w, hkCurveHilbertVelocity hT F⟩ (Ioo 0 T) := by
  refine ⟨⟨?_, ?_⟩, h.satisfies_transport, ?_⟩
  · intro x t ht
    exact (h.classical.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)).differentiableAt
        (by simp)
  · intro x t _
    exact (h.velocity_derivative x t).differentiableAt
  · intro t ht
    have hp := h.hilbert_pair t
    rw [projIcc_of_mem hT (Ioo_subset_Icc_self ht)] at hp
    exact hp.congr_ae (h.representative ⟨t, Ioo_subset_Icc_self ht⟩)
      (.of_forall fun x ↦ (h.velocity_derivative x t).deriv.symm)

/-- The complete L²-metric supported H² class contains a coupled fixed point
of the frozen transport operator whenever the numerical budgets hold. -/
theorem exists_hkFrozen_fixedPoint
    {B : NNReal} {T S R L : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hBT : (B : ℝ) * T ≤ 1) (hR : S * Real.exp 2 ≤ R)
    (hL : 0 ≤ L) (hRL : R < L)
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0)
    (hbudget : hkTransportH2Bound 1 * ‖W₀‖ ≤ B)
    (hsmall : ∀ s ∈ Icc 0 T,
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) s ≤ 1 / 2) :
    ∃ (F : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
      (c w : ℝ → ℝ → ℝ),
      IsHkFrozenOutput hT F F W₀ w₀ c w ∧
      IsClassicalSolutionOn 1 ⟨w, hkCurveHilbertVelocity hT F⟩ (Ioo 0 T) := by
  let Z : supportedHkBaseBall 1 2 univ
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B :=
    ⟨0, ⟨⟨0, by simpa only [norm_zero] using B.coe_nonneg, map_zero _⟩, map_zero _⟩⟩
  have : Nonempty C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B) :=
    ⟨ContinuousMap.const _ Z⟩
  have := completeSpace_supportedHkCurves
    1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B 0 T
  obtain ⟨Φ, hΦ, hcontract⟩ :=
    exists_hkFrozen_contraction hT hS hBT hR hL hRL W₀ hw₀ hW₀ hsupp₀ hbudget hsmall
  let F := hcontract.fixedPoint Φ
  have hfix : Φ F = F := hcontract.fixedPoint_isFixedPt
  obtain ⟨c, w, hF⟩ := hΦ F
  rw [hfix] at hF
  exact ⟨F, c, w, hF, hF.isClassicalSolutionOn⟩

/-- Compactly supported weak H² data generate a coupled classical solution
for a constructed positive time, with a continuous L² trace and a uniform
supported H² graph bound. The time and ball budgets depend only on the datum. -/
theorem exists_hkCurve_local_solution
    {S : ℝ} (hS : 0 ≤ S) (W₀ : W^{2,2}((Set.univ : Set (ℝ^1))))
    {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0) :
    ∃ (T : ℝ) (hT : 0 < T) (B : NNReal)
      (F : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
            Icc (-(S * Real.exp 2)) (S * Real.exp 2)) B))
      (c w : ℝ → ℝ → ℝ),
      IsHkFrozenOutput hT.le F F W₀ w₀ c w ∧
      IsClassicalSolutionOn 1 ⟨w, hkCurveHilbertVelocity hT.le F⟩ (Ioo 0 T) := by
  obtain ⟨hB, hτ, hbudget, hBT⟩ := hkTransportH2Bound_explicit_budget W₀
  let B : NNReal := ⟨hkTransportH2Bound 1 * ‖W₀‖ + 1, hB.le⟩
  let R := S * Real.exp 2
  let L := R + 1
  obtain ⟨δ, hδ, hfactor⟩ := exists_pos_frozen_transport_factor_le_half L (2 * (B : ℝ))
  let T := min δ (1 / ((B : ℝ) + 1))
  have hT : 0 < T := lt_min hδ hτ
  have hL : 0 ≤ L := by dsimp [L, R]; positivity
  obtain ⟨F, c, w, hF, hsol⟩ := exists_hkFrozen_fixedPoint
    (B := B) hT.le hS (hBT T hT.le (min_le_right _ _)) (le_refl R) hL
    (lt_add_one R) W₀ hw₀ hW₀ hsupp₀ hbudget
    (fun s hs ↦ hfactor s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩)
  exact ⟨T, hT, B, F, c, w, hF, hsol⟩

end DeGregorio.Iteration
