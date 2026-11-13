/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.DerivativeSplits
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff
public import PDE.Spaces.Sobolev.Calculus.Product.ClassicalLeibniz
import Mathlib.Algebra.Order.Chebyshev

/-!
# Derivative errors of radial truncation

Subtracting a jet from its truncated jet gives the ordered Leibniz sum, with the
undifferentiated cutoff replaced by `χ_R - 1`. Every coefficient vanishes on the inner
ball and is uniformly bounded after multiplication by the corresponding radial power.
For a weight with polynomial growth, the lower exterior jet energies dominate the full
error. Their integrability gives convergence of the weighted square integral to zero.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Metric Set SobolevSpace
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- The coefficient of a left derivative word in a cutoff jet error.
The empty word represents the principal tail term `χ_R - 1`. -/
def radialCutoffJetError (α : List (Fin n)) (R : ℝ) : ℝ^n → ℝ :=
  fun x ↦ iteratedPartialDeriv α (radialCutoff R) x - if α = [] then 1 else 0

/-- Each coefficient in the finite exterior error is continuous. -/
theorem continuous_radialCutoffJetError (α : List (Fin n)) (R : ℝ) :
    Continuous (radialCutoffJetError α R) :=
  (PDE.contDiff_top_iteratedPartialDeriv (radialCutoff_contDiff R) α).continuous.sub
    continuous_const

/-- The principal tail term and all differentiated terms vanish in the inner ball. -/
theorem radialCutoffJetError_zero_inside (α : List (Fin n))
    {R : ℝ} (hR : 0 < R) {x : ℝ^n} (hx : ‖x‖ < R) :
    radialCutoffJetError α R x = 0 := by
  by_cases hα : α = []
  · subst α
    simp [radialCutoffJetError, iteratedPartialDeriv, radialCutoff_eq_one hR hx.le]
  · simp [radialCutoffJetError, hα,
      radialCutoff_derivative_zero_inside α hα hR hx]

/-- Each cutoff coefficient has a uniform bound after multiplying by
the radial power corresponding to its derivative order. -/
theorem exists_radialCutoffJetError_scaled_bound (α : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      (‖x‖ ^ 2) ^ α.length * (radialCutoffJetError α R x) ^ 2 ≤ C := by
  by_cases hα : α = []
  · subst α
    refine ⟨1, zero_le_one, ?_⟩
    intro R _ x
    have hχ := radialCutoff_mem_Icc R x
    change 0 ≤ radialCutoff R x ∧ radialCutoff R x ≤ 1 at hχ
    simp only [radialCutoffJetError, iteratedPartialDeriv, ↓reduceIte,
      List.length_nil, pow_zero, one_mul]
    nlinarith [hχ.1, hχ.2]
  obtain ⟨B, hB, hderiv⟩ := exists_radialCutoff_derivative_bound α
  refine ⟨B ^ 2 * (4 : ℝ) ^ α.length, by positivity, ?_⟩
  intro R hR x
  simp only [radialCutoffJetError, hα, ↓reduceIte, sub_zero]
  by_cases hx : ‖x‖ ≤ 2 * R
  · have hi : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    have hd : (iteratedPartialDeriv α (radialCutoff R) x) ^ 2 ≤
        B ^ 2 * (R⁻¹ ^ 2) ^ α.length := by
      have hs := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg hB (pow_nonneg hi _))).mpr (hderiv R hR x)
      simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm α.length 2] using hs
    have hs : ‖x‖ * R⁻¹ ≤ 2 := (mul_inv_le_iff₀ hR).mpr hx
    have hs0 : 0 ≤ ‖x‖ * R⁻¹ := mul_nonneg (norm_nonneg x) hi
    have hr : ‖x‖ ^ 2 * R⁻¹ ^ 2 ≤ 4 := by
      nlinarith [mul_self_le_mul_self hs0 hs]
    calc
      _ ≤ (‖x‖ ^ 2) ^ α.length * (B ^ 2 * (R⁻¹ ^ 2) ^ α.length) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = B ^ 2 * (‖x‖ ^ 2 * R⁻¹ ^ 2) ^ α.length := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hr α.length) (sq_nonneg B)
  · have hz : iteratedPartialDeriv α (radialCutoff R) x = 0 := by
      exact radialCutoff_derivative_zero_outside α hR (lt_of_not_ge hx)
    rw [hz]
    simpa using (show 0 ≤ B ^ 2 * (4 : ℝ) ^ α.length by positivity)

private theorem sum_derivativeSplits_empty_left (α : List (Fin n))
    (g : List (Fin n) → ℝ) :
    ((derivativeSplits α).map
      (fun p ↦ (if p.1 = [] then 1 else 0) * g p.2)).sum = g α := by
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [List.sum_map_ite, derivativeSplits_filter_first_nil]
  simp

/-- The exact jet error is the full ordered Leibniz sum, with no split discarded
or multiplicity merged. -/
theorem radialCutoff_jet_sub_eq_sum (α : List (Fin n))
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (R : ℝ) (x : ℝ^n) :
    iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
        iteratedPartialDeriv α u x =
      ((derivativeSplits α).map (fun p ↦
        radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x)).sum := by
  rw [iteratedPartialDeriv_mul_eq_sum_split α _ _ (radialCutoff_contDiff R) hu]
  simp_rw [radialCutoffJetError, sub_mul]
  rw [List.sum_hom₂ _ (fun a b : ℝ ↦ a - b) (by intros; ring) (by simp),
    sum_derivativeSplits_empty_left α (fun γ ↦ iteratedPartialDeriv γ u x)]

/-- A cutoff jet error vanishes in the inner ball, including the undifferentiated row. -/
theorem radialCutoff_jet_sub_zero_inside
    (α : List (Fin n)) {u : ℝ^n → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {R : ℝ} (hR : 0 < R) {x : ℝ^n} (hx : ‖x‖ < R) :
    iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
      iteratedPartialDeriv α u x = 0 := by
  rw [radialCutoff_jet_sub_eq_sum α hu]
  simp [radialCutoffJetError_zero_inside _ hR hx]

/-- A weight with polynomial growth on the exterior controls the cutoff jet error by
finitely many lower radial jet energies. Every ordered Leibniz split is retained. -/
theorem exists_radialCutoff_jet_exterior_bound (α : List (Fin n)) (s : ℕ) :
    ∃ B : List (Fin n) → ℝ, (∀ β, 0 ≤ B β) ∧
      ∀ (u W : ℝ^n → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ C : ℝ, 0 ≤ C → ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
        (R ≤ ‖x‖ → W x ≤ C * (‖x‖ ^ 2) ^ (α.length + s)) →
        W x * (iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
            iteratedPartialDeriv α u x) ^ 2 ≤
          (derivativeSplits α).length * C *
            ((derivativeSplits α).map (fun p ↦
              B p.1 * (‖x‖ ^ 2) ^ (p.2.length + s) *
                (iteratedPartialDeriv p.2 u x) ^ 2)).sum := by
  choose B hB hbound using exists_radialCutoffJetError_scaled_bound
  refine ⟨B, hB, ?_⟩
  intro u W hu C hC R hR x htail
  have hsum0 : 0 ≤ ((derivativeSplits α).map (fun p ↦
      B p.1 * (‖x‖ ^ 2) ^ (p.2.length + s) *
        (iteratedPartialDeriv p.2 u x) ^ 2)).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (mul_nonneg (hB _) (by positivity)) (sq_nonneg _)
  rw [radialCutoff_jet_sub_eq_sum α hu]
  by_cases hx : ‖x‖ < R
  · have hz : ((derivativeSplits α).map (fun p ↦
        radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x)).sum = 0 := by
      simp [radialCutoffJetError_zero_inside _ hR hx]
    rw [hz]
    simpa using mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hC) hsum0
  have hxR : R ≤ ‖x‖ := le_of_not_gt hx
  let terms := (derivativeSplits α).map (fun p ↦
    radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x)
  have hCS : terms.sum ^ 2 ≤ (derivativeSplits α).length *
      ((derivativeSplits α).map (fun p ↦
        (radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x) ^ 2)).sum := by
    simpa [terms, List.map_map, Function.comp_def] using
      (Multiset.sq_sum_le_card_mul_sum_sq (terms : Multiset ℝ))
  have hterm (p : List (Fin n) × List (Fin n)) (hp : p ∈ derivativeSplits α) :
      (‖x‖ ^ 2) ^ (α.length + s) *
          (radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x) ^ 2 ≤
        B p.1 * (‖x‖ ^ 2) ^ (p.2.length + s) *
          (iteratedPartialDeriv p.2 u x) ^ 2 := by
    have hlen : α.length + s = p.1.length + (p.2.length + s) := by
      have := derivativeSplits_length hp
      omega
    calc
      _ = ((‖x‖ ^ 2) ^ p.1.length * (radialCutoffJetError p.1 R x) ^ 2) *
          ((‖x‖ ^ 2) ^ (p.2.length + s) * (iteratedPartialDeriv p.2 u x) ^ 2) := by
        rw [hlen, pow_add, mul_pow]
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hbound p.1 R hR x) (by positivity :
            0 ≤ (‖x‖ ^ 2) ^ (p.2.length + s) *
              (iteratedPartialDeriv p.2 u x) ^ 2)
  calc
    _ ≤ (C * (‖x‖ ^ 2) ^ (α.length + s)) *
        ((derivativeSplits α).length * ((derivativeSplits α).map (fun p ↦
          (radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x) ^ 2)).sum) :=
      mul_le_mul (htail hxR) hCS
        (sq_nonneg _) (mul_nonneg hC (by positivity))
    _ = (derivativeSplits α).length * C *
        ((derivativeSplits α).map (fun p ↦ (‖x‖ ^ 2) ^ (α.length + s) *
          (radialCutoffJetError p.1 R x * iteratedPartialDeriv p.2 u x) ^ 2)).sum := by
      rw [List.sum_map_mul_left]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (List.sum_le_sum hterm) (mul_nonneg (Nat.cast_nonneg _) hC)

/-- The square of a jet, weighted by its radial degree and restricted to the exterior
of the ball of radius `L`. The offset `s` allows an additional radial weight. -/
def exteriorJetEnergy (s : ℕ) (L : ℝ) (u : ℝ^n → ℝ)
    (γ : List (Fin n)) : ℝ^n → ℝ :=
  {x | L ≤ ‖x‖}.indicator
    (fun x ↦ (‖x‖ ^ 2) ^ (γ.length + s) * (iteratedPartialDeriv γ u x) ^ 2)

/-- Exterior radial energies of the lower jets imply weighted square-integral convergence
of the truncated jet. The measure is arbitrary and the weight only needs a polynomial
upper bound outside the ball of radius `L`. -/
theorem radialCutoff_jet_integral_convergence (α : List (Fin n)) (s : ℕ)
    {C L : ℝ} (hC : 0 ≤ C) {W u : ℝ^n → ℝ} {ν : Measure (ℝ^n)}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hW : AEStronglyMeasurable W ν) (hW0 : ∀ᵐ x ∂ν, 0 ≤ W x)
    (htail : ∀ᵐ x ∂ν, L ≤ ‖x‖ → W x ≤ C * (‖x‖ ^ 2) ^ (α.length + s))
    (hjets : ∀ p ∈ derivativeSplits α,
      Integrable (exteriorJetEnergy s L u p.2) ν) :
    (∀ R : ℝ, 0 < R → L ≤ R →
      Integrable (fun x ↦ W x *
        (iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
          iteratedPartialDeriv α u x) ^ 2) ν) ∧
    Tendsto (fun R : ℝ ↦ ∫ x, W x *
      (iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
        iteratedPartialDeriv α u x) ^ 2 ∂ν) atTop (𝓝 0) := by
  obtain ⟨B, _, hbound⟩ := exists_radialCutoff_jet_exterior_bound α s
  let H : ℝ^n → ℝ := fun x ↦ (derivativeSplits α).length * C *
    ((derivativeSplits α).map (fun p ↦ B p.1 * exteriorJetEnergy s L u p.2 x)).sum
  have hH : Integrable H ν := by
    have hsum (l : List (List (Fin n) × List (Fin n)))
        (hl : ∀ p ∈ l, Integrable (exteriorJetEnergy s L u p.2) ν) :
        Integrable (fun x ↦
          (l.map (fun p ↦ B p.1 * exteriorJetEnergy s L u p.2 x)).sum) ν := by
      induction l with
      | nil => simp
      | cons p l ih =>
        simpa only [List.map_cons, List.sum_cons] using
          ((hl p (by simp)).const_mul (B p.1)).fun_add
          (ih (fun q hq ↦ hl q (by simp [hq])))
    exact (hsum _ hjets).const_mul _
  let F (R : ℝ) : ℝ^n → ℝ := fun x ↦ W x *
    (iteratedPartialDeriv α (fun y ↦ radialCutoff R y * u y) x -
      iteratedPartialDeriv α u x) ^ 2
  have hFm (R : ℝ) : AEStronglyMeasurable (F R) ν :=
    hW.mul
      (((PDE.contDiff_top_iteratedPartialDeriv ((radialCutoff_contDiff R).mul hu) α).continuous.sub
        (PDE.contDiff_top_iteratedPartialDeriv hu α).continuous).aestronglyMeasurable.pow 2)
  have hb (R : ℝ) (hR : 0 < R) (hLR : L ≤ R) :
      ∀ᵐ x ∂ν, ‖F R x‖ ≤ H x := by
    filter_upwards [hW0, htail] with x hx htx
    change ‖W x * _ ^ 2‖ ≤ H x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hx (sq_nonneg _))]
    by_cases hL : L ≤ ‖x‖
    · simpa [H, exteriorJetEnergy, hL, mul_assoc] using
        hbound u W hu C hC R hR x (fun hRx ↦ htx (hLR.trans hRx))
    · have hin : ‖x‖ < R := (lt_of_not_ge hL).trans_le hLR
      rw [radialCutoff_jet_sub_zero_inside α hu hR hin]
      simp [H, exteriorJetEnergy, hL]
  refine ⟨fun R hR hLR ↦ hH.mono' (hFm R) (hb R hR hLR), ?_⟩
  have hb' : ∀ᶠ R : ℝ in atTop, ∀ᵐ x ∂ν, ‖F R x‖ ≤ H x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop L] with R hR hLR
    exact hb R hR hLR
  have ht : ∀ᵐ x ∂ν, Tendsto (fun R : ℝ ↦ F R x) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    simp [F, radialCutoff_jet_sub_zero_inside α hu
      ((norm_nonneg x).trans_lt hR) hR]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence H
      (Eventually.of_forall hFm) hb' hH ht

attribute [inherit_doc exteriorJetEnergy] exteriorJetEnergy.eq_1
attribute [inherit_doc radialCutoffJetError] radialCutoffJetError.eq_1

end SobolevSpace.Approximation
