/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.TailEnergy

/-!
# The nonlinear De Giorgi tail-energy estimate

The distance between two levels controls the higher superlevel measure by
the lower tail energy. Combining this with the PDE-derived Sobolev measure
gain yields a power strictly greater than one in the lower energy.

This estimate concerns `H¹` solutions of homogeneous scalar equations
with measurable uniformly elliptic coefficients. Neither a truncation
inequality nor extra regularity of the solution is an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped NNReal Sobolev ENNReal Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

private theorem tail_energy_le_power_of_measure_gain
    {q : ℝ≥0∞} (hq2 : 2 < q) (hqtop : q ≠ ∞) (C : ℝ) (hC : 0 ≤ C)
    (u : H¹(Ω)) (k h : ℝ) (hkh : k < h) (V : Set ℝ^n) (hV : MeasurableSet V)
    (ht : (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω) ≤
      C * (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω) *
        (domainMeasure n Ω).real (V ∩ {x | h < wkpBaseCoordinateCLM u x}) ^
          (1 - 2 / q.toReal)) :
    (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω) ≤
      C / (h - k) ^ (2 * (1 - 2 / q.toReal)) *
        (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω) ^
          (2 - 2 / q.toReal) := by
  let μ := domainMeasure n Ω
  let T : ℝ^n → ℝ := fun x ↦ max (wkpBaseCoordinateCLM u x - k) 0
  let I := ∫ x, T x ^ 2 ∂μ
  let E := V ∩ {x | h < wkpBaseCoordinateCLM u x}
  let δ := 1 - 2 / q.toReal
  have hqr : (2 : ℝ) < q.toReal := by
    exact_mod_cast (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hqtop).mpr hq2
  have hδ : 0 < δ := by
    dsimp only [δ]
    have := (div_lt_one (by linarith : 0 < q.toReal)).mpr hqr
    linarith
  have hT : MemLp T 2 μ := ((Lp.memLp (wkpBaseCoordinateCLM u)).sub
    (memLp_const k)).pos_part
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hE : MeasurableSet E :=
    hV.inter (measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable)
  have hmeasure : μ.real E ≤ I / (h - k) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hkh))).mpr
    calc
      μ.real E * (h - k) ^ 2 = ∫ _x in E, (h - k) ^ 2 ∂μ := by
        simp [smul_eq_mul]
      _ ≤ ∫ x in E, T x ^ 2 ∂μ := by
        apply setIntegral_mono_on (integrable_const _) hT.integrable_sq.integrableOn hE
        intro x hx
        apply pow_le_pow_left₀ (sub_pos.mpr hkh).le _ 2
        exact (sub_le_sub_right hx.2.le k).trans (le_max_left _ _)
      _ ≤ I := setIntegral_le_integral hT.integrable_sq
        (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  change (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂μ) ≤
    C * I * μ.real E ^ δ at ht
  calc
    _ ≤ C * I * (I / (h - k) ^ 2) ^ δ :=
      ht.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow measureReal_nonneg hmeasure hδ.le) (mul_nonneg hC hI))
    _ = _ := by
      have hd : ((h - k) ^ 2) ^ δ = (h - k) ^ (2 * δ) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast_mul (sub_pos.mpr hkh).le 2 δ).symm
      rw [Real.div_rpow hI (sq_nonneg _), hd]
      have hp : I ^ (2 - 2 / q.toReal) = I * I ^ δ := by
        rw [show 2 - 2 / q.toReal = 1 + δ by dsimp only [δ]; ring,
          Real.rpow_add_of_nonneg hI zero_le_one hδ.le, Real.rpow_one]
      rw [hp]
      dsimp only [δ]
      ring


/-- The higher tail energy is bounded by a power `2-2/q > 1` of the lower
tail energy. The level-gap factor is explicit. The constant is uniform in
both levels and in the weak solution. -/
theorem exists_superlevel_nonlinear_energy_le
    (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : H¹(Ω)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (k h : ℝ), k < h → ∀ V : Set ℝ^n, MeasurableSet V →
        (∀ x ∈ V, η.toFun x = 1) →
        (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω) ≤
          C / (h - k) ^ (2 * (1 - 2 / q.toReal)) *
            (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω) ^
              (2 - 2 / q.toReal) := by
  obtain ⟨C, hC, htail⟩ := exists_superlevel_tail_energy_le hΩb hq2.le hq a ha η hη
  refine ⟨C, hC, ?_⟩
  intro u hu k h hkh V hV hone
  exact tail_energy_le_power_of_measure_gain hq2 (hq.trans_lt ENNReal.coe_lt_top).ne
    C hC.le u k h hkh V hV (htail u hu k h hkh.le V hV hone)

/-- The nonlinear De Giorgi energy bound is uniform on all subdomains of
a fixed bounded open set. The inverse level-gap power and the square of the
cutoff derivative bound are explicit; the constant is independent of the
subdomain, coefficients within the stated bounds, solution, levels and cutoff. -/
theorem exists_uniform_superlevel_nonlinear_energy_le
    {W : Set ℝ^n} (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set ℝ^n) [Boundary.C1ExtensionAtlas n V], V ⊆ W →
      ∀ a : Fin n → Fin n → DerivLp n ∞ V,
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ u : H¹(V), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (k h : ℝ), k < h →
      ∀ (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport η.toFun ⊆ V →
      ∀ D : ℝ, 0 ≤ D → (∀ i, ‖partialTestFunctionLpTop (Ω := V) η i‖ ≤ D) →
      ∀ E : Set ℝ^n, MeasurableSet E → (∀ x ∈ E, η.toFun x = 1) →
        (∫ x in E, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n V) ≤
          C * D ^ 2 / (h - k) ^ (2 * (1 - 2 / q.toReal)) *
            (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n V) ^
              (2 - 2 / q.toReal) := by
  obtain ⟨C, hC, htail⟩ := exists_uniform_superlevel_tail_energy_le
    hWb hq2.le hq hα hΛ
  refine ⟨C, hC, ?_⟩
  intro V hV hVW a haΛ ha u hu k h hkh η hη D hD hηD E hE hone
  exact tail_energy_le_power_of_measure_gain hq2 (hq.trans_lt ENNReal.coe_lt_top).ne
    (C * D ^ 2) (mul_nonneg hC.le (sq_nonneg D)) u k h hkh E hE
      (htail V hVW a haΛ ha u hu k h hkh.le η hη D hD hηD E hE hone)

end SobolevSpace.GraphSpace
