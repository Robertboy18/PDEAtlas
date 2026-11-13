/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.SobolevGain
import PDE.Elliptic.Regularity.Interior.DeGiorgi.MeasureGain

/-!
# Tail-energy decay for weak elliptic solutions

For a homogeneous weak divergence-form solution, the `L²` energy above
a higher level on an interior set is bounded by the lower-level energy times
a positive power of the higher superlevel measure. The proof applies the
Sobolev estimate to the cutoff of the lower truncation and Hölder's inequality
on the support of the higher truncation.

The coefficients are measurable and uniformly elliptic. All representatives,
truncations and tests come from the Sobolev and weak-equation APIs.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped NNReal Sobolev ENNReal Distributions

namespace SobolevSpace.GraphSpace

open PDE.Elliptic.Regularity.DeGiorgi

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

private theorem superlevel_base_ae (u : H¹(Ω)) (k : ℝ) :
    (wkpBaseCoordinateCLM (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
      (u - wkpConstant k)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ max (wkpBaseCoordinateCLM u x - k) 0 := by
  have hbase :
      (wkpBaseCoordinateCLM (u - wkpConstant k) : ℝ^n → ℝ) =ᵐ[
        domainMeasure n Ω] fun x ↦ wkpBaseCoordinateCLM u x - k := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (wkpBaseCoordinateCLM u)
      (wkpBaseCoordinateCLM (wkpConstant k)),
      wkpConstant_base_ae (n := n) (p := 2) (Ω := Ω) k] with x hx hk
    exact hx.trans (congrArg (wkpBaseCoordinateCLM u x - ·) hk)
  exact (lipschitzCompositionOn_base_ae hΩ.isOpen Lp.lipschitzWith_pos_part
    (u - wkpConstant k)).trans (hbase.fun_comp (fun s ↦ max s 0))

private theorem tail_energy_le_of_cutoff_bound
    {q : ℝ≥0∞} (hq2 : 2 ≤ q) (u : H¹(Ω)) (k h : ℝ) (hkh : k ≤ h)
    (V : Set ℝ^n) (hV : MeasurableSet V)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (hone : ∀ x ∈ V, η.toFun x = 1) (C : ℝ)
    (hv : MemLp (baseRepresentative (cutoffH1ToH10 hΩ.isOpen η hη
      (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
        (u - wkpConstant k)) : H¹(Ω))) q (domainMeasure n Ω))
    (hbound : (eLpNorm (baseRepresentative (cutoffH1ToH10 hΩ.isOpen η hη
      (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
        (u - wkpConstant k)) : H¹(Ω))) q (domainMeasure n Ω)).toReal ^ 2 ≤
      C * ‖wkpBaseCoordinateCLM (lipschitzCompositionOn hΩ.isOpen
        Lp.lipschitzWith_pos_part (u - wkpConstant k))‖ ^ 2) :
    (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω) ≤
      C * (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω) *
        (domainMeasure n Ω).real (V ∩ {x | h < wkpBaseCoordinateCLM u x}) ^
          (1 - 2 / q.toReal) := by
  classical
  let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
    (u - wkpConstant k)
  let v := cutoffH1ToH10 hΩ.isOpen η hη T
  let w : ℝ^n → ℝ := V.indicator (fun x ↦ max (wkpBaseCoordinateCLM u x - h) 0)
  let E := V ∩ {x | h < wkpBaseCoordinateCLM u x}
  have hE : MeasurableSet E :=
    hV.inter (measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable)
  have hT := superlevel_base_ae u k
  have hTh := superlevel_base_ae u h
  have hw : MemLp w 2 (domainMeasure n Ω) :=
    ((Lp.memLp _).ae_eq hTh).indicator hV.nullMeasurableSet
  have hvrep : baseRepresentative (v : H¹(Ω)) =ᵐ[domainMeasure n Ω]
      fun x ↦ η.toFun x * max (wkpBaseCoordinateCLM u x - k) 0 := by
    filter_upwards [cutoffCLM_base_apply_ae η T, hT] with x hx htx
    exact hx.trans (congrArg (η.toFun x * ·) htx)
  have hsupport : ∀ᵐ x ∂domainMeasure n Ω, x ∉ E → w x = 0 := .of_forall fun x hx ↦ by
    by_cases hxV : x ∈ V
    · simp only [w, indicator_of_mem hxV, max_eq_right (sub_nonpos.mpr
        (le_of_not_gt fun hh : h < wkpBaseCoordinateCLM u x ↦ hx ⟨hxV, hh⟩))]
    · exact indicator_of_notMem hxV _
  have hdom : ∀ᵐ x ∂domainMeasure n Ω,
      ‖w x‖ ≤ ‖baseRepresentative (v : H¹(Ω)) x‖ := by
    filter_upwards [hvrep] with x hx
    by_cases hxV : x ∈ V
    · rw [show w x = max (wkpBaseCoordinateCLM u x - h) 0 from indicator_of_mem hxV _,
        hx, hone x hxV, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_max_right _ 0), abs_of_nonneg (le_max_right _ 0)]
      exact max_le_max (sub_le_sub_left hkh _) le_rfl
    · rw [show w x = 0 from indicator_of_notMem hxV _, norm_zero]
      exact norm_nonneg _
  have htail := integral_sq_le_eLpNorm_sq_mul_measure hq2 hE hw hv hsupport hdom
  have henergy : ‖wkpBaseCoordinateCLM T‖ ^ 2 =
      ∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω := by
    rw [Lp.norm_sq_eq_integral_sq]
    exact integral_congr_ae (hT.fun_comp (fun s ↦ s ^ 2))
  have hwint : (∫ x, w x ^ 2 ∂domainMeasure n Ω) =
      ∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω := by
    rw [← integral_indicator hV]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ V <;> simp [w, hx]
  rw [hwint] at htail
  rw [henergy] at hbound
  exact htail.trans (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg measureReal_nonneg _))


/-- The higher superlevel has a measure gain in its interior `L²` energy.
For `q > 2` the exponent is positive. The constant is chosen before the weak
solution and both levels. No essential bound on the solution is assumed. -/
theorem exists_superlevel_tail_energy_le
    (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : H¹(Ω)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (k h : ℝ), k ≤ h → ∀ V : Set ℝ^n, MeasurableSet V →
        (∀ x ∈ V, η.toFun x = 1) →
        (∫ x in V, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n Ω) ≤
          C * (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n Ω) *
            (domainMeasure n Ω).real (V ∩ {x | h < wkpBaseCoordinateCLM u x}) ^
              (1 - 2 / q.toReal) := by
  classical
  obtain ⟨S, hS, hSob⟩ := exists_superlevel_cutoff_sobolev_sq_le hΩb hq2 hq
  let A := 8 * (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 +
    2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C := S ^ 2 * A / α ^ 2 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu k h hkh V hV hone
  let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
    (u - wkpConstant k)
  let v := cutoffH1ToH10 hΩ.isOpen η hη T
  have hzero : ∀ᵐ x ∂domainMeasure n Ω, ‖(0 : DerivLp n 2 Ω) x‖ ≤ (0 : ℝ) :=
    (Lp.coeFn_zero ℝ 2 _).mono fun x hx ↦ by rw [hx, Pi.zero_apply, norm_zero]
  obtain ⟨hv, hs⟩ := hSob a α ha 0 u hu 0 le_rfl hzero k η hη
  have hbound : (eLpNorm (baseRepresentative (v : H¹(Ω)))
      q (domainMeasure n Ω)).toReal ^ 2 ≤ C * ‖wkpBaseCoordinateCLM T‖ ^ 2 := by
    change α ^ 2 *
      (eLpNorm (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω)).toReal ^ 2 ≤
      S ^ 2 * (A * ‖wkpBaseCoordinateCLM T‖ ^ 2 + _) at hs
    simp only [mul_zero, zero_mul, add_zero] at hs
    have hα : 0 < α ^ 2 := sq_pos_of_pos ha.1
    calc
      _ ≤ S ^ 2 * (A * ‖wkpBaseCoordinateCLM T‖ ^ 2) / α ^ 2 := by
        apply (le_div_iff₀ hα).mpr
        rw [mul_comm]
        exact hs
      _ = (S ^ 2 * A / α ^ 2) * ‖wkpBaseCoordinateCLM T‖ ^ 2 := by ring
      _ ≤ C * ‖wkpBaseCoordinateCLM T‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)
  exact tail_energy_le_of_cutoff_bound hq2 u k h hkh V hV η hη hone C hv hbound

/-- The tail-energy measure gain is uniform over all subdomains of a fixed
bounded open set, all coefficients with the given ellipticity and size bounds,
and all cutoffs with derivative norm at most `D`. The factor `D²` is explicit. -/
theorem exists_uniform_superlevel_tail_energy_le
    {W : Set ℝ^n} (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set ℝ^n) [Boundary.C1ExtensionAtlas n V], V ⊆ W →
      ∀ a : Fin n → Fin n → DerivLp n ∞ V,
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ u : H¹(V), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (k h : ℝ), k ≤ h →
      ∀ (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport η.toFun ⊆ V →
      ∀ D : ℝ, 0 ≤ D → (∀ i, ‖partialTestFunctionLpTop (Ω := V) η i‖ ≤ D) →
      ∀ E : Set ℝ^n, MeasurableSet E → (∀ x ∈ E, η.toFun x = 1) →
        (∫ x in E, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 ∂domainMeasure n V) ≤
          C * D ^ 2 *
            (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂domainMeasure n V) *
              (domainMeasure n V).real (E ∩ {x | h < wkpBaseCoordinateCLM u x}) ^
                (1 - 2 / q.toReal) := by
  obtain ⟨S, hS, hSob⟩ := exists_uniform_superlevel_cutoff_sobolev_sq_le hWb hq2 hq
  let B := 8 * ((n : ℝ) * n * Λ) ^ 2 + 2 * α ^ 2 * n
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C := S ^ 2 * B / α ^ 2 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro V hV hVW a haΛ ha u hu k h hkh η hη D hD hηD E hE hone
  let T := lipschitzCompositionOn hV.isOpen Lp.lipschitzWith_pos_part
    (u - wkpConstant k)
  let v := cutoffH1ToH10 hV.isOpen η hη T
  have hzero : ∀ᵐ x ∂domainMeasure n V, ‖(0 : DerivLp n 2 V) x‖ ≤ (0 : ℝ) :=
    (Lp.coeFn_zero ℝ 2 _).mono fun x hx ↦ by rw [hx, Pi.zero_apply, norm_zero]
  obtain ⟨hv, hs⟩ := hSob V hVW a α ha 0 u hu 0 le_rfl hzero k η hη
  let A := 8 * (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := V) η i‖) ^ 2 +
    2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := V) η i‖ ^ 2
  have hsum : (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := V) η i‖) ≤
      ((n : ℝ) * n * Λ) * D :=
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      mul_le_mul (haΛ i j) (hηD i) (norm_nonneg _) hΛ).trans_eq
        (by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring)
  have hsq : (∑ i, ‖partialTestFunctionLpTop (Ω := V) η i‖ ^ 2) ≤
      (n : ℝ) * D ^ 2 :=
    (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hηD i) 2).trans_eq (by simp)
  have hA : A ≤ B * D ^ 2 := by
    have hb := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsum 2
    have hd := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * α ^ 2)
    dsimp only [A, B]
    nlinarith only [hb, hd]
  have hbound : (eLpNorm (baseRepresentative (v : H¹(V)))
      q (domainMeasure n V)).toReal ^ 2 ≤ (C * D ^ 2) * ‖wkpBaseCoordinateCLM T‖ ^ 2 := by
    change α ^ 2 *
      (eLpNorm (baseRepresentative (v : H¹(V))) q (domainMeasure n V)).toReal ^ 2 ≤
        S ^ 2 * (A * ‖wkpBaseCoordinateCLM T‖ ^ 2 + _) at hs
    simp only [mul_zero, zero_mul, add_zero] at hs
    have hs' := hs.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (sq_nonneg S))
    calc
      _ ≤ S ^ 2 * (B * D ^ 2 * ‖wkpBaseCoordinateCLM T‖ ^ 2) / α ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
        rw [mul_comm]
        exact hs'
      _ = (S ^ 2 * B / α ^ 2) * D ^ 2 * ‖wkpBaseCoordinateCLM T‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg D))
        (sq_nonneg _)
  exact tail_energy_le_of_cutoff_bound hq2 u k h hkh E hE η hη hone (C * D ^ 2) hv hbound

end SobolevSpace.GraphSpace
