/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
public import PDE.Analysis.MeasureTheory.Lp.FiniteTimeFamily
public import PDE.Hyperbolic.WeakWave.Coefficients.IntegrationByParts
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak

/-!
# Compact coefficient fields and their Sobolev realizations

Joint continuity on a compact cylinder gives continuity in the `L∞` norm. Classical
spatial derivatives identify the rows of the Sobolev graph space. Both facts
apply to arbitrary representatives of the coefficient classes.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Continuous classical time derivatives of a matrix field give a bounded, norm
continuous derivative of its `L∞` matrix curve and absolute continuity of that curve. -/
theorem exists_principal_derivative_of_continuousOn_compact (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (A Adot : ℝ → Fin n → Fin n → ℝ^n → ℝ) (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hA : ∀ i j, ContinuousOn (fun p ↦ A p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAdot : ∀ i j, ContinuousOn (fun p ↦ Adot p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAderiv : ∀ i j, ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ A s i j x) (Adot t i j x) (Icc a b) t)
    (hArep : ∀ t ∈ Icc a b, ∀ i j, (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A t i j) :
    ∃ (coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) (N : ℝ≥0),
      ContinuousOn coeffDot (Icc a b) ∧
      (∀ t ∈ Icc a b, ‖coeffDot t‖ ≤ N) ∧
      AbsolutelyContinuousOnInterval coeff a b ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt coeff (coeffDot t) t := by
  have hμK : ∀ᵐ x ∂domainMeasure n Ω, x ∈ closure Ω :=
    (ae_restrict_mem hΩ.measurableSet).mono fun x hx ↦ subset_closure hx
  obtain ⟨D, N, hDcont, hDbound, hLip, hderiv⟩ :=
    exists_lp_top_family_derivative_of_representatives hΩbounded.isCompact_closure
      hμK (fun ij : Fin n × Fin n ↦ fun t ↦ A t ij.1 ij.2)
      (fun ij : Fin n × Fin n ↦ fun t ↦ Adot t ij.1 ij.2) (fun t ij ↦ coeff t ij.1 ij.2)
      (fun ij ↦ hA ij.1 ij.2) (fun ij ↦ hAdot ij.1 ij.2)
      (fun ij ↦ hAderiv ij.1 ij.2) (fun ij t ht ↦ hArep t ht ij.1 ij.2)
  let coeffDot (t : ℝ) (i j : Fin n) := D t (i, j)
  have hcoeffLip : LipschitzOnWith N coeff (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr fun i ↦ ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr fun j ↦ ?_
    exact (norm_le_pi_norm ((fun ij ↦ coeff s ij.1 ij.2) -
      (fun ij ↦ coeff t ij.1 ij.2)) (i, j)).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul s hs t ht)
  refine ⟨coeffDot, N, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ (continuousOn_pi.mp hDcont) (i, j)
  · exact fun t ht ↦ (pi_norm_le_iff_of_nonneg N.coe_nonneg).mpr fun i ↦
      (pi_norm_le_iff_of_nonneg N.coe_nonneg).mpr fun j ↦
        (norm_le_pi_norm (D t) (i, j)).trans (hDbound t ht)
  · exact (show LipschitzOnWith N coeff (uIcc a b) by
      simpa only [uIcc_of_le hab.le] using hcoeffLip).absolutelyContinuousOnInterval
  · rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd : HasDerivWithinAt coeff (coeffDot t) (Icc a b) t :=
      hasDerivWithinAt_pi.mpr fun i ↦ hasDerivWithinAt_pi.mpr fun j ↦
        (hasDerivWithinAt_pi.mp (hderiv t ⟨ht.1.le, ht.2.le⟩)) (i, j)
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Classical first derivatives on the open domain identify an `L∞` coefficient and
its derivative classes with an element of the Sobolev graph space. -/
theorem exists_w1Top_of_classical_derivatives (hΩ : IsOpen Ω) (F : DerivLp n ∞ Ω)
    (D : Fin n → DerivLp n ∞ Ω) (f : ℝ^n → ℝ) (d : Fin n → ℝ^n → ℝ)
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
    (hD : ∀ i, (D i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] d i) (hf : ∀ x ∈ Ω, ContDiffAt ℝ 1 f x)
    (hd : ∀ i, ∀ x ∈ Ω, d i x = (∂[i] f) x) :
    ∃ U : W^{1,∞}(Ω), (U : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) = F ∧ ∀ i,
      (U : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = D i := by
  let U : WkpAmbientOn n 1 ∞ Ω := WithLp.toLp ∞ (firstOrderRows F D)
  have hbase : U (baseIndex n 1) = F := firstOrderRows_baseIndex F D
  have hderiv (i : Fin n) : U (singleDerivIndex n i) = D i := firstOrderRows_singleDerivIndex F D i
  have hU : IsWkpOn U := by
    intro r
    rcases r.eq_baseIndex_or_eq_singleDerivIndex with hr | ⟨i, hr⟩
    · subst r
      rw [hbase, baseIndex_toList]
      exact hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain (Lp.memLp F) le_top)
    · subst r
      rw [hbase, hderiv, singleDerivIndex_toList]
      have hd' : (D i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (∂[i] f) := by
        filter_upwards [hD i, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
        exact hx.trans (hd i x hxΩ)
      exact (hasWeakDerivativeOn_congr_ae hF hd').2 (hasWeakDerivativeOn_of_contDiffAt_one hΩ hf i)
  exact ⟨⟨U, hU⟩, hbase, hderiv⟩

/-- Continuous drift and potential fields, with continuous classical spatial drift
derivatives, give the `L² × H¹₀` estimate uniformly in time. The constant is constructed
from compactness, and the direction of the estimate follows from integration by parts. -/
theorem exists_lowerOrder_bound_base_left_of_continuousOn_compact (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (B : ℝ → Fin n → ℝ^n → ℝ)
    (DB : ℝ → Fin n → Fin n → ℝ^n → ℝ) (C : ℝ → ℝ^n → ℝ)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hB : ∀ i, ContinuousOn (fun p ↦ B p.1 i p.2) (Icc a b ×ˢ closure Ω))
    (hDB : ∀ i j, ContinuousOn (fun p ↦ DB p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hC : ContinuousOn (Function.uncurry C) (Icc a b ×ˢ closure Ω))
    (hBdiff : ∀ t ∈ Icc a b, ∀ i, ∀ x ∈ Ω, ContDiffAt ℝ 1 (B t i) x)
    (hDBderiv : ∀ t ∈ Icc a b, ∀ i j, ∀ x ∈ Ω, DB t i j x = (∂[j] (B t i)) x)
    (hBrep : ∀ t ∈ Icc a b, ∀ i, ((z t).1 i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] B t i)
    (hCrep : ∀ t ∈ Icc a b, ((z t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] C t) :
    ContinuousOn z (Icc a b) ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ u v : H¹₀(Ω), |lowerOrderForm
      (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2) u v| ≤ L * ‖baseCoordCLM u‖ * ‖v‖ := by
  classical
  have hK := hΩbounded.isCompact_closure
  have hμK : ∀ᵐ x ∂domainMeasure n Ω, x ∈ closure Ω :=
    (ae_restrict_mem hΩ.measurableSet).mono fun x hx ↦ subset_closure hx
  have hz : ContinuousOn z (Icc a b) := (continuousOn_pi.mpr fun i ↦
      MeasureTheory.continuousOn_lp_top_of_continuousOn_compact hK hμK (fun t ↦ B t i)
        (fun t ↦ (z t).1 i) (hB i) (fun t ht ↦ hBrep t ht i)).prodMk
      (MeasureTheory.continuousOn_lp_top_of_continuousOn_compact hK hμK C
        (fun t ↦ (z t).2) hC hCrep)
  obtain ⟨Z₀, hZ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  let Z := max Z₀ 0
  have hZ : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z := fun t ht ↦ (hZ₀ t ht).trans (le_max_left _ _)
  choose D M hD using fun ij : Fin n × Fin n ↦ exists_lp_top_curve_of_continuousOn_compact hK hμK
      (fun t ↦ DB t ij.1 ij.2) (hDB ij.1 ij.2)
  let Q : ℝ := ∑ ij, (M ij : ℝ)
  have hM (ij : Fin n × Fin n) : (M ij : ℝ) ≤ Q :=
    Finset.single_le_sum (fun k _ ↦ (M k).coe_nonneg) (Finset.mem_univ ij)
  refine ⟨hz, (n : ℝ) * (Z + Q) + Z, by dsimp [Z, Q]; positivity, fun t ht u v ↦ ?_⟩
  choose U hUbase hUderiv using fun i : Fin n ↦
    exists_w1Top_of_classical_derivatives hΩ ((z t).1 i) (fun j ↦ D (i, j) t)
      (B t i) (fun j ↦ DB t i j) (hBrep t ht i)
      (fun j ↦ (hD (i, j) t ht).1) (hBdiff t ht i) (hDBderiv t ht i)
  have hbound := abs_lowerOrderForm_le_base_left hΩ U (z t).2 u v
  simp only [hUbase, hUderiv] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ (∑ _i : Fin n, (Z + Q)) + Z := add_le_add (Finset.sum_le_sum fun i _ ↦
        add_le_add (((norm_le_pi_norm (z t).1 i).trans (norm_fst_le (z t))).trans
          (hZ t ht)) ((hD (i, i) t ht).2.trans (hM (i, i)))) ((norm_snd_le (z t)).trans (hZ t ht))
    _ = _ := by simp [mul_add]

end SobolevSpace.GraphSpace
