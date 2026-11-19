/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.Sobolev
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.Stampacchia
import PDE.Analysis.Variational.LaxMilgram

/-!
# Uniform boundedness for the scalar Dirichlet equation

Stampacchia's truncation argument bounds a zero-boundary weak solution
of `-div(A Du) = f` by a constant times `‖f‖∞`. The matrix is merely measurable,
bounded and uniformly elliptic. The constant depends on the domain, the
ellipticity lower bound and a Sobolev exponent, and is uniform in the matrix
and the solution. No boundedness of the solution is assumed.

The proof applies the derived superlevel Sobolev estimate to the solution and
its negative, then uses linearity to recover the precise dependence on the load.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

open Approximation.UpToBoundary PDE.Analysis.Variational

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A uniform `L∞` estimate for the scalar Dirichlet problem with
bounded forcing. The coefficient field needs no continuity. -/
theorem exists_norm_le_of_bounded_dirichlet_load
    (P : InwardPartition Ω) (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a : Fin n → Fin n → DerivLp n ∞ Ω, AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
        IsWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M) →
        ∀ᵐ x ∂domainMeasure n Ω, ‖baseCoordCLM u x‖ ≤ K * M := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  obtain ⟨C, hC, hSob⟩ := exists_superlevelH10_eLpNorm_le P hΩb hq2.le hq hα
  obtain ⟨K, hK, hStamp⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_upper_bound_of_superlevel_eLpNorm
      (μ := domainMeasure n Ω) hq2 (hq.trans_lt ENNReal.coe_lt_top).ne hC
  have hupper (a : Fin n → Fin n → DerivLp n ∞ Ω) (ha : AEUniformlyElliptic a α)
      (f : DerivLp n 2 Ω) (u : H¹₀(Ω)) (hu : IsWeakDivergenceSolution a f u)
      (hf : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ 1) :
      ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ≤ K := by
    apply hStamp
    intro k hk
    obtain ⟨hm, hb⟩ := hSob a ha f u hu.toInterior 1 zero_le_one hf k hk
    have he := superlevelH10_base_ae P u hk
    refine ⟨hm.ae_eq he, ?_⟩
    rw [← eLpNorm_congr_ae he]
    simpa only [mul_one] using hb
  have hunit (a : Fin n → Fin n → DerivLp n ∞ Ω) (ha : AEUniformlyElliptic a α)
      (f : DerivLp n 2 Ω) (u : H¹₀(Ω)) (hu : IsWeakDivergenceSolution a f u)
      (hf : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ 1) :
      ∀ᵐ x ∂domainMeasure n Ω, ‖baseCoordCLM u x‖ ≤ K := by
    have hnf : ∀ᵐ x ∂domainMeasure n Ω, ‖(-f) x‖ ≤ 1 := by
      filter_upwards [Lp.coeFn_neg f, hf] with x hx hb
      simpa only [hx, Pi.neg_apply, norm_neg] using hb
    have hneg := hupper a ha (-f) (-u) hu.neg hnf
    simp only [map_neg] at hneg
    filter_upwards [hupper a ha f u hu hf, hneg, Lp.coeFn_neg (baseCoordCLM u)]
      with x hp hm he
    rw [he, Pi.neg_apply] at hm
    exact Real.norm_eq_abs _ ▸ abs_le.mpr ⟨by linarith, hp⟩
  refine ⟨K, hK, fun a ha f u hu M hM hf ↦ ?_⟩
  have hpos (M' : ℝ) (hM' : 0 < M') (hf' : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M') :
      ∀ᵐ x ∂domainMeasure n Ω, ‖baseCoordCLM u x‖ ≤ K * M' := by
    have hscaled : ∀ᵐ x ∂domainMeasure n Ω, ‖(M'⁻¹ • f) x‖ ≤ 1 := by
      filter_upwards [Lp.coeFn_smul M'⁻¹ f, hf'] with x hx hb
      rw [hx, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM')]
      exact (inv_mul_le_iff₀ hM').2 (by rwa [mul_one])
    have hbound := hunit a ha (M'⁻¹ • f) (M'⁻¹ • u) (hu.smul M'⁻¹) hscaled
    simp only [map_smul] at hbound
    filter_upwards [hbound, Lp.coeFn_smul M'⁻¹ (baseCoordCLM u)] with x hx he
    rw [he, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM')] at hx
    exact ((inv_mul_le_iff₀ hM').1 hx).trans_eq (mul_comm _ _)
  filter_upwards [ae_all_iff.2 fun k : ℕ ↦ hpos (M + 1 / (k + 1)) (by positivity)
    (hf.mono fun x hx ↦ hx.trans (le_add_of_nonneg_right (by positivity)))] with x hx
  exact ge_of_tendsto' (by simpa using
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_add M).const_mul K) hx

end SobolevSpace.GraphSpace
