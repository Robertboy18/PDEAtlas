/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension

/-!
# The Laplacian of a localized Sobolev function

The cutoff extension has Laplacian χf + 2∇χ·∇u + (Δχ)u when the local
Sobolev Laplacian is f. A second cutoff η equal to one on the support of χ
allows the first derivative term to be bounded using η∇u. The estimate keeps
the sum defining f together, rather than bounding its diagonal terms separately.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped ENNReal Distributions Sobolev

namespace PDE.Elliptic.Interior

variable {n : ℕ} {V : Set (ℝ^n)}

/-- A bounded smooth multiplier acts on an L² class through its pointwise
product. This local helper also applies to derivatives of the cutoff. -/
private theorem test_smul_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : DerivLp n 2 V) :
    ((testFunctionLpTop (Ω := V) ψ • u : DerivLp n 2 V) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n V]
      fun x ↦ ψ x * u x := by
  filter_upwards [mulLpLeft_apply_ae (testFunctionLpTop (Ω := V) ψ) u,
    testFunctionLpTop_apply_ae (Ω := V) ψ] with x hx hψ
  simpa only [mulLpLeft_apply, hψ, _root_.TestFunction.toFun_eq_coe] using hx

/-- The pointwise second partial derivative, retained as a compact smooth test
so the L∞ multiplier construction supplies its integrability. -/
private def secondTest (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) where
  toFun := (∂[i] (∂[i] ψ.toFun))
  contDiff' := by simpa only [iteratedPartialDeriv, _root_.TestFunction.toFun_eq_coe] using
    contDiff_top_iteratedPartialDeriv ψ.contDiff [i, i]
  hasCompactSupport' := by simpa only [iteratedPartialDeriv] using
    iteratedPartialDeriv_hasCompactSupport ψ [i, i]
  tsupport_subset' := subset_univ _

/-- Localization bounds the whole-space Laplacian by the forcing and the
localized first derivatives. The constants A and B bound first and diagonal
second derivatives of χ. Neither boundary data nor regularity of ∂V is used. -/
theorem norm_laplacian_extendByCutoff_le
    (hV : IsOpen V) (U : W^{2,2}(V)) (F : DerivLp n 2 V)
    (hΔ : (∑ i : Fin n, (U : WkpAmbientOn n 2 2 V) (topPureDerivIndex n 2 i)) = F)
    (χ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχV : tsupport χ.toFun ⊆ V)
    (hη : ∀ x ∈ tsupport χ.toFun, η x = 1)
    {A B : ℝ}
    (hχ : ∀ x, |χ x| ≤ 1)
    (hfirst : ∀ (i : Fin n) x, |(∂[i] χ.toFun) x| ≤ A)
    (hsecond : ∀ (i : Fin n) x,
      |(∂[i] (∂[i] χ.toFun)) x| ≤ B) :
    ‖∑ i : Fin n, (extendByCutoff hV (subset_univ V) χ hχV U :
        WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 i)‖ ≤
      ‖F‖ + 2 * A * (∑ i : Fin n, ‖testFunctionLpTop (Ω := V) η •
        (U : WkpAmbientOn n 2 2 V) (firstDerivIndex n 2 (by norm_num) i)‖) +
          n * B * ‖(U : WkpAmbientOn n 2 2 V) (baseIndex n 2)‖ := by
  classical
  let u₀ : DerivLp n 2 V := (U : WkpAmbientOn n 2 2 V) (baseIndex n 2)
  let u₁ (i : Fin n) : DerivLp n 2 V :=
    (U : WkpAmbientOn n 2 2 V) (firstDerivIndex n 2 (by norm_num) i)
  let u₂ (i : Fin n) : DerivLp n 2 V :=
    (U : WkpAmbientOn n 2 2 V) (topPureDerivIndex n 2 i)
  let b (i : Fin n) : DerivLp n 2 V := partialTestFunctionLpTop (Ω := V) χ i • u₁ i
  let c (i : Fin n) : DerivLp n 2 V := testFunctionLpTop (Ω := V) (secondTest χ i) • u₀
  let S : DerivLp n 2 V := testFunctionLpTop (Ω := V) χ • F +
    ∑ i : Fin n, ((2 : ℝ) • b i + c i)
  let W : W^{2,2}((univ : Set (ℝ^n))) := extendByCutoff hV (subset_univ V) χ hχV U
  let T : DerivLp n 2 univ :=
    ∑ i : Fin n, (W : WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 i)
  let R (x : ℝ^n) : ℝ := ∑ i : Fin n,
    weakLeibnizExpansion χ.toFun (wkpWordRepresentative U) [i, i] x
  have hR (x : ℝ^n) : R x =
      χ x * (∑ i : Fin n, (u₂ i : ℝ^n → ℝ) x) +
        ∑ i : Fin n, (2 * (∂[i] χ.toFun) x * u₁ i x +
          (∂[i] (∂[i] χ.toFun)) x * u₀ x) := by
    simp only [R, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [weakLeibnizExpansion, TestFunction.toFun_eq_coe, wkpWordRepresentative,
      derivativeSplits, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      iteratedPartialDeriv, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Std.le_refl, ↓reduceDIte, Nat.one_le_ofNat, zero_le, derivIndexOfList_nil, List.sum_cons,
      List.sum_nil, add_zero, topPureDerivIndex, pureDerivIndex, List.reduceReplicate,
      firstDerivIndex, add_right_inj, u₂, u₁, u₀]
    ring
  have hTs : (T : ℝ^n → ℝ) =ᵐ[volume] R := by
    have hcoord (i : Fin n) :
        ((W : WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 i) : ℝ^n → ℝ)
          =ᵐ[volume] weakLeibnizExpansion χ.toFun (wkpWordRepresentative U) [i, i] := by
      simpa [domainMeasure, topPureDerivIndex_toList] using
        extendByCutoff_coordinate_ae hV (subset_univ V) χ hχV U (topPureDerivIndex n 2 i)
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ
      (fun i ↦ (W : WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 i))
    simp only [domainMeasure, Measure.restrict_univ] at hsum
    filter_upwards [hsum, ae_all_iff.mpr hcoord] with x hx hi
    exact hx.trans (Finset.sum_congr rfl fun i _ ↦ hi i)
  have hb (i : Fin n) : (b i : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
      fun x ↦ (∂[i] χ.toFun) x * u₁ i x := by
    filter_upwards [mulLpLeft_apply_ae (partialTestFunctionLpTop (Ω := V) χ i) (u₁ i),
      partialTestFunctionLpTop_apply_ae (Ω := V) χ i] with x hx hd
    simpa only [b, mulLpLeft_apply, hd, iteratedPartialDeriv] using hx
  have hc (i : Fin n) : (c i : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
      fun x ↦ (∂[i] (∂[i] χ.toFun)) x * u₀ x :=
    test_smul_ae (secondTest χ i) u₀
  have hbc (i : Fin n) : (((2 : ℝ) • b i + c i : DerivLp n 2 V) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n V] fun x ↦
        2 * (∂[i] χ.toFun) x * u₁ i x +
          (∂[i] (∂[i] χ.toFun)) x * u₀ x := by
    filter_upwards [Lp.coeFn_add ((2 : ℝ) • b i) (c i), Lp.coeFn_smul (2 : ℝ) (b i),
      hb i, hc i] with x ha hs hb hc
    rw [ha, Pi.add_apply, hs, Pi.smul_apply, hb, hc]
    simp only [smul_eq_mul, mul_assoc]
  have hSs : (S : ℝ^n → ℝ) =ᵐ[domainMeasure n V] R := by
    have hsumU : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
        fun x ↦ ∑ i : Fin n, (u₂ i : ℝ^n → ℝ) x := by
      rw [← hΔ]
      exact Lp.coeFn_fun_finsetSum Finset.univ u₂
    filter_upwards [Lp.coeFn_add (testFunctionLpTop (Ω := V) χ • F)
        (∑ i : Fin n, ((2 : ℝ) • b i + c i)), test_smul_ae χ F,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (2 : ℝ) • b i + c i),
      ae_all_iff.mpr hbc, hsumU] with x ha hχf hsum hi hF
    rw [ha, Pi.add_apply, hχf, hsum, hF, hR]
    exact congrArg (fun r ↦ χ x * (∑ i : Fin n, (u₂ i : ℝ^n → ℝ) x) + r)
      (Finset.sum_congr rfl fun i _ ↦ hi i)
  have hsupp : Function.support R ⊆ V := fun x hx ↦ by_contra fun hxV ↦ hx <|
    Finset.sum_eq_zero fun i _ ↦ by_contra fun hi ↦
      hxV (hχV (weakLeibnizExpansion_support U χ [i, i] hi))
  have hnorm : ‖T‖ = ‖S‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    simp only [domainMeasure, Measure.restrict_univ] at hTs ⊢
    rw [eLpNorm_congr_ae hTs, eLpNorm_congr_ae hSs]
    exact congrArg ENNReal.toReal
      (eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 2)
        ((Lp.stronglyMeasurable T).aestronglyMeasurable.congr hTs) hsupp).symm
  have hbnorm (i : Fin n) : ‖b i‖ ≤ A * ‖testFunctionLpTop (Ω := V) η • u₁ i‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hb i, test_smul_ae η (u₁ i)] with x hb hηu
    rw [hb, hηu]
    by_cases hx : x ∈ tsupport χ.toFun
    · rw [hη x hx, one_mul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hfirst i x) (abs_nonneg _)
    · rw [show (∂[i] χ.toFun) x = 0 from image_eq_zero_of_notMem_tsupport fun hd ↦
        hx (tsupport_iteratedPartialDeriv_subset_tsupport [i] χ.toFun hd), zero_mul, norm_zero]
      have hA : 0 ≤ A := (abs_nonneg _).trans (hfirst i x)
      positivity
  have hcnorm (i : Fin n) : ‖c i‖ ≤ B * ‖u₀‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hc i] with x hx
    rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hsecond i x) (abs_nonneg _)
  have hf : ‖testFunctionLpTop (Ω := V) χ • F‖ ≤ ‖F‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [test_smul_ae χ F] with x hx
    rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ x) (abs_nonneg (F x))
  calc
    ‖T‖ = ‖S‖ := hnorm
    _ ≤ ‖testFunctionLpTop (Ω := V) χ • F‖ + ∑ i : Fin n, ‖(2 : ℝ) • b i + c i‖ :=
      (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ ‖F‖ + ∑ i : Fin n,
        (2 * A * ‖testFunctionLpTop (Ω := V) η • u₁ i‖ + B * ‖u₀‖) := by
      refine add_le_add hf (Finset.sum_le_sum fun i _ ↦ (norm_add_le _ _).trans ?_)
      rw [norm_smul, Real.norm_two, mul_assoc]
      gcongr
      exacts [hbnorm i, hcnorm i]
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, u₀, u₁,
      add_assoc]

end PDE.Elliptic.Interior
