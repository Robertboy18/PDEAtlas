/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Lipschitz
import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension

/-!
# Localizing elliptic coefficient matrices

A locally Lipschitz coefficient matrix on an open set can be replaced near any compact
subset by a globally bounded Lipschitz matrix with the same ellipticity constant.
The construction blends the matrix with a scalar identity using a smooth compact cutoff.
No symmetry or sign condition on individual entries is required.

The scalar Lipschitz extension theorem is used only to estimate cutoff products. Ellipticity
is preserved by the matrix blend itself, including where the cutoff vanishes.

For `W¹,∞` coefficients, compact Sobolev cutoff extension and the bounded weak-gradient
theorem construct the Lipschitz representatives as well. Thus the interior regularity
theorems can start from local Sobolev coefficient bundles without any extension hypothesis.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n : ℕ}

/-- Multiplication by a smooth compact cutoff turns a locally Lipschitz coefficient into a
globally Lipschitz function. No bound on the coefficient away from the cutoff is needed. -/
theorem exists_lipschitzWith_cutoff_mul
    {Ω : Set (ℝ^n)} (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω) (hηbound : ∀ x, ‖η.toFun x‖ ≤ 1)
    {f : ℝ^n → ℝ} (hf : LocallyLipschitzOn Ω f) :
    ∃ C : NNReal, LipschitzWith C (fun x ↦ η.toFun x * f x) := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    η.hasCompactSupport (hf.mono hηΩ)
  obtain ⟨g, hg, heq⟩ := hL.extend_real
  obtain ⟨M, hM⟩ := η.hasCompactSupport.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : NNReal := ⟨max M 0, le_max_right _ _⟩
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    η.hasCompactSupport η.contDiff (by simp)
  have hprod : (fun x ↦ η.toFun x * f x) = (fun x ↦ η.toFun x * g x) := by
    funext x
    by_cases hx : x ∈ tsupport η.toFun
    · rw [heq hx]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [hprod]
  have hbound (x y : ℝ^n) (hx : x ∈ tsupport η.toFun) :
      ‖η.toFun x * g x - η.toFun y * g y‖ ≤ (D * B + L : NNReal) * ‖x - y‖ := by
    have hgx : ‖g x‖ ≤ B := (hM x hx).trans (le_max_left _ _)
    calc
      ‖η.toFun x * g x - η.toFun y * g y‖ =
          ‖(η.toFun x - η.toFun y) * g x + η.toFun y * (g x - g y)‖ := by congr 1; ring
      _ ≤ ‖η.toFun x - η.toFun y‖ * ‖g x‖ + ‖η.toFun y‖ * ‖g x - g y‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ (D * ‖x - y‖) * B + 1 * (L * ‖x - y‖) :=
        add_le_add (mul_le_mul (hD.norm_sub_le x y) hgx (norm_nonneg _) (by positivity))
          (mul_le_mul (hηbound y) (hg.norm_sub_le x y) (norm_nonneg _) zero_le_one)
      _ = (D * B + L : NNReal) * ‖x - y‖ := by push_cast; ring
  refine ⟨D * B + L, lipschitzWith_iff_norm_sub_le.mpr fun x y ↦ ?_⟩
  by_cases hx : x ∈ tsupport η.toFun
  · exact hbound x y hx
  by_cases hy : y ∈ tsupport η.toFun
  · simpa only [norm_sub_rev] using hbound y x hy
  · simp only [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy,
      zero_mul, sub_self, norm_zero]
    positivity

/-- The interior of the set where a cutoff equals one is an open set on which the cutoff is one,
between a compact set near which it is one and a domain containing its support. -/
private theorem subset_interior_eq_one {Ω K : Set (ℝ^n)} (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω) (hηnhds : ∀ x ∈ K, η.toFun =ᶠ[nhds x] 1) :
    K ⊆ interior {x | η.toFun x = 1} ∧ interior {x | η.toFun x = 1} ⊆ Ω ∧
      ∀ x ∈ interior {x | η.toFun x = 1}, η.toFun x = 1 := by
  have hone (x : ℝ^n) (hx : x ∈ interior {x | η.toFun x = 1}) : η.toFun x = 1 :=
    (interior_subset hx : x ∈ {y | η.toFun y = 1})
  exact ⟨fun x hx ↦ mem_interior_iff_mem_nhds.mpr (hηnhds x hx), fun x hx ↦ hηΩ
    (subset_tsupport _ (by simp only [mem_support, hone x hx, ne_eq, one_ne_zero,
      not_false_eq_true])), hone⟩

/-- A locally Lipschitz, almost everywhere elliptic matrix has a bounded globally Lipschitz
elliptic extension agreeing with it on a neighborhood of any prescribed compact subset.
The extension keeps the original ellipticity constant. The original entries need not be
bounded on the domain. -/
theorem exists_global_elliptic_extension_of_compact
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, LocallyLipschitzOn Ω (a i j))
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : ∀ᵐ x ∂domainMeasure n Ω,
      MatrixEllipticLowerBound (fun i j ↦ a i j x) alpha)
    (K : Set (ℝ^n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ (B : Fin n → Fin n → DerivLp n ∞ univ)
        (b : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal),
        (∀ i j, LipschitzWith (C i j) (b i j)) ∧
        (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[volume] b i j) ∧
        AEUniformlyElliptic B alpha ∧
        (∀ i j, EqOn (b i j) (a i j) V) := by
  obtain ⟨η, hηΩ, _hηK, hηnhds, hηrange⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ hK hKΩ
  let d := scalarIdentityMatrix (n := n) alpha
  let q (i j : Fin n) (x : ℝ^n) := η.toFun x * (a i j x - d i j)
  have hηbound (x : ℝ^n) : ‖η.toFun x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hηrange x).1] using (hηrange x).2
  have hq (i j : Fin n) : ∃ C : NNReal, LipschitzWith C (q i j) :=
    exists_lipschitzWith_cutoff_mul η hηΩ hηbound
      ((ha i j).sub (LipschitzWith.const (d i j)).locallyLipschitz.locallyLipschitzOn)
  choose C hC using hq
  let b (i j : Fin n) (x : ℝ^n) := d i j + q i j x
  have hb (i j : Fin n) : LipschitzWith (C i j) (b i j) := by
    simpa only [zero_add] using (LipschitzWith.const (d i j)).add (hC i j)
  have hbLp (i j : Fin n) : MemLp (b i j) ∞ (domainMeasure n univ) :=
    (memLp_top_const (d i j)).add
      ((hC i j).continuous.memLp_top_of_hasCompactSupport
        η.hasCompactSupport.mul_right (domainMeasure n univ))
  let B (i j : Fin n) : DerivLp n ∞ univ := (hbLp i j).toLp (b i j)
  have hBrep (i j : Fin n) : (B i j : ℝ^n → ℝ) =ᵐ[volume] b i j := by
    simpa only [domainMeasure, Measure.restrict_univ] using (hbLp i j).coeFn_toLp
  have hbglue (x : ℝ^n) :
      (fun i j ↦ b i j x) =
        glueCoefficientField η.toFun alpha (fun y i j ↦ a i j y) x := by
    funext i j
    dsimp [b, q, d, glueCoefficientField, glueToScalarIdentity]
    ring
  have hB : AEUniformlyElliptic B alpha := by
    refine ⟨halpha, ?_⟩
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp hA,
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hBrep i)] with x hx hbx
    intro ξ
    have h := matrixEllipticLowerBound_glueCoefficientField
      η.toFun alpha alpha (fun y i j ↦ a i j y) x (hηrange x).1 (hηrange x).2
      le_rfl (fun hne ↦ hx (hηΩ (subset_tsupport η.toFun hne))) ξ
    rw [← hbglue] at h
    simp_rw [hbx]
    simpa only [dotProduct, principalEnergy, mul_right_comm] using h
  obtain ⟨hKV, hVΩ, hηone⟩ := subset_interior_eq_one η hηΩ hηnhds
  refine ⟨_, isOpen_interior, hKV, hVΩ, B, b, C, hb, hBrep, hB, fun i j x hx ↦ ?_⟩
  simp only [b, q, hηone x hx, one_mul, add_sub_cancel]

/-- A `W¹,∞` matrix on an open set has a bounded globally Lipschitz elliptic extension near
each compact subset. The Lipschitz representatives are constructed from the bounded weak
derivatives after compact cutoff extension. -/
theorem exists_global_elliptic_extension_of_w1Top
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    {alpha : ℝ}
    (hA : AEUniformlyElliptic
      (fun i j ↦ (A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) alpha)
    (K : Set (ℝ^n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ (B : Fin n → Fin n → DerivLp n ∞ univ)
        (b : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal),
        (∀ i j, LipschitzWith (C i j) (b i j)) ∧
        (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[volume] b i j) ∧
        AEUniformlyElliptic B alpha ∧
        (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n V] baseRepresentative (A i j)) := by
  obtain ⟨η, hηΩ, _hηK, hηnhds, hηrange⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ hK hKΩ
  let U (i j : Fin n) : W^{1,∞}((univ : Set (ℝ^n))) :=
    extendByCutoff hΩ (subset_univ Ω) η hηΩ (A i j)
  choose a ha haU using fun i j ↦ (U i j).exists_lipschitzWith_baseRepresentative
  have haeq (i j : Fin n) :
      a i j =ᵐ[volume] fun x ↦ η.toFun x * baseRepresentative (A i j) x :=
    (haU i j).trans (by simpa only [domainMeasure, Measure.restrict_univ] using
      extendByCutoff_base_ae hΩ (subset_univ Ω) η hηΩ (A i j))
  let d := scalarIdentityMatrix (n := n) alpha
  let q (i j : Fin n) (x : ℝ^n) := η.toFun x * d i j
  have hqcompact (i j : Fin n) : HasCompactSupport (q i j) := η.hasCompactSupport.mul_right
  have hq (i j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (q i j) := η.contDiff.mul contDiff_const
  choose D hD using fun i j ↦
    ContDiff.lipschitzWith_of_hasCompactSupport (hqcompact i j) (hq i j) (by simp)
  let b (i j : Fin n) (x : ℝ^n) := a i j x - q i j x + d i j
  have hb (i j : Fin n) : LipschitzWith
      ((∑ k : Fin n, ‖(U i j : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n k)‖₊) + D i j)
      (b i j) := by
    simpa only [add_zero] using ((ha i j).sub (hD i j)).add (LipschitzWith.const (d i j))
  have haLp (i j : Fin n) : MemLp (a i j) ∞ (domainMeasure n univ) :=
    (memLp_congr_ae (show a i j =ᵐ[domainMeasure n univ] baseRepresentative (U i j) by
      simpa only [domainMeasure, Measure.restrict_univ] using haU i j)).mpr
      (Lp.memLp ((U i j : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)))
  have hbLp (i j : Fin n) : MemLp (b i j) ∞ (domainMeasure n univ) :=
    ((haLp i j).sub ((hq i j).continuous.memLp_top_of_hasCompactSupport
      (hqcompact i j) (domainMeasure n univ))).add (memLp_top_const (d i j))
  let B (i j : Fin n) : DerivLp n ∞ univ := (hbLp i j).toLp (b i j)
  have hBrep (i j : Fin n) : (B i j : ℝ^n → ℝ) =ᵐ[volume] b i j := by
    simpa only [domainMeasure, Measure.restrict_univ] using (hbLp i j).coeFn_toLp
  have hBglue : ∀ᵐ x ∂volume, (fun i j ↦ B i j x) =
      glueCoefficientField η.toFun alpha (fun y i j ↦ baseRepresentative (A i j) y) x := by
    filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (haeq i),
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hBrep i)] with x hxa hxB
    funext i j
    rw [hxB i j]
    dsimp only [b]
    rw [hxa i j]
    dsimp [q, d, glueCoefficientField, glueToScalarIdentity]
    ring
  have hlocal : ∀ᵐ x ∂volume, x ∈ Ω →
      MatrixEllipticLowerBound (fun i j ↦ baseRepresentative (A i j) x) alpha := by
    refine (ae_restrict_iff' hΩ.measurableSet).mp (hA.2.mono fun x hx ξ ↦ ?_)
    simpa only [baseRepresentative, dotProduct, principalEnergy, mul_right_comm] using hx ξ
  have hB : AEUniformlyElliptic B alpha := by
    refine ⟨hA.1, ?_⟩
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [hBglue, hlocal] with x hxB hx
    intro ξ
    have h := matrixEllipticLowerBound_glueCoefficientField η.toFun alpha alpha
      (fun y i j ↦ baseRepresentative (A i j) y) x (hηrange x).1 (hηrange x).2
      le_rfl (fun hne ↦ hx (hηΩ (subset_tsupport η.toFun hne))) ξ
    rw [← hxB] at h
    simpa only [dotProduct, principalEnergy, mul_right_comm] using h
  obtain ⟨hKV, hVΩ, hηone⟩ := subset_interior_eq_one η hηΩ hηnhds
  refine ⟨_, isOpen_interior, hKV, hVΩ, B, b, _, hb, hBrep, hB, fun i j ↦ ?_⟩
  filter_upwards [ae_restrict_of_ae hBglue,
    ae_restrict_mem isOpen_interior.measurableSet] with x hxB hxV
  have h := congrFun (congrFun hxB i) j
  simpa only [glueCoefficientField, glueToScalarIdentity, hηone x hxV,
    one_mul, sub_self, zero_mul, add_zero] using h

end SobolevSpace.GraphSpace.BoundaryRegularity
