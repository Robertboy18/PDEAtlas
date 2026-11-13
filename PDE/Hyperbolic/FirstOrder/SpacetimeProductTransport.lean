/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeProductPairing
import PDE.Analysis.MeasureTheory.Lp.MultiplierRepresentative

/-!
# The transport pairing on the product measure

For each component, integration by parts puts the spatial derivative on the test
and on the coefficient. Their scalar integrands are respectively
`u_q C_jpq ∂_j Φ_p` and `u_q B_jpq Φ_p`. Here `C` and `B` are joint representatives
of the coefficient's base and indicated weak derivative rows.

Base continuity in spatial L∞ on Icc and a uniform weak-derivative bound give
Bochner L² membership of the multiplied tests. The product-integral pairing theorem
then proves integrability and identifies the finite sum with `transportTestFunctional`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)
local notation "σ" => domainMeasure n univ

/-- Product-space integration of the transport term equals the weak transport
pairing, with both the differentiated-test and differentiated-coefficient contributions.
The joint coefficient representatives need only agree almost everywhere with the
Sobolev rows. Base continuity on Icc and a uniform bound on the indicated weak derivative give
integrability. -/
theorem integral_spacetime_transport_pairing
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, ContinuousOn (fun t ↦
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → H} (hu : MemLp u 2 ν) (U : Fin m → ℝ × ℝ^n → ℝ)
    (hU : ∀ p, AEStronglyMeasurable (U p) ((ν).prod σ))
    (hUsec : ∀ p, ∀ᵐ t ∂ν, (fun x ↦ U p (t, x)) =ᵐ[σ] (u t p : ℝ^n → ℝ))
    (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ)
    (hC : ∀ j p q, AEStronglyMeasurable (C j p q) ((ν).prod σ))
    (hB : ∀ j p q, AEStronglyMeasurable (B j p q) ((ν).prod σ))
    (hCsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ C j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ))
    (hBsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ B j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ))
    (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :
    Integrable (fun z ↦ ∑ p, ∑ j, ∑ q, U q z *
      (C j p q z *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) z +
          B j p q z * Φ p z)) ((ν).prod σ) ∧
      (∫ z, ∑ p, ∑ j, ∑ q, U q z *
        (C j p q z *
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) z +
            B j p q z * Φ p z) ∂(ν).prod σ) =
        ∫ t, transportTestFunctional (A t) (spacetimeTestH1Slice Φ t) (u t) ∂ν := by
  classical
  let v (d : DerivIndex n 1) (p : Fin m) (t : ℝ) : D :=
    wkpCoordinateCLM d (spacetimeTestH1Slice Φ t p)
  have hv (d : DerivIndex n 1) (p : Fin m) : MemLp (v d p) 2 ν := by
    have hφ : MemLp (spacetimeTestH1Slice Φ) 2 ν :=
      memLp_restrict_Ioc_of_continuousOn (continuous_spacetimeTestH1Slice Φ).continuousOn
    simpa only [v, Function.comp_def, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      using ((wkpCoordinateCLM d).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)).comp_memLp' hφ
  have huq (q : Fin m) : MemLp (fun t ↦ u t q) 2 ν := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) q).comp_memLp' hu
  let c (j : Fin n) (p q : Fin m) (t : ℝ) := (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let d (j : Fin n) (p q : Fin m) (t : ℝ) :=
    (A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)
  have hcv (j : Fin n) (p q : Fin m) : MemLp
      (fun t ↦ c j p q t • v (singleDerivIndex n j) p t) 2 ν :=
    memLp_coefficientBase_mul hab (fun t ↦ A t j p q) (hA j p q) (hv (singleDerivIndex n j) p)
  have hdv (j : Fin n) (p q : Fin m) : MemLp (fun t ↦ d j p q t • v (baseIndex n 1) p t) 2 ν :=
    memLp_coefficientDerivative_mul hab (fun t ↦ A t j p q) (hA j p q) j L
      (fun t ht ↦ hL t ht j p q) (hv (baseIndex n 1) p)
  let R (p : Fin m) (j : Fin n) (q : Fin m) (z : ℝ × ℝ^n) : ℝ := U q z * (C j p q z *
      (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) z +
        B j p q z * Φ p z)
  let S (p : Fin m) (j : Fin n) (q : Fin m) (t : ℝ) : ℝ :=
    inner ℝ (u t q) (c j p q t • v (singleDerivIndex n j) p t + d j p q t • v (baseIndex n 1) p t)
  have hint {w : ℝ → D} (hw : MemLp w 2 ν) (q : Fin m) : Integrable (fun t ↦ ⟪u t q, w t⟫_ℝ) ν :=
    memLp_one_iff_integrable.1 ((innerSL ℝ (E := D)).memLp_of_bilin 1 (huq q) hw)
  have hS (p : Fin m) (j : Fin n) (q : Fin m) : Integrable (S p j q) ν :=
    hint ((hcv j p q).add (hdv j p q)) q
  have hrow (p : Fin m) (j : Fin n) (q : Fin m) : Integrable (R p j q) ((ν).prod σ) ∧
        (∫ z, R p j q z ∂(ν).prod σ) = ∫ t, S p j q t ∂ν := by
    have hbase := integral_mul_prod_eq_integral_L2_inner_multiplier
      (huq q) (hcv j p q) (hC j p q) (hU q)
      (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ))
        (Φ p)).continuous.aestronglyMeasurable (hCsec j p q) (hUsec q)
      (Eventually.of_forall fun t ↦ by
        simpa only [v, firstOrderRows_singleDerivIndex] using
          (spacetimeTestH1Slice_coordinate_ae Φ t p (singleDerivIndex n j)).symm)
    have hderiv := integral_mul_prod_eq_integral_L2_inner_multiplier
      (huq q) (hdv j p q) (hB j p q) (hU q)
      (Φ p).continuous.aestronglyMeasurable (hBsec j p q) (hUsec q)
      (Eventually.of_forall fun t ↦ by
        simpa only [v, firstOrderRows_baseIndex] using
          (spacetimeTestH1Slice_coordinate_ae Φ t p (baseIndex n 1)).symm)
    refine ⟨(hbase.1.add hderiv.1).congr (.of_forall fun z ↦ by simp only [Pi.add_apply, R,
      mul_add]), ?_⟩
    simp only [R, mul_add, S, inner_add_right]
    rw [integral_add hbase.1 hderiv.1, integral_add (hint (hcv j p q) q) (hint (hdv j p q) q),
      hbase.2, hderiv.2]
  -- Finite sums of rows with integrable sides and equal integrals have the same property.
  have hsum {ι : Type} (s : Finset ι) (f : ι → ℝ × ℝ^n → ℝ) (g : ι → ℝ → ℝ)
      (h : ∀ i ∈ s, Integrable (f i) ((ν).prod σ) ∧ Integrable (g i) ν ∧
        ∫ z, f i z ∂(ν).prod σ = ∫ t, g i t ∂ν) :
      Integrable (fun z ↦ ∑ i ∈ s, f i z) ((ν).prod σ) ∧ Integrable (fun t ↦ ∑ i ∈ s, g i t) ν ∧
        ∫ z, ∑ i ∈ s, f i z ∂(ν).prod σ = ∫ t, ∑ i ∈ s, g i t ∂ν := by
    refine ⟨integrable_finsetSum s fun i hi ↦ (h i hi).1,
      integrable_finsetSum s fun i hi ↦ (h i hi).2.1, ?_⟩
    rw [integral_finsetSum s fun i hi ↦ (h i hi).1, integral_finsetSum s fun i hi ↦ (h i hi).2.1]
    exact Finset.sum_congr rfl fun i hi ↦ (h i hi).2.2
  have hall := hsum Finset.univ (fun p z ↦ ∑ j, ∑ q, R p j q z) (fun p t ↦ ∑ j, ∑ q, S p j q t)
    fun p _ ↦ hsum _ _ _ fun j _ ↦ hsum _ _ _ fun q _ ↦ ⟨(hrow p j q).1, hS p j q, (hrow p j q).2⟩
  exact ⟨hall.1, hall.2.2.trans (integral_congr_ae (.of_forall fun t ↦ by
    simp only [transportTestFunctional_apply, S, c, d, v]))⟩

end PDE.Hyperbolic.FirstOrder
