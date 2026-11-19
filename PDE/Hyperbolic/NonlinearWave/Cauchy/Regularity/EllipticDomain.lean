/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.SpatialTests
public import PDE.Spaces.Sobolev.Fractional.Integer.Complexification
public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart
public import PDE.DistributionTheory.TemperedDistribution.Sobolev

/-!
# The whole-space H² domain of the weak Laplacian

An H¹ function whose weak Laplacian is represented in L² belongs to H².
Schwartz testing identifies the complexified distributional Laplacian.
The whole-space Bessel regularity theorem supplies two Sobolev orders;
uniqueness of weak derivatives identifies the resulting real bundle.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace TemperedDistribution
open scoped Sobolev SobolevSpace.WholeSpaceHilbert SchwartzMap Laplacian InnerProductSpace

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ}

/-- An L² variational Laplacian satisfies the distributional equation against
all real Schwartz tests. -/
theorem integral_laplacian_eq_of_gradientForm_eq (u : H¹(ℝ^n)) (g : DerivLp n 2 univ)
    (h : gradientForm n u = -(energyTriple n).pivotToDual g) (φ : 𝓢(ℝ^n, ℝ)) :
    (∫ x, (energyTriple n).inclusion u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, g x * φ x := by
  let w := lowerOrderCLM (by decide : 1 ≤ 2) (φ.toWkpSpace 2)
  have hw : (energyTriple n).inclusion w =ᵐ[volume] φ := by
    change (φ.toWkpSpace 2).val (baseIndex n 2) =ᵐ[volume] φ
    simpa only [baseIndex_toList, iteratedPartialDeriv] using
      φ.toWkpSpace_coordinate_ae (baseIndex n 2)
  have heq := congrArg (fun q : StrongDual ℝ H¹(ℝ^n) ↦ q w) h
  rw [gradientForm_schwartz, neg_apply,
    PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply, L2.inner_def] at heq
  apply neg_injective
  refine heq.trans (congrArg Neg.neg ?_)
  simp only [domainMeasure, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The variational Laplacian agrees with the complex distributional Laplacian.
This identity is independent of the Sobolev order used for subsequent regularity. -/
theorem laplacian_complexifyL2_inclusion (u : H¹(ℝ^n)) (g : DerivLp n 2 univ)
    (h : gradientForm n u = -(energyTriple n).pivotToDual g) :
    Δ (Fractional.complexifyL2CLM n ((energyTriple n).inclusion u) : 𝓢'(ℝ^n, ℂ)) =
      (Fractional.complexifyL2CLM n g : 𝓢'(ℝ^n, ℂ)) := by
  let z := Fractional.complexifyL2CLM n ((energyTriple n).inclusion u)
  let b := Fractional.complexifyL2CLM n g
  have hz := Fractional.complexifyL2CLM_ae ((energyTriple n).inclusion u)
  have hb := Fractional.complexifyL2CLM_ae g
  ext φ
  rw [TemperedDistribution.laplacian_apply_apply,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  have hcomponent (l : ℂ →L[ℝ] ℝ) : (∫ x, (energyTriple n).inclusion u x * l ((Δ φ) x)) =
        ∫ x, g x * l (φ x) := by
    have hφ := integral_laplacian_eq_of_gradientForm_eq u g h (φ.postcompCLM l)
    have hlap (x : ℝ^n) :
        laplacian (φ.postcompCLM l : ℝ^n → ℝ) x = l ((Δ φ) x) := by
      change laplacian (l ∘ (φ : ℝ^n → ℂ)) x = l ((Δ φ) x)
      rw [SchwartzMap.laplacian_apply]
      exact ((l.contDiff.comp (φ.smooth 2)).contDiffAt).coordinate_laplacian_eq_laplacian
        |>.trans ((φ.contDiffAt 2).laplacian_CLM_comp_left)
    simpa only [hlap, SchwartzMap.postcompCLM_apply] using hφ
  have hL : Integrable (fun x ↦ (Δ φ) x * z x) volume :=
    ((Δ φ).memLp 2 volume).integrable_mul (Lp.memLp z)
  have hR : Integrable (fun x ↦ φ x * b x) volume := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  have hreal (l : ℂ →L[ℝ] ℝ) :
      l (∫ x, (Δ φ) x * z x) = l (∫ x, φ x * b x) := by
    rw [← l.integral_comp_comm hL, ← l.integral_comp_comm hR]
    calc
      _ = ∫ x, (energyTriple n).inclusion u x * l ((Δ φ) x) := by
        apply integral_congr_ae
        filter_upwards [hz] with x hx
        rw [hx, mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul]
      _ = ∫ x, g x * l (φ x) := hcomponent l
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hb] with x hx
        rw [hx, mul_comm (φ x), ← Complex.real_smul, map_smul, smul_eq_mul]
  exact Complex.ext (hreal Complex.reCLM) (hreal Complex.imCLM)

/-- The full weak Laplacian domain on whole-space H¹ is H². Both the second
derivatives and their L² trace are obtained from the variational equation. -/
theorem exists_h2_of_gradientForm_eq
    (u : H¹(ℝ^n)) (g : DerivLp n 2 univ)
    (h : gradientForm n u = -(energyTriple n).pivotToDual g) :
    ∃ U : W^{2,2}(ℝ^n), lowerOrderCLM (by decide : 1 ≤ 2) U = u ∧ Δ U = g := by
  let z := Fractional.complexifyL2CLM n ((energyTriple n).inclusion u)
  let b := Fractional.complexifyL2CLM n g
  have hz := Fractional.complexifyL2CLM_ae ((energyTriple n).inclusion u)
  have hΔ := laplacian_complexifyL2_inclusion u g h
  have htwo : MemSobolev 2 2 (z : 𝓢'(ℝ^n, ℂ)) := by
    have hz0 : MemSobolev 0 2 (z : 𝓢'(ℝ^n, ℂ)) := memSobolev_zero_iff.mpr ⟨z, rfl⟩
    simpa only [zero_add] using hz0.add_two_of_laplacian (memSobolev_zero_iff.mpr ⟨b, hΔ⟩)
  obtain ⟨U, hU⟩ := Fractional.exists_wkpSpaceOn_two_re_of_memSobolev z htwo
  have hlow : lowerOrderCLM (by decide : 1 ≤ 2) U = u := by
    apply (energyTriple n).injective
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [hU, hz] with x hx hy using hx.trans (congrArg Complex.re hy)
  refine ⟨U, hlow, ?_⟩
  apply (energyTriple n).pivotToDual_injective
  ext w
  have heq := congrArg (fun q : StrongDual ℝ H¹(ℝ^n) ↦ q w) h
  rw [← hlow, gradientForm_h2, neg_apply,
    PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply] at heq
  exact neg_injective heq

end PDE.Hyperbolic.NonlinearWave.Cauchy
