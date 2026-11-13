/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart
public import PDE.FDeriv.Operators
import PDE.Elliptic.Regularity.Interior.DistributionalPoisson

/-!
# Real W²,² regularity for distributional Poisson solutions

If real functions `u` and `f` are locally L² and `Δu = f` in distributions,
then `u` has a real W²,² representative on each relatively compact open
subset of the domain. The equation is stated against real test functions.

Real and imaginary parts of a complex test function give the complexified
equation. The local Bessel regularity theorem derives H² without an assumed
weak gradient. Taking the real part of its representative and restricting
the resulting weak-derivative bundle gives the real Sobolev conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace TemperedDistribution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal SchwartzMap Laplacian Distributions Sobolev

namespace PDE.Elliptic.Interior

variable {n : ℕ}

/-- A compact test factor makes locally L² data integrable after complexification.
Only the L² norm on the test factor's support is used. -/
private theorem integrable_schwartz_mul_of_locally_memLp
    {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}
    (hu : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun x ↦ φ x * (u x : ℂ)) volume := by
  have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    isFiniteMeasure_restrict.mpr hφ.measure_lt_top.ne
  have huK : IntegrableOn (fun x ↦ (u x : ℂ)) (tsupport φ) volume :=
    ((hu _ hφ hφΩ).ofReal).integrable (by norm_num)
  have hprod : IntegrableOn (fun x ↦ φ x * (u x : ℂ)) (tsupport φ) volume :=
    huK.continuousOn_mul φ.continuous.continuousOn hφ
  apply hprod.integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- Testing against the real and imaginary components gives the complex
Poisson equation. The Laplacian commutes with each projection because the
test function is smooth. -/
private theorem integral_laplacian_eq_of_real_tests
    {Ω : Opens (ℝ^n)} {u f : ℝ^n → ℝ}
    (hu : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (hf : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, f x * φ x)
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    (∫ x, (Δ φ) x • (u x : ℂ)) = ∫ x, φ x • (f x : ℂ) := by
  have hcomponent (l : ℂ →L[ℝ] ℝ) :
      (∫ x, u x * l ((Δ φ) x)) = ∫ x, f x * l (φ x) := by
    let ψ : 𝓓(Ω, ℝ) := {
      toFun := l ∘ φ
      contDiff' := l.contDiff.comp (φ.smooth ⊤)
      hasCompactSupport' := hφ.comp_left (g := l) (map_zero l)
      tsupport_subset' := by
        apply Subset.trans ?_ hφΩ
        apply closure_minimal ?_ (isClosed_tsupport (φ : ℝ^n → ℂ))
        intro x hx
        apply subset_tsupport φ
        intro hx0
        apply hx
        change l (φ x) = 0
        simp [hx0]
    }
    have hlap (x : ℝ^n) :
        laplacian (ψ : ℝ^n → ℝ) x = l ((Δ φ : 𝓢(ℝ^n, ℂ)) x) := by
      change laplacian (l ∘ (φ : ℝ^n → ℂ)) x = l ((Δ φ : 𝓢(ℝ^n, ℂ)) x)
      rw [SchwartzMap.laplacian_apply]
      exact ((l.contDiff.comp (φ.smooth 2)).contDiffAt).coordinate_laplacian_eq_laplacian.trans
        (φ.contDiffAt 2).laplacian_CLM_comp_left
    have h := hweak ψ
    change (∫ x, u x * laplacian (ψ : ℝ^n → ℝ) x) = ∫ x, f x * l (φ x) at h
    simpa only [hlap] using h
  have hΔ : HasCompactSupport (Δ φ : 𝓢(ℝ^n, ℂ)) :=
    hφ.of_isClosed_subset (isClosed_tsupport (Δ φ : 𝓢(ℝ^n, ℂ)))
      (SchwartzMap.tsupport_laplacian_subset φ)
  have hL := integrable_schwartz_mul_of_locally_memLp hu (Δ φ) hΔ
    ((SchwartzMap.tsupport_laplacian_subset φ).trans hφΩ)
  have hR := integrable_schwartz_mul_of_locally_memLp hf φ hφ hφΩ
  simp only [smul_eq_mul]
  apply Complex.ext
  · change Complex.reCLM (∫ x, (Δ φ) x * (u x : ℂ)) =
      Complex.reCLM (∫ x, φ x * (f x : ℂ))
    rw [← Complex.reCLM.integral_comp_comm hL, ← Complex.reCLM.integral_comp_comm hR]
    simpa [Complex.mul_re, mul_comm] using hcomponent Complex.reCLM
  · change Complex.imCLM (∫ x, (Δ φ) x * (u x : ℂ)) =
      Complex.imCLM (∫ x, φ x * (f x : ℂ))
    rw [← Complex.imCLM.integral_comp_comm hL, ← Complex.imCLM.integral_comp_comm hR]
    simpa [Complex.mul_im, mul_comm] using hcomponent Complex.imCLM

/-- Real locally L² Poisson data give a W²,² representative on every open set
whose closure is compact and contained in the domain. The first and second
weak derivatives are derived from the distributional equation. No boundary
condition, boundary regularity, or initial Sobolev membership is assumed. -/
theorem exists_wkpSpaceOn_two_ae_eq_of_integral_laplacian_eq
    {Ω : Opens (ℝ^n)} {u f : ℝ^n → ℝ}
    (hu : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (hf : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, f x * φ x)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{2,2}(V),
      (((U : WkpAmbientOn n 2 2 V) (baseIndex n 2) :
        DerivLp n 2 V) : ℝ^n → ℝ) =ᵐ[volume.restrict V] u := by
  obtain ⟨W, _, hclW, _, z, hz, hzu⟩ :=
    exists_memSobolev_two_ae_eq_near_compact_of_integral_laplacian_eq
      (u := fun x ↦ (u x : ℂ)) (f := fun x ↦ (f x : ℂ)) Ω.isOpen
      (fun K hK hKΩ ↦ (hu K hK hKΩ).ofReal)
      (fun K hK hKΩ ↦ (hf K hK hKΩ).ofReal)
      (integral_laplacian_eq_of_real_tests hu hf hweak)
      (closure V) hcompact hVΩ
  obtain ⟨R, hR⟩ := SobolevSpace.Fractional.exists_wkpSpaceOn_two_re_of_memSobolev z hz
  refine ⟨restrictCLM hV.measurableSet (subset_univ V) R, ?_⟩
  have hbase := restrictCLM_apply_ae hV.measurableSet (subset_univ V) R (baseIndex n 2)
  have hreal : (fun x ↦ (z x).re) =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (show V ⊆ W from subset_closure.trans hclW) hzu] with x hx
    simpa using congrArg Complex.re hx
  have hRlocal := ae_restrict_of_ae (s := V) hR
  change _ =ᵐ[volume.restrict V] _ at hbase
  filter_upwards [hbase, hRlocal, hreal] with x hx₁ hx₂ hx₃
  exact hx₁.trans (hx₂.trans hx₃)

end PDE.Elliptic.Interior
