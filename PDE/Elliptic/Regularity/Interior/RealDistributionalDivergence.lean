/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart.FirstOrder
public import PDE.FDeriv.Operators
import PDE.Elliptic.Regularity.Interior.DistributionalDivergence

/-!
# Real first derivatives from a distributional divergence equation

Real L² data satisfying `Δu = div f` have an H¹ representative on
relatively compact open subsets of the testing domain. The input identity
uses real test functions and their Fréchet derivatives. Complexifying
the identity permits the Fourier Sobolev estimate; taking real parts then
recovers real weak derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace TemperedDistribution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal SchwartzMap Laplacian LineDeriv Distributions Sobolev

namespace PDE.Elliptic.Interior

variable {n : ℕ} {ι : Type*} [Fintype ι]

private theorem integral_laplacian_divergence_eq_of_real_tests
    {Ω : Opens (ℝ^n)} (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (f : ι → Lp ℝ 2 (volume : Measure (ℝ^n))) (v : ι → ℝ^n)
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) =
        -∑ i, ∫ x, f i x * fderiv ℝ (φ : ℝ^n → ℝ) x (v i))
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    (∫ x, (Δ φ) x * (u x : ℂ)) =
      -∑ i, ∫ x, (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x * (f i x : ℂ) := by
  have hcomponent (l : ℂ →L[ℝ] ℝ) :
      (∫ x, u x * l ((Δ φ) x)) =
        -∑ i, ∫ x, f i x * l ((∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x) := by
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
    have hderiv (i : ι) (x : ℝ^n) :
        fderiv ℝ (ψ : ℝ^n → ℝ) x (v i) =
          l ((∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x) := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact congrArg (fun L : (ℝ^n) →L[ℝ] ℝ ↦ L (v i))
        (l.hasFDerivAt.comp x φ.differentiableAt.hasFDerivAt).fderiv
    simpa only [hlap, hderiv] using hweak ψ
  have hL : Integrable (fun x ↦ (Δ φ) x * (u x : ℂ)) volume :=
    ((Δ φ).memLp 2 volume).integrable_mul (Lp.memLp u).ofReal
  have hR (i : ι) :
      Integrable (fun x ↦ (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x * (f i x : ℂ)) volume :=
    ((∂_{v i} φ).memLp 2 volume).integrable_mul (Lp.memLp (f i)).ofReal
  apply Complex.ext
  · change Complex.reCLM (∫ x, (Δ φ) x * (u x : ℂ)) =
      Complex.reCLM (-∑ i, ∫ x, (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x * (f i x : ℂ))
    simp only [map_neg, map_sum, ← Complex.reCLM.integral_comp_comm hL,
      ← Complex.reCLM.integral_comp_comm (hR _)]
    simpa [Complex.mul_re, mul_comm] using hcomponent Complex.reCLM
  · change Complex.imCLM (∫ x, (Δ φ) x * (u x : ℂ)) =
      Complex.imCLM (-∑ i, ∫ x, (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x * (f i x : ℂ))
    simp only [map_neg, map_sum, ← Complex.imCLM.integral_comp_comm hL,
      ← Complex.imCLM.integral_comp_comm (hR _)]
    simpa [Complex.mul_im, mul_comm] using hcomponent Complex.imCLM

/-- An L² function whose Laplacian is the divergence of finitely many L²
fields has an H¹ representative on every relatively compact open set.
The directions are arbitrary and no first derivative of the state is assumed. -/
theorem exists_wkpSpaceOn_one_ae_eq_of_integral_laplacian_divergence_eq
    {Ω : Opens (ℝ^n)} (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (f : ι → Lp ℝ 2 (volume : Measure (ℝ^n))) (v : ι → ℝ^n)
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) =
        -∑ i, ∫ x, f i x * fderiv ℝ (φ : ℝ^n → ℝ) x (v i))
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{1,2}(V),
      baseRepresentative U =ᵐ[volume.restrict V] u := by
  let uC : Lp ℂ 2 (volume : Measure (ℝ^n)) := Complex.ofRealCLM.compLpL 2 volume u
  let fC (i : ι) : Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    Complex.ofRealCLM.compLpL 2 volume (f i)
  have huC : (uC : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (u x : ℂ) :=
    Complex.ofRealCLM.coeFn_compLpL u
  have hfC (i : ι) : (fC i : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (f i x : ℂ) :=
    Complex.ofRealCLM.coeFn_compLpL (f i)
  have hC (φ : 𝓢(ℝ^n, ℂ)) (hφ : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
      (∫ x, (Δ φ) x • uC x) =
        -∑ i, ∫ x, (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x • fC i x := by
    calc
      _ = ∫ x, (Δ φ) x * (u x : ℂ) := integral_congr_ae
        (huC.mono fun _ hx ↦ by simp only [hx, smul_eq_mul])
      _ = -∑ i, ∫ x, (∂_{v i} φ : 𝓢(ℝ^n, ℂ)) x * (f i x : ℂ) :=
        integral_laplacian_divergence_eq_of_real_tests u f v hweak φ hφ hφΩ
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact integral_congr_ae ((hfC i).mono fun _ hx ↦ by simp only [hx, smul_eq_mul])
  obtain ⟨W, _, hclW, _, z, hz, hzu⟩ :=
    exists_memSobolev_one_ae_eq_near_compact_of_lp_divergence_eq
      Ω.isOpen uC fC v hC (closure V) hcompact hVΩ
  obtain ⟨R, hR⟩ := SobolevSpace.Fractional.exists_wkpSpaceOn_one_re_of_memSobolev z hz
  refine ⟨restrictCLM hV.measurableSet (subset_univ V) R, ?_⟩
  have hbase := restrictCLM_apply_ae hV.measurableSet (subset_univ V) R (baseIndex n 1)
  have hreal : (fun x ↦ (z x).re) =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (show V ⊆ W from subset_closure.trans hclW) hzu,
      ae_restrict_of_ae huC] with x hx hxC
    simpa using congrArg Complex.re (hx.trans hxC)
  have hRlocal := ae_restrict_of_ae (s := V) hR
  change _ =ᵐ[volume.restrict V] _ at hbase
  filter_upwards [hbase, hRlocal, hreal] with x hx₁ hx₂ hx₃
  exact hx₁.trans (hx₂.trans hx₃)

end PDE.Elliptic.Interior
