/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolventAdjoint
public import PDE.Analysis.Distribution.Schwartz.Density
public import PDE.Analysis.Calculus.Laplacian.Regularity

/-!
# Square-integrable solutions of `Δ²u - Δu = 0`

The operator `Δ² - Δ` has Fourier symbol `(4π²|ξ|²)² + 4π²|ξ|²`, which vanishes only at the
origin. If a real `L²` function annihilates `(Δ² - Δ) χ` for every smooth compactly supported
`χ`, the pairing is continuous on Schwartz space and vanishes on its dense subspace of compactly
supported functions, hence on all of it. Testing with inverse transforms of smooth compactly
supported functions shows that the symbol times the transform vanishes almost everywhere, so
the function is zero.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SchwartzMap LineDeriv Laplacian Set Filter Topology
open scoped ENNReal NNReal SchwartzMap ContDiff

namespace HeatEquation.WholeSpace

variable {n : ℕ}



theorem ae_ne_zero_euclidean (hn : 0 < n) : ∀ᵐ ξ ∂(volume : Measure (ℝ^n)), ξ ≠ 0 := by
  have : Nontrivial (ℝ^n) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, 0, ?_⟩⟩
    intro h
    have := congrArg (fun v : ℝ^n ↦ v ⟨0, hn⟩) h
    simp at this
  have hs : volume ({0} : Set (ℝ^n)) = 0 := measure_singleton 0
  rw [ae_iff]
  simp [hs]

/-- The operator `Δ² - Δ` on complex Schwartz functions. -/
def schwartzBiharmonicSubLaplacian (n : ℕ) : 𝓢(ℝ^n, ℂ) →L[ℂ] 𝓢(ℝ^n, ℂ) :=
  (laplacianCLM ℂ (ℝ^n) 𝓢(ℝ^n, ℂ)).comp (laplacianCLM ℂ (ℝ^n) 𝓢(ℝ^n, ℂ)) -
    laplacianCLM ℂ (ℝ^n) 𝓢(ℝ^n, ℂ)

theorem fourier_schwartzBiharmonicSubLaplacian_apply (χ : 𝓢(ℝ^n, ℂ)) (ξ : ℝ^n) :
    𝓕 (schwartzBiharmonicSubLaplacian n χ) ξ =
      (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * 𝓕 χ ξ := by
  simp only [schwartzBiharmonicSubLaplacian, sub_apply,
    ContinuousLinearMap.comp_apply, laplacianCLM_eq]
  rw [← fourierTransformCLM_apply ℂ, map_sub]
  simp only [fourierTransformCLM_apply, sub_apply, fourier_laplacian_apply]
  push_cast
  ring

/-- A real square-integrable function annihilated by `Δ² - Δ` against all smooth compactly
supported tests vanishes. -/
theorem ae_eq_zero_of_integral_mul_biharmonic_sub_laplacian (hn : 0 < n) {u : ℝ^n → ℝ}
    (hu : MemLp u 2 volume)
    (h : ∀ χ : ℝ^n → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ x, u x * (Δ (Δ χ) x - Δ χ x) = 0) :
    u =ᵐ[volume] 0 := by
  have hmc : MemLp (fun x ↦ (u x : ℂ)) 2 (volume : Measure (ℝ^n)) := hu.ofReal
  set uc : Lp ℂ 2 (volume : Measure (ℝ^n)) := hmc.toLp (fun x ↦ (u x : ℂ)) with huc
  have hcoe : (uc : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (u x : ℂ) := hmc.coeFn_toLp
  set L : 𝓢(ℝ^n, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    (toLpCLM ℂ ℂ 2 volume).comp (schwartzBiharmonicSubLaplacian n)
  set Λ : 𝓢(ℝ^n, ℂ) → ℂ := fun χ ↦ inner ℂ (L χ) uc
  have hΛc : Continuous Λ := (L.continuous).inner continuous_const
  -- real tests
  have hreal : ∀ (g : ℝ^n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ G : 𝓢(ℝ^n, ℂ), (∀ x, G x = (g x : ℂ)) → Λ G = 0 := by
    intro g hg hgc G hG
    have hGfun : (G : ℝ^n → ℂ) = Complex.ofRealCLM ∘ g := funext hG
    have hΔg : ContDiff ℝ ∞ (Δ g) := hg.laplacian (by simp)
    have hΔG (x : ℝ^n) : (Δ G) x = ((Δ g x : ℝ) : ℂ) := by
      rw [SchwartzMap.laplacian_apply, hGfun]
      exact (hg.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
    have hΔΔG (x : ℝ^n) : (Δ (Δ G)) x = ((Δ (Δ g) x : ℝ) : ℂ) := by
      rw [SchwartzMap.laplacian_apply,
        show ((Δ G : 𝓢(ℝ^n, ℂ)) : ℝ^n → ℂ) = Complex.ofRealCLM ∘ (Δ g) from funext hΔG]
      exact (hΔg.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
    have hB (x : ℝ^n) : schwartzBiharmonicSubLaplacian n G x =
        ((Δ (Δ g) x - Δ g x : ℝ) : ℂ) := by
      simp only [schwartzBiharmonicSubLaplacian, sub_apply, ContinuousLinearMap.comp_apply,
        laplacianCLM_eq, hΔΔG, hΔG]
      push_cast
      ring
    simp only [Λ, L, ContinuousLinearMap.comp_apply, toLpCLM_apply, L2.inner_def]
    have hint : ∫ x, inner ℂ ((schwartzBiharmonicSubLaplacian n G).toLp 2 volume x) (uc x) =
        ((∫ x, u x * (Δ (Δ g) x - Δ g x) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [(schwartzBiharmonicSubLaplacian n G).coeFn_toLp 2 (volume : Measure (ℝ^n)),
        hcoe] with x h1 h2
      rw [h1, h2, RCLike.inner_apply', hB, Complex.conj_ofReal]
      push_cast
      ring
    rw [hint, h g hg hgc, Complex.ofReal_zero]
  -- compactly supported complex tests
  have hcs : ∀ χ : 𝓢(ℝ^n, ℂ), HasCompactSupport (χ : ℝ^n → ℂ) → Λ χ = 0 := by
    intro χ hχ
    have hre_sm : ContDiff ℝ ∞ (fun x ↦ (χ x).re) := Complex.reCLM.contDiff.comp (χ.smooth ⊤)
    have him_sm : ContDiff ℝ ∞ (fun x ↦ (χ x).im) := Complex.imCLM.contDiff.comp (χ.smooth ⊤)
    have hre_cs : HasCompactSupport (fun x ↦ (χ x).re) :=
      hχ.comp_left (g := Complex.re) (by simp)
    have him_cs : HasCompactSupport (fun x ↦ (χ x).im) :=
      hχ.comp_left (g := Complex.im) (by simp)
    have hre_c : HasCompactSupport (fun x ↦ (((χ x).re : ℝ) : ℂ)) :=
      hre_cs.comp_left (g := Complex.ofRealCLM) (by simp)
    have him_c : HasCompactSupport (fun x ↦ (((χ x).im : ℝ) : ℂ)) :=
      him_cs.comp_left (g := Complex.ofRealCLM) (by simp)
    set Gre : 𝓢(ℝ^n, ℂ) := hre_c.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hre_sm)
    set Gim : 𝓢(ℝ^n, ℂ) := him_c.toSchwartzMap (Complex.ofRealCLM.contDiff.comp him_sm)
    have hsplit : χ = Gre + Complex.I • Gim := by
      ext x
      simp only [add_apply, smul_apply, smul_eq_mul]
      change χ x = (((χ x).re : ℝ) : ℂ) + Complex.I * (((χ x).im : ℝ) : ℂ)
      rw [mul_comm]
      exact (Complex.re_add_im (χ x)).symm
    have h1 := hreal _ hre_sm hre_cs Gre (fun x ↦ rfl)
    have h2 := hreal _ him_sm him_cs Gim (fun x ↦ rfl)
    simp only [Λ] at h1 h2 ⊢
    rw [hsplit, map_add, map_smul, inner_add_left, inner_smul_left, h1, h2]
    simp
  have hall : Λ = fun _ ↦ 0 :=
    Continuous.ext_on SchwartzMap.dense_hasCompactSupport hΛc continuous_const
      (fun χ hχ ↦ hcs χ hχ)
  -- the Fourier side
  set P : ℝ^n → ℝ := fun ξ ↦ (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2
  have hPc : Continuous P := by fun_prop
  have hF : ∀ g : ℝ^n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ ξ, g ξ • (((P ξ : ℝ) : ℂ) * (𝓕 uc : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) = 0 := by
    intro g hg hgc
    have hgc' : HasCompactSupport (fun x ↦ ((g x : ℝ) : ℂ)) :=
      hgc.comp_left (g := Complex.ofRealCLM) (by simp)
    set G : 𝓢(ℝ^n, ℂ) := hgc'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
    have h0 := congrFun hall (𝓕⁻ G)
    simp only [Λ, L, ContinuousLinearMap.comp_apply, toLpCLM_apply] at h0
    rw [← Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq, L2.inner_def] at h0
    rw [← h0]
    apply integral_congr_ae
    filter_upwards [(𝓕 (schwartzBiharmonicSubLaplacian n (𝓕⁻ G))).coeFn_toLp 2
      (volume : Measure (ℝ^n))] with ξ h1
    rw [h1, RCLike.inner_apply', fourier_schwartzBiharmonicSubLaplacian_apply,
      FourierTransform.fourier_fourierInv_eq]
    have hGξ : G ξ = ((g ξ : ℝ) : ℂ) := rfl
    rw [hGξ, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    simp only [Complex.real_smul]
    ring
  have hloc : LocallyIntegrable (fun ξ ↦ ((P ξ : ℝ) : ℂ) *
      (𝓕 uc : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) volume := by
    have hl : LocallyIntegrable (𝓕 uc : Lp ℂ 2 (volume : Measure (ℝ^n))) volume :=
      (Lp.memLp _).locallyIntegrable (by norm_num)
    rw [← locallyIntegrableOn_univ] at hl ⊢
    exact hl.continuousOn_mul (Complex.continuous_ofReal.comp hPc).continuousOn
      isClosed_univ.isLocallyClosed
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hF
  have hhat : (𝓕 uc : Lp ℂ 2 (volume : Measure (ℝ^n))) = 0 := by
    apply Lp.ext
    filter_upwards [hzero, ae_ne_zero_euclidean hn,
      Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^n))] with ξ h1 h2 h3
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr h2
    rw [h3]
    exact (mul_eq_zero.mp h1).resolve_left (by norm_cast; simp only [P]; positivity)
  have hz : uc = 0 := by rw [← norm_eq_zero, ← Lp.norm_fourier_eq, hhat, norm_zero]
  filter_upwards [hz ▸ hcoe, Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^n))] with x h1 h2
  rw [h2] at h1
  simpa using h1.symm

end HeatEquation.WholeSpace
