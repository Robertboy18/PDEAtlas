/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.SuperlevelMeasure
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.UniformSobolev

/-!
# Sobolev gain for superlevel cutoffs

The truncated weak equation controls the full gradient of `η (u-k)₊`, including
the derivative of the cutoff. The zero-boundary Sobolev inequality then gives
an improved integrability estimate with constants uniform in the solution
and the truncation level. The forcing contributes the measure of the
superlevel set.

This is the Sobolev step of the De Giorgi iteration for scalar divergence-form
equations with measurable uniformly elliptic coefficients.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

private theorem norm_gradient_cutoff_sq_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) (T : H¹(Ω)) :
    ‖∇ (cutoffH1ToH10 hΩ.isOpen η hη T : H¹(Ω))‖ ^ 2 ≤
      2 * ∑ i, ‖(testFunctionLpTop (Ω := Ω) η •
        wkpCoordinateCLM (singleDerivIndex n i) T : DerivLp n 2 Ω)‖ ^ 2 +
      2 * (∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2) *
        ‖wkpBaseCoordinateCLM T‖ ^ 2 := by
  classical
  let v := cutoffH1ToH10 hΩ.isOpen η hη T
  have hnorm : ‖∇ (v : H¹(Ω))‖ ^ 2 = ∑ i, ‖derivCoordCLM i v‖ ^ 2 :=
    Lp.norm_euclideanTuple_sq _
  rw [hnorm]
  have hterm (i : Fin n) :
      ‖derivCoordCLM i v‖ ^ 2 ≤
        2 * ‖(testFunctionLpTop (Ω := Ω) η •
          wkpCoordinateCLM (singleDerivIndex n i) T : DerivLp n 2 Ω)‖ ^ 2 +
        2 * ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2 *
          ‖wkpBaseCoordinateCLM T‖ ^ 2 := by
    rw [derivCoordCLM_cutoffH1ToH10]
    have h := norm_add_le
      (testFunctionLpTop (Ω := Ω) η • wkpCoordinateCLM (singleDerivIndex n i) T :
        DerivLp n 2 Ω)
      (partialTestFunctionLpTop (Ω := Ω) η i • wkpBaseCoordinateCLM T)
    have hd :
        ‖(partialTestFunctionLpTop (Ω := Ω) η i • wkpBaseCoordinateCLM T :
          DerivLp n 2 Ω)‖ ≤
        ‖partialTestFunctionLpTop (Ω := Ω) η i‖ * ‖wkpBaseCoordinateCLM T‖ :=
      Lp.norm_smul_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg _)
      (h.trans (add_le_add le_rfl hd)) 2
    nlinarith only [hs, sq_nonneg
      (‖(testFunctionLpTop (Ω := Ω) η •
        wkpCoordinateCLM (singleDerivIndex n i) T : DerivLp n 2 Ω)‖ -
        ‖partialTestFunctionLpTop (Ω := Ω) η i‖ * ‖wkpBaseCoordinateCLM T‖)]
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)

private theorem superlevel_sobolev_of_gradient_estimate
    {q : ℝ≥0∞} {C : ℝ} (hC : 0 < C)
    (hSob : ∀ v : H¹₀(Ω),
      MemLp (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω) ∧
        eLpNorm (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω) ≤
          ENNReal.ofReal (C * ‖∇ (v : H¹(Ω))‖)) :
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω) (α : ℝ), AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 Ω) (u : H¹(Ω)), IsInteriorWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M) →
      ∀ (k : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω),
      let U := u - wkpConstant k
      let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
      let v := cutoffH1ToH10 hΩ.isOpen η hη T
      MemLp (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω) ∧
      α ^ 2 * (eLpNorm (baseRepresentative (v : H¹(Ω)))
        q (domainMeasure n Ω)).toReal ^ 2 ≤
        C ^ 2 * ((8 * (∑ i, ∑ j,
          ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 +
            2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2) *
              ‖wkpBaseCoordinateCLM T‖ ^ 2 +
          4 * α * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 * M *
            (domainMeasure n Ω).real {x | 0 < wkpBaseCoordinateCLM U x} ^ (1 / 2 : ℝ) *
              ‖wkpBaseCoordinateCLM T‖) := by
  intro a α ha f u hu M hM hf k η hη
  dsimp only
  let U := u - wkpConstant k
  let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
  let v := cutoffH1ToH10 hΩ.isOpen η hη T
  obtain ⟨hv, hSobv⟩ := hSob v
  refine ⟨hv, ?_⟩
  have hs : (eLpNorm (baseRepresentative (v : H¹(Ω)))
      q (domainMeasure n Ω)).toReal ≤ C * ‖∇ (v : H¹(Ω))‖ := by
    change eLpNorm (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω) ≤
      ENNReal.ofReal (C * ‖∇ (v : H¹(Ω))‖) at hSobv
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSobv
    rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _))] at h
    exact h
  have he := hu.superlevel_cutoff_gradient_sq_le_measure a ha f u hM hf k η hη
  have hc := norm_gradient_cutoff_sq_le η hη T
  have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg α)
  have hs' := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hs 2) (sq_nonneg α)
  change α ^ 2 *
    (eLpNorm (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω)).toReal ^ 2 ≤ _
  dsimp only at he
  change α ^ 2 * ∑ i, ‖(testFunctionLpTop (Ω := Ω) η •
      wkpCoordinateCLM (singleDerivIndex n i) T : DerivLp n 2 Ω)‖ ^ 2 ≤ _ at he
  nlinarith only [hs', mul_le_mul_of_nonneg_left
    (show α ^ 2 * ‖∇ (v : H¹(Ω))‖ ^ 2 ≤
      (8 * (∑ i, ∑ j, ‖a i j‖ *
          ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 +
        2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2) *
          ‖wkpBaseCoordinateCLM T‖ ^ 2 +
        4 * α * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 * M *
          (domainMeasure n Ω).real {x | 0 < wkpBaseCoordinateCLM U x} ^
            (1 / 2 : ℝ) * ‖wkpBaseCoordinateCLM T‖ by
      dsimp only [U, T, v] at *
      nlinarith only [hc', he]) (sq_nonneg C)]

/-- The Sobolev superlevel estimate derived from the weak equation.
One may choose `2 ≤ q ≤ 2n/(n-2)` above dimension two, or `2 ≤ q ≤ 4`
in dimensions one and two. The positive constant depends only on the domain,
dimension and exponent; all coefficient and cutoff factors are displayed. -/
theorem exists_superlevel_cutoff_sobolev_sq_le
    (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω) (α : ℝ), AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 Ω) (u : H¹(Ω)), IsInteriorWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M) →
      ∀ (k : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω),
      let U := u - wkpConstant k
      let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
      let v := cutoffH1ToH10 hΩ.isOpen η hη T
      MemLp (baseRepresentative (v : H¹(Ω))) q (domainMeasure n Ω) ∧
      α ^ 2 * (eLpNorm (baseRepresentative (v : H¹(Ω)))
        q (domainMeasure n Ω)).toReal ^ 2 ≤
        C ^ 2 * ((8 * (∑ i, ∑ j,
          ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 +
            2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2) *
              ‖wkpBaseCoordinateCLM T‖ ^ 2 +
          4 * α * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 * M *
            (domainMeasure n Ω).real {x | 0 < wkpBaseCoordinateCLM U x} ^ (1 / 2 : ℝ) *
              ‖wkpBaseCoordinateCLM T‖) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Fact.out
  obtain ⟨C, hC, hSob⟩ := exists_uniform_eLpNorm_le_gradient_on_subdomains
    hΩb hn hq2 hq
  exact ⟨C, hC, superlevel_sobolev_of_gradient_estimate hC (hSob Ω hΩ.isOpen Subset.rfl)⟩

/-- The superlevel Sobolev estimate has one constant on every open subdomain
of a fixed bounded ambient set. The coefficient and cutoff factors remain
explicit, so this version applies uniformly along a shrinking-domain iteration. -/
theorem exists_uniform_superlevel_cutoff_sobolev_sq_le
    {W : Set ℝ^n} (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set ℝ^n) [hV : Boundary.C1ExtensionAtlas n V],
      V ⊆ W →
      ∀ (a : Fin n → Fin n → DerivLp n ∞ V) (α : ℝ), AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 V) (u : H¹(V)), IsInteriorWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n V, ‖f x‖ ≤ M) →
      ∀ (k : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ V),
      let U := u - wkpConstant k
      let T := lipschitzCompositionOn hV.isOpen Lp.lipschitzWith_pos_part U
      let v := cutoffH1ToH10 hV.isOpen η hη T
      MemLp (baseRepresentative (v : H¹(V))) q (domainMeasure n V) ∧
      α ^ 2 * (eLpNorm (baseRepresentative (v : H¹(V)))
        q (domainMeasure n V)).toReal ^ 2 ≤
        C ^ 2 * ((8 * (∑ i, ∑ j,
          ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := V) η i‖) ^ 2 +
            2 * α ^ 2 * ∑ i, ‖partialTestFunctionLpTop (Ω := V) η i‖ ^ 2) *
              ‖wkpBaseCoordinateCLM T‖ ^ 2 +
          4 * α * ‖testFunctionLpTop (Ω := V) η‖ ^ 2 * M *
            (domainMeasure n V).real {x | 0 < wkpBaseCoordinateCLM U x} ^ (1 / 2 : ℝ) *
              ‖wkpBaseCoordinateCLM T‖) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Fact.out
  obtain ⟨C, hC, hSob⟩ := exists_uniform_eLpNorm_le_gradient_on_subdomains
    hWb hn hq2 hq
  refine ⟨C, hC, ?_⟩
  intro V hV hVW
  exact superlevel_sobolev_of_gradient_estimate hC (hSob V hV.isOpen hVW)

end SobolevSpace.GraphSpace
