/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.RealSpectrum.Classical.WellPosed

/-!
# A defective two-component system from fractional Sobolev data

The nonzero nilpotent Jordan block has real spectrum at every real frequency.
The real-spectrum existence and uniqueness theorem for fractional Sobolev data
therefore applies to this coupled system (`exists_unique_jointC1_nilpotentJordan`). Its
equations are `∂t U₀ + ∂x U₁ = 0` and `∂t U₁ = 0`. The matrix is not diagonalizable.
-/

@[expose] public noncomputable section

open Set SobolevSpace.Fractional
open scoped Matrix Matrix.Norms.L2Operator

namespace PDE.Examples.Hyperbolic.FirstOrder.RealSpectrum.Jordan

open PDE.Hyperbolic.FirstOrder

/-- The nonzero nilpotent Jordan block of size two. -/
def nilpotentJordan : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The off-diagonal entry of the Jordan block is `1`. -/
theorem nilpotentJordan_offDiagonal : nilpotentJordan 0 1 = 1 := rfl

/-- The block is nilpotent of index two. -/
theorem nilpotentJordan_sq : nilpotentJordan ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, nilpotentJordan, Fin.sum_univ_two]

/-- At every real frequency the symbol has real spectrum. -/
theorem nilpotentJordan_realSpectrum (ξ : ℝ^1) :
    ∀ z ∈ spectrum ℂ
      (∑ _j : Fin 1, ξ _j • nilpotentJordan.map Complex.ofReal), z.im = 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := ξ 0 • nilpotentJordan.map Complex.ofReal
  have hupper : A.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [A, nilpotentJordan]
  intro z hz
  have hz' : z ∈ spectrum ℂ A := by simpa [A] using hz
  rw [hupper.spectrum_eq_range_diag] at hz'
  obtain ⟨i, rfl⟩ := hz'
  fin_cases i <;> simp [A, nilpotentJordan]

/-- For `s > 5/2` and data in `Hˢ`, the Jordan system has a `C¹` solution, unique among
solutions that are `C¹` for `t > 0` and continuous for `t ≥ 0`. -/
theorem exists_unique_jointC1_nilpotentJordan {s : ℝ} (hs : (5 : ℝ) / 2 < s)
    (f : Fin 2 → HsSpaceReal 1 s) :
    ∃ U : ℝ × ℝ^1 → ℝ^2,
      ContDiff ℝ 1 U ∧
      (∀ p : ℝ × ℝ^1,
        fderiv ℝ U p (1, 0) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) nilpotentJordan
            (fderiv ℝ U p (0, EuclideanSpace.single 0 1)) = 0) ∧
      (∀ x, U (0, x) = realSpectrumInitialData (by norm_num; linarith) f x) ∧
      ∀ V : ℝ × ℝ^1 → ℝ^2,
        ContDiffOn ℝ 1 V (Ioi 0 ×ˢ univ) →
        ContinuousOn V (Ici 0 ×ˢ univ) →
        (∀ t > 0, ∀ x, fderiv ℝ V (t, x) (1, 0) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) nilpotentJordan
            (fderiv ℝ V (t, x) (0, EuclideanSpace.single 0 1)) = 0) →
        (∀ x, V (0, x) = realSpectrumInitialData (by norm_num; linarith) f x) →
        EqOn V U (Ici 0 ×ˢ univ) := by
  have hthreshold : (1 : ℝ) < 2 * (s - (2 : ℕ)) := by norm_num; linarith
  obtain ⟨U, hU, heq, hinit, huniq⟩ := exists_unique_jointC1_realSpectrumSolution
    (fun _ : Fin 1 ↦ nilpotentJordan) nilpotentJordan_realSpectrum
      (by simpa using hthreshold) f
  exact ⟨U, hU, by simpa using heq, hinit, by simpa using huniq⟩

end PDE.Examples.Hyperbolic.FirstOrder.RealSpectrum.Jordan
