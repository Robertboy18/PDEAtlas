/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.RealSpectrum.Jordan
import PDE.Spaces.Sobolev.Fractional.WholeSpace.WeakDerivative

/-!
# Schwartz data for the Jordan system

Every real Schwartz function `ψ` gives fractional Sobolev data `(0, ψ)`, and
`exists_unique_jointC1_realSpectrumSolution_of_ae_eq` gives a `C¹` solution of the
Jordan system with exactly these initial values, unique among classical solutions
(`exists_unique_jointC1_nilpotentJordan_schwartz`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.Fractional
open scoped SchwartzMap Matrix.Norms.L2Operator

namespace PDE.Examples.Hyperbolic.FirstOrder.RealSpectrum.Jordan

open PDE.Hyperbolic.FirstOrder

/-- For every real Schwartz function `ψ`, the Jordan system has a `C¹` solution with
initial value `(0, ψ)`, unique among classical solutions. -/
theorem exists_unique_jointC1_nilpotentJordan_schwartz
    {s : ℝ} (hs : (5 : ℝ) / 2 < s) (ψ : 𝓢(ℝ^1, ℝ)) :
    ∃ U : ℝ × ℝ^1 → ℝ^2,
      ContDiff ℝ 1 U ∧
      (∀ p : ℝ × ℝ^1,
        fderiv ℝ U p (1, 0) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) nilpotentJordan
            (fderiv ℝ U p (0, EuclideanSpace.single 0 1)) = 0) ∧
      (∀ x, U (0, x) = WithLp.toLp 2 ![0, ψ x]) ∧
      ∀ V : ℝ × ℝ^1 → ℝ^2,
        ContDiffOn ℝ 1 V (Ioi 0 ×ˢ univ) →
        ContinuousOn V (Ici 0 ×ˢ univ) →
        (∀ t > 0, ∀ x, fderiv ℝ V (t, x) (1, 0) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) nilpotentJordan
            (fderiv ℝ V (t, x) (0, EuclideanSpace.single 0 1)) = 0) →
        (∀ x, V (0, x) = WithLp.toLp 2 ![0, ψ x]) →
        EqOn V U (Ici 0 ×ˢ univ) := by
  have hs0 : 0 ≤ s := by linarith
  have hthreshold : ((1 : ℕ) : ℝ) < 2 * (s - (2 : ℕ)) := by norm_num; linarith
  let φ (i : Fin 2) : 𝓢(ℝ^1, ℂ) :=
    if i = 0 then 0 else ψ.postcompCLM Complex.ofRealCLM
  have hφ (i : Fin 2) (x : ℝ^1) : (φ i x).im = 0 := by
    fin_cases i <;> simp [φ]
  let f (i : Fin 2) : HsSpaceReal 1 s :=
    HsSpaceReal.ofPhysical hs0 (SchwartzMap.memSobolev (s := s) (φ i)).toBesselPotentialSpace
      (isRealL2_ofSchwartz hs0 (φ i) (hφ i))
  let v (x : ℝ^1) : ℝ^2 := WithLp.toLp 2 ![0, ψ x]
  have hv : Continuous v := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    exact continuous_pi fun i ↦ by
      fin_cases i
      · exact continuous_const
      · exact ψ.continuous
  have hdata (i : Fin 2) :
      (fun x ↦ v x i) =ᵐ[volume] (HsSpaceReal.toL2FunCLM 1 hs0 (f i) : ℝ^1 → ℝ) := by
    have hreal := HsSpaceReal.toL2FunCLM_apply_ae hs0 (f i)
    change _ =ᵐ[volume] fun x ↦
      ((toL2Fun hs0 (SchwartzMap.memSobolev (s := s) (φ i)).toBesselPotentialSpace :
        ℝ^1 → ℂ) x).re at hreal
    rw [toL2Fun_ofSchwartz] at hreal
    filter_upwards [hreal, (φ i).coeFn_toLp 2 (volume : Measure (ℝ^1))] with x hx hφx
    rw [hx, hφx]
    fin_cases i <;> simp [v, φ]
  obtain ⟨U, hU, heq, hinit, huniq⟩ := exists_unique_jointC1_realSpectrumSolution_of_ae_eq
    (fun _ : Fin 1 ↦ nilpotentJordan) nilpotentJordan_realSpectrum hthreshold f hv hdata
  exact ⟨U, hU, by simpa using heq, hinit, by simpa using huniq⟩

end PDE.Examples.Hyperbolic.FirstOrder.RealSpectrum.Jordan
