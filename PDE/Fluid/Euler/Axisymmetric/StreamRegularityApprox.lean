/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.StreamRegularityLimit
public import PDE.Fluid.Euler.Axisymmetric.StreamRegularityPeriodic
public import PDE.Spaces.Sobolev.Approximation.Mollification.UniformJets
import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles

/-!
# Stream functions in the cylinder for sources of finite regularity

Let `n ≥ 2`, `P` be a compactly supported `C^{3n}` function on the plane, odd in the second
coordinate and vanishing for `|x₁| > a` with `a + 1/4 < L/2`, and
`Ω = periodizeZ hL (P ∘ pointPairEquiv⁻¹)` the `L`-periodic profile it defines. The mollifications
`P_j` of `P` at the scales `1/(8(j+1))` are smooth and odd, vanish for `|x₁| > a + 1/4`, and their
coordinate derivatives of order at most `3n` converge uniformly
(`SobolevSpace.Approximation.iteratedPartialDeriv_mollify_tendstoUniformly`). Their periodizations
`Ω_j` are smooth, odd and periodic profiles with `Ω_j → Ω` pointwise, and `∂_s^l ∂_z^{2n} Ω_j`,
`l ≤ n`, is the periodization of the derivative of `P_j` along the word `0^l 1^{2n}`, so these
derivatives are uniformly Cauchy. By `exists_isStreamFunction_of_tendsto` the angular vorticity
`r Ω(r², z)` has a `Cⁿ` stream function in the cylinder (`exists_isStreamFunction_of_contDiff`),
with no smoothness of `P` beyond `C^{3n}`.

## Main results

* `exists_isStreamFunction_of_contDiff`: existence for `C^{3n}` sources.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open PDE.Common (pointPairEquiv)

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries SobolevSpace.Approximation
open AxisymmetricFlow (squaredRadiusMap contDiff_squaredRadiusMap)
open scoped Topology

set_option linter.missingDocs true

noncomputable section

variable {L : ℝ}

/-- **The stream function of a source of class `C^{3n}`.** For `n ≥ 2` and a compactly
supported `C^{3n}` function `P` on the plane, odd in the second coordinate and vanishing for
`|x₁| > a` with `0 ≤ a` and `a + 1/4 < L/2`, the angular vorticity `r Ω(r², z)` of the `L`-periodic
profile `Ω = periodizeZ hL (P ∘ pointPairEquiv⁻¹)` has a `Cⁿ` stream function in the cylinder with
period `L`, odd in `z`, of the axis-regular form `r Ψ₀(r², z)` with `Ψ₀` of class `Cⁿ`. -/
theorem exists_isStreamFunction_of_contDiff (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) {P : ℝ^2 → ℝ}
    (hP : ContDiff ℝ (3 * n : ℕ) P) (hPc : HasCompactSupport P)
    (hodd : PDE.Common.IsOddUnderCoordinateReflection 1 P) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a + 1 / 4 < L / 2) (hPz : ∀ x : ℝ^2, a < |x 1| → P x = 0) :
    ∃ φ : ℝ^2 → ℝ,
      IsStreamFunction L (meridianVorticity (periodizeZ hL (P ∘ pointPairEquiv.symm))) φ ∧
      ContDiff ℝ n φ ∧ (∀ x, φ (axialReflection x) = -φ x) ∧
      ∃ Ψ₀ : ℝ^2 → ℝ, ContDiff ℝ n Ψ₀ ∧ ∀ x, φ x = x 0 * Ψ₀ (squaredRadiusMap x) := by
  set μ := standardMollifier 2
  set ε : ℕ → ℝ := fun j ↦ 1 / 8 * (1 / ((j : ℝ) + 1)) with hεdef
  have hεpos : ∀ j, 0 < ε j := fun j ↦ by positivity
  have hεle8 : ∀ j, ε j ≤ 1 / 8 := fun j ↦ mul_le_of_le_one_right (by norm_num)
    ((div_le_one (by positivity)).2 (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]))
  have hεle : ∀ j, ε j ≤ 1 := fun j ↦ (hεle8 j).trans (by norm_num)
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 8 : ℝ)
  set M : ℕ → ℝ^2 → ℝ := fun j ↦ mollify μ (ε j) P with hMdef
  have hM : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (M j) := fun j ↦
    mollify_contDiff_of_pos μ (hεpos j) P hP.continuous.locallyIntegrable
  have hModd : ∀ j, PDE.Common.IsOddUnderCoordinateReflection 1 (M j) := fun j ↦
    mollify_odd_of_radial μ (fun t ↦ Real.smoothTransition (2 - t) /
      ∫ y : ℝ^2, Real.smoothTransition (2 - ‖y‖)) standardMollifier_eq_norm (hεpos j) 1 hodd
  have hMz : ∀ j, ∀ x : ℝ^2, a + 1 / 4 < |x 1| → M j x = 0 := by
    intro j x hx
    by_contra hne
    obtain ⟨y, hy, z, hz, rfl⟩ := support_mollify_subset_closedBall_add_support μ (hεpos j)
      (tsupport_standardMollifier_subset_closedBall 2) P hne
    have hy' : ‖y‖ ≤ ε j * 2 := by simpa using hy
    have hz' : |z 1| ≤ a := not_lt.1 fun h ↦ hz (hPz z h)
    have hy1 : |y 1| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 1
    have h1 : |(y + z) 1| ≤ |y 1| + |z 1| := by simpa using abs_add_le (y 1) (z 1)
    linarith [hεle8 j]
  -- the profiles
  have hcoord : ∀ s z : ℝ, (pointPairEquiv.symm (s, z) : ℝ^2) 1 = z := fun s z ↦ by simp
  have hvan : ∀ (g : ℝ^2 → ℝ), (∀ x : ℝ^2, a + 1 / 4 < |x 1| → g x = 0) →
      ∀ s z, a + 1 / 4 < |z| → (g ∘ pointPairEquiv.symm) (s, z) = 0 := fun g hg s z hz ↦ by
    simp only [Function.comp_apply]
    exact hg _ (by rw [hcoord]; exact hz)
  have ha0' : 0 ≤ a + 1 / 4 := by linarith
  set Ω : ℕ → ℝ × ℝ → ℝ := fun j ↦ periodizeZ hL (M j ∘ pointPairEquiv.symm) with hΩdef
  have hΩs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ω j) := fun j ↦
    contDiff_periodizeZ hL (hvan _ (hMz j)) ha0' ha ((hM j).comp pointPairEquiv.symm.contDiff)
  have hΩp : ∀ j s z, Ω j (s, z + L) = Ω j (s, z) := fun j s z ↦ periodizeZ_add hL s z
  have hrefl : ∀ s z : ℝ, (pointPairEquiv.symm (s, -z) : ℝ^2) =
      PDE.Common.coordinateReflection 1 (pointPairEquiv.symm (s, z)) := fun s z ↦ by
    ext i
    fin_cases i <;>
      simp [PDE.Common.coordinateReflection_apply_same]
  have hΩo : ∀ j s z, Ω j (s, -z) = -Ω j (s, z) := fun j s z ↦
    periodizeZ_neg hL (hvan _ (hMz j)) ha (fun s z ↦ by
      simp only [Function.comp_apply, hrefl]
      exact hModd j _) s z
  -- convergence of the derivative words
  have hconv : ∀ w : List (Fin 2), w.length ≤ 3 * n →
      TendstoUniformly (fun j ↦ iteratedPartialDeriv w (M j)) (iteratedPartialDeriv w P)
        atTop := fun w hw ↦
    iteratedPartialDeriv_mollify_tendstoUniformly μ hP hPc ε hεpos hεle hε0 w hw
  have hlim : ∀ q, Tendsto (fun j ↦ Ω j q) atTop
      (𝓝 (periodizeZ hL (P ∘ pointPairEquiv.symm) q)) := fun q ↦
    (hconv [] (by simp)).tendsto_at _
  have hcauchy : ∀ η > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ l ≤ n, ∀ s ∈ modeCollar L,
      ∀ z ∈ Icc 0 L,
        |(sDeriv^[l] (zDeriv^[2 * n] (fun q ↦ Ω i q - Ω j q))) (s, z)| ≤ η := by
    intro η hη
    have hw : ∀ l ≤ n, (List.replicate l (0 : Fin 2) ++ List.replicate (2 * n) 1).length ≤
        3 * n := fun l hl ↦ by simp; omega
    have hev : ∀ l ∈ Finset.range (n + 1), ∀ᶠ j in atTop, ∀ x : ℝ^2,
        dist (iteratedPartialDeriv (List.replicate l (0 : Fin 2) ++ List.replicate (2 * n) 1)
          P x) (iteratedPartialDeriv (List.replicate l 0 ++ List.replicate (2 * n) 1) (M j) x) <
          η / 2 := fun l hl ↦
      Metric.tendstoUniformly_iff.1 (hconv _ (hw l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))))
        (η / 2) (half_pos hη)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((Filter.eventually_all_finset _).2 hev)
    refine ⟨N, fun i hi j hj l hl s _ z _ ↦ ?_⟩
    have hfun : (fun q ↦ Ω i q - Ω j q) =
        periodizeZ hL ((fun x ↦ M i x - M j x) ∘ pointPairEquiv.symm) := rfl
    have hdv : ∀ x : ℝ^2, a + 1 / 4 < |x 1| → M i x - M j x = 0 := fun x hx ↦ by
      rw [hMz i x hx, hMz j x hx, sub_self]
    rw [hfun, iterate_sDeriv_zDeriv_periodizeZ hL (hvan _ hdv) ha0' ha,
      iterate_sDeriv_zDeriv_comp_pointPairEquiv_symm]
    set w := List.replicate l (0 : Fin 2) ++ List.replicate (2 * n) 1
    have hsub : iteratedPartialDeriv w (fun x ↦ M i x - M j x) =
        fun x ↦ iteratedPartialDeriv w (M i) x - iteratedPartialDeriv w (M j) x :=
      PDE.iteratedPartialDeriv_sub_of_contDiff w ((hM i).of_le (by exact_mod_cast le_top))
        ((hM j).of_le (by exact_mod_cast le_top))
    simp only [periodizeZ, Function.comp_apply, hsub]
    set x := pointPairEquiv.symm (s, toIcoMod hL (-(L / 2)) z)
    have hl' := Finset.mem_range.2 (Nat.lt_succ_of_le hl)
    have h1 := hN i hi l hl' x
    have h2 := hN j hj l hl' x
    rw [dist_eq_norm, Real.norm_eq_abs] at h1 h2
    linarith [abs_sub_le (iteratedPartialDeriv w (M i) x) (iteratedPartialDeriv w P x)
      (iteratedPartialDeriv w (M j) x), abs_sub_comm (iteratedPartialDeriv w (M i) x)
      (iteratedPartialDeriv w P x)]
  exact exists_isStreamFunction_of_tendsto hL hn hΩs hΩp hΩo hlim hcauchy

end

end Euler.Cylinder
