/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.WeakGradient
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.HolderSolution

/-!
# Hölder weak gradients of nonlinear Euler–Lagrange solutions

An autonomous uniformly convex C² density with bounded Hessian gives local
H² regularity from the H¹ Euler–Lagrange equation. Its weak gradient
coordinates solve homogeneous linear equations with the measurable
coefficients `D²L(Du)`. De Giorgi's oscillation estimate therefore constructs
Hölder representatives of those coordinates.

This removes the locally Lipschitz-gradient seed for the homogeneous
nonlinear problem in dimensions greater than two. The density and the
original weak equation are the inputs; coefficient regularity and gradient
boundedness are not assumed. It is the first regularity step in the
nonlinear bootstrap of Evans, *Partial Differential Equations*, §8.3.2.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ} [Fact (0 < n)] {Ω V : Set (ℝ^n)}

omit [Fact (0 < n)] in
/-- In every dimension there is an auxiliary exponent `q > 2` that the De Giorgi iteration
accepts: at most `2n/(n-2)` if `n > 2`, and at most `4` if `n ≤ 2`. The regularity theorems
of this directory take such a `q` as an argument, and this lemma supplies it. -/
theorem exists_auxiliary_exponent :
    ∃ q : ℝ≥0∞, 2 < q ∧ q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0) := by
  let q : ℝ≥0 := if 2 < n then Inequalities.pStar n 2 else 4
  have hq : (2 : ℝ≥0) < q := by
    dsimp only [q]
    split_ifs with hdim
    · have hn : 0 < n := by omega
      have hd : (2 : ℝ) < n := by exact_mod_cast hdim
      change (2 : ℝ) < (Inequalities.pStar n 2 : ℝ)
      rw [Inequalities.pStar_coe hn (by simpa using hd)]
      norm_num
      apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 2)).mpr
      nlinarith
    · norm_num
  exact ⟨(q : ℝ≥0∞), by exact_mod_cast hq, le_rfl⟩

/-- Starting with the homogeneous nonlinear Euler–Lagrange equation
and an H¹ field, each weak gradient coordinate has a local Hölder
representative. For each admissible auxiliary exponent `q`, the Hölder
exponent is chosen before the domains `Ω` and `V`, the density and the
solution: it depends only on the dimension, on `q` and on the two bounds
`θ` and `Λ`. No continuity or essential boundedness of the gradient is an
input. -/
theorem exists_holder_exponent_weakGradient_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {Λ : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧
      ∀ (Ω V : Set (ℝ^n)) (_ : IsOpen Ω), Bornology.IsBounded Ω →
      ∀ (_ : IsOpen V), IsCompact (closure V) → closure V ⊆ Ω →
      ∀ (L : ℝ^n → ℝ), ContDiff ℝ 2 L →
        (∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ) →
        (∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z) →
      ∀ (u : H¹(Ω)),
        (∀ v : H¹₀(Ω),
          (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ V → ∀ i : Fin n,
        ∃ (g : ℝ^n → ℝ) (K : ℝ≥0), Continuous g ∧
          HolderOnWith K γ g (ball z (R / 64)) ∧
          g =ᵐ[volume.restrict (ball z (R / 64))]
            wkpCoordinateCLM (singleDerivIndex n i) u := by
  obtain ⟨γ, hγ, hγ1, hholder⟩ :=
    exists_holder_representative_of_homogeneous_weak_equation hq2 hq hθ Λ.coe_nonneg
  refine ⟨γ, hγ, hγ1, ?_⟩
  intro Ω V hΩ hbounded hV hVc hVΩ L hL hbound hpositive u hweak z R hR hball i
  have hweakF (v : H¹₀(Ω)) :
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
        ∫ x, wkpBaseCoordinateCLM (0 : H¹(Ω)) x *
          baseCoordCLM v x ∂domainMeasure n Ω := by
    rw [hweak v, map_zero]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
    simp only [hx, Pi.zero_apply, zero_mul]
  obtain ⟨W, B, hW, _hBrep, hBbound, hB, hlinear, _hdiv⟩ :=
    exists_interior_linearizedEquations_of_gradientDensity hΩ hbounded
      hV hVc hVΩ hL hbound hθ hpositive u 0 hweakF
  have hWi : IsInteriorWeakDivergenceSolution B 0 (∂[i] W) := by
    simpa only [map_zero] using hlinear i
  obtain ⟨g, K, hg, hgh, hga⟩ := hholder V hV
    (hbounded.subset (subset_closure.trans hVΩ)) B hBbound hB (∂[i] W) hWi z R hR hball
  have hbase : wkpBaseCoordinateCLM (∂[i] W) =
      wkpCoordinateCLM (singleDerivIndex n i)
        (lowerOrderCLM (by omega : 1 ≤ 2) W) := by
    simp only [wkpBaseCoordinateCLM_apply, partialDerivCLM,
      derivativeWordCLM_apply, derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
    rfl
  rw [hbase, hW] at hga
  refine ⟨g, K, hg, hgh, hga.trans ?_⟩
  exact (restrictCLM_apply_ae hV.measurableSet
    (subset_closure.trans hVΩ) u (singleDerivIndex n i)).filter_mono
      (ae_mono (domainMeasure_le ((ball_subset_ball (by linarith : R / 64 ≤ R)).trans hball)))

/-- Starting with the homogeneous nonlinear Euler–Lagrange equation
and an H¹ field on a fixed pair of domains, `V` with compact closure in
`Ω`, each weak gradient coordinate has a local Hölder representative. The
domains are fixed before the exponent. No continuity or essential boundedness
of the gradient is an input.

This is `exists_holder_exponent_weakGradient_of_gradientDensity` on one pair of domains. That
theorem states that one exponent serves all domains. -/
theorem exists_holder_weakGradient_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {Λ : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧
      ∀ (_ : IsOpen Ω), Bornology.IsBounded Ω →
      ∀ (_ : IsOpen V), IsCompact (closure V) → closure V ⊆ Ω →
      ∀ (L : ℝ^n → ℝ), ContDiff ℝ 2 L →
        (∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ) →
        (∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z) →
      ∀ (u : H¹(Ω)),
        (∀ v : H¹₀(Ω),
          (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ V → ∀ i : Fin n,
        ∃ (g : ℝ^n → ℝ) (K : ℝ≥0), Continuous g ∧
          HolderOnWith K γ g (ball z (R / 64)) ∧
          g =ᵐ[volume.restrict (ball z (R / 64))]
            wkpCoordinateCLM (singleDerivIndex n i) u := by
  obtain ⟨γ, hγ, hγ1, hreg⟩ :=
    exists_holder_exponent_weakGradient_of_gradientDensity (n := n) (Λ := Λ) hq2 hq hθ
  exact ⟨γ, hγ, hγ1, hreg Ω V⟩

end PDE.Elliptic.Regularity.Quasilinear
