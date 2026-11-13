/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletClassical

/-!
# Fixed-time stability of the domain heat series

Polynomially weighted spectral damping is bounded on the pivot Hilbert space.
The elliptic lift therefore gives a supremum estimate at every fixed positive time.
Its constant may diverge at zero; its role is to pass the maximum principle from
smooth approximating data to the constructed spectral solution.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set
open scoped ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)

/-- Polynomially weighted positive-time damping is a bounded Hilbert operator. -/
theorem norm_spectralHeatPower_le (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) :
    ‖spectralHeatPower b lambda hlambda m f t‖ ≤ (m.factorial : ℝ) / t ^ m * ‖f‖ := by
  let C : ℝ := (m.factorial : ℝ) / t ^ m
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.le m)
  rw [← b.repr.norm_map, ← b.repr.norm_map f]
  calc
    _ ≤ ‖C • b.repr f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      rw [spectralHeatPower_repr b lambda hlambda m f ht, norm_mul,
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hlambda i) m) (Real.exp_nonneg _))]
      change _ ≤ ‖C * b.repr f i‖
      rw [norm_mul, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_mul_le m (hlambda i) ht)
        (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg hC]

/-- Weighted heat vectors respect subtraction of the initial data. -/
theorem spectralHeatPower_sub (m : ℕ) (f g : H) {t : ℝ} (ht : 0 < t) :
    spectralHeatPower b lambda hlambda m (f - g) t =
      spectralHeatPower b lambda hlambda m f t - spectralHeatPower b lambda hlambda m g t := by
  apply b.repr.injective
  ext i
  simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, spectralHeatPower_repr b lambda hlambda m _ ht,
    mul_sub]

namespace DirichletHeatSpectrum

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- A fixed-time supremum bound follows from spectral damping and the bounded elliptic lift. -/
theorem norm_classicalPower_le (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    ‖S.classicalPower hopen hbounded hgraph hγ 0 f t x‖ ≤
      ‖dirichletHolderLiftCLM hopen hbounded hgraph hγ 2‖ *
        ((2 + n + 1).factorial : ℝ) / t ^ (2 + n + 1) * ‖f‖ := by
  rw [classicalPower, CKGammaOn.interiorDerivative_apply _ _ hx]
  calc
    _ ≤ ‖S.holderPower hopen hbounded hgraph hγ 2 0 f t‖ :=
      ((S.holderPower hopen hbounded hgraph hγ 2 0 f t).derivative 0).norm_coe_le_norm _
        |>.trans ((S.holderPower hopen hbounded hgraph hγ 2 0 f t).norm_derivative_le 0)
    _ ≤ ‖dirichletHolderLiftCLM hopen hbounded hgraph hγ 2‖ *
        ‖spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (2 + n + 1) f t‖ := by
      unfold holderPower
      rw [Nat.zero_add]
      exact (dirichletHolderLiftCLM hopen hbounded hgraph hγ 2).le_opNorm _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (norm_spectralHeatPower_le S.basis S.eigenvalue S.eigenvalue_nonneg (2 + n + 1) f ht)
        (norm_nonneg (dirichletHolderLiftCLM hopen hbounded hgraph hγ 2))
      simpa only [mul_div_assoc, mul_assoc] using h

/-- The positive-time classical representative respects subtraction on the closure. -/
theorem classicalPower_sub (f g : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    S.classicalPower hopen hbounded hgraph hγ 0 (f - g) t x =
      S.classicalPower hopen hbounded hgraph hγ 0 f t x -
        S.classicalPower hopen hbounded hgraph hγ 0 g t x := by
  have h : S.holderPower hopen hbounded hgraph hγ 2 0 (f - g) t =
      S.holderPower hopen hbounded hgraph hγ 2 0 f t -
        S.holderPower hopen hbounded hgraph hγ 2 0 g t := by
    unfold holderPower
    rw [spectralHeatPower_sub _ _ _ _ _ _ ht, map_sub]
  simp only [classicalPower, CKGammaOn.interiorDerivative_apply _ _ hx, h]
  rfl

end DirichletHeatSpectrum

end HeatEquation
