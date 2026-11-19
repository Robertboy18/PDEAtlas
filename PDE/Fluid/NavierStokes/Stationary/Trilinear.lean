/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Representative
public import PDE.Spaces.Sobolev.Inequalities.Ladyzhenskaya.WholeSpace

/-!
# Ladyzhenskaya's inequality and the convection form on `H¹(ℝ³; ℝ³)`

On the energy space `E = H¹(ℝ³)³`, with `‖v‖²_E = Σₖ ‖vₖ‖₂² + Σₖᵢ ‖∂ᵢvₖ‖₂²`, the convection
trilinear form is

`b(u, v, w) = ∫ (u · ∇) v · w = Σₖ Σᵢ ∫ uᵢ ∂ᵢvₖ wₖ`.

Ladyzhenskaya's inequality `‖f‖₄⁴ ≤ ‖f‖₂ ‖∂₀f‖₂ ‖∂₁f‖₂ ‖∂₂f‖₂` for scalar `f ∈ H¹(ℝ³)` gives
`‖f‖₄ ≤ ½ ‖f‖_{H¹}`, so the componentwise inclusion `l4CLM : E → L⁴(ℝ³)³` has norm at most `1/2`.
Hölder's inequality then bounds the form by `‖u‖_{L⁴} ‖∇v‖_{L²} ‖w‖_{L⁴}`, and

`|b(u, v, w)| ≤ ¼ ‖u‖_E ‖v‖_E ‖w‖_E`.

The form is assembled from `ContinuousLinearMap.transportPairing`, so it is a continuous
trilinear form; `convectionTrilinear_eq_integral` writes it as the Lebesgue integral of the
chosen representatives of `u`, `w` and of the weak gradient of `v`.

## Main results

* `NavierStokes.l4_ladyzhenskaya`: `‖u‖₄⁴ ≤ 4 ‖u‖₂ ‖∇u‖₂³` for `u ∈ H¹(ℝ³)`, together with
  `l4_ladyzhenskaya_gradient` (`27 ‖u‖₄⁸ ≤ ‖u‖₂² ‖∇u‖₂⁶`), `l4_ladyzhenskaya_add`
  (`‖u‖₄² ≤ 3^{3/4}/16 (‖u‖₂ + ‖∇u‖₂)²`, the scalar form of Lemma 6 of Hou, Wang and Yang,
  with a constant larger by `π/2`) and `l4_ladyzhenskaya_weighted`
  (`‖u‖₄² ≤ t/4 (s² ‖u‖₂² + ‖∇u‖₂²)` for `t² s ≥ 1`). The product form with constant one is
  `SobolevSpace.Inequalities.toReal_eLpNorm_four_pow_four_le_H1`.
* `Stationary.l4CLM`, `Stationary.norm_l4CLM_apply_le`,
  `Stationary.norm_l4CLM_apply_sq_le_weighted`,
  `Stationary.toReal_eLpNorm_representative_le_half`: the `L⁴` inclusion of `E`.
* `Stationary.convectionTrilinear`, `Stationary.convectionTrilinear_eq_integral`,
  `Stationary.norm_convectionTrilinear_le`, `Stationary.norm_convectionTrilinear_le_weighted`,
  `Stationary.convectionTrilinear_isBoundedBy`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Appendix A, Lemma 6, p. 59.
  <https://arxiv.org/abs/2509.25116v2>
* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372.
  <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Inequalities
open scoped ENNReal Sobolev

namespace NavierStokes

local notation "E" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- **Ladyzhenskaya's inequality** on `H¹(ℝ³)`: `‖u‖₄⁴ ≤ 4 ‖u‖₂ ‖∇u‖₂³`. The proof gives
constant one (`SobolevSpace.Inequalities.toReal_eLpNorm_four_pow_four_le_H1`), and `3^{-3/2}`
with the arithmetic-geometric mean inequality (`l4_ladyzhenskaya_gradient`). -/
theorem l4_ladyzhenskaya (u : H¹(ℝ^3)) :
    (eLpNorm (baseRepresentative u) 4 volume).toReal ^ 4 ≤
      4 * ‖wkpBaseCoordinateCLM u‖ * ‖Stationary.scalarGradientCLM u‖ ^ 3 := by
  have h := toReal_eLpNorm_four_pow_four_le_H1 u
  rw [Fin.prod_univ_three] at h
  have hG (j : Fin 3) := Stationary.norm_partial_le_norm_scalarGradientCLM u j
  have ha : 0 ≤ ‖wkpBaseCoordinateCLM u‖ := norm_nonneg _
  have hG0 : 0 ≤ ‖Stationary.scalarGradientCLM u‖ := norm_nonneg _
  have hprod : ‖wkpCoordinateCLM (singleDerivIndex 3 0) u‖ *
      ‖wkpCoordinateCLM (singleDerivIndex 3 1) u‖ *
        ‖wkpCoordinateCLM (singleDerivIndex 3 2) u‖ ≤ ‖Stationary.scalarGradientCLM u‖ ^ 3 := by
    calc _ ≤ ‖Stationary.scalarGradientCLM u‖ * ‖Stationary.scalarGradientCLM u‖ *
          ‖Stationary.scalarGradientCLM u‖ := by
          gcongr
          exacts [hG 0, hG 1, hG 2]
      _ = _ := by ring
  have hN : 0 ≤ ‖Stationary.scalarGradientCLM u‖ ^ 3 := by positivity
  calc _ ≤ _ := h
    _ ≤ ‖wkpBaseCoordinateCLM u‖ * ‖Stationary.scalarGradientCLM u‖ ^ 3 := by gcongr
    _ ≤ 4 * ‖wkpBaseCoordinateCLM u‖ * ‖Stationary.scalarGradientCLM u‖ ^ 3 := by
        nlinarith [mul_nonneg ha hN]

/-- Ladyzhenskaya's inequality with the arithmetic-geometric mean constant:
`27 ‖u‖₄⁸ ≤ ‖u‖₂² ‖∇u‖₂⁶`, that is `‖u‖₄⁴ ≤ 3^{-3/2} ‖u‖₂ ‖∇u‖₂³`. -/
theorem l4_ladyzhenskaya_gradient (u : H¹(ℝ^3)) :
    27 * (eLpNorm (baseRepresentative u) 4 volume).toReal ^ 8 ≤
      ‖wkpBaseCoordinateCLM u‖ ^ 2 * ‖Stationary.scalarGradientCLM u‖ ^ 6 := by
  have h := toReal_eLpNorm_four_pow_eight_le_H1 u
  rwa [← Stationary.norm_scalarGradientCLM_sq, ← pow_mul] at h

/-- Ladyzhenskaya's inequality in the norm `‖u‖₂ + ‖∇u‖₂`:
`65536 ‖u‖₄⁸ ≤ 27 (‖u‖₂ + ‖∇u‖₂)⁸`, that is `‖u‖₄² ≤ K (‖u‖₂ + ‖∇u‖₂)²` with
`K = 3^{3/4}/16 ≈ 0.1425`. This is the scalar form of Lemma 6 of Hou, Wang and Yang, whose
constant `3^{3/4}/(8π) ≈ 0.0907` comes from Talenti's sharp Sobolev constant; ours is larger by
the factor `π/2`. -/
theorem l4_ladyzhenskaya_add (u : H¹(ℝ^3)) :
    65536 * (eLpNorm (baseRepresentative u) 4 volume).toReal ^ 8 ≤
      27 * (‖wkpBaseCoordinateCLM u‖ + ‖Stationary.scalarGradientCLM u‖) ^ 8 := by
  have h := l4_ladyzhenskaya_gradient u
  set N := (eLpNorm (baseRepresentative u) 4 volume).toReal
  set a := ‖wkpBaseCoordinateCLM u‖
  set B := ‖Stationary.scalarGradientCLM u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  -- `a B³ ≤ (27/256) (a + B)⁴` by the arithmetic-geometric mean inequality for `3a, B, B, B`.
  have h₁ : 3 * a * B ≤ ((3 * a + B) / 2) ^ 2 := by nlinarith [sq_nonneg (3 * a - B)]
  have h₂ : (3 * a + B) / 2 * B ≤ (3 * (a + B) / 4) ^ 2 := by
    nlinarith [sq_nonneg ((3 * a + B) / 2 - B)]
  have h₃ : 3 * (a * B ^ 3) ≤ (3 * (a + B) / 4) ^ 4 := by
    have hp : 0 ≤ (3 * a + B) / 2 * B := by positivity
    calc 3 * (a * B ^ 3) = 3 * a * B * B ^ 2 := by ring
      _ ≤ ((3 * a + B) / 2) ^ 2 * B ^ 2 := by gcongr
      _ = ((3 * a + B) / 2 * B) ^ 2 := by ring
      _ ≤ ((3 * (a + B) / 4) ^ 2) ^ 2 := by gcongr
      _ = (3 * (a + B) / 4) ^ 4 := by ring
  have h₄ : 65536 * (a * B ^ 3) ^ 2 ≤ 729 * (a + B) ^ 8 := by
    have hq : 0 ≤ 3 * (a * B ^ 3) := by positivity
    have h₅ : (3 * (a * B ^ 3)) ^ 2 ≤ ((3 * (a + B) / 4) ^ 4) ^ 2 := by gcongr
    nlinarith [h₅]
  nlinarith [h₄, h]

/-- Weighted energy form of Ladyzhenskaya's inequality: for `s > 0` and `t ≥ 0` with
`t² s ≥ 1`, `‖u‖₄² ≤ t/4 (s² ‖u‖₂² + ‖∇u‖₂²)`. In the norm `c ‖u‖₂² + ‖∇u‖₂²` with `c = s²`
the best choice is `t = c^{-1/4}`; optimizing over `s` recovers
`‖u‖₄² ≤ 3^{-3/4} ‖u‖₂^{1/2} ‖∇u‖₂^{3/2}`. The arithmetic-geometric mean inequality for
`s² ‖u‖₂², ‖∂₀u‖₂², ‖∂₁u‖₂², ‖∂₂u‖₂²` bounds the square root of the product form. -/
theorem l4_ladyzhenskaya_weighted (u : H¹(ℝ^3)) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hst : 1 ≤ t ^ 2 * s) :
    (eLpNorm (baseRepresentative u) 4 volume).toReal ^ 2 ≤
      t / 4 * (s ^ 2 * ‖wkpBaseCoordinateCLM u‖ ^ 2 + ‖Stationary.scalarGradientCLM u‖ ^ 2) := by
  have h := toReal_eLpNorm_four_pow_four_le_H1 u
  rw [Fin.prod_univ_three] at h
  rw [Stationary.norm_scalarGradientCLM_sq, Fin.sum_univ_three]
  set N := (eLpNorm (baseRepresentative u) 4 volume).toReal
  set a := ‖wkpBaseCoordinateCLM u‖
  set b₀ := ‖wkpCoordinateCLM (singleDerivIndex 3 0) u‖
  set b₁ := ‖wkpCoordinateCLM (singleDerivIndex 3 1) u‖
  set b₂ := ‖wkpCoordinateCLM (singleDerivIndex 3 2) u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb₀ : 0 ≤ b₀ := norm_nonneg _
  have hb₁ : 0 ≤ b₁ := norm_nonneg _
  have hb₂ : 0 ≤ b₂ := norm_nonneg _
  set S := s ^ 2 * a ^ 2 + (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2)
  have h₁ : s * a * b₀ ≤ (s ^ 2 * a ^ 2 + b₀ ^ 2) / 2 := by nlinarith [sq_nonneg (s * a - b₀)]
  have h₂ : b₁ * b₂ ≤ (b₁ ^ 2 + b₂ ^ 2) / 2 := by nlinarith [sq_nonneg (b₁ - b₂)]
  have h₃ : s * a * b₀ * (b₁ * b₂) ≤ ((s * a * b₀ + b₁ * b₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (s * a * b₀ - b₁ * b₂)]
  have hp : 0 ≤ (s * a * b₀ + b₁ * b₂) / 2 := by positivity
  have h₄ : s * (a * (b₀ * b₁ * b₂)) ≤ (S / 4) ^ 2 := by
    calc s * (a * (b₀ * b₁ * b₂)) = s * a * b₀ * (b₁ * b₂) := by ring
      _ ≤ ((s * a * b₀ + b₁ * b₂) / 2) ^ 2 := h₃
      _ ≤ (S / 4) ^ 2 := pow_le_pow_left₀ hp (by simp only [S]; linarith) 2
  have hS : 0 ≤ S := by positivity
  have hN : (N ^ 2) ^ 2 ≤ (t / 4 * S) ^ 2 := by
    calc (N ^ 2) ^ 2 = N ^ 4 := by ring
      _ ≤ a * (b₀ * b₁ * b₂) := h
      _ ≤ t ^ 2 * s * (a * (b₀ * b₁ * b₂)) := by
          have hx : 0 ≤ a * (b₀ * b₁ * b₂) := by positivity
          nlinarith
      _ ≤ t ^ 2 * (S / 4) ^ 2 := by nlinarith [sq_nonneg t]
      _ = (t / 4 * S) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hN

namespace Stationary

/-- Componentwise `L⁴` inclusion of whole-space velocity fields, into the Hilbert product of
three `L⁴(ℝ³)` spaces. -/
def l4CLM : E →L[ℝ] PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 univ) :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ l4EmbeddingThree

/-- The components of `l4CLM v` are the `L⁴` classes of the components of `v`. -/
theorem l4CLM_apply (v : E) (i : Fin 3) : l4CLM v i = l4EmbeddingThree (v i) :=
  rfl

/-- The `L⁴` components represent the chosen representative of the velocity field. -/
theorem l4CLM_apply_ae (v : E) :
    ∀ᵐ x ∂volume, ∀ i, (l4CLM v i : ℝ^3 → ℝ) x = representative v x i := by
  exact Filter.Eventually.of_forall fun _ _ ↦ rfl

/-- Energy form of Ladyzhenskaya's inequality for velocity fields: the `L⁴` inclusion of
`H¹(ℝ³)³` has norm at most `1/2`. -/
theorem norm_l4CLM_apply_le (v : E) : ‖l4CLM v‖ ≤ ‖v‖ / 2 := by
  have hsq : ‖l4CLM v‖ ^ 2 ≤ (‖v‖ / 2) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, div_pow, PiLp.norm_sq_eq_of_L2, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h := norm_l4EmbeddingThree_apply_le (v i)
    rw [l4CLM_apply]
    calc ‖l4EmbeddingThree (v i)‖ ^ 2 ≤ (‖v i‖ / 2) ^ 2 := by gcongr
      _ = ‖v i‖ ^ 2 / 2 ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Weighted energy form for velocity fields: for `s > 0` and `t ≥ 0` with `t² s ≥ 1`,
`‖l4CLM v‖² ≤ t/4 (s² ‖v‖₂² + ‖∇v‖₂²)`. -/
theorem norm_l4CLM_apply_sq_le_weighted (v : E) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hst : 1 ≤ t ^ 2 * s) :
    ‖l4CLM v‖ ^ 2 ≤ t / 4 * (s ^ 2 * ‖massCLM v‖ ^ 2 + ‖gradientCLM v‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc ∑ k, ‖l4CLM v k‖ ^ 2
      ≤ ∑ k, t / 4 * (s ^ 2 * ‖wkpBaseCoordinateCLM (v k)‖ ^ 2 +
          ‖scalarGradientCLM (v k)‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [l4CLM_apply, norm_l4EmbeddingThree_apply]
        exact l4_ladyzhenskaya_weighted (v k) hs ht hst
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl

/-- The `L²` norm of `|f|²` is the square of the `L⁴` norm of `f`. -/
private theorem eLpNorm_norm_rpow_two {F : Type*} [NormedAddCommGroup F] (f : ℝ^3 → F)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x ↦ ‖f x‖ ^ (2 : ℝ)) 2 volume = eLpNorm f 4 volume ^ (2 : ℝ) := by
  rw [eLpNorm_norm_rpow f hf (by norm_num)]
  norm_num

/-- The `L⁴` norm of the Euclidean length of a velocity field is at most the Hilbert-product
norm of its `L⁴` components: `‖|v|‖₄² = ‖Σₖ vₖ²‖₂ ≤ Σₖ ‖vₖ‖₄²` by Minkowski's inequality. -/
theorem toReal_eLpNorm_representative_le (v : E) :
    (eLpNorm (representative v) 4 volume).toReal ≤ ‖l4CLM v‖ := by
  have hrep (i : Fin 3) : MemLp (fun x ↦ representative v x i) 4 volume := by
    have h := Lp.memLp (l4CLM v i)
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h.ae_eq (by filter_upwards [l4CLM_apply_ae v] with x hx using hx i)
  have hnorm (i : Fin 3) :
      eLpNorm (fun x ↦ representative v x i) 4 volume = ENNReal.ofReal ‖l4CLM v i‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    have h : eLpNorm (l4CLM v i : ℝ^3 → ℝ) 4 (domainMeasure 3 univ) =
        eLpNorm (l4CLM v i : ℝ^3 → ℝ) 4 volume := by
      simp [domainMeasure]
    rw [h]
    exact (eLpNorm_congr_ae (by filter_upwards [l4CLM_apply_ae v] with x hx using hx i)).symm
  have hrepm : AEStronglyMeasurable (representative v) volume :=
    (memLp_representative v).aestronglyMeasurable
  have hpt : (fun x ↦ ‖representative v x‖ ^ (2 : ℝ)) =
      ∑ i : Fin 3, fun x ↦ ‖representative v x i‖ ^ (2 : ℝ) := by
    funext x
    rw [Finset.sum_apply, Real.rpow_two, EuclideanSpace.norm_sq_eq]
    simp only [Real.rpow_two]
  have hmain : eLpNorm (representative v) 4 volume ^ (2 : ℝ) ≤
      ENNReal.ofReal (‖l4CLM v‖ ^ 2) := by
    rw [← eLpNorm_norm_rpow_two _ hrepm, hpt]
    calc eLpNorm (∑ i : Fin 3, fun x ↦ ‖representative v x i‖ ^ (2 : ℝ)) 2 volume
        ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ ‖representative v x i‖ ^ (2 : ℝ)) 2 volume :=
          eLpNorm_sum_le (by norm_num)
      _ = ∑ i : Fin 3, ENNReal.ofReal (‖l4CLM v i‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [eLpNorm_norm_rpow_two _ (hrep i).aestronglyMeasurable, hnorm i, ENNReal.rpow_two,
            ENNReal.ofReal_pow (norm_nonneg _)]
      _ = ENNReal.ofReal (‖l4CLM v‖ ^ 2) := by
          rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sq_nonneg _), Real.rpow_two] at h2
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- Energy form of Ladyzhenskaya's inequality for velocity fields:
`‖v‖_{L⁴(ℝ³; ℝ³)} ≤ ½ ‖v‖_E`. -/
theorem toReal_eLpNorm_representative_le_half (v : E) :
    (eLpNorm (representative v) 4 volume).toReal ≤ ‖v‖ / 2 :=
  (toReal_eLpNorm_representative_le v).trans (norm_l4CLM_apply_le v)

/-- The weak gradient matrix `(∂ᵢvₖ)` of a whole-space velocity field as a Hilbert tuple
indexed by `(k, i)`. -/
def gradientCoordinates :
    E →L[ℝ] PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 univ) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 univ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun ki ↦ (wkpCoordinateCLM (singleDerivIndex 3 ki.2)).comp
        (PiLp.proj 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) ki.1))

/-- The `(k, i)` coordinate of the gradient matrix is the weak derivative `∂ᵢvₖ`. -/
theorem gradientCoordinates_apply (v : E) (ki : Fin 3 × Fin 3) :
    gradientCoordinates v ki = wkpCoordinateCLM (singleDerivIndex 3 ki.2) (v ki.1) :=
  rfl

/-- The gradient matrix has the full Frobenius gradient norm. -/
theorem norm_gradientCoordinates (v : E) : ‖gradientCoordinates v‖ = ‖gradientCLM v‖ := by
  have hsq : ‖gradientCoordinates v‖ ^ 2 = ‖gradientCLM v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- The convection trilinear form `b(u, v, w) = ∫ (u · ∇) v · w = Σₖ Σᵢ ∫ uᵢ ∂ᵢvₖ wₖ` on the
energy space `H¹(ℝ³)³`. -/
def convectionTrilinear : PDE.Analysis.ContinuousTrilinearForm E E E :=
  PDE.Analysis.ContinuousTrilinearForm.restrict ContinuousLinearMap.transportPairing
    l4CLM gradientCoordinates l4CLM

/-- Coordinate form of the convection form in the `L⁴` and `L²` coordinates. -/
theorem convectionTrilinear_apply (u v w : E) :
    convectionTrilinear u v w = ∑ k : Fin 3, ∑ i : Fin 3, ∫ x, (l4CLM u i : ℝ^3 → ℝ) x *
      (gradientCoordinates v (k, i) : ℝ^3 → ℝ) x * (l4CLM w k : ℝ^3 → ℝ) x
        ∂domainMeasure 3 univ := by
  rw [convectionTrilinear, PDE.Analysis.ContinuousTrilinearForm.restrict_apply,
    ContinuousLinearMap.transportPairing_eq_integral]

/-- A product of two `L⁴` functions and one `L²` function is integrable. -/
private theorem integrable_mul_mul_of_memLp {μ : Measure (ℝ^3)} {f g h : ℝ^3 → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 2 μ) (hh : MemLp h 4 μ) :
    Integrable (fun x ↦ f x * g x * h x) μ := by
  have hfh : MemLp (fun x ↦ f x * h x) 2 μ := hf.fun_mul hh
  refine (hfh.integrable_mul hg).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.mul_apply]
  ring

/-- The `(k, i)` term of the convection form with the chosen representatives. -/
private theorem integral_l4CLM_mul_gradient_mul (u v w : E) (k i : Fin 3) :
    Integrable (fun x ↦ representative u x i * gradientRepresentative v x k i *
      representative w x k) volume ∧
    ∫ x, (l4CLM u i : ℝ^3 → ℝ) x * (gradientCoordinates v (k, i) : ℝ^3 → ℝ) x *
        (l4CLM w k : ℝ^3 → ℝ) x ∂domainMeasure 3 univ =
      ∫ x, representative u x i * gradientRepresentative v x k i * representative w x k := by
  have hμ : ∀ {p : ℝ≥0∞} (F : DerivLp 3 p univ), MemLp (F : ℝ^3 → ℝ) p volume := fun F ↦ by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp F
  have hae : (fun x ↦ (l4CLM u i : ℝ^3 → ℝ) x * (gradientCoordinates v (k, i) : ℝ^3 → ℝ) x *
      (l4CLM w k : ℝ^3 → ℝ) x) =ᵐ[volume] fun x ↦ representative u x i *
        gradientRepresentative v x k i * representative w x k := by
    filter_upwards [l4CLM_apply_ae u, l4CLM_apply_ae w] with x hu hw
    rw [hu i, hw k]
    rfl
  have hint := integrable_mul_mul_of_memLp (hμ (l4CLM u i)) (hμ (gradientCoordinates v (k, i)))
    (hμ (l4CLM w k))
  refine ⟨hint.congr hae, ?_⟩
  have hd : domainMeasure 3 (univ : Set (ℝ^3)) = volume := by simp [domainMeasure]
  calc _ = ∫ x, (l4CLM u i : ℝ^3 → ℝ) x * (gradientCoordinates v (k, i) : ℝ^3 → ℝ) x *
        (l4CLM w k : ℝ^3 → ℝ) x := by simp only [hd]
    _ = _ := integral_congr_ae hae

/-- The convection form is the Lebesgue integral of `Σₖ Σᵢ uᵢ ∂ᵢvₖ wₖ`, written with the
chosen representatives of `u`, `w` and of the weak gradient of `v`; the integrand is
integrable (`integrable_convectionDensity`). -/
theorem convectionTrilinear_eq_integral (u v w : E) :
    convectionTrilinear u v w = ∫ x, ∑ k : Fin 3, ∑ i : Fin 3,
      representative u x i * gradientRepresentative v x k i * representative w x k := by
  rw [convectionTrilinear_apply, integral_finsetSum _ fun k _ ↦
    integrable_finsetSum _ fun i _ ↦ (integral_l4CLM_mul_gradient_mul u v w k i).1]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ (integral_l4CLM_mul_gradient_mul u v w k i).1]
  exact Finset.sum_congr rfl fun i _ ↦ (integral_l4CLM_mul_gradient_mul u v w k i).2

/-- The convection density `Σₖ Σᵢ uᵢ ∂ᵢvₖ wₖ` of three `H¹(ℝ³)³` fields is integrable. -/
theorem integrable_convectionDensity (u v w : E) :
    Integrable (fun x ↦ ∑ k : Fin 3, ∑ i : Fin 3,
      representative u x i * gradientRepresentative v x k i * representative w x k) volume :=
  integrable_finsetSum _ fun k _ ↦
    integrable_finsetSum _ fun i _ ↦ (integral_l4CLM_mul_gradient_mul u v w k i).1

/-- Hölder's inequality in the `L⁴`, `L²`, `L⁴` coordinates:
`|b(u, v, w)| ≤ ‖u‖_{L⁴} ‖∇v‖_{L²} ‖w‖_{L⁴}`. -/
theorem norm_convectionTrilinear_le_l4 (u v w : E) :
    ‖convectionTrilinear u v w‖ ≤ ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖l4CLM w‖ := by
  have h := ContinuousLinearMap.norm_transportPairing_le (l4CLM u) (gradientCoordinates v)
    (l4CLM w)
  rw [norm_gradientCoordinates] at h
  simpa only [convectionTrilinear, PDE.Analysis.ContinuousTrilinearForm.restrict_apply]
    using h

/-- `|b(u, v, w)| ≤ ¼ ‖u‖_E ‖∇v‖_{L²} ‖w‖_E`. -/
theorem norm_convectionTrilinear_le_gradient (u v w : E) :
    ‖convectionTrilinear u v w‖ ≤ 1 / 4 * ‖u‖ * ‖gradientCLM v‖ * ‖w‖ := by
  calc ‖convectionTrilinear u v w‖ ≤ ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖l4CLM w‖ :=
        norm_convectionTrilinear_le_l4 u v w
    _ ≤ ‖u‖ / 2 * ‖gradientCLM v‖ * (‖w‖ / 2) := by
        gcongr
        exacts [norm_l4CLM_apply_le u, norm_l4CLM_apply_le w]
    _ = 1 / 4 * ‖u‖ * ‖gradientCLM v‖ * ‖w‖ := by ring

/-- `|b(u, v, w)| ≤ ½ ‖u‖_{L⁴} ‖∇v‖_{L²} ‖w‖_E`. -/
theorem norm_convectionTrilinear_le_coefficient (u v w : E) :
    ‖convectionTrilinear u v w‖ ≤ 1 / 2 * ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖w‖ := by
  calc ‖convectionTrilinear u v w‖ ≤ ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖l4CLM w‖ :=
        norm_convectionTrilinear_le_l4 u v w
    _ ≤ ‖l4CLM u‖ * ‖gradientCLM v‖ * (‖w‖ / 2) := by
        gcongr
        exact norm_l4CLM_apply_le w
    _ = 1 / 2 * ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖w‖ := by ring

/-- **Trilinear bound.** `|b(u, v, w)| ≤ ¼ ‖u‖_E ‖v‖_E ‖w‖_E` on `H¹(ℝ³)³`. -/
theorem norm_convectionTrilinear_le (u v w : E) :
    ‖convectionTrilinear u v w‖ ≤ 1 / 4 * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc ‖convectionTrilinear u v w‖ ≤ 1 / 4 * ‖u‖ * ‖gradientCLM v‖ * ‖w‖ :=
        norm_convectionTrilinear_le_gradient u v w
    _ ≤ 1 / 4 * ‖u‖ * ‖v‖ * ‖w‖ := by
        gcongr
        exact norm_gradientCLM_le v

/-- Weighted trilinear bound in the norm `‖h‖_s² = s² ‖h‖₂² + ‖∇h‖₂²`: for `s > 0` and `t ≥ 0`
with `t² s ≥ 1`, `|b(u, v, w)| ≤ t/4 ‖u‖_s ‖∇v‖₂ ‖w‖_s`. -/
theorem norm_convectionTrilinear_le_weighted (u v w : E) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hst : 1 ≤ t ^ 2 * s) :
    ‖convectionTrilinear u v w‖ ≤ t / 4 *
      Real.sqrt (s ^ 2 * ‖massCLM u‖ ^ 2 + ‖gradientCLM u‖ ^ 2) * ‖gradientCLM v‖ *
        Real.sqrt (s ^ 2 * ‖massCLM w‖ ^ 2 + ‖gradientCLM w‖ ^ 2) := by
  have hu' : ‖l4CLM u‖ ≤ Real.sqrt (t / 4) *
      Real.sqrt (s ^ 2 * ‖massCLM u‖ ^ 2 + ‖gradientCLM u‖ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (norm_l4CLM_apply_sq_le_weighted u hs ht hst)
  have hw' : ‖l4CLM w‖ ≤ Real.sqrt (t / 4) *
      Real.sqrt (s ^ 2 * ‖massCLM w‖ ^ 2 + ‖gradientCLM w‖ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (norm_l4CLM_apply_sq_le_weighted w hs ht hst)
  have h4 : Real.sqrt (t / 4) * Real.sqrt (t / 4) = t / 4 := Real.mul_self_sqrt (by positivity)
  calc _ ≤ ‖l4CLM u‖ * ‖gradientCLM v‖ * ‖l4CLM w‖ := norm_convectionTrilinear_le_l4 u v w
    _ ≤ (Real.sqrt (t / 4) * Real.sqrt (s ^ 2 * ‖massCLM u‖ ^ 2 + ‖gradientCLM u‖ ^ 2)) *
          ‖gradientCLM v‖ *
          (Real.sqrt (t / 4) * Real.sqrt (s ^ 2 * ‖massCLM w‖ ^ 2 + ‖gradientCLM w‖ ^ 2)) := by
        gcongr
    _ = _ := by
        rw [show ∀ x y z w : ℝ, (x * y) * z * (x * w) = (x * x) * y * z * w from
          fun x y z w ↦ by ring, h4]

/-- The convection form is bounded with constant `1/4`. -/
theorem convectionTrilinear_isBoundedBy : convectionTrilinear.IsBoundedBy (1 / 4) :=
  norm_convectionTrilinear_le

end Stationary

end NavierStokes
