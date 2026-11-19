/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Product
import PDE.FDeriv.PartialDeriv.Smooth

/-!
# The Laplacian of a localized mixed quartic

For a smooth cutoff `χ` on the plane with `χ(0) = 1`, the localized quartic
`Q = (x₁ x₂³ / 6) χ` has `ΔQ = x₁ x₂ + O(|x|³)` and `∂₁ΔQ = x₂ + O(|x|²)` at the origin. Only
`χ(0) = 1` and the smoothness of `χ` enter: by the product rule
`ΔQ - x₁ x₂ = x₁ x₂ (χ - 1) + (x₂³/3) ∂₁χ + x₁ x₂² ∂₂χ + (x₁ x₂³/6) Δχ`, and
`∂₁ΔQ = Δ(∂₁Q)` with `∂₁Q = (x₂³/6) χ + (x₁ x₂³/6) ∂₁χ`.

This is the corrector of the Poisson error and of the first nonlinear mode in Chen and Hou,
Part II, Appendix C.4, (C.19), and Part I, Section 4.2.1, (4.11). There `χ` is a product
`κ(x₁; ν₁, ν₂) κ(x₂; ν₁, ν₂)` of the cutoffs of Part I, Appendix C.1.1, (C.6), as in (C.9).

## Main results

* `PDE.laplacian_localizedQuartic_sub_isBigO`
* `PDE.partialDeriv_laplacian_localizedQuartic_sub_isBigO`

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2.1, (4.11), and
  Appendix C.1.1, (C.6) and (C.9).
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.4, (C.19).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology ContDiff

namespace PDE

variable {χ : ℝ^2 → ℝ}

/-- A coordinate of the plane is smooth. -/
private theorem contDiff_coord (i : Fin 2) : ContDiff ℝ ∞ (fun y : ℝ^2 ↦ y i) :=
  (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).contDiff

/-- A coordinate is `O(|x|)` at the origin. -/
private theorem isBigO_coord (i : Fin 2) :
    (fun x : ℝ^2 ↦ x i) =O[𝓝 0] fun x ↦ ‖x‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun x ↦ by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i)

/-- A continuous function is `O(1)` at the origin. -/
private theorem isBigO_one_of_continuous {f : ℝ^2 → ℝ} (hf : Continuous f) :
    f =O[𝓝 0] fun _ ↦ (1 : ℝ) :=
  (hf.tendsto 0).isBigO_one ℝ

/-- For a smooth `χ` with `χ(0) = 1`, `χ - 1 = O(|x|)` at the origin. -/
private theorem isBigO_sub_one (hχ : ContDiff ℝ ∞ χ) (h0 : χ 0 = 1) :
    (fun x ↦ χ x - 1) =O[𝓝 0] fun x ↦ ‖x‖ := by
  have h := ((hχ.differentiable (by simp)) 0).hasFDerivAt.isBigO_sub
  rw [h0] at h
  simpa using h.norm_right

/-- The quartic `x₁ x₂³ / 6` as a product. -/
private noncomputable def quartic : ℝ^2 → ℝ := fun x ↦ 1 / 6 * (x 0 * (x 1 * x 1 * x 1))

/-- The quartic `x₁ x₂³ / 6` is smooth. -/
private theorem contDiff_quartic : ContDiff ℝ ∞ quartic :=
  contDiff_const.mul ((contDiff_coord 0).mul (((contDiff_coord 1).mul (contDiff_coord 1)).mul
    (contDiff_coord 1)))

/-- `∂₁ (x₁ x₂³ / 6) = x₂³ / 6`. -/
private theorem partialDeriv_zero_quartic :
    ∂[0] quartic = fun x ↦ 1 / 6 * (x 1 * x 1 * x 1) := by
  funext y
  have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) y
  unfold quartic
  simp (disch := fun_prop) only [partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
  simp

/-- `∂₂ (x₁ x₂³ / 6) = x₁ x₂² / 2`. -/
private theorem partialDeriv_one_quartic :
    ∂[1] quartic = fun x ↦ 1 / 2 * (x 0 * (x 1 * x 1)) := by
  funext y
  have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) y
  unfold quartic
  simp (disch := fun_prop) only [partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
  simp
  ring

/-- `Δ (x₁ x₂³ / 6) = x₁ x₂`. -/
private theorem laplacian_quartic (x : ℝ^2) : laplacian quartic x = x 0 * x 1 := by
  have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) x
  simp only [laplacian, Fin.sum_univ_two]
  rw [show (fun y ↦ (∂[0] quartic) y) = ∂[0] quartic from rfl,
    show (fun y ↦ (∂[1] quartic) y) = ∂[1] quartic from rfl, partialDeriv_zero_quartic,
    partialDeriv_one_quartic]
  simp (disch := fun_prop) only [partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
  simp
  ring

/-- At the origin, the product of an `O(|x|ᵃ)` and an `O(|x|ᵇ)` function is `O(|x|ᵃ⁺ᵇ)`. -/
private theorem isBigO_mul_pow {f g : ℝ^2 → ℝ} {a b : ℕ}
    (hf : f =O[𝓝 0] fun x ↦ ‖x‖ ^ a) (hg : g =O[𝓝 0] fun x ↦ ‖x‖ ^ b) :
    (fun x ↦ f x * g x) =O[𝓝 0] fun x ↦ ‖x‖ ^ (a + b) := by
  simpa [pow_add] using hf.mul hg

/-- For `b ≤ a`, an `O(|x|ᵃ)` function at the origin is `O(|x|ᵇ)`. -/
private theorem isBigO_pow_of_le {f : ℝ^2 → ℝ} {a b : ℕ} (hab : b ≤ a)
    (hf : f =O[𝓝 0] fun x ↦ ‖x‖ ^ a) : f =O[𝓝 0] fun x ↦ ‖x‖ ^ b := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_norm_pow_norm_pow h).isBigO
  · exact h ▸ hf

/-- A coordinate is `O(|x|¹)` at the origin. -/
private theorem isBigO_coord_pow (i : Fin 2) :
    (fun x : ℝ^2 ↦ x i) =O[𝓝 0] fun x ↦ ‖x‖ ^ 1 := by
  simpa using isBigO_coord i

/-- A continuous function is `O(|x|⁰)` at the origin. -/
private theorem isBigO_continuous_pow {f : ℝ^2 → ℝ} (hf : Continuous f) :
    f =O[𝓝 0] fun x ↦ ‖x‖ ^ 0 := by
  simpa using isBigO_one_of_continuous hf

/-- The localized quartic `x₁ x₂³ / 6 · χ` is the product of `quartic` and `χ`. -/
private theorem localizedQuartic_eq (χ : ℝ^2 → ℝ) :
    (fun y : ℝ^2 ↦ y 0 * y 1 ^ 3 / 6 * χ y) = fun y ↦ quartic y * χ y := by
  funext y
  simp only [quartic]
  ring

/-- **`ΔQ = x₁ x₂ + O(|x|³)`** for the localized quartic `Q = (x₁ x₂³/6) χ` with a smooth cutoff
`χ`, `χ(0) = 1`. -/
theorem laplacian_localizedQuartic_sub_isBigO (hχ : ContDiff ℝ ∞ χ) (h0 : χ 0 = 1) :
    (fun x : ℝ^2 ↦ laplacian (fun y ↦ y 0 * y 1 ^ 3 / 6 * χ y) x - x 0 * x 1) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 3 := by
  have hexp : ∀ x : ℝ^2, laplacian (fun y ↦ y 0 * y 1 ^ 3 / 6 * χ y) x - x 0 * x 1 =
      x 0 * x 1 * (χ x - 1) + 2 * (1 / 6 * (x 1 * x 1 * x 1) * (∂[0] χ) x +
        1 / 2 * (x 0 * (x 1 * x 1)) * (∂[1] χ) x) + quartic x * laplacian χ x := by
    intro x
    rw [localizedQuartic_eq, laplacian_mul (contDiff_quartic.contDiffAt.of_le (by simp))
      ((hχ.of_le (by simp)).contDiffAt), laplacian_quartic, Fin.sum_univ_two,
      partialDeriv_zero_quartic, partialDeriv_one_quartic]
    ring
  simp_rw [hexp]
  have c0 := isBigO_coord_pow 0
  have c1 := isBigO_coord_pow 1
  have hχ1 : (fun x ↦ χ x - 1) =O[𝓝 0] fun x ↦ ‖x‖ ^ 1 := by
    simpa using isBigO_sub_one hχ h0
  have d0 := isBigO_continuous_pow ((hχ.partialDeriv (k := ∞) 0).continuous)
  have d1 := isBigO_continuous_pow ((hχ.partialDeriv (k := ∞) 1).continuous)
  have dl := isBigO_continuous_pow (contDiff_laplacian_coord hχ).continuous
  have k1 : (fun x : ℝ^2 ↦ (1 / 6 : ℝ)) =O[𝓝 0] fun x ↦ ‖x‖ ^ 0 :=
    isBigO_continuous_pow continuous_const
  have k2 : (fun x : ℝ^2 ↦ (1 / 2 : ℝ)) =O[𝓝 0] fun x ↦ ‖x‖ ^ 0 :=
    isBigO_continuous_pow continuous_const
  have t1 := isBigO_mul_pow (isBigO_mul_pow c0 c1) hχ1
  have t2 := isBigO_mul_pow (isBigO_mul_pow k1 (isBigO_mul_pow (isBigO_mul_pow c1 c1) c1)) d0
  have t3 := isBigO_mul_pow (isBigO_mul_pow k2 (isBigO_mul_pow c0 (isBigO_mul_pow c1 c1))) d1
  have t4 := isBigO_mul_pow (isBigO_mul_pow k1 (isBigO_mul_pow c0
    (isBigO_mul_pow (isBigO_mul_pow c1 c1) c1))) dl
  exact (t1.add ((t2.add t3).const_mul_left 2)).add (isBigO_pow_of_le (by norm_num) t4)

/-- **`∂₁ΔQ = x₂ + O(|x|²)`** for the localized quartic `Q = (x₁ x₂³/6) χ` with a smooth cutoff
`χ`, `χ(0) = 1`. -/
theorem partialDeriv_laplacian_localizedQuartic_sub_isBigO (hχ : ContDiff ℝ ∞ χ) (h0 : χ 0 = 1) :
    (fun x : ℝ^2 ↦ (∂[0] (laplacian (fun y ↦ y 0 * y 1 ^ 3 / 6 * χ y))) x - x 1) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 2 := by
  set χ₀ := ∂[0] χ with hχ₀
  have sχ₀ : ContDiff ℝ ∞ χ₀ := hχ.partialDeriv (k := ∞) 0
  set b : ℝ^2 → ℝ := fun x ↦ 1 / 6 * (x 1 * x 1 * x 1) with hb
  have sb : ContDiff ℝ ∞ b :=
    contDiff_const.mul (((contDiff_coord 1).mul (contDiff_coord 1)).mul (contDiff_coord 1))
  have hb0 : ∂[0] b = fun _ ↦ 0 := by
    funext y
    have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) y
    simp (disch := fun_prop) only [hb, partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
    simp
  have hb1 : ∂[1] b = fun x ↦ 1 / 2 * (x 1 * x 1) := by
    funext y
    have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) y
    simp (disch := fun_prop) only [hb, partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
    simp
    ring
  have hlb : ∀ x : ℝ^2, laplacian b x = x 1 := by
    intro x
    simp only [laplacian, Fin.sum_univ_two]
    rw [show (fun y ↦ (∂[0] b) y) = ∂[0] b from rfl, show (fun y ↦ (∂[1] b) y) = ∂[1] b from rfl,
      hb0, hb1]
    have dc := fun i : Fin 2 ↦ (contDiff_coord i).differentiable (by simp) x
    simp (disch := fun_prop) only [partialDeriv_mul, partialDeriv_coord, partialDeriv_const]
    simp
    ring
  have sQ : ContDiff ℝ ∞ (fun y ↦ quartic y * χ y) := contDiff_quartic.mul hχ
  have hQ0 : ∂[0] (fun y ↦ quartic y * χ y) = fun y ↦ b y * χ y + quartic y * χ₀ y := by
    funext y
    rw [partialDeriv_mul ((contDiff_quartic.differentiable (by simp)) y)
      ((hχ.differentiable (by simp)) y), partialDeriv_zero_quartic]
  have hexp : ∀ x : ℝ^2,
      (∂[0] (laplacian (fun y ↦ y 0 * y 1 ^ 3 / 6 * χ y))) x - x 1 =
        x 1 * (χ x - 1) + 2 * (1 / 2 * (x 1 * x 1) * (∂[1] χ) x) + b x * laplacian χ x +
          (x 0 * x 1 * χ₀ x + 2 * (1 / 6 * (x 1 * x 1 * x 1) * (∂[0] χ₀) x +
            1 / 2 * (x 0 * (x 1 * x 1)) * (∂[1] χ₀) x) + quartic x * laplacian χ₀ x) := by
    intro x
    rw [localizedQuartic_eq, ← laplacian_partialDeriv_eq sQ 0 x]
    change laplacian (∂[0] (fun y ↦ quartic y * χ y)) x - x 1 = _
    rw [hQ0, laplacian_add _ _ x ((sb.mul hχ).contDiffAt.of_le (by simp))
      ((contDiff_quartic.mul sχ₀).contDiffAt.of_le (by simp)),
      laplacian_mul (sb.contDiffAt.of_le (by simp)) ((hχ.of_le (by simp)).contDiffAt),
      laplacian_mul (contDiff_quartic.contDiffAt.of_le (by simp))
        ((sχ₀.of_le (by simp)).contDiffAt),
      hlb, laplacian_quartic, Fin.sum_univ_two, Fin.sum_univ_two, hb0, hb1,
      partialDeriv_zero_quartic, partialDeriv_one_quartic]
    ring
  simp_rw [hexp]
  have c0 := isBigO_coord_pow 0
  have c1 := isBigO_coord_pow 1
  have hχ1 : (fun x ↦ χ x - 1) =O[𝓝 0] fun x ↦ ‖x‖ ^ 1 := by
    simpa using isBigO_sub_one hχ h0
  have d1 := isBigO_continuous_pow ((hχ.partialDeriv (k := ∞) 1).continuous)
  have dl := isBigO_continuous_pow (contDiff_laplacian_coord hχ).continuous
  have e0 := isBigO_continuous_pow sχ₀.continuous
  have e00 := isBigO_continuous_pow ((sχ₀.partialDeriv (k := ∞) 0).continuous)
  have e01 := isBigO_continuous_pow ((sχ₀.partialDeriv (k := ∞) 1).continuous)
  have el := isBigO_continuous_pow (contDiff_laplacian_coord sχ₀).continuous
  have k1 : (fun x : ℝ^2 ↦ (1 / 6 : ℝ)) =O[𝓝 0] fun x ↦ ‖x‖ ^ 0 :=
    isBigO_continuous_pow continuous_const
  have k2 : (fun x : ℝ^2 ↦ (1 / 2 : ℝ)) =O[𝓝 0] fun x ↦ ‖x‖ ^ 0 :=
    isBigO_continuous_pow continuous_const
  have u1 := isBigO_mul_pow c1 hχ1
  have u2 := isBigO_mul_pow (isBigO_mul_pow k2 (isBigO_mul_pow c1 c1)) d1
  have u3 := isBigO_mul_pow (isBigO_mul_pow k1 (isBigO_mul_pow (isBigO_mul_pow c1 c1) c1)) dl
  have u4 := isBigO_mul_pow (isBigO_mul_pow c0 c1) e0
  have u5 := isBigO_mul_pow (isBigO_mul_pow k1 (isBigO_mul_pow (isBigO_mul_pow c1 c1) c1)) e00
  have u6 := isBigO_mul_pow (isBigO_mul_pow k2 (isBigO_mul_pow c0 (isBigO_mul_pow c1 c1))) e01
  have u7 := isBigO_mul_pow (isBigO_mul_pow k1 (isBigO_mul_pow c0
    (isBigO_mul_pow (isBigO_mul_pow c1 c1) c1))) el
  exact ((u1.add (u2.const_mul_left 2)).add (isBigO_pow_of_le (by norm_num) u3)).add
    ((u4.add ((isBigO_pow_of_le (by norm_num) u5).add (isBigO_pow_of_le (by norm_num) u6)
      |>.const_mul_left 2)).add (isBigO_pow_of_le (by norm_num) u7))

end PDE
