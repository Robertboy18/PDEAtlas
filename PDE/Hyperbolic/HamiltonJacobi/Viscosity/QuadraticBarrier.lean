/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Comparison
import Mathlib.Analysis.Normed.Operator.Prod
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth quadratic penalties on space × time

The product norm on `E × ℝ` is a maximum norm, so its square need not be
smooth. We use `Q(x,t) = ‖x‖² + t²`. This quadratic dominates the squared
product norm and is smooth because `E` has an inner product.

The doubled penalty combines `Q(z-w)/(2ε)`, a small localization
`α(Q(z)+Q(w))`, and reciprocal time barriers `a/(T-zₜ) + a/(T-wₜ)`.
Its spatial derivatives agree up to the localization terms; its time
derivatives leave two reciprocal terms after cancellation. These terms are
positive when `0 < a` and both contact times differ from `T`.
The reciprocal terms are `C¹` at every contact away from their poles, which
makes the penalty admissible for the local `C¹` viscosity tests.
These calculations do not require finite dimensionality.

The penalty is a variant of the function `Φ` in (5) of Evans, §10.2, which subtracts
`(|x-y|²+(t-s)²)/ε²`, `ε(|x|²+|y|²)` and `λ(t+s)`. The reciprocal terms replace `λ(t+s)`; they
come from the proof of his Lemma (Extrema at a terminal time).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, Lemma (Extrema at a terminal time) and its proof,
  and equation (5) in the proof of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The smooth quadratic `‖x‖² + t²` on space × time. -/
def quadraticSize (z : E × ℝ) : ℝ := ‖z.1‖ ^ 2 + z.2 ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The spacetime quadratic is nonnegative. -/
theorem quadraticSize_nonneg (z : E × ℝ) : 0 ≤ quadraticSize z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The spacetime quadratic controls the spatial norm squared. -/
theorem norm_fst_sq_le_quadraticSize (z : E × ℝ) : ‖z.1‖ ^ 2 ≤ quadraticSize z :=
  le_add_of_nonneg_right (sq_nonneg _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The smooth quadratic dominates the square of the maximum product norm. -/
theorem norm_sq_le_quadraticSize (z : E × ℝ) : ‖z‖ ^ 2 ≤ quadraticSize z := by
  rw [Prod.norm_def, quadraticSize]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Quadratic separation controls squared distance in the product metric. -/
theorem dist_sq_le_quadraticSize_sub (z w : E × ℝ) :
    dist z w ^ 2 ≤ quadraticSize (z - w) := by
  rw [dist_eq_norm]
  exact norm_sq_le_quadraticSize (z - w)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The spacetime quadratic is continuous in the product topology. -/
theorem continuous_quadraticSize : Continuous (quadraticSize (E := E)) :=
  (continuous_fst.norm.pow 2).add (continuous_snd.pow 2)

omit [CompleteSpace E] in
/-- The sum of the squared spatial norm and squared time is smooth, even
though the maximum product norm itself need not be differentiable. -/
theorem contDiff_quadraticSize {n : ℕ∞ω} :
    ContDiff ℝ n (quadraticSize (E := E)) :=
  (contDiff_fst.norm_sq ℝ).add (contDiff_snd.pow 2)

omit [CompleteSpace E] in
/-- The quadratic penalty has a derivative that tends to zero at its center.
The product norm gives the uniform bound needed when smoothing a contact. -/
theorem norm_fderiv_quadraticSize_le (z : E × ℝ) :
    ‖fderiv ℝ (quadraticSize (E := E)) z‖ ≤ 4 * ‖z‖ := by
  have hd : HasFDerivAt (quadraticSize (E := E))
      ((2 : ℝ) • (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        (2 : ℝ) • (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ)) z := by
    simpa only [quadraticSize, Real.norm_eq_abs, sq_abs, two_smul] using!
      (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).norm_sq.add (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq
  have hfst : ‖(innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ)‖ ≤ ‖z.1‖ := by
    calc
      _ ≤ ‖innerSL ℝ z.1‖ * ‖ContinuousLinearMap.fst ℝ E ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖z.1‖ * 1 := by
        rw [innerSL_apply_norm]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le ℝ E ℝ) (norm_nonneg _)
      _ = ‖z.1‖ := mul_one _
  have hsnd : ‖(innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ)‖ ≤ ‖z.2‖ := by
    calc
      _ ≤ ‖innerSL ℝ z.2‖ * ‖ContinuousLinearMap.snd ℝ E ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖z.2‖ * 1 := by
        rw [innerSL_apply_norm]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ E ℝ) (norm_nonneg _)
      _ = ‖z.2‖ := mul_one _
  rw [hd.fderiv]
  calc
    _ ≤ ‖(2 : ℝ) • (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ)‖ +
        ‖(2 : ℝ) • (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ)‖ := by
      simpa only using! norm_add_le ((2 : ℝ) • (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ))
        ((2 : ℝ) • (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ))
    _ ≤ 2 * ‖(innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ)‖ +
        2 * ‖(innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ)‖ := by
      apply add_le_add
      · simpa only [Real.norm_ofNat] using! ContinuousLinearMap.opNorm_smul_le (2 : ℝ)
            ((innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E ℝ))
      · simpa only [Real.norm_ofNat] using! ContinuousLinearMap.opNorm_smul_le (2 : ℝ)
            ((innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E ℝ))
    _ ≤ 4 * ‖z‖ := by nlinarith [norm_fst_le z, norm_snd_le z]

/-- Quadratic separation and localization, with a reciprocal barrier at each time. -/
private def doublingBarrier (ε α a T : ℝ) (z w : E × ℝ) : ℝ :=
  quadraticSize (z - w) / (2 * ε) + α * (quadraticSize z + quadraticSize w) +
    a / (T - z.2) + a / (T - w.2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem doublingBarrier_comm (ε α a T : ℝ) (z w : E × ℝ) :
    doublingBarrier ε α a T z w = doublingBarrier ε α a T w z := by
  have hQ : quadraticSize (z - w) = quadraticSize (w - z) := by
    simp only [quadraticSize, Prod.fst_sub, Prod.snd_sub]
    rw [norm_sub_rev z.1 w.1, ← neg_sub w.2 z.2, neg_sq]
  simp only [doublingBarrier, hQ]
  ac_rfl

omit [CompleteSpace E] in
private theorem contDiffAt_doublingBarrier_left {z w : E × ℝ} {ε α a T : ℝ} (hzT : T - z.2 ≠ 0) :
    ContDiffAt ℝ 1 (fun x ↦ doublingBarrier ε α a T x w) z := by
  have hQ : ContDiff ℝ 1 (quadraticSize (E := E)) := contDiff_quadraticSize
  have hsep : ContDiffAt ℝ 1 (fun x ↦ quadraticSize (x - w) / (2 * ε)) z :=
    (hQ.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const)).div_const (2 * ε)
  have hloc : ContDiffAt ℝ 1 (fun x ↦ α * (quadraticSize x + quadraticSize w)) z :=
    contDiffAt_const.mul (hQ.contDiffAt.add contDiffAt_const)
  have htime : ContDiffAt ℝ 1 (fun x : E × ℝ ↦ a / (T - x.2)) z :=
    contDiffAt_const.div (contDiffAt_const.sub contDiffAt_snd) hzT
  exact ((hsep.add hloc).add htime).add contDiffAt_const

omit [CompleteSpace E] in
private theorem time_doublingBarrier_left {z w : E × ℝ} {ε α a T : ℝ} (hzT : T - z.2 ≠ 0) :
    fderiv ℝ (fun x ↦ doublingBarrier ε α a T x w) z (0, 1) =
      (z.2 - w.2) / ε + 2 * α * z.2 + a / (T - z.2) ^ 2 := by
  have hslice : HasDerivAt (fun t ↦ doublingBarrier ε α a T (z.1, t) w)
      ((z.2 - w.2) / ε + 2 * α * z.2 + a / (T - z.2) ^ 2) z.2 := by
    simp only [doublingBarrier, quadraticSize, Prod.fst_sub, Prod.snd_sub]
    cas
  have hchain := (contDiffAt_doublingBarrier_left (w := w)
    (ε := ε) (α := α) (a := a) hzT).differentiableAt_one.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hchain.unique hslice

private theorem space_doublingBarrier_left {z w : E × ℝ} {ε α a T : ℝ} (hε : ε ≠ 0) :
    ∇ (fun x ↦ doublingBarrier ε α a T (x, z.2) w) z.1 = ε⁻¹ • (z.1 - w.1) + (2 * α) • z.1 := by
  have hsep := ((hasFDerivAt_id z.1).sub_const w.1).norm_sq
  have hloc := (hasFDerivAt_id z.1).norm_sq
  have h := ((((hsep.add_const ((z.2 - w.2) ^ 2)).mul_const (2 * ε)⁻¹).add
    (((hloc.add_const (z.2 ^ 2)).add_const (quadraticSize w)).const_mul α)).add_const
      (a / (T - z.2))).add_const (a / (T - w.2))
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! h using 1
  ext x
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_add_left, real_inner_smul_left, innerSL_apply_apply]
  cas using hε

/-- The doubled touching tests share the separation momentum, with opposite
localization corrections. The two Hamiltonians may depend on position and may
differ, on arbitrary open spacetime domains. Their difference bounds the
remaining time terms. -/
theorem IsSpatialViscositySubsolution.doubling_barrier_inequality {H K : E → E → ℝ}
    {U V : Set (E × ℝ)} {u v : E × ℝ → ℝ} {z w : E × ℝ} {ε α a T : ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (hv : IsSpatialViscositySupersolution K V v)
    (hz : z ∈ U) (hw : w ∈ V) (hε : ε ≠ 0) (hzT : T - z.2 ≠ 0) (hwT : T - w.2 ≠ 0)
    (hmax : IsLocalMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 -
      (quadraticSize (q.1 - q.2) / (2 * ε) + α * (quadraticSize q.1 + quadraticSize q.2) + a /
      (T - q.1.2) + a / (T - q.2.2))) (U ×ˢ V) (z, w)) :
    2 * α * (z.2 + w.2) + a / (T - z.2) ^ 2 + a / (T - w.2) ^ 2 ≤
      K (ε⁻¹ • (z.1 - w.1) - (2 * α) • w.1) w.1 - H (ε⁻¹ • (z.1 - w.1) + (2 * α) • z.1) z.1 := by
  let Ψ : (E × ℝ) → (E × ℝ) → ℝ := doublingBarrier ε α a T
  have hswap : Ψ z = fun y ↦ Ψ y z := by
    funext y
    exact doublingBarrier_comm ε α a T z y
  have hleft : ContDiffAt ℝ 1 (fun x ↦ Ψ x w) z := contDiffAt_doublingBarrier_left hzT
  have hright : ContDiffAt ℝ 1 (Ψ z) w := by
    rw [hswap]
    exact contDiffAt_doublingBarrier_left hwT
  have hlt : fderiv ℝ (fun x ↦ Ψ x w) z (0, 1) =
      (z.2 - w.2) / ε + 2 * α * z.2 + a / (T - z.2) ^ 2 := time_doublingBarrier_left hzT
  have hrt : fderiv ℝ (Ψ z) w (0, 1) =
      -(z.2 - w.2) / ε + 2 * α * w.2 + a / (T - w.2) ^ 2 := by
    rw [hswap]
    simpa only [neg_sub] using (time_doublingBarrier_left (z := w) (w := z) (α := α) (a := a) hwT)
  have hlx : ∇ (fun x ↦ Ψ (x, z.2) w) z.1 =
      ε⁻¹ • (z.1 - w.1) + (2 * α) • z.1 := space_doublingBarrier_left hε
  have hrx : ∇ (fun x ↦ Ψ z (x, w.2)) w.1 =
      -(ε⁻¹ • (z.1 - w.1) - (2 * α) • w.1) := by
    simp_rw [hswap]
    rw [space_doublingBarrier_left hε]
    simp only [sub_eq_add_neg, smul_add, smul_neg, neg_add_rev, neg_neg]
    abel
  have h := hu.doubling_inequality hv hz hw (Ψ := Ψ) hleft hright hmax
  rw [hlt, hrt, hlx, hrx, neg_neg] at h
  simp only [neg_div] at h
  rw [mul_add]
  linarith only [h]

end HamiltonJacobi

end
