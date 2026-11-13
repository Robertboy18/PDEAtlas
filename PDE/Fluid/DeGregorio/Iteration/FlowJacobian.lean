/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.HilbertCoefficient
import CAS.ExactTactic

/-!
# Spatial differentiation of the Hilbert flow

Spatial difference quotients of the constructed characteristics satisfy an
approximate linear ODE. The Hilbert coefficient's square-root modulus
makes the error tend uniformly to zero. Grönwall identifies the spatial
derivative with the positive exponential integral of that coefficient.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem norm_taylor_remainder_le_sqrt
    {b c : ℝ → ℝ} {M : NNReal}
    (hb : ∀ x, HasDerivAt b (c x) x)
    (hc : ∀ x y, |c y - c x| ≤ (M : ℝ) * Real.sqrt |y - x|) (x y : ℝ) :
    ‖b y - b x - c x * (y - x)‖ ≤ (M : ℝ) * Real.sqrt |y - x| * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z ↦ b z - c x * z) (f' := fun z ↦ c z - c x)
    (s := uIcc x y)
    (fun z _ ↦ by
      convert ((hb z).sub ((hasDerivAt_id z).const_mul (c x))).hasDerivWithinAt using 1
      · funext w
        rfl
      · simp only [mul_one])
    (fun z hz ↦ (hc x z).trans <| mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (abs_sub_left_of_mem_uIcc hz)) M.coe_nonneg)
    (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
  have heq : b y - c x * y - (b x - c x * x) = b y - b x - c x * (y - x) := by
    cas
  simpa only [heq, Real.norm_eq_abs] using h

private theorem hasDerivAt_flow_space
    {b c X : ℝ → ℝ → ℝ} {T : ℝ} {K M R : NNReal}
    (hc : Continuous (Function.uncurry c))
    (hcbound : ∀ x t, ‖c x t‖ ≤ (K : ℝ))
    (hcmod : ∀ x y t, |c y t - c x t| ≤ (M : ℝ) * Real.sqrt |y - x|)
    (hb : ∀ x t, HasDerivAt (fun y ↦ b y t) (c x t) x)
    (hX : ∀ x, Continuous (X x)) (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T → HasDerivAt (X x) (b (X x t) t) t)
    (hXLip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith R (fun x ↦ X x t))
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun y ↦ X y t) (Real.exp (∫ s in 0..t, c (X x s) s)) x := by
  let q : ℝ → ℝ := fun s ↦ c (X x s) s
  have hq : Continuous q := hc.comp ((hX x).prodMk continuous_id)
  let J : ℝ → ℝ := fun s ↦ Real.exp (∫ r in 0..s, q r)
  have hJ' (s : ℝ) : HasDerivAt J (q s * J s) s := by
    simpa only [J, mul_comm] using (hq.integral_hasStrictDerivAt 0 s).hasDerivAt.exp
  have hJ : Continuous J :=
    (show Differentiable ℝ J from fun s ↦ (hJ' s).differentiableAt).continuous
  have hJ₀ : J 0 = 1 := by simp only [J, intervalIntegral.integral_same, Real.exp_zero]
  let D : ℝ → ℝ → ℝ := fun h s ↦ (X (x + h) s - X x s) / h
  let D' : ℝ → ℝ → ℝ := fun h s ↦ (b (X (x + h) s) s - b (X x s) s) / h
  let ε : ℝ → ℝ := fun h ↦ (M : ℝ) * Real.sqrt (|h| * (R : ℝ)) * (R : ℝ)
  have hD' (h s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (D h) (D' h s) s :=
    ((hX' (x + h) s hs).sub (hX' x s hs)).div_const h
  have hD (h : ℝ) : Continuous (D h) := ((hX (x + h)).sub (hX x)).div_const h
  have hD₀ (h : ℝ) (hh : h ≠ 0) : D h 0 = 1 := by
    simp only [D, hX₀, add_sub_cancel_left, div_self hh]
  have hlin (s : ℝ) : LipschitzWith K (fun z : ℝ ↦ q s * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq, ← mul_sub, abs_mul, Real.dist_eq]
    exact mul_le_mul_of_nonneg_right (hcbound (X x s) s) (abs_nonneg _)
  have herror (h s : ℝ) (hh : h ≠ 0) (hs : s ∈ Icc (0 : ℝ) T) :
      dist (D' h s) (q s * D h s) ≤ ε h := by
    have hdist : |X (x + h) s - X x s| ≤ |h| * (R : ℝ) := by
      simpa only [Real.dist_eq, add_sub_cancel_left, mul_comm] using
        (hXLip s hs).dist_le_mul (x + h) x
    have htaylor := norm_taylor_remainder_le_sqrt (fun y ↦ hb y s)
      (fun y z ↦ hcmod y z s) (X x s) (X (x + h) s)
    have heq : D' h s - q s * D h s =
        h⁻¹ * (b (X (x + h) s) s - b (X x s) s -
          c (X x s) s * (X (x + h) s - X x s)) := by
      dsimp only [D', D, q]
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_left_comm, ← mul_sub]
    rw [Real.dist_eq, heq, abs_mul, abs_inv]
    calc
      |h|⁻¹ * |b (X (x + h) s) s - b (X x s) s -
          c (X x s) s * (X (x + h) s - X x s)| ≤
          |h|⁻¹ * ((M : ℝ) * Real.sqrt (|h| * (R : ℝ)) * (|h| * (R : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (abs_nonneg h))
        apply htaylor.trans
        gcongr
      _ = ε h := by
        dsimp only [ε]
        generalize Real.sqrt (|h| * (R : ℝ)) = z
        have hhabs : |h| ≠ 0 := abs_ne_zero.mpr hh
        cas using hhabs
  have hestimate (h : ℝ) (hh : h ≠ 0) :
      dist (D h t) (J t) ≤ gronwallBound 0 K (ε h) t := by
    have h := dist_le_of_approx_trajectories_ODE hlin (hD h).continuousOn
      (fun s hs ↦ (hD' h s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs ↦ herror h s hh (Ico_subset_Icc_self hs)) hJ.continuousOn
      (fun s _ ↦ (hJ' s).hasDerivWithinAt)
      (εg := 0) (fun s _ ↦ by simp only [dist_self, le_refl])
      (δ := 0) (by rw [hD₀ h hh, hJ₀, dist_self])
      t ht
    simpa only [add_zero, sub_zero] using h
  have heps : Tendsto ε (𝓝[≠] 0) (𝓝 0) := by
    have hcont : Continuous ε := by dsimp only [ε]; fun_prop
    simpa only [ε, abs_zero, zero_mul, Real.sqrt_zero, mul_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun h ↦ gronwallBound 0 K (ε h) t) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, gronwallBound_ε0_δ0] using
      ((gronwallBound_continuous_ε 0 K t).tendsto 0).comp heps
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  change Tendsto (fun h ↦ h⁻¹ * (X (x + h) t - X x t)) (𝓝[≠] 0) (𝓝 (J t))
  simp_rw [← div_eq_inv_mul]
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
    (by filter_upwards [self_mem_nhdsWithin] with h hh; exact hestimate h hh) hbound

/-- Every flow `X` of the normalized Hilbert velocity with `X x 0 = x` has spatial
derivative `exp (∫₀ᵗ c(X(x, s), s) ds)` at each time `t ∈ [0, T]`. -/
theorem hasDerivAt_hkCurve_hilbert_flow_space
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ}
    (hbc : ∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x)
    (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t)
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun y ↦ X y t) (Real.exp (∫ s in 0..t, c (X x s) s)) x := by
  obtain ⟨d, hd, _hpair, hb, hdbound, hdmod⟩ :=
    exists_hkCurve_hilbert_coefficient hT f
  obtain ⟨Z, hZ, hZ₀, hZ', hdist, _hgrowth, _hjoint, hunique⟩ :=
    exists_hkCurve_hilbert_flow hT f
  let R : NNReal := ⟨Real.exp (2 * (B : ℝ) * T), (Real.exp_pos _).le⟩
  have hZLip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      LipschitzWith R (fun y ↦ Z y s) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    apply (hdist y z s hs).trans
    change _ ≤ Real.exp (2 * (B : ℝ) * T) * dist y z
    rw [mul_comm]
    gcongr
    exact hs.2
  have hXZ (y : ℝ) : EqOn (X y) (Z y) (Icc (0 : ℝ) T) :=
    hunique y (X y) (fun s hs ↦ (hX' y s hs).continuousAt.continuousWithinAt)
      (hX' y) (hX₀ y)
  have hcd (y s : ℝ) : c y s = d y s := (hbc y s).unique (hb y s)
  have hint : (∫ s in 0..t, c (X x s) s) = ∫ s in 0..t, d (Z x s) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change c (X x s) s = d (Z x s) s
    rw [hXZ x ⟨hs.1, hs.2.trans ht.2⟩, hcd]
  rw [hint, funext (fun y ↦ hXZ y ht)]
  exact hasDerivAt_flow_space (K := 2 * B) hd hdbound hdmod hb hZ hZ₀ hZ' hZLip x t ht

/-- The constructed Eulerian inverse has reciprocal positive spatial
Jacobian at every time of the closed interval, including the endpoints. -/
theorem hasDerivAt_hkCurve_inverse_space
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ}
    (hbc : ∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x)
    (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t)
    (hY : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ Y p.1 p.2))
    (hXY : ∀ y t, t ∈ Icc (0 : ℝ) T → X (Y y t) t = y)
    (y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun z ↦ Y z t)
      (Real.exp (∫ s in 0..t, c (X (Y y t) s) s))⁻¹ y := by
  have hYslice : Continuous (fun z ↦ Y z t) :=
    hY.comp (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0 T))))
  have h := hasDerivAt_hkCurve_hilbert_flow_space hT f hbc hX₀ hX' (Y y t) t ht
  exact h.of_local_left_inverse hYslice.continuousAt (Real.exp_ne_zero _)
    (.of_forall fun z ↦ hXY z t ht)

end DeGregorio.Iteration
