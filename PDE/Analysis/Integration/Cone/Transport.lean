/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Continuity
public import PDE.Analysis.Integration.Cone.NormalTrace
public import PDE.Analysis.Calculus.TransportCone
import PDE.Analysis.Calculus.Divergence.Continuity
import PDE.FDeriv.SpaceTime

/-!
# Arbitrary currents on shrinking balls

Reynolds transport and the spatial divergence theorem give the balance for an
arbitrary C¹ scalar density P and C¹ spatial flux Q. The volume integrand uses
actual coordinate derivatives, with convention ∂t P − div Q. Continuity on a
fixed rescaled ball handles the terminal vertex.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped RealInnerProductSpace

namespace PDE.Analysis

variable {n : ℕ}

/-- The signed spacetime divergence of a scalar density and spatial flux. -/
def coneCurrentDivergence (P : ℝ^(n + 1) → ℝ) (Q : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] P) p - ∑ i : Fin n, (∂[i.succ] (fun q ↦ Q q i)) p

/-- The signed spacetime divergence equals the time derivative minus the divergence of a slice. -/
theorem coneCurrentDivergence_timeSpaceCons (P : ℝ^(n + 1) → ℝ)
    {Q : ℝ^(n + 1) → ℝ^n} (hQ : ContDiff ℝ 1 Q) (t : ℝ) (x : ℝ^n) :
    coneCurrentDivergence P Q (timeSpaceCons t x) =
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x := by
  unfold coneCurrentDivergence divergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (partialDeriv_timeSpaceCons_spatial i (fun q ↦ Q q i) t x
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hQ).differentiable one_ne_zero _)).symm

/-- The actual signed divergence of a C¹ current is continuous. -/
theorem continuous_coneCurrentDivergence {P : ℝ^(n + 1) → ℝ}
    {Q : ℝ^(n + 1) → ℝ^n} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    Continuous (coneCurrentDivergence P Q) := by
  apply ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
  apply continuous_finsetSum
  intro i _
  exact ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hQ).continuous_fderiv
    one_ne_zero).clm_apply continuous_const)

/-- Angular form of the outward lateral current flux. -/
def coneCurrentNormalFlux (P : ℝ^(n + 1) → ℝ) (Q : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) × ℝ^n) : ℝ := P p.1 - ⟪Q p.1, p.2⟫

/-- A continuous current has a continuous flux as a function of point and normal. -/
theorem continuous_coneCurrentNormalFlux {P : ℝ^(n + 1) → ℝ}
    {Q : ℝ^(n + 1) → ℝ^n} (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (coneCurrentNormalFlux P Q) :=
  (hP.comp continuous_fst).sub ((hQ.comp continuous_fst).inner continuous_snd)

/-- Spherical integration separates density and normal spatial flux. -/
theorem sphereIntegral_coneCurrentNormalFlux {P : ℝ^(n + 1) → ℝ}
    {Q : ℝ^(n + 1) → ℝ^n} (hP : Continuous P) (hQ : Continuous Q)
    (c : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n
      (fun x ↦ coneNormalTrace (coneCurrentNormalFlux P Q) c (timeSpaceCons t x)) c r =
      sphereIntegral n (fun x ↦ P (timeSpaceCons t x)) c r -
        sphereIntegral n (fun x ↦ ⟪Q (timeSpaceCons t x),
          NormedSpace.normalize (x - c)⟫) c r := by
  let X (ω : Metric.sphere (0 : ℝ^n) 1) := timeSpaceCons t (c + r • (ω : ℝ^n))
  have hX : Continuous X := (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.comp
    (continuous_const.add (continuous_subtype_val.const_smul r))
  have hpi : Integrable (fun ω ↦ P (X ω)) ((volume : Measure (ℝ^n)).toSphere) :=
    (hP.comp hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqi : Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ ⟪Q (X ω), (ω : ℝ^n)⟫)
      ((volume : Measure (ℝ^n)).toSphere) :=
    ((hQ.comp hX).inner continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnormal (ω : Metric.sphere (0 : ℝ^n) 1) :
      NormedSpace.normalize (c + r • (ω : ℝ^n) - c) = (ω : ℝ^n) := by
    rw [add_sub_cancel_left, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp ω.property)]
  unfold sphereIntegral coneNormalTrace coneCurrentNormalFlux
  simp only [spatialPart_timeSpaceCons, hnormal]
  rw [integral_sub hpi hqi, mul_sub]

/-- Reynolds transport and Gauss give the exact shrinking-ball derivative for any C¹ current. -/
theorem hasDerivAt_ballIntegral_current [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (c : ℝ^n) (T : ℝ)
    {t : ℝ} (ht : t < T) :
    HasDerivAt (fun s ↦ ballIntegral n (fun x ↦ P (timeSpaceCons s x)) c (T - s))
      (ballIntegral n (fun x ↦ coneCurrentDivergence P Q (timeSpaceCons t x)) c (T - t) -
        sphereIntegral n (fun x ↦ coneNormalTrace (coneCurrentNormalFlux P Q) c
          (timeSpaceCons t x)) c (T - t)) t := by
  let f (s : ℝ) (x : ℝ^n) := P (timeSpaceCons s x)
  have hf : ContDiff ℝ 1 (Function.uncurry f) :=
    hP.comp (contDiff_timeSpaceCons_uncurry n)
  have hder := hasDerivAt_ballIntegral_shrinking f hf c T (sub_pos.mpr ht)
  have htime : ballIntegral n
      (fun x ↦ fderiv ℝ (Function.uncurry f) (t, x) ((1 : ℝ), (0 : ℝ^n))) c (T - t) =
      ballIntegral n (fun x ↦ (∂[0] P) (timeSpaceCons t x)) c (T - t) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    exact fderiv_timeSpaceCons_time P t x (hP.differentiable one_ne_zero _)
  have hsliceQ : ContDiff ℝ 1 (fun x ↦ Q (timeSpaceCons t x)) :=
    hQ.comp (contDiff_timeSpaceCons_spatial n t)
  have hpt : Continuous (fun x ↦ (∂[0] P) (timeSpaceCons t x)) :=
    ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball c (T - t)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
      Metric.ball_subset_closedBall
  have hvolume : ballIntegral n
      (fun x ↦ coneCurrentDivergence P Q (timeSpaceCons t x)) c (T - t) =
      ballIntegral n (fun x ↦ (∂[0] P) (timeSpaceCons t x)) c (T - t) -
        sphereIntegral n (fun x ↦ ⟪Q (timeSpaceCons t x),
          NormedSpace.normalize (x - c)⟫) c (T - t) := by
    simp_rw [coneCurrentDivergence_timeSpaceCons P hQ]
    rw [ballIntegral, integral_sub (hint hpt) (hint hsliceQ.continuous_divergence)]
    exact congrArg (_ - ·)
      (ballIntegral_divergence_eq_sphereIntegral_inner_normal hsliceQ c (sub_pos.mpr ht))
  apply hder.congr_deriv
  rw [htime, hvolume, sphereIntegral_coneCurrentNormalFlux hP.continuous hQ.continuous c t
    (sub_pos.mpr ht)]
  dsimp only [f]
  ring

/-- The balance integrated between arbitrary times, allowing the upper time to be the vertex. -/
theorem integral_ballIntegral_current_divergence [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (c : ℝ^n)
    {s τ T : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    (∫ t in s..τ, ballIntegral n
      (fun x ↦ coneCurrentDivergence P Q (timeSpaceCons t x)) c (T - t)) =
      ballIntegral n (fun x ↦ P (timeSpaceCons τ x)) c (T - τ) -
        ballIntegral n (fun x ↦ P (timeSpaceCons s x)) c (T - s) +
          ∫ t in s..τ, sphereIntegral n
            (fun x ↦ coneNormalTrace (coneCurrentNormalFlux P Q) c (timeSpaceCons t x))
            c (T - t) := by
  have hR := continuousOn_ballIntegral_shrinking (continuous_coneCurrentDivergence hP hQ) c T
  have hiR : IntervalIntegrable (fun t ↦ ballIntegral n
      (fun x ↦ coneCurrentDivergence P Q (timeSpaceCons t x)) c (T - t)) volume s τ :=
    (hR.mono (show Icc s τ ⊆ Iic T from fun _ ht ↦ ht.2.trans hτ)).intervalIntegrable_of_Icc hsτ
  have hiF := intervalIntegrable_sphereIntegral_coneNormalTrace
    (continuous_coneCurrentNormalFlux hP.continuous hQ.continuous) c hsτ hτ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsτ
    ((continuousOn_ballIntegral_shrinking hP.continuous c T).mono
      (show Icc s τ ⊆ Iic T from fun _ ht ↦ ht.2.trans hτ))
    (fun t ht ↦ hasDerivAt_ballIntegral_current hP hQ c T (ht.2.trans_le hτ)) (hiR.sub hiF)
  rw [intervalIntegral.integral_sub hiR hiF] at hFTC
  linarith

end PDE.Analysis
