/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.HolderVorticity
public import PDE.Fluid.Incompressible.HalfPlane.VelocityDilation
public import PDE.Fluid.Incompressible.HalfPlane.VelocityExterior
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Linearity

/-!
# Scale-adapted Hessian estimates of the stream of a decaying Hölder vorticity

Let `f` be a decaying Hölder vorticity (`IsHolderVorticity α f`) with grouped stream
`Ψ = GreenFunction.quadrantPotential f`, let `x` be a point of the open upper half-plane, `δ > 0`
and `R ≥ 2(|x| + 2δ)`, and let `B` and `L` be the size and the `α`-Hölder constant of `f` on the
closed upper half-plane inside `B(x, 2δ)`. The Hessian `D = ∂ₗ∂ₖΨ - ∂ₗ∂ₖΨ_R` relative to the far
potential `Ψ_R = quadrantPotential (farSource R f)` satisfies

```text
|D(x)| ≤ C (B + δ^α L) + C I₂,   |D(x) - D(z)| ≤ C (L + B δ^(-α)) |x - z|^α + C |x - z| I₃
```

for `z` in the open upper half-plane with `2|x - z| ≤ δ` (`exists_abs_hessian_sub_far_le`,
`exists_abs_hessian_sub_far_sub_le`). Here `I₂` and `I₃` bound the integrals of `|f(y)|/|x - y|²`
and `|f(y)|/|x - y|³` over `{0 < y₁, δ ≤ |x - y|, |y| ≤ 2R}`, and `C` depends only on `α`. The far
part is treated separately by the expansions of the far potential.

## Main definitions

* `localPiece`: the local piece `χ_δ(· - x) N` of the near source.
* `middlePiece`: the intermediate piece `(1 - χ_δ(· - x)) N` of the near source.
* `Setting`: the size and Hölder bounds of `f` on the closed upper half-plane inside `B(x, 2δ)`,
  with `R ≥ 2(|x| + 2δ)`.

## Main results

* `exists_partialDeriv_partialDeriv_halfSpaceGreenPotential_eq`: the Hessian entries of a Green
  potential are entries of the velocity gradient up to sign, `∂ₗ∂₀φ = ∂ₗu₁` and `∂ₗ∂₁φ = -∂ₗu₀`.
* `Setting.holder_localPiece`: the local piece is Hölder on the closed upper half-plane with
  constant `L + K δ^(-α) B`.
* `Setting.integral_abs_localPiece_le`: the mass of the local piece is at most `4π δ² B`.
* `Setting.hessian_sub_far_eq`: the Hessian relative to the far part is the sum of the Hessians of
  the two pieces.
* `exists_abs_hessian_sub_far_le`: the bound of `D(x)`.
* `exists_abs_hessian_sub_far_sub_le`: the bound of `D(x) - D(z)`.

## How it works

On `B(0, R/2)` the stream is the Green potential of the near source `N` plus the far potential. The
cutoff `χ(y) = χ_δ(y - x)`, equal to one on `B(x, δ)` and to zero outside `B(x, 2δ)`, splits `N`
into a local piece `χ N` and an intermediate piece `(1 - χ) N`, so `D` is the sum of the Hessians of
their Green potentials, and these are entries of velocity gradients up to sign
(`exists_partialDeriv_partialDeriv_halfSpaceGreenPotential_eq`). The local piece has Hölder constant
`L + K δ^(-α) B`, with `K` a constant of the cutoff, and mass at most `4π δ² B`. The dilation
invariant bound of the velocity gradient at scale `δ`
(`abs_partialDeriv_halfPlaneVelocity_le_of_scale`) turns this into `C (B + δ^α L)`, and the Hölder
estimate of the velocity gradient (`abs_partialDeriv_halfPlaneVelocity_sub_le`) into
`C (L + B δ^(-α)) |x - z|^α`. The intermediate piece vanishes on `B(x, δ)`, so its velocity gradient
at `x` and its differences are absolutely convergent integrals against `|f(y)|/|x - y|²` and
`|x - z| |f(y)|/|x - y|³` (`abs_partialDeriv_halfPlaneVelocity_le_of_eq_zero`,
`abs_partialDeriv_halfPlaneVelocity_sub_le_of_eq_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

/-- **Hessian entries of a Green potential are velocity-gradient entries up to sign**:
`∂ₗ∂₀φ = ∂ₗu₁` and `∂ₗ∂₁φ = -∂ₗu₀` for `u = halfPlaneVelocity P`. -/
theorem exists_partialDeriv_partialDeriv_halfSpaceGreenPotential_eq (k l : Fin 2) :
    ∃ (k' : Fin 2) (s : ℝ), |s| = 1 ∧ ∀ (P : ℝ^2 → ℝ) (x : ℝ^2),
      (∂[l] (∂[k] (halfSpaceGreenPotential P))) x =
        s * (∂[l] (fun y ↦ halfPlaneVelocity P y k')) x := by
  fin_cases k
  · refine ⟨1, 1, abs_one, fun P x ↦ ?_⟩
    simp only [Fin.zero_eta, one_mul]
    rw [← halfPlaneVelocity_one]
  · refine ⟨0, -1, by simp, fun P x ↦ ?_⟩
    have h : ∂[(1 : Fin 2)] (halfSpaceGreenPotential P) =
        -(fun y ↦ halfPlaneVelocity P y 0) := by
      rw [halfPlaneVelocity_zero, neg_neg]
    simp only [Fin.mk_one, h, PDE.partialDeriv_neg, neg_mul, one_mul]

end IncompressibleFlow

end

end

/-! ### The local and intermediate pieces (internal) -/

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

/-- Second partial derivatives depend only on the germ. -/
theorem partialDeriv_partialDeriv_congr {f g : ℝ^2 → ℝ} {x : ℝ^2}
    (h : f =ᶠ[𝓝 x] g) (k l : Fin 2) :
    (∂[l] (∂[k] f)) x = (∂[l] (∂[k] g)) x :=
  PDE.partialDeriv_congr_nhds l (h.partialDeriv k)

variable {α : ℝ} {f : ℝ^2 → ℝ} {x : ℝ^2} {δ R : ℝ}

/-- The local piece `χ_δ(· - x) N` of the near source. -/
def localPiece (x : ℝ^2) (δ R : ℝ) (f : ℝ^2 → ℝ) (y : ℝ^2) : ℝ :=
  radialCutoff δ (y - x) * nearSource R f y

/-- The intermediate piece `(1 - χ_δ(· - x)) N` of the near source. -/
def middlePiece (x : ℝ^2) (δ R : ℝ) (f : ℝ^2 → ℝ) (y : ℝ^2) : ℝ :=
  (1 - radialCutoff δ (y - x)) * nearSource R f y

/-- The cutoff `y ↦ χ_δ(y - x)` around `x` is continuous. -/
theorem continuous_radialCutoff_sub (δ : ℝ) (x : ℝ^2) :
    Continuous fun y : ℝ^2 ↦ radialCutoff δ (y - x) :=
  (contDiff_radialCutoff (n := 2) δ (k := 0)).continuous.comp (continuous_id.sub continuous_const)

/-- The setting of the engine: the size and Hölder bounds of `f` on the closed upper half-plane
inside `B(x, 2δ)`, with `R ≥ 2(|x| + 2δ)`. -/
structure Setting (α : ℝ) (f : ℝ^2 → ℝ) (x : ℝ^2) (δ R B L : ℝ) : Prop where
  hf : IsHolderVorticity α f
  hx : 0 < x 1
  hδ : 0 < δ
  hR : 2 * (‖x‖ + 2 * δ) ≤ R
  hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ B
  hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
    |f y - f z| ≤ L * ‖y - z‖ ^ α

namespace Setting

variable {B L : ℝ} (S : Setting α f x δ R B L)
include S

/-- In the setting the radius `R` is positive. -/
theorem R_pos : 0 < R := by have := S.hδ; linarith [S.hR, norm_nonneg x]

/-- In the setting `|x| < R/2`. -/
theorem x_lt : ‖x‖ < R / 2 := by have := S.hδ; linarith [S.hR]

/-- In the setting the size bound `B` is nonnegative. -/
theorem B_nonneg : 0 ≤ B := (abs_nonneg _).trans (S.hB x S.hx.le (by simp; linarith [S.hδ]))

/-- In the setting the Hölder constant `L` is nonnegative. -/
theorem L_nonneg : 0 ≤ L := by
  set e : ℝ^2 := EuclideanSpace.single 0 δ
  have he1 : e 1 = 0 := by simp [e]
  have hne : ‖e‖ = δ := by simp [e, abs_of_pos S.hδ]
  have hz1 : 0 ≤ (x + e) 1 := by simp [he1, S.hx.le]
  have hd : ‖x - (x + e)‖ = δ := by rw [sub_add_cancel_left, norm_neg, hne]
  have h := S.hL x (x + e) S.hx.le hz1 (by simp; linarith [S.hδ]) (by rw [hd]; linarith [S.hδ])
  rw [show x - (x + e) = -e by abel, norm_neg, hne] at h
  have hpos : 0 < δ ^ α := Real.rpow_pos_of_pos S.hδ α
  by_contra hneg
  have : L * δ ^ α < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
  linarith [abs_nonneg (f x - f (x + e))]

/-- On the closed upper half-plane inside `B(x, 2δ)` the near source is `f`. -/
theorem nearSource_eq {y : ℝ^2} (hy : 0 ≤ y 1) (hxy : ‖y - x‖ ≤ 2 * δ) :
    nearSource R f y = f y := by
  refine nearSource_eq_self S.R_pos hy ?_
  have := norm_le_norm_add_norm_sub' y x
  linarith [S.hR, S.hδ, norm_nonneg x]

/-- The local piece `χ_δ(· - x) N` is continuous. -/
theorem continuous_localPiece : Continuous (localPiece x δ R f) :=
  (continuous_radialCutoff_sub δ x).mul (continuous_nearSource S.hf.continuousOn)

/-- The intermediate piece `(1 - χ_δ(· - x)) N` is continuous. -/
theorem continuous_middlePiece : Continuous (middlePiece x δ R f) :=
  (continuous_const.sub (continuous_radialCutoff_sub δ x)).mul
    (continuous_nearSource S.hf.continuousOn)

/-- The local piece `χ_δ(· - x) N` has compact support. -/
theorem hasCompactSupport_localPiece : HasCompactSupport (localPiece x δ R f) :=
  (hasCompactSupport_nearSource S.R_pos).mul_left

/-- The intermediate piece `(1 - χ_δ(· - x)) N` has compact support. -/
theorem hasCompactSupport_middlePiece : HasCompactSupport (middlePiece x δ R f) :=
  (hasCompactSupport_nearSource S.R_pos).mul_left

/-- The radial cutoff around `x` vanishes outside `B̄(x, 2δ)`. -/
theorem cutoff_eq_zero {y : ℝ^2} (hy : y ∉ closedBall x (2 * δ)) :
    radialCutoff δ (y - x) = 0 := by
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  exact radialCutoff_eq_zero_of_le_norm S.hδ hy.le

/-- The local piece is bounded by `B` on the closed upper half-plane. -/
theorem abs_localPiece_le {y : ℝ^2} (hy : 0 ≤ y 1) : |localPiece x δ R f y| ≤ B := by
  unfold localPiece
  by_cases hyT : y ∈ closedBall x (2 * δ)
  · rw [mem_closedBall, dist_eq_norm] at hyT
    rw [S.nearSource_eq hy hyT, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_radialCutoff_le_one _ _)).trans
      (S.hB y hy (by rwa [norm_sub_rev]))
  · rw [S.cutoff_eq_zero hyT, zero_mul, abs_zero]
    exact S.B_nonneg

/-- The Hölder constant of the local piece on the closed upper half-plane. -/
theorem holder_localPiece {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ δ : ℝ, 0 < δ → ∀ c y z : ℝ^2,
      |radialCutoff δ (y - c) - radialCutoff δ (z - c)| ≤ K * δ ^ (-α) * ‖y - z‖ ^ α)
    (y z : ℝ^2) (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |localPiece x δ R f y - localPiece x δ R f z| ≤
      (L + K * δ ^ (-α) * B) * ‖y - z‖ ^ α := by
  refine abs_mul_sub_mul_le (S := {y | 0 ≤ y 1}) (T := closedBall x (2 * δ))
    (by have := Real.rpow_pos_of_pos S.hδ (-α); positivity) S.L_nonneg S.B_nonneg
    (fun _ ↦ abs_radialCutoff_le_one _ _) (fun a b ↦ hKb δ S.hδ x a b)
    (fun a ha ↦ S.cutoff_eq_zero ha) (fun a ha haT ↦ ?_) (fun a ha b hb haT hbT ↦ ?_) hy hz
  · rw [mem_closedBall, dist_eq_norm] at haT
    rw [S.nearSource_eq ha haT]
    exact S.hB a ha (by rwa [norm_sub_rev])
  · rw [mem_closedBall, dist_eq_norm] at haT hbT
    rw [S.nearSource_eq ha haT, S.nearSource_eq hb hbT]
    exact S.hL a b ha hb (by rwa [norm_sub_rev]) (by rwa [norm_sub_rev])

/-- The middle piece is Hölder on the closed upper half-plane with some constant. -/
theorem exists_holder_middlePiece : ∃ M : ℝ, ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
    |middlePiece x δ R f y - middlePiece x δ R f z| ≤ M * ‖y - z‖ ^ α := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_radialCutoff_sub_le S.hf.exponent_pos
    S.hf.exponent_lt_one.le
  obtain ⟨M, hM0, hM⟩ := S.hf.exists_holder_nearSource S.R_pos
  obtain ⟨B', hB', hfB'⟩ := S.hf.exists_bound
  refine ⟨M + K * δ ^ (-α) * B', fun y z hy hz ↦ ?_⟩
  unfold middlePiece
  refine abs_mul_sub_mul_le (S := {y | 0 ≤ y 1}) (T := univ)
    (g := fun a ↦ 1 - radialCutoff δ (a - x)) (f := nearSource R f) (K := K * δ ^ (-α))
    (by have := Real.rpow_pos_of_pos S.hδ (-α); positivity) hM0 hB' (fun a ↦ ?_)
    (fun a b ↦ ?_) (fun a ha ↦ absurd (mem_univ a) ha) (fun a ha _ ↦ ?_)
    (fun a ha b hb _ _ ↦ hM a b ha hb) hy hz
  · have h := radialCutoff_mem_Icc (n := 2) δ (a - x)
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  · rw [show 1 - radialCutoff δ (a - x) - (1 - radialCutoff δ (b - x)) =
      -(radialCutoff δ (a - x) - radialCutoff δ (b - x)) by ring, abs_neg]
    exact hKb δ S.hδ x a b
  · rw [nearSource_of_nonneg ha, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_radialCutoff_le_one _ _)).trans (hfB' a ha)

/-- The mass of the local piece: `∫_{ℝ²₊} |χ N| ≤ 4π δ² B`. -/
theorem integral_abs_localPiece_le :
    ∫ y in HalfSpace.upper 2, |localPiece x δ R f y| ≤ 4 * Real.pi * δ ^ 2 * B := by
  have hint : Integrable (localPiece x δ R f) :=
    S.continuous_localPiece.integrable_of_hasCompactSupport S.hasCompactSupport_localPiece
  have hind : Integrable ((ball x (2 * δ)).indicator fun _ : ℝ^2 ↦ B) :=
    (integrableOn_const (measure_ball_lt_top (x := x) (r := 2 * δ)).ne).integrable_indicator
      measurableSet_ball
  have hle : ∀ y ∈ HalfSpace.upper 2, |localPiece x δ R f y| ≤
      (ball x (2 * δ)).indicator (fun _ ↦ B) y := by
    intro y hy
    by_cases hyb : y ∈ ball x (2 * δ)
    · rw [indicator_of_mem hyb]
      exact S.abs_localPiece_le (le_of_lt (show 0 < y 1 from hy))
    · rw [indicator_of_notMem hyb]
      have : ‖y - x‖ ≥ 2 * δ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hyb; exact hyb
      simp [localPiece, radialCutoff_eq_zero_of_le_norm S.hδ this]
  calc ∫ y in HalfSpace.upper 2, |localPiece x δ R f y|
      ≤ ∫ y in HalfSpace.upper 2, (ball x (2 * δ)).indicator (fun _ ↦ B) y :=
        setIntegral_mono_on hint.abs.integrableOn hind.integrableOn
          (HalfSpace.measurableSet_upper 2) hle
    _ ≤ ∫ y, (ball x (2 * δ)).indicator (fun _ ↦ B) y :=
        setIntegral_le_integral hind (Eventually.of_forall fun y ↦
          indicator_nonneg (fun _ _ ↦ S.B_nonneg) y)
    _ = 4 * Real.pi * δ ^ 2 * B := by
        rw [integral_indicator measurableSet_ball, setIntegral_const,
          measureReal_ball_two x (by linarith [S.hδ]), smul_eq_mul]
        ring

/-- The middle piece vanishes on the closed upper half-plane inside `B(x, δ)`. -/
theorem middlePiece_eq_zero (y : ℝ^2) (_hy : 0 ≤ y 1) (hxy : ‖x - y‖ < δ) :
    middlePiece x δ R f y = 0 := by
  rw [middlePiece, radialCutoff_eq_one S.hδ (by rw [norm_sub_rev]; exact hxy.le), sub_self,
    zero_mul]

/-- The middle piece is bounded by `|f|` on the intermediate region and vanishes elsewhere on the
upper half-plane. -/
theorem lintegral_middlePiece_le (p : ℕ) :
    ∫⁻ y in HalfSpace.upper 2, ENNReal.ofReal (|middlePiece x δ R f y| / ‖x - y‖ ^ p) ≤
      ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ p) := by
  set T := {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R}
  have hT : MeasurableSet T := by
    have h1 : Measurable fun y : ℝ^2 ↦ y 1 :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
    have h2 : Measurable fun y : ℝ^2 ↦ ‖x - y‖ :=
      (continuous_const.sub continuous_id).norm.measurable
    have h3 : Measurable fun y : ℝ^2 ↦ ‖y‖ := continuous_norm.measurable
    exact (measurableSet_lt measurable_const h1).inter
      ((measurableSet_le measurable_const h2).inter (measurableSet_le h3 measurable_const))
  have hle : ∀ y ∈ HalfSpace.upper 2,
      ENNReal.ofReal (|middlePiece x δ R f y| / ‖x - y‖ ^ p) ≤
        T.indicator (fun y ↦ ENNReal.ofReal (|f y| / ‖x - y‖ ^ p)) y := by
    intro y hy
    have hy1 : 0 < y 1 := hy
    by_cases hyT : y ∈ T
    · rw [indicator_of_mem hyT]
      refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
      have hc := radialCutoff_mem_Icc (n := 2) δ (y - x)
      rw [middlePiece, nearSource_of_nonneg hy1.le, abs_mul, abs_mul]
      have h1 : |1 - radialCutoff δ (y - x)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
      calc |1 - radialCutoff δ (y - x)| * (|radialCutoff R y| * |f y|) ≤ 1 * (1 * |f y|) := by
            gcongr
            exact abs_radialCutoff_le_one _ _
        _ = |f y| := by ring
    · rw [indicator_of_notMem hyT]
      have hz : middlePiece x δ R f y = 0 := by
        simp only [T, mem_ofPred_eq, not_and, not_le] at hyT
        by_cases hd : δ ≤ ‖x - y‖
        · rw [middlePiece, nearSource_eq_zero S.R_pos hy1.le (hyT hy1 hd).le, mul_zero]
        · exact S.middlePiece_eq_zero y hy1.le (lt_of_not_ge hd)
      simp [hz]
  calc ∫⁻ y in HalfSpace.upper 2, ENNReal.ofReal (|middlePiece x δ R f y| / ‖x - y‖ ^ p)
      ≤ ∫⁻ y in HalfSpace.upper 2,
          T.indicator (fun y ↦ ENNReal.ofReal (|f y| / ‖x - y‖ ^ p)) y :=
        setLIntegral_mono' (HalfSpace.measurableSet_upper 2) hle
    _ ≤ ∫⁻ y, T.indicator (fun y ↦ ENNReal.ofReal (|f y| / ‖x - y‖ ^ p)) y :=
        setLIntegral_le_lintegral _ _
    _ = _ := lintegral_indicator hT _

/-- The Green potential of the near source is the sum of the potentials of the two pieces. -/
theorem halfSpaceGreenPotential_nearSource_eq :
    halfSpaceGreenPotential (nearSource R f) = fun y ↦
      halfSpaceGreenPotential (localPiece x δ R f) y +
        halfSpaceGreenPotential (middlePiece x δ R f) y := by
  funext y
  rw [← halfSpaceGreenPotential_add
    (hasIntegrableHalfSpaceGreenPotential_of_continuous S.continuous_localPiece
      S.hasCompactSupport_localPiece)
    (hasIntegrableHalfSpaceGreenPotential_of_continuous S.continuous_middlePiece
      S.hasCompactSupport_middlePiece)]
  congr 1
  funext w
  simp only [localPiece, middlePiece]
  ring

/-- At points `w` of the open upper half-plane in `B(0, R/2)`, the Hessian relative to the far
part is the sum of the Hessians of the two pieces. -/
theorem hessian_sub_far_eq {w : ℝ^2} (hw : 0 < w 1) (hwR : ‖w‖ < R / 2) (k l : Fin 2) :
    (∂[l] (∂[k] (quadrantPotential f))) w - (∂[l] (∂[k] (quadrantPotential (farSource R f)))) w =
      (∂[l] (∂[k] (halfSpaceGreenPotential (localPiece x δ R f)))) w +
        (∂[l] (∂[k] (halfSpaceGreenPotential (middlePiece x δ R f)))) w := by
  obtain ⟨Ml, hMl⟩ : ∃ M : ℝ, ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |localPiece x δ R f y - localPiece x δ R f z| ≤ M * ‖y - z‖ ^ α := by
    obtain ⟨K, hK, hKb⟩ := exists_abs_radialCutoff_sub_le S.hf.exponent_pos
      S.hf.exponent_lt_one.le
    exact ⟨_, S.holder_localPiece hK hKb⟩
  obtain ⟨Mm, hMm⟩ := S.exists_holder_middlePiece
  have hloc := contDiffAt_halfSpaceGreenPotential_of_holder S.continuous_localPiece
    S.hasCompactSupport_localPiece S.hf.exponent_pos S.hf.exponent_lt_one hMl hw
  have hmid := contDiffAt_halfSpaceGreenPotential_of_holder S.continuous_middlePiece
    S.hasCompactSupport_middlePiece S.hf.exponent_pos S.hf.exponent_lt_one hMm hw
  rw [partialDeriv_partialDeriv_congr (S.hf.quadrantPotential_eventuallyEq S.R_pos hwR),
    partialDeriv_partialDeriv_add k l (S.hf.contDiffAt_nearSource S.R_pos hw)
      (S.hf.contDiffAt_farSource S.R_pos hwR), add_sub_cancel_right,
    S.halfSpaceGreenPotential_nearSource_eq, partialDeriv_partialDeriv_add k l hloc hmid]

end Setting

end IncompressibleFlow

end

/-! ### The engine -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

variable {α : ℝ}

/-- **The engine, pointwise.** For a decaying Hölder vorticity `f`, a point `x` of the open upper
half-plane, `δ > 0` and `R ≥ 2(|x| + 2δ)`, with `|f| ≤ B` and `α`-Hölder constant `L` on the
closed upper half-plane inside `B̄(x, 2δ)` and `I` a bound of
`∫⁻_{0 < y₁, δ ≤ |x - y|, |y| ≤ 2R} |f(y)|/|x - y|²`,
`|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ_R(x)| ≤ C (B + δ^α L) + C I`, `Ψ_R` the far potential. -/
theorem exists_abs_hessian_sub_far_le (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃x : ℝ^2⦄ ⦃δ R B L I : ℝ⦄, IsHolderVorticity α f →
      0 < x 1 → 0 < δ → 2 * (‖x‖ + 2 * δ) ≤ R →
      (∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ B) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
        |f y - f z| ≤ L * ‖y - z‖ ^ α) → 0 ≤ I →
      ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2) ≤ ENNReal.ofReal I →
      ∀ k l : Fin 2, |(∂[l] (∂[k] (quadrantPotential f))) x -
        (∂[l] (∂[k] (quadrantPotential (farSource R f)))) x| ≤ C * (B + δ ^ α * L) + C * I := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_radialCutoff_sub_le hα hα1.le
  refine ⟨50 / α * (1 + K) + 8 + 40 * Real.pi + 10 / Real.pi, by positivity, ?_⟩
  intro f x δ R B L I hf hx hδ hR hB hL hI0 hI k l
  have S : Setting α f x δ R B L := ⟨hf, hx, hδ, hR, hB, hL⟩
  have hB0 := S.B_nonneg
  have hL0 := S.L_nonneg
  set C := 50 / α * (1 + K) + 8 + 40 * Real.pi + 10 / Real.pi
  obtain ⟨k', s, hs, hks⟩ := exists_partialDeriv_partialDeriv_halfSpaceGreenPotential_eq k l
  rw [S.hessian_sub_far_eq hx S.x_lt k l, hks, hks]
  have hxU : x ∈ HalfSpace.upper 2 := hx
  -- the local piece
  have hloc : |(∂[l] (fun y ↦ halfPlaneVelocity (localPiece x δ R f) y k')) x| ≤
      50 / α * (1 + K) * (B + δ ^ α * L) + (8 + 40 * Real.pi) * B := by
    have h := abs_partialDeriv_halfPlaneVelocity_le_of_scale S.continuous_localPiece
      S.hasCompactSupport_localPiece hα hα1.le (S.holder_localPiece hK hKb)
      (fun y hy ↦ S.abs_localPiece_le hy) hδ l k' hxU
    have hmass := S.integral_abs_localPiece_le
    have hδα : δ ^ α * δ ^ (-α) = 1 := by
      rw [Real.rpow_neg hδ.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ α).ne']
    have h2 : (δ ^ 2)⁻¹ * ∫ y in HalfSpace.upper 2, |localPiece x δ R f y| ≤ 4 * Real.pi * B := by
      calc (δ ^ 2)⁻¹ * ∫ y in HalfSpace.upper 2, |localPiece x δ R f y|
          ≤ (δ ^ 2)⁻¹ * (4 * Real.pi * δ ^ 2 * B) := by gcongr
        _ = 4 * Real.pi * B := by field_simp
    have h3 : δ ^ α * (L + K * δ ^ (-α) * B) = δ ^ α * L + K * B := by
      rw [mul_add, show δ ^ α * (K * δ ^ (-α) * B) = K * B * (δ ^ α * δ ^ (-α)) by ring, hδα,
        mul_one]
    have hδL : 0 ≤ δ ^ α * L := mul_nonneg (Real.rpow_nonneg hδ.le _) hL0
    calc _ ≤ 50 * (δ ^ α * (L + K * δ ^ (-α) * B)) / α + 8 * B +
          10 * ((δ ^ 2)⁻¹ * ∫ y in HalfSpace.upper 2, |localPiece x δ R f y|) := h
      _ ≤ 50 * (δ ^ α * L + K * B) / α + 8 * B + 10 * (4 * Real.pi * B) := by
          rw [h3]; gcongr
      _ ≤ 50 / α * (1 + K) * (B + δ ^ α * L) + (8 + 40 * Real.pi) * B := by
          rw [show 50 * (δ ^ α * L + K * B) / α = 50 / α * (δ ^ α * L + K * B) by ring]
          have h50 : 0 ≤ 50 / α := by positivity
          nlinarith [mul_nonneg h50 (mul_nonneg hK hδL), mul_nonneg h50 hB0,
            mul_nonneg h50 hδL, mul_nonneg h50 (mul_nonneg hK hB0)]
  -- the middle piece
  obtain ⟨Mm, hMm⟩ := S.exists_holder_middlePiece
  have hmid : |(∂[l] (fun y ↦ halfPlaneVelocity (middlePiece x δ R f) y k')) x| ≤
      10 / Real.pi * I :=
    abs_partialDeriv_halfPlaneVelocity_le_of_eq_zero S.continuous_middlePiece
      S.hasCompactSupport_middlePiece hα hα1.le hMm hx hδ S.middlePiece_eq_zero hI0
      ((S.lintegral_middlePiece_le 2).trans hI) l k'
  rw [← mul_add, abs_mul, hs, one_mul]
  have hπ : 0 ≤ 10 / Real.pi := by positivity
  have h50 : 0 ≤ 50 / α * (1 + K) := by positivity
  have hδL : 0 ≤ δ ^ α * L := mul_nonneg (Real.rpow_nonneg hδ.le _) hL0
  calc |(∂[l] (fun y ↦ halfPlaneVelocity (localPiece x δ R f) y k')) x +
        (∂[l] (fun y ↦ halfPlaneVelocity (middlePiece x δ R f) y k')) x|
      ≤ _ := abs_add_le _ _
    _ ≤ 50 / α * (1 + K) * (B + δ ^ α * L) + (8 + 40 * Real.pi) * B + 10 / Real.pi * I :=
        add_le_add hloc hmid
    _ ≤ C * (B + δ ^ α * L) + C * I := by
        simp only [C]
        nlinarith [mul_nonneg hπ (add_nonneg hB0 hδL), mul_nonneg h50 hI0,
          mul_nonneg (by positivity : (0 : ℝ) ≤ 8 + 40 * Real.pi) hδL,
          mul_nonneg (by positivity : (0 : ℝ) ≤ 8 + 40 * Real.pi) hI0, Real.pi_pos]

/-- **The engine, differences.** Under the hypotheses of `exists_abs_hessian_sub_far_le`, for `z`
in the open upper half-plane with `2|x - z| ≤ δ` and `I` a bound of
`∫⁻_{0 < y₁, δ ≤ |x - y|, |y| ≤ 2R} |f(y)|/|x - y|³`, the Hessian `D = ∂ₗ∂ₖΨ - ∂ₗ∂ₖΨ_R` relative
to the far potential satisfies `|D(x) - D(z)| ≤ C (L + B δ^(-α)) |x - z|^α + C |x - z| I`. -/
theorem exists_abs_hessian_sub_far_sub_le (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃x z : ℝ^2⦄ ⦃δ R B L I : ℝ⦄, IsHolderVorticity α f →
      0 < x 1 → 0 < δ → 2 * (‖x‖ + 2 * δ) ≤ R →
      (∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ B) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
        |f y - f z| ≤ L * ‖y - z‖ ^ α) → 0 ≤ I →
      ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ 3) ≤ ENNReal.ofReal I →
      0 < z 1 → 2 * ‖x - z‖ ≤ δ →
      ∀ k l : Fin 2, |((∂[l] (∂[k] (quadrantPotential f))) x -
          (∂[l] (∂[k] (quadrantPotential (farSource R f)))) x) -
        ((∂[l] (∂[k] (quadrantPotential f))) z -
          (∂[l] (∂[k] (quadrantPotential (farSource R f)))) z)| ≤
        C * (L + B * δ ^ (-α)) * ‖x - z‖ ^ α + C * ‖x - z‖ * I := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_radialCutoff_sub_le hα hα1.le
  refine ⟨211 / (α * (1 - α)) * (1 + K) + 10 / Real.pi, ?_, ?_⟩
  · have : 0 < 1 - α := by linarith
    positivity
  intro f x z δ R B L I hf hx hδ hR hB hL hI0 hI hz hxz k l
  have S : Setting α f x δ R B L := ⟨hf, hx, hδ, hR, hB, hL⟩
  have hB0 := S.B_nonneg
  have hL0 := S.L_nonneg
  have hzR : ‖z‖ < R / 2 := by
    have := norm_le_norm_add_norm_sub' z x
    rw [norm_sub_rev] at this
    linarith [S.hR, norm_nonneg x]
  obtain ⟨k', s, hs, hks⟩ := exists_partialDeriv_partialDeriv_halfSpaceGreenPotential_eq k l
  rw [S.hessian_sub_far_eq hx S.x_lt k l, S.hessian_sub_far_eq hz hzR k l, hks, hks, hks, hks]
  have hxU : x ∈ HalfSpace.upper 2 := hx
  have hzU : z ∈ HalfSpace.upper 2 := hz
  have hloc := abs_partialDeriv_halfPlaneVelocity_sub_le S.continuous_localPiece
    S.hasCompactSupport_localPiece hα hα1 (S.holder_localPiece hK hKb) l k' hxU hzU
  obtain ⟨Mm, hMm⟩ := S.exists_holder_middlePiece
  have hmid := abs_partialDeriv_halfPlaneVelocity_sub_le_of_eq_zero S.continuous_middlePiece
    S.hasCompactSupport_middlePiece hα hα1.le hMm hx hδ S.middlePiece_eq_zero hz hxz hI0
    ((S.lintegral_middlePiece_le 3).trans hI) l k'
  set a := (∂[l] (fun y ↦ halfPlaneVelocity (localPiece x δ R f) y k')) x
  set b := (∂[l] (fun y ↦ halfPlaneVelocity (middlePiece x δ R f) y k')) x
  set a' := (∂[l] (fun y ↦ halfPlaneVelocity (localPiece x δ R f) y k')) z
  set b' := (∂[l] (fun y ↦ halfPlaneVelocity (middlePiece x δ R f) y k')) z
  rw [show s * a + s * b - (s * a' + s * b') = s * ((a - a') + (b - b')) by ring, abs_mul, hs,
    one_mul]
  have ht : 0 ≤ ‖x - z‖ ^ α := by positivity
  have hd : 0 ≤ ‖x - z‖ := norm_nonneg _
  have hc1 : 0 ≤ 211 / (α * (1 - α)) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hπ : 0 ≤ 10 / Real.pi := by positivity
  have hBδ : 0 ≤ B * δ ^ (-α) := mul_nonneg hB0 (Real.rpow_nonneg hδ.le _)
  have hLK : L + K * δ ^ (-α) * B ≤ (1 + K) * (L + B * δ ^ (-α)) := by
    nlinarith [mul_nonneg hK hL0]
  calc |a - a' + (b - b')| ≤ |a - a'| + |b - b'| := abs_add_le _ _
    _ ≤ 211 / (α * (1 - α)) * (L + K * δ ^ (-α) * B) * ‖x - z‖ ^ α +
        10 / Real.pi * ‖x - z‖ * I := add_le_add hloc hmid
    _ ≤ 211 / (α * (1 - α)) * ((1 + K) * (L + B * δ ^ (-α))) * ‖x - z‖ ^ α +
        10 / Real.pi * ‖x - z‖ * I := by gcongr
    _ ≤ (211 / (α * (1 - α)) * (1 + K) + 10 / Real.pi) * (L + B * δ ^ (-α)) * ‖x - z‖ ^ α +
        (211 / (α * (1 - α)) * (1 + K) + 10 / Real.pi) * ‖x - z‖ * I := by
        have hLB : 0 ≤ L + B * δ ^ (-α) := add_nonneg hL0 hBδ
        have e1 : 0 ≤ 10 / Real.pi * (L + B * δ ^ (-α)) * ‖x - z‖ ^ α :=
          mul_nonneg (mul_nonneg hπ hLB) ht
        have e2 : 0 ≤ 211 / (α * (1 - α)) * (1 + K) * ‖x - z‖ * I :=
          mul_nonneg (mul_nonneg (mul_nonneg hc1 (by linarith)) hd) hI0
        nlinarith [e1, e2]

end IncompressibleFlow

end

end
