/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHalfPlaneImage
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
public import PDE.Analysis.Calculus.HalfPlaneSmoothing
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization

/-!
# Singular integrals of odd extensions across the boundary of the half-plane

For `ω` on the closed upper half-plane let `W` be its odd extension across `{y₁ = 0}`
(`oddHalfSpaceExtension`) and `E(y) = ω(y₀, |y₁|)` its even reflection (`evenReflection`). When
`ω` does not vanish on the boundary `W` jumps there, so the Hölder theory of whole-plane singular
integrals does not apply to `W`; it does apply to `E`, which is Hölder on the plane with the
constant of `ω` on the closed half-plane (`abs_evenReflection_sub_le`). Since `W = E` above the
boundary and `W = -E` below it, for `x` in the open upper half-plane

`P.V.∫ K(x - y) W(y) dy = T E(x) - 2 ∫_{y₁<0} K(x - y) E(y) dy`,

the whole-plane singular integral of `E` minus twice its image part. Both are Hölder up to the
boundary (`PlanarSingularIntegral`, `PlanarHalfPlaneImage`). In the bounds below
`H = halfPlaneSingularIntegral K ω`, `M` is the Hölder constant of `ω` on the closed upper
half-plane, `B` a bound of `|ω|` there and `‖E‖₁ = 2 ‖ω‖_{L¹(ℝ²₊)}`. The Hölder estimate depends
on `ω` only through `M`.

## Main definitions

* `halfPlaneSingularIntegral`: `T E(x) - 2 ∫_{y₁<0} K(x - y) E(y) dy`.

## Main results

* `oddHalfSpaceExtension_ae_eq`: `W = E - 2 · 1_{y₁<0} E` almost everywhere.
* `hasPrincipalValueAt_halfPlaneSingularIntegral`: for `x₁ > 0`,
  `P.V.∫ kᵢⱼ(x - y) W(y) dy = H(x)`.
* `abs_halfPlaneSingularIntegral_sub_le`: `|H(x) - H(x')| ≤ 42π/(α(1-α)) · A M |x - x'|^α`.
* `abs_halfPlaneSingularIntegral_le`: `|H(x)| ≤ A (10πM/α + 4B + 3‖E‖₁)`.
* `abs_halfPlaneSingularIntegral_le_log`:
  `|H(x)| ≤ (10πA/α)(1 + B log(2 + M)) + 4AB + 3A ‖E‖₁`.
* `halfPlaneSingularIntegral_sub`: `H` is linear on Hölder data with integrable even extensions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection halfPlaneFold evenReflection_of_nonneg evenReflection_sub
  abs_evenReflection_le abs_evenReflection_sub_le)

namespace GreenFunction

/-- `PDE.Common.lastIndex` is the second coordinate in the plane. -/
theorem lastIndex_two : (PDE.Common.lastIndex : Fin 2) = 1 := rfl

/-- The reflection of the plane in the boundary of the upper half-plane. -/
theorem reflect_two_eq (y : ℝ^2) : HalfSpace.reflect 2 y = !₂[y 0, -y 1] := by
  ext i; fin_cases i <;> simp [HalfSpace.reflect, lastIndex_two]

variable {f : ℝ^2 → ℝ}

/-- Below the boundary the even reflection is `f ∘ reflect`. -/
theorem evenReflection_of_neg {y : ℝ^2} (hy : y 1 < 0) :
    evenReflection f y = f (HalfSpace.reflect 2 y) := by
  rw [evenReflection, halfPlaneFold, reflect_two_eq, abs_of_neg hy]

/-- Off the boundary line the odd extension is `E` above and `-E` below:
`W = E - 2 · 1_{y₁<0} E` almost everywhere. -/
theorem oddHalfSpaceExtension_ae_eq (f : ℝ^2 → ℝ) :
    oddHalfSpaceExtension f =ᵐ[volume] fun y ↦
      evenReflection f y - 2 * {y : ℝ^2 | y 1 < 0}.indicator (evenReflection f) y := by
  have hnull : volume {y : ℝ^2 | y 1 = 0} = 0 := volume_coordinate_eq_zero 1
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  have hy' : y 1 ≠ 0 := hy
  rcases lt_or_gt_of_ne hy' with h | h
  · have hl : y ∈ HalfSpace.lower 2 := h
    have hu : y ∉ HalfSpace.upper 2 := fun hu ↦ by
      have : (0 : ℝ) < y 1 := hu
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem hl, indicator_of_notMem hu,
      indicator_of_mem (show y ∈ {y : ℝ^2 | y 1 < 0} from h), evenReflection_of_neg h]
    ring
  · have hu : y ∈ HalfSpace.upper 2 := h
    have hl : y ∉ HalfSpace.lower 2 := fun hl ↦ by
      have : y 1 < 0 := hl
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem hu, indicator_of_notMem hl,
      indicator_of_notMem (show y ∉ {y : ℝ^2 | y 1 < 0} from fun h' ↦ by
        have : y 1 < 0 := h'
        linarith),
      evenReflection_of_nonneg h.le]
    ring

/-- The even and odd extensions have the same absolute value almost everywhere. -/
theorem abs_oddHalfSpaceExtension_ae_eq (f : ℝ^2 → ℝ) :
    (fun y ↦ |oddHalfSpaceExtension f y|) =ᵐ[volume]
      fun y ↦ |evenReflection f y| := by
  filter_upwards [oddHalfSpaceExtension_ae_eq f] with y hy
  rw [hy]
  by_cases h : y ∈ {y : ℝ^2 | y 1 < 0}
  · rw [indicator_of_mem h]
    rw [show evenReflection f y - 2 * evenReflection f y =
      -evenReflection f y by ring, abs_neg]
  · rw [indicator_of_notMem h, mul_zero, sub_zero]

/-- The principal value of a Hessian kernel against an odd extension at an interior point,
`P.V.∫ K(x - y) W(y) dy`, written as the whole-plane singular integral of the even extension
minus twice its image part. -/
def halfPlaneSingularIntegral (K : ℝ^2 → ℝ) (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  singularIntegral K (evenReflection f) x -
    2 * ∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * evenReflection f y

variable {M α : ℝ}

/-- **The principal value of an odd extension at an interior point.** For `f` Hölder on the
closed upper half-plane with integrable even extension and `x₁ > 0`,
`P.V.∫ kᵢⱼ(x - y) W(y) dy = T E(x) - 2 ∫_{y₁<0} kᵢⱼ(x - y) E(y) dy`. -/
theorem hasPrincipalValueAt_halfPlaneSingularIntegral (i j : Fin 2) (hα : 0 < α)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) {x : ℝ^2} (hx : 0 < x 1) :
    PDE.Analysis.HasPrincipalValueAt univ (fun x y ↦ hessianKernel i j (x - y))
      (oddHalfSpaceExtension f) x (halfPlaneSingularIntegral (hessianKernel i j) f x) := by
  have hK := isSingularKernel_hessianKernel i j
  set E := evenReflection f with hEdef
  set W := oddHalfSpaceExtension f with hWdef
  set L := {y : ℝ^2 | y 1 < 0} with hLdef
  have hEM := abs_evenReflection_sub_le hα.le hM
  have hupper : ∀ y ∈ ball x (x 1), 0 < y 1 := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h := PiLp.norm_apply_le (y - x) 1
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h
    have := neg_abs_le (y 1 - x 1)
    linarith
  have hWE : ∀ y, 0 < y 1 → W y = E y := fun y hy ↦ by
    rw [hWdef, oddHalfSpaceExtension_eqOn f (show y ∈ HalfSpace.upper 2 from hy), hEdef,
      evenReflection_of_nonneg hy.le]
  have hWae : W =ᵐ[volume] fun y ↦ E y - 2 * L.indicator E y := oddHalfSpaceExtension_ae_eq f
  have hLm : MeasurableSet L := measurableSet_lower
  have hEL : Integrable (fun y ↦ E y - 2 * L.indicator E y) :=
    hE.sub ((hE.indicator hLm).const_mul 2)
  have hW : Integrable W := hEL.congr hWae.symm
  have hfar : IntegrableOn (fun y ↦ hessianKernel i j (x - y) * W y) (univ \ ball x (x 1)) := by
    rw [← compl_eq_univ_sdiff]
    exact hK.integrableOn_compl_ball hW x hx
  have hPV := hasPrincipalValueAt_hessianKernel_of_holder i j MeasurableSet.univ hx hα
    (subset_univ _) hW.aestronglyMeasurable (fun y hy ↦ by
      rw [hWE y (hupper y hy), hWE x hx, ← norm_neg (x - y), neg_sub]
      exact hEM y x) hfar
  convert hPV using 1
  -- identify the value
  have h1 : ∫ y in ball x (x 1), hessianKernel i j (x - y) * (W y - W x) =
      ∫ y in ball x (x 1), hessianKernel i j (x - y) * (E y - E x) := by
    refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
    rw [hWE y (hupper y hy), hWE x hx]
  have hLsub : L ⊆ (ball x (x 1))ᶜ := fun y hy hyb ↦ (hupper y hyb).not_gt hy
  have iKE : IntegrableOn (fun y ↦ hessianKernel i j (x - y) * E y) (ball x (x 1))ᶜ :=
    hK.integrableOn_compl_ball hE x hx
  have iKLE : IntegrableOn (fun y ↦ hessianKernel i j (x - y) * L.indicator E y)
      (ball x (x 1))ᶜ := hK.integrableOn_compl_ball (hE.indicator hLm) x hx
  have h2 : ∫ y in univ \ ball x (x 1), hessianKernel i j (x - y) * W y =
      (∫ y in (ball x (x 1))ᶜ, hessianKernel i j (x - y) * E y) -
        2 * ∫ y in L, hessianKernel i j (x - y) * E y := by
    rw [← compl_eq_univ_sdiff]
    have hcongr : ∫ y in (ball x (x 1))ᶜ, hessianKernel i j (x - y) * W y =
        ∫ y in (ball x (x 1))ᶜ, (hessianKernel i j (x - y) * E y -
          2 * (hessianKernel i j (x - y) * L.indicator E y)) :=
      integral_congr_ae ((ae_restrict_of_ae hWae).mono fun y hy ↦ by simp only [hy]; ring)
    rw [hcongr, integral_sub iKE (iKLE.const_mul 2), integral_const_mul]
    congr 2
    rw [show (fun y ↦ hessianKernel i j (x - y) * L.indicator E y) =
        L.indicator (fun y ↦ hessianKernel i j (x - y) * E y) from
      funext fun y ↦ (indicator_mul_right L (fun y ↦ hessianKernel i j (x - y)) E).symm,
      setIntegral_indicator hLm, inter_eq_right.mpr hLsub]
  rw [h1, h2, halfPlaneSingularIntegral, hK.singularIntegral_eq hα hE hEM x hx]
  ring

variable {K : ℝ^2 → ℝ} {A : ℝ}

/-- **Hölder continuity up to the boundary.** For a singular kernel with zero mean on horizontal
lines and `f` Hölder on the closed upper half-plane with integrable even extension, `0 < α < 1`,
`|H(x) - H(x')| ≤ 42π/(α(1-α)) · A M |x - x'|^α` for `x, x'` in the open upper half-plane. -/
theorem abs_halfPlaneSingularIntegral_sub_le (hK : IsSingularKernel K A)
    (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) {x x' : ℝ^2} (hx : 0 < x 1) (hx' : 0 < x' 1) :
    |halfPlaneSingularIntegral K f x - halfPlaneSingularIntegral K f x'| ≤
      42 * Real.pi / (α * (1 - α)) * A * M * ‖x - x'‖ ^ α := by
  have hEM := abs_evenReflection_sub_le hα.le hM
  have h1 := hK.abs_singularIntegral_sub_le hα hα1 hE hEM x x'
  have h2 := hK.abs_integral_lower_sub_le hL hα hα1 hE hEM hx hx'
  rw [halfPlaneSingularIntegral, halfPlaneSingularIntegral]
  calc |singularIntegral K (evenReflection f) x -
        2 * (∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * evenReflection f y) -
      (singularIntegral K (evenReflection f) x' -
        2 * ∫ y in {y : ℝ^2 | y 1 < 0}, K (x' - y) * evenReflection f y)|
      = |(singularIntegral K (evenReflection f) x -
          singularIntegral K (evenReflection f) x') -
        2 * ((∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * evenReflection f y) -
          ∫ y in {y : ℝ^2 | y 1 < 0}, K (x' - y) * evenReflection f y)| := by ring_nf
    _ ≤ _ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_two]
      calc _ ≤ 10 * Real.pi / (α * (1 - α)) * A * M * ‖x - x'‖ ^ α +
            2 * (16 * Real.pi / (α * (1 - α)) * A * M * ‖x - x'‖ ^ α) := by gcongr
        _ = _ := by ring

/-- **Size bound up to the boundary.** For `|f| ≤ B` on the closed upper half-plane,
`|H(x)| ≤ A (10πM/α + 4B + 3‖E‖₁)` at every point of the open upper half-plane. -/
theorem abs_halfPlaneSingularIntegral_le (hK : IsSingularKernel K A)
    (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) {B : ℝ} (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 < x 1) :
    |halfPlaneSingularIntegral K f x| ≤
      A * (10 * Real.pi * M / α + 4 * B + 3 * ∫ y, |evenReflection f y|) := by
  have hEM := abs_evenReflection_sub_le hα.le hM
  have hEB := abs_evenReflection_le hB
  have h1 := hK.abs_singularIntegral_le hα hE hEM x
  have h2 := hK.abs_integral_lower_le hL hα hα1 hE hEM hEB hx
  rw [halfPlaneSingularIntegral]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_two]
  calc _ ≤ A * (2 * Real.pi * M / α + ∫ y, |evenReflection f y|) +
        2 * (A * (4 * Real.pi * M / α + 2 * B + ∫ y, |evenReflection f y|)) := by
        gcongr
    _ = _ := by ring

/-- **Logarithmic size bound up to the boundary.** For `|f| ≤ B` on the closed upper
half-plane, `|H(x)| ≤ (10πA/α)(1 + B log(2 + M)) + 4AB + 3A ‖E‖₁`. -/
theorem abs_halfPlaneSingularIntegral_le_log (hK : IsSingularKernel K A)
    (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) {B : ℝ} (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 < x 1) :
    |halfPlaneSingularIntegral K f x| ≤
      10 * Real.pi * A / α * (1 + B * Real.log (2 + M)) + 4 * A * B +
        3 * A * ∫ y, |evenReflection f y| := by
  have hEM := abs_evenReflection_sub_le hα.le hM
  have hEB := abs_evenReflection_le hB
  have h1 := hK.abs_singularIntegral_le_log hα hE hEM hEB x
  have h2 := hK.abs_integral_lower_le_log hL hα hα1 hE hEM hEB hx
  rw [halfPlaneSingularIntegral]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_two]
  calc _ ≤ 2 * Real.pi * A / α * (1 + B * Real.log (2 + M)) +
          A * (∫ y, |evenReflection f y|) +
        2 * (4 * Real.pi * A / α * (1 + B * Real.log (2 + M)) + 2 * A * B +
          A * ∫ y, |evenReflection f y|) := by gcongr
    _ = _ := by ring

/-- The half-plane singular integral is linear on Hölder data with integrable even extensions. -/
theorem halfPlaneSingularIntegral_sub {g : ℝ^2 → ℝ} {Mg : ℝ} (hK : IsSingularKernel K A)
    (hα : 0 < α) (hMf : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hMg : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ Mg * ‖y - z‖ ^ α)
    (hEf : Integrable (evenReflection f)) (hEg : Integrable (evenReflection g))
    {x : ℝ^2} (hx : 0 < x 1) :
    halfPlaneSingularIntegral K (f - g) x =
      halfPlaneSingularIntegral K f x - halfPlaneSingularIntegral K g x := by
  unfold halfPlaneSingularIntegral
  rw [evenReflection_sub, hK.singularIntegral_sub hα hEf hEg (abs_evenReflection_sub_le hα.le hMf)
    (abs_evenReflection_sub_le hα.le hMg) x]
  have h1 := hK.integrableOn_lower_mul hEf hx
  have h2 := hK.integrableOn_lower_mul hEg hx
  have e : ∫ y in {y : ℝ^2 | y 1 < 0},
      K (x - y) * (evenReflection f - evenReflection g) y =
      (∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * evenReflection f y) -
        ∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * evenReflection g y := by
    rw [← integral_sub h1 h2]
    congr 1; funext y; simp only [Pi.sub_apply]; ring
  rw [e]
  ring

end GreenFunction
