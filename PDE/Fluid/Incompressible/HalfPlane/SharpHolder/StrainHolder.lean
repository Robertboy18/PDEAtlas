/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Integration.Rectangle.MixedPrimitive
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainTransport
public import PDE.Spaces.Holder.Directional
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The horizontal Hölder estimate of the localized strain

Chen and Hou, Part I, Lemma 3.1: for a kernel `K(y) = y₁ y₂ / |y|⁴` and a function `W` on the
plane (the odd extension of the vorticity), the principal values

`P(x) = P.V. ∫_{Q(x)} K(x - y) W(y) dy`

over the boxes `Q(x) = [x₁ - a, x₁ + a] × [x₂ - b₁, x₂ + b₂]` satisfy, for two points at the same
height with `a ≥ |x₁ - z₁| / 2`,

`|P(x) - P(z)| / (π |x - z|^{1/2}) ≤ C₁(max(b₁, b₂) / |x - z|) [W]_{C_x^{1/2}(Q(x) ∪ Q(z))}`,

with the constant `C₁ = strainConstant` of the transport estimate.

The principal value is that of the ball truncations. Reflecting in the vertical line through `x`
pairs `y` with `R y = (2 x₁ - y₁, y₂)`; since `K` is odd in its first coordinate,

`∫_{Q(x) ∖ B(x, ε)} K(x - y) W(y) dy = ∫_{Q(x) ∖ B(x, ε), y₁ < x₁} K(x - y) (W(y) - W(R y)) dy`,

whose integrand is bounded by `√2 [W]_x |x - y|^{-3/2}`; dominated convergence gives the
principal value as an absolutely convergent integral (`tendsto_setIntegral_diff_ball`). Fubini on
that integrand, followed by undoing the reflection on each horizontal line off the pole, writes
`P(x) - P(z)` as an integral over heights of one-dimensional integrals against the localized
kernel `k_A`, each bounded by the line estimate `abs_integral_localStrainDifference_mul_le`.

## Main results

* `tendsto_setIntegral_diff_ball`: existence of the principal value over a bounded set symmetric
  in the vertical line through the point, from the horizontal Hölder seminorm alone.
* `abs_sub_div_le_strainConstant`: Part I, Lemma 3.1.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (3.4), p. 27, Lemma 3.1, p. 28, and
  Section 3.3, pp. 31-36.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric PDE.Common
open PDE.Analysis (planeEquiv measurePreserving_planeEquiv planeEquivSwap planeEquivSwap_apply
  measurePreserving_planeEquivSwap)
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

/-! ### Coordinates and the reflection -/

/-- The reflection `R y = (2c - y₁, y₂)` in the vertical line `{y₁ = c}`. -/
def verticalReflection (c : ℝ) (y : ℝ^2) : ℝ^2 :=
  coordinateReflection 0 y + EuclideanSpace.single 0 (2 * c)

/-- The first coordinate of the reflection is `2c - y₁`. -/
theorem verticalReflection_zero (c : ℝ) (y : ℝ^2) : verticalReflection c y 0 = 2 * c - y 0 := by
  simp [verticalReflection, coordinateReflection_apply_same]
  ring

/-- The reflection keeps the height. -/
theorem verticalReflection_one (c : ℝ) (y : ℝ^2) : verticalReflection c y 1 = y 1 := by
  simp [verticalReflection]

/-- The reflection is an involution. -/
theorem verticalReflection_verticalReflection (c : ℝ) (y : ℝ^2) :
    verticalReflection c (verticalReflection c y) = y := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, verticalReflection_zero]
    ring
  · simp [verticalReflection_one]

/-- The reflection preserves Lebesgue measure. -/
theorem measurePreserving_verticalReflection (c : ℝ) :
    MeasurePreserving (verticalReflection c) volume volume :=
  (measurePreserving_add_right volume _).comp (measurePreserving_coordinateReflection 0)

/-- The reflection as a measurable equivalence. -/
def verticalReflectionEquiv (c : ℝ) : ℝ^2 ≃ᵐ ℝ^2 where
  toFun := verticalReflection c
  invFun := verticalReflection c
  left_inv := verticalReflection_verticalReflection c
  right_inv := verticalReflection_verticalReflection c
  measurable_toFun := (measurePreserving_verticalReflection c).measurable
  measurable_invFun := (measurePreserving_verticalReflection c).measurable

/-- The reflection is a measurable embedding. -/
theorem measurableEmbedding_verticalReflection (c : ℝ) :
    MeasurableEmbedding (verticalReflection c) :=
  (verticalReflectionEquiv c).measurableEmbedding

/-- `x - R y` is the coordinate reflection of `x - y` for the line through `x`. -/
theorem sub_verticalReflection (x y : ℝ^2) :
    x - verticalReflection (x 0) y = coordinateReflection 0 (x - y) := by
  ext i
  fin_cases i
  · simp [verticalReflection_zero, coordinateReflection_apply_same]
    ring
  · simp [verticalReflection_one]

/-- The reflection in the vertical line through `x` preserves distances to `x`. -/
theorem norm_sub_verticalReflection (x y : ℝ^2) :
    ‖x - verticalReflection (x 0) y‖ = ‖x - y‖ := by
  rw [sub_verticalReflection, norm_coordinateReflection]

/-- A vertical line `{y₁ = c}` is a null set. -/
theorem volume_setOf_zero_eq (c : ℝ) : volume {y : ℝ^2 | y 0 = c} = 0 := by
  have hs : MeasurableSet {y : ℝ^2 | y 0 = c} :=
    measurableSet_eq_fun (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable measurable_const
  rw [← measurePreserving_planeEquivSwap.measure_preimage hs.nullMeasurableSet]
  have : planeEquivSwap ⁻¹' {y : ℝ^2 | y 0 = c} = univ ×ˢ {c} := by
    ext p
    simp [planeEquivSwap_apply]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-! ### The kernel -/

variable {K : ℝ^2 → ℝ}

/-- A kernel with `K(y) = y₁ y₂ / |y|⁴` is `strainDensity` in coordinates. -/
theorem kernel_apply (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (v : ℝ^2) :
    K v = strainDensity (v 0) (v 1) := by
  rw [hK, strainDensity_eq, show ‖v‖ ^ 4 = (‖v‖ ^ 2) ^ 2 by ring, EuclideanSpace.norm_sq_fin_two]

/-- The kernel is odd under the reflection in the vertical line through `x`. -/
theorem kernel_sub_verticalReflection (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (x y : ℝ^2) :
    K (x - verticalReflection (x 0) y) = -K (x - y) := by
  rw [sub_verticalReflection, kernel_apply hK, kernel_apply hK, coordinateReflection_apply_same,
    coordinateReflection_apply_of_ne (0 : Fin 2) (1 : Fin 2) (by decide), strainDensity_neg_left]

/-- `|K(v)| ≤ 1 / (2 |v|²)`. -/
theorem abs_kernel_le (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (v : ℝ^2) :
    |K v| ≤ 1 / (2 * ‖v‖ ^ 2) := by
  rw [kernel_apply hK, EuclideanSpace.norm_sq_fin_two]
  exact abs_strainDensity_le _ _

/-- The kernel is measurable. -/
theorem measurable_kernel (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) : Measurable K := by
  have : K = fun v ↦ strainDensity (v 0) (v 1) := funext (kernel_apply hK)
  rw [this]
  simp only [strainDensity_eq]
  fun_prop

/-! ### The principal value -/

/-- The bound `|K(x - y)| |W(y) - W(R y)| ≤ √2 C |x - y|^{-3/2}` of the reflected integrand. -/
theorem abs_kernel_mul_sub_le (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {S : Set (ℝ^2)}
    {W : ℝ^2 → ℝ} {C : ℝ≥0} (hC : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≤ C)
    {x y : ℝ^2} (hy : y ∈ S) (hRy : verticalReflection (x 0) y ∈ S) :
    |K (x - y) * (W y - W (verticalReflection (x 0) y))| ≤
      Real.sqrt 2 * C * ‖x - y‖ ^ (-(3 / 2 : ℝ)) := by
  have hW : |W y - W (verticalReflection (x 0) y)| ≤ C * |2 * (x 0 - y 0)| ^ (1 / 2 : ℝ) := by
    have h := HolderSpace.dist_le_directionalSeminorm_mul (i := 0) (α := 1 / 2)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hC) hy hRy fun j hj ↦ by
        fin_cases j
        exacts [absurd rfl hj, (verticalReflection_one _ _).symm]
    rw [Real.dist_eq, verticalReflection_zero,
      show y 0 - (2 * x 0 - y 0) = -(2 * (x 0 - y 0)) by ring, abs_neg] at h
    exact h.trans (mul_le_mul (ENNReal.toReal_le_coe_of_le_coe hC) (le_of_eq (by norm_num))
      (by positivity) C.2)
  set v := x - y
  have hv0 : v 0 = x 0 - y 0 := by simp [v]
  by_cases hv : v = 0
  · have : K v = 0 := by rw [kernel_apply hK, hv]; simp [strainDensity_eq]
    rw [this, zero_mul, abs_zero]
    positivity
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h0 := EuclideanSpace.abs_apply_le_norm v 0
  have h1 := EuclideanSpace.abs_apply_le_norm v 1
  rw [abs_mul, kernel_apply hK, strainDensity_eq, abs_div, abs_mul,
      ← EuclideanSpace.norm_sq_fin_two,
    abs_of_pos (by positivity : 0 < (‖v‖ ^ 2) ^ 2)]
  rw [← hv0] at hW
  calc |v 0| * |v 1| / (‖v‖ ^ 2) ^ 2 * |W y - W (verticalReflection (x 0) y)|
      ≤ |v 0| * |v 1| / (‖v‖ ^ 2) ^ 2 * (C * |2 * v 0| ^ (1 / 2 : ℝ)) := by gcongr
    _ = Real.sqrt 2 * C * (|v 0| ^ (3 / 2 : ℝ) * |v 1|) / ‖v‖ ^ (4 : ℝ) := by
        rw [abs_mul, abs_two, Real.mul_rpow (by norm_num) (abs_nonneg _),
          ← Real.sqrt_eq_rpow, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (abs_nonneg _) (by norm_num),
          Real.rpow_one]
        ring
    _ ≤ Real.sqrt 2 * C * (‖v‖ ^ (3 / 2 : ℝ) * ‖v‖) / ‖v‖ ^ (4 : ℝ) := by
        gcongr
    _ = Real.sqrt 2 * C * ‖v‖ ^ (-(3 / 2 : ℝ)) := by
        rw [mul_div_assoc]
        congr 1
        rw [← Real.rpow_add_one hn.ne', ← Real.rpow_sub hn]
        norm_num

/-- The half-plane `{y₁ < c}` is measurable. -/
theorem measurableSet_lt_coord (c : ℝ) : MeasurableSet {y : ℝ^2 | y 0 < c} :=
  measurableSet_lt (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable measurable_const

/-- The reflected integrand `K(x - y) (W(y) - W(R y))` is measurable. -/
private theorem aestronglyMeasurable_kernel_mul_sub (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4)
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) (x : ℝ^2) :
    AEStronglyMeasurable fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y)) :=
  ((measurable_kernel hK).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
    (hWm.sub (hWm.comp_measurePreserving (measurePreserving_verticalReflection (x 0))))

/-- The reflected integrand `K(x - y) (W(y) - W(R y))` is integrable on the left half
`{y ∈ S, y₁ < x₁}` of a bounded set `S` symmetric in the vertical line through `x`, when `W` has
horizontal `1/2`-Hölder seminorm at most `C` on `S`: it is bounded by `√2 C |x - y|^{-3/2}`. -/
theorem integrableOn_kernel_mul_sub (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {S : Set (ℝ^2)}
    {x : ℝ^2} (hSm : MeasurableSet S) (hSR : ∀ y ∈ S, verticalReflection (x 0) y ∈ S)
    (hSb : Bornology.IsBounded S) {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≤ C) :
    IntegrableOn (fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y)))
      (S ∩ {y | y 0 < x 0}) := by
  set S' := S ∩ {y : ℝ^2 | y 0 < x 0} with hS'_def
  have hS'm : MeasurableSet S' := hSm.inter (measurableSet_lt_coord _)
  obtain ⟨r, hr⟩ := hSb.subset_closedBall x
  set F : ℝ^2 → ℝ := fun v ↦
    S'.indicator (fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y))) (v + x)
  have hFb : ∀ v, ‖F v‖ ≤ Real.sqrt 2 * C * ‖v‖ ^ (-(3 / 2 : ℝ)) := fun v ↦ by
    by_cases hv : v + x ∈ S'
    · simp only [F, indicator_of_mem hv, Real.norm_eq_abs]
      have h := abs_kernel_mul_sub_le hK hC (x := x) hv.1 (hSR _ hv.1)
      rw [show x - (v + x) = -v by abel, norm_neg] at h
      rwa [show x - (v + x) = -v by abel]
    · simp only [F, indicator_of_notMem hv, norm_zero]
      positivity
  have hFm : AEStronglyMeasurable F :=
    ((aestronglyMeasurable_kernel_mul_sub hK hWm x).indicator hS'm).comp_measurePreserving
      (measurePreserving_add_right volume x)
  have hFball : IntegrableOn F (ball 0 (r + 1)) :=
    integrableOn_ball_of_norm_le_rpow (by simp) (by norm_num) (ae_of_all _ hFb) hFm
  have hsupp : Function.support F ⊆ ball 0 (r + 1) := fun v hv ↦ by
    by_contra hvb
    refine hv (indicator_of_notMem (fun h ↦ hvb ?_) _)
    have := hr h.1
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right] at this
    exact mem_ball_zero_iff.2 (by linarith)
  have hFint : Integrable F := (integrableOn_iff_integrable_of_support_subset hsupp).1 hFball
  have h := hFint.comp_sub_right x
  simp only [F, sub_add_cancel] at h
  exact (integrable_indicator_iff hS'm).1 h

/-- **The principal value of the strain kernel** over a bounded measurable set `S` symmetric in
the vertical line through `x`: if `W` is integrable on `S` with horizontal `1/2`-Hölder seminorm
at most `C` there, the ball truncations converge to the absolutely convergent integral
`∫_{y ∈ S, y₁ < x₁} K(x - y) (W(y) - W(R y)) dy`. -/
theorem tendsto_setIntegral_diff_ball (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {S : Set (ℝ^2)}
    {x : ℝ^2} (hSm : MeasurableSet S) (hSR : ∀ y ∈ S, verticalReflection (x 0) y ∈ S)
    (hSb : Bornology.IsBounded S) {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W)
    (hWi : IntegrableOn W S) {C : ℝ≥0} (hC : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≤ C) :
    Tendsto (fun ε ↦ ∫ y in S \ ball x ε, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 (∫ y in S ∩ {y | y 0 < x 0}, K (x - y) * (W y - W (verticalReflection (x 0) y)))) := by
  set S' := S ∩ {y : ℝ^2 | y 0 < x 0} with hS'_def
  have hS'm : MeasurableSet S' := hSm.inter (measurableSet_lt_coord _)
  have hRmp := measurePreserving_verticalReflection (x 0)
  have hRemb := measurableEmbedding_verticalReflection (x 0)
  have hKx : Measurable fun y ↦ K (x - y) :=
    (measurable_kernel hK).comp (measurable_const.sub measurable_id)
  have hRS : verticalReflection (x 0) ⁻¹' S = S := Subset.antisymm
    (fun y hy ↦ by simpa only [verticalReflection_verticalReflection] using hSR _ hy) hSR
  have hWRi : IntegrableOn (fun y ↦ W (verticalReflection (x 0) y)) S := by
    simpa only [hRS, Function.comp_def] using
      (hRmp.integrableOn_comp_preimage hRemb (f := W) (s := S)).2 hWi
  have hGi := integrableOn_kernel_mul_sub hK hSm hSR hSb hWm hC
  -- the truncated integrals
  have htrunc : ∀ ε > 0, ∫ y in S \ ball x ε, K (x - y) * W y =
      ∫ y in S' \ ball x ε, K (x - y) * (W y - W (verticalReflection (x 0) y)) := fun ε hε ↦ by
    set Rε := S \ ball x ε
    have hRεm : MeasurableSet Rε := hSm.diff measurableSet_ball
    have hRεR : verticalReflection (x 0) ⁻¹' Rε = Rε := by
      ext y
      simp only [Rε, mem_preimage, Set.mem_sdiff, mem_ball, dist_eq_norm]
      rw [← norm_neg (verticalReflection (x 0) y - x), neg_sub, ← norm_neg (y - x), neg_sub,
        norm_sub_verticalReflection]
      exact and_congr_left' (Set.ext_iff.1 hRS y)
    have hKb : ∀ y ∈ Rε, ‖K (x - y)‖ ≤ 1 / (2 * ε ^ 2) := fun y hy ↦ by
      have hd : ε ≤ ‖x - y‖ := dist_eq_norm x y ▸ not_lt.1 fun h ↦ hy.2 (mem_ball'.2 h)
      rw [Real.norm_eq_abs]
      exact (abs_kernel_le hK _).trans (by gcongr)
    have hi₁ : IntegrableOn (fun y ↦ K (x - y) * W y) Rε :=
      (hWi.mono_set sdiff_subset).bdd_mul hKx.aestronglyMeasurable.restrict
        ((ae_restrict_iff' hRεm).2 (Eventually.of_forall hKb))
    have hi₂ : IntegrableOn (fun y ↦ K (x - y) * W (verticalReflection (x 0) y)) Rε :=
      (hWRi.mono_set sdiff_subset).bdd_mul hKx.aestronglyMeasurable.restrict
        ((ae_restrict_iff' hRεm).2 (Eventually.of_forall hKb))
    have hset : Rε ∩ {y : ℝ^2 | y 0 < x 0} = S' \ ball x ε := by
      ext y
      simp only [Rε, S', mem_inter_iff, Set.mem_sdiff, mem_ofPred_eq]
      tauto
    have hcompl : Rε \ {y : ℝ^2 | y 0 < x 0} =
        verticalReflection (x 0) ⁻¹' (Rε ∩ {y : ℝ^2 | y 0 ≤ x 0}) := by
      ext y
      rw [preimage_inter, hRεR]
      simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, mem_preimage,
        verticalReflection_zero, not_lt]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
    have hae : (Rε ∩ {y : ℝ^2 | y 0 ≤ x 0} : Set (ℝ^2)) =ᵐ[volume]
        (Rε ∩ {y : ℝ^2 | y 0 < x 0} : Set (ℝ^2)) :=
      eventuallyEqSet_iff.2 <| (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))).mono
        fun y hy ↦ and_congr_right' (by
          simp only [mem_ofPred_eq]; exact ⟨fun h ↦ lt_of_le_of_ne h hy, le_of_lt⟩)
    rw [← integral_inter_add_sdiff (measurableSet_lt_coord (x 0)) hi₁, hcompl]
    have hrefl : ∫ y in verticalReflection (x 0) ⁻¹' (Rε ∩ {y : ℝ^2 | y 0 ≤ x 0}), K (x - y) * W y =
        -∫ y in Rε ∩ {y : ℝ^2 | y 0 < x 0}, K (x - y) * W (verticalReflection (x 0) y) := by
      have h := hRmp.setIntegral_preimage_emb hRemb
        (fun y ↦ K (x - verticalReflection (x 0) y) * W (verticalReflection (x 0) y))
        (Rε ∩ {y : ℝ^2 | y 0 ≤ x 0})
      simp only [verticalReflection_verticalReflection] at h
      rw [h, setIntegral_congr_set hae, ← integral_neg]
      refine setIntegral_congr_fun ((hRεm.inter (measurableSet_lt_coord _))) fun y _ ↦ ?_
      rw [kernel_sub_verticalReflection hK, neg_mul]
    rw [hrefl, ← sub_eq_add_neg, ← integral_sub (hi₁.mono_set inter_subset_left)
      (hi₂.mono_set inter_subset_left), hset]
    refine setIntegral_congr_fun (hS'm.diff measurableSet_ball) fun y _ ↦ ?_
    ring
  -- dominated convergence
  have hlim : Tendsto
      (fun ε ↦ ∫ y in S' \ ball x ε, K (x - y) * (W y - W (verticalReflection (x 0) y)))
      (𝓝[>] 0)
      (𝓝 (∫ y in S', K (x - y) * (W y - W (verticalReflection (x 0) y)))) := by
    simp only [← integral_indicator (hS'm.diff measurableSet_ball), ← integral_indicator hS'm]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y ↦ ‖S'.indicator (fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y))) y‖)
      (Eventually.of_forall fun ε ↦
        (aestronglyMeasurable_kernel_mul_sub hK hWm x).indicator (hS'm.diff measurableSet_ball))
      (Eventually.of_forall fun ε ↦ Eventually.of_forall fun y ↦
        norm_indicator_le_of_subset sdiff_subset _ y)
      (hGi.integrable_indicator hS'm).norm (Eventually.of_forall fun y ↦ ?_)
    by_cases hyS : y ∈ S'
    · have hd : 0 < dist y x := dist_pos.2 fun h ↦ lt_irrefl (x 0) (h ▸ hyS.2)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
      rw [indicator_of_mem hyS, indicator_of_mem (show y ∈ S' \ ball x ε from
        ⟨hyS, fun h ↦ (mem_ball.1 h).not_ge hε.2.le⟩)]
    · simp [hyS]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (htrunc ε hε).symm

/-! ### Horizontal lines -/

/-- The reflection in coordinates: `R (s, t) = (2c - s, t)`. -/
theorem verticalReflection_mk (c s t : ℝ) : verticalReflection c !₂[s, t] = !₂[2 * c - s, t] := by
  ext i
  fin_cases i
  · simp [verticalReflection_zero]
  · simp [verticalReflection_one]

/-- The kernel at `x - (s, t)` in coordinates. -/
theorem kernel_sub_mk (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (x : ℝ^2) (s t : ℝ) :
    K (x - !₂[s, t]) = strainDensity (x 0 - s) (x 1 - t) := by
  rw [kernel_apply hK]
  simp

/-- On a horizontal line off the height of `x`, `s ↦ K(x - (s, t))` is continuous. -/
private theorem continuous_kernel_sub_mk (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (x : ℝ^2) {t : ℝ}
    (ht : t ≠ x 1) : Continuous fun s ↦ K (x - !₂[s, t]) := by
  simp only [kernel_sub_mk hK]
  exact (continuous_strainDensity_left (sub_ne_zero.2 ht.symm)).comp
    (continuous_const.sub continuous_id)

/-- On a horizontal line off the pole the reflection can be undone:
`∫_{I, s < x₁} K(x - (s, t)) (W(s, t) - W(2x₁ - s, t)) ds = ∫_I K(x - (s, t)) W(s, t) ds` for the
interval `I = [x₁ - a, x₁ + a]` symmetric about `x₁`. -/
theorem setIntegral_inter_Iio_eq (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x : ℝ^2} {a t : ℝ}
    (ht : t ≠ x 1) {W : ℝ^2 → ℝ}
    (hWc : ContinuousOn (fun s ↦ W !₂[s, t]) (Icc (x 0 - a) (x 0 + a))) :
    ∫ s in Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0),
        K (x - !₂[s, t]) * (W !₂[s, t] - W (verticalReflection (x 0) !₂[s, t])) =
      ∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t] := by
  set I := Icc (x 0 - a) (x 0 + a)
  have hk := continuous_kernel_sub_mk hK x ht
  set ρ : ℝ → ℝ := fun s ↦ 2 * x 0 - s
  have hρI : ∀ s ∈ I, ρ s ∈ I := fun s hs ↦ ⟨by simp only [ρ]; linarith [hs.2],
    by simp only [ρ]; linarith [hs.1]⟩
  have hρρ : ∀ s, ρ (ρ s) = s := fun s ↦ by simp only [ρ]; ring
  have hWρ : ContinuousOn (fun s ↦ W !₂[ρ s, t]) I :=
    hWc.comp (continuous_const.sub continuous_id).continuousOn hρI
  have hi₁ : IntegrableOn (fun s ↦ K (x - !₂[s, t]) * W !₂[s, t]) I :=
    (hk.continuousOn.mul hWc).integrableOn_compact isCompact_Icc
  have hi₂ : IntegrableOn (fun s ↦ K (x - !₂[s, t]) * W !₂[ρ s, t]) I :=
    (hk.continuousOn.mul hWρ).integrableOn_compact isCompact_Icc
  have hmp : MeasurePreserving ρ volume volume := Measure.measurePreserving_sub_left volume _
  have hemb : MeasurableEmbedding ρ := (Homeomorph.subLeft (2 * x 0)).measurableEmbedding
  -- the reflected half
  have hpre : ρ ⁻¹' (I ∩ Ioi (x 0)) = I ∩ Iio (x 0) := by
    ext s
    simp only [ρ, I, mem_preimage, mem_inter_iff, mem_Icc, mem_Ioi, mem_Iio]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
  have hrefl : ∫ s in I ∩ Iio (x 0), K (x - !₂[s, t]) * W !₂[ρ s, t] =
      -∫ s in I ∩ Ioi (x 0), K (x - !₂[s, t]) * W !₂[s, t] := by
    have h := hmp.setIntegral_preimage_emb hemb
      (fun u ↦ K (x - !₂[ρ u, t]) * W !₂[u, t]) (I ∩ Ioi (x 0))
    simp only [hρρ, hpre] at h
    rw [h, ← integral_neg]
    refine setIntegral_congr_fun (measurableSet_Icc.inter measurableSet_Ioi) fun u _ ↦ ?_
    have := kernel_sub_verticalReflection hK x !₂[u, t]
    rw [verticalReflection_mk] at this
    simp only [ρ, this, neg_mul]
  have hsplit : ∫ s in I, K (x - !₂[s, t]) * W !₂[s, t] =
      (∫ s in I ∩ Iio (x 0), K (x - !₂[s, t]) * W !₂[s, t]) +
        ∫ s in I ∩ Ioi (x 0), K (x - !₂[s, t]) * W !₂[s, t] := by
    rw [← integral_inter_add_sdiff measurableSet_Iio hi₁, sdiff_eq, compl_Iio,
      setIntegral_congr_set (EventuallyEqSet.rfl.inter Ioi_ae_eq_Ici.symm)]
  simp only [verticalReflection_mk]
  change ∫ s in I ∩ Iio (x 0), K (x - !₂[s, t]) * (W !₂[s, t] - W !₂[ρ s, t]) = _
  simp only [mul_sub]
  rw [integral_sub (hi₁.mono_set inter_subset_left) (hi₂.mono_set inter_subset_left), hrefl,
    hsplit, sub_neg_eq_add]

/-! ### Scaling a horizontal difference -/

/-- `K₁` is homogeneous of degree `-2`. -/
theorem strainDensity_mul {d : ℝ} (hd : d ≠ 0) (a b : ℝ) :
    strainDensity (d * a) (d * b) = strainDensity a b / d ^ 2 := by
  simp only [strainDensity_eq]
  rcases eq_or_ne (a ^ 2 + b ^ 2) 0 with h | h
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha, hb]
  · field_simp

/-- `s ∈ [c - a, c + a]` exactly when `|s - c| ≤ a`. -/
theorem mem_Icc_iff_abs_sub_le {c a s : ℝ} : s ∈ Icc (c - a) (c + a) ↔ |s - c| ≤ a := by
  rw [mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The difference of two horizontal line integrals at heights equal to that of `x` and `z`,
rescaled to the unit distance: with `d = x₁ - z₁ > 0`, `m = (x₁ + z₁)/2` and `t` off the common
height `x₂`,
`∫_{|s - x₁| ≤ a} K(x - (s, t)) W(s, t) ds - ∫_{|s - z₁| ≤ a} K(z - (s, t)) W(s, t) ds =
d⁻¹ ∫ k_{a/d}(u, (x₂ - t)/d) W(m + d u, t) du`. -/
theorem integral_sub_integral_eq (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x z : ℝ^2}
    (hxz : x 1 = z 1) (hd : z 0 < x 0) {a t : ℝ} (ht : t ≠ x 1) {W : ℝ^2 → ℝ}
    (hix : IntegrableOn (fun s ↦ K (x - !₂[s, t]) * W !₂[s, t]) (Icc (x 0 - a) (x 0 + a)))
    (hiz : IntegrableOn (fun s ↦ K (z - !₂[s, t]) * W !₂[s, t]) (Icc (z 0 - a) (z 0 + a))) :
    (∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t]) -
        ∫ s in Icc (z 0 - a) (z 0 + a), K (z - !₂[s, t]) * W !₂[s, t] =
      (x 0 - z 0)⁻¹ * ∫ u, localStrainDifference (a / (x 0 - z 0)) u ((x 1 - t) / (x 0 - z 0)) *
        W !₂[(x 0 + z 0) / 2 + (x 0 - z 0) * u, t] := by
  set d := x 0 - z 0 with hd_def
  have hd0 : 0 < d := sub_pos.2 hd
  set m := (x 0 + z 0) / 2
  set σ := (x 1 - t) / d
  set Φ : ℝ → ℝ := fun s ↦ (Icc (x 0 - a) (x 0 + a)).indicator
    (fun s ↦ K (x - !₂[s, t]) * W !₂[s, t]) s - (Icc (z 0 - a) (z 0 + a)).indicator
    (fun s ↦ K (z - !₂[s, t]) * W !₂[s, t]) s
  have hΦ : (∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t]) -
      ∫ s in Icc (z 0 - a) (z 0 + a), K (z - !₂[s, t]) * W !₂[s, t] = ∫ s, Φ s := by
    rw [integral_sub (hix.integrable_indicator measurableSet_Icc)
      (hiz.integrable_indicator measurableSet_Icc), integral_indicator measurableSet_Icc,
      integral_indicator measurableSet_Icc]
  have hscale : ∫ s, Φ s = d * ∫ u, Φ (m + d * u) := by
    have h := Measure.integral_comp_mul_left (fun v ↦ Φ (m + v)) d
    rw [integral_add_left_eq_self m (μ := volume) (f := Φ), abs_inv, abs_of_pos hd0,
      smul_eq_mul] at h
    rw [h]
    field_simp
  have hpt : ∀ u, Φ (m + d * u) =
      localStrainDifference (a / d) u σ * W !₂[m + d * u, t] / d ^ 2 := fun u ↦ by
    have hx0 : x 0 = m + d * (1 / 2) := by simp only [m, d]; ring
    have hz0 : z 0 = m + d * (-(1 / 2)) := by simp only [m, d]; ring
    have hσd : x 1 - t = d * σ := by simp only [σ]; field_simp
    have hcx : m + d * u ∈ Icc (x 0 - a) (x 0 + a) ↔ |u - 1 / 2| ≤ a / d := by
      rw [mem_Icc_iff_abs_sub_le, le_div_iff₀ hd0, hx0, show m + d * u - (m + d * (1 / 2)) =
        d * (u - 1 / 2) by ring, abs_mul, abs_of_pos hd0, mul_comm]
    have hcz : m + d * u ∈ Icc (z 0 - a) (z 0 + a) ↔ |u + 1 / 2| ≤ a / d := by
      rw [mem_Icc_iff_abs_sub_le, le_div_iff₀ hd0, hz0, show m + d * u - (m + d * (-(1 / 2))) =
        d * (u + 1 / 2) by ring, abs_mul, abs_of_pos hd0, mul_comm]
    have hKx : K (x - !₂[m + d * u, t]) = -strainDensity (u - 1 / 2) σ / d ^ 2 := by
      rw [kernel_sub_mk hK, hσd, show x 0 - (m + d * u) = d * (-(u - 1 / 2)) by rw [hx0]; ring,
        strainDensity_mul hd0.ne', strainDensity_neg_left, neg_div]
    have hKz : K (z - !₂[m + d * u, t]) = -strainDensity (u + 1 / 2) σ / d ^ 2 := by
      rw [kernel_sub_mk hK, ← hxz, hσd,
        show z 0 - (m + d * u) = d * (-(u + 1 / 2)) by rw [hz0]; ring,
        strainDensity_mul hd0.ne', strainDensity_neg_left, neg_div]
    simp only [Φ, indicator, localStrainDifference]
    by_cases h₁ : |u - 1 / 2| ≤ a / d <;> by_cases h₂ : |u + 1 / 2| ≤ a / d <;>
      simp only [h₁, h₂, hcx, hcz, ite_true, ite_false, hKx, hKz] <;> ring
  rw [hΦ, hscale]
  simp only [hpt, integral_div]
  field_simp

/-! ### Integrating over heights -/

/-- The affine substitution `σ = (t - e)/c` in a lower integral over the line. -/
theorem setLIntegral_comp_div_sub {c : ℝ} (hc : c ≠ 0) (e : ℝ) (F : ℝ → ℝ≥0∞) (S : Set ℝ) :
    ∫⁻ t in (fun t ↦ (t - e) / c) ⁻¹' S, F ((t - e) / c) =
      ENNReal.ofReal |c| * ∫⁻ σ in S, F σ := by
  set φ : ℝ ≃ᵐ ℝ :=
    (MeasurableEquiv.subRight e).trans (MeasurableEquiv.mulLeft₀ c⁻¹ (inv_ne_zero hc))
  have hφ : ⇑φ = fun t ↦ (t - e) / c := by
    ext t
    change c⁻¹ * (t - e) = (t - e) / c
    ring
  have hmap : Measure.map φ volume = ENNReal.ofReal |c| • volume := by
    have h₁ : Measure.map (fun t : ℝ ↦ t - e) volume = volume :=
      (measurePreserving_sub_right volume e).map_eq
    have h₂ := Real.map_volume_mul_left (inv_ne_zero hc)
    rw [inv_inv] at h₂
    have : ⇑φ = (fun t ↦ c⁻¹ * t) ∘ fun t ↦ t - e := by
      ext t
      rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) (measurable_sub_const e), h₁, h₂]
  have hmp : MeasurePreserving φ volume (ENNReal.ofReal |c| • volume) := ⟨φ.measurable, hmap⟩
  have h := hmp.setLIntegral_comp_preimage_emb φ.measurableEmbedding F S
  rw [hφ] at h
  rw [h, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-- Integrating a function of `|h - t| / d` over the heights `[h - b₁, h + b₂]`. -/
theorem lintegral_Icc_abs_div_le {h b₁ b₂ d : ℝ} (hd : 0 < d) (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc (h - b₁) (h + b₂), F (|h - t| / d) ≤
      ENNReal.ofReal d * ((∫⁻ σ in Ioo 0 (b₁ / d), F σ) + ∫⁻ σ in Ioo 0 (b₂ / d), F σ) := by
  have hsub : Icc (h - b₁) (h + b₂) ≤ᵐ[volume] (Ioo (h - b₁) h ∪ Ioo h (h + b₂) : Set ℝ) :=
    (measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite {h - b₁, h, h + b₂}).measure_zero _)).mono
      fun t ht ⟨h₁, h₂⟩ ↦ by
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
        rcases lt_or_gt_of_ne ht.2.1 with h₃ | h₃
        exacts [Or.inl ⟨h₁.lt_of_ne' ht.1, h₃⟩, Or.inr ⟨h₃, h₂.lt_of_ne ht.2.2⟩]
  have hleft : ∫⁻ t in Ioo (h - b₁) h, F (|h - t| / d) =
      ENNReal.ofReal d * ∫⁻ σ in Ioo 0 (b₁ / d), F σ := by
    have e₁ : (fun t ↦ (t - h) / (-d)) = fun t ↦ (h - t) / d :=
      funext fun t ↦ by rw [div_neg, ← neg_div, neg_sub]
    have hpre : (fun t ↦ (h - t) / d) ⁻¹' Ioo 0 (b₁ / d) = Ioo (h - b₁) h := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      rw [div_pos_iff_of_pos_right hd, div_lt_div_iff_of_pos_right hd]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hs := setLIntegral_comp_div_sub (neg_ne_zero.2 hd.ne') h F (Ioo 0 (b₁ / d))
    simp only [e₁] at hs
    rw [hpre, abs_neg, abs_of_pos hd] at hs
    rw [← hs]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [abs_of_pos (by linarith [ht.2] : 0 < h - t), div_neg, ← neg_div, neg_sub]
  have hright : ∫⁻ t in Ioo h (h + b₂), F (|h - t| / d) =
      ENNReal.ofReal d * ∫⁻ σ in Ioo 0 (b₂ / d), F σ := by
    have hpre : (fun t ↦ (t - h) / d) ⁻¹' Ioo 0 (b₂ / d) = Ioo h (h + b₂) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      rw [div_pos_iff_of_pos_right hd, div_lt_div_iff_of_pos_right hd]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hs := setLIntegral_comp_div_sub hd.ne' h F (Ioo 0 (b₂ / d))
    rw [hpre, abs_of_pos hd] at hs
    rw [← hs]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.1] : 0 < t - h)]
  calc ∫⁻ t in Icc (h - b₁) (h + b₂), F (|h - t| / d)
      ≤ ∫⁻ t in Ioo (h - b₁) h ∪ Ioo h (h + b₂), F (|h - t| / d) := lintegral_mono_set' hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [hleft, hright, mul_add]

/-! ### Boxes and the reflected integral -/

/-- The rectangle `Q_{a,b₁,b₂}(x) = [x₁ - a, x₁ + a] × [x₂ - b₁, x₂ + b₂]` of Chen and Hou,
Part I, (3.4). -/
def box (a b₁ b₂ : ℝ) (x : ℝ^2) : Set (ℝ^2) :=
  {y | x 0 - a ≤ y 0 ∧ y 0 ≤ x 0 + a ∧ x 1 - b₁ ≤ y 1 ∧ y 1 ≤ x 1 + b₂}

/-- The absolutely convergent form `∫_{y ∈ S, y₁ < x₁} K(x - y) (W(y) - W(R y)) dy` of the
principal value `P.V. ∫_S K(x - y) W(y) dy` (`tendsto_setIntegral_diff_ball`). -/
def reflectedIntegral (K W : ℝ^2 → ℝ) (S : Set (ℝ^2)) (x : ℝ^2) : ℝ :=
  ∫ y in S ∩ {y | y 0 < x 0}, K (x - y) * (W y - W (verticalReflection (x 0) y))

variable {a b₁ b₂ : ℝ}

/-- Membership in a box in coordinates. -/
theorem mk_mem_box {x : ℝ^2} {s t : ℝ} :
    !₂[s, t] ∈ box a b₁ b₂ x ↔ s ∈ Icc (x 0 - a) (x 0 + a) ∧ t ∈ Icc (x 1 - b₁) (x 1 + b₂) := by
  simp only [box, mem_ofPred_eq, mem_Icc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  tauto

/-- Boxes are measurable. -/
theorem measurableSet_box (x : ℝ^2) : MeasurableSet (box a b₁ b₂ x) := by
  have h₀ : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h₁ : Measurable fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  have e : box a b₁ b₂ x = ({y : ℝ^2 | x 0 - a ≤ y 0} ∩ {y | y 0 ≤ x 0 + a}) ∩
      ({y : ℝ^2 | x 1 - b₁ ≤ y 1} ∩ {y | y 1 ≤ x 1 + b₂}) := by
    ext y
    simp only [box, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [e]
  exact ((measurableSet_le measurable_const h₀).inter (measurableSet_le h₀ measurable_const)).inter
    ((measurableSet_le measurable_const h₁).inter (measurableSet_le h₁ measurable_const))

/-- Boxes are bounded. -/
theorem isBounded_box (x : ℝ^2) : Bornology.IsBounded (box a b₁ b₂ x) := by
  refine (Metric.isBounded_closedBall (x := x) (r := |a| + |b₁| + |b₂|)).subset fun y hy ↦ ?_
  rw [mem_closedBall, dist_eq_norm]
  refine (EuclideanSpace.norm_le_abs_add_abs_fin_two _).trans ?_
  have h₀ : |(y - x) 0| ≤ |a| := by
    rw [PiLp.sub_apply, abs_le]
    constructor <;> linarith [hy.1, hy.2.1, le_abs_self a, neg_abs_le a]
  have h₁ : |(y - x) 1| ≤ |b₁| + |b₂| := by
    rw [PiLp.sub_apply, abs_le]
    constructor <;> linarith [hy.2.2.1, hy.2.2.2, le_abs_self b₁, le_abs_self b₂,
      abs_nonneg b₁, abs_nonneg b₂, neg_abs_le b₁]
  linarith

/-- A box is symmetric in the vertical line through its center. -/
theorem verticalReflection_mem_box {x y : ℝ^2} (hy : y ∈ box a b₁ b₂ x) :
    verticalReflection (x 0) y ∈ box a b₁ b₂ x := by
  simp only [box, mem_ofPred_eq, verticalReflection_zero, verticalReflection_one] at hy ⊢
  refine ⟨by linarith [hy.2.1], by linarith [hy.1], hy.2.2.1, hy.2.2.2⟩

/-- The left half of a box in the coordinates `(height, abscissa)`. -/
theorem planeEquivSwap_preimage_box_inter (x : ℝ^2) :
    planeEquivSwap ⁻¹' (box a b₁ b₂ x ∩ {y | y 0 < x 0}) =
      Icc (x 1 - b₁) (x 1 + b₂) ×ˢ (Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0)) := by
  ext p
  simp only [mem_preimage, planeEquivSwap_apply, mem_inter_iff, mk_mem_box, mem_ofPred_eq,
    mem_prod, mem_Iio, Matrix.cons_val_zero]
  tauto

/-- A horizontal slice with a finite horizontal Hölder seminorm is continuous. -/
theorem continuousOn_slice {W : ℝ^2 → ℝ} {C : ℝ≥0} {D : Set (ℝ^2)}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) D W ≤ C) {t : ℝ} {I : Set ℝ}
    (hI : ∀ s ∈ I, !₂[s, t] ∈ D) : ContinuousOn (fun s ↦ W !₂[s, t]) I :=
  ((HolderSpace.holderOnWith_slice_zero hC t).continuousOn (by norm_num)).mono hI

/-- **Fubini for the reflected integral over a box**: off the common height the reflection is
undone on each horizontal line, so
`∫_{y ∈ Q(x), y₁ < x₁} K(x - y)(W(y) - W(R y)) dy = ∫_{x₂ - b₁}^{x₂ + b₂} F(t) dt` with
`F(t) = ∫_{x₁ - a}^{x₁ + a} K(x - (s, t)) W(s, t) ds`, and `F` is integrable. -/
theorem reflectedIntegral_box_eq (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x : ℝ^2}
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ x) W ≤ C) :
    reflectedIntegral K W (box a b₁ b₂ x) x =
        ∫ t in Icc (x 1 - b₁) (x 1 + b₂),
          ∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t] ∧
      IntegrableOn (fun t ↦ ∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t])
        (Icc (x 1 - b₁) (x 1 + b₂)) := by
  set G : ℝ^2 → ℝ := fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y))
  have hGi : IntegrableOn G (box a b₁ b₂ x ∩ {y | y 0 < x 0}) :=
    integrableOn_kernel_mul_sub hK (measurableSet_box x) (fun _ hy ↦ verticalReflection_mem_box hy)
      (isBounded_box x) hWm hC
  have hGi' : IntegrableOn (fun p : ℝ × ℝ ↦ G !₂[p.2, p.1])
      (Icc (x 1 - b₁) (x 1 + b₂) ×ˢ (Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0))) := by
    have h := (measurePreserving_planeEquivSwap.integrableOn_comp_preimage
      planeEquivSwap.measurableEmbedding (f := G) (s := box a b₁ b₂ x ∩ {y | y 0 < x 0})).2 hGi
    rw [planeEquivSwap_preimage_box_inter] at h
    simpa only [Function.comp_def, planeEquivSwap_apply] using h
  have hrepr : reflectedIntegral K W (box a b₁ b₂ x) x = ∫ t in Icc (x 1 - b₁) (x 1 + b₂),
      ∫ s in Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0), G !₂[s, t] := by
    rw [reflectedIntegral, ← measurePreserving_planeEquivSwap.setIntegral_preimage_emb
      planeEquivSwap.measurableEmbedding, planeEquivSwap_preimage_box_inter, Measure.volume_eq_prod,
      setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
    simp only [planeEquivSwap_apply, G]
  have hslice : ∀ᵐ t ∂volume.restrict (Icc (x 1 - b₁) (x 1 + b₂)),
      ∫ s in Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0), G !₂[s, t] =
        ∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t] := by
    have hne : ∀ᵐ t ∂volume.restrict (Icc (x 1 - b₁) (x 1 + b₂)), t ≠ x 1 :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (x 1)))
    filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t ht htI
    exact setIntegral_inter_Iio_eq hK ht
      (continuousOn_slice hC fun s hs ↦ mk_mem_box.2 ⟨hs, htI⟩)
  refine ⟨hrepr.trans (integral_congr_ae hslice), ?_⟩
  have hint : Integrable (fun t ↦ ∫ s in Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0), G !₂[s, t])
      (volume.restrict (Icc (x 1 - b₁) (x 1 + b₂))) := by
    have h : Integrable (fun p : ℝ × ℝ ↦ G !₂[p.2, p.1])
        ((volume.restrict (Icc (x 1 - b₁) (x 1 + b₂))).prod
          (volume.restrict (Icc (x 0 - a) (x 0 + a) ∩ Iio (x 0)))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hGi'
    exact h.integral_prod_left
  exact hint.congr hslice

/-! ### Lemma 3.1 -/

/-- The slices of `W` through the union of the two boxes, rescaled to the unit distance, are
`1/2`-Hölder with constant `C d^{1/2}`. -/
private theorem holderOnWith_rescaled_slice {x z : ℝ^2} (hxz : x 1 = z 1) (hd : z 0 < x 0)
    (ha : (x 0 - z 0) / 2 ≤ a) {W : ℝ^2 → ℝ} {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ x ∪ box a b₁ b₂ z) W ≤ C)
    {t : ℝ} (ht : t ∈ Icc (x 1 - b₁) (x 1 + b₂)) :
    HolderOnWith (C * ((x 0 - z 0) ^ (1 / 2 : ℝ)).toNNReal) (1 / 2)
      (fun u ↦ W !₂[(x 0 + z 0) / 2 + (x 0 - z 0) * u, t])
      (Icc (-(a / (x 0 - z 0) + 1 / 2)) (a / (x 0 - z 0) + 1 / 2)) := by
  set d := x 0 - z 0
  have hd0 : 0 < d := sub_pos.2 hd
  have hmem : ∀ u ∈ Icc (-(a / d + 1 / 2)) (a / d + 1 / 2),
      !₂[(x 0 + z 0) / 2 + d * u, t] ∈ box a b₁ b₂ x ∪ box a b₁ b₂ z := fun u hu ↦ by
    have hd : d * (a / d + 1 / 2) = a + d / 2 := by field_simp
    have h₁ : d * u ≤ a + d / 2 := by linarith [mul_le_mul_of_nonneg_left hu.2 hd0.le]
    have h₂ : -(a + d / 2) ≤ d * u := by linarith [mul_le_mul_of_nonneg_left hu.1 hd0.le]
    rcases le_or_gt (x 0 - a) ((x 0 + z 0) / 2 + d * u) with h | h
    · exact Or.inl (mk_mem_box.2 ⟨⟨h, by simp only [d] at h₁; linarith⟩, ht⟩)
    · refine Or.inr (mk_mem_box.2 ⟨⟨by simp only [d] at h₂; linarith, by linarith⟩, ?_⟩)
      rwa [← hxz]
  have hslice := HolderSpace.holderOnWith_slice_zero hC t
  intro u hu u' hu'
  have h := hslice _ (hmem u hu) _ (hmem u' hu')
  refine h.trans ?_
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    show (x 0 + z 0) / 2 + d * u - ((x 0 + z 0) / 2 + d * u') = d * (u - u') by ring, abs_mul,
    abs_of_pos hd0, ENNReal.coe_mul, mul_assoc]
  gcongr
  rw [ENNReal.ofReal_mul hd0.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hd0.le (by norm_num), ENNReal.ofReal]
  norm_num

/-- **Chen and Hou, Part I, Lemma 3.1**, for the reflected integrals. Let `x, z` be at the same
height with `x₁ ≠ z₁`, let `a ≥ |x₁ - z₁| / 2`, and let `W` be measurable with
horizontal `1/2`-Hölder seminorm at most `C` on `Q(x) ∪ Q(z)`. Then
`|P(x) - P(z)| / (π |x₁ - z₁|^{1/2}) ≤ C₁(max(b₁, b₂) / |x₁ - z₁|) C`, where `P(x)` is the
reflected integral `reflectedIntegral K W (Q(x)) x`. When `W` is also integrable on the boxes,
`P(x)` is the principal value of `∫_{Q(x)} K(x - y) W(y) dy`
(`abs_sub_div_le_strainConstant_of_tendsto`). -/
theorem abs_sub_div_le_strainConstant (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {W : ℝ^2 → ℝ}
    {x z : ℝ^2} (hxz : x 1 = z 1) (hne : x 0 ≠ z 0)
    (ha : |x 0 - z 0| / 2 ≤ a) (hWm : AEStronglyMeasurable W) {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ x ∪ box a b₁ b₂ z) W ≤ C) :
    ENNReal.ofReal (|reflectedIntegral K W (box a b₁ b₂ x) x -
        reflectedIntegral K W (box a b₁ b₂ z) z| / (Real.pi * |x 0 - z 0| ^ (1 / 2 : ℝ))) ≤
      strainConstant (max b₁ b₂ / |x 0 - z 0|) * C := by
  wlog hlt : z 0 < x 0 generalizing x z
  · have hlt' : x 0 < z 0 := lt_of_le_of_ne (not_lt.1 hlt) hne
    have := this hxz.symm hne.symm (by rwa [abs_sub_comm]) (by rwa [union_comm]) hlt'
    rwa [abs_sub_comm (reflectedIntegral K W (box a b₁ b₂ z) z), abs_sub_comm (z 0)] at this
  set d := x 0 - z 0 with hd_def
  have hd0 : 0 < d := sub_pos.2 hlt
  have habs : |x 0 - z 0| = d := abs_of_pos hd0
  rw [habs] at ha ⊢
  set h := x 1 with hh
  set A := a / d
  have hA : 1 / 2 ≤ A := by
    rw [le_div_iff₀ hd0]
    linarith
  have hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ x) W ≤ C :=
    (HolderSpace.directionalSeminorm_mono subset_union_left).trans hC
  have hCz : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ z) W ≤ C :=
    (HolderSpace.directionalSeminorm_mono subset_union_right).trans hC
  obtain ⟨hAx, hIx⟩ := reflectedIntegral_box_eq hK hWm hCx
  obtain ⟨hAz, hIz⟩ := reflectedIntegral_box_eq hK hWm hCz
  rw [← hxz] at hAz hIz
  set Fx : ℝ → ℝ := fun t ↦ ∫ s in Icc (x 0 - a) (x 0 + a), K (x - !₂[s, t]) * W !₂[s, t]
  set Fz : ℝ → ℝ := fun t ↦ ∫ s in Icc (z 0 - a) (z 0 + a), K (z - !₂[s, t]) * W !₂[s, t]
  set I := Icc (h - b₁) (h + b₂)
  have hdiff : reflectedIntegral K W (box a b₁ b₂ x) x - reflectedIntegral K W (box a b₁ b₂ z) z =
      ∫ t in I, (Fx t - Fz t) := by
    rw [hAx, hAz, integral_sub hIx hIz]
  -- the bound on each line
  have hpt : ∀ t ∈ I, t ≠ h → ‖Fx t - Fz t‖ₑ ≤
      2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * strainCost (|h - t| / d) := by
    intro t ht hth
    have hσ : (h - t) / d ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm hth)) hd0.ne'
    have hix : IntegrableOn (fun s ↦ K (x - !₂[s, t]) * W !₂[s, t]) (Icc (x 0 - a) (x 0 + a)) :=
      ((continuous_kernel_sub_mk hK x hth).continuousOn.mul (continuousOn_slice hCx
        fun s hs ↦ mk_mem_box.2 ⟨hs, ht⟩)).integrableOn_compact isCompact_Icc
    have hiz : IntegrableOn (fun s ↦ K (z - !₂[s, t]) * W !₂[s, t]) (Icc (z 0 - a) (z 0 + a)) :=
      ((continuous_kernel_sub_mk hK z (hxz ▸ hth)).continuousOn.mul (continuousOn_slice hCz
        fun s hs ↦ mk_mem_box.2 ⟨hs, by rwa [← hxz]⟩)).integrableOn_compact isCompact_Icc
    have heq := integral_sub_integral_eq hK hxz hlt hth hix hiz
    have hg := holderOnWith_rescaled_slice hxz hlt (by simpa [d] using ha) hC ht
    have hline := abs_integral_localStrainDifference_mul_le hA hσ hg
    change ‖Fx t - Fz t‖ₑ ≤ _
    rw [show Fx t - Fz t = _ from heq, Real.enorm_eq_ofReal_abs, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg _), abs_inv, abs_of_pos hd0]
    rw [abs_div, abs_of_pos hd0] at hline
    calc ENNReal.ofReal d⁻¹ * ENNReal.ofReal |∫ u, localStrainDifference A u ((h - t) / d) *
          W !₂[(x 0 + z 0) / 2 + d * u, t]|
        ≤ ENNReal.ofReal d⁻¹ * (2 * ↑(C * (d ^ (1 / 2 : ℝ)).toNNReal) *
            strainCost (|h - t| / d)) := by gcongr
      _ = 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * strainCost (|h - t| / d) := by
        rw [ENNReal.coe_mul, ENNReal.ofReal_mul (inv_nonneg.2 hd0.le)]
        rw [show ((d ^ (1 / 2 : ℝ)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (d ^ (1 / 2 : ℝ)) from rfl]
        ring
  -- integrate over the heights
  set S := ∫⁻ σ in Ioo 0 (max b₁ b₂ / d), strainCost σ
  have hS₁ : ∫⁻ σ in Ioo 0 (b₁ / d), strainCost σ ≤ S :=
    lintegral_mono_set (Ioo_subset_Ioo_right (div_le_div_of_nonneg_right (le_max_left _ _) hd0.le))
  have hS₂ : ∫⁻ σ in Ioo 0 (b₂ / d), strainCost σ ≤ S :=
    lintegral_mono_set (Ioo_subset_Ioo_right (div_le_div_of_nonneg_right (le_max_right _ _) hd0.le))
  have hint : ENNReal.ofReal |∫ t in I, (Fx t - Fz t)| ≤
      2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * (ENNReal.ofReal d * (S + S)) := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hne : ∀ᵐ t ∂volume.restrict I, t ≠ h :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton h))
    calc ∫⁻ t in I, ‖Fx t - Fz t‖ₑ
        ≤ ∫⁻ t in I, 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) *
            strainCost (|h - t| / d) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t ht htI
          exact hpt t htI ht
      _ = 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) *
            ∫⁻ t in I, strainCost (|h - t| / d) :=
          lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])
      _ ≤ 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * (ENNReal.ofReal d * (S + S)) := by
          gcongr
          exact (lintegral_Icc_abs_div_le hd0 _).trans (by gcongr)
  rw [hdiff, ENNReal.ofReal_div_of_pos (by positivity)]
  calc ENNReal.ofReal |∫ t in I, (Fx t - Fz t)| / ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ))
      ≤ 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * (ENNReal.ofReal d * (S + S)) /
          ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) := by gcongr
    _ = strainConstant (max b₁ b₂ / d) * C := by
        have hπ : 0 < Real.pi := Real.pi_pos
        have hdp : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd0 _
        have key : ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * ENNReal.ofReal d =
            ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) * ENNReal.ofReal (1 / Real.pi) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        have hfour : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / Real.pi) = ENNReal.ofReal (4 / Real.pi) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
        rw [strainConstant, ← hfour]
        rw [show 2 * C * ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * (ENNReal.ofReal d * (S + S)) =
            ENNReal.ofReal (d⁻¹ * d ^ (1 / 2 : ℝ)) * ENNReal.ofReal d * (4 * C * S) by ring, key]
        rw [mul_comm (ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ))) _, mul_assoc,
          mul_comm (ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ))) _, ← mul_assoc,
          ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
            ENNReal.ofReal_ne_top]
        ring

/-- **Chen and Hou, Part I, Lemma 3.1**, for the principal values. Under the hypotheses of
`abs_sub_div_le_strainConstant`, with `W` also integrable on the two boxes, the ball truncations
of `∫_{Q(x)} K(x - y) W(y) dy` and `∫_{Q(z)} K(z - y) W(y) dy` converge, and their limits
`P(x)`, `P(z)` satisfy `|P(x) - P(z)| / (π |x₁ - z₁|^{1/2}) ≤ C₁(max(b₁, b₂)/|x₁ - z₁|) C`. -/
theorem abs_sub_div_le_strainConstant_of_tendsto (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4)
    {W : ℝ^2 → ℝ} {x z : ℝ^2} (hxz : x 1 = z 1) (hne : x 0 ≠ z 0) (ha : |x 0 - z 0| / 2 ≤ a)
    (hWm : AEStronglyMeasurable W) (hWi : IntegrableOn W (box a b₁ b₂ x ∪ box a b₁ b₂ z))
    {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b₁ b₂ x ∪ box a b₁ b₂ z) W ≤ C)
    {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in box a b₁ b₂ x \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in box a b₁ b₂ z \ ball z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz)) :
    ENNReal.ofReal (|vx - vz| / (Real.pi * |x 0 - z 0| ^ (1 / 2 : ℝ))) ≤
      strainConstant (max b₁ b₂ / |x 0 - z 0|) * C := by
  have hx := tendsto_setIntegral_diff_ball hK (measurableSet_box x)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box x) hWm
    (hWi.mono_set subset_union_left)
    ((HolderSpace.directionalSeminorm_mono subset_union_left).trans hC)
  have hz := tendsto_setIntegral_diff_ball hK (measurableSet_box z)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box z) hWm
    (hWi.mono_set subset_union_right)
    ((HolderSpace.directionalSeminorm_mono subset_union_right).trans hC)
  rw [tendsto_nhds_unique hvx hx, tendsto_nhds_unique hvz hz]
  exact abs_sub_div_le_strainConstant hK hxz hne ha hWm hC

end IncompressibleFlow.SharpHolder
