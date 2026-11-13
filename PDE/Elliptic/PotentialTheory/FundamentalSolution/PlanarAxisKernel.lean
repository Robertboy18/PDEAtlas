/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarRectangleIntegrals
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import CAS.ExactTactic

/-!
# The kernel of `u / x₁` near the axis

For the horizontal velocity `u = (1/π) ∫_{y₁ ≥ 0} K(x, y) W(y) dy` of a vorticity odd in `x₁`,
symmetrized in `y₁`, Chen and Hou II, Appendix B.4, change variables `y = x + x₁ s` near the
singularity; the kernel becomes `-x₁⁻¹ K_s(s)` with

`K_s(s) = (s₂/|s|² - s₂/((s₁ + 2)² + s₂²)) / 2 = 2 (s₁ + 1) s₂ / (|s|² ((s₁ + 2)² + s₂²))`

(`axisKernel`; coordinates `s = (s 0, s 1)`). It is `π (∂₂Φ(s + 2e₁) - ∂₂Φ(s))` for the gradient
kernels of the fundamental solution, hence locally integrable, and it is nonnegative on
`{s₁ ≥ -1, s₂ ≥ 0}`. The two integrals of Supplementary material II, Section 6.2,

`J₁(B) = ∫_{[-1,0] × [0, 1/B]} K_s` and `J₂(B) = ∫_{[0, 1/B]²} K_s`,

are `axisStripIntegral (1/B)` and `axisSquareIntegral (1/B)` here, functions of the side `L = 1/B`.

## Main results

* `integral_rectangle_axisKernel`: `∫_Q K_s` on every closed rectangle through the corner sums of
  the gradient kernels (`integral_rectangle_gradientKernel_one_eq_cornerSum`), also around the
  pole.
* `axisStripIntegral_eq`: `J₁ = L (2 arctan(1/L) - arctan(2/L)) / 2 + log(4 (1 + L²)/(4 + L²)) / 2`,
  the formula of Supp. 6.2 in the variable `L = 1/B`; `monotone_axisStripIntegral` and
  `axisStripIntegral_le_log_two`: `J₁(B) ≤ log 2 = lim_{B → 0} J₁(B)` for every `B > 0`.
* `axisSquareIntegral_eq`: `J₂ = (L log 2)/4 + (L/2)(arctan(2/L) - arctan(1/(L+1)))
  - ((L+2)/4) log(1 + L²/(L+2)²) + log(4 + L²)/2 - log 2`.
* `hasDerivAt_axisSquareIntegral`: `dJ₂/dL = E₁ + E₂` with
  `E₁ = log(2(L+2)²/((L+2)² + L²))/4` and `E₂ = (arctan(2/L) - arctan(1/(L+1)))/2`;
  `mul_axisSquareRate_lt_one`: `L (E₁ + E₂) < 1`.
* `antitoneOn_axisSquareIntegral_sub_log`: `J₂₁(B) = J₂(B) + log B` is increasing in `B`
  (Supp. 6.2).
* `antitoneOn_axisSquareIntegral_div_sqrt`: if `J₂(1/L₀) ≥ 2` then `L ↦ J₂(1/L)/√L` is
  antitone on `[L₀, ∞)`, so `B ↦ √B J₂(B)` is increasing on `(0, 1/L₀]`: the supremum of
  `x₁^{1/2} J₂(x₁/h)` over a cell `(0, z]` with `z ≤ h/L₀` is its value at `z`. This is the bound
  used in Supp. 6.2.
* `horizontalVelocityKernel`, `horizontalVelocityKernel_add_smul`,
  `setIntegral_horizontalVelocityKernel`: the kernel `K(x, y)` of `u` symmetrized in `y₁`, with
  `K(x, x + x₁ s) = -K_s(s)/x₁`, and the change of variables `y = x + x₁ s` on rectangles.
* `abs_setIntegral_horizontalVelocityKernel_le`: the bounds of `II_{in,1}` and `II_{in,2}` of
  App. B.4, `|∫_{x + x₁ ([a,b] × [-L,L])} K ω| ≤ x₁ (M₊ + M₋) ∫_{[a,b] × [0,L]} K_s` with the
  bounds `M_±` of `|ω|` on the two halves (`K_s` is odd in `s₂`, `|K_s|` even).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix B.4, and
  Supplementary material II, Section 6.2.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PDE.Analysis
open scoped Interval Pointwise

namespace PotentialTheory.Planar

/-- The kernel `K_s(s) = (s₂/|s|² - s₂/((s₁ + 2)² + s₂²)) / 2` of Chen and Hou II, App. B.4. -/
def axisKernel (s : ℝ^2) : ℝ :=
  (s 1 / ‖s‖ ^ 2 - s 1 / ((s 0 + 2) ^ 2 + s 1 ^ 2)) / 2

/-- The corner function `-(2 v arctan(u/v) + u log(u² + v²))/4` of `π ∂₂Φ`. -/
def gradientOneCorner (u v : ℝ) : ℝ :=
  -(2 * (v * Real.arctan (u / v)) + u * Real.log (u ^ 2 + v ^ 2)) / 4

/-- `K_s(p, q) = (q / (p² + q²) - q / ((p + 2)² + q²)) / 2` at the point `(p, q)`. -/
theorem axisKernel_toLp (p q : ℝ) :
    axisKernel !₂[p, q] = (q / (p ^ 2 + q ^ 2) - q / ((p + 2) ^ 2 + q ^ 2)) / 2 := by
  simp [axisKernel, norm_sq_vec]

/-- `K_s = 2 (s₁ + 1) s₂ / (|s|² ((s₁ + 2)² + s₂²))` off the pole. -/
theorem axisKernel_toLp_eq {p q : ℝ} (h : p ^ 2 + q ^ 2 ≠ 0) :
    axisKernel !₂[p, q] = 2 * (p + 1) * q / ((p ^ 2 + q ^ 2) * ((p + 2) ^ 2 + q ^ 2)) := by
  rw [axisKernel_toLp]
  rcases eq_or_ne ((p + 2) ^ 2 + q ^ 2) 0 with h2 | h2
  · have hq : q = 0 := by nlinarith [sq_nonneg (p + 2), sq_nonneg q]
    simp [hq]
  field_simp
  ring

/-- `K_s ≥ 0` on `{s₁ ≥ -1, s₂ ≥ 0}`. -/
theorem axisKernel_nonneg {s : ℝ^2} (h0 : -1 ≤ s 0) (h1 : 0 ≤ s 1) : 0 ≤ axisKernel s := by
  have hs : s = !₂[s 0, s 1] := by ext i; fin_cases i <;> rfl
  rw [hs]
  rcases eq_or_ne (s 0 ^ 2 + s 1 ^ 2) 0 with h | h
  · have h1' : s 1 = 0 := by nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
    simp [axisKernel_toLp, h1']
  rw [axisKernel_toLp_eq h]
  have : 0 ≤ s 0 + 1 := by linarith
  positivity

/-- The first coordinate of `2 e₁` is `2`. -/
private theorem single_zero_two_apply_zero : (EuclideanSpace.single 0 (2 : ℝ) : ℝ^2) 0 = 2 := by
  simp

/-- The second coordinate of `2 e₁` is `0`. -/
private theorem single_zero_two_apply_one : (EuclideanSpace.single 0 (2 : ℝ) : ℝ^2) 1 = 0 := by
  simp

/-- `K_s(s) = π ∂₂Φ(s + 2e₁) - π ∂₂Φ(s)`. -/
theorem axisKernel_eq_gradientKernel (s : ℝ^2) :
    axisKernel s = Real.pi * gradientKernel 1 (s + EuclideanSpace.single 0 2) -
      Real.pi * gradientKernel 1 s := by
  have hn : ‖s + EuclideanSpace.single 0 (2 : ℝ)‖ ^ 2 = (s 0 + 2) ^ 2 + s 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_fin_two]; simp
  rw [gradientKernel_eq_div, gradientKernel_eq_div, hn, axisKernel]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [PiLp.add_apply, single_zero_two_apply_one, add_zero]
  field_simp
  ring

/-- The preimage of a translated rectangle. -/
private theorem preimage_add_coordinateRectangle (a b c d : ℝ) (v : ℝ^2) :
    (fun y ↦ y + v) ⁻¹' coordinateRectangle (a + v 0) (b + v 0) (c + v 1) (d + v 1) =
      coordinateRectangle a b c d := by
  ext y
  simp only [mem_preimage, mem_coordinateRectangle, PiLp.add_apply, mem_Icc]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- Translation of a rectangle integral. -/
private theorem setIntegral_coordinateRectangle_add (f : ℝ^2 → ℝ) (a b c d : ℝ) (v : ℝ^2) :
    ∫ y in coordinateRectangle a b c d, f (y + v) =
      ∫ y in coordinateRectangle (a + v 0) (b + v 0) (c + v 1) (d + v 1), f y := by
  rw [← preimage_add_coordinateRectangle a b c d v]
  exact (measurePreserving_add_right volume v).setIntegral_preimage_emb
    (measurableEmbedding_addRight v) f _

/-- The translate `y ↦ ∂₂Φ(y + v)` of the gradient kernel is integrable on every closed rectangle.
-/
private theorem integrableOn_gradientKernel_add (a b c d : ℝ) (v : ℝ^2) :
    IntegrableOn (fun y ↦ gradientKernel 1 (y + v)) (coordinateRectangle a b c d) := by
  rw [← preimage_add_coordinateRectangle a b c d v]
  exact ((measurePreserving_add_right volume v).integrableOn_comp_preimage
    (measurableEmbedding_addRight v)).2
    ((locallyIntegrable_gradientKernel 1).integrableOn_isCompact
      (isCompact_coordinateRectangle _ _ _ _))

/-- `K_s` is integrable on every closed rectangle. -/
theorem integrableOn_axisKernel (a b c d : ℝ) :
    IntegrableOn axisKernel (coordinateRectangle a b c d) := by
  have i1 : IntegrableOn (gradientKernel 1) (coordinateRectangle a b c d) :=
    (locallyIntegrable_gradientKernel 1).integrableOn_isCompact
      (isCompact_coordinateRectangle a b c d)
  have i2 := integrableOn_gradientKernel_add a b c d (EuclideanSpace.single 0 2)
  have h := (i2.const_mul Real.pi).sub (i1.const_mul Real.pi)
  refine IntegrableOn.congr_fun h (fun y _ ↦ ?_) (measurableSet_coordinateRectangle a b c d)
  simp [axisKernel_eq_gradientKernel]

/-- **`∫_Q K_s` on a closed rectangle**, also around the pole:
`∫_{[a,b] × [c,d]} K_s = Σ_corners G(· + 2, ·) - Σ_corners G` with
`G(u, v) = -(2 v arctan(u/v) + u log(u² + v²))/4`. -/
theorem integral_rectangle_axisKernel {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ y in coordinateRectangle a b c d, axisKernel y =
      cornerSum gradientOneCorner (a + 2) (b + 2) c d - cornerSum gradientOneCorner a b c d := by
  have i1 : IntegrableOn (gradientKernel 1) (coordinateRectangle a b c d) :=
    (locallyIntegrable_gradientKernel 1).integrableOn_isCompact
      (isCompact_coordinateRectangle a b c d)
  have i2 := integrableOn_gradientKernel_add a b c d (EuclideanSpace.single 0 2)
  simp_rw [axisKernel_eq_gradientKernel]
  rw [integral_sub (i2.const_mul Real.pi) (i1.const_mul Real.pi), integral_const_mul,
    integral_const_mul, setIntegral_coordinateRectangle_add]
  simp only [single_zero_two_apply_zero, single_zero_two_apply_one, add_zero]
  rw [integral_rectangle_gradientKernel_one_eq_cornerSum hab hcd,
    integral_rectangle_gradientKernel_one_eq_cornerSum (by linarith) hcd]
  rfl

/-! ### The integrals `J₁` and `J₂` -/

/-- `J₁(B) = ∫_{[-1,0] × [0, L]} K_s` with `L = 1/B`, Chen and Hou II, App. B.4 and Supp. 6.2. -/
def axisStripIntegral (L : ℝ) : ℝ := ∫ y in coordinateRectangle (-1) 0 0 L, axisKernel y

/-- `J₂(B) = ∫_{[0, L]²} K_s` with `L = 1/B`, Chen and Hou II, App. B.4 and Supp. 6.2. -/
def axisSquareIntegral (L : ℝ) : ℝ := ∫ y in coordinateRectangle 0 L 0 L, axisKernel y

/-- **The closed form of `J₁`**, Supp. 6.2: for `L ≥ 0`,
`J₁ = L (2 arctan(1/L) - arctan(2/L)) / 2 + (log(1 + L²) - log(4 + L²) + log 4) / 2`. -/
theorem axisStripIntegral_eq {L : ℝ} (hL : 0 ≤ L) :
    axisStripIntegral L = L * (2 * Real.arctan (1 / L) - Real.arctan (2 / L)) / 2 +
      (Real.log (1 + L ^ 2) - Real.log (4 + L ^ 2) + Real.log 4) / 2 := by
  rw [axisStripIntegral, integral_rectangle_axisKernel (by norm_num) hL]
  simp only [cornerSum, gradientOneCorner]
  norm_num
  rw [show (-1 / L) = -(1 / L) by ring, Real.arctan_neg]
  ring_nf

/-- **The closed form of `J₂`**, Supp. 6.2: for `L > 0`,
`J₂ = (L/4) log 2 + (L/2)(arctan(2/L) - arctan(1/(L+1)))
- ((L+2)/4)(log((L+2)² + L²) - 2 log(L+2)) + (log(4 + L²) - log 4)/2`. -/
theorem axisSquareIntegral_eq {L : ℝ} (hL : 0 < L) :
    axisSquareIntegral L = L / 4 * Real.log 2 +
      L / 2 * (Real.arctan (2 / L) - Real.arctan (1 / (L + 1))) -
      (L + 2) / 4 * (Real.log ((L + 2) ^ 2 + L ^ 2) - 2 * Real.log (L + 2)) +
      (Real.log (4 + L ^ 2) - Real.log 4) / 2 := by
  rw [axisSquareIntegral, integral_rectangle_axisKernel hL.le hL.le]
  simp only [cornerSum, gradientOneCorner]
  have hL0 : L ≠ 0 := hL.ne'
  have h1 : Real.arctan ((L + 2) / L) = Real.pi / 4 + Real.arctan (1 / (L + 1)) := by
    have hq : (1 + 1 / (L + 1)) / (1 - 1 * (1 / (L + 1))) = (L + 2) / L := by
      have h0 : L + 1 ≠ 0 := by linarith
      have e1 : 1 + 1 / (L + 1) = (L + 2) / (L + 1) := by field_simp; ring
      have e2 : 1 - 1 * (1 / (L + 1)) = L / (L + 1) := by field_simp; ring
      rw [e1, e2, div_div_div_cancel_right₀ h0]
    rw [← Real.arctan_one, Real.arctan_add (by
      rw [one_mul]; exact (div_lt_one (by linarith)).2 (by linarith)), hq]
  have h2 : Real.log (L ^ 2 + L ^ 2) = Real.log 2 + 2 * Real.log L := by
    rw [show L ^ 2 + L ^ 2 = 2 * L ^ 2 by ring, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  have h3 : Real.log ((L + 2) ^ 2 + 0 ^ 2) = 2 * Real.log (L + 2) := by
    rw [zero_pow two_ne_zero, add_zero, Real.log_pow]; push_cast; ring
  have h4 : Real.log (L ^ 2 + 0 ^ 2) = 2 * Real.log L := by
    rw [zero_pow two_ne_zero, add_zero, Real.log_pow]; push_cast; ring
  rw [div_self hL0, Real.arctan_one, h1, h2, h3, h4]
  norm_num
  ring_nf

/-! ### Monotonicity -/

/-- `K_s ≥ 0` on a rectangle `[a, b] × [c, d]` with `a ≥ -1` and `c ≥ 0`. -/
private theorem axisKernel_nonneg_of_mem {a b c d : ℝ} (ha : -1 ≤ a) (hc : 0 ≤ c) {y : ℝ^2}
    (hy : y ∈ coordinateRectangle a b c d) : 0 ≤ axisKernel y :=
  axisKernel_nonneg (ha.trans hy.1.1) (hc.trans hy.2.1)

/-- For `a ≥ -1` and `c ≥ 0`, the integral of `K_s` over `[a, b] × [c, d]` increases with the upper
sides `b` and `d`. -/
private theorem setIntegral_axisKernel_mono {a b c d b' d' : ℝ} (ha : -1 ≤ a) (hc : 0 ≤ c)
    (hb : b ≤ b') (hd : d ≤ d') :
    ∫ y in coordinateRectangle a b c d, axisKernel y ≤
      ∫ y in coordinateRectangle a b' c d', axisKernel y := by
  refine setIntegral_mono_set (integrableOn_axisKernel a b' c d') ?_ ?_
  · exact (ae_restrict_iff' (measurableSet_coordinateRectangle a b' c d')).2
      (Eventually.of_forall fun y hy ↦ axisKernel_nonneg_of_mem ha hc hy)
  · refine Eventually.of_forall fun y hy ↦ ?_
    exact ⟨⟨hy.1.1, hy.1.2.trans hb⟩, hy.2.1, hy.2.2.trans hd⟩

/-- `J₁` increases with the side `L`, that is, decreases in `B = 1/L`. -/
theorem monotone_axisStripIntegral : Monotone axisStripIntegral := fun _ _ h ↦
  setIntegral_axisKernel_mono (by norm_num) le_rfl le_rfl h

/-- `J₂` increases with the side `L`, that is, decreases in `B = 1/L`. -/
theorem monotone_axisSquareIntegral : Monotone axisSquareIntegral := fun _ _ h ↦
  setIntegral_axisKernel_mono (by norm_num) le_rfl h h

/-- `J₁ ≥ 0` for every side `L`. -/
theorem axisStripIntegral_nonneg (L : ℝ) : 0 ≤ axisStripIntegral L :=
  setIntegral_nonneg (measurableSet_coordinateRectangle _ _ _ _) fun _ hy ↦
    axisKernel_nonneg_of_mem (by norm_num) le_rfl hy

/-- `J₂ ≥ 0` for every side `L`. -/
theorem axisSquareIntegral_nonneg (L : ℝ) : 0 ≤ axisSquareIntegral L :=
  setIntegral_nonneg (measurableSet_coordinateRectangle _ _ _ _) fun _ hy ↦
    axisKernel_nonneg_of_mem (by norm_num) le_rfl hy

/-! ### The limit of `J₁` -/

/-- The derivative of `2 arctan x - arctan (2x)` is `6x² / ((1 + x²)(1 + 4x²))`. -/
private theorem hasDerivAt_two_arctan_sub (x : ℝ) :
    HasDerivAt (fun x ↦ 2 * Real.arctan x - Real.arctan (2 * x))
      (6 * x ^ 2 / ((1 + x ^ 2) * (1 + 4 * x ^ 2))) x := by
  have h := ((Real.hasDerivAt_arctan x).const_mul 2).sub
    ((Real.hasDerivAt_arctan (2 * x)).comp x ((hasDerivAt_id' x).const_mul 2))
  refine h.congr_deriv ?_
  have h1 : (1 + x ^ 2) ≠ 0 := by positivity
  have h2 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  have h3 : (1 + (2 * x) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `0 ≤ 2 arctan x - arctan (2x) ≤ 2x³` for `x ≥ 0`. -/
private theorem two_arctan_sub_mem {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 2 * Real.arctan x - Real.arctan (2 * x) ∧
      2 * Real.arctan x - Real.arctan (2 * x) ≤ 2 * x ^ 3 := by
  have hpos : ∀ t : ℝ, 0 ≤ 6 * t ^ 2 / ((1 + t ^ 2) * (1 + 4 * t ^ 2)) := fun t ↦ by positivity
  constructor
  · have hm : MonotoneOn (fun x ↦ 2 * Real.arctan x - Real.arctan (2 * x)) (Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun x _ ↦ (hasDerivAt_two_arctan_sub x).continuousAt.continuousWithinAt)
        (fun x _ ↦ (hasDerivAt_two_arctan_sub x).differentiableAt.differentiableWithinAt)
        fun x _ ↦ by rw [(hasDerivAt_two_arctan_sub x).deriv]; exact hpos x
    simpa using hm (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  · have hd : ∀ x, HasDerivAt (fun x ↦ 2 * x ^ 3 - (2 * Real.arctan x - Real.arctan (2 * x)))
        (6 * x ^ 2 - 6 * x ^ 2 / ((1 + x ^ 2) * (1 + 4 * x ^ 2))) x := fun x ↦
      (((hasDerivAt_pow 3 x).const_mul 2).sub (hasDerivAt_two_arctan_sub x)).congr_deriv
        (by ring)
    have hm : MonotoneOn (fun x ↦ 2 * x ^ 3 - (2 * Real.arctan x - Real.arctan (2 * x)))
        (Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
        (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt) fun x _ ↦ by
          rw [(hd x).deriv, sub_nonneg, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.arctan_zero, sub_self] at this
    linarith

/-- `J₁(B) → log 2` as `B → 0`, that is, as the side `L = 1/B → ∞`. -/
theorem tendsto_axisStripIntegral_atTop :
    Tendsto axisStripIntegral atTop (𝓝 (Real.log 2)) := by
  have hA : Tendsto (fun L : ℝ ↦ L * (2 * Real.arctan (1 / L) - Real.arctan (2 / L)) / 2)
      atTop (𝓝 0) := by
    have hup : Tendsto (fun L : ℝ ↦ 1 / L ^ 2) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) two_ne_zero)).congr fun L ↦ by
        simp [one_div]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with L hL
      have := (two_arctan_sub_mem (x := 1 / L) (by positivity)).1
      rw [show 2 / L = 2 * (1 / L) by ring]
      positivity
    · filter_upwards [eventually_gt_atTop 0] with L hL
      have := (two_arctan_sub_mem (x := 1 / L) (by positivity)).2
      rw [show 2 / L = 2 * (1 / L) by ring]
      calc L * (2 * Real.arctan (1 / L) - Real.arctan (2 * (1 / L))) / 2
          ≤ L * (2 * (1 / L) ^ 3) / 2 := by gcongr
        _ = 1 / L ^ 2 := by field_simp
  have hB : Tendsto (fun L : ℝ ↦ (Real.log (1 + L ^ 2) - Real.log (4 + L ^ 2) + Real.log 4) / 2)
      atTop (𝓝 (Real.log 2)) := by
    have hq : Tendsto (fun L : ℝ ↦ (1 + L ^ 2) / (4 + L ^ 2)) atTop (𝓝 1) := by
      have h3 : Tendsto (fun L : ℝ ↦ 3 / (4 + L ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 4
          (tendsto_pow_atTop two_ne_zero))
      have := tendsto_const_nhds (x := (1 : ℝ)) |>.sub h3
      rw [sub_zero] at this
      refine this.congr fun L ↦ ?_
      have : 4 + L ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hl := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq)
    rw [Real.log_one] at hl
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := (hl.add_const (Real.log 4)).div_const 2
    rw [zero_add, h4, mul_div_cancel_left₀ _ two_ne_zero] at this
    refine this.congr fun L ↦ ?_
    simp only [Function.comp_apply]
    rw [Real.log_div (by positivity) (by positivity), h4]
  refine (hA.add hB).congr' ?_ |>.trans (by rw [zero_add])
  filter_upwards [eventually_ge_atTop 0] with L hL
  rw [axisStripIntegral_eq hL]

/-- **`J₁(B) ≤ log 2` for every `B > 0`**: `J₁` decreases in `B` to its limit `log 2` at `0`. -/
theorem axisStripIntegral_le_log_two (L : ℝ) : axisStripIntegral L ≤ Real.log 2 :=
  monotone_axisStripIntegral.ge_of_tendsto tendsto_axisStripIntegral_atTop L

/-! ### The derivative of `J₂` in the side `L` -/

/-- The logarithmic part `E₁(L) = (log 2 + 2 log(L + 2) - log((L + 2)² + L²)) / 4` of
`dJ₂/dL`, the integral of `K_s` along the right edge of `[0, L]²`. -/
def axisSquareRateLog (L : ℝ) : ℝ :=
  (Real.log 2 + 2 * Real.log (L + 2) - Real.log ((L + 2) ^ 2 + L ^ 2)) / 4

/-- The arctangent part `E₂(L) = (arctan(2/L) - arctan(1/(L + 1))) / 2` of `dJ₂/dL`, the integral
of `K_s` along the top edge of `[0, L]²`. -/
def axisSquareRateArctan (L : ℝ) : ℝ :=
  (Real.arctan (2 / L) - Real.arctan (1 / (L + 1))) / 2

/-- The closed form of `J₂` (`axisSquareIntegral_eq`) as a function. -/
private def axisSquareClosed (L : ℝ) : ℝ :=
  L / 4 * Real.log 2 + L / 2 * (Real.arctan (2 / L) - Real.arctan (1 / (L + 1))) -
    (L + 2) / 4 * (Real.log ((L + 2) ^ 2 + L ^ 2) - 2 * Real.log (L + 2)) +
    (Real.log (4 + L ^ 2) - Real.log 4) / 2

/-- For `L > 0` the closed form of `J₂` has derivative `E₁(L) + E₂(L)`. -/
private theorem hasDerivAt_axisSquareClosed {L : ℝ} (hL : 0 < L) :
    HasDerivAt axisSquareClosed (axisSquareRateLog L + axisSquareRateArctan L) L := by
  have hL1 : L + 1 ≠ 0 := by linarith
  have hL2 : 0 < L + 2 := by linarith
  have hD : 0 < (L + 2) ^ 2 + L ^ 2 := by positivity
  have hF : 0 < 4 + L ^ 2 := by positivity
  unfold axisSquareClosed axisSquareRateLog axisSquareRateArctan
  cas using hL.ne'

/-- **`dJ₂/dL = E₁ + E₂`** for `L > 0`. -/
theorem hasDerivAt_axisSquareIntegral {L : ℝ} (hL : 0 < L) :
    HasDerivAt axisSquareIntegral (axisSquareRateLog L + axisSquareRateArctan L) L := by
  refine (hasDerivAt_axisSquareClosed hL).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hL] with M hM
  exact axisSquareIntegral_eq hM

/-- `arctan a - arctan b ≤ (a - b) / (1 + b²)` for `0 ≤ b ≤ a`: `arctan` is concave on `[0, ∞)`. -/
theorem arctan_sub_arctan_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    Real.arctan a - Real.arctan b ≤ (a - b) / (1 + b ^ 2) := by
  set φ : ℝ → ℝ := fun x ↦ (x - b) / (1 + b ^ 2) - (Real.arctan x - Real.arctan b) with hφ
  have hd : ∀ x, HasDerivAt φ (1 / (1 + b ^ 2) - 1 / (1 + x ^ 2)) x := fun x ↦ by
    exact ((((hasDerivAt_id' x).sub_const b).div_const (1 + b ^ 2)).sub
      ((Real.hasDerivAt_arctan x).sub_const (Real.arctan b))).congr_deriv (by ring)
  have hmono : MonotoneOn φ (Ici b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici b)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv, sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [mem_Ioi.1 hx])
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hab) hab
  simp only [hφ, sub_self, zero_div] at this
  linarith

/-- `E₁(L) ≥ 0` for `L ≥ 0`. -/
theorem axisSquareRateLog_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ axisSquareRateLog L := by
  unfold axisSquareRateLog
  have h2 : Real.log 2 + 2 * Real.log (L + 2) = Real.log (2 * (L + 2) ^ 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  rw [h2]
  have : Real.log ((L + 2) ^ 2 + L ^ 2) ≤ Real.log (2 * (L + 2) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  linarith

/-- `E₁(L) ≤ (L + 1) / ((L + 2)² + L²)` for `L ≥ 0`. -/
theorem axisSquareRateLog_le {L : ℝ} (hL : 0 ≤ L) :
    axisSquareRateLog L ≤ (L + 1) / ((L + 2) ^ 2 + L ^ 2) := by
  unfold axisSquareRateLog
  have hD : 0 < (L + 2) ^ 2 + L ^ 2 := by positivity
  have h2 : Real.log 2 + 2 * Real.log (L + 2) - Real.log ((L + 2) ^ 2 + L ^ 2) =
      Real.log (2 * (L + 2) ^ 2 / ((L + 2) ^ 2 + L ^ 2)) := by
    rw [Real.log_div (by positivity) hD.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  rw [h2]
  have := Real.log_le_sub_one_of_pos (x := 2 * (L + 2) ^ 2 / ((L + 2) ^ 2 + L ^ 2))
    (by positivity)
  have e : 2 * (L + 2) ^ 2 / ((L + 2) ^ 2 + L ^ 2) - 1 = 4 * (L + 1) / ((L + 2) ^ 2 + L ^ 2) := by
    field_simp; ring
  rw [e] at this
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  calc _ ≤ 4 * (L + 1) / ((L + 2) ^ 2 + L ^ 2) := this
    _ = (L + 1) / ((L + 2) ^ 2 + L ^ 2) * 4 := by ring

/-- `E₂(L) ≥ 0` for `L > 0`. -/
theorem axisSquareRateArctan_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ axisSquareRateArctan L := by
  unfold axisSquareRateArctan
  have : 1 / (L + 1) ≤ 2 / L := by
    rw [div_le_div_iff₀ (by linarith) hL]; linarith
  linarith [Real.arctan_strictMono.monotone this]

/-- `E₂(L) ≤ (L + 2)(L + 1) / (2L ((L + 1)² + 1))` for `L > 0`. -/
theorem axisSquareRateArctan_le {L : ℝ} (hL : 0 < L) :
    axisSquareRateArctan L ≤ (L + 2) * (L + 1) / (2 * L * ((L + 1) ^ 2 + 1)) := by
  unfold axisSquareRateArctan
  have hle : 1 / (L + 1) ≤ 2 / L := by
    rw [div_le_div_iff₀ (by linarith) hL]; linarith
  have h := arctan_sub_arctan_le (by positivity) hle
  have e : (2 / L - 1 / (L + 1)) / (1 + (1 / (L + 1)) ^ 2) =
      (L + 2) * (L + 1) / (L * ((L + 1) ^ 2 + 1)) := by
    have : L + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e] at h
  have e2 : (L + 2) * (L + 1) / (2 * L * ((L + 1) ^ 2 + 1)) =
      (L + 2) * (L + 1) / (L * ((L + 1) ^ 2 + 1)) / 2 := by
    field_simp
  rw [e2]
  linarith

/-- **`L dJ₂/dL < 1`**: with `log x ≤ x - 1` and the concavity of `arctan`,
`L (E₁ + E₂) ≤ 1 - 1/(L² + 2L + 2)`. -/
theorem mul_axisSquareRate_lt_one {L : ℝ} (hL : 0 < L) :
    L * (axisSquareRateLog L + axisSquareRateArctan L) < 1 := by
  have h1 := axisSquareRateLog_le hL.le
  have h2 := axisSquareRateArctan_le hL
  have hb : L * ((L + 1) / ((L + 2) ^ 2 + L ^ 2) +
      (L + 2) * (L + 1) / (2 * L * ((L + 1) ^ 2 + 1))) = 1 - 1 / (L ^ 2 + 2 * L + 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (L ^ 2 + 2 * L + 2) := by positivity
  calc L * (axisSquareRateLog L + axisSquareRateArctan L)
      ≤ L * ((L + 1) / ((L + 2) ^ 2 + L ^ 2) +
          (L + 2) * (L + 1) / (2 * L * ((L + 1) ^ 2 + 1))) := by gcongr
    _ < 1 := by rw [hb]; linarith

/-- **`J₂₁(B) = J₂(B) + log B` is increasing in `B`**, Chen and Hou II, Supp. 6.2: in the side
`L = 1/B`, `J₂ - log L` is antitone on `(0, ∞)`. -/
theorem antitoneOn_axisSquareIntegral_sub_log :
    AntitoneOn (fun L ↦ axisSquareIntegral L - Real.log L) (Ioi 0) := by
  have hd : ∀ L ∈ Ioi (0 : ℝ), HasDerivAt (fun L ↦ axisSquareIntegral L - Real.log L)
      (axisSquareRateLog L + axisSquareRateArctan L - 1 / L) L := fun L hL ↦
    ((hasDerivAt_axisSquareIntegral hL).sub (Real.hasDerivAt_log (ne_of_gt hL))).congr_deriv
      (by rw [one_div])
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun L hL ↦ (hd L hL).continuousAt.continuousWithinAt) (fun L hL ↦ ?_) fun L hL ↦ ?_
  · rw [interior_Ioi] at hL; exact (hd L hL).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hL
    rw [(hd L hL).deriv]
    have := mul_axisSquareRate_lt_one hL
    have hL' : (0 : ℝ) < L := hL
    rw [sub_nonpos, le_div_iff₀ hL', mul_comm]
    exact this.le

/-- **`√B J₂(B)` is increasing on `(0, 1/L₀]`** when `J₂(1/L₀) ≥ 2`: in the side `L = 1/B`,
`J₂(L)/√L` is antitone on `[L₀, ∞)`, because `2 L dJ₂/dL < 2 ≤ J₂`. -/
theorem antitoneOn_axisSquareIntegral_div_sqrt {L₀ : ℝ} (hL₀ : 0 < L₀)
    (h2 : 2 ≤ axisSquareIntegral L₀) :
    AntitoneOn (fun L ↦ axisSquareIntegral L / √L) (Ici L₀) := by
  have hd : ∀ L, 0 < L → HasDerivAt (fun L ↦ axisSquareIntegral L / √L)
      (((axisSquareRateLog L + axisSquareRateArctan L) * √L -
        axisSquareIntegral L * (1 / (2 * √L))) / √L ^ 2) L := fun L hL ↦ by
    have hs : HasDerivAt (fun L ↦ √L) (1 / (2 * √L)) L := by
      simpa using Real.hasDerivAt_sqrt hL.ne'
    exact (hasDerivAt_axisSquareIntegral hL).div hs (Real.sqrt_pos.2 hL).ne'
  refine antitoneOn_of_deriv_nonpos (convex_Ici L₀)
    (fun L hL ↦ (hd L (hL₀.trans_le hL)).continuousAt.continuousWithinAt) (fun L hL ↦ ?_)
    fun L hL ↦ ?_
  · rw [interior_Ici] at hL
    exact (hd L (hL₀.trans hL)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hL
    have hL' : 0 < L := hL₀.trans hL
    rw [(hd L hL').deriv]
    have hs : 0 < √L := Real.sqrt_pos.2 hL'
    have hJ : 2 ≤ axisSquareIntegral L := h2.trans (monotone_axisSquareIntegral hL.le)
    have hE := mul_axisSquareRate_lt_one hL'
    refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
    have hss : √L * √L = L := Real.mul_self_sqrt hL'.le
    rw [sub_nonpos, show axisSquareIntegral L * (1 / (2 * √L)) = axisSquareIntegral L / (2 * √L)
      by ring, le_div_iff₀ (by positivity)]
    nlinarith [hss]

/-- **The supremum of `x₁^{1/2} J₂(x₁/h)` over a cell `(0, z]`**, Supp. 6.2: if
`J₂(1/L₀) ≥ 2` and `0 < t ≤ z ≤ h/L₀`, then `√t J₂(t/h) ≤ √z J₂(z/h)`, that is,
`√t · axisSquareIntegral (h/t) ≤ √z · axisSquareIntegral (h/z)`. -/
theorem sqrt_mul_axisSquareIntegral_le {L₀ h t z : ℝ} (hL₀ : 0 < L₀)
    (h2 : 2 ≤ axisSquareIntegral L₀) (hh : 0 < h) (ht : 0 < t) (htz : t ≤ z)
    (hz : z * L₀ ≤ h) :
    √t * axisSquareIntegral (h / t) ≤ √z * axisSquareIntegral (h / z) := by
  have hz0 : 0 < z := ht.trans_le htz
  have hmem : ∀ w, 0 < w → w * L₀ ≤ h → h / w ∈ Ici L₀ := fun w hw hwL ↦
    mem_Ici.2 ((le_div_iff₀ hw).2 (by linarith))
  have hA := antitoneOn_axisSquareIntegral_div_sqrt hL₀ h2
    (hmem z hz0 hz) (hmem t ht ((mul_le_mul_of_nonneg_right htz hL₀.le).trans hz))
    (div_le_div_of_nonneg_left hh.le ht htz)
  simp only at hA
  have key : ∀ w, 0 < w → √w * axisSquareIntegral (h / w) =
      √h * (axisSquareIntegral (h / w) / √(h / w)) := fun w hw ↦ by
    rw [Real.sqrt_div hh.le, div_div_eq_mul_div]
    have : 0 < √h := Real.sqrt_pos.2 hh
    field_simp
  rw [key t ht, key z hz0]
  exact mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg h)

/-! ### The singular part of `u / x₁` near the axis -/

/-- The kernel `K(x, y) = ((x₂ - y₂)/|x - y|² - (x₂ - y₂)/((x₁ + y₁)² + (x₂ - y₂)²)) / 2` of the
horizontal velocity symmetrized in `y₁`, Chen and Hou II, App. B.4:
`u(x) = (1/π) ∫_{y₁ ≥ 0} K(x, y) W(y) dy` for `W` odd in `y₁`. -/
def horizontalVelocityKernel (x y : ℝ^2) : ℝ :=
  ((x 1 - y 1) / ‖x - y‖ ^ 2 - (x 1 - y 1) / ((x 0 + y 0) ^ 2 + (x 1 - y 1) ^ 2)) / 2

/-- **The change of variables `y = x + x₁ s`**: `K(x, x + x₁ s) = -K_s(s) / x₁` for `x₁ > 0`. -/
theorem horizontalVelocityKernel_add_smul {x : ℝ^2} (hx : 0 < x 0) (s : ℝ^2) :
    horizontalVelocityKernel x (x + x 0 • s) = -axisKernel s / x 0 := by
  have hc : x 0 ≠ 0 := hx.ne'
  have hn : ‖x - (x + x 0 • s)‖ ^ 2 = x 0 ^ 2 * ‖s‖ ^ 2 := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [horizontalVelocityKernel, axisKernel, hn, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  have e1 : x 1 - (x 1 + x 0 * s 1) = -(x 0 * s 1) := by ring
  have e2 : (x 0 + (x 0 + x 0 * s 0)) ^ 2 + (-(x 0 * s 1)) ^ 2 =
      x 0 ^ 2 * ((s 0 + 2) ^ 2 + s 1 ^ 2) := by ring
  rw [e1, e2]
  rcases eq_or_ne (‖s‖ ^ 2) 0 with h | h
  · have hs1 : s 1 = 0 := by
      rw [EuclideanSpace.norm_sq_fin_two] at h; nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
    simp [hs1]
  rcases eq_or_ne ((s 0 + 2) ^ 2 + s 1 ^ 2) 0 with h' | h'
  · have hs1 : s 1 = 0 := by nlinarith [sq_nonneg (s 0 + 2), sq_nonneg (s 1)]
    simp [hs1]
  field_simp
  ring

/-- For `c > 0`, `c ([a, b] × [d, e]) = [c a, c b] × [c d, c e]`. -/
private theorem smul_coordinateRectangle {c : ℝ} (hc : 0 < c) (a b d e : ℝ) :
    c • coordinateRectangle a b d e = coordinateRectangle (c * a) (c * b) (c * d) (c * e) := by
  ext y
  constructor
  · rintro ⟨z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    simp only [mem_coordinateRectangle, PiLp.smul_apply, smul_eq_mul, mem_Icc]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨c⁻¹ • y, ⟨⟨?_, ?_⟩, ?_, ?_⟩, by simp only; rw [smul_inv_smul₀ hc.ne']⟩ <;>
      simp only [PiLp.smul_apply, smul_eq_mul]
    · rw [le_inv_mul_iff₀ hc]; exact h1
    · rw [inv_mul_le_iff₀ hc]; exact h2
    · rw [le_inv_mul_iff₀ hc]; exact h3
    · rw [inv_mul_le_iff₀ hc]; exact h4

/-- **The singular part near the axis by `y = x + x₁ s`**: for `x₁ > 0` and every `ω`,
`∫_{x + x₁ ([a,b] × [c,d])} K(x, y) ω(y) dy = -x₁ ∫_{[a,b] × [c,d]} K_s(s) ω(x + x₁ s) ds`. -/
theorem setIntegral_horizontalVelocityKernel {x : ℝ^2} (hx : 0 < x 0) (a b c d : ℝ)
    (ω : ℝ^2 → ℝ) :
    ∫ y in coordinateRectangle (x 0 + x 0 * a) (x 0 + x 0 * b) (x 1 + x 0 * c) (x 1 + x 0 * d),
        horizontalVelocityKernel x y * ω y =
      -x 0 * ∫ s in coordinateRectangle a b c d, axisKernel s * ω (x + x 0 • s) := by
  set g : ℝ^2 → ℝ := fun z ↦ horizontalVelocityKernel x (x + z) * ω (x + z) with hg
  have hscale := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (ℝ^2))) g
    (coordinateRectangle a b c d) hx
  rw [finrank_euclideanSpace_fin, smul_coordinateRectangle hx] at hscale
  have htrans : ∫ z in coordinateRectangle (x 0 * a) (x 0 * b) (x 0 * c) (x 0 * d), g z =
      ∫ y in coordinateRectangle (x 0 + x 0 * a) (x 0 + x 0 * b) (x 1 + x 0 * c) (x 1 + x 0 * d),
        horizontalVelocityKernel x y * ω y := by
    have := setIntegral_coordinateRectangle_add (fun y ↦ horizontalVelocityKernel x y * ω y)
      (x 0 * a) (x 0 * b) (x 0 * c) (x 0 * d) x
    simp only [hg]
    rw [show (x 0 * a + x 0) = x 0 + x 0 * a by ring, show (x 0 * b + x 0) = x 0 + x 0 * b by ring,
      show (x 0 * c + x 1) = x 1 + x 0 * c by ring, show (x 0 * d + x 1) = x 1 + x 0 * d by ring]
      at this
    rw [← this]
    simp only [add_comm x]
  rw [← htrans]
  have hpt : ∀ s, axisKernel s * ω (x + x 0 • s) = -x 0 * g (x 0 • s) := fun s ↦ by
    simp only [hg, horizontalVelocityKernel_add_smul hx]
    field_simp
  simp_rw [hpt, integral_const_mul, hscale, smul_eq_mul]
  have hc : x 0 ≠ 0 := hx.ne'
  field_simp

/-- `K_s` is odd under the reflection `s₂ ↦ -s₂`. -/
private theorem axisKernel_reflection_one (s : ℝ^2) :
    axisKernel (PDE.Common.coordinateReflection 1 s) = -axisKernel s := by
  simp only [axisKernel, PDE.Common.norm_coordinateReflection,
    PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)]
  ring

/-- **The singular part near the axis**, Chen and Hou II, App. B.4: if `|ω(x + x₁ s)| ≤ Mu` on
`[a, b] × [0, L]` and `≤ Md` on `[a, b] × [-L, 0]`, with `-1 ≤ a` and `x₁ > 0`, then
`|∫_{x + x₁ ([a,b] × [-L,L])} K(x, y) ω(y) dy| ≤ x₁ (Mu + Md) ∫_{[a,b] × [0,L]} K_s`. With
`[a, b] = [-1, 0]` and `L = kh/x₁` this is the bound of `II_{in,1}` by `J₁(B₁)`
(`axisStripIntegral`), with `[a, b] = [0, L]` and `L = h/x₁` that of `II_{in,2}` by `J₂(B₂)`
(`axisSquareIntegral`), with the factor `x₁` in front of `II_{in,i}`. -/
theorem abs_setIntegral_horizontalVelocityKernel_le {x : ℝ^2} (hx : 0 < x 0) {a b L Mu Md : ℝ}
    (ha : -1 ≤ a) (hMu : 0 ≤ Mu) (hMd : 0 ≤ Md) {ω : ℝ^2 → ℝ}
    (hu : ∀ s ∈ coordinateRectangle a b 0 L, |ω (x + x 0 • s)| ≤ Mu)
    (hd : ∀ s ∈ coordinateRectangle a b (-L) 0, |ω (x + x 0 • s)| ≤ Md) :
    |∫ y in coordinateRectangle (x 0 + x 0 * a) (x 0 + x 0 * b) (x 1 + x 0 * -L) (x 1 + x 0 * L),
        horizontalVelocityKernel x y * ω y| ≤
      x 0 * (Mu + Md) * ∫ s in coordinateRectangle a b 0 L, axisKernel s := by
  rw [setIntegral_horizontalVelocityKernel hx, abs_mul, abs_neg, abs_of_pos hx]
  set J := ∫ s in coordinateRectangle a b 0 L, axisKernel s with hJ
  set f : ℝ^2 → ℝ := fun s ↦ axisKernel s * ω (x + x 0 • s) with hf
  set Rp := coordinateRectangle a b 0 L
  set Rm := coordinateRectangle a b (-L) 0
  have hJ0 : 0 ≤ J := setIntegral_nonneg (measurableSet_coordinateRectangle _ _ _ _)
    fun s hs ↦ axisKernel_nonneg (ha.trans hs.1.1) hs.2.1
  have hsub : coordinateRectangle a b (-L) L ⊆ Rp ∪ Rm := by
    rintro s ⟨h1, h2, h3⟩
    rcases le_total 0 (s 1) with h | h
    · exact Or.inl ⟨h1, h, h3⟩
    · exact Or.inr ⟨h1, h2, h⟩
  have hKp : ∀ s ∈ Rp, |axisKernel s| = axisKernel s := fun s hs ↦
    abs_of_nonneg (axisKernel_nonneg (ha.trans hs.1.1) hs.2.1)
  have hlinJ : ∫⁻ s in Rp, ENNReal.ofReal (axisKernel s) = ENNReal.ofReal J := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_axisKernel a b 0 L)
      ((ae_restrict_iff' (measurableSet_coordinateRectangle _ _ _ _)).2
        (Eventually.of_forall fun s hs ↦ axisKernel_nonneg (ha.trans hs.1.1) hs.2.1))]
  have hrefl : ∫⁻ s in Rm, ENNReal.ofReal |axisKernel s| = ENNReal.ofReal J := by
    have hpre : PDE.Common.coordinateReflection 1 ⁻¹' Rp = Rm := by
      ext s
      simp only [Rp, Rm, mem_preimage, mem_coordinateRectangle, mem_Icc,
        PDE.Common.coordinateReflection_apply_same,
        PDE.Common.coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)]
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
    have hemb := (PDE.Common.coordinateReflectionLinearIsometryEquiv (n := 2)
      1).toMeasurableEquiv.measurableEmbedding
    have := (PDE.Common.measurePreserving_coordinateReflection (n := 2)
      1).setLIntegral_comp_preimage_emb hemb (fun s ↦ ENNReal.ofReal |axisKernel s|) Rp
    rw [hpre] at this
    simp only [axisKernel_reflection_one, abs_neg] at this
    rw [this, ← hlinJ]
    exact setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _) fun s hs ↦ by
      rw [hKp s hs]
  have hmain : ‖∫ s in coordinateRectangle a b (-L) L, f s‖ₑ ≤
      ENNReal.ofReal ((Mu + Md) * J) := by
    calc ‖∫ s in coordinateRectangle a b (-L) L, f s‖ₑ
        ≤ ∫⁻ s in coordinateRectangle a b (-L) L, ‖f s‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s in Rp ∪ Rm, ‖f s‖ₑ := lintegral_mono_set hsub
      _ ≤ (∫⁻ s in Rp, ‖f s‖ₑ) + ∫⁻ s in Rm, ‖f s‖ₑ := lintegral_union_le _ _ _
      _ ≤ (∫⁻ s in Rp, ENNReal.ofReal Mu * ENNReal.ofReal (axisKernel s)) +
            ∫⁻ s in Rm, ENNReal.ofReal Md * ENNReal.ofReal |axisKernel s| := by
          refine add_le_add (setLIntegral_mono' (measurableSet_coordinateRectangle _ _ _ _)
            fun s hs ↦ ?_) (setLIntegral_mono' (measurableSet_coordinateRectangle _ _ _ _)
            fun s hs ↦ ?_)
          · rw [hf, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hMu, abs_mul, hKp s hs]
            exact ENNReal.ofReal_le_ofReal ((mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right
              (hu s hs) (axisKernel_nonneg (ha.trans hs.1.1) hs.2.1)))
          · rw [hf, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hMd, abs_mul]
            exact ENNReal.ofReal_le_ofReal ((mul_comm _ _).trans_le
              (mul_le_mul_of_nonneg_right (hd s hs) (abs_nonneg _)))
      _ = ENNReal.ofReal ((Mu + Md) * J) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlinJ, hrefl,
            ← ENNReal.ofReal_mul hMu, ← ENNReal.ofReal_mul hMd,
            ← ENNReal.ofReal_add (mul_nonneg hMu hJ0) (mul_nonneg hMd hJ0)]
          ring_nf
  rw [Real.enorm_eq_ofReal_abs] at hmain
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain) hx.le

end PotentialTheory.Planar
