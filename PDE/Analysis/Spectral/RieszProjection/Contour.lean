/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Circle integrals of the resolvent

Let `a` be an element of a complex Banach algebra `A` and let `g` be a scalar
function. The weighted resolvent integral

`rieszIntegral a r g = (2πi)⁻¹ ∮_{|z| = r} g(z) (z - a)⁻¹ dz`

is the holomorphic functional calculus along the circle of radius `r`. For
`g = 1` it is the Riesz projection `rieszInner a r` onto the part of the
spectrum inside the circle.

The facts below need only one circle:

* the first resolvent identity and the relation `a (z - a)⁻¹ = z (z - a)⁻¹ - 1`,
  which give `a · Φ(g) = Φ(z g) - ((2πi)⁻¹ ∮ g) · 1`;
* every element commuting with `a` commutes with each weighted integral;
* a circle free of spectrum lies in an open annulus free of spectrum;
* the integral does not change when the radius moves across an annulus free of
  spectrum on which the weight is holomorphic;
* the norm bound `‖Φ(g)‖ ≤ r · sup ‖g(z) (z - a)⁻¹‖` over the circle;
* the lower bound `‖(z - a)⁻¹‖ ≥ |p - z|⁻¹` for every point `p` of the spectrum, so the
  resolvent is not integrable on a circle that meets the spectrum without lying in it, and
  `rieszInner a r = 0` whenever the circle meets the spectrum;
* `C(0, -r)` is the circle `C(0, r)` started at the opposite point, so
  `rieszInner a (-r) = rieszInner a r`.
-/

@[expose] public noncomputable section

open Complex Metric Set
open scoped Real

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A continuous complex-linear map commutes with circle integrals of integrable functions. -/
theorem map_circleIntegral (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

end ContinuousLinearMap

namespace circleIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A circle integral does not change when the radius changes sign: `C(c, -R)` runs over the
circle `C(c, R)` in the same direction, starting at the opposite point. -/
theorem integral_neg_radius (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, -R), f z) = ∮ z in C(c, R), f z := by
  set F : ℝ → E := fun θ ↦ deriv (circleMap c R) θ • f (circleMap c R θ)
  have hper : Function.Periodic F (2 * π) := fun θ ↦ by
    simp only [F, deriv_circleMap, periodic_circleMap c R θ, periodic_circleMap 0 R θ]
  have hshift (θ : ℝ) : deriv (circleMap c (-R)) θ • f (circleMap c (-R) θ) = F (θ + π) := by
    simp only [F, deriv_circleMap, circleMap_neg_radius]
  calc (∮ z in C(c, -R), f z) = ∫ θ in 0..2 * π, F (θ + π) := by
        simp only [circleIntegral, hshift]
    _ = ∫ θ in π..π + 2 * π, F θ := by
        rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm]
    _ = ∫ θ in 0..0 + 2 * π, F θ := hper.intervalIntegral_add_eq π 0
    _ = ∮ z in C(c, R), f z := by rw [zero_add]; rfl

end circleIntegral

namespace PDE.Analysis.Spectral

section Resolvent

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] {a : A}

/-- On the resolvent set, `(z - a) (z - a)⁻¹ = 1`. -/
theorem smul_one_sub_mul_resolvent {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    (z • (1 : A) - a) * resolvent a z = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact Ring.mul_inverse_cancel _ hz

/-- On the resolvent set, `(z - a)⁻¹ (z - a) = 1`. -/
theorem resolvent_mul_smul_one_sub {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    resolvent a z * (z • (1 : A) - a) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact Ring.inverse_mul_cancel _ hz

/-- On the resolvent set, `a (z - a)⁻¹ = z (z - a)⁻¹ - 1`. -/
theorem mul_resolvent {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    a * resolvent a z = z • resolvent a z - 1 := by
  have h := smul_one_sub_mul_resolvent hz
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  rw [← h]
  abel

/-- On the resolvent set, `(z - a)⁻¹ a = z (z - a)⁻¹ - 1`. -/
theorem resolvent_mul {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    resolvent a z * a = z • resolvent a z - 1 := by
  have h := resolvent_mul_smul_one_sub hz
  rw [mul_sub, mul_smul_comm, mul_one] at h
  rw [← h]
  abel

/-- The first resolvent identity `(z - a)⁻¹ - (w - a)⁻¹ = (w - z) (z - a)⁻¹ (w - a)⁻¹`. -/
theorem resolvent_sub_resolvent_eq_smul_mul {z w : ℂ} (hz : z ∈ resolventSet ℂ a)
    (hw : w ∈ resolventSet ℂ a) :
    resolvent a z - resolvent a w = (w - z) • (resolvent a z * resolvent a w) := by
  have hzw : resolvent a z * ((w • (1 : A) - a) - (z • (1 : A) - a)) * resolvent a w =
      resolvent a z - resolvent a w := by
    rw [mul_sub, sub_mul, mul_assoc, smul_one_sub_mul_resolvent hw, mul_one,
      resolvent_mul_smul_one_sub hz, one_mul]
  rw [← hzw, sub_sub_sub_cancel_right, ← sub_smul, mul_smul_comm, mul_one, smul_mul_assoc]

/-- For distinct points of the resolvent set,
`(z - a)⁻¹ (w - a)⁻¹ = (w - z)⁻¹ ((z - a)⁻¹ - (w - a)⁻¹)`. -/
theorem resolvent_mul_resolvent {z w : ℂ} (hz : z ∈ resolventSet ℂ a)
    (hw : w ∈ resolventSet ℂ a) (hzw : z ≠ w) :
    resolvent a z * resolvent a w = (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
  rw [resolvent_sub_resolvent_eq_smul_mul hz hw, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hzw.symm), one_smul]

omit [NormedAlgebra ℂ A] in
/-- An element commuting with `x` commutes with `Ring.inverse x`. -/
theorem commute_ringInverse {b x : A} (h : Commute b x) : Commute b (Ring.inverse x) := by
  by_cases hx : IsUnit x
  · rw [Ring.inverse_of_isUnit hx]
    exact Commute.units_inv_right (by rwa [hx.unit_spec])
  · rw [Ring.inverse_non_unit x hx]
    exact Commute.zero_right b

/-- An element commuting with `a` commutes with every value of its resolvent. -/
theorem commute_resolvent {b : A} (h : Commute b a) (z : ℂ) : Commute b (resolvent a z) :=
  commute_ringInverse ((Algebra.commute_algebraMap_right z b).sub_right h)

/-- The circle of radius `r` lies in the resolvent set when it carries no spectrum. -/
theorem sphere_subset_resolventSet {r : ℝ} (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    sphere (0 : ℂ) r ⊆ resolventSet ℂ a := fun z hz ↦
  spectrum.notMem_iff.mp (hfree z (mem_sphere_zero_iff_norm.mp hz))

/-- Every circle inside a spectrum-free open annulus lies in the resolvent set. -/
theorem sphere_subset_resolventSet_of_annulus {r δ ρ : ℝ}
    (h : ∀ z : ℂ, r - δ < ‖z‖ → ‖z‖ < r + δ → z ∈ resolventSet ℂ a)
    (h₁ : r - δ < ρ) (h₂ : ρ < r + δ) : sphere (0 : ℂ) ρ ⊆ resolventSet ℂ a := fun z hz ↦
  h z (by rwa [mem_sphere_zero_iff_norm.mp hz]) (by rwa [mem_sphere_zero_iff_norm.mp hz])

variable [CompleteSpace A]

/-- The resolvent is complex differentiable on the resolvent set. -/
theorem differentiableAt_resolvent {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    DifferentiableAt ℂ (resolvent a) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt

/-- The resolvent is continuous on the resolvent set. -/
theorem continuousOn_resolvent : ContinuousOn (resolvent a) (resolventSet ℂ a) :=
  fun _ hz ↦ (differentiableAt_resolvent hz).continuousAt.continuousWithinAt

/-- A circle free of spectrum lies in an open annulus free of spectrum. -/
theorem exists_annulus_subset_resolventSet {r : ℝ} (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    ∃ δ, 0 < δ ∧ δ < r ∧
      ∀ z : ℂ, r - δ < ‖z‖ → ‖z‖ < r + δ → z ∈ resolventSet ℂ a := by
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := (spectrum.isCompact a).exists_forall_le'
    (f := fun z : ℂ ↦ |‖z‖ - r|) (by fun_prop) (a := 0)
    (fun z hz ↦ abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hfree z h hz))
  refine ⟨min δ₀ (r / 2), lt_min hδ₀ (half_pos hr),
    (min_le_right _ _).trans_lt (half_lt_self hr), fun z h₁ h₂ ↦ ?_⟩
  by_contra hz
  have hm := min_le_left δ₀ (r / 2)
  have : |‖z‖ - r| < δ₀ := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  linarith [hδ₀le z hz]

/-- The resolvent is large near the spectrum: `1 ≤ |p - z| ‖(z - a)⁻¹‖` for `z` in the
resolvent set and `p` in the spectrum. -/
theorem one_le_norm_sub_mul_norm_resolvent {z p : ℂ} (hz : z ∈ resolventSet ℂ a)
    (hp : p ∈ spectrum ℂ a) : 1 ≤ ‖p - z‖ * ‖resolvent a z‖ := by
  by_contra! h
  have hu : IsUnit (1 - (z - p) • resolvent a z) := by
    refine IsUnit.one_sub_of_norm_lt_one ?_
    rwa [norm_smul, norm_sub_rev]
  have heq : algebraMap ℂ A p - a =
      (algebraMap ℂ A z - a) * (1 - (z - p) • resolvent a z) := by
    rw [mul_sub, mul_one, mul_smul_comm, Algebra.algebraMap_eq_smul_one z,
      smul_one_sub_mul_resolvent hz, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  exact hp (by rw [spectrum.mem_resolventSet_iff, heq]; exact hz.mul hu)

open MeasureTheory in
/-- On a circle that meets the spectrum without lying in it, the resolvent is not circle
integrable. Along an arc of the resolvent set ending at a point `p` of the spectrum, the
resolvent is at least `|p - z|⁻¹`, and `|p - z|⁻¹` is not integrable along the arc. -/
theorem not_circleIntegrable_resolvent {r : ℝ} {p w : ℂ} (hp : ‖p‖ = r)
    (hpσ : p ∈ spectrum ℂ a) (hw : ‖w‖ = r) (hwσ : w ∉ spectrum ℂ a) :
    ¬CircleIntegrable (resolvent a) 0 r := by
  have hr : 0 < r := by aesop
  intro hint
  have hrange (z : ℂ) (hz : ‖z‖ = r) : ∃ θ, circleMap 0 r θ = z := by
    have hz' : z ∈ range (circleMap 0 r) := by
      rw [range_circleMap, abs_of_pos hr]
      exact mem_sphere_zero_iff_norm.mpr hz
    exact hz'
  obtain ⟨θ₀, hθ₀⟩ := hrange w hw
  obtain ⟨θ₁, hθ₁⟩ := hrange p hp
  -- the first angle `θp ≥ θ₀` at which the circle meets the spectrum
  set F : Set ℝ := circleMap 0 r ⁻¹' spectrum ℂ a ∩ Ici θ₀
  have hFclosed : IsClosed F :=
    ((spectrum.isClosed a).preimage (continuous_circleMap 0 r)).inter isClosed_Ici
  obtain ⟨n, hn⟩ := exists_nat_ge ((θ₀ - θ₁) / (2 * π))
  have hFne : F.Nonempty := by
    refine ⟨θ₁ + n * (2 * π), ?_, ?_⟩
    · simp only [mem_preimage, (periodic_circleMap 0 r).nat_mul n θ₁, hθ₁, hpσ]
    · have := (div_le_iff₀ Real.two_pi_pos).mp hn
      simp only [mem_Ici]
      linarith
  have hbdd : BddBelow F := ⟨θ₀, fun θ hθ ↦ hθ.2⟩
  set θp := sInf F
  have hθpF : θp ∈ F := hFclosed.csInf_mem hFne hbdd
  have hθ₀p : θ₀ < θp := lt_of_le_of_ne hθpF.2 fun h ↦ hwσ (by
    rw [← hθ₀, h]
    exact hθpF.1)
  have hfree (θ : ℝ) (h₁ : θ₀ ≤ θ) (h₂ : θ < θp) : circleMap 0 r θ ∈ resolventSet ℂ a :=
    spectrum.notMem_iff.mp fun hσ ↦ (csInf_le hbdd ⟨hσ, h₁⟩).not_gt h₂
  -- on `[θ₀, θp)` the resolvent is at least `(r (θp - θ))⁻¹`, which is not integrable
  have hper : Function.Periodic (fun θ ↦ resolvent a (circleMap 0 r θ)) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 r θ]
  have hint' := hper.intervalIntegrable₀ Real.two_pi_pos.ne' hint θ₀ θp
  have hinv : IntervalIntegrable (fun θ ↦ (θ - θp)⁻¹) volume θ₀ θp := by
    refine (hint'.norm.const_mul r).mono_fun
      ((measurable_id.sub_const θp).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_uIoc).mono fun θ hθ ↦ ?_
    rw [uIoc_of_le hθ₀p.le] at hθ
    dsimp only
    rcases hθ.2.eq_or_lt with h | h
    · rw [h, sub_self, inv_zero, norm_zero]
      exact norm_nonneg _
    · have h1 := one_le_norm_sub_mul_norm_resolvent (hfree θ hθ.1.le h) hθpF.1
      have hlip := (lipschitzWith_circleMap 0 r).dist_le_mul θp θ
      rw [dist_eq_norm, Real.dist_eq, abs_of_pos (sub_pos.mpr h), Real.coe_nnabs,
        abs_of_pos hr] at hlip
      have hpos : 0 < θp - θ := sub_pos.mpr h
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_neg (sub_neg.mpr h), neg_sub,
        abs_of_nonneg (by positivity), inv_le_iff_one_le_mul₀ hpos]
      calc 1 ≤ ‖circleMap 0 r θp - circleMap 0 r θ‖ * ‖resolvent a (circleMap 0 r θ)‖ := h1
        _ ≤ r * (θp - θ) * ‖resolvent a (circleMap 0 r θ)‖ := by gcongr
        _ = r * ‖resolvent a (circleMap 0 r θ)‖ * (θp - θ) := by ring
  rcases intervalIntegrable_sub_inv_iff.mp hinv with h | h
  · exact hθ₀p.ne h
  · exact h right_mem_uIcc

end Resolvent

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The weighted resolvent integral `(2πi)⁻¹ ∮_{|z| = r} g(z) (z - a)⁻¹ dz`. -/
def rieszIntegral (a : A) (r : ℝ) (g : ℂ → ℂ) : A :=
  ((2 * π * I)⁻¹ : ℂ) • ∮ z in C(0, r), g z • resolvent a z

/-- The Riesz projection of `a` for the disc of radius `r`, the circle integral
`(2πi)⁻¹ ∮_{|z| = r} (z - a)⁻¹ dz`. For `r > 0` and a circle that carries no spectrum it is
the idempotent onto the spectral part of `a` inside the disc. -/
def rieszInner (a : A) (r : ℝ) : A :=
  ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ z in C(0, r), Ring.inverse (z • 1 - a)

/-- The Riesz projection is the weighted integral with weight `1`. -/
theorem rieszInner_eq_rieszIntegral (a : A) (r : ℝ) : rieszInner a r = rieszIntegral a r 1 := by
  simp [rieszInner, rieszIntegral, resolvent, Algebra.algebraMap_eq_smul_one]

/-- The Riesz projection does not change when the radius changes sign. -/
theorem rieszInner_neg_radius (a : A) (r : ℝ) : rieszInner a (-r) = rieszInner a r := by
  simp only [rieszInner, circleIntegral.integral_neg_radius]

variable {a : A} {r : ℝ} {g : ℂ → ℂ}

/-- The weighted integral depends only on the weight on the circle. -/
theorem rieszIntegral_congr (hr : 0 ≤ r) {g₁ g₂ : ℂ → ℂ} (h : EqOn g₁ g₂ (sphere 0 r)) :
    rieszIntegral a r g₁ = rieszIntegral a r g₂ := by
  unfold rieszIntegral
  congr 1
  exact circleIntegral.integral_congr hr fun z hz ↦ by simp only [h hz]

/-- The weighted integral is homogeneous in the weight. -/
theorem rieszIntegral_smul (c : ℂ) :
    rieszIntegral a r (fun z ↦ c * g z) = c • rieszIntegral a r g := by
  unfold rieszIntegral
  simp only [mul_smul]
  rw [circleIntegral.integral_smul, smul_comm]

/-- The norm bound `‖Φ(g)‖ ≤ r C` when `‖g(z) (z - a)⁻¹‖ ≤ C` on the circle. -/
theorem norm_rieszIntegral_le (hr : 0 ≤ r) {C : ℝ}
    (h : ∀ z ∈ sphere (0 : ℂ) r, ‖g z • resolvent a z‖ ≤ C) :
    ‖rieszIntegral a r g‖ ≤ r * C :=
  circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr h

/-- The weighted integral with weight `0` vanishes. -/
theorem rieszIntegral_zero (a : A) (r : ℝ) : rieszIntegral a r 0 = 0 := by
  simp [rieszIntegral, circleIntegral]

variable [CompleteSpace A]

/-- On a circle free of spectrum, `g(z) (z - a)⁻¹` is continuous for continuous `g`. -/
theorem continuousOn_smul_resolvent (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a)
    (hg : ContinuousOn g (sphere 0 r)) :
    ContinuousOn (fun z ↦ g z • resolvent a z) (sphere 0 r) :=
  hg.smul (continuousOn_resolvent.mono hres)

/-- On a circle free of spectrum, `g(z) (z - a)⁻¹` is circle integrable for continuous `g`. -/
theorem circleIntegrable_smul_resolvent (hr : 0 ≤ r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a)
    (hg : ContinuousOn g (sphere 0 r)) :
    CircleIntegrable (fun z ↦ g z • resolvent a z) 0 r :=
  (continuousOn_smul_resolvent hres hg).circleIntegrable hr

/-- On a circle free of spectrum, the weighted integral is additive in continuous weights. -/
theorem rieszIntegral_sub (hr : 0 ≤ r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a)
    {g₁ g₂ : ℂ → ℂ} (hg₁ : ContinuousOn g₁ (sphere 0 r)) (hg₂ : ContinuousOn g₂ (sphere 0 r)) :
    rieszIntegral a r (fun z ↦ g₁ z - g₂ z) = rieszIntegral a r g₁ - rieszIntegral a r g₂ := by
  unfold rieszIntegral
  rw [← smul_sub, ← circleIntegral.integral_sub (circleIntegrable_smul_resolvent hr hres hg₁)
    (circleIntegrable_smul_resolvent hr hres hg₂)]
  simp only [sub_smul]

/-- An element commuting with `a` commutes with every weighted resolvent integral. -/
theorem commute_rieszIntegral {b : A} (h : Commute b a) (r : ℝ) (g : ℂ → ℂ) :
    Commute b (rieszIntegral a r g) := by
  unfold rieszIntegral
  refine Commute.smul_right ?_ _
  by_cases hint : CircleIntegrable (fun z ↦ g z • resolvent a z) 0 r
  · have hl := (ContinuousLinearMap.mul ℂ A b).map_circleIntegral hint
    have hr := ((ContinuousLinearMap.mul ℂ A).flip b).map_circleIntegral hint
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
    change b * _ = _ * b
    rw [hl, hr]
    congr 1
    ext z
    rw [mul_smul_comm, smul_mul_assoc, (commute_resolvent h z).eq]
  · rw [circleIntegral.integral_undef hint]
    exact Commute.zero_right b

/-- An element commuting with `a` commutes with its Riesz projection. -/
theorem commute_rieszInner {S : A} (h : Commute S a) : Commute S (rieszInner a r) := by
  rw [rieszInner_eq_rieszIntegral]
  exact commute_rieszIntegral h r 1

/-- If the circle of radius `r` meets the spectrum, the integral defining `rieszInner a r` is
`0`. Either the whole circle lies in the spectrum, where `Ring.inverse` vanishes, or the
resolvent is not integrable on the circle. -/
theorem rieszInner_eq_zero_of_mem_spectrum {z : ℂ} (hz : ‖z‖ = r) (hzσ : z ∈ spectrum ℂ a) :
    rieszInner a r = 0 := by
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  have hfun : (fun w : ℂ ↦ Ring.inverse (w • (1 : A) - a)) = resolvent a := by
    ext w
    simp [resolvent, Algebra.algebraMap_eq_smul_one]
  unfold rieszInner
  rw [hfun]
  by_cases hw : ∃ w : ℂ, ‖w‖ = r ∧ w ∉ spectrum ℂ a
  · obtain ⟨w, hw, hwσ⟩ := hw
    rcases hr.eq_or_lt with rfl | hr'
    · simp
    · rw [circleIntegral.integral_undef (not_circleIntegrable_resolvent hz hzσ hw hwσ),
        smul_zero]
  · rw [circleIntegral.integral_congr hr (f := resolvent a) (g := fun _ ↦ 0) fun w hw' ↦
      Ring.inverse_non_unit _ (spectrum.mem_iff.mp (Classical.byContradiction fun hwσ ↦
        hw ⟨w, mem_sphere_zero_iff_norm.mp hw', hwσ⟩))]
    simp [circleIntegral]

/-- The multiplication rule `a · Φ(g) = Φ(z g) - ((2πi)⁻¹ ∮ g) · 1` on a circle free of
spectrum. -/
theorem mul_rieszIntegral (hr : 0 ≤ r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a)
    (hg : ContinuousOn g (sphere 0 r)) :
    a * rieszIntegral a r g =
      rieszIntegral a r (fun z ↦ z * g z) - ((2 * π * I)⁻¹ * ∮ z in C(0, r), g z) • (1 : A) := by
  have hint := circleIntegrable_smul_resolvent hr hres hg
  have hz : ContinuousOn (fun z : ℂ ↦ z * g z) (sphere 0 r) := continuousOn_id.mul hg
  have h1 : CircleIntegrable (fun z ↦ g z • (1 : A)) 0 r :=
    (hg.smul continuousOn_const).circleIntegrable hr
  have hl := (ContinuousLinearMap.mul ℂ A a).map_circleIntegral hint
  simp only [ContinuousLinearMap.mul_apply'] at hl
  have hcongr : (∮ z in C(0, r), a * (g z • resolvent a z)) =
      ∮ z in C(0, r), ((z * g z) • resolvent a z - g z • (1 : A)) := by
    refine circleIntegral.integral_congr hr fun z hz ↦ ?_
    simp only [mul_smul_comm, mul_resolvent (hres hz), smul_sub, mul_smul]
    rw [smul_comm]
  unfold rieszIntegral
  rw [mul_smul_comm, hl, hcongr, circleIntegral.integral_sub
    (circleIntegrable_smul_resolvent hr hres hz) h1, circleIntegral.integral_smul_const,
    smul_sub, smul_smul]

/-- On a circle free of spectrum, `a^n` times the Riesz projection is the integral with
weight `z^n`. -/
theorem pow_mul_rieszInner (hr : 0 ≤ r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a) (n : ℕ) :
    a ^ n * rieszInner a r = rieszIntegral a r (fun z ↦ z ^ n) := by
  induction n with
  | zero => simp [rieszInner_eq_rieszIntegral, Pi.one_def]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_rieszIntegral hr hres (continuous_pow n).continuousOn]
    have h0 : (∮ z in C(0, r), z ^ n) = 0 := by
      simpa using circleIntegral.integral_sub_zpow_of_ne (n := (n : ℤ)) (by omega) 0 0 r
    rw [h0, mul_zero, zero_smul, sub_zero]
    congr 1
    ext z
    ring

/-- The weighted integral does not change across a closed annulus free of spectrum on which
the weight is holomorphic. -/
theorem rieszIntegral_eq_of_annulus {r₁ r₂ : ℝ} (h₀ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hres : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ a)
    (hg : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → DifferentiableAt ℂ g z) :
    rieszIntegral a r₂ g = rieszIntegral a r₁ g := by
  have hd : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      DifferentiableAt ℂ (fun z ↦ g z • resolvent a z) z := fun z h₁ h₂ ↦
    (hg z h₁ h₂).smul (differentiableAt_resolvent (hres z h₁ h₂))
  unfold rieszIntegral
  congr 1
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable h₀ hle countable_empty
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · simp only [mem_sdiff, mem_closedBall, dist_zero_right, mem_ball, not_lt] at hz
    exact (hd z hz.2 hz.1).continuousAt.continuousWithinAt
  · simp only [mem_sdiff, mem_ball, dist_zero_right, mem_closedBall, not_le, mem_empty_iff_false,
      not_false_eq_true, and_true] at hz
    exact hd z hz.2.le hz.1.le

/-- The Riesz projection does not change across a closed annulus free of spectrum. -/
theorem rieszInner_eq_of_annulus {r₁ r₂ : ℝ} (h₀ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hres : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ a) :
    rieszInner a r₂ = rieszInner a r₁ := by
  simp only [rieszInner_eq_rieszIntegral]
  exact rieszIntegral_eq_of_annulus h₀ hle hres fun _ _ _ ↦ differentiableAt_const _

/-- The resolvent is bounded on a circle free of spectrum. -/
theorem exists_norm_resolvent_le (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a) :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent a z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
    (continuousOn_resolvent.mono hres)
  exact ⟨max M 0, le_max_right _ _, fun z hz ↦ (hM z hz).trans (le_max_left _ _)⟩

end PDE.Analysis.Spectral
