/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.L2Space
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Energy
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Restriction
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The quadratic Gagliardo norm

The shared Slobodeckij construction accepts every exponent `1 ≤ p ≤ ∞` and real Banach-valued
functions. We record the quadratic formulas used by the Fourier and Hilbert-space theory. With the
default exponent `p = 2`, `GagliardoSpace n s Ω` has norm squared equal to its base `L²` energy plus
its Gagliardo energy.

The first-difference construction describes fractional Sobolev regularity
when `0 < s < 1`. Its definition at other orders does not by itself identify
an integer-order or negative-order Sobolev space; `memGagliardo_neg_half_iff` records
one such degeneracy.

The seminorm is monotone in the domain, and `gagliardoSq_pos_of_isOpen` shows it is
strictly positive on an open set for every continuous function taking two different
values there.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

namespace GagliardoSpace

/-- The graph norm is the sum in quadrature of the base `L²` norm and the
difference-quotient `L²` norm. -/
theorem norm_sq_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : GagliardoSpace n s Ω (F := F)) :
    ‖u‖ ^ 2 =
      ‖toLp n s Ω u‖ ^ 2 + ‖differenceQuotient n s Ω u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

/-- The graph inner product is the sum of the base and difference-quotient
inner products. -/
theorem inner_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u v : GagliardoSpace n s Ω (F := F)) :
    inner ℝ u v =
      inner ℝ (toLp n s Ω u) (toLp n s Ω v) +
        inner ℝ (differenceQuotient n s Ω u)
          (differenceQuotient n s Ω v) :=
  WithLp.prod_inner_apply u.1 v.1

end GagliardoSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Gagliardo seminorm squared, as an extended-real integral.

`MemGagliardo` is stated through `MemLp`, which requires almost-everywhere strong
measurability in addition to finiteness of this integral. -/
noncomputable def gagliardoSq (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) (u : ℝ^n → F) :
    ℝ≥0∞ :=
  ∫⁻ p, (‖diffQuot n s u p‖₊ : ℝ≥0∞) ^ 2 ∂(gagliardoProductMeasure n Ω)

/-- The Gagliardo seminorm is monotone in the domain. -/
theorem gagliardoSq_mono {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂) (u : ℝ^n → F) :
    gagliardoSq n s Ω₁ u ≤ gagliardoSq n s Ω₂ u :=
  lintegral_mono' (gagliardoProductMeasure_mono h) le_rfl

/-! ## Membership in terms of the seminorm -/

/-- `gagliardoSq` is the square of the raw `L²` seminorm of the difference quotient.
This formula uses `eLpNorm'` because it applies to arbitrary functions; `eLpNorm` is
infinite for functions that are not almost-everywhere strongly measurable. -/
theorem gagliardoSq_eq_eLpNorm'_sq (u : ℝ^n → F) :
    gagliardoSq n s Ω u =
      eLpNorm' (diffQuot n s u) 2 (gagliardoProductMeasure n Ω) ^ 2 := by
  rw [gagliardoSq]
  simpa [ENNReal.rpow_two, enorm_eq_nnnorm] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (μ := gagliardoProductMeasure n Ω)
      (f := diffQuot n s u) (q := (2 : ℝ))
      (by norm_num))

namespace GagliardoSpace

/-- The raw seminorm of any representative is the squared norm of the stored
difference quotient, on an arbitrary domain. -/
theorem gagliardoSq_eq_norm_sq_of_toLp_ae (u : GagliardoSpace n s Ω (F := F))
    {f : ℝ^n → F}
    (hf : (toLp n s Ω u : ℝ^n → F) =ᵐ[volume.restrict Ω] f) :
    gagliardoSq n s Ω f =
      ENNReal.ofReal (‖differenceQuotient n s Ω u‖ ^ 2) := by
  have hdiff := (differenceQuotient_apply_ae u).trans
    (diffQuot_congr_ae (n := n) (s := s) hf)
  calc
    gagliardoSq n s Ω f =
        ∫⁻ p, ‖(differenceQuotient n s Ω u : ℝ^n × ℝ^n → F) p‖ₑ ^ 2
          ∂gagliardoProductMeasure n Ω :=
      lintegral_congr_ae (hdiff.fun_comp (fun t : F ↦ ‖t‖ₑ ^ 2)).symm
    _ = eLpNorm (differenceQuotient n s Ω u : ℝ^n × ℝ^n → F)
        2 (gagliardoProductMeasure n Ω) ^ 2 := by
      simpa [ENNReal.rpow_two] using
        (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
          (Lp.aestronglyMeasurable (differenceQuotient n s Ω u))).symm
    _ = ENNReal.ofReal (‖differenceQuotient n s Ω u‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

end GagliardoSpace

/-- The Gagliardo condition is square integrability on `Ω` together with
finiteness of `gagliardoSq`. -/
theorem memGagliardo_iff (u : ℝ^n → F) :
    MemGagliardo n s Ω u ↔
      MemLp u 2 ((volume : Measure (ℝ^n)).restrict Ω) ∧
        gagliardoSq n s Ω u < ⊤ := by
  have hnorm (hu : MemLp u 2 ((volume : Measure (ℝ^n)).restrict Ω)) :
      gagliardoSq n s Ω u =
        eLpNorm (diffQuot n s u) 2 (gagliardoProductMeasure n Ω) ^ 2 := by
    calc
      gagliardoSq n s Ω u =
          eLpNorm' (diffQuot n s u) 2 (gagliardoProductMeasure n Ω) ^ 2 :=
        gagliardoSq_eq_eLpNorm'_sq u
      _ = eLpNorm (diffQuot n s u) 2 (gagliardoProductMeasure n Ω) ^ 2 := by
        congr 1
        symm
        simpa using eLpNorm_eq_eLpNorm' (p := (2 : ℝ≥0∞))
          (by norm_num) (by norm_num)
          (aestronglyMeasurable_diffQuot hu.aestronglyMeasurable)
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [hnorm h.1]
    exact ENNReal.pow_lt_top h.2
  · rintro ⟨hu, hfinite⟩
    refine ⟨hu, ?_⟩
    rw [hnorm hu] at hfinite
    exact (ENNReal.pow_lt_top_iff.mp hfinite).resolve_right (by norm_num)

/-- Full-space specialization of `memGagliardo_iff`. -/
theorem memGagliardo_univ_iff (u : ℝ^n → F) :
    MemGagliardo n s Set.univ u ↔
      MemLp u 2 (volume : Measure (ℝ^n)) ∧
        gagliardoSq n s Set.univ u < ⊤ := by
  rw [memGagliardo_iff, Measure.restrict_univ]

/-! ## A degenerate order

At `s = -n/2`, the raw condition on a finite-measure domain reduces to square
integrability. This also covers empty domains and dimension zero. -/

/-- At `s = -n/2` the Gagliardo condition on a finite-measure domain is equivalent to
square integrability. The quotient is the difference of the two coordinate pullbacks of
`u`; finite measure makes both pullbacks square integrable. This describes the raw
Gagliardo condition, without identifying it with a negative-order space of distributions. -/
theorem memGagliardo_neg_half_iff (hΩ : volume Ω ≠ ⊤) (u : ℝ^n → F) :
    MemGagliardo n (-((n : ℝ) / 2)) Ω u
      ↔ MemLp u 2 ((volume : Measure (ℝ^n)).restrict Ω) := by
  have : IsFiniteMeasure ((volume : Measure (ℝ^n)).restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hΩ
  refine ⟨fun h ↦ h.1, fun hu ↦ ⟨hu, ?_⟩⟩
  rw [show diffQuot n (-((n : ℝ) / 2)) u = fun p ↦ u p.1 - u p.2 by
    funext p; simp [diffQuot]]
  have h1 : MemLp (fun p : ℝ^n × ℝ^n ↦ u p.1) 2 (gagliardoProductMeasure n Ω) :=
    MemLp.comp_fst hu _
  have h2 : MemLp (fun p : ℝ^n × ℝ^n ↦ u p.2) 2 (gagliardoProductMeasure n Ω) :=
    MemLp.comp_snd hu _
  exact h1.sub h2

/-! ## Positivity -/

/-- If a continuous function takes different values at `x` and `y`, then for some
`r > 0` it takes different values at every point of `ball x r` and every point of
`ball y r`. -/
theorem exists_ball_forall_ne {v : ℝ^n → ℝ} (hv : Continuous v) {x y : ℝ^n}
    (hxy : v x ≠ v y) :
    ∃ r > 0, ∀ a ∈ Metric.ball x r, ∀ b ∈ Metric.ball y r, v a ≠ v b := by
  set ε := |v x - v y| / 2 with hε
  have hε0 : 0 < ε := by
    have : v x - v y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.continuous_iff.mp hv x ε hε0
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.continuous_iff.mp hv y ε hε0
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun a ha b hb hab ↦ ?_⟩
  have hda := h₁ a (lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_left _ _))
  have hdb := h₂ b (lt_of_lt_of_le (Metric.mem_ball.mp hb) (min_le_right _ _))
  rw [Real.dist_eq] at hda hdb
  rw [hab] at hda
  have hlt : |v x - v y| < 2 * ε := by
    calc |v x - v y| ≤ |v x - v b| + |v b - v y| := abs_sub_le _ _ _
    _ < ε + ε := by
        refine add_lt_add ?_ ?_
        · rwa [abs_sub_comm]
        · exact hdb
    _ = 2 * ε := by ring
  rw [hε] at hlt
  linarith [abs_nonneg (v x - v y)]

/-- If `Ω` is open and a continuous real function `v` takes different values at two
points of `Ω`, then the Gagliardo seminorm of `v` on `Ω` is strictly positive, for
every order `s`. -/
theorem gagliardoSq_pos_of_isOpen (hΩ : IsOpen Ω) {v : ℝ^n → ℝ}
    (hv : Continuous v) {x y : ℝ^n} (hxΩ : x ∈ Ω) (hyΩ : y ∈ Ω) (hxy : v x ≠ v y) :
    0 < gagliardoSq n s Ω v := by
  obtain ⟨r, hr0, hsep⟩ := exists_ball_forall_ne hv hxy
  obtain ⟨rx, hrx0, hrxΩ⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
  obtain ⟨ry, hry0, hryΩ⟩ := Metric.isOpen_iff.1 hΩ y hyΩ
  obtain ⟨ρ, hρ0, hρr, hρx, hρy⟩ :
      ∃ ρ, 0 < ρ ∧ ρ ≤ r ∧ ρ ≤ rx ∧ ρ ≤ ry :=
    ⟨min r (min rx ry), lt_min hr0 (lt_min hrx0 hry0), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hbx : Metric.ball x ρ ⊆ Ω := (Metric.ball_subset_ball hρx).trans hrxΩ
  have hby : Metric.ball y ρ ⊆ Ω := (Metric.ball_subset_ball hρy).trans hryΩ
  rw [pos_iff_ne_zero]
  intro h0
  have hmeas : AEMeasurable (fun p : ℝ^n × ℝ^n ↦ (‖diffQuot n s v p‖₊ : ℝ≥0∞) ^ 2)
      (gagliardoProductMeasure n Ω) :=
    ((aestronglyMeasurable_diffQuot (n := n) (s := s) (Ω := Ω) (p := 2)
      hv.aestronglyMeasurable).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2
  rw [gagliardoSq] at h0
  have hae : ∀ᵐ p ∂(gagliardoProductMeasure n Ω), diffQuot n s v p = 0 := by
    filter_upwards [(lintegral_eq_zero_iff' hmeas).mp h0] with p hp
    simpa [pow_eq_zero_iff] using hp
  have hnull :
      (gagliardoProductMeasure n Ω) {p : ℝ^n × ℝ^n | diffQuot n s v p ≠ 0} = 0 := by
    rw [← ae_iff]
    exact hae
  have hsub : (Metric.ball x ρ) ×ˢ (Metric.ball y ρ)
      ⊆ {p : ℝ^n × ℝ^n | diffQuot n s v p ≠ 0} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hvab : v a ≠ v b :=
      hsep a (Metric.ball_subset_ball hρr ha) b (Metric.ball_subset_ball hρr hb)
    have hab : a ≠ b := by
      rintro rfl
      exact hvab rfl
    have hpos : (0 : ℝ) < ‖a - b‖ := by simpa [sub_eq_zero] using hab
    have hden : ‖a - b‖ ^ ((n : ℝ) / (2 : ℝ≥0∞).toReal + s) ≠ 0 := by positivity
    intro hcon
    rw [diffQuot_apply_real, div_eq_zero_iff] at hcon
    rcases hcon with h | h
    · exact hvab (sub_eq_zero.mp h)
    · exact hden h
  have hz := measure_mono_null hsub hnull
  rw [Measure.prod_prod, Measure.restrict_apply' hΩ.measurableSet,
    Measure.restrict_apply' hΩ.measurableSet] at hz
  rw [Set.inter_eq_self_of_subset_left hbx,
    Set.inter_eq_self_of_subset_left hby] at hz
  exact (mul_ne_zero (Metric.measure_ball_pos volume x hρ0).ne'
    (Metric.measure_ball_pos volume y hρ0).ne') hz

/-- A continuous real function on `ℝ^n` that is not constant has strictly positive
Gagliardo seminorm on `ℝ^n`, for every order `s`. -/
theorem gagliardoSq_univ_pos {v : ℝ^n → ℝ} (hv : Continuous v)
    (hne : ∃ x y, v x ≠ v y) :
    0 < gagliardoSq n s Set.univ v := by
  obtain ⟨x, y, hxy⟩ := hne
  exact gagliardoSq_pos_of_isOpen isOpen_univ hv (Set.mem_univ x) (Set.mem_univ y) hxy

end SobolevSpace.Fractional
