/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothFamily
public import PDE.Analysis.ODE.Flow.Variation
import PDE.Analysis.ODE.Flow.Estimates

/-!
# Higher regularity of flows of fields smooth in space and continuous in time

For a linear equation `y' = A(r, p) y + B(r, p)` with initial value `y₀ p` at a base time `t`,
whose coefficients are smooth families of order `m` in the parameter `p`
(`PDE.Analysis.IsSmoothFamilyOn`) and only continuous in the time `r`, the solution
`linearFlowOn A B a b s t y₀ p` is a smooth family of order `m` in `p`
(`isSmoothFamilyOn_linearFlowOn`). The induction differentiates once: the derivative in `p`
solves the linear equation `z' = A z + (D_p A) y + D_p B` with coefficients of order `m - 1`
(`hasFDerivAt_linearFlowOn`, from `hasFDerivAt_of_parametric`).

For a field `v` that is `C¹` with bounded derivative and a smooth family of order `m` in space,
the flow maps form a smooth family of order `m` (`isSmoothFamilyOn_flowOn`): the first variation
solves a linear equation whose coefficient `Dv(r, flowOn v a b r t x)` is a composition of smooth
families of order `m - 1`. In particular every flow map is `C^m` (`contDiff_flowOn_of_family`),
with all its spatial derivatives jointly continuous in the final time and the point.

## Main definitions

* `linearFlowOn`: the solution at time `s` of `y' = A(r, p) y + B(r, p)` on `[a, b]` with the
  value `y₀ p` at time `t`.

## Main results

* `norm_linearFlowOn_sub_le`: solutions at two parameters differ by at most a Grönwall bound in
  the differences of the initial values and of the coefficients.
* `continuousOn_linearFlowOn`: for a continuous initial value the solution is jointly continuous
  in the time and the parameter.
* `hasFDerivAt_linearFlowOn`: for `C¹` coefficients and initial value the solution is
  differentiable in the parameter, and its derivative solves `z' = A z + (D_p A) y + D_p B`.
* `isSmoothFamilyOn_linearFlowOn`: coefficients that are smooth families of order `m` with
  `‖A‖ ≤ K` and a `C^m` initial value give solutions forming a smooth family of order `m`.
* `variationOn_eq_linearFlowOn`: the first variation solves `J' = Dv(r, flowOn v a b r t x) ∘ J`.
* `IsC1FieldOn.isSmoothFamilyOn_flowOn`: the flow maps of a `C¹` field with bounded derivative
  that is a smooth family of order `m` form a smooth family of order `m`.
* `IsC1FieldOn.contDiff_flowOn_of_family`: these flow maps are `C^m`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric ContinuousLinearMap
open scoped NNReal Topology

namespace PDE.Analysis.ODE

universe u

variable {P Y : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The solution at time `s` of the linear equation `y' = A(r, p) y + B(r, p)` on `[a, b]` with
the value `y₀ p` at time `t`. -/
def linearFlowOn (A : ℝ → P → Y →L[ℝ] Y) (B : ℝ → P → Y) (a b s t : ℝ) (y₀ : P → Y) (p : P) :
    Y :=
  flowOn (fun r y ↦ A r p y + B r p) a b s t (y₀ p)

variable {A : ℝ → P → Y →L[ℝ] Y} {B : ℝ → P → Y} {a b t : ℝ} {K : ℝ≥0} {y₀ : P → Y}

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
/-- The linear field with jointly continuous coefficients bounded by `K` is a Lipschitz field. -/
theorem isLipschitzFieldOn_linear (hA : ContinuousOn (fun q : ℝ × P ↦ A q.1 q.2) (Icc a b ×ˢ univ))
    (hB : ContinuousOn (fun q : ℝ × P ↦ B q.1 q.2) (Icc a b ×ˢ univ))
    (hK : ∀ r ∈ Icc a b, ∀ p, ‖A r p‖ ≤ K) (p : P) :
    IsLipschitzFieldOn (fun r y ↦ A r p y + B r p) a b K := by
  have hmaps : MapsTo (fun q : ℝ × Y ↦ (q.1, p)) (Icc a b ×ˢ univ) (Icc a b ×ˢ univ) :=
    fun q hq ↦ ⟨hq.1, mem_univ _⟩
  refine ⟨?_, fun r hr ↦ LipschitzWith.of_dist_le_mul fun y y' ↦ ?_⟩
  · exact ((hA.comp (continuousOn_fst.prodMk continuousOn_const) hmaps).clm_apply
      continuousOn_snd).add (hB.comp (continuousOn_fst.prodMk continuousOn_const) hmaps)
  · rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub]
    exact ((A r p).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK r hr p) (norm_nonneg _))

section Linear

variable (hA : ContinuousOn (fun q : ℝ × P ↦ A q.1 q.2) (Icc a b ×ˢ univ))
  (hB : ContinuousOn (fun q : ℝ × P ↦ B q.1 q.2) (Icc a b ×ˢ univ))
  (hK : ∀ r ∈ Icc a b, ∀ p, ‖A r p‖ ≤ K) (ht : t ∈ Icc a b)
include hA hB hK ht

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The solution starts from the initial value. -/
theorem linearFlowOn_self (p : P) : linearFlowOn A B a b t t y₀ p = y₀ p :=
  (isLipschitzFieldOn_linear hA hB hK p).flowOn_self ht _

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The solution solves the linear equation. -/
theorem hasDerivWithinAt_linearFlowOn {s : ℝ} (hs : s ∈ Icc a b) (p : P) :
    HasDerivWithinAt (fun r ↦ linearFlowOn A B a b r t y₀ p)
      (A s p (linearFlowOn A B a b s t y₀ p) + B s p) (Icc a b) s :=
  (isLipschitzFieldOn_linear hA hB hK p).hasDerivWithinAt_flowOn hs ht _

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The solution is continuous in time. -/
theorem continuousOn_linearFlowOn_time (p : P) :
    ContinuousOn (fun r ↦ linearFlowOn A B a b r t y₀ p) (Icc a b) :=
  (isLipschitzFieldOn_linear hA hB hK p).continuousOn_flowOn_time ht _

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- **Comparison of two parameters.** With `‖A r p₀ - A r p‖ ≤ ε₁`, `‖B r p₀ - B r p‖ ≤ ε₂` and
`‖y(r, p₀)‖ ≤ M` on `[a, b]`, the solutions differ by at most
`gronwallBound ‖y₀ p₀ - y₀ p‖ K (ε₁ M + ε₂) |s - t|`. -/
theorem norm_linearFlowOn_sub_le {p₀ p : P} {ε₁ ε₂ M : ℝ}
    (hA₁ : ∀ r ∈ Icc a b, ‖A r p₀ - A r p‖ ≤ ε₁) (hB₂ : ∀ r ∈ Icc a b, ‖B r p₀ - B r p‖ ≤ ε₂)
    (hM : ∀ r ∈ Icc a b, ‖linearFlowOn A B a b r t y₀ p₀‖ ≤ M) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖linearFlowOn A B a b s t y₀ p₀ - linearFlowOn A B a b s t y₀ p‖ ≤
      gronwallBound ‖y₀ p₀ - y₀ p‖ K (ε₁ * M + ε₂) |s - t| := by
  have h := norm_sub_le_of_hasDerivWithinAt_affine (M₁ := fun r ↦ linearFlowOn A B a b r t y₀ p₀)
    (M₂ := fun r ↦ linearFlowOn A B a b r t y₀ p) (A₁ := fun r ↦ A r p₀) (A₂ := fun r ↦ A r p)
    (B₁ := fun r ↦ B r p₀) (B₂ := fun r ↦ B r p) ht
    (fun r hr ↦ hasDerivWithinAt_linearFlowOn hA hB hK ht hr p₀)
    (fun r hr ↦ hasDerivWithinAt_linearFlowOn hA hB hK ht hr p) (fun r hr ↦ hK r hr p) hA₁ hM
    hB₂ hs
  simpa only [linearFlowOn_self hA hB hK ht] using h

/-- **Joint continuity.** For a continuous initial value the solution is jointly continuous in the
time and the parameter. -/
theorem continuousOn_linearFlowOn (hy₀ : Continuous y₀) :
    ContinuousOn (fun q : ℝ × P ↦ linearFlowOn A B a b q.1 t y₀ q.2) (Icc a b ×ˢ univ) := by
  rintro ⟨s₀, p₀⟩ ⟨hs₀, -⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_linearFlowOn_time hA hB hK ht (y₀ := y₀) p₀)
  set M₀ := max M 0
  have hab : 0 ≤ b - a := sub_nonneg.mpr (hs₀.1.trans hs₀.2)
  set c : ℝ := (1 + (M₀ + 1) * (b - a)) * Real.exp (K * (b - a))
  have hc : 0 ≤ c := by positivity
  set η : ℝ := ε / (2 * (c + 1))
  have hη : 0 < η := by positivity
  have hcη : c * η < ε / 2 := by
    have : c * η = ε / 2 * (c / (c + 1)) := by
      simp only [η]; field_simp
    rw [this]
    have : c / (c + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    nlinarith
  obtain ⟨δA, hδA, hAc⟩ := exists_forall_dist_lt_of_continuousOn (G := A) hA
    (c := fun _ ↦ p₀) continuousOn_const hη
  obtain ⟨δB, hδB, hBc⟩ := exists_forall_dist_lt_of_continuousOn (G := B) hB
    (c := fun _ ↦ p₀) continuousOn_const hη
  obtain ⟨δ₀, hδ₀, hy₀c⟩ := Metric.continuous_iff.mp hy₀ p₀ η hη
  obtain ⟨δt, hδt, htc⟩ := Metric.continuousWithinAt_iff.mp
    (continuousOn_linearFlowOn_time hA hB hK ht (y₀ := y₀) p₀ s₀ hs₀) (ε / 2) (half_pos hε)
  refine ⟨min (min δA δB) (min δ₀ δt), by positivity, fun {q} hq hqd ↦ ?_⟩
  obtain ⟨s, p⟩ := q
  have hs : s ∈ Icc a b := hq.1
  have hd : dist (s, p) (s₀, p₀) < min (min δA δB) (min δ₀ δt) := hqd
  rw [Prod.dist_eq, max_lt_iff] at hd
  have hp : dist p p₀ < min (min δA δB) (min δ₀ δt) := hd.2
  have hst : dist s s₀ < δt := hd.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpA : dist p p₀ < δA := hp.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hpB : dist p p₀ < δB := hp.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hp₀ : dist p p₀ < δ₀ := hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hA₁ : ∀ r ∈ Icc a b, ‖A r p₀ - A r p‖ ≤ η := fun r hr ↦ by
    rw [← dist_eq_norm, dist_comm]; exact (hAc r hr p hpA).le
  have hB₂ : ∀ r ∈ Icc a b, ‖B r p₀ - B r p‖ ≤ η := fun r hr ↦ by
    rw [← dist_eq_norm, dist_comm]; exact (hBc r hr p hpB).le
  have hM' : ∀ r ∈ Icc a b, ‖linearFlowOn A B a b r t y₀ p₀‖ ≤ M₀ :=
    fun r hr ↦ (hM r hr).trans (le_max_left _ _)
  have hcomp := norm_linearFlowOn_sub_le hA hB hK ht hA₁ hB₂ hM' hs
  have hy₀p : ‖y₀ p₀ - y₀ p‖ ≤ η := by
    rw [← dist_eq_norm, dist_comm]; exact (hy₀c p hp₀).le
  have hst' : |s - t| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hgr : gronwallBound ‖y₀ p₀ - y₀ p‖ K (η * M₀ + η) |s - t| ≤ c * η := by
    have hM₀ : 0 ≤ M₀ := le_max_right _ _
    calc gronwallBound ‖y₀ p₀ - y₀ p‖ K (η * M₀ + η) |s - t|
        ≤ (‖y₀ p₀ - y₀ p‖ + (η * M₀ + η) * |s - t|) * Real.exp (K * |s - t|) :=
          gronwallBound_le_add_mul_exp K.coe_nonneg (by positivity)
      _ ≤ (η + (η * M₀ + η) * (b - a)) * Real.exp (K * (b - a)) := by
          gcongr
      _ = c * η := by simp only [c]; ring
  have h1 : dist (linearFlowOn A B a b s t y₀ p) (linearFlowOn A B a b s t y₀ p₀) < ε / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact (hcomp.trans hgr).trans_lt hcη
  have h2 : dist (linearFlowOn A B a b s t y₀ p₀) (linearFlowOn A B a b s₀ t y₀ p₀) < ε / 2 :=
    htc hs hst
  calc dist (linearFlowOn A B a b s t y₀ p) (linearFlowOn A B a b s₀ t y₀ p₀)
      ≤ dist (linearFlowOn A B a b s t y₀ p) (linearFlowOn A B a b s t y₀ p₀) +
        dist (linearFlowOn A B a b s t y₀ p₀) (linearFlowOn A B a b s₀ t y₀ p₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

end Linear

/-! ### The derivative in the parameter -/

/-- The flip `T ↦ (y ↦ (h ↦ T h y))` as a continuous linear map. -/
def flipCLM (P Y : Type u) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] : (P →L[ℝ] Y →L[ℝ] Y) →L[ℝ] Y →L[ℝ] P →L[ℝ] Y :=
  ((flipₗᵢ ℝ P Y Y).toContinuousLinearEquiv : (P →L[ℝ] Y →L[ℝ] Y) →L[ℝ] Y →L[ℝ] P →L[ℝ] Y)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
/-- `flipCLM P Y T y` is the flip of `T` applied to `y`. -/
@[simp]
theorem flipCLM_apply (T : P →L[ℝ] Y →L[ℝ] Y) (y : Y) : flipCLM P Y T y = T.flip y := by
  simp [flipCLM]

/-- The coefficient `z ↦ A(r, p) ∘ z` of the equation of the derivative in the parameter. -/
def linearFlowDerivCoeff (A : ℝ → P → Y →L[ℝ] Y) (r : ℝ) (p : P) :
    (P →L[ℝ] Y) →L[ℝ] P →L[ℝ] Y :=
  compL ℝ P Y Y (A r p)

/-- The forcing `(D_p A) y + D_p B` of the equation of the derivative in the parameter. -/
def linearFlowDerivForcing (A : ℝ → P → Y →L[ℝ] Y) (B : ℝ → P → Y) (a b t : ℝ) (y₀ : P → Y)
    (r : ℝ) (p : P) : P →L[ℝ] Y :=
  flipCLM P Y (fderiv ℝ (A r) p) (linearFlowOn A B a b r t y₀ p) + fderiv ℝ (B r) p

section Derivative

variable (hA : IsSmoothFamilyOn 1 A (Icc a b)) (hB : IsSmoothFamilyOn 1 B (Icc a b))
  (hK : ∀ r ∈ Icc a b, ∀ p, ‖A r p‖ ≤ K) (ht : t ∈ Icc a b) (hy₀ : ContDiff ℝ 1 y₀)
include hA hB hK ht hy₀

/-- **Lipschitz dependence on the parameter** near every parameter. -/
theorem exists_forall_norm_linearFlowOn_sub_le (p₀ : P) :
    ∃ C : ℝ, ∀ p ∈ ball p₀ 1, ∀ r ∈ Icc a b,
      ‖linearFlowOn A B a b r t y₀ p - linearFlowOn A B a b r t y₀ p₀‖ ≤ C * ‖p - p₀‖ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, isSmoothFamilyOn_succ_iff] at hA hB
  have hAc := hA.2.1
  have hBc := hB.2.1
  have hDA := isSmoothFamilyOn_zero_iff.mp hA.2.2
  have hDB := isSmoothFamilyOn_zero_iff.mp hB.2.2
  set S : Set (ℝ × P) := Icc a b ×ˢ closedBall p₀ 1
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hSsub : S ⊆ Icc a b ×ˢ univ := prod_mono subset_rfl (subset_univ _)
  obtain ⟨LA, hLA⟩ := hS.exists_bound_of_continuousOn (hDA.mono hSsub)
  obtain ⟨LB, hLB⟩ := hS.exists_bound_of_continuousOn (hDB.mono hSsub)
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall p₀ 1).exists_bound_of_continuousOn
    (hy₀.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_linearFlowOn_time hAc hBc hK ht (y₀ := y₀) p₀)
  set LA' := max LA 0
  set LB' := max LB 0
  set L₀' := max L₀ 0
  set M' := max M 0
  refine ⟨(L₀' + (LA' * M' + LB') * (b - a)) * Real.exp (K * (b - a)), fun p hp r hr ↦ ?_⟩
  have hab : 0 ≤ b - a := sub_nonneg.mpr (ht.1.trans ht.2)
  have hconv := convex_closedBall p₀ 1
  have hp' : p ∈ closedBall p₀ 1 := ball_subset_closedBall hp
  have hp₀ : p₀ ∈ closedBall p₀ 1 := mem_closedBall_self zero_le_one
  have hA₁ : ∀ r ∈ Icc a b, ‖A r p₀ - A r p‖ ≤ LA' * ‖p - p₀‖ := fun r hr ↦ by
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := A r) (C := LA')
      (fun q _ ↦ (hA.1 r hr q)) (fun q hq ↦ (hLA (r, q) ⟨hr, hq⟩).trans (le_max_left _ _))
      hp' hp₀
    rwa [norm_sub_rev p₀] at this
  have hB₂ : ∀ r ∈ Icc a b, ‖B r p₀ - B r p‖ ≤ LB' * ‖p - p₀‖ := fun r hr ↦ by
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := B r) (C := LB')
      (fun q _ ↦ (hB.1 r hr q)) (fun q hq ↦ (hLB (r, q) ⟨hr, hq⟩).trans (le_max_left _ _))
      hp' hp₀
    rwa [norm_sub_rev p₀] at this
  have hy₀p : ‖y₀ p₀ - y₀ p‖ ≤ L₀' * ‖p - p₀‖ := by
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := y₀) (C := L₀')
      (fun q _ ↦ (hy₀.differentiable one_ne_zero q))
      (fun q hq ↦ (hL₀ q hq).trans (le_max_left _ _)) hp' hp₀
    rwa [norm_sub_rev p₀] at this
  have hM' : ∀ r ∈ Icc a b, ‖linearFlowOn A B a b r t y₀ p₀‖ ≤ M' :=
    fun r hr ↦ (hM r hr).trans (le_max_left _ _)
  have hcomp := norm_linearFlowOn_sub_le hAc hBc hK ht hA₁ hB₂ hM' hr
  have hrt : |r - t| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2, ht.1, ht.2]
  have hLA0 : 0 ≤ LA' := le_max_right _ _
  have hLB0 : 0 ≤ LB' := le_max_right _ _
  have hL00 : 0 ≤ L₀' := le_max_right _ _
  have hM0 : 0 ≤ M' := le_max_right _ _
  rw [norm_sub_rev]
  calc ‖linearFlowOn A B a b r t y₀ p₀ - linearFlowOn A B a b r t y₀ p‖
      ≤ gronwallBound ‖y₀ p₀ - y₀ p‖ K (LA' * ‖p - p₀‖ * M' + LB' * ‖p - p₀‖) |r - t| := hcomp
    _ ≤ (‖y₀ p₀ - y₀ p‖ + (LA' * ‖p - p₀‖ * M' + LB' * ‖p - p₀‖) * |r - t|) *
          Real.exp (K * |r - t|) := gronwallBound_le_add_mul_exp K.coe_nonneg (by positivity)
    _ ≤ (L₀' * ‖p - p₀‖ + (LA' * ‖p - p₀‖ * M' + LB' * ‖p - p₀‖) * (b - a)) *
          Real.exp (K * (b - a)) := by gcongr
    _ = (L₀' + (LA' * M' + LB') * (b - a)) * Real.exp (K * (b - a)) * ‖p - p₀‖ := by ring

/-- The coefficients of the equation of the derivative are jointly continuous and bounded. -/
theorem continuousOn_linearFlowDeriv :
    ContinuousOn (fun q : ℝ × P ↦ linearFlowDerivCoeff A q.1 q.2) (Icc a b ×ˢ univ) ∧
      ContinuousOn (fun q : ℝ × P ↦ linearFlowDerivForcing A B a b t y₀ q.1 q.2)
        (Icc a b ×ˢ univ) ∧
      ∀ r ∈ Icc a b, ∀ p, ‖linearFlowDerivCoeff A r p‖ ≤ K := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, isSmoothFamilyOn_succ_iff] at hA hB
  have hDA := isSmoothFamilyOn_zero_iff.mp hA.2.2
  have hDB := isSmoothFamilyOn_zero_iff.mp hB.2.2
  refine ⟨(compL ℝ P Y Y).continuous.comp_continuousOn hA.2.1, ?_, fun r hr p ↦
    (norm_compL_apply_le (E := P) (A r p)).trans (hK r hr p)⟩
  exact (((flipCLM P Y).continuous.comp_continuousOn hDA).clm_apply
    (continuousOn_linearFlowOn hA.2.1 hB.2.1 hK ht hy₀.continuous)).add hDB

/-- **The derivative in the parameter.** For coefficients and initial value of class `C¹` the
solution is differentiable in the parameter, and its derivative is the solution of
`z' = A z + (D_p A) y + D_p B` with `z = D y₀` at the base time. -/
theorem hasFDerivAt_linearFlowOn {s : ℝ} (hs : s ∈ Icc a b) (p₀ : P) :
    HasFDerivAt (fun p ↦ linearFlowOn A B a b s t y₀ p)
      (linearFlowOn (linearFlowDerivCoeff A) (linearFlowDerivForcing A B a b t y₀) a b s t
        (fun p ↦ fderiv ℝ y₀ p) p₀) p₀ := by
  obtain ⟨hA'c, hB'c, hK'⟩ := continuousOn_linearFlowDeriv hA hB hK ht hy₀
  obtain ⟨C, hC⟩ := exists_forall_norm_linearFlowOn_sub_le hA hB hK ht hy₀ p₀
  rw [show (1 : ℕ) = 0 + 1 from rfl, isSmoothFamilyOn_succ_iff] at hA hB
  have hAc := hA.2.1
  have hBc := hB.2.1
  have hDA := isSmoothFamilyOn_zero_iff.mp hA.2.2
  have hDB := isSmoothFamilyOn_zero_iff.mp hB.2.2
  set Df : ℝ → Y → P → (Y × P) →L[ℝ] Y := fun r z p ↦
    (A r p).comp (fst ℝ Y P) + ((fderiv ℝ (A r) p).comp (snd ℝ Y P)).flip z +
      (fderiv ℝ (B r) p).comp (snd ℝ Y P) with hDf_def
  have hinl (r : ℝ) (z : Y) (p : P) : (Df r z p).comp (inl ℝ Y P) = A r p := by
    ext w; simp [Df]
  have hinr (r : ℝ) (z : Y) (p : P) :
      (Df r z p).comp (inr ℝ Y P) = flipCLM P Y (fderiv ℝ (A r) p) z + fderiv ℝ (B r) p := by
    ext h; simp [Df]
  have hmaps : MapsTo (fun q : ℝ × Y × P ↦ (q.1, q.2.2)) (Icc a b ×ˢ univ) (Icc a b ×ˢ univ) :=
    fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hc₂ : ContinuousOn (fun q : ℝ × Y × P ↦ (q.1, q.2.2)) (Icc a b ×ˢ univ) :=
    continuousOn_fst.prodMk (continuous_snd.comp continuous_snd).continuousOn
  have hDfc : ContinuousOn (fun q : ℝ × Y × P ↦ Df q.1 q.2.1 q.2.2) (Icc a b ×ˢ univ) := by
    have h1 : ContinuousOn (fun q : ℝ × Y × P ↦ (A q.1 q.2.2).comp (fst ℝ Y P))
        (Icc a b ×ˢ univ) :=
      (hAc.comp hc₂ hmaps).clm_comp (continuousOn_const (c := fst ℝ Y P))
    have h2 : ContinuousOn
        (fun q : ℝ × Y × P ↦ ((fderiv ℝ (A q.1) q.2.2).comp (snd ℝ Y P)).flip q.2.1)
        (Icc a b ×ˢ univ) := by
      have := (((flipₗᵢ ℝ (Y × P) Y Y).continuous.comp_continuousOn
        ((hDA.comp hc₂ hmaps).clm_comp (continuousOn_const (c := snd ℝ Y P)))).clm_apply
          (continuous_fst.comp continuous_snd).continuousOn)
      simpa using this
    have h3 : ContinuousOn (fun q : ℝ × Y × P ↦ (fderiv ℝ (B q.1) q.2.2).comp (snd ℝ Y P))
        (Icc a b ×ˢ univ) :=
      (hDB.comp hc₂ hmaps).clm_comp (continuousOn_const (c := snd ℝ Y P))
    exact (h1.add h2).add h3
  have hf (r : ℝ) (hr : r ∈ Icc a b) (z : Y) (p : P) :
      HasFDerivAt (fun q : Y × P ↦ A r q.2 q.1 + B r q.2) (Df r z p) (z, p) := by
    have hcA : HasFDerivAt (fun q : Y × P ↦ A r q.2) ((fderiv ℝ (A r) p).comp (snd ℝ Y P))
        (z, p) := (hA.1 r hr p).hasFDerivAt.comp (z, p) hasFDerivAt_snd
    have hcB : HasFDerivAt (fun q : Y × P ↦ B r q.2) ((fderiv ℝ (B r) p).comp (snd ℝ Y P))
        (z, p) := (hB.1 r hr p).hasFDerivAt.comp (z, p) hasFDerivAt_snd
    exact (hcA.clm_apply hasFDerivAt_fst).add hcB
  have hy₀eq : (fun p ↦ linearFlowOn A B a b t t y₀ p) = y₀ :=
    funext (linearFlowOn_self hAc hBc hK ht)
  refine hasFDerivAt_of_parametric (f := fun r z p ↦ A r p z + B r p) (Df := Df)
    (y := fun p r ↦ linearFlowOn A B a b r t y₀ p)
    (Z := fun r ↦ linearFlowOn (linearFlowDerivCoeff A) (linearFlowDerivForcing A B a b t y₀) a b r
      t (fun p ↦ fderiv ℝ y₀ p) p₀) (Dy₀ := fderiv ℝ y₀ p₀) (ρ := 1) (C := C)
    (K := K) ht one_pos hDfc hf (fun r hr ↦ by rw [hinl]; exact hK r hr p₀)
    (fun p _ r hr ↦ hasDerivWithinAt_linearFlowOn hAc hBc hK ht hr p)
    (by rw [hy₀eq]; exact (hy₀.differentiable one_ne_zero p₀).hasFDerivAt) hC
    (fun r hr ↦ ?_) (linearFlowOn_self hA'c hB'c hK' ht (y₀ := fun p ↦ fderiv ℝ y₀ p) p₀) hs
  have h := hasDerivWithinAt_linearFlowOn hA'c hB'c hK' ht (y₀ := fun p ↦ fderiv ℝ y₀ p) hr p₀
  convert h using 1
  rw [hinl, hinr]
  rfl

end Derivative

/-- **Smooth dependence on the parameter.** If the coefficients `A`, `B` are smooth families of
order `m` in the parameter on `[a, b]`, `‖A‖ ≤ K`, and the initial value is `C^m`, then the
solutions of `y' = A(r, p) y + B(r, p)` form a smooth family of order `m` in the parameter. -/
theorem isSmoothFamilyOn_linearFlowOn {m : ℕ} (hA : IsSmoothFamilyOn m A (Icc a b))
    (hB : IsSmoothFamilyOn m B (Icc a b)) (hK : ∀ r ∈ Icc a b, ∀ p, ‖A r p‖ ≤ K)
    (ht : t ∈ Icc a b) (hy₀ : ContDiff ℝ m y₀) :
    IsSmoothFamilyOn m (fun s p ↦ linearFlowOn A B a b s t y₀ p) (Icc a b) := by
  induction m generalizing Y with
  | zero =>
    exact isSmoothFamilyOn_zero_iff.mpr (continuousOn_linearFlowOn
      (isSmoothFamilyOn_zero_iff.mp hA) (isSmoothFamilyOn_zero_iff.mp hB) hK ht
      (contDiff_zero.mp (by exact_mod_cast hy₀)))
  | succ m ih =>
    have hA1 : IsSmoothFamilyOn 1 A (Icc a b) := hA.mono (by omega)
    have hB1 : IsSmoothFamilyOn 1 B (Icc a b) := hB.mono (by omega)
    have hy₀1 : ContDiff ℝ 1 y₀ := hy₀.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
    have hym : IsSmoothFamilyOn m (fun s p ↦ linearFlowOn A B a b s t y₀ p) (Icc a b) :=
      ih (hA.mono (Nat.le_succ m)) (hB.mono (Nat.le_succ m)) hK
        (hy₀.of_le (by exact_mod_cast Nat.le_succ m))
    have hDA := (isSmoothFamilyOn_succ_iff.mp hA).2.2
    have hDB := (isSmoothFamilyOn_succ_iff.mp hB).2.2
    have hA' : IsSmoothFamilyOn m (linearFlowDerivCoeff A) (Icc a b) := by
      have := IsSmoothFamilyOn.clm_comp (Q := Y →L[ℝ] Y) (R := (P →L[ℝ] Y) →L[ℝ] P →L[ℝ] Y)
        (compL ℝ P Y Y) (hA.mono (Nat.le_succ m))
      exact this
    have hB' : IsSmoothFamilyOn m (linearFlowDerivForcing A B a b t y₀) (Icc a b) := by
      have := (IsSmoothFamilyOn.bilinear (flipCLM P Y) hDA hym).add hDB
      exact this
    have hK' := (continuousOn_linearFlowDeriv hA1 hB1 hK ht hy₀1).2.2
    have hcd : ContDiff ℝ ((m : WithTop ℕ∞) + 1) y₀ := by exact_mod_cast hy₀
    have hy₀' : ContDiff ℝ m (fun p ↦ fderiv ℝ y₀ p) := (contDiff_succ_iff_fderiv.mp hcd).2.2
    have hz := ih hA' hB' hK' hy₀'
    rw [isSmoothFamilyOn_succ_iff]
    refine ⟨fun s hs p ↦ (hasFDerivAt_linearFlowOn hA1 hB1 hK ht hy₀1 hs p).differentiableAt,
      continuousOn_linearFlowOn (isSmoothFamilyOn_zero_iff.mp (hA.mono (Nat.zero_le _)))
        (isSmoothFamilyOn_zero_iff.mp (hB.mono (Nat.zero_le _))) hK ht hy₀1.continuous,
      hz.congr fun s hs ↦ ?_⟩
    funext p
    exact ((hasFDerivAt_linearFlowOn hA1 hB1 hK ht hy₀1 hs p).fderiv).symm

/-! ### Flows -/

section Flow

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- The first variation solves the linear equation `J' = Dv(r, flowOn v a b r t x) ∘ J`. -/
theorem variationOn_eq_linearFlowOn (s t : ℝ) (x : E) :
    variationOn v Dv a b s t x =
      linearFlowOn (fun r x ↦ compL ℝ E E E (Dv r (flowOn v a b r t x))) (fun _ _ ↦ 0) a b s t
        (fun _ ↦ ContinuousLinearMap.id ℝ E) x := by
  simp only [variationOn, linearFlowOn, add_zero, compL_apply]

/-- **Smooth flows.** If the field `v` is `C¹` with bounded derivative and a smooth family of
order `m` in space on `[a, b]`, then for every base time `t ∈ [a, b]` the flow maps
`flowOn v a b s t` form a smooth family of order `m`: they are `C^m` and their spatial
derivatives of order at most `m` are jointly continuous in the final time and the point. -/
theorem IsC1FieldOn.isSmoothFamilyOn_flowOn (hv : IsC1FieldOn v Dv a b K) {m : ℕ}
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b) :
    IsSmoothFamilyOn m (fun s x ↦ flowOn v a b s t x) (Icc a b) := by
  induction m with
  | zero =>
    refine isSmoothFamilyOn_zero_iff.mpr ?_
    exact hv.isLipschitzFieldOn.continuousOn_flowOn.comp
      (continuousOn_fst.prodMk (continuousOn_const.prodMk continuousOn_snd))
      fun q hq ↦ ⟨hq.1, ht, mem_univ _⟩
  | succ m ih =>
    have hflow := ih (hsm.mono (Nat.le_succ m))
    have hDv : IsSmoothFamilyOn m Dv (Icc a b) :=
      (isSmoothFamilyOn_succ_iff.mp hsm).2.2.congr fun r hr ↦
        funext fun x ↦ (hv.hasFDerivAt r hr x).fderiv
    have hA : IsSmoothFamilyOn m (fun r x ↦ compL ℝ E E E (Dv r (flowOn v a b r t x)))
        (Icc a b) :=
      IsSmoothFamilyOn.clm_comp (Q := E →L[ℝ] E) (R := (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E)
        (compL ℝ E E E) (hDv.comp hflow)
    have hB : IsSmoothFamilyOn m (fun (_ : ℝ) (_ : E) ↦ (0 : E →L[ℝ] E)) (Icc a b) :=
      isSmoothFamilyOn_const contDiff_const
    have hK : ∀ r ∈ Icc a b, ∀ x, ‖compL ℝ E E E (Dv r (flowOn v a b r t x))‖ ≤ K :=
      fun r hr x ↦ (norm_compL_apply_le (E := E) _).trans (hv.norm_le r hr _)
    have hJ := isSmoothFamilyOn_linearFlowOn hA hB hK ht
      (contDiff_const (c := ContinuousLinearMap.id ℝ E))
    rw [isSmoothFamilyOn_succ_iff]
    refine ⟨fun s hs x ↦ (hv.hasFDerivAt_flowOn hs ht x).differentiableAt,
      isSmoothFamilyOn_zero_iff.mp (hflow.mono (Nat.zero_le _)), hJ.congr fun s hs ↦ ?_⟩
    funext x
    rw [(hv.hasFDerivAt_flowOn hs ht x).fderiv, variationOn_eq_linearFlowOn]

/-- The flow maps of a `C¹` field that is a smooth family of order `m` are `C^m`. -/
theorem IsC1FieldOn.contDiff_flowOn_of_family (hv : IsC1FieldOn v Dv a b K) {m : ℕ}
    (hsm : IsSmoothFamilyOn m v (Icc a b)) {s : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ContDiff ℝ m (flowOn v a b s t) :=
  (hv.isSmoothFamilyOn_flowOn hsm ht).contDiff hs

end Flow

end PDE.Analysis.ODE
