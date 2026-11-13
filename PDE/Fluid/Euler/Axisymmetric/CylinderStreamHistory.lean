/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamTime
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import PDE.FDeriv.SpaceTime

/-!
# Stream functions of vorticity histories

Let `Ω(t, s, z)` be a vorticity profile, smooth on an open set `V ⊇ [0, T) × ℝ²` and `L`-periodic in
`z`. The stream profiles `Ψ(t, s, z)` of its slices are smooth on an open set `W ⊇ [0, T) × ℝ²`. If
`Ω` is also odd in `z`, then at the times of `[0, T)` the profile `Ψ` solves the reduced stream
equation `Ω = -(8 Ψ_s + 4 s Ψ_ss + Ψ_zz)` on `0 < s < 1`, vanishes at the wall `s = 1` and is
`L`-periodic and odd in `z`, and `φ(r, z) = r Ψ(t, r², z)` is the stream function in the cylinder of
the angular vorticity `ω^θ(r, z) = r Ω(t, r², z)`, `C¹` at the wall.

## Main definitions

* `historyStream L Ω`: the stream profile `Ψ(t, s, z)` of the slices of a profile `Ω(t, s, z)`.

## Main results

* `modeTerm_congr`, `streamProfile_congr`: the stream profile only reads the source on the collar
  `modeCollar L × ℝ`.
* `exists_isOpen_contDiffOn_streamProfile`: joint smoothness on an open set containing
  `[0, T) × ℝ²`.
* `historyStream_equation`, `historyStream_wall`, `historyStream_periodic`,
  `isOddUnderCoordinateReflection_historyStream`: the stream problem for each slice.
* `exists_historyStream`: the smoothness and the stream problem together.
* `isStreamFunction_ofProfiles_historyStream`, `hasWallRegularityOn_ofProfiles_historyStream`: the
  stream function in the cylinder and its regularity at the wall.

## How it works

The stream profile of a source `Ω(s, z)` only reads `Ω` on `modeCollar L × ℝ`
(`streamProfile_congr`): outside the collar every cut-off mode vanishes, and the mode solutions on
the collar only use the source on the collar. For each `t₀ ∈ [0, T)` the tube lemma gives `ε > 0`
such that `V` contains the points with `|t - t₀| < ε`, `s` near the collar and `z ∈ [0, L]`, and by
periodicity `Ω` is smooth at all points with such `t` and `s`. We multiply `Ω` by a bump in `t`
around `t₀` and a bump in `s` equal to one on the collar. The product is smooth on all of `ℝ³`, so
its stream profiles are jointly smooth (`contDiff_streamProfile_slices`), and for `|t - t₀| < ε/2`
the bumps do not change them. The union of these slabs is the open set `W` of
`exists_isOpen_contDiffOn_streamProfile`.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries AxisymmetricFlow
open PDE.Common (timeSpaceCons hasFDerivAt_timeSpaceCons_spatial)
open scoped Topology Real

set_option linter.missingDocs true

noncomputable section

/-! ### Dependence of the stream profile on the collar only -/

/-- The averaged source at a point `σ` of the collar only reads the source on the collar. -/
theorem modeAverage_congr {μ : ℝ} (hμ : 0 < μ) {F₁ F₂ : ℝ → ℝ}
    (h : EqOn F₁ F₂ (Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2))) {σ : ℝ}
    (hσ : σ ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) :
    modeAverage μ F₁ σ = modeAverage μ F₂ σ := by
  unfold modeAverage
  refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
  rw [uIcc_of_le zero_le_one] at hτ
  have hmem : σ * τ ∈ uIcc 0 σ := by
    rcases le_total 0 σ with h0 | h0
    · rw [uIcc_of_le h0]
      constructor <;> nlinarith [hτ.1, hτ.2]
    · rw [uIcc_of_ge h0]
      constructor <;> nlinarith [hτ.1, hτ.2]
  simp only [h (uIcc_subset_modeInterval hμ hσ hmem)]

/-- **The cut-off modes only read the source on the collar.** -/
theorem modeTerm_congr {μ : ℝ} (hμ : 0 < μ) {F₁ F₂ : ℝ → ℝ}
    (h : EqOn F₁ F₂ (Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2))) : modeTerm μ F₁ = modeTerm μ F₂ := by
  have hQ : ∀ σ ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), modeQuotient μ F₁ σ = modeQuotient μ F₂ σ :=
    fun σ hσ ↦ by simp only [modeQuotient, modeAverage_congr hμ h hσ]
  have hP : ∀ s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2),
      particularMode μ F₁ s = particularMode μ F₂ s := fun s hs ↦ by
    simp only [particularMode]
    congr 1
    exact intervalIntegral.integral_congr fun σ hσ ↦ hQ σ (uIcc_subset_modeInterval hμ hs hσ)
  have h1 : (1 : ℝ) ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2) := by
    have : 0 < 2 / μ ^ 2 := by positivity
    constructor
    · rw [neg_div]; linarith
    · linarith
  funext s
  by_cases hs : s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)
  · simp only [modeTerm, modeSolution, hP s hs, hP 1 h1]
  · simp [modeTerm, modeCutoff_of_notMem hμ hs]

/-- **The stream profile only reads the source on the collar** `modeCollar L × ℝ`. -/
theorem streamProfile_congr {L : ℝ} (hL : 0 < L) {G₁ G₂ : ℝ × ℝ → ℝ}
    (h : ∀ s ∈ modeCollar L, ∀ z, G₁ (s, z) = G₂ (s, z)) :
    streamProfile L G₁ = streamProfile L G₂ := by
  funext p
  unfold streamProfile
  congr 1
  funext k
  have hc : EqOn (coefficientMode L G₁ k) (coefficientMode L G₂ k)
      (Icc (-2 / modeFrequency L k ^ 2) (1 + 2 / modeFrequency L k ^ 2)) := by
    intro s hs
    simp only [coefficientMode]
    congr 1
    funext z
    exact h s (collar_subset_modeCollar k hs) z
  simp only [streamMode, modeTerm_congr (modeFrequency_pos hL k) hc]

/-! ### Vorticity profiles smooth near `[0, T) × ℝ²` -/

/-- The stream profile `Ψ(t, s, z)` of the slices `(s, z) ↦ Ω(t, s, z)` of a vorticity profile on
profile space. -/
def historyStream (L : ℝ) (Ω : ℝ^3 → ℝ) (q : ℝ^3) : ℝ :=
  streamProfile L (fun p ↦ Ω (profilePoint (q 0) p.1 p.2)) (WithLp.toLp 2 ![q 1, q 2])

/-- The profile chart `(t, (s, z)) ↦ (t, s, z)` is continuous. -/
theorem continuous_profilePoint_uncurry :
    Continuous fun x : ℝ × (ℝ × ℝ) ↦ profilePoint x.1 x.2.1 x.2.2 := by
  have h : (fun x : ℝ × (ℝ × ℝ) ↦ profilePoint x.1 x.2.1 x.2.2) = fun x ↦
      x.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        x.2.1 • EuclideanSpace.single (1 : Fin 3) 1 + x.2.2 • EuclideanSpace.single (2 : Fin 3) 1 :=
    funext fun x ↦ profilePoint_eq _ _ _
  rw [h]
  fun_prop

/-- The profile chart `(t, (s, z)) ↦ (t, s, z)` is smooth. -/
theorem contDiff_profilePoint_uncurry :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × (ℝ × ℝ) ↦ profilePoint x.1 x.2.1 x.2.2 := by
  have h : (fun x : ℝ × (ℝ × ℝ) ↦ profilePoint x.1 x.2.1 x.2.2) = fun x ↦
      x.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        x.2.1 • EuclideanSpace.single (1 : Fin 3) 1 + x.2.2 • EuclideanSpace.single (2 : Fin 3) 1 :=
    funext fun x ↦ profilePoint_eq _ _ _
  rw [h]
  exact ((contDiff_fst.smul contDiff_const).add ((contDiff_fst.comp contDiff_snd).smul
    contDiff_const)).add ((contDiff_snd.comp contDiff_snd).smul contDiff_const)

/-- A shift of the axial coordinate of a profile point. -/
theorem profilePoint_add_axial (t s z c : ℝ) :
    profilePoint t s (z + c) = profilePoint t s z + EuclideanSpace.single (2 : Fin 3) c := by
  ext i
  fin_cases i <;> simp [profilePoint]

/-- A function periodic along `v` is smooth at `q + n v` if it is smooth at `q`. -/
theorem contDiffAt_add_zsmul_of_periodic {Ω : ℝ^3 → ℝ} {v : ℝ^3}
    (hper : ∀ q, Ω (q + v) = Ω q) {q : ℝ^3} (h : ContDiffAt ℝ (⊤ : ℕ∞) Ω q) (n : ℤ) :
    ContDiffAt ℝ (⊤ : ℕ∞) Ω (q + n • v) := by
  have hP : Function.Periodic Ω v := hper
  have hfun : Ω = Ω ∘ fun y ↦ y - n • v := by
    funext y
    simp only [Function.comp_apply]
    have := hP.zsmul n (y - n • v)
    rw [sub_add_cancel] at this
    exact this
  rw [hfun]
  refine ContDiffAt.comp (q + n • v) ?_ (contDiffAt_id.sub contDiffAt_const)
  simpa using h

/-- **Joint smoothness of the stream profiles of a vorticity history.** Let `Ω(t, s, z)` be
smooth on an open set `V` containing `[0, T) × ℝ²` and `L`-periodic in `z`. Then the stream
profiles `Ψ(t, s, z)` of its slices are smooth on an open set `W` containing `[0, T) × ℝ²`. -/
theorem exists_isOpen_contDiffOn_streamProfile {L T : ℝ} (hL : 0 < L) {Ω : ℝ^3 → ℝ}
    {V : Set (ℝ^3)} (hV : IsOpen V) (hTV : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ V)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω V)
    (hper : ∀ q, Ω (q + EuclideanSpace.single (2 : Fin 3) L) = Ω q) :
    ∃ W : Set (ℝ^3), IsOpen W ∧ (∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ W) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (historyStream L Ω) W := by
  set c : ℝ := 2 * π / L
  set a : ℝ := -2 / c ^ 2
  set b : ℝ := 1 + 2 / c ^ 2
  have hab : a < b := by
    have : 0 < 2 / c ^ 2 := by positivity
    simp only [a, b, neg_div]
    linarith
  set K₁ : Set ℝ := Icc (a - 1) (b + 1)
  set f : ℝ × (ℝ × ℝ) → ℝ^3 := fun x ↦ profilePoint x.1 x.2.1 x.2.2
  -- the tube lemma
  have htube : ∀ t₀ : ℝ, t₀ ∈ Ico 0 T → ∃ ε > 0, ∀ t : ℝ, dist t t₀ < ε →
      ∀ s ∈ K₁, ∀ z ∈ Icc 0 L, profilePoint t s z ∈ V := by
    intro t₀ ht₀
    have hsub : ({t₀} : Set ℝ) ×ˢ (K₁ ×ˢ Icc 0 L) ⊆ f ⁻¹' V := by
      rintro ⟨t, s, z⟩ ⟨rfl, -⟩
      exact hTV _ (by simp [f, ht₀.1]) (by simp [f, ht₀.2])
    obtain ⟨u, v, hu, -, htu, htv, huv⟩ := generalized_tube_lemma isCompact_singleton
      (isCompact_Icc.prod isCompact_Icc) (hV.preimage continuous_profilePoint_uncurry) hsub
    obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu t₀ (htu rfl)
    exact ⟨ε, hε, fun t ht s hs z hz ↦
      huv (show (t, (s, z)) ∈ u ×ˢ v from ⟨hεu (Metric.mem_ball.2 ht), htv ⟨hs, hz⟩⟩)⟩
  choose ε hε hεV using htube
  have hdist : Continuous fun q : ℝ^3 ↦ q 0 := (EuclideanSpace.proj (0 : Fin 3)).continuous
  set W : Set (ℝ^3) := ⋃ t₀, ⋃ h : t₀ ∈ Ico 0 T, {q : ℝ^3 | dist (q 0) t₀ < ε t₀ h / 2}
  refine ⟨W, isOpen_iUnion fun t₀ ↦ isOpen_iUnion fun h ↦
    isOpen_lt (hdist.dist continuous_const) continuous_const, fun q h0 hT ↦
      mem_iUnion₂.2 ⟨q 0, ⟨h0, hT⟩, by simpa using half_pos (hε (q 0) ⟨h0, hT⟩)⟩, ?_⟩
  intro q hq
  obtain ⟨t₀, ht₀, hq : dist (q 0) t₀ < ε t₀ ht₀ / 2⟩ := mem_iUnion₂.1 hq
  set ε₀ := ε t₀ ht₀
  have hε₀ : 0 < ε₀ := hε t₀ ht₀
  let η : ContDiffBump t₀ := ⟨3 * ε₀ / 4, 7 * ε₀ / 8, by positivity, by linarith⟩
  set m : ℝ := (a + b) / 2 with hm
  set ρ : ℝ := (b - a) / 2 with hρdef
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  let χ : ContDiffBump m := ⟨ρ + 1 / 4, ρ + 1 / 2, by positivity, by linarith⟩
  set Φ' : ℝ × (ℝ × ℝ) → ℝ := fun x ↦ η x.1 * (χ x.2.1 * Ω (f x))
  have hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : dist x.1 t₀ < ε₀ ∧ dist x.2.1 m < ρ + 1
    · -- `Ω` is smooth at the profile point by the tube and periodicity
      obtain ⟨n, hn, -⟩ := existsUnique_sub_zsmul_mem_Ico hL x.2.2 0
      rw [zero_add] at hn
      have hs : x.2.1 ∈ K₁ := by
        obtain ⟨h1, h2⟩ := abs_lt.1 (Real.dist_eq x.2.1 m ▸ hx.2)
        constructor <;> linarith
      have hPΩ : ContDiffAt ℝ (⊤ : ℕ∞) Ω (profilePoint x.1 x.2.1 (x.2.2 - n • L)) :=
        hΩ.contDiffAt (hV.mem_nhds (hεV t₀ ht₀ x.1 hx.1 x.2.1 hs _ (Ico_subset_Icc_self hn)))
      have hshift : f x = profilePoint x.1 x.2.1 (x.2.2 - n • L) +
          n • EuclideanSpace.single (2 : Fin 3) L := by
        rw [show (n • EuclideanSpace.single (2 : Fin 3) L : ℝ^3) =
          EuclideanSpace.single (2 : Fin 3) (n • L) by ext i; fin_cases i <;> simp,
          ← profilePoint_add_axial, sub_add_cancel]
      exact (η.contDiff.comp contDiff_fst).contDiffAt.mul
        ((χ.contDiff.comp (contDiff_fst.comp contDiff_snd)).contDiffAt.mul
          ((hshift ▸ contDiffAt_add_zsmul_of_periodic hper hPΩ n).comp x
            contDiff_profilePoint_uncurry.contDiffAt))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      rcases not_and_or.1 hx with h | h
      · filter_upwards [((continuous_fst.dist continuous_const).tendsto x).eventually_const_lt
          (show 7 * ε₀ / 8 < dist x.1 t₀ by linarith [not_lt.1 h])] with y hy
        simp only [Φ', η.zero_of_le_dist (show η.rOut ≤ dist y.1 t₀ from hy.le), zero_mul]
      · filter_upwards [(((continuous_fst.comp continuous_snd).dist continuous_const).tendsto
          x).eventually_const_lt (show ρ + 1 / 2 < dist x.2.1 m by linarith [not_lt.1 h])]
          with y hy
        simp only [Φ', χ.zero_of_le_dist (show χ.rOut ≤ dist y.2.1 m from hy.le), zero_mul,
          mul_zero]
  have hmain := contDiff_streamProfile_slices hL hΦ' fun t s z ↦ by
    simp only [Φ', f, profilePoint_add_axial, hper]
  -- the projection `ℝ³ → ℝ × ℝ²`
  set g : ℝ^3 →L[ℝ] ℝ × ℝ^2 :=
    (EuclideanSpace.proj (0 : Fin 3) : ℝ^3 →L[ℝ] ℝ).prod
      (((EuclideanSpace.proj (1 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (0 : Fin 2) 1)) +
      ((EuclideanSpace.proj (2 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (1 : Fin 2) 1)))
  have hg : ∀ q : ℝ^3, g q = (q 0, WithLp.toLp 2 ![q 1, q 2]) := fun q ↦ by
    refine Prod.ext rfl ?_
    ext i
    fin_cases i <;> simp [g]
  refine (((hmain.comp g.contDiff).contDiffAt (x := q)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [((hdist.dist continuous_const).tendsto q).eventually_lt_const
    (show dist (q 0) t₀ < 3 * ε₀ / 4 by linarith)] with q' hq'
  have hη : η (q' 0) = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall.2 hq'.le)
  simp only [historyStream, Function.comp_apply, hg]
  refine congrFun (streamProfile_congr hL fun s hs z ↦ ?_) _
  change s ∈ Icc a b at hs
  have hχ : χ s = 1 := χ.one_of_mem_closedBall <| Metric.mem_closedBall.2 <|
    show |s - m| ≤ ρ + 1 / 4 from abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simp only [Φ', f, hη, hχ, one_mul]

/-! ### The stream function problem for every slice -/

/-- The slice of the history stream at time `t` is the stream profile of the slice of `Ω`. -/
theorem historyStream_timeSpaceCons (L : ℝ) (Ω : ℝ^3 → ℝ) (t : ℝ) (p : ℝ^2) :
    historyStream L Ω (timeSpaceCons t p) =
      streamProfile L (fun p ↦ Ω (profilePoint t p.1 p.2)) p := by
  have hp : (WithLp.toLp 2 ![p 0, p 1] : ℝ^2) = p := by
    ext i
    fin_cases i <;> simp
  simp [historyStream, timeSpaceCons, hp]

/-- Second spatial partial derivatives at a slice point are those of the slice. -/
private theorem secondPartialDeriv_succ_eq {F : ℝ^3 → ℝ} {t : ℝ} {p : ℝ^2}
    (hF : ContDiffAt ℝ 2 F (timeSpaceCons t p)) (j : Fin 2) :
    (∂[j.succ] (∂[j.succ] F)) (timeSpaceCons t p) =
      (∂[j] (∂[j] (fun y ↦ F (timeSpaceCons t y)))) p := by
  have hD : ∀ᶠ y in 𝓝 (timeSpaceCons t p), DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  have hcont : ContinuousAt (timeSpaceCons t) p :=
    (hasFDerivAt_timeSpaceCons_spatial 2 t p).continuousAt
  have hev : (∂[j] (fun y ↦ F (timeSpaceCons t y))) =ᶠ[𝓝 p] fun p' ↦
      (∂[j.succ] F) (timeSpaceCons t p') := by
    filter_upwards [hcont.preimage_mem_nhds hD] with p' hp'
    exact PDE.partialDeriv_timeSpaceCons_spatial j F t p' hp'
  have hF1 : DifferentiableAt ℝ (∂[j.succ] F) (timeSpaceCons t p) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (timeSpaceCons t p) :=
      hF.fderiv_right (m := 1) (by norm_num)
    exact (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  rw [PDE.partialDeriv_congr_nhds j hev, PDE.partialDeriv_timeSpaceCons_spatial j _ t p hF1]

/-- **The history stream solves the reduced stream equation** at every point `(t, s, z)` with
`0 < s < 1` where it is `C²`, when the slice of `Ω` at time `t` is smooth, odd and `L`-periodic in
`z`. -/
theorem historyStream_equation {L : ℝ} (hL : 0 < L) {Ω : ℝ^3 → ℝ} {q : ℝ^3}
    (hslice : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ Ω (profilePoint (q 0) p.1 p.2)))
    (hper : ∀ s z, Ω (profilePoint (q 0) s (z + L)) = Ω (profilePoint (q 0) s z))
    (hodd : ∀ s z, Ω (profilePoint (q 0) s (-z)) = -Ω (profilePoint (q 0) s z))
    (hq : q 1 ∈ Ioo (0 : ℝ) 1) (hC2 : ContDiffAt ℝ 2 (historyStream L Ω) q) :
    Ω q = -spacetimeSquaredRadiusDiffusion (historyStream L Ω) q := by
  set t := q 0
  set p : ℝ^2 := WithLp.toLp 2 ![q 1, q 2]
  have hqp : q = timeSpaceCons t p := by ext i; fin_cases i <;> simp [timeSpaceCons, p, t]
  have hcomp : (fun y ↦ historyStream L Ω (timeSpaceCons t y)) =
      streamProfile L (fun p ↦ Ω (profilePoint t p.1 p.2)) :=
    funext fun p ↦ historyStream_timeSpaceCons L Ω t p
  have hC2' : ContDiffAt ℝ 2 (historyStream L Ω) (timeSpaceCons t p) := hqp ▸ hC2
  have h1 := (PDE.partialDeriv_timeSpaceCons_spatial (0 : Fin 2) _ t p
    (hC2'.differentiableAt (by norm_num))).symm
  have h11 := secondPartialDeriv_succ_eq hC2' (0 : Fin 2)
  have h22 := secondPartialDeriv_succ_eq hC2' (1 : Fin 2)
  rw [hcomp] at h1 h11 h22
  have heq := streamProfile_equation hL hslice (fun s z ↦ hper s z) (fun s z ↦ hodd s z)
    (p := p) (by simpa [p] using hq)
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h11 h22
  have hval : Ω q = Ω (profilePoint t (p 0) (p 1)) :=
    congrArg Ω (by ext i; fin_cases i <;> simp [p, t, profilePoint])
  simp only [spacetimeSquaredRadiusDiffusion]
  rw [hval, hqp, h1, h11, h22, show (timeSpaceCons t p) 1 = p 0 by simp [timeSpaceCons]]
  linarith

/-- The history stream vanishes at the wall `s = 1`. -/
theorem historyStream_wall (L : ℝ) (Ω : ℝ^3 → ℝ) (t z : ℝ) :
    historyStream L Ω (profilePoint t 1 z) = 0 := by
  simp only [historyStream]
  exact streamProfile_wall (by simp)

/-- The history stream is `L`-periodic in `z`. -/
theorem historyStream_periodic {L : ℝ} (hL : 0 < L) (Ω : ℝ^3 → ℝ) (q : ℝ^3) :
    historyStream L Ω (q + EuclideanSpace.single (2 : Fin 3) L) = historyStream L Ω q := by
  have h : (WithLp.toLp 2 ![(q + EuclideanSpace.single (2 : Fin 3) L) 1,
      (q + EuclideanSpace.single (2 : Fin 3) L) 2] : ℝ^2) =
      WithLp.toLp 2 ![q 1, q 2] + EuclideanSpace.single (1 : Fin 2) L := by
    ext i
    fin_cases i <;> simp
  simp only [historyStream, h]
  have h0 : (q + EuclideanSpace.single (2 : Fin 3) L) 0 = q 0 := by simp
  rw [h0]
  exact streamProfile_periodic hL _

/-- The history stream is odd in `z`. -/
theorem isOddUnderCoordinateReflection_historyStream (L : ℝ) (Ω : ℝ^3 → ℝ) :
    PDE.Common.IsOddUnderCoordinateReflection (2 : Fin 3) (historyStream L Ω) := by
  intro q
  have h0 : PDE.Common.coordinateReflection (2 : Fin 3) q 0 = q 0 := by
    simp
  have h : (WithLp.toLp 2 ![PDE.Common.coordinateReflection (2 : Fin 3) q 1,
      PDE.Common.coordinateReflection (2 : Fin 3) q 2] : ℝ^2) =
      axialReflection (WithLp.toLp 2 ![q 1, q 2]) := by
    ext i
    fin_cases i <;> simp [PDE.Common.coordinateReflection_apply_same, axialReflection_apply_one]
  simp only [historyStream, h0, h]
  exact streamProfile_odd _

/-! ### The profile and meridian forms -/

/-- The slices of a profile smooth near `[0, T) × ℝ²` are smooth at times of `[0, T)`. -/
theorem contDiff_slice_of_contDiffOn {T : ℝ} {Ω : ℝ^3 → ℝ} {V : Set (ℝ^3)}
    (hTV : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ V) (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω V) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ Ω (profilePoint t p.1 p.2)) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ profilePoint t p.1 p.2) :=
    contDiff_profilePoint_uncurry.comp (contDiff_const.prodMk contDiff_id)
  exact hΩ.comp_contDiff hf fun p ↦ hTV _ (by simp [ht.1]) (by simp [ht.2])

/-- **The stream profiles of a vorticity history.** Let `Ω(t, s, z)` be smooth on an open
`V ⊇ [0, T) × ℝ²`, and `L`-periodic and odd in `z`. Then there is an open `W ⊇ [0, T) × ℝ²` on
which `Ψ = historyStream L Ω` is smooth, and `Ψ` solves the reduced stream equation
`Ω = -(8 Ψ_s + 4 s Ψ_ss + Ψ_zz)` on `0 < s < 1` at the times of `[0, T)`, vanishes at the wall
`s = 1`, and is `L`-periodic and odd in `z`. -/
theorem exists_historyStream {L T : ℝ} (hL : 0 < L) {Ω : ℝ^3 → ℝ} {V : Set (ℝ^3)}
    (hV : IsOpen V) (hTV : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ V)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω V)
    (hper : ∀ q, Ω (q + EuclideanSpace.single (2 : Fin 3) L) = Ω q)
    (hodd : PDE.Common.IsOddUnderCoordinateReflection (2 : Fin 3) Ω) :
    ∃ W : Set (ℝ^3), IsOpen W ∧ (∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ W) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (historyStream L Ω) W ∧
      (∀ q ∈ profileStrip (Ico 0 T),
        Ω q = -spacetimeSquaredRadiusDiffusion (historyStream L Ω) q) ∧
      (∀ t z, historyStream L Ω (profilePoint t 1 z) = 0) ∧
      (∀ q, historyStream L Ω (q + EuclideanSpace.single (2 : Fin 3) L) =
        historyStream L Ω q) ∧
      PDE.Common.IsOddUnderCoordinateReflection (2 : Fin 3) (historyStream L Ω) := by
  obtain ⟨W, hWo, hTW, hW⟩ := exists_isOpen_contDiffOn_streamProfile hL hV hTV hΩ hper
  refine ⟨W, hWo, hTW, hW, fun q hq ↦ ?_, historyStream_wall L Ω,
    historyStream_periodic hL Ω, isOddUnderCoordinateReflection_historyStream L Ω⟩
  have ht : q 0 ∈ Ico 0 T := hq.1
  have hC2 : ContDiffAt ℝ 2 (historyStream L Ω) q :=
    (hW.contDiffAt (hWo.mem_nhds (hTW q ht.1 ht.2))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine historyStream_equation hL (contDiff_slice_of_contDiffOn hTV hΩ ht)
    (fun s z ↦ by rw [profilePoint_add_axial, hper]) (fun s z ↦ ?_) ⟨hq.2.1, hq.2.2⟩ hC2
  have h := hodd (profilePoint (q 0) s z)
  have hr : PDE.Common.coordinateReflection (2 : Fin 3) (profilePoint (q 0) s z) =
      profilePoint (q 0) s (-z) := by
    ext i
    fin_cases i <;> simp [profilePoint, PDE.Common.coordinateReflection_apply_same]
  rwa [hr] at h

/-- **The angular stream function at every time.** For a vorticity profile `Ω(t, s, z)` whose
slice at time `t` is smooth, odd and `L`-periodic in `z`, the angular stream function
`φ(r, z) = r Ψ(t, r², z)` of the profile fields with stream profile `Ψ = historyStream L Ω` is the
stream function in the cylinder of the angular vorticity `ω^θ(r, z) = r Ω(t, r², z)`. It is of
the axis-regular form `r Ψ(r², z)`. -/
theorem isStreamFunction_ofProfiles_historyStream {L : ℝ} (hL : 0 < L) {Ω : ℝ^3 → ℝ}
    (U : ℝ^3 → ℝ) {t : ℝ}
    (hslice : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ Ω (profilePoint t p.1 p.2)))
    (hper : ∀ s z, Ω (profilePoint t s (z + L)) = Ω (profilePoint t s z))
    (hodd : ∀ s z, Ω (profilePoint t s (-z)) = -Ω (profilePoint t s z)) :
    IsStreamFunction L (fun x ↦ (ofProfiles U Ω (historyStream L Ω)).vorticity x t)
      (fun x ↦ (ofProfiles U Ω (historyStream L Ω)).streamFunction x t) := by
  set G : ℝ × ℝ → ℝ := fun p ↦ Ω (profilePoint t p.1 p.2)
  have hv : (fun x ↦ (ofProfiles U Ω (historyStream L Ω)).vorticity x t) =
      meridianVorticity G := by
    funext x
    simp [ofProfiles, meridianVorticity, meridianProfilePoint, G]
  have hs : (fun x ↦ (ofProfiles U Ω (historyStream L Ω)).streamFunction x t) =
      meridianStream L G := by
    funext x
    have hp : (WithLp.toLp 2 ![meridianProfilePoint t x 1, meridianProfilePoint t x 2] : ℝ^2) =
        squaredRadiusMap x := by
      ext i
      fin_cases i <;> simp [meridianProfilePoint, squaredRadiusMap]
    have h0 : meridianProfilePoint t x 0 = t := by simp [meridianProfilePoint]
    simp only [ofProfiles, meridianStream, historyStream, hp, h0, G]
  rw [hv, hs]
  exact isStreamFunction_meridianStream hL hslice (fun s z ↦ hper s z) (fun s z ↦ hodd s z)

/-- **Wall regularity.** If the history stream is smooth on an open set containing
`[0, T) × ℝ²`, the stream function of the profile fields is `C¹` at every wall point at every time
of `[0, T)`. -/
theorem hasWallRegularityOn_ofProfiles_historyStream {L T : ℝ} {Ω : ℝ^3 → ℝ} (U : ℝ^3 → ℝ)
    {W : Set (ℝ^3)} (hWo : IsOpen W) (hTW : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ W)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (historyStream L Ω) W) :
    HasWallRegularityOn (ofProfiles U Ω (historyStream L Ω)) (Ico 0 T) := by
  intro z t ht
  have hmem : meridianProfilePoint t (meridianPoint 1 z) ∈ W :=
    hTW _ (by simp [meridianProfilePoint, ht.1]) (by simp [meridianProfilePoint, ht.2])
  have hΨ : ContDiffAt ℝ 1 (historyStream L Ω) (meridianProfilePoint t (meridianPoint 1 z)) :=
    (hW.contDiffAt (hWo.mem_nhds hmem)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hc : ContDiffAt ℝ 1 (fun y : ℝ^2 ↦ historyStream L Ω (meridianProfilePoint t y))
      (meridianPoint 1 z) :=
    hΨ.comp _ (contDiff_meridianProfilePoint t).contDiffAt
  exact ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.contDiffAt).mul hc

end

end Euler.Cylinder
