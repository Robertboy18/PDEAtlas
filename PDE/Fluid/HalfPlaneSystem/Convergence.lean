/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.FieldPair
public import PDE.Fluid.HalfPlaneSystem.Iteration

/-!
# The difference estimate of the iteration map

Local existence is proved by iterating the map `carriedHistory U κ ω₀ θ₀ (-T) T`, which sends a
vorticity history to the vorticity carried by the flow of its field under the law `U`. The velocity
gradient of a bounded vorticity is only log-Lipschitz, so the map is not a contraction in the sup
norm. This module proves the inequality that still makes the iteration converge: the difference
estimate `abs_carriedHistory_sub_le`, which has the form of the hypothesis of Osgood's uniqueness
lemma rather than of a Lipschitz bound.

For two fields forming an `IsFieldPair` the carried vorticities differ by at most
`C ∫₀^{|t|} φ_A(Dm)`: the labels differ by the flow comparison, the amplitude of the first field is
Lipschitz in the label, and the weighted forcings `κ(X) Dθ₀(Y)(W e₀)` along the same label differ
through the inverse variations `W` and through the coefficient, `|κ(X) - κ(X')| ≤ Bκ₁ ‖X - X'‖`.
Here `Dm(r)` bounds the difference of the two histories at the times of absolute value `r`, and
`φ_A(r) = r (1 + log (A / r))` is the Osgood modulus. The fields of two `C^{1,α}` histories with a
common support radius `R₁ ≤ R₀` that differ by at most `Dm |r|` on the closed half-plane form such a
pair, with `c₀ = C 0 0` from the size bound of the law and `c₁ = 2 C 0 α` from its homogeneous Kato
bound.

## Main results

* `IsFieldPair.abs_carriedVorticity_sub_le`: at every `t ∈ [-T, T]` the vorticities carried by the
  two fields of a pair differ on the closed half-plane by at most
  `pairCarriedConst T K K₂ K₁ c₀ c₁ N L Bκ · ∫₀^{|t|} φ_A(Dm)`, when the amplitude of the first
  field is `L`-Lipschitz in the label, `‖Dθ₀‖ ≤ N` and the temperature datum is `C²` within the
  closed half-plane.
* `isFieldPair_lawField`: for `0 < α < 1`, the fields of two `C^{1,α}` histories with the same
  bounds whose difference is bounded by a nondecreasing majorant form a pair.
* `abs_carriedHistory_sub_le`: the difference estimate of the iteration map, the combination of the
  two.
* `pairCarriedConst`: the constant of the estimate.

`LocalExistence.lean` supplies the Lipschitz bound `L` of the amplitude and uses
`abs_carriedHistory_sub_le` to show that the iteration map satisfies the hypotheses of the abstract
convergence theorem of `FixedPoint.lean`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The constant of the difference estimate of the carried vorticities of a pair of fields:
`L e^{K T} c_X + T (Bκ₀ N e^{2 K₁ T} c_J + Bκ₁ c_X N e^{K₁ T})`, with `c_X = pairFlowConst` and
`c_J = pairVariationConst`. -/
def pairCarriedConst (T : ℝ) (K K₂ : ℝ≥0) (K₁ c₀ c₁ N L : ℝ) (Bκ : ℕ → ℝ) : ℝ :=
  L * Real.exp (K * T) * pairFlowConst T K₁ c₀ +
    T * (Bκ 0 * (N * Real.exp (K₁ * T) * Real.exp (K₁ * T) * pairVariationConst T K₂ K₁ c₀ c₁) +
      Bκ 1 * pairFlowConst T K₁ c₀ * (N * Real.exp (K₁ * T)))

variable {v v' : ℝ → ℝ^2 → ℝ^2} {Dv Dv' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v D2v' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {T : ℝ} {K K₂ : ℝ≥0} {K₁ c₀ c₁ A : ℝ}
  {Dm : ℝ → ℝ} {κ ω₀ θ₀ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ} {N L : ℝ}

/-- **The difference estimate of the carried vorticities of a pair of fields.** If the carried
amplitude of the first field is `L`-Lipschitz in the label on the closed half-plane and
`‖Dθ₀‖ ≤ N` there, then at every `t ∈ [-T, T]` the carried vorticities differ on the closed
half-plane by at most `pairCarriedConst T K K₂ K₁ c₀ c₁ N L Bκ * ∫₀^{|t|} φ_A(Dm)`. It is the
estimate that makes the iteration converge. Proof: the two carried vorticities are amplitudes
at the labels `Y`, `Y'` of the two flows. The amplitude of the first field is Lipschitz in the
label and the labels differ by the flow comparison; at the common label `Y'` the two forcings
differ through the inverse first variations and through the coefficient at the two positions. -/
theorem IsFieldPair.abs_carriedVorticity_sub_le
    (hp : IsFieldPair v v' Dv Dv' D2v D2v' T K K₂ K₁ c₀ c₁ A Dm)
    (hκ : IsForcingCoefficient κ Bκ) (hθ₀ : ContDiffOn ℝ 2 θ₀ H̄)
    (hN : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ θ₀ H̄ y‖ ≤ N) (hL0 : 0 ≤ L)
    (hLip : ∀ t ∈ Icc (-T) T, ∀ a' a'' : ℝ^2, 0 ≤ a' 1 → 0 ≤ a'' 1 →
      |forcedAmplitude (dataVorticity ω₀) (weightedForcing v Dv (-T) T κ (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) a' t -
        forcedAmplitude (dataVorticity ω₀) (weightedForcing v Dv (-T) T κ (dataTemperature θ₀)
          (EuclideanSpace.single 0 1)) a'' t| ≤ L * ‖a' - a''‖)
    {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity κ ω₀ θ₀ v Dv (-T) T x t - carriedVorticity κ ω₀ θ₀ v' Dv' (-T) T x t| ≤
      pairCarriedConst T K K₂ K₁ c₀ c₁ N L Bκ *
        ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus A (Dm r) := by
  have hv := hp.left
  have hv' := hp.right
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have h0 := hp.zero_mem
  have hK₁ := hp.deriv_bound_nonneg
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by simp))
  have hB0 := hκ.bound_nonneg 0
  have hB1 := hκ.bound_nonneg 1
  have hFc := hp.pairFlowConst_nonneg
  have hVc := hp.pairVariationConst_nonneg
  set I := ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus A (Dm r) with hIdef
  have htT : |t| ∈ Icc 0 T := ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩
  have hI0 : 0 ≤ I := integral_osgoodModulus_nonneg hp.nonneg_majorant hp.le_modulus htT
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set Y := flowOn v (-T) T 0 t x with hYdef
  set Y' := flowOn v' (-T) T 0 t x with hY'def
  have hY : 0 ≤ Y 1 := hp.mapsTo_left 0 h0 t ht hx
  have hY' : 0 ≤ Y' 1 := hp.mapsTo_right 0 h0 t ht hx
  set G := weightedForcing v Dv (-T) T κ (dataTemperature θ₀) e
  set G' := weightedForcing v' Dv' (-T) T κ (dataTemperature θ₀) e
  have hθC2 : ContDiff ℝ 2 (dataTemperature θ₀) := contDiff_dataTemperature hθ₀
  have hθC1 : ContDiff ℝ 1 (dataTemperature θ₀) := hθC2.of_le (by norm_num)
  -- the amplitude is Lipschitz in the label
  have h1 : |forcedAmplitude (dataVorticity ω₀) G Y t - forcedAmplitude (dataVorticity ω₀) G Y' t|
      ≤ L * ‖Y - Y'‖ := hLip t ht Y Y' hY hY'
  -- the labels
  have hlab := hL.norm_flowOn_sub_flowOn_le_of_inverse hL' (s := t) (t := 0) ht h0 x
  have hflow := hp.norm_flowOn_sub_le_osgood ht hY'
  have heg : Real.exp (K * |0 - t|) ≤ Real.exp (K * T) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.2)
    rw [zero_sub, abs_neg]; exact htT.2
  have hYY : ‖Y - Y'‖ ≤ Real.exp (K * T) * (pairFlowConst T K₁ c₀ * I) :=
    hlab.trans (mul_le_mul heg hflow (norm_nonneg _) (Real.exp_pos _).le)
  -- the forcing integrals
  have hGc (g : ℝ^2 → ℝ → ℝ)
      (hg : ContinuousOn (fun p : ℝ^2 × ℝ ↦ g p.1 p.2) (univ ×ˢ Icc (-T) T)) :
      IntervalIntegrable (fun r ↦ g Y' r) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hg.comp (continuousOn_const.prodMk continuousOn_id) fun r hr ↦ ⟨mem_univ _, hr⟩).mono
      ?_
    exact uIcc_subset_Icc h0 ht
  have hGi := hGc G (continuousOn_weightedForcing hv.toIsC1FieldOn h0
    hκ.contDiff_one.continuous hθC1)
  have hG'i := hGc G' (continuousOn_weightedForcing hv'.toIsC1FieldOn h0
    hκ.contDiff_one.continuous hθC1)
  have hdiff2 : forcedAmplitude (dataVorticity ω₀) G Y' t -
      forcedAmplitude (dataVorticity ω₀) G' Y' t = ∫ r in (0)..t, (G Y' r - G' Y' r) := by
    simp only [forcedAmplitude]
    rw [intervalIntegral.integral_sub hGi hG'i]
    ring
  have hfd : ‖fderiv ℝ (dataTemperature θ₀) Y'‖ ≤ N := by
    unfold dataTemperature
    rw [PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 (k := 2) (by norm_num)
      (by exact_mod_cast hθ₀) hY']
    exact hN Y' hY'
  set E := Real.exp (K₁ * T)
  have hbound : ∀ r ∈ Set.uIoc (0 : ℝ) t, ‖G Y' r - G' Y' r‖ ≤
      Bκ 0 * (N * E * E * (pairVariationConst T K₂ K₁ c₀ c₁ * I)) +
        Bκ 1 * (pairFlowConst T K₁ c₀ * I) * (N * E) := by
    intro r hr
    have hr' : |r - 0| ≤ |t - 0| := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hr)
    rw [sub_zero, sub_zero] at hr'
    have hrT : r ∈ Icc (-T) T := ⟨by linarith [neg_abs_le r, htT.2],
      (le_abs_self r).trans (hr'.trans htT.2)⟩
    have hW := hv.toIsC1FieldOn.norm_variationOn_inverse_sub_le hv'.toIsC1FieldOn (s := r)
      (t := 0) hrT h0 Y'
    have hWb := hv.toIsC1FieldOn.norm_variationOn_le_of_invariant hp.mapsTo_left
      hp.norm_deriv_left h0 hrT (hp.mapsTo_left r hrT 0 h0 hY')
    have hWb' := hv'.toIsC1FieldOn.norm_variationOn_le_of_invariant hp.mapsTo_right
      hp.norm_deriv_right h0 hrT (hp.mapsTo_right r hrT 0 h0 hY')
    have hJ := hp.norm_variationOn_sub_le hrT hY'
    have hJI : ∫ q in (0)..|r|, PDE.Analysis.osgoodModulus A (Dm q) ≤ I :=
      integral_osgoodModulus_mono hp.modulus_pos hp.monotoneOn hp.nonneg_majorant hp.le_modulus
        (abs_nonneg r) hr' htT.2
    have hexp : Real.exp (K₁ * |0 - r|) ≤ E := by
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK₁)
      rw [zero_sub, abs_neg]; exact hr'.trans htT.2
    set X := flowOn v (-T) T r 0 Y'
    set X' := flowOn v' (-T) T r 0 Y'
    set W := variationOn v Dv (-T) T 0 r X
    set W' := variationOn v' Dv' (-T) T 0 r X'
    have hWW : ‖W - W'‖ ≤ E * (pairVariationConst T K₂ K₁ c₀ c₁ * I) * E := by
      refine hW.trans (mul_le_mul (mul_le_mul (hWb.trans hexp)
        (hJ.trans (mul_le_mul_of_nonneg_left hJI hVc)) (norm_nonneg _)
        (Real.exp_pos _).le) (hWb'.trans hexp) (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hVc hI0)))
    have he : ‖e‖ = 1 := by simp [e]
    have hXX : ‖X - X'‖ ≤ pairFlowConst T K₁ c₀ * I :=
      (hp.norm_flowOn_sub_le_osgood hrT hY').trans
        (mul_le_mul_of_nonneg_left hJI hFc)
    set g := fderiv ℝ (dataTemperature θ₀) Y' (W e)
    set g' := fderiv ℝ (dataTemperature θ₀) Y' (W' e)
    have hGG : G Y' r - G' Y' r = κ X * (g - g') + (κ X - κ X') * g' := by
      simp only [G, G', weightedForcing, labelForcing, g, g', W, W', X, X']
      ring
    have hgg : |g - g'| ≤ N * E * E * (pairVariationConst T K₂ K₁ c₀ c₁ * I) := by
      rw [← map_sub, ← sub_apply, ← Real.norm_eq_abs]
      calc ‖fderiv ℝ (dataTemperature θ₀) Y' ((W - W') e)‖
          ≤ ‖fderiv ℝ (dataTemperature θ₀) Y'‖ * (‖W - W'‖ * ‖e‖) :=
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)))
        _ ≤ N * (E * (pairVariationConst T K₂ K₁ c₀ c₁ * I) * E * 1) := by
            rw [he]
            exact mul_le_mul hfd (by linarith) (by positivity) hN0
        _ = _ := by ring
    have hg' : |g'| ≤ N * E := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (dataTemperature θ₀) Y' (W' e)‖
          ≤ ‖fderiv ℝ (dataTemperature θ₀) Y'‖ * (‖W'‖ * ‖e‖) :=
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)))
        _ ≤ N * (E * 1) := by
            rw [he]
            exact mul_le_mul hfd (by linarith [hWb'.trans hexp]) (by positivity) hN0
        _ = N * E := by ring
    rw [hGG, Real.norm_eq_abs]
    calc |κ X * (g - g') + (κ X - κ X') * g'| ≤ |κ X| * |g - g'| + |κ X - κ X'| * |g'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Bκ 0 * (N * E * E * (pairVariationConst T K₂ K₁ c₀ c₁ * I)) +
          Bκ 1 * (pairFlowConst T K₁ c₀ * I) * (N * E) := by
          refine add_le_add (mul_le_mul (hκ.abs_le X) hgg (abs_nonneg _) hB0)
            (mul_le_mul ((hκ.abs_sub_le X X').trans (mul_le_mul_of_nonneg_left hXX hB1)) hg'
              (abs_nonneg _) (by positivity))
  have h2 : |forcedAmplitude (dataVorticity ω₀) G Y' t -
      forcedAmplitude (dataVorticity ω₀) G' Y' t| ≤
      (Bκ 0 * (N * E * E * (pairVariationConst T K₂ K₁ c₀ c₁ * I)) +
        Bκ 1 * (pairFlowConst T K₁ c₀ * I) * (N * E)) * T := by
    rw [hdiff2, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left htT.2 (by positivity)
  change |forcedAmplitude (dataVorticity ω₀) G Y t -
    forcedAmplitude (dataVorticity ω₀) G' Y' t| ≤ _
  have hsplit : forcedAmplitude (dataVorticity ω₀) G Y t -
      forcedAmplitude (dataVorticity ω₀) G' Y' t =
      (forcedAmplitude (dataVorticity ω₀) G Y t - forcedAmplitude (dataVorticity ω₀) G Y' t) +
      (forcedAmplitude (dataVorticity ω₀) G Y' t - forcedAmplitude (dataVorticity ω₀) G' Y' t) :=
    by ring
  rw [hsplit]
  calc _ ≤ |forcedAmplitude (dataVorticity ω₀) G Y t - forcedAmplitude (dataVorticity ω₀) G Y' t|
        + |forcedAmplitude (dataVorticity ω₀) G Y' t -
          forcedAmplitude (dataVorticity ω₀) G' Y' t| := abs_add_le _ _
    _ ≤ L * (Real.exp (K * T) * (pairFlowConst T K₁ c₀ * I)) +
        (Bκ 0 * (N * E * E * (pairVariationConst T K₂ K₁ c₀ c₁ * I)) +
          Bκ 1 * (pairFlowConst T K₁ c₀ * I) * (N * E)) * T :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hYY hL0)) h2
    _ = pairCarriedConst T K K₂ K₁ c₀ c₁ N L Bκ * I := by unfold pairCarriedConst; ring

/-! ### The fields of two histories under a law -/

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}

/-- **The fields of two histories form a pair.** For two `C^{1,α}` histories on `[-T, T]` with
the bounds `R₁ ≤ R₀, B, M, B₁, M₁` that differ on the closed half-plane at time `r` by at most
`Dm |r|`, with `Dm` nondecreasing with values in `[0, A']`, `A' > 0`, the fields of the law form
an `IsFieldPair` with `K₁ = C 0 α (1 + B log (2 + M) + B)`, `c₀ = C 0 0`, `c₁ = 2 C 0 α` and the
Osgood parameter `pairModulusBound A' M`. -/
theorem isFieldPair_lawField (hU : IsVelocityLaw U R₀ C) {ω ω' : ℝ → ℝ^2 → ℝ}
    {α R₁ B M B₁ M₁ A' : ℝ} (hω : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁)
    (hω' : IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁) (hR : R₁ ≤ R₀) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) (hA' : 0 < A') (hmono : MonotoneOn Dm (Icc 0 T))
    (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s) (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A')
    (hsub : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ Dm |r|) :
    IsFieldPair (lawField U ω) (lawField U ω') (lawFieldDeriv U ω) (lawFieldDeriv U ω')
      (lawFieldDeriv₂ U ω) (lawFieldDeriv₂ U ω') T
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
        (C 0 α * (1 + B * Real.log (2 + M) + B))))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 * (C 1 α * max B (max B₁ M₁))))
      (C 0 α * (1 + B * Real.log (2 + M) + B)) (C 0 0) (2 * C 0 α) (pairModulusBound A' M)
      Dm := by
  have hb := isBoundedFlowOn_lawField hU hω hR hα hα1 (by linarith)
  have hb' := isBoundedFlowOn_lawField hU hω' hR hα hα1 (by linarith)
  have hC := hU.const_nonneg 0 α
  refine
    { nonneg := hT
      left := hω.isC2FieldOn_lawField hU hR hα hα1
      right := hω'.isC2FieldOn_lawField hU hR hα hα1
      mapsTo_left := hb.mapsTo
      mapsTo_right := hb'.mapsTo
      norm_deriv_left := hb.norm_deriv_le
      norm_deriv_right := hb'.norm_deriv_le
      const_nonneg := hU.const_nonneg 0 0
      deriv_const_nonneg := by positivity
      modulus_pos := IsHistoryPair.modulus_pos
      monotoneOn := hmono
      nonneg_majorant := hDm0
      le_modulus := fun s hs ↦ (hDmA s hs).trans ((le_max_left A' 1).trans (le_max_right _ _))
      norm_sub_le := fun r hr y hy ↦ ?_
      norm_deriv_sub_le := fun r hr y hy ↦ ?_ }
  · rw [lawField_of_nonneg U ω r hy, lawField_of_nonneg U ω' r hy]
    exact hU.norm_sub_le hR (hω.continuousOn r hr) (hω.eq_zero r hr) (hω'.continuousOn r hr)
      (hω'.eq_zero r hr) (hsub r hr) hy
  · have hrT : |r| ∈ Icc 0 T := ⟨abs_nonneg r, abs_le.mpr ⟨hr.1, hr.2⟩⟩
    have hβ0 := hDm0 _ hrT
    have hβA := hDmA _ hrT
    rw [lawFieldDeriv_eq hU hω hR hα hα1 hr hy, lawFieldDeriv_eq hU hω' hR hα hα1 hr hy]
    have hM0 : 0 ≤ M := hω.holder_nonneg hr
    have h1 := hU.norm_fderivWithin_sub_le_osgood hα hα1 hR (hω.continuousOn r hr)
      (hω.eq_zero r hr) (hω'.continuousOn r hr) (hω'.eq_zero r hr) (hω.holder r hr)
      (hω'.holder r hr) hM0 hM0 (hsub r hr) hβA hy
    have hA₁0 : 0 < 2 * A' + (M + M) := by linarith
    have h2 := PDE.Analysis.osgoodModulus_le_osgoodModulus (r := Dm |r|) hA₁0
      (le_max_left (2 * A' + (M + M)) (max A' 1)) hβ0
    have h3 := PDE.Analysis.le_osgoodModulus (A := pairModulusBound A' M) hβ0
      (hβA.trans ((le_max_left A' 1).trans (le_max_right _ _)))
    refine h1.trans ?_
    calc C 0 α * (PDE.Analysis.osgoodModulus (2 * A' + (M + M)) (Dm |r|) + Dm |r|)
        ≤ C 0 α * (PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm |r|) +
          PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm |r|)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC
      _ = 2 * C 0 α * PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm |r|) := by ring

/-- **The difference estimate of the iteration map.** Let `ω, ω'` be `C^{1,α}` histories on
`[-T, T]` with the bounds `R₁ ≤ R₀, B, M, B₁, M₁` that differ on the closed half-plane at time `r`
by at most `Dm |r|`, with `Dm` nondecreasing with values in `[0, A']`. If the carried amplitude of
`ω` is `L`-Lipschitz in the label on the closed half-plane and `‖Dθ₀‖ ≤ N` there, then at every
`t ∈ [-T, T]` the images under the iteration map differ on the closed half-plane by at most
`pairCarriedConst … * ∫₀^{|t|} φ_A(Dm)`, `A = pairModulusBound A' M`. Proof: the fields of the two
histories form a pair (`isFieldPair_lawField`), to which
`IsFieldPair.abs_carriedVorticity_sub_le` applies. -/
theorem abs_carriedHistory_sub_le (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    {ω ω' : ℝ → ℝ^2 → ℝ} {α R₁ B M B₁ M₁ A' : ℝ}
    (hω : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁)
    (hω' : IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁) (hR : R₁ ≤ R₀) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) (hA' : 0 < A') (hmono : MonotoneOn Dm (Icc 0 T))
    (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s) (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A')
    (hsub : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ Dm |r|)
    (hθ₀ : ContDiffOn ℝ 2 θ₀ H̄) (hN : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ θ₀ H̄ y‖ ≤ N)
    (hL0 : 0 ≤ L)
    (hLip : ∀ t ∈ Icc (-T) T, ∀ a' a'' : ℝ^2, 0 ≤ a' 1 → 0 ≤ a'' 1 →
      |forcedAmplitude (dataVorticity ω₀) (weightedForcing (lawField U ω) (lawFieldDeriv U ω)
          (-T) T κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a' t -
        forcedAmplitude (dataVorticity ω₀) (weightedForcing (lawField U ω) (lawFieldDeriv U ω)
          (-T) T κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a'' t| ≤ L * ‖a' - a''‖)
    {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedHistory U κ ω₀ θ₀ (-T) T ω t x - carriedHistory U κ ω₀ θ₀ (-T) T ω' t x| ≤
      pairCarriedConst T
        (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
          (C 0 α * (1 + B * Real.log (2 + M) + B))))
        (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 * (C 1 α * max B (max B₁ M₁))))
        (C 0 α * (1 + B * Real.log (2 + M) + B)) (C 0 0) (2 * C 0 α) N L Bκ *
        ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) :=
  (isFieldPair_lawField hU hω hω' hR hα hα1 hT hA' hmono hDm0 hDmA hsub).abs_carriedVorticity_sub_le
    hκ hθ₀ hN hL0 hLip ht hx

end HalfPlaneSystem
