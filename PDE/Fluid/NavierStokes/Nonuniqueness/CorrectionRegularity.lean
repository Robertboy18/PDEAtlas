/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.MixedConvection
public import PDE.Fluid.NavierStokes.Nonuniqueness.ForwardMild
public import PDE.Fluid.NavierStokes.Selfsimilar.ForwardMildRegularity

/-!
# Regularity of the ancient correction at every Sobolev order

The ancient correction `U_cor` of an unstable profile lies in vector `H³` and solves the free
forward mild equation (`forwardFreeMild_of_forwardMild`)

`U_cor(τ) = S₀(τ - σ) U_cor(σ) + ∫_σ^τ Π S₀(τ - r) (F(r) + L_far(r) U_cor(r) - B U_cor(r) -
  (U_cor(r)·∇) U_cor(r)) dr`

for `σ ≤ τ ≤ 0`. Each term of the integrand is available at every order: the cutoff forcing
`F = cutoffForcing D R m` in vector `Hᵐ`, the cutoff coefficient `L_far = cutoffCoefficient D R m`
and the profile transport `B` from `Hᵐ⁺¹` to `Hᵐ`, and the convection with a frozen coefficient,
`v ↦ (w·∇) v` from `Hᵐ⁺¹` to `Hᵐ` for `w ∈ Hᵐ` (`mixedConvection`). The operators of successive
orders agree once the top order is forgotten. Writing the integrand as
`F(r) + A_m(r) U_cor(r)`, with the family `A_m(r) = L_far(r) - B - (U_cor(r)·∇)`
(`correctionOperator`) built from the regularity already known, the parabolic smoothing of
forward mild solutions (`forwardMild_memSobolev_succ`) lifts `U_cor` from `Hᵐ⁺¹` to `Hᵐ⁺²`, with
the mild equation one order higher, on every interval `(σ, 0]`. Since forgetting the top order is
injective, the lifts from different starting times agree, so by induction `U_cor` is a continuous
path in vector `Hᵐ` on `τ ≤ 0` for every `m` (`exists_correctionLift`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile) (R : ℝ)

/-! ### Lowering the cutoff coefficient and forcing -/

/-- Forgetting the top order of the cutoff field of order `k + 1` gives the cutoff field of
order `k`. -/
theorem lowerOrderCLM_cutoffSobolev (k : ℕ) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r) (τ : ℝ)
    (i : Fin 3) :
    lowerOrderCLM (Nat.le_succ k) (cutoffSobolev D R (k + 1) hr τ i) =
      cutoffSobolev D R k hr τ i := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [wkpBaseCoordinateCLM_lowerOrderCLM]
  refine Lp.ext ?_
  have h := (baseRepresentative_cutoffSobolev D (R := R) (k + 1) hr τ i).trans
    (baseRepresentative_cutoffSobolev D (R := R) k hr τ i).symm
  simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
    wkpBaseCoordinateCLM_apply] using h

/-- Forgetting the top order of the cutoff coefficient of order `k + 1` gives the cutoff
coefficient of order `k`. -/
theorem vectorLower_cutoffCoefficient (k : ℕ) (τ : ℝ) (v : VectorH 3 (k + 2)) :
    vectorLower 3 k (cutoffCoefficient D R (k + 1) τ v) =
      cutoffCoefficient D R k τ (vectorLower 3 (k + 1) v) := by
  have h := vectorLowerOrderCLM_profileTransport (Nat.le_succ k)
    (cutoffSobolev D R (k + 2) le_top τ) v
  simp only [lowerOrderCLM_cutoffSobolev] at h
  exact h

/-- Forgetting the top order of the unprojected cutoff forcing of order `k + 1` gives the
unprojected cutoff forcing of order `k`. -/
theorem vectorLower_cutoffConvection (k : ℕ) (τ : ℝ) :
    vectorLower 3 k (cutoffConvection D R (k + 1) τ) = cutoffConvection D R k τ := by
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  simp only [domainMeasure, Measure.restrict_univ]
  have h := (cutoffConvection_base_ae D R (k + 1) τ j).trans
    (cutoffConvection_base_ae D R k τ j).symm
  rw [← baseRepresentative_lowerOrderCLM (Nat.le_succ k)] at h
  exact h

/-- Forgetting the top order of the cutoff forcing of order `k + 1` gives the cutoff forcing of
order `k`. -/
theorem vectorLower_cutoffForcing (k : ℕ) (τ : ℝ) :
    vectorLower 3 k (cutoffForcing D R (k + 1) τ) = cutoffForcing D R k τ := by
  rw [cutoffForcing, cutoffForcing, map_neg, vectorLower_leraySobolev,
    vectorLower_cutoffConvection]

/-! ### The operator family of the correction equation -/

/-- An order `m` with `3 < 2m` satisfies `3 ≤ m + 1`. -/
theorem three_le_succ_of_three_lt_two_mul {m : ℕ} (hm : (3 : ℝ) < 2 * m) : 3 ≤ m + 1 := by
  have h : (1 : ℝ) < m := by linarith
  have h' : 1 < m := by exact_mod_cast h
  omega

/-- The order `m + 1` satisfies the algebra threshold when `m` does. -/
theorem three_lt_two_mul_succ {m : ℕ} (hm : (3 : ℝ) < 2 * m) : (3 : ℝ) < 2 * (m + 1 : ℕ) := by
  push_cast
  linarith

/-- The linear part of the correction equation at order `m`, with the convection coefficient
frozen at `w ∈ Hᵐ`: `v ↦ L_far(τ) v - B v - (w·∇) v` from vector `Hᵐ⁺¹` to vector `Hᵐ`, with the
cutoff coefficient `L_far`, the transport `B` of the linearization at the profile and the
unprojected convection. -/
def correctionOperator (m : ℕ) (hm : (3 : ℝ) < 2 * m) (τ : ℝ) (w : VectorH 3 m) :
    VectorH 3 (m + 1) →L[ℝ] VectorH 3 m :=
  cutoffCoefficient D R m τ - (D.profileCoefficientBounds m).transport - mixedConvection m hm w

/-- Forgetting the top order of the operator of order `m + 1` gives the operator of order `m`
frozen at the lowered coefficient. -/
theorem vectorLower_correctionOperator {m : ℕ} (hm : (3 : ℝ) < 2 * m)
    (hm' : (3 : ℝ) < 2 * (m + 1 : ℕ)) (τ : ℝ) (w : VectorH 3 (m + 1)) (v : VectorH 3 (m + 2)) :
    vectorLower 3 m (correctionOperator D R (m + 1) hm' τ w v) =
      correctionOperator D R m hm τ (vectorLower 3 m w) (vectorLower 3 (m + 1) v) := by
  simp only [correctionOperator, sub_apply, map_sub]
  rw [vectorLower_cutoffCoefficient, ProfileCoefficientBounds.vectorLower_transport
    (D.profileCoefficientBounds (m + 1)) (D.profileCoefficientBounds m),
    vectorLower_mixedConvection hm hm']

/-- A coefficient path continuous on a set gives an operator family continuous on it in the
operator norm. -/
theorem continuousOn_correctionOperator {m : ℕ} (hm : (3 : ℝ) < 2 * m) {w : ℝ → VectorH 3 m}
    {S : Set ℝ} (hw : ContinuousOn w S) :
    ContinuousOn (fun τ ↦ correctionOperator D R m hm τ (w τ)) S :=
  (((continuous_cutoffCoefficient D R m).continuousOn).sub continuousOn_const).sub
    ((mixedConvection m hm).continuous.comp_continuousOn hw)

/-- At order two the integrand of the free forward mild equation of the ancient correction is the
cutoff forcing plus the operator frozen at the correction. -/
theorem correctionForcing_sub_transport (hm : (3 : ℝ) < 2 * (2 : ℕ)) (v : ℝ → VectorH 3 3)
    (r : ℝ) :
    correctionForcing D R v r - (D.profileCoefficientBounds 2).transport (v r) =
      cutoffForcing D R 2 r + correctionOperator D R 2 hm r (vectorLower 3 2 (v r)) (v r) := by
  simp only [correctionForcing, correctionOperator, sub_apply,
    ← convection_eq_mixedConvection hm]
  abel

/-! ### The induction over the order -/

/-- The integrand `F(r) + A_m(r) V(r)` of the forward mild equation of a path `V` in vector
`Hᵐ⁺¹`: the cutoff forcing plus the operator family frozen at `V` in vector `Hᵐ`. -/
def liftForcing (m : ℕ) (hm : (3 : ℝ) < 2 * m) (V : ℝ → VectorH 3 (m + 1)) (r : ℝ) :
    VectorH 3 m :=
  cutoffForcing D R m r + correctionOperator D R m hm r (vectorLower 3 m (V r)) (V r)

/-- A path continuous on a set has an integrand continuous on it. -/
theorem continuousOn_liftForcing {m : ℕ} (hm : (3 : ℝ) < 2 * m) {V : ℝ → VectorH 3 (m + 1)}
    {S : Set ℝ} (hV : ContinuousOn V S) : ContinuousOn (liftForcing D R m hm V) S :=
  (continuous_cutoffForcing D R m).continuousOn.add
    ((continuousOn_correctionOperator D R hm
      ((vectorLower 3 m).continuous.comp_continuousOn hV)).clm_apply hV)

variable (s : ℝ)

/-- `V` is the ancient correction in vector `Hᵐ⁺¹` on `τ ≤ 0`: a continuous path there whose
lowering to vector `H³` is the correction, solving for `σ ≤ τ ≤ 0`

`V(τ) = S₀(τ - σ) V(σ) + ∫_σ^τ Π S₀(τ - r) (F(r) + A_m(r) V(r)) dr`

with the cutoff forcing `F` and the operator family `A_m` frozen at `V` in vector `Hᵐ`
(`liftForcing`). -/
def IsCorrectionLift (m : ℕ) (hm : (3 : ℝ) < 2 * m) (V : ℝ → VectorH 3 (m + 1)) : Prop :=
  ContinuousOn V (Iic 0) ∧
    (∀ τ ≤ 0, vectorLowerOrderCLM (three_le_succ_of_three_lt_two_mul hm) (V τ) =
      ancientLift D.dichotomy.η (ancientCorrection D R s) τ) ∧
    ∀ σ τ, σ ≤ τ → τ ≤ 0 → V τ = vectorSelfsimilarHeat 3 (m + 1) (τ - σ).toNNReal (V σ) +
      ∫ r in σ..τ, projectedSelfsimilarHeatGainKernel 3 m (τ - r) (liftForcing D R m hm V r)

variable {D R s}

/-- The ancient correction itself is the lift of order three. -/
theorem isCorrectionLift_two (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (hm : (3 : ℝ) < 2 * (2 : ℕ)) :
    IsCorrectionLift D R s 2 hm (ancientLift D.dichotomy.η (ancientCorrection D R s)) := by
  refine ⟨(ancientLift D.dichotomy.η (ancientCorrection D R s)).continuous.continuousOn,
    fun τ _ ↦ vectorLowerOrderCLM_refl_apply _, fun σ τ hστ hτ ↦ ?_⟩
  refine (forwardFreeMild_of_forwardMild D R s hR hs σ τ hστ hτ).trans
    (congrArg₂ (· + ·) rfl (intervalIntegral.integral_congr fun r _ ↦ ?_))
  exact congrArg _ (correctionForcing_sub_transport D R hm _ r)

/-- One step of the induction: a lift of order `m + 1` gives a lift of order `m + 2`. -/
theorem IsCorrectionLift.succ {m : ℕ} {hm : (3 : ℝ) < 2 * m} {V : ℝ → VectorH 3 (m + 1)}
    (hV : IsCorrectionLift D R s m hm V) :
    ∃ W : ℝ → VectorH 3 (m + 2), IsCorrectionLift D R s (m + 1) (three_lt_two_mul_succ hm) W := by
  obtain ⟨hVc, hVlow, hVeq⟩ := hV
  have hm' := three_lt_two_mul_succ hm
  have hex : ∀ σ : ℝ, ∃ Wσ : ℝ → VectorH 3 (m + 2), ContinuousOn Wσ (Ioc σ 0) ∧
      (∀ t ∈ Ioc σ 0, vectorLower 3 (m + 1) (Wσ t) = V t) ∧
      ∀ σ' ∈ Ioc σ 0, ∀ t ∈ Icc σ' 0,
        Wσ t = vectorSelfsimilarHeat 3 (m + 2) (t - σ').toNNReal (Wσ σ') +
          ∫ r in σ'..t, projectedSelfsimilarHeatGainKernel 3 (m + 1) (t - r)
            (cutoffForcing D R (m + 1) r + correctionOperator D R (m + 1) hm' r (V r) (Wσ r)) := by
    intro σ
    have hsub : Icc σ 0 ⊆ Iic (0 : ℝ) := fun t ht ↦ ht.2
    have hVc' : ContinuousOn V (Icc σ 0) := hVc.mono hsub
    have hA₀op := continuousOn_correctionOperator D R hm
      ((vectorLower 3 m).continuous.comp_continuousOn hVc')
    have hAop := continuousOn_correctionOperator D R hm' hVc'
    obtain ⟨a₀, ha₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA₀op
    obtain ⟨a₁, ha₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hAop
    obtain ⟨Wσ, hWc, -, hWlow, -, hWeq⟩ := forwardMild_memSobolev_succ (k := m) (σ := σ)
      (τ := 0) (a := max a₀ a₁)
      (A₀ := fun r ↦ correctionOperator D R m hm r (vectorLower 3 m (V r)))
      (A := fun r ↦ correctionOperator D R (m + 1) hm' r (V r))
      (f := fun r ↦ cutoffForcing D R (m + 1) r) (U := V)
      ((hA₀op.comp continuousOn_fst fun _ hp ↦ hp.1).clm_apply continuousOn_snd)
      (fun r hr ↦ (ha₀ r hr).trans (le_max_left _ _))
      ((hAop.comp continuousOn_fst fun _ hp ↦ hp.1).clm_apply continuousOn_snd)
      (fun r hr ↦ (ha₁ r hr).trans (le_max_right _ _))
      (fun r _ v ↦ vectorLower_correctionOperator D R hm hm' r (V r) v)
      (continuous_cutoffForcing D R (m + 1)).continuousOn hVc'
      (fun t ht ↦ by
        simp only [vectorLower_cutoffForcing]
        exact hVeq σ t ht.1.le ht.2)
    exact ⟨Wσ, hWc, hWlow, hWeq⟩
  choose Wσ hWc hWlow hWeq using hex
  -- Lifts from different starting times agree.
  have hagree : ∀ σ t, t ∈ Ioc σ 0 → Wσ σ t = Wσ (t - 1) t := fun σ t ht ↦
    vectorLower_injective 3 (m + 1) ((hWlow σ t ht).trans
      (hWlow (t - 1) t ⟨by linarith, ht.2⟩).symm)
  refine ⟨fun t ↦ Wσ (t - 1) t, fun t₀ ht₀ ↦ ?_, fun τ hτ ↦ ?_, fun σ τ hστ hτ ↦ ?_⟩
  · have hnhds : Ioc (t₀ - 1) 0 ∈ 𝓝[Iic 0] t₀ :=
      mem_nhdsWithin.mpr ⟨Ioi (t₀ - 1), isOpen_Ioi, by simp, fun t ht ↦ ⟨ht.1, ht.2⟩⟩
    have h₁ : ContinuousWithinAt (Wσ (t₀ - 1)) (Ioc (t₀ - 1) 0) t₀ :=
      hWc (t₀ - 1) t₀ ⟨by linarith, ht₀⟩
    exact (h₁.congr (fun t ht ↦ (hagree _ t ht).symm) rfl).mono_of_mem_nhdsWithin hnhds
  · have h := hWlow (τ - 1) τ ⟨by linarith, hτ⟩
    beta_reduce
    rw [← hVlow τ hτ, ← h, vectorLower, vectorLowerOrderCLM_trans_apply]
  · have hσ : σ ∈ Ioc (σ - 1) 0 := ⟨by linarith, hστ.trans hτ⟩
    have h := hWeq (σ - 1) σ hσ τ ⟨hστ, hτ⟩
    rw [hagree (σ - 1) τ ⟨by linarith, hτ⟩] at h
    beta_reduce
    refine h.trans (congrArg₂ (· + ·) rfl (intervalIntegral.integral_congr fun r hr ↦ ?_))
    rw [uIcc_of_le hστ] at hr
    have hr' : r ∈ Ioc (σ - 1) 0 := ⟨by linarith [hr.1], hr.2.trans hτ⟩
    simp only [liftForcing]
    rw [hagree (σ - 1) r hr', ← hWlow (r - 1) r ⟨by linarith, hr'.2⟩]

/-- **Regularity of the ancient correction at every order.** Above the threshold radius and for
`s ∈ [0, 1]`, for every order `m ≥ 2` the ancient correction is a continuous path in vector
`Hᵐ⁺¹` on `τ ≤ 0`, solving the free forward mild equation in vector `Hᵐ⁺¹`. -/
theorem exists_correctionLift (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ (m : ℕ) (hm : (3 : ℝ) < 2 * m), ∃ V : ℝ → VectorH 3 (m + 1),
      IsCorrectionLift D R s m hm V := by
  have key : ∀ k : ℕ, ∃ V : ℝ → VectorH 3 (k + 2 + 1),
      IsCorrectionLift D R s (k + 2) (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        V := by
    intro k
    induction k with
    | zero => exact ⟨_, isCorrectionLift_two hR hs _⟩
    | succ k ih =>
      obtain ⟨V, hV⟩ := ih
      exact hV.succ
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by
    have h := three_le_succ_of_three_lt_two_mul hm
    omega⟩
  exact key k

/-- Above the threshold radius and for `s ∈ [0, 1]`, at every `τ ≤ 0` the ancient correction lies
in vector `Hᵐ` for every `m ≥ 3`. -/
theorem exists_vectorLowerOrderCLM_eq_ancientCorrection (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 3 ≤ m) {τ : ℝ} (hτ : τ ≤ 0) :
    ∃ v : VectorH 3 m, vectorLowerOrderCLM hm v =
      ancientLift D.dichotomy.η (ancientCorrection D R s) τ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : (3 : ℝ) < 2 * k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    linarith
  obtain ⟨V, -, hVlow, -⟩ := exists_correctionLift hR hs k hk
  exact ⟨V τ, hVlow τ hτ⟩

end NavierStokes.Nonuniqueness
