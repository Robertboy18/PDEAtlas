/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Averaging
public import PDE.FDeriv.Laplacian.Congruence
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.MeasureTheory.Function.LocalL2
import PDE.FDeriv.Laplacian.Continuity

/-!
# Extending weak equations from symmetric tests

A weak equation that is linear in the test field and has at most second derivatives on it reads
`∫ jetDensity a b c φ = 0` with

`jetDensity a b c φ x = a(x)·φ(x) + Σⱼ bⱼ(x)·∂ⱼφ(x) + c(x)·Δφ(x)`

and locally integrable vector coefficients `a`, `bⱼ`, `c`; every linear functional of `Dφ(x)` is a
sum `Σⱼ bⱼ·∂ⱼφ`. If the coefficients transform under the axisymmetry group with the character
`s ↦ parity (odd && s)` of a sector, an equation that holds against the smooth compactly supported
solenoidal tests of that sector holds against all of them (`weak_eq_of_symmetric_tests`).

The weak self-similar profile equation of an even axisymmetric field `U ∈ L²_loc` is of this form
with `a = U`, `c = -U` and `bⱼ = (½ ξⱼ - Uⱼ) U`, all invariant, so it follows from the even
axisymmetric tests (`WeakProfileEquation.of_symmetric_tests`).

## How it works

A change of variables makes the integral equivariant,
`∫ jetDensity (act θ s φ) = parity (odd && s) * ∫ jetDensity φ` (`integral_jetDensity_act`, from the
pointwise rule `jetDensity_act_apply`). The derivatives of the rotation average are the averages of
the derivatives and the coefficients are locally integrable, so Fubini's theorem gives
`∫ jetDensity (A φ) = ∫₀¹ ∫ jetDensity (R_{2πt} φ) dt` (`integral_jetDensity_rotationAverage`). The
sector average is half the sum of the rotation average and its reflection weighted by `parity odd`,
so the two facts give `∫ jetDensity φ = ∫ jetDensity (sectorAverage odd φ)`. The sector average is a
solenoidal test field in the sector of the equation, where the equation holds by assumption. Only
smooth tests are averaged.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real Filter
open PDE.CoordinateSystems (axialRotation equatorialReflection)
open NavierStokes.Nonuniqueness
open scoped RealInnerProductSpace Interval

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

/-- The pairing `Σⱼ bⱼ·L eⱼ` of a first-order coefficient with a linear map, the general linear
functional of a matrix. -/
def firstOrderPairing (b : Fin 3 → ℝ^3) (L : ℝ^3 →L[ℝ] ℝ^3) : ℝ :=
  ∑ j, ⟪b j, L (EuclideanSpace.single j 1)⟫

/-- The density `a(x)·φ(x) + Σⱼ bⱼ(x)·∂ⱼφ(x) + c(x)·Δφ(x)` of a weak equation that is linear in
the test field and uses at most its second derivatives, with `Δ` the coordinate Laplacian. -/
def jetDensity (a : ℝ^3 → ℝ^3) (b : ℝ^3 → Fin 3 → ℝ^3) (c : ℝ^3 → ℝ^3)
    (φ : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ :=
  ⟪a x, φ x⟫ + ∑ j, ⟪b x j, PDE.partialDeriv j φ x⟫ + ⟪c x, PDE.laplacian φ x⟫

/-- The first-order part of the jet density is the pairing of the coefficient with `Dφ(x)`. -/
theorem sum_inner_partialDeriv_eq (b : Fin 3 → ℝ^3) (φ : ℝ^3 → ℝ^3) (x : ℝ^3) :
    ∑ j, ⟪b j, PDE.partialDeriv j φ x⟫ = firstOrderPairing b (fderiv ℝ φ x) :=
  rfl

variable {a c : ℝ^3 → ℝ^3} {b : ℝ^3 → Fin 3 → ℝ^3} {φ ψ : ℝ^3 → ℝ^3}

/-! ### Pointwise jet bounds -/

/-- The values, derivatives and Laplacians of all transforms of a smooth compactly supported
field are bounded uniformly, and vanish outside a common centred ball. -/
theorem exists_jet_bound (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ C R : ℝ, ∀ θ s x,
      (‖act θ s φ x‖ ≤ C ∧ ‖fderiv ℝ (act θ s φ) x‖ ≤ C ∧
        ‖PDE.laplacian (act θ s φ) x‖ ≤ C) ∧
      (R < ‖x‖ → act θ s φ x = 0 ∧ fderiv ℝ (act θ s φ) x = 0 ∧
        PDE.laplacian (act θ s φ) x = 0) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  obtain ⟨C₀, hC₀⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨C₁, hC₁⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨C₂, hC₂⟩ := hφ2.continuous_coordinate_laplacian.bounded_above_of_compact_support
    hφc.coordinate_laplacian
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℝ^3)
  refine ⟨max C₀ (max C₁ C₂), R, fun θ s x ↦ ⟨⟨?_, ?_, ?_⟩, fun hx ↦ ?_⟩⟩
  · rw [act_apply, LinearIsometryEquiv.norm_map]
    exact (hC₀ _).trans (le_max_left _ _)
  · rw [fderiv_act (hdiff _)]
    refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_).trans
      ((hC₁ ((groupElement θ s).symm x)).trans ((le_max_left _ _).trans (le_max_right _ _)))
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      (ContinuousLinearMap.opNorm_comp_le _ _) |>.trans ?_
    · exact (groupElement θ s).toLinearIsometry.norm_toContinuousLinearMap_le
    · exact mul_le_of_le_one_right (norm_nonneg _)
        (groupElement θ s).symm.toLinearIsometry.norm_toContinuousLinearMap_le
  · rw [laplacian_act hφ2, LinearIsometryEquiv.norm_map]
    exact (hC₂ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hnot : (groupElement θ s).symm x ∉ tsupport φ := by
      intro hmem
      have := hR hmem
      simp only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] at this
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [act_apply, image_eq_zero_of_notMem_tsupport hnot, map_zero]
    · rw [fderiv_act (hdiff _), fderiv_of_notMem_tsupport ℝ hnot]
      simp
    · rw [laplacian_act hφ2, EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hnot,
        map_zero]

/-! ### Integrability -/

/-- A pairing bounded by `M ‖e‖ ‖v‖` is dominated by `|M| C ‖e‖` on the closed ball `B̄(0,R)`
and vanishes outside it, when `‖v‖ ≤ C` and `v` vanishes outside the ball. -/
private theorem norm_pairing_le_indicator {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (P : E → F → ℝ) (M : ℝ) (hPb : ∀ e v, ‖P e v‖ ≤ M * ‖e‖ * ‖v‖)
    (e : ℝ^3 → E) {C R : ℝ} (y : ℝ^3) {v : F} (hC : ‖v‖ ≤ C) (hR : R < ‖y‖ → v = 0) :
    ‖P (e y) v‖ ≤ (Metric.closedBall (0 : ℝ^3) R).indicator (fun x ↦ |M| * C * ‖e x‖) y := by
  by_cases hx : y ∈ Metric.closedBall (0 : ℝ^3) R
  · rw [indicator_of_mem hx]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
    calc ‖P (e y) v‖ ≤ M * ‖e y‖ * ‖v‖ := hPb _ _
      _ ≤ |M| * ‖e y‖ * C := by
          gcongr
          exact le_abs_self M
      _ = |M| * C * ‖e y‖ := by ring
  · have hvx : v = 0 := hR (by simpa using hx)
    have h0 : P (e y) 0 = 0 := by
      have := hPb (e y) 0
      rw [norm_zero, mul_zero] at this
      exact norm_le_zero_iff.mp this
    rw [indicator_of_notMem hx, hvx, h0, norm_zero]

/-- The dominating function `|M| C ‖e‖` on a closed ball of a locally integrable field is
integrable. -/
private theorem integrable_indicator_closedBall {E : Type*} [NormedAddCommGroup E] {e : ℝ^3 → E}
    (he : LocallyIntegrable (fun x ↦ ‖e x‖) volume) (M C R : ℝ) :
    Integrable ((Metric.closedBall (0 : ℝ^3) R).indicator fun x ↦ |M| * C * ‖e x‖) :=
  IntegrableOn.integrable_indicator
    ((he.integrableOn_isCompact (isCompact_closedBall 0 R)).const_mul (|M| * C))
    measurableSet_closedBall

/-- A pairing bounded by `M ‖e‖ ‖v‖` of a locally integrable field with a bounded field that
vanishes outside a ball is integrable. -/
private theorem integrable_pairing {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : E → F → ℝ) (hP : Continuous (Function.uncurry P)) (M : ℝ)
    (hPb : ∀ e v, ‖P e v‖ ≤ M * ‖e‖ * ‖v‖) {e : ℝ^3 → E}
    (hem : AEStronglyMeasurable e volume) (he : LocallyIntegrable (fun x ↦ ‖e x‖) volume)
    {v : ℝ^3 → F} (hv : AEStronglyMeasurable v volume) {C R : ℝ} (hC : ∀ x, ‖v x‖ ≤ C)
    (hR : ∀ x, R < ‖x‖ → v x = 0) :
    Integrable (fun x ↦ P (e x) (v x)) :=
  (integrable_indicator_closedBall he M C R).mono' (hP.comp_aestronglyMeasurable₂ hem hv)
    (Eventually.of_forall fun x ↦ norm_pairing_le_indicator P M hPb e x (hC x) (hR x))

/-- Local integrability of the coefficients of a jet density: each coefficient is almost
everywhere strongly measurable with locally integrable norm. -/
structure IsLocallyIntegrableJet (a : ℝ^3 → ℝ^3) (b : ℝ^3 → Fin 3 → ℝ^3)
    (c : ℝ^3 → ℝ^3) : Prop where
  /-- The zeroth-order coefficient is measurable. -/
  measurable_a : AEStronglyMeasurable a volume
  /-- The first-order coefficients are measurable. -/
  measurable_b : ∀ j, AEStronglyMeasurable (fun x ↦ b x j) volume
  /-- The second-order coefficient is measurable. -/
  measurable_c : AEStronglyMeasurable c volume
  /-- The zeroth-order coefficient is locally integrable. -/
  integrable_a : LocallyIntegrable (fun x ↦ ‖a x‖) volume
  /-- The first-order coefficients are locally integrable. -/
  integrable_b : ∀ j, LocallyIntegrable (fun x ↦ ‖b x j‖) volume
  /-- The second-order coefficient is locally integrable. -/
  integrable_c : LocallyIntegrable (fun x ↦ ‖c x‖) volume

/-- The Euclidean inner product is continuous and bounded by the product of the norms. -/
private theorem inner_pairing_facts :
    Continuous (Function.uncurry fun e v : ℝ^3 ↦ ⟪e, v⟫) ∧
      ∀ e v : ℝ^3, ‖⟪e, v⟫‖ ≤ 1 * ‖e‖ * ‖v‖ :=
  ⟨continuous_inner, fun e v ↦ by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_real_inner_le_norm e v⟩

/-- The partial derivatives of a smooth field are bounded by the norm of its derivative. -/
private theorem norm_partialDeriv_le' (φ : ℝ^3 → ℝ^3) (j : Fin 3) (x : ℝ^3) :
    ‖PDE.partialDeriv j φ x‖ ≤ ‖fderiv ℝ φ x‖ := by
  unfold PDE.partialDeriv
  refine ((fderiv ℝ φ x).le_opNorm _).trans ?_
  simp

/-- The jet density of a smooth compactly supported field with locally integrable coefficients
is integrable. -/
theorem integrable_jetDensity (hJ : IsLocallyIntegrableJet a b c)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (jetDensity a b c φ) := by
  obtain ⟨C, R, hCR⟩ := exists_jet_bound hφ hφc
  have hb (x : ℝ^3) : ‖φ x‖ ≤ C ∧ ‖fderiv ℝ φ x‖ ≤ C ∧ ‖PDE.laplacian φ x‖ ≤ C := by
    have h := (hCR 0 false x).1
    rwa [act_zero_false] at h
  have hz (x : ℝ^3) (hx : R < ‖x‖) :
      φ x = 0 ∧ fderiv ℝ φ x = 0 ∧ PDE.laplacian φ x = 0 := by
    have h := (hCR 0 false x).2 hx
    rwa [act_zero_false] at h
  obtain ⟨hinner, hinner_le⟩ := inner_pairing_facts
  have h0 : Integrable (fun x ↦ ⟪a x, φ x⟫) :=
    integrable_pairing (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le hJ.measurable_a
      hJ.integrable_a hφ.continuous.aestronglyMeasurable (fun x ↦ (hb x).1)
      (fun x hx ↦ (hz x hx).1)
  have h1 (j : Fin 3) : Integrable (fun x ↦ ⟪b x j, PDE.partialDeriv j φ x⟫) := by
    have hcont : Continuous (fun x ↦ PDE.partialDeriv j φ x) :=
      (hφ.partialDeriv j (k := 0) (hkr := by simp)).continuous
    exact integrable_pairing (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le (hJ.measurable_b j)
      (hJ.integrable_b j) hcont.aestronglyMeasurable
      (fun x ↦ (norm_partialDeriv_le' φ j x).trans (hb x).2.1)
      (fun x hx ↦ by rw [PDE.partialDeriv, (hz x hx).2.1, zero_apply])
  have hlap : Continuous (PDE.laplacian φ) :=
    (hφ.of_le (by simp) : ContDiff ℝ 2 φ).continuous_coordinate_laplacian
  have h2 : Integrable (fun x ↦ ⟪c x, PDE.laplacian φ x⟫) :=
    integrable_pairing (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le hJ.measurable_c
      hJ.integrable_c hlap.aestronglyMeasurable (fun x ↦ (hb x).2.2)
      (fun x hx ↦ (hz x hx).2.2)
  have h1' : Integrable (fun x ↦ ∑ j, ⟪b x j, PDE.partialDeriv j φ x⟫) :=
    integrable_finsetSum _ fun j _ ↦ h1 j
  refine ((h0.add h1').add h2).congr (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply]
  rfl

/-! ### Equivariance -/

/-- The coefficients of a jet density transform under the axisymmetry group with the character
`s ↦ parity (odd && s)`: `a(g y) = χ g a(y)`, `c(g y) = χ g c(y)`, and the first-order pairing
satisfies `b(g y)(g L g⁻¹) = χ b(y)(L)`, almost everywhere. -/
structure IsEquivariantJet (odd : Bool) (a : ℝ^3 → ℝ^3) (b : ℝ^3 → Fin 3 → ℝ^3)
    (c : ℝ^3 → ℝ^3) : Prop where
  /-- Equivariance of the zeroth-order coefficient. -/
  a_comp : ∀ θ s, ∀ᵐ y ∂volume,
    a (groupElement θ s y) = parity (odd && s) • groupElement θ s (a y)
  /-- Equivariance of the first-order coefficient. -/
  b_comp : ∀ θ s, ∀ᵐ y ∂volume, ∀ L : ℝ^3 →L[ℝ] ℝ^3,
    firstOrderPairing (b (groupElement θ s y)) ((groupCLM θ s).comp (L.comp (groupInvCLM θ s))) =
      parity (odd && s) * firstOrderPairing (b y) L
  /-- Equivariance of the second-order coefficient. -/
  c_comp : ∀ θ s, ∀ᵐ y ∂volume,
    c (groupElement θ s y) = parity (odd && s) • groupElement θ s (c y)

/-- Pointwise transformation of the jet density under the action. -/
theorem jetDensity_act_apply (hφ : ContDiff ℝ 2 φ) (θ : ℝ) (s : Bool) (y : ℝ^3) {χ : ℝ}
    (ha : a (groupElement θ s y) = χ • groupElement θ s (a y))
    (hb : ∀ L : ℝ^3 →L[ℝ] ℝ^3, firstOrderPairing (b (groupElement θ s y))
      ((groupCLM θ s).comp (L.comp (groupInvCLM θ s))) = χ * firstOrderPairing (b y) L)
    (hc : c (groupElement θ s y) = χ • groupElement θ s (c y)) :
    jetDensity a b c (act θ s φ) (groupElement θ s y) = χ * jetDensity a b c φ y := by
  have hd : DifferentiableAt ℝ φ ((groupElement θ s).symm (groupElement θ s y)) := by
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact (hφ.differentiable (by simp)) y
  unfold jetDensity
  rw [sum_inner_partialDeriv_eq, sum_inner_partialDeriv_eq, fderiv_act hd, laplacian_act hφ,
    act_apply, LinearIsometryEquiv.symm_apply_apply, ha, hc, hb, real_inner_smul_left,
    real_inner_smul_left, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  ring

/-- The integral of the jet density is equivariant with the character of the sector. -/
theorem integral_jetDensity_act {odd : Bool} (hJ : IsEquivariantJet odd a b c)
    (hφ : ContDiff ℝ 2 φ) (θ : ℝ) (s : Bool) :
    ∫ x, jetDensity a b c (act θ s φ) x = parity (odd && s) * ∫ x, jetDensity a b c φ x := by
  rw [← integral_comp_groupElement θ s, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hJ.a_comp θ s, hJ.b_comp θ s, hJ.c_comp θ s] with y ha hb hc
  exact jetDensity_act_apply hφ θ s y ha hb hc

/-! ### Averaging the jet density -/

/-- The jet density of the rotation average is the average of the jet densities of the rotated
fields. -/
theorem jetDensity_rotationAverage (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ^3) :
    jetDensity a b c (rotationAverage φ) x =
      ∫ t in (0 : ℝ)..1, jetDensity a b c (act (2 * π * t) false φ) x := by
  have hfam := contDiff_rotationFamily hφ
  have hline : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prodMk continuous_id
  have hv : Continuous (fun t ↦ rotationFamily φ (x, t)) := by
    have h := hfam.continuous.comp hline
    exact h
  have hp (j : Fin 3) : Continuous
      (fun t ↦ PDE.partialDeriv j (fun y ↦ rotationFamily φ (y, t)) x) := by
    have h := (PDE.Calculus.contDiff_partialDeriv_slice hfam j).continuous.comp hline
    exact h
  have hl : Continuous (fun t ↦ PDE.laplacian (fun y ↦ rotationFamily φ (y, t)) x) := by
    have h := (PDE.Calculus.continuous_laplacian_slice hfam).comp hline
    exact h
  have hA : IntervalIntegrable (fun t ↦ ⟪a x, rotationFamily φ (x, t)⟫) volume 0 1 :=
    ((innerSL ℝ (a x)).continuous.comp hv).intervalIntegrable 0 1
  have hB (j : Fin 3) : IntervalIntegrable
      (fun t ↦ ⟪b x j, PDE.partialDeriv j (fun y ↦ rotationFamily φ (y, t)) x⟫) volume 0 1 :=
    ((innerSL ℝ (b x j)).continuous.comp (hp j)).intervalIntegrable 0 1
  have hB' : IntervalIntegrable (fun t ↦ ∑ j,
      ⟪b x j, PDE.partialDeriv j (fun y ↦ rotationFamily φ (y, t)) x⟫) volume 0 1 := by
    have h := IntervalIntegrable.sum Finset.univ fun j _ ↦ hB j
    refine h.congr fun t _ ↦ ?_
    simp only [Finset.sum_apply]
  have hC : IntervalIntegrable
      (fun t ↦ ⟪c x, PDE.laplacian (fun y ↦ rotationFamily φ (y, t)) x⟫) volume 0 1 :=
    ((innerSL ℝ (c x)).continuous.comp hl).intervalIntegrable 0 1
  have hslice (t : ℝ) : (fun y ↦ rotationFamily φ (y, t)) = act (2 * π * t) false φ := rfl
  have hrhs : (fun t ↦ jetDensity a b c (act (2 * π * t) false φ) x) =
      fun t ↦ ⟪a x, rotationFamily φ (x, t)⟫ +
        ∑ j, ⟪b x j, PDE.partialDeriv j (fun y ↦ rotationFamily φ (y, t)) x⟫ +
        ⟪c x, PDE.laplacian (fun y ↦ rotationFamily φ (y, t)) x⟫ := by
    funext t
    rw [hslice]
    rfl
  rw [hrhs, intervalIntegral.integral_add (hA.add hB') hC, intervalIntegral.integral_add hA hB',
    intervalIntegral.integral_finsetSum fun j _ ↦ hB j]
  unfold jetDensity
  rw [rotationAverage_eq, PDE.Calculus.laplacian_intervalAverage hfam]
  simp only [PDE.Calculus.partialDeriv_intervalAverage hfam]
  rw [← innerSL_apply_apply ℝ (a x), ← (innerSL ℝ (a x)).intervalIntegral_comp_comm
      (hv.intervalIntegrable 0 1),
    ← innerSL_apply_apply ℝ (c x), ← (innerSL ℝ (c x)).intervalIntegral_comp_comm
      (hl.intervalIntegrable 0 1)]
  congr 2
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← innerSL_apply_apply ℝ (b x j), ← (innerSL ℝ (b x j)).intervalIntegral_comp_comm
    ((hp j).intervalIntegrable 0 1)]
  rfl

/-- A pairing bounded by `M ‖e‖ ‖v‖` of a locally integrable field of the space variable with a
continuous bounded field of time and space that vanishes outside a ball is integrable on the
product with a finite measure in time. -/
private theorem integrable_pairing_prod {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (P : E → F → ℝ) (hP : Continuous (Function.uncurry P)) (M : ℝ)
    (hPb : ∀ e v, ‖P e v‖ ≤ M * ‖e‖ * ‖v‖) {e : ℝ^3 → E}
    (hem : AEStronglyMeasurable e volume) (he : LocallyIntegrable (fun x ↦ ‖e x‖) volume)
    {v : ℝ × ℝ^3 → F} (hv : Continuous v) {C R : ℝ} (hC : ∀ p, ‖v p‖ ≤ C)
    (hR : ∀ p : ℝ × ℝ^3, R < ‖p.2‖ → v p = 0) :
    Integrable (fun p : ℝ × ℝ^3 ↦ P (e p.2) (v p)) (μ.prod volume) := by
  have hem' : AEStronglyMeasurable (fun p : ℝ × ℝ^3 ↦ e p.2) (μ.prod volume) :=
    hem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  exact ((integrable_indicator_closedBall he M C R).comp_snd μ).mono'
    (hP.comp_aestronglyMeasurable₂ hem' hv.aestronglyMeasurable)
    (Eventually.of_forall fun p ↦ norm_pairing_le_indicator P M hPb e p.2 (hC p) (hR p))

/-- The jet densities of the rotated fields are integrable jointly in the angle parameter and
the point. -/
theorem integrable_jetDensity_rotationFamily (hJ : IsLocallyIntegrableJet a b c)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (Function.uncurry fun t x ↦ jetDensity a b c (act (2 * π * t) false φ) x)
      ((volume.restrict (Ι (0 : ℝ) 1)).prod volume) := by
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) 1)) := by
    rw [uIoc_of_le zero_le_one]
    infer_instance
  have hfam := contDiff_rotationFamily hφ
  obtain ⟨C, R, hCR⟩ := exists_jet_bound hφ hφc
  obtain ⟨hinner, hinner_le⟩ := inner_pairing_facts
  have hv0 : Continuous (fun p : ℝ × ℝ^3 ↦ act (2 * π * p.1) false φ p.2) := by
    have h := hfam.continuous.comp continuous_swap
    exact h
  have hv1 (j : Fin 3) : Continuous
      (fun p : ℝ × ℝ^3 ↦ PDE.partialDeriv j (act (2 * π * p.1) false φ) p.2) := by
    have h := (PDE.Calculus.contDiff_partialDeriv_slice hfam j).continuous.comp continuous_swap
    exact h
  have hv2 : Continuous (fun p : ℝ × ℝ^3 ↦ PDE.laplacian (act (2 * π * p.1) false φ) p.2) := by
    have h := (PDE.Calculus.continuous_laplacian_slice hfam).comp continuous_swap
    exact h
  have h0 : Integrable (fun p : ℝ × ℝ^3 ↦ ⟪a p.2, act (2 * π * p.1) false φ p.2⟫)
      ((volume.restrict (Ι (0 : ℝ) 1)).prod volume) :=
    integrable_pairing_prod _ (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le hJ.measurable_a
      hJ.integrable_a hv0 (fun p ↦ (hCR _ false p.2).1.1)
      (fun p hp ↦ ((hCR _ false p.2).2 hp).1)
  have h1 (j : Fin 3) : Integrable
      (fun p : ℝ × ℝ^3 ↦ ⟪b p.2 j, PDE.partialDeriv j (act (2 * π * p.1) false φ) p.2⟫)
      ((volume.restrict (Ι (0 : ℝ) 1)).prod volume) :=
    integrable_pairing_prod _ (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le (hJ.measurable_b j)
      (hJ.integrable_b j) (hv1 j)
      (fun p ↦ (norm_partialDeriv_le' _ j p.2).trans (hCR _ false p.2).1.2.1)
      (fun p hp ↦ by rw [PDE.partialDeriv, ((hCR _ false p.2).2 hp).2.1, zero_apply])
  have h2 : Integrable (fun p : ℝ × ℝ^3 ↦ ⟪c p.2, PDE.laplacian (act (2 * π * p.1) false φ) p.2⟫)
      ((volume.restrict (Ι (0 : ℝ) 1)).prod volume) :=
    integrable_pairing_prod _ (fun e v : ℝ^3 ↦ ⟪e, v⟫) hinner 1 hinner_le hJ.measurable_c
      hJ.integrable_c hv2 (fun p ↦ (hCR _ false p.2).1.2.2)
      (fun p hp ↦ ((hCR _ false p.2).2 hp).2.2)
  have h1' := integrable_finsetSum Finset.univ fun j _ ↦ h1 j
  refine ((h0.add h1').add h2).congr (Eventually.of_forall fun p ↦ ?_)
  simp only [Pi.add_apply]
  rfl

/-- Fubini's theorem for the rotation average: the integral of the jet density of the average
is the average over the angle of the integrals of the jet densities of the rotated fields. -/
theorem integral_jetDensity_rotationAverage (hJ : IsLocallyIntegrableJet a b c)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, jetDensity a b c (rotationAverage φ) x =
      ∫ t in (0 : ℝ)..1, ∫ x, jetDensity a b c (act (2 * π * t) false φ) x := by
  simp only [jetDensity_rotationAverage hφ]
  exact (intervalIntegral_integral_swap (integrable_jetDensity_rotationFamily hJ hφ hφc)).symm

/-! ### Extension to all tests -/

/-- The jet density is additive in `C²` test fields. -/
theorem jetDensity_add {u v : ℝ^3 → ℝ^3} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : ℝ^3) : jetDensity a b c (u + v) x = jetDensity a b c u x + jetDensity a b c v x := by
  have hud : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
  have hvd : DifferentiableAt ℝ v x := (hv.differentiable (by simp)) x
  have huv : ContDiffAt ℝ 2 (u + v) x := by
    rw [Pi.add_def]
    exact (hu.add hv).contDiffAt
  have hlap : PDE.laplacian (u + v) x = PDE.laplacian u x + PDE.laplacian v x := by
    rw [huv.coordinate_laplacian_eq_laplacian,
      hu.contDiffAt.coordinate_laplacian_eq_laplacian,
      hv.contDiffAt.coordinate_laplacian_eq_laplacian,
      hu.contDiffAt.laplacian_add hv.contDiffAt]
  have hpart (j : Fin 3) :
      PDE.partialDeriv j (u + v) x = PDE.partialDeriv j u x + PDE.partialDeriv j v x :=
    PDE.partialDeriv_add hud hvd
  unfold jetDensity
  simp only [hlap, hpart, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
  ring

/-- The jet density is homogeneous in `C²` test fields. -/
theorem jetDensity_smul (r : ℝ) {u : ℝ^3 → ℝ^3} (hu : ContDiff ℝ 2 u) (x : ℝ^3) :
    jetDensity a b c (r • u) x = r * jetDensity a b c u x := by
  have hru : ContDiffAt ℝ 2 (r • u) x := by
    rw [Pi.smul_def]
    exact (hu.const_smul r).contDiffAt
  have hlap : PDE.laplacian (r • u) x = r • PDE.laplacian u x := by
    rw [hru.coordinate_laplacian_eq_laplacian,
      hu.contDiffAt.coordinate_laplacian_eq_laplacian,
      InnerProductSpace.laplacian_smul r hu.contDiffAt]
  have hpart (j : Fin 3) : PDE.partialDeriv j (r • u) x = r • PDE.partialDeriv j u x :=
    PDE.partialDeriv_const_smul r
  unfold jetDensity
  simp only [hlap, hpart, Pi.smul_apply, real_inner_smul_right]
  rw [← Finset.mul_sum]
  ring

/-- A weak equation with jet density whose coefficients are locally integrable and equivariant
with the character of a sector, and which holds against the smooth compactly supported
solenoidal tests of that sector, holds against all smooth compactly supported solenoidal
tests. -/
theorem weak_eq_of_symmetric_tests (odd : Bool) (hL : IsLocallyIntegrableJet a b c)
    (hE : IsEquivariantJet odd a b c)
    (htest : ∀ ψ, IsSolenoidalTestField ψ → IsInSector odd ψ → ∫ x, jetDensity a b c ψ x = 0)
    (φ : ℝ^3 → ℝ^3) (hφ : IsSolenoidalTestField φ) :
    Integrable (jetDensity a b c φ) ∧ ∫ x, jetDensity a b c φ x = 0 := by
  refine ⟨integrable_jetDensity hL hφ.1 hφ.2.1, ?_⟩
  have hψ : IsSolenoidalTestField (rotationAverage φ) := hφ.rotationAverage
  have hψ' : IsSolenoidalTestField (act 0 true (rotationAverage φ)) := hψ.act 0 true
  have h2 {u : ℝ^3 → ℝ^3} (hu : IsSolenoidalTestField u) : ContDiff ℝ 2 u := hu.1.of_le (by simp)
  have hint {u : ℝ^3 → ℝ^3} (hu : IsSolenoidalTestField u) : Integrable (jetDensity a b c u) :=
    integrable_jetDensity hL hu.1 hu.2.1
  have hlin (x : ℝ^3) : jetDensity a b c (sectorAverage odd φ) x =
      (1 / 2) * (jetDensity a b c (rotationAverage φ) x +
        parity odd * jetDensity a b c (act 0 true (rotationAverage φ)) x) := by
    rw [sectorAverage, jetDensity_smul _ (h2 (hψ.add (hψ'.smul (parity odd)))),
      jetDensity_add (h2 hψ) (h2 (hψ'.smul (parity odd))), jetDensity_smul _ (h2 hψ')]
  have hsector := htest _ (hφ.sectorAverage odd) (isInSector_sectorAverage hφ.1 odd)
  simp only [hlin] at hsector
  rw [integral_const_mul, integral_add (hint hψ) ((hint hψ').const_mul _), integral_const_mul,
    integral_jetDensity_act hE (h2 hψ) 0 true, Bool.and_true,
    integral_jetDensity_rotationAverage hL hφ.1 hφ.2.1] at hsector
  have hrot (t : ℝ) : ∫ x, jetDensity a b c (act (2 * π * t) false φ) x =
      ∫ x, jetDensity a b c φ x := by
    rw [integral_jetDensity_act hE (h2 hφ), Bool.and_false, parity_false, one_mul]
  simp only [hrot, intervalIntegral.integral_const, sub_zero, one_smul] at hsector
  have hsq : parity odd * parity odd = 1 := parity_mul_self odd
  have : (1 / 2 : ℝ) * ((1 + parity odd * parity odd) * ∫ x, jetDensity a b c φ x) = 0 := by
    rw [← hsector]
    ring
  rw [hsq] at this
  linarith

/-! ### The weak profile equation -/

/-- The first-order coefficient of the weak profile equation, `bⱼ(ξ) = (½ ξⱼ - Uⱼ(ξ)) U(ξ)`. -/
def profileFirstOrder (U : ℝ^3 → ℝ^3) (x : ℝ^3) (j : Fin 3) : ℝ^3 :=
  ((1 / 2 : ℝ) * x j - U x j) • U x

/-- The first-order pairing of the profile coefficient is `½ U·L ξ - U·L U`. -/
theorem firstOrderPairing_profileFirstOrder (U : ℝ^3 → ℝ^3) (x : ℝ^3) (L : ℝ^3 →L[ℝ] ℝ^3) :
    firstOrderPairing (profileFirstOrder U x) L = (1 / 2 : ℝ) * ⟪U x, L x⟫ - ⟪U x, L (U x)⟫ := by
  rw [EuclideanSpace.map_eq_sum_smul_single L x, EuclideanSpace.map_eq_sum_smul_single L (U x)]
  simp only [firstOrderPairing, profileFirstOrder, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The weak profile density is the jet density with coefficients `U`, `profileFirstOrder U`
and `-U`. -/
theorem weakProfileDensity_eq_jetDensity (U φ : ℝ^3 → ℝ^3) (x : ℝ^3) :
    weakProfileDensity U φ x = jetDensity U (profileFirstOrder U) (-U) φ x := by
  rw [jetDensity, sum_inner_partialDeriv_eq, firstOrderPairing_profileFirstOrder,
    weakProfileDensity, Pi.neg_apply, inner_neg_left]
  ring

/-- The coefficients of the weak profile equation of an even axisymmetric field are invariant. -/
theorem isEquivariantJet_profile {U : ℝ^3 → ℝ^3} (hU : IsEvenAxisymmetric U) :
    IsEquivariantJet false U (profileFirstOrder U) (-U) := by
  refine ⟨fun θ s ↦ ?_, fun θ s ↦ ?_, fun θ s ↦ ?_⟩
  · filter_upwards [hU.ae_comp_groupElement θ s] with y hy
    rw [hy, Bool.false_and, parity_false, one_smul]
  · filter_upwards [hU.ae_comp_groupElement θ s] with y hy L
    rw [Bool.false_and, parity_false, one_mul, firstOrderPairing_profileFirstOrder,
      firstOrderPairing_profileFirstOrder, hy]
    simp only [ContinuousLinearMap.comp_apply, groupCLM_apply, groupInvCLM_apply,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  · filter_upwards [hU.ae_comp_groupElement θ s] with y hy
    rw [Pi.neg_apply, Pi.neg_apply, hy, Bool.false_and, parity_false, one_smul, map_neg]

/-- The coefficients of the weak profile equation of a field in `L²_loc` are locally
integrable. -/
theorem isLocallyIntegrableJet_profile {U : ℝ^3 → ℝ^3} (hUm : AEStronglyMeasurable U volume)
    (hU2 : LocallyIntegrable (fun x ↦ ‖U x‖ ^ 2) volume) :
    IsLocallyIntegrableJet U (profileFirstOrder U) (-U) := by
  have hU1 : LocallyIntegrable (fun x ↦ ‖U x‖) volume := locallyIntegrable_norm_of_sq hUm hU2
  have hcomp (j : Fin 3) : AEStronglyMeasurable (fun x ↦ U x j) volume :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hUm
  have hcoord (j : Fin 3) : Continuous (fun x : ℝ^3 ↦ (1 / 2 : ℝ) * x j) :=
    continuous_const.mul (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hmb (j : Fin 3) : AEStronglyMeasurable (fun x ↦ profileFirstOrder U x j) volume :=
    ((hcoord j).aestronglyMeasurable.sub (hcomp j)).smul hUm
  refine ⟨hUm, hmb, hUm.neg, hU1, fun j ↦ ?_, by simpa only [Pi.neg_apply, norm_neg] using hU1⟩
  have hdom : LocallyIntegrable (fun x ↦ ‖x‖ * ‖U x‖ + ‖U x‖ ^ 2) volume :=
    (hU1.continuous_mul continuous_norm).add hU2
  refine hdom.mono (hmb j).norm (Eventually.of_forall fun x ↦ ?_)
  have hxj : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hUj : |U x j| ≤ ‖U x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (U x) j
  rw [norm_norm, Real.norm_of_nonneg (by positivity), profileFirstOrder, norm_smul,
    Real.norm_eq_abs]
  calc |(1 / 2 : ℝ) * x j - U x j| * ‖U x‖ ≤ (‖x‖ + ‖U x‖) * ‖U x‖ := by
        gcongr
        calc |(1 / 2 : ℝ) * x j - U x j| ≤ |(1 / 2 : ℝ) * x j| + |U x j| := abs_sub _ _
          _ ≤ ‖x‖ + ‖U x‖ := by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
              linarith [abs_nonneg (x j)]
    _ = ‖x‖ * ‖U x‖ + ‖U x‖ ^ 2 := by ring

/-- The weak self-similar profile equation of an even axisymmetric field in `L²_loc` follows
from the equation tested only with even axisymmetric smooth compactly supported solenoidal
fields. -/
theorem _root_.NavierStokes.Nonuniqueness.WeakProfileEquation.of_symmetric_tests
    {U : ℝ^3 → ℝ^3} (hU : IsEvenAxisymmetric U) (hUm : AEStronglyMeasurable U volume)
    (hU2 : LocallyIntegrable (fun x ↦ ‖U x‖ ^ 2) volume)
    (htest : ∀ φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      ∫ x, weakProfileDensity U φ x = 0) :
    WeakProfileEquation U := by
  have hdens (φ : ℝ^3 → ℝ^3) :
      weakProfileDensity U φ = jetDensity U (profileFirstOrder U) (-U) φ :=
    funext (weakProfileDensity_eq_jetDensity U φ)
  intro φ hφ
  rw [hdens]
  refine weak_eq_of_symmetric_tests false (isLocallyIntegrableJet_profile hUm hU2)
    (isEquivariantJet_profile hU) (fun ψ hψ hsec ↦ ?_) φ hφ
  rw [← hdens]
  exact htest ψ hψ (isInSector_false_iff.mp hsec)

end NavierStokes.Symmetry
