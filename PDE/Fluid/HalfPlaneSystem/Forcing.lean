/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Law
public import PDE.Fluid.Boussinesq.HalfPlane.CarriedBounds
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# The weighted forcing of the vorticity equation in label form

The vorticity equation `ω_t + u · ∇ω = κ(x) ∂₀θ` of a half-plane system has the forcing `κ(x) ∂₀θ`,
with `κ` the forcing coefficient (`κ = 1` for Boussinesq, `κ = r⁻⁴` for axisymmetric Euler near the
wall). This module writes the forcing along a particle in terms of the data and of the flow,
differentiates it in the label of the particle, and bounds it and its derivative. The answers give
the vorticity as an explicit time integral.

Along the particle of label `y` the forcing is `G_κ(y, r) = κ(X(r, y)) Dθ₀(y) (W e₀)`
(`weightedForcing`), the label forcing of `PDE.Hyperbolic.Transport.labelForcing` multiplied by the
coefficient at the particle. Its derivative in the label is `κ(X) DG + G Dκ(X) ∘ DX`
(`weightedForcingDeriv`), where `DX` is the first variation of `y ↦ X(r, y)`. The Eulerian forms are
`weightedForcing_eq` and the forced transport equation `hasDerivAt_forcedAmplitude_weightedForcing`.

On the closed half-plane, for a field with the flow bounds `Boussinesq.HalfPlane.IsBoundedFlowOn`
and data of the class `Boussinesq.HalfPlane.IsHolderData`, the forcing, its derivative and the
Hölder constant of the derivative are bounded, and so is the amplitude
`Ω(y, t) = ω̃₀(y) + ∫₀ᵗ G_κ(y, r) dr` with its derivative in the label. These extend the bounds of
`PDE.Fluid.Boussinesq.HalfPlane.CarriedBounds` to the weighted forcing. The flow bounds are
hypotheses here, and the constants, sums and products of the bounds of the coefficient and of the
flow, are not optimized.

## Main results

* `weightedForcing`, `weightedForcingDeriv`: the forcing and its derivative in the label;
  `hasFDerivAt_weightedForcing`: for a `C²` field, a differentiable coefficient and `C²` temperature
  data, the forcing is differentiable in the label with this derivative.
* `weightedForcing_eq`: at the label of the particle at `x` the forcing is `κ(x)` times the
  derivative in the direction `e` of the carried quantity at `x`.
* `contDiffOn_forcedAmplitude_weightedForcing`, `hasDerivAt_forcedAmplitude_weightedForcing`: the
  Eulerian amplitude is jointly `C¹` and solves the forced transport equation `w_t + Dw v = κ Dθ e`
  at every point and every time of `(a, b)`.
* `IsForcingCoefficient.abs_le`, `IsForcingCoefficient.norm_fderiv_le`,
  `IsForcingCoefficient.abs_sub_le`, `IsForcingCoefficient.norm_fderiv_sub_le`,
  `IsForcingCoefficient.bound_nonneg`: the bounds `Bκ 0`, `Bκ 1`, `Bκ 2` of a forcing coefficient
  and of its derivatives, and the Lipschitz bounds that follow.
* `IsBoundedFlowOn.abs_weightedForcing_le`, `IsBoundedFlowOn.norm_weightedForcingDeriv_le`,
  `IsBoundedFlowOn.norm_weightedForcingDeriv_sub_le`: on the closed half-plane the forcing is at
  most `weightedForcingBound`, its derivative in the label at most `weightedForcingDerivBound`, and
  the derivative is `α`-Hölder with the constant `weightedForcingDerivHolderConst`.
* `hasFDerivAt_weightedAmplitude`, `contDiff_weightedAmplitude` and the bounds
  `IsBoundedFlowOn.abs_weightedAmplitude_le`, `IsBoundedFlowOn.norm_fderiv_weightedAmplitude_le`,
  `IsBoundedFlowOn.norm_fderiv_weightedAmplitude_sub_le`,
  `IsBoundedFlowOn.abs_weightedAmplitude_sub_le`,
  `IsBoundedFlowOn.abs_weightedAmplitude_time_sub_le`,
  `IsBoundedFlowOn.norm_fderiv_weightedAmplitude_time_sub_le`: the amplitude is `C¹` in the label;
  its size, its derivative, the Hölder constant of the derivative and its changes in the label and
  in time are bounded.

`CarriedVorticity.lean` defines the carried vorticity as the amplitude at the label and transfers
these bounds to it, and `Solution.lean` uses the forced transport equation to show that the carried
fields solve the system. The bounds of the coefficient are used throughout the folder.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The weighted forcing -/

/-- The weighted forcing at the label `y` and the time `r`: the forcing coefficient at the
particle of label `y` times the label forcing. -/
def weightedForcing (v : ℝ → ℝ^2 → ℝ^2) (Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2) (a b : ℝ)
    (κ θ₀ : ℝ^2 → ℝ) (e y : ℝ^2) (r : ℝ) : ℝ :=
  κ (flowOn v a b r 0 y) * labelForcing v Dv a b θ₀ e y r

/-- The derivative in the label of the weighted forcing. -/
def weightedForcingDeriv (v : ℝ → ℝ^2 → ℝ^2) (Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2)
    (D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) (a b : ℝ) (κ θ₀ : ℝ^2 → ℝ) (e y : ℝ^2)
    (r : ℝ) : ℝ^2 →L[ℝ] ℝ :=
  κ (flowOn v a b r 0 y) • labelForcingDeriv v Dv D2v a b θ₀ e y r +
    labelForcing v Dv a b θ₀ e y r • (fderiv ℝ κ (flowOn v a b r 0 y)).comp
      (variationOn v Dv a b r 0 y)

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b : ℝ} {K K₂ : ℝ≥0} {κ θ₀ : ℝ^2 → ℝ}
  {e : ℝ^2}

/-- The particle of label `y` at time `r` depends continuously on `(y, r)`. -/
theorem continuousOn_flowOn_label_time (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b) :
    ContinuousOn (fun p : ℝ^2 × ℝ ↦ flowOn v a b p.2 0 p.1) (univ ×ˢ Icc a b) :=
  hv.isLipschitzFieldOn.continuousOn_flowOn.comp (f := fun p : ℝ^2 × ℝ ↦ (p.2, 0, p.1))
    (continuous_snd.prodMk (continuous_const.prodMk continuous_fst)).continuousOn
    fun _ hp ↦ ⟨hp.2, h0, mem_univ _⟩

/-- The weighted forcing is jointly continuous on `ℝ² × [a, b]`. -/
theorem continuousOn_weightedForcing (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hκ : Continuous κ) (hθ₀ : ContDiff ℝ 1 θ₀) :
    ContinuousOn (fun p : ℝ^2 × ℝ ↦ weightedForcing v Dv a b κ θ₀ e p.1 p.2)
      (univ ×ˢ Icc a b) :=
  (hκ.comp_continuousOn (continuousOn_flowOn_label_time hv h0)).mul
    (continuousOn_labelForcing hv h0 hθ₀)

/-- **The weighted forcing is `C¹` in the label**, with derivative `weightedForcingDeriv`. -/
theorem hasFDerivAt_weightedForcing (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hκ : Differentiable ℝ κ) (hθ₀ : ContDiff ℝ 2 θ₀) {r : ℝ}
    (hr : r ∈ Icc a b) (y : ℝ^2) :
    HasFDerivAt (fun z ↦ weightedForcing v Dv a b κ θ₀ e z r)
      (weightedForcingDeriv v Dv D2v a b κ θ₀ e y r) y := by
  have hX : HasFDerivAt (fun z ↦ flowOn v a b r 0 z) (variationOn v Dv a b r 0 y) y :=
    hv.toIsC1FieldOn.hasFDerivAt_flowOn hr h0 y
  have hκX := (hκ (flowOn v a b r 0 y)).hasFDerivAt.comp y hX
  have hG := hasFDerivAt_labelForcing (e := e) hv h0 hθ₀ hr y
  exact hκX.mul hG

/-- The derivative of the weighted forcing in the label is jointly continuous. -/
theorem continuousOn_weightedForcingDeriv (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hκ : ContDiff ℝ 1 κ) (hθ₀ : ContDiff ℝ 2 θ₀) :
    ContinuousOn (fun p : ℝ^2 × ℝ ↦ weightedForcingDeriv v Dv D2v a b κ θ₀ e p.1 p.2)
      (univ ×ˢ Icc a b) := by
  have hv1 := hv.toIsC1FieldOn
  have hX := continuousOn_flowOn_label_time hv1 h0
  have hκX : ContinuousOn (fun p : ℝ^2 × ℝ ↦ κ (flowOn v a b p.2 0 p.1)) (univ ×ˢ Icc a b) :=
    hκ.continuous.comp_continuousOn hX
  have hDκX : ContinuousOn (fun p : ℝ^2 × ℝ ↦ fderiv ℝ κ (flowOn v a b p.2 0 p.1))
      (univ ×ˢ Icc a b) :=
    (hκ.continuous_fderiv one_ne_zero).comp_continuousOn hX
  have hJ : ContinuousOn (fun p : ℝ^2 × ℝ ↦ variationOn v Dv a b p.2 0 p.1)
      (univ ×ˢ Icc a b) :=
    hv1.continuousOn_variationOn.comp (f := fun p : ℝ^2 × ℝ ↦ (p.2, 0, p.1))
      (continuous_snd.prodMk (continuous_const.prodMk continuous_fst)).continuousOn
      fun p hp ↦ ⟨hp.2, h0, mem_univ _⟩
  exact (hκX.smul (continuousOn_labelForcingDeriv hv h0 hθ₀)).add
    ((continuousOn_labelForcing hv1 h0 (hθ₀.of_le (by norm_num))).smul (hDκX.clm_comp hJ))

/-- **The Eulerian form of the weighted forcing**: at the label of the particle at `x` it is
`κ(x)` times the derivative in the direction `e` of the carried quantity at `x`. -/
theorem weightedForcing_eq (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hθ₀ : Differentiable ℝ θ₀) {r : ℝ} (hr : r ∈ Icc a b) (x : ℝ^2) :
    weightedForcing v Dv a b κ θ₀ e (flowOn v a b 0 r x) r =
      κ x * fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 r z)) x e := by
  rw [weightedForcing, labelForcing_eq hv h0 hθ₀ hr,
    hv.isLipschitzFieldOn.flowOn_flowOn_self h0 hr x]

/-- **The Eulerian amplitude with the weighted forcing is jointly `C¹`.** -/
theorem contDiffOn_forcedAmplitude_weightedForcing (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hκ : ContDiff ℝ 1 κ) (hθ₀ : ContDiff ℝ 2 θ₀) {Ω₀ : ℝ^2 → ℝ}
    (hΩ₀ : ContDiff ℝ 1 Ω₀) :
    ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦
      forcedAmplitude Ω₀ (weightedForcing v Dv a b κ θ₀ e) (flowOn v a b 0 p.2 p.1) p.2)
      (univ ×ˢ Ioo a b) :=
  contDiffOn_comp_flowOn_label hv.toIsC1FieldOn h0
    (contDiffOn_forcedAmplitude (G := weightedForcing v Dv a b κ θ₀ e) hΩ₀
      (continuousOn_weightedForcing hv.toIsC1FieldOn h0 hκ.continuous
        (hθ₀.of_le (by norm_num)))
      (fun r hr y ↦ hasFDerivAt_weightedForcing hv h0 (hκ.differentiable one_ne_zero) hθ₀ hr y)
      (continuousOn_weightedForcingDeriv hv h0 hκ hθ₀) h0)

/-- **The forced transport equation with the weighted forcing**: the Eulerian amplitude solves
`w_t + Dw v = κ Dθ e` at every point and every time of `(a, b)`, with `θ` the carried
quantity. For the field of a solution this is the vorticity equation. Proof: the amplitude at
the label is differentiated in time along the flow, where the label is constant and the
amplitude grows by the forcing; `weightedForcing_eq` writes the forcing at the point. -/
theorem hasDerivAt_forcedAmplitude_weightedForcing (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hκ : ContDiff ℝ 1 κ) (hθ₀ : ContDiff ℝ 2 θ₀) {Ω₀ : ℝ^2 → ℝ}
    (hΩ₀ : ContDiff ℝ 1 Ω₀) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ^2) :
    HasDerivAt
      (fun s ↦ forcedAmplitude Ω₀ (weightedForcing v Dv a b κ θ₀ e) (flowOn v a b 0 s x) s)
      (κ x * fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 t z)) x e -
        fderiv ℝ (fun z ↦ forcedAmplitude Ω₀ (weightedForcing v Dv a b κ θ₀ e)
          (flowOn v a b 0 t z) t) x (v t x)) t := by
  have hv1 := hv.toIsC1FieldOn
  have hGc := continuousOn_weightedForcing (e := e) hv1 h0 hκ.continuous
    (hθ₀.of_le (by norm_num))
  have h := hasDerivAt_comp_flowOn_label_time hv1 h0
    (contDiffOn_forcedAmplitude (G := weightedForcing v Dv a b κ θ₀ e) hΩ₀ hGc
      (fun r hr y ↦ hasFDerivAt_weightedForcing hv h0 (hκ.differentiable one_ne_zero) hθ₀ hr y)
      (continuousOn_weightedForcingDeriv hv h0 hκ hθ₀) h0)
    (fun y t ht ↦ hasDerivAt_forcedAmplitude (G := weightedForcing v Dv a b κ θ₀ e) hGc h0 ht y)
    ht x
  rwa [weightedForcing_eq hv1 h0 (hθ₀.differentiable two_ne_zero) (Ioo_subset_Icc_self ht)] at h

/-! ### Bounds on the closed half-plane -/

/-- The bound `Bκ₀ N L` of the weighted forcing. -/
def weightedForcingBound (Bκ : ℕ → ℝ) (N L : ℝ) : ℝ :=
  Bκ 0 * (N * L)

/-- The bound `Bκ₀ c₀ + N L Bκ₁ L` of the derivative of the weighted forcing,
`c₀ = forcingDerivBound N L σ`. -/
def weightedForcingDerivBound (Bκ : ℕ → ℝ) (N L σ : ℝ) : ℝ :=
  Bκ 0 * forcingDerivBound N L σ + N * L * (Bκ 1 * L)

/-- The Lipschitz part of the derivative of the weighted forcing. -/
def weightedForcingDerivLipschitz (Bκ : ℕ → ℝ) (N L σ : ℝ) : ℝ :=
  Bκ 1 * L * forcingDerivBound N L σ + forcingDerivBound N L σ * (Bκ 1 * L) +
    N * L * (Bκ 2 * L * L + Bκ 1 * σ)

/-- The `α`-Hölder constant in the label of the derivative of the weighted forcing. -/
def weightedForcingDerivHolderConst (Bκ : ℕ → ℝ) (N L σ η : ℝ) : ℝ :=
  Bκ 0 * forcingDerivHolderConst N L σ η +
    max (weightedForcingDerivLipschitz Bκ N L σ) (2 * weightedForcingDerivBound Bκ N L σ)

namespace IsForcingCoefficient

variable {Bκ : ℕ → ℝ}

/-- The coefficient is bounded by `Bκ 0`. -/
theorem abs_le (hκ : IsForcingCoefficient κ Bκ) (x : ℝ^2) : |κ x| ≤ Bκ 0 := by
  have h := hκ.norm_iteratedFDeriv_le 0 x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

/-- The derivative of the coefficient is bounded by `Bκ 1`. -/
theorem norm_fderiv_le (hκ : IsForcingCoefficient κ Bκ) (x : ℝ^2) : ‖fderiv ℝ κ x‖ ≤ Bκ 1 := by
  have h := hκ.norm_iteratedFDeriv_le 1 x
  rwa [norm_iteratedFDeriv_one] at h

/-- The second derivative of the coefficient is bounded by `Bκ 2`. -/
theorem norm_fderiv_fderiv_le (hκ : IsForcingCoefficient κ Bκ) (x : ℝ^2) :
    ‖fderiv ℝ (fderiv ℝ κ) x‖ ≤ Bκ 2 := by
  have h := hκ.norm_iteratedFDeriv_le 2 x
  rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h

/-- The coefficient is `C¹`. -/
theorem contDiff_one (hκ : IsForcingCoefficient κ Bκ) : ContDiff ℝ 1 κ :=
  hκ.contDiff.of_le (by exact_mod_cast le_top)

/-- The coefficient is `Bκ 1`-Lipschitz. -/
theorem abs_sub_le (hκ : IsForcingCoefficient κ Bκ) (x y : ℝ^2) :
    |κ x - κ y| ≤ Bκ 1 * ‖x - y‖ := by
  rw [← Real.norm_eq_abs]
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (hκ.contDiff_one.differentiable one_ne_zero) z)
    (fun z _ ↦ hκ.norm_fderiv_le z) (mem_univ _) (mem_univ _)

/-- The derivative of the coefficient is `Bκ 2`-Lipschitz. -/
theorem norm_fderiv_sub_le (hκ : IsForcingCoefficient κ Bκ) (x y : ℝ^2) :
    ‖fderiv ℝ κ x - fderiv ℝ κ y‖ ≤ Bκ 2 * ‖x - y‖ := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ κ) :=
    hκ.contDiff.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (h2.differentiable one_ne_zero) z)
    (fun z _ ↦ hκ.norm_fderiv_fderiv_le z) (mem_univ _) (mem_univ _)

/-- The bounds are nonnegative. -/
theorem bound_nonneg (hκ : IsForcingCoefficient κ Bκ) (k : ℕ) : 0 ≤ Bκ k :=
  (norm_nonneg _).trans (hκ.norm_iteratedFDeriv_le k 0)

end IsForcingCoefficient

/-- The bound of the weighted forcing is nonnegative. -/
theorem weightedForcingBound_nonneg {Bκ : ℕ → ℝ} (hκ : IsForcingCoefficient κ Bκ) {N L : ℝ}
    (hN : 0 ≤ N) (hL : 0 ≤ L) : 0 ≤ weightedForcingBound Bκ N L := by
  have := hκ.bound_nonneg 0
  unfold weightedForcingBound
  positivity

/-- The bound of the derivative of the weighted forcing is nonnegative. -/
theorem weightedForcingDerivBound_nonneg {Bκ : ℕ → ℝ} (hκ : IsForcingCoefficient κ Bκ)
    {N L σ : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    0 ≤ weightedForcingDerivBound Bκ N L σ := by
  have := hκ.bound_nonneg 0
  have := hκ.bound_nonneg 1
  have := forcingDerivBound_nonneg hN hL hσ
  unfold weightedForcingDerivBound
  positivity

/-- The Hölder constant of the derivative of the weighted forcing is nonnegative. -/
theorem weightedForcingDerivHolderConst_nonneg {Bκ : ℕ → ℝ} (hκ : IsForcingCoefficient κ Bκ)
    {N L σ η : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hη : 0 ≤ η) :
    0 ≤ weightedForcingDerivHolderConst Bκ N L σ η := by
  have := hκ.bound_nonneg 0
  have := forcingDerivHolderConst_nonneg hN hL hσ hη
  have h2 : 0 ≤ 2 * weightedForcingDerivBound Bκ N L σ := by
    have := weightedForcingDerivBound_nonneg hκ hN hL hσ
    positivity
  unfold weightedForcingDerivHolderConst
  exact add_nonneg (by positivity) (h2.trans (le_max_right _ _))

/-! ### The amplitude with the weighted forcing -/

variable {α R N : ℝ} {ω₀ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-- **The amplitude with the weighted forcing is differentiable in the label**, with derivative
`Dω̃₀ + ∫₀ᵗ DG_κ`. -/
theorem hasFDerivAt_weightedAmplitude (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) (y : ℝ^2) :
    HasFDerivAt (fun z ↦ forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) z t)
      (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y r) y :=
  hasFDerivAt_forcedAmplitude
    (G := weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1))
    (DG := weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1))
    (hd.contDiff_dataVorticity.differentiable one_ne_zero)
    (continuousOn_weightedForcing hv.toIsC1FieldOn h0 hκ.contDiff_one.continuous
      (hd.contDiff_dataTemperature.of_le (by norm_num)))
    (fun r hr z ↦ hasFDerivAt_weightedForcing hv h0 (hκ.contDiff_one.differentiable one_ne_zero)
      hd.contDiff_dataTemperature hr z)
    (continuousOn_weightedForcingDeriv hv h0 hκ.contDiff_one hd.contDiff_dataTemperature) h0 ht y

/-- **The amplitude with the weighted forcing is `C¹` in the label** at every time of
`[a, b]`. -/
theorem contDiff_weightedAmplitude (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 1 (fun z ↦ forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) z t) := by
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨_, ?_, fun y ↦
    hasFDerivAt_weightedAmplitude hv h0 hd hκ ht y⟩
  exact (hd.contDiff_dataVorticity.continuous_fderiv one_ne_zero).add
    (continuous_integral_of_continuousOn
      (f := weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1))
      (continuousOn_weightedForcingDeriv hv h0 hκ.contDiff_one hd.contDiff_dataTemperature) h0 ht)

end HalfPlaneSystem

namespace Boussinesq.HalfPlane.IsBoundedFlowOn

open HalfPlaneSystem

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b : ℝ} {K K₂ : ℝ≥0} {κ θ₀ : ℝ^2 → ℝ}

variable {α V K₁ L δ σ η : ℝ} {ω₀ : ℝ^2 → ℝ} {R N : ℝ} {Bκ : ℕ → ℝ}

/-- **The weighted forcing is at most `Bκ₀ N L`** on the closed half-plane. -/
theorem abs_weightedForcing_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    (hκ : IsForcingCoefficient κ Bκ) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    |weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r| ≤
      weightedForcingBound Bκ N L := by
  rw [weightedForcing, abs_mul]
  exact mul_le_mul (hκ.abs_le _) (hb.abs_labelForcing_le h0 hd hr hy) (abs_nonneg _)
    (hκ.bound_nonneg 0)

/-- The variation of the particle in its label is at most `L`. -/
theorem norm_variationOn_label_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖variationOn v Dv a b r 0 y‖ ≤ L :=
  hb.norm_variationOn_le r hr 0 h0 y hy

/-- **The derivative of the weighted forcing in the label is at most `Bκ₀ c₀ + N L Bκ₁ L`** on
the closed half-plane. -/
theorem norm_weightedForcingDeriv_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    (hκ : IsForcingCoefficient κ Bκ) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r‖ ≤
      weightedForcingDerivBound Bκ N L σ := by
  have hL0 := hb.zero_le_L h0
  have hG := hb.abs_labelForcing_le h0 hd hr hy
  have hDG := hb.norm_labelForcingDeriv_le h0 hd hr hy
  have hJ := hb.norm_variationOn_label_le h0 hr hy
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hd.norm_fderiv_dataTemperature_le hy)
  have h1 : ‖fderiv ℝ κ (flowOn v a b r 0 y)‖ ≤ Bκ 1 := hκ.norm_fderiv_le _
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hκ.abs_le _) hDG (norm_nonneg _) (hκ.bound_nonneg 0)
  · rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul hG ?_ (norm_nonneg _) (by positivity)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h1 hJ (norm_nonneg _) (hκ.bound_nonneg 1))

/-- The label forcing is Lipschitz in the label with constant `c₀` on the closed half-plane. -/
theorem abs_labelForcing_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {r : ℝ} (hr : r ∈ Icc a b) {y y' : ℝ^2} (hy : 0 ≤ y 1)
    (hy' : 0 ≤ y' 1) :
    |labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r -
        labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y' r| ≤
      forcingDerivBound N L σ * ‖y - y'‖ := by
  rw [← Real.norm_eq_abs]
  exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (hasFDerivAt_labelForcing hv h0 hd.contDiff_dataTemperature hr z).hasFDerivWithinAt)
    (fun z hz ↦ hb.norm_labelForcingDeriv_le h0 hd hr hz) hy' hy

/-- **The derivative of the weighted forcing is `α`-Hölder in the label** on the closed
half-plane, with the constant `weightedForcingDerivHolderConst Bκ N L σ η`. -/
theorem norm_weightedForcingDeriv_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {r : ℝ} (hr : r ∈ Icc a b) {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    ‖weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r -
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y' r‖ ≤
      weightedForcingDerivHolderConst Bκ N L σ η * ‖y - y'‖ ^ α := by
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set θ := dataTemperature θ₀
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hη0 := hb.zero_le_η h0
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hd.norm_fderiv_dataTemperature_le hy)
  have hB0 := hκ.bound_nonneg 0
  have hB1 := hκ.bound_nonneg 1
  have hB2 := hκ.bound_nonneg 2
  have hc0 := forcingDerivBound_nonneg hN0 hL0 hσ0
  have hcα := forcingDerivHolderConst_nonneg hN0 hL0 hσ0 hη0
  refine norm_sub_le_add_max_mul_rpow (S := H̄) (A := Bκ 0 * forcingDerivHolderConst N L σ η)
    (by positivity) hα0 hα1 (fun z hz w hw ↦ ?_)
    (fun z hz ↦ hb.norm_weightedForcingDeriv_le h0 hd hκ hr hz) hy hy'
  -- the Hölder-plus-Lipschitz estimate at two labels `z, w`
  set X := flowOn v a b r 0 z
  set X' := flowOn v a b r 0 w
  set J := variationOn v Dv a b r 0 z
  set J' := variationOn v Dv a b r 0 w
  set G := labelForcing v Dv a b θ e z r
  set G' := labelForcing v Dv a b θ e w r
  set DG := labelForcingDeriv v Dv D2v a b θ e z r
  set DG' := labelForcingDeriv v Dv D2v a b θ e w r
  have hd0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hXX : ‖X - X'‖ ≤ L * ‖z - w‖ := hb.norm_flowOn_sub_le hv.toIsC1FieldOn hr h0 hz hw
  have hJ : ‖J‖ ≤ L := hb.norm_variationOn_label_le h0 hr hz
  have hJJ : ‖J - J'‖ ≤ σ * ‖z - w‖ := hb.norm_variationOn_sub_le hv hr h0 hz hw
  have hG' : |G'| ≤ N * L := hb.abs_labelForcing_le h0 hd hr hw
  have hGG : |G - G'| ≤ forcingDerivBound N L σ * ‖z - w‖ :=
    hb.abs_labelForcing_sub_le hv h0 hd hr hz hw
  have hDG' : ‖DG'‖ ≤ forcingDerivBound N L σ := hb.norm_labelForcingDeriv_le h0 hd hr hw
  have hDGG : ‖DG - DG'‖ ≤ forcingDerivHolderConst N L σ η * ‖z - w‖ ^ α :=
    hb.norm_labelForcingDeriv_sub_le hv h0 hd hα0 hα1 hr hz hw
  have hκX : |κ X| ≤ Bκ 0 := hκ.abs_le X
  have hκXX : |κ X - κ X'| ≤ Bκ 1 * (L * ‖z - w‖) :=
    (hκ.abs_sub_le X X').trans (mul_le_mul_of_nonneg_left hXX hB1)
  have hP : ‖(fderiv ℝ κ X).comp J‖ ≤ Bκ 1 * L :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hκ.norm_fderiv_le X) hJ (norm_nonneg _) hB1)
  have hPP : ‖(fderiv ℝ κ X).comp J - (fderiv ℝ κ X').comp J'‖ ≤
      (Bκ 2 * L * L + Bκ 1 * σ) * ‖z - w‖ := by
    have heq : (fderiv ℝ κ X).comp J - (fderiv ℝ κ X').comp J' =
        (fderiv ℝ κ X - fderiv ℝ κ X').comp J + (fderiv ℝ κ X').comp (J - J') := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(fderiv ℝ κ X - fderiv ℝ κ X').comp J‖ ≤ Bκ 2 * (L * ‖z - w‖) * L :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
        ((hκ.norm_fderiv_sub_le X X').trans (mul_le_mul_of_nonneg_left hXX hB2)) hJ
        (norm_nonneg _) (by positivity))
    have h2 : ‖(fderiv ℝ κ X').comp (J - J')‖ ≤ Bκ 1 * (σ * ‖z - w‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hκ.norm_fderiv_le X') hJJ (norm_nonneg _) hB1)
    calc _ ≤ Bκ 2 * (L * ‖z - w‖) * L + Bκ 1 * (σ * ‖z - w‖) := add_le_add h1 h2
      _ = _ := by ring
  have hsplit : weightedForcingDeriv v Dv D2v a b κ θ e z r -
      weightedForcingDeriv v Dv D2v a b κ θ e w r =
      (κ X • (DG - DG') + (κ X - κ X') • DG') +
        ((G - G') • (fderiv ℝ κ X).comp J +
          G' • ((fderiv ℝ κ X).comp J - (fderiv ℝ κ X').comp J')) := by
    simp only [weightedForcingDeriv, smul_sub, sub_smul]
    abel
  rw [hsplit]
  have h₁ : ‖κ X • (DG - DG') + (κ X - κ X') • DG'‖ ≤
      Bκ 0 * (forcingDerivHolderConst N L σ η * ‖z - w‖ ^ α) +
        Bκ 1 * (L * ‖z - w‖) * forcingDerivBound N L σ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hκX hDGG (norm_nonneg _) hB0
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hκXX hDG' (norm_nonneg _) (by positivity)
  have h₂ : ‖(G - G') • (fderiv ℝ κ X).comp J +
      G' • ((fderiv ℝ κ X).comp J - (fderiv ℝ κ X').comp J')‖ ≤
      forcingDerivBound N L σ * ‖z - w‖ * (Bκ 1 * L) +
        N * L * ((Bκ 2 * L * L + Bκ 1 * σ) * ‖z - w‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hGG hP (norm_nonneg _) (by positivity)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hG' hPP (norm_nonneg _) (by positivity)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (Bκ 0 * (forcingDerivHolderConst N L σ η * ‖z - w‖ ^ α) +
          Bκ 1 * (L * ‖z - w‖) * forcingDerivBound N L σ) +
        (forcingDerivBound N L σ * ‖z - w‖ * (Bκ 1 * L) +
          N * L * ((Bκ 2 * L * L + Bκ 1 * σ) * ‖z - w‖)) := add_le_add h₁ h₂
    _ = Bκ 0 * forcingDerivHolderConst N L σ η * ‖z - w‖ ^ α +
        weightedForcingDerivLipschitz Bκ N L σ * ‖z - w‖ := by
        unfold weightedForcingDerivLipschitz; ring

/-! ### Bounds of the amplitude with the weighted forcing -/

/-- The amplitude with the weighted forcing is bounded by `N + |t| Bκ₀ N L` on the closed
half-plane. -/
theorem abs_weightedAmplitude_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t| ≤
      N + |t| * weightedForcingBound Bκ N L := by
  rw [forcedAmplitude]
  refine (abs_add_le _ _).trans (add_le_add (hd.abs_dataVorticity_le hy) ?_)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_).trans_eq
    (by rw [sub_zero, mul_comm])
  rw [Real.norm_eq_abs]
  exact hb.abs_weightedForcing_le h0 hd hκ (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy

/-- **The derivative of the amplitude with the weighted forcing is at most `N + |t| c₀`** on the
closed half-plane, `c₀ = weightedForcingDerivBound Bκ N L σ`. -/
theorem norm_fderiv_weightedAmplitude_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y r‖ ≤
      N + |t| * weightedForcingDerivBound Bκ N L σ := by
  refine (norm_add_le _ _).trans (add_le_add (hd.norm_fderiv_dataVorticity_le hy) ?_)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_).trans_eq
    (by rw [sub_zero, mul_comm])
  exact hb.norm_weightedForcingDeriv_le h0 hd hκ (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy

/-- **The derivative of the amplitude with the weighted forcing is `α`-Hölder** on the closed
half-plane with constant `N + |t| c_α`, `c_α = weightedForcingDerivHolderConst Bκ N L σ η`. -/
theorem norm_fderiv_weightedAmplitude_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    ‖(fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y r) -
      (fderiv ℝ (dataVorticity ω₀) y' + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y' r)‖ ≤
      (N + |t| * weightedForcingDerivHolderConst Bκ N L σ η) * ‖y - y'‖ ^ α := by
  set G := weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
  have hGc : ContinuousOn (fun p : ℝ^2 × ℝ ↦ G p.1 p.2) (univ ×ˢ Icc a b) :=
    continuousOn_weightedForcingDeriv hv h0 hκ.contDiff_one hd.contDiff_dataTemperature
  have hGr (z : ℝ^2) : IntervalIntegrable (G z) MeasureTheory.volume 0 t :=
    ((hGc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun r hr ↦ ⟨mem_univ _, hr⟩).mono (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hsplit : (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t, G y r) -
      (fderiv ℝ (dataVorticity ω₀) y' + ∫ r in (0)..t, G y' r) =
      (fderiv ℝ (dataVorticity ω₀) y - fderiv ℝ (dataVorticity ω₀) y') +
        ∫ r in (0)..t, (G y r - G y' r) := by
    rw [intervalIntegral.integral_sub (hGr y) (hGr y')]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hI : ‖∫ r in (0)..t, (G y r - G y' r)‖ ≤
      weightedForcingDerivHolderConst Bκ N L σ η * ‖y - y'‖ ^ α * |t| :=
    (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
      hb.norm_weightedForcingDeriv_sub_le hv h0 hd hκ hα0 hα1
        (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy hy').trans_eq (by rw [sub_zero])
  calc _ ≤ N * ‖y - y'‖ ^ α + weightedForcingDerivHolderConst Bκ N L σ η * ‖y - y'‖ ^ α * |t| :=
        add_le_add (hd.norm_fderiv_dataVorticity_sub_le hy hy') hI
    _ = _ := by ring

/-- **The amplitude with the weighted forcing is Lipschitz in the label** on the closed
half-plane with constant `N + |t| c₀`. -/
theorem abs_weightedAmplitude_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) {t : ℝ} (ht : t ∈ Icc a b)
    {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t -
      forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y' t| ≤
      (N + |t| * weightedForcingDerivBound Bκ N L σ) * ‖y - y'‖ := by
  rw [← Real.norm_eq_abs]
  exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (hasFDerivAt_weightedAmplitude hv h0 hd hκ ht z).hasFDerivWithinAt)
    (fun z hz ↦ hb.norm_fderiv_weightedAmplitude_le h0 hd hκ ht hz) hy' hy

/-- The amplitude with the weighted forcing is Lipschitz in time with constant `Bκ₀ N L` on the
closed half-plane. -/
theorem abs_weightedAmplitude_time_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y s -
      forcedAmplitude (dataVorticity ω₀)
        (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t| ≤
      weightedForcingBound Bκ N L * |s - t| := by
  have hGc := continuousOn_weightedForcing (e := EuclideanSpace.single 0 1) hv.toIsC1FieldOn h0
    hκ.contDiff_one.continuous (hd.contDiff_dataTemperature.of_le (by norm_num))
  have hGy := continuousOn_slice_of_continuousOn hGc y
  have h := norm_integral_sub_integral_le hGy h0 hs ht fun r hr ↦ by
    rw [Real.norm_eq_abs]; exact hb.abs_weightedForcing_le h0 hd hκ hr hy
  rw [Real.norm_eq_abs] at h
  unfold forcedAmplitude
  rwa [add_sub_add_left_eq_sub]

/-- The derivative of the amplitude with the weighted forcing is Lipschitz in time with constant
`c₀` on the closed half-plane. -/
theorem norm_fderiv_weightedAmplitude_time_sub_le
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖(fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..s,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y r) -
      (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          y r)‖ ≤
      weightedForcingDerivBound Bκ N L σ * |s - t| := by
  have hGc := continuousOn_weightedForcingDeriv (e := EuclideanSpace.single 0 1) hv h0
    hκ.contDiff_one hd.contDiff_dataTemperature
  have hGy := continuousOn_slice_of_continuousOn hGc y
  have h := norm_integral_sub_integral_le hGy h0 hs ht fun r hr ↦
    hb.norm_weightedForcingDeriv_le h0 hd hκ hr hy
  refine le_of_eq_of_le ?_ h
  congr 1
  abel

end Boussinesq.HalfPlane.IsBoundedFlowOn
