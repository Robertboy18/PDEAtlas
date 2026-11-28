/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Law
public import PDE.Fluid.Incompressible.HalfPlane.VelocityField
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The field of a velocity law on the whole plane

A velocity law gives the velocity only on the closed upper half-plane `H̄`, but the theory of flows
of ordinary differential equations is stated for fields on the whole plane. This module extends the
field across the boundary line and proves that the field of a vorticity history has the regularity
in space and time that the flow theory needs.

A field `u` given on `H̄` is extended by the weighted reflection of order `K` of each component
(`extendedField K u`): the extension equals `u` on `H̄`, is `C^K` on the plane whenever `u` is `C^K`
within `H̄`, and its first two derivatives are bounded by fixed multiples of those of `u` within
`H̄`. These are the lemmas of `IncompressibleFlow.extendedVelocity` for an arbitrary field. Below
the boundary the extension has no meaning for the system: only its values on `H̄` enter the
equations.

For a velocity law `U` (`IsVelocityLaw U R₀ C`) and a vorticity history `ω` supported in a disc of
radius `R ≤ R₀`, the field of the history is `lawField U ω t = extendedField 2 (U (ω t))`. For a
`C^{1,α}` history, `0 < α < 1`, it is a `C²` field on `[a, b] × ℝ²` in the sense of the flow theory,
with derivative bounded by the Kato bound and second derivative by the `C²` bound of the law.
Continuity in time of the derivatives comes from the linearity of the law, the homogeneous Kato
bound and, at the second order, the bound of the law at a smaller Hölder exponent applied to
`ω s - ω t`.

## Main results

* `extendedField`: the extension of a field across the boundary line, with
  `extendedField_of_nonneg`, `extendedField_normal_eq_zero`, `contDiff_extendedField`,
  `fderiv_extendedField_of_nonneg`, `fderiv_fderiv_extendedField_of_nonneg`,
  `norm_fderiv_extendedField_le` and `norm_fderiv_fderiv_extendedField_le`: it is the field on `H̄`,
  it is `C^K`, its first two derivatives on `H̄` are those of the field within `H̄`, and they are
  bounded on the plane by fixed multiples (`PDE.Analysis.reflectionBound`, not computed here) of the
  bounds within `H̄`.
* `lawField`, `lawFieldDeriv`, `lawFieldDeriv₂`: the field of a history and its first two
  derivatives; `lawField_of_nonneg`: on `H̄` it is `U (ω t)`.
* `IncompressibleFlow.IsVorticityHistory.contDiffOn_law`,
  `IncompressibleFlow.IsVorticityHistory.norm_law_le`,
  `IncompressibleFlow.IsVorticityHistory.norm_fderivWithin_law_le`,
  `IncompressibleFlow.IsVorticityHistory.law_normal_eq_zero`: at every time of a Hölder history the
  field of the law is `C¹` within `H̄`, bounded by `C 0 0 B`, its derivative is bounded by the Kato
  bound, and its normal component vanishes on the boundary.
* `IncompressibleFlow.IsVorticityHistory.exists_norm_law_sub_le`,
  `IncompressibleFlow.IsVorticityHistory.exists_norm_fderivWithin_law_sub_le`: the field and its
  derivative are continuous in time uniformly on `H̄`.
* `IncompressibleFlow.IsVorticityHistory.isC1FieldOn_extendedField_law`: the extensions of order
  `K ≥ 1` form a `C¹` field on `[a, b] × ℝ²`.
* `IncompressibleFlow.IsC1VorticityHistory.isC2FieldOn_lawField`: for a `C^{1,α}` history the fields
  `lawField U ω t` form a `C²` field on `[a, b] × ℝ²`.

For `C^{k,α}` histories, `FieldHigher.lean` constructs the field extended at order `k + 1`
and identifies its flow with that of `lawField` on the closed half-plane.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow SobolevSpace.GraphSpace.HigherOrderReflection

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The extension of a field -/

variable {u w : ℝ^2 → ℝ^2}

/-- The extension to the plane of a field `u` given on the closed half-plane: the weighted
reflection of order `K` of each component of `u` across the boundary line `x₁ = 0`. -/
def extendedField (K : ℕ) (u : ℝ^2 → ℝ^2) (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 fun k ↦ weightedReflectionFun 1 K (fun y ↦ u y k) x

/-- A component of the extended field is the weighted reflection of order `K` of that component
of the field. -/
@[simp]
theorem extendedField_apply (K : ℕ) (u : ℝ^2 → ℝ^2) (x : ℝ^2) (k : Fin 2) :
    extendedField K u x k = weightedReflectionFun 1 K (fun y ↦ u y k) x :=
  rfl

/-- On the closed half-plane the extended field is the field. -/
theorem extendedField_of_nonneg (K : ℕ) (u : ℝ^2 → ℝ^2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    extendedField K u x = u x := by
  ext k
  simp [weightedReflectionFun_eq_of_nonneg _ _ _ _ hx]

/-- The normal component of the extended field vanishes on the boundary line where that of the
field does. -/
theorem extendedField_normal_eq_zero (K : ℕ) {u : ℝ^2 → ℝ^2} {x : ℝ^2} (hx : x 1 = 0)
    (hu : u x 1 = 0) : extendedField K u x 1 = 0 := by
  rw [extendedField_of_nonneg K u hx.symm.le]
  exact hu

/-- The components of a field that is `C^K` within `H̄` are `C^K` within `H̄`. -/
theorem contDiffOn_apply {K : ℕ}
    (hu : ContDiffOn ℝ K u H̄) (k : Fin 2) :
    ContDiffOn ℝ K (fun y ↦ u y k) H̄ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) k).contDiff.comp_contDiffOn hu

variable {K : ℕ}

/-- The extended field is `C^K` when the field is `C^K` within the closed half-plane. -/
theorem contDiff_extendedField (hK : 1 ≤ K) (hu : ContDiffOn ℝ K u H̄) :
    ContDiff ℝ K (extendedField K u) :=
  contDiff_piLp' (p := 2) fun k ↦
    PDE.Analysis.contDiff_weightedReflectionFun 1 hK (contDiffOn_apply hu k)

/-- The derivative of the extended field from the derivatives of its components. -/
theorem hasFDerivAt_extendedField (hK : 1 ≤ K) (hu : ContDiffOn ℝ K u H̄)
    (x : ℝ^2) :
    HasFDerivAt (extendedField K u)
      (∑ j, toComponentL j
        (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y j)) x)) x :=
  hasFDerivAt_toLp_of_components fun k ↦
    (((PDE.Analysis.contDiff_weightedReflectionFun 1 hK
      (contDiffOn_apply hu k)).differentiable
        (by exact_mod_cast (show K ≠ 0 by omega))) x).hasFDerivAt

/-- The derivative of the extended field as the sum of the embedded component derivatives. -/
theorem fderiv_extendedField (hK : 1 ≤ K) (hu : ContDiffOn ℝ K u H̄)
    (x : ℝ^2) :
    fderiv ℝ (extendedField K u) x = ∑ j, toComponentL j
      (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y j)) x) :=
  (hasFDerivAt_extendedField hK hu x).fderiv

/-- On the closed half-plane the derivative of the extended field is the derivative of the
velocity within the closed half-plane. -/
theorem fderiv_extendedField_of_nonneg (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (extendedField K u) x = fderivWithin ℝ u H̄ x := by
  have hd : DifferentiableWithinAt ℝ u H̄ x :=
    hu.differentiableOn (by exact_mod_cast (show K ≠ 0 by omega)) x hx
  rw [fderiv_extendedField hK hu]
  conv_rhs => rw [← sum_toComponentL_proj_comp (fderivWithin ℝ u H̄ x)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 hK
    (contDiffOn_apply hu j) hx, fderivWithin_apply_eq hx hd j]

/-- The derivative of the extended field is bounded by `2 c₁` times the bound of the
derivative of the field within the closed half-plane. -/
theorem norm_fderiv_extendedField_le (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) {Q : ℝ}
    (hQ : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ u H̄ y‖ ≤ Q) (x : ℝ^2) :
    ‖fderiv ℝ (extendedField K u) x‖ ≤ 2 * PDE.Analysis.reflectionBound K 1 * Q := by
  have hK0 : (K : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  rw [fderiv_extendedField hK hu]
  refine (norm_sum_toComponentL_le _).trans ?_
  have hk (k : Fin 2) :
      ‖fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y k)) x‖ ≤
      PDE.Analysis.reflectionBound K 1 * Q :=
    PDE.Analysis.norm_fderiv_weightedReflectionFun_le 1 hK
      (contDiffOn_apply hu k)
      (fun y hy ↦ (norm_fderivWithin_apply_le hy (hu.differentiableOn hK0 y hy) k).trans
        (hQ y hy)) x
  rw [Fin.sum_univ_two]
  linarith [hk 0, hk 1]

/-- The second derivative of the extended field from those of its components. -/
theorem fderiv_fderiv_extendedField (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) (x : ℝ^2) :
    fderiv ℝ (fderiv ℝ (extendedField K u)) x = ∑ j, (toComponentL j).comp
      (fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y j))) x) := by
  have hfun : fderiv ℝ (extendedField K u) = fun y ↦ ∑ j, toComponentL j
      (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y j)) y) :=
    funext (fderiv_extendedField (by omega) hu)
  rw [hfun]
  refine HasFDerivAt.fderiv (HasFDerivAt.fun_sum fun j _ ↦ ?_)
  have hE := (PDE.Analysis.contDiff_weightedReflectionFun 1 (by omega)
    (contDiffOn_apply hu j)).fderiv_right (m := 1) (by exact_mod_cast hK)
  exact (toComponentL j).hasFDerivAt.comp x
    ((hE.differentiable one_ne_zero) x).hasFDerivAt

/-- On the closed half-plane the second derivative of the extended field is the second
derivative of the field within the closed half-plane. -/
theorem fderiv_fderiv_extendedField_of_nonneg (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (fderiv ℝ (extendedField K u)) x =
      fderivWithin ℝ (fderivWithin ℝ u H̄) H̄ x := by
  have hu2 : ContDiffOn ℝ 2 u H̄ := hu.of_le (by exact_mod_cast hK)
  rw [fderiv_fderiv_extendedField hK hu]
  ext h : 1
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  conv_rhs => rw [← sum_toComponentL_proj_comp
    (fderivWithin ℝ (fderivWithin ℝ u H̄) H̄ x h)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.Analysis.fderiv_fderiv_weightedReflectionFun_of_nonneg 1 hK
    (contDiffOn_apply hu j) hx, fderivWithin_fderivWithin_apply_eq hx hu2 j]
  rfl

/-- The second derivative of the extended field is bounded by `2 c₂` times the bound of the
second derivative of the field within the closed half-plane. -/
theorem norm_fderiv_fderiv_extendedField_le (hK : 2 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) {Q : ℝ} (hQ : ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ u H̄) H̄ y‖ ≤ Q) (x : ℝ^2) :
    ‖fderiv ℝ (fderiv ℝ (extendedField K u)) x‖ ≤
      2 * PDE.Analysis.reflectionBound K 2 * Q := by
  have hu2 : ContDiffOn ℝ 2 u H̄ := hu.of_le (by exact_mod_cast hK)
  rw [fderiv_fderiv_extendedField hK hu, Fin.sum_univ_two]
  refine (norm_add_le (E := ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) _ _).trans ?_
  have hk (k : Fin 2) :
      ‖(toComponentL k).comp
          (fderiv ℝ (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ u y k))) x)‖ ≤
        PDE.Analysis.reflectionBound K 2 * Q := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _)
      (norm_toComponentL_le k)).trans ?_
    refine PDE.Analysis.norm_fderiv_fderiv_weightedReflectionFun_le 1 hK
      (contDiffOn_apply hu k) (fun y hy ↦ ?_) x
    rw [fderivWithin_fderivWithin_apply_eq hy hu2 k]
    refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_).trans (hQ y hy)
    exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) (norm_projCompL_le k)
  linarith [hk 0, hk 1]

/-! ### The field of a vorticity history -/

/-- The field of a vorticity history `ω` under the velocity law `U`: at time `t` the extension by
the weighted reflection of order two of `U (ω t)`. -/
def lawField (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) : ℝ^2 → ℝ^2 :=
  extendedField 2 (U (ω t))

/-- The spatial derivative of the field of a history. -/
def lawFieldDeriv (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) :
    ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (lawField U ω t) x

/-- The second spatial derivative of the field of a history. -/
def lawFieldDeriv₂ (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) :
    ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (fderiv ℝ (lawField U ω t)) x

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}

/-- On the closed half-plane the field of a history is the field of the law. -/
theorem lawField_of_nonneg (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) {x : ℝ^2}
    (hx : 0 ≤ x 1) : lawField U ω t x = U (ω t) x :=
  extendedField_of_nonneg 2 _ hx

private theorem min_le_rpow_mul_rpow {A X : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) :
    min A X ≤ A ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
  have hm : 0 ≤ min A X := le_min hA hX
  calc min A X = min A X ^ (1 / 2 : ℝ) * min A X ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add' hm (by norm_num)]; norm_num
    _ ≤ A ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _

end HalfPlaneSystem

namespace IncompressibleFlow.IsVorticityHistory

open HalfPlaneSystem

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M : ℝ}

/-- At every time the field of the law is `C¹` within the closed half-plane. -/
theorem contDiffOn_law (hU : IsVelocityLaw U R₀ C) (hω : IsVorticityHistory ω a b α R B M)
    (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ 1 (U (ω t)) H̄ :=
  hU.contDiffOn_one hα hα1 hR (hω.continuousOn t ht) (hω.eq_zero t ht) (hω.holder t ht)

/-- The field of the law at a time of a history is bounded by `C 0 0 B` on `H̄`. -/
theorem norm_law_le (hU : IsVelocityLaw U R₀ C) (hω : IsVorticityHistory ω a b α R B M)
    (hR : R ≤ R₀) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖U (ω t) x‖ ≤ C 0 0 * B :=
  hU.norm_le hR (hω.continuousOn t ht) (hω.eq_zero t ht) (hω.abs_le t ht) x hx

/-- The normal component of the field of the law vanishes on the boundary line. -/
theorem law_normal_eq_zero (hU : IsVelocityLaw U R₀ C) (hω : IsVorticityHistory ω a b α R B M)
    (hR : R ≤ R₀) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : x 1 = 0) : U (ω t) x 1 = 0 :=
  hU.normal_eq_zero hR (hω.continuousOn t ht) (hω.eq_zero t ht) x hx

/-- At every time the derivative of the field of the law is bounded by the Kato bound. -/
theorem norm_fderivWithin_law_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1) {t : ℝ}
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (U (ω t)) H̄ x‖ ≤ C 0 α * (1 + B * Real.log (2 + M) + B) :=
  hU.norm_fderivWithin_le hα hα1 hR (hω.continuousOn t ht) (hω.eq_zero t ht) (hω.holder t ht)
    (hω.holder_nonneg ht) (hω.abs_le t ht) x hx

/-- **Continuity in time of the field of the law**, uniformly on the closed half-plane. -/
theorem exists_norm_law_sub_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖U (ω s) y - U (ω t) y‖ ≤ ε := by
  have hC := hU.const_nonneg 0 0
  obtain ⟨δ, hδ, hδt⟩ := hω.uniform t ht (ε / (C 0 0 + 1)) (by positivity)
  refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
  refine (hU.norm_sub_le hR (hω.continuousOn s hs) (hω.eq_zero s hs) (hω.continuousOn t ht)
    (hω.eq_zero t ht) (fun z hz ↦ hδt s hs hst z hz) hy).trans ?_
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Continuity in time of the derivative of the field of the law**, uniformly on the closed
half-plane (the homogeneous Kato bound for `ω s - ω t`). -/
theorem exists_norm_fderivWithin_law_sub_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1) {t : ℝ}
    (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (U (ω s)) H̄ y - fderivWithin ℝ (U (ω t)) H̄ y‖ ≤ ε := by
  have hM0 := hω.holder_nonneg ht
  have hA : 0 < 2 * 1 + (M + M) := by linarith
  have hcont : Continuous fun η ↦
      C 0 α * (PDE.Analysis.osgoodModulus (2 * 1 + (M + M)) η + η) :=
    continuous_const.mul ((PDE.Analysis.continuous_osgoodModulus hA).add continuous_id)
  obtain ⟨η, hη, hη1, hηε⟩ := exists_pos_le_one_of_continuousAt hcont.continuousAt
    (by simp [PDE.Analysis.osgoodModulus_zero]) hε
  obtain ⟨δ, hδ, hδt⟩ := hω.uniform t ht η hη
  refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
  exact (hU.norm_fderivWithin_sub_le_osgood hα hα1 hR (hω.continuousOn s hs) (hω.eq_zero s hs)
    (hω.continuousOn t ht) (hω.eq_zero t ht) (hω.holder s hs) (hω.holder t ht) hM0 hM0
    (fun z hz ↦ hδt s hs hst z hz) hη1 hy).trans hηε

/-- The extensions of order `K ≥ 1` of the fields of the law of a vorticity history whose fields
are `C^K` within the closed half-plane form a `C¹` field on `[a, b] × ℝ²`, with derivatives
bounded by `2 reflectionBound K 1` times the Kato bound. -/
theorem isC1FieldOn_extendedField_law (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1) {K : ℕ}
    (hK : 1 ≤ K) (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (U (ω t)) H̄) :
    PDE.Analysis.ODE.IsC1FieldOn (fun t ↦ extendedField K (U (ω t)))
      (fun t x ↦ fderiv ℝ (extendedField K (U (ω t))) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound K 1 *
        (C 0 α * (1 + B * Real.log (2 + M) + B)))) where
  continuousOn := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦
        weightedReflectionFun 1 K (fun y ↦ U (ω p.1) y k) p.2) (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_weightedReflectionFun 1 hK
        (f := fun t y ↦ U (ω t) y k)
        (fun t ht ↦ contDiffOn_apply (hu t ht) k) (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_law_sub_le hU hR ht hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      rw [← Real.norm_eq_abs, ← PiLp.sub_apply]
      exact (PiLp.norm_apply_le _ k).trans (h s hs hst y hy)
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hcomp)
  continuousOn_deriv := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦
        fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ U (ω p.1) y k)) p.2)
        (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_fderiv_weightedReflectionFun 1 hK
        (f := fun t y ↦ U (ω t) y k)
        (fun t ht ↦ contDiffOn_apply (hu t ht) k) (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_fderivWithin_law_sub_le hU hR hα hα1 ht hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      refine (norm_fderivWithin_apply_sub_le hy
        ((hω.contDiffOn_law hU hR hα hα1 hs).differentiableOn one_ne_zero y hy)
        ((hω.contDiffOn_law hU hR hα hα1 ht).differentiableOn one_ne_zero y hy)
        k).trans (h s hs hst y hy)
    have heq : EqOn (Function.uncurry fun t x ↦ fderiv ℝ (extendedField K (U (ω t))) x)
        (fun p : ℝ × ℝ^2 ↦ toComponentL 0
            (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ U (ω p.1) y 0)) p.2) +
          toComponentL 1
            (fderiv ℝ (weightedReflectionFun 1 K (fun y ↦ U (ω p.1) y 1)) p.2))
        (Icc a b ×ˢ univ) := fun p hp ↦ by
      change fderiv ℝ (extendedField K (U (ω p.1))) p.2 = _
      rw [fderiv_extendedField hK (hu p.1 hp.1), Fin.sum_univ_two]
    refine ContinuousOn.congr ?_ heq
    exact ((toComponentL 0).continuous.comp_continuousOn (hcomp 0)).add
      ((toComponentL 1).continuous.comp_continuousOn (hcomp 1))
  hasFDerivAt t ht x :=
    ((contDiff_extendedField hK (hu t ht)).differentiable
      (by exact_mod_cast (show K ≠ 0 by omega)) x).hasFDerivAt
  norm_le t ht x :=
    (norm_fderiv_extendedField_le hK (hu t ht)
      (fun _ hy ↦ hω.norm_fderivWithin_law_le hU hR hα hα1 ht hy) x).trans
        (Real.le_coe_toNNReal _)

end IncompressibleFlow.IsVorticityHistory

namespace IncompressibleFlow.IsC1VorticityHistory

open HalfPlaneSystem

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M B₁ M₁ : ℝ}

/-- The level-one data of a time of a `C¹` history, with the bound `max B (max B₁ M₁)`. -/
theorem levelOne_data (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) {t : ℝ}
    (ht : t ∈ Icc a b) :
    (∀ j ≤ 1, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (ω t) H̄ y‖ ≤ max B (max B₁ M₁)) ∧
    ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 1 (ω t) H̄ y - iteratedFDerivWithin ℝ 1 (ω t) H̄ z‖ ≤
        max B (max B₁ M₁) * ‖y - z‖ ^ α := by
  refine ⟨fun j hj y hy ↦ ?_, fun y z hy hz ↦ ?_⟩
  · interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (hω.abs_le t ht y hy).trans (le_max_left _ _)
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)]
      exact (hω.norm_fderivWithin_le t ht y hy).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hω.holder_iteratedFDerivWithin ht y z hy hz).trans (by
      gcongr
      exact (le_max_right _ _).trans (le_max_right _ _))

/-- At every time the field of the law is `C²` within the closed half-plane. -/
theorem contDiffOn_law_two (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (U (ω t)) H̄ := by
  obtain ⟨hN, hM⟩ := hω.levelOne_data ht
  exact_mod_cast hU.contDiffOn_succ (k := 1) le_rfl hα hα1 hR
    (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero t ht) hN hM

/-- At every time the second derivatives of the field of the law within the closed half-plane are
bounded by `C 1 α · max B (max B₁ M₁)`. -/
theorem norm_fderivWithin_fderivWithin_law_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (U (ω t)) H̄) H̄ x‖ ≤ C 1 α * max B (max B₁ M₁) := by
  rw [← norm_iteratedFDerivWithin_two _ hx]
  obtain ⟨hN, hM⟩ := hω.levelOne_data ht
  exact hU.norm_iteratedFDerivWithin_le (k := 1) le_rfl hα hα1 hR
    (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero t ht) hN hM 2 le_rfl x hx

/-- At every time the second derivatives of the field of the law within the closed half-plane are
`α`-Hölder on it with constant `C 1 α · max B (max B₁ M₁)`. -/
theorem norm_fderivWithin_fderivWithin_law_sub_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {t : ℝ} (ht : t ∈ Icc a b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (U (ω t)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (U (ω t)) H̄) H̄ z‖ ≤
      C 1 α * max B (max B₁ M₁) * ‖y - z‖ ^ α := by
  obtain ⟨hN, hM⟩ := hω.levelOne_data ht
  have h := hU.holder_iteratedFDerivWithin (k := 1) le_rfl hα hα1 hR
    (by exact_mod_cast hω.contDiffOn t ht) (hω.eq_zero t ht) hN hM y z hy hz
  rwa [norm_iteratedFDerivWithin_succ_sub _ hy hz 1, norm_iteratedFDerivWithin_one_sub _ hy hz]
    at h

/-- **Continuity in time of the second derivatives of the field of the law**, uniformly on the
closed half-plane: the difference `g = ω s - ω t` is small in `C¹` with an `α`-Hölder gradient of
constant `2 M₁`, hence small in `C^{1,α/2}`, and the `C²` bound of the law at the exponent `α/2`
applies. -/
theorem exists_norm_fderivWithin_fderivWithin_law_sub_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (U (ω s)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (U (ω t)) H̄) H̄ y‖ ≤ ε := by
  have hM₁ : 0 ≤ M₁ := by
    have h := hω.holder_fderivWithin t ht (EuclideanSpace.single 0 1) 0 (by simp) (by simp)
    have hn : ‖(EuclideanSpace.single 0 1 : ℝ^2)‖ = 1 := by simp
    rw [sub_zero, hn, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set α' := α / 2 with hα'def
  have hα' : 0 < α' := by positivity
  have hα'1 : α' < 1 := by linarith
  have hC := hU.const_nonneg 1 α'
  -- the smallness needed: `C 1 α' · η' ≤ ε` with `η'` the `C^{1,α'}` size of the difference
  set η' := ε / (C 1 α' + 1) with hη'def
  have hη' : 0 < η' := by positivity
  have hη'ε : C 1 α' * η' ≤ ε := by
    rw [hη'def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  -- a gradient size `η₁` with `η₁ ≤ η'` and `2 η₁^{1/2} M₁^{1/2} ≤ η'`
  set η₁ := min η' ((η' / (2 * (M₁ + 1) ^ (1 / 2 : ℝ))) ^ 2) with hη₁def
  have hM1p : 0 < (M₁ + 1) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hη₁ : 0 < η₁ := lt_min hη' (by positivity)
  obtain ⟨δ₀, hδ₀, hδ₀t⟩ := hω.uniform t ht η' hη'
  obtain ⟨δ₁, hδ₁, hδ₁t⟩ := hω.uniform_fderivWithin t ht η₁ hη₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun s hs hst y hy ↦ ?_⟩
  have hst₀ : |s - t| < δ₀ := hst.trans_le (min_le_left _ _)
  have hst₁ : |s - t| < δ₁ := hst.trans_le (min_le_right _ _)
  obtain ⟨hgc, hgd, hgM⟩ := hω.fderivWithin_sub_data hs ht
  -- the data of the difference at the exponent `α'`
  have hN : ∀ j ≤ 1, ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ j (ω s - ω t) H̄ z‖ ≤ η' := by
    intro j hj z hz
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact hδ₀t s hs hst₀ z hz
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper z hz), hgd z hz]
      exact (hδ₁t s hs hst₁ z hz).trans (min_le_left _ _)
  have hM' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ y - iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖ ≤
        η' * ‖y - z‖ ^ α' := by
    intro y z hy hz
    set D := ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ y -
      iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖
    have hd0 : 0 ≤ ‖y - z‖ := norm_nonneg _
    have hD1 : D ≤ 2 * η₁ := by
      have h1 : ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ y‖ ≤ η₁ := by
        rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy), hgd y hy]
        exact hδ₁t s hs hst₁ y hy
      have h2 : ‖iteratedFDerivWithin ℝ 1 (ω s - ω t) H̄ z‖ ≤ η₁ := by
        rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper z hz), hgd z hz]
        exact hδ₁t s hs hst₁ z hz
      exact (norm_sub_le _ _).trans (by linarith)
    have hD2 : D ≤ 2 * M₁ * ‖y - z‖ ^ α := hgM y z hy hz
    have hmin := min_le_rpow_mul_rpow (by positivity : (0 : ℝ) ≤ 2 * η₁)
      (by positivity : (0 : ℝ) ≤ 2 * M₁ * ‖y - z‖ ^ α)
    have hsplit : (2 * M₁ * ‖y - z‖ ^ α) ^ (1 / 2 : ℝ) =
        (2 * M₁) ^ (1 / 2 : ℝ) * ‖y - z‖ ^ α' := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hd0 _), ← Real.rpow_mul hd0, hα'def]
      ring_nf
    have hη₁b : (2 * η₁) ^ (1 / 2 : ℝ) * (2 * M₁) ^ (1 / 2 : ℝ) ≤ η' := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have hle : 2 * η₁ * (2 * M₁) ≤ (η' / (M₁ + 1) ^ (1 / 2 : ℝ)) ^ 2 * (M₁ + 1) := by
        have h1 : η₁ ≤ (η' / (2 * (M₁ + 1) ^ (1 / 2 : ℝ))) ^ 2 := min_le_right _ _
        have h2 : (η' / (2 * (M₁ + 1) ^ (1 / 2 : ℝ))) ^ 2 =
            (η' / (M₁ + 1) ^ (1 / 2 : ℝ)) ^ 2 / 4 := by
          field_simp; ring
        rw [h2] at h1
        nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 4 * M₁)]
      have hsq : (η' / (M₁ + 1) ^ (1 / 2 : ℝ)) ^ 2 * (M₁ + 1) = η' ^ 2 := by
        have hp : ((M₁ + 1) ^ (1 / 2 : ℝ)) ^ 2 = M₁ + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
        field_simp
        rw [hp]
      rw [hsq] at hle
      calc (2 * η₁ * (2 * M₁)) ^ (1 / 2 : ℝ) ≤ (η' ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
        _ = η' := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hη'.le]; norm_num
    calc D ≤ min (2 * η₁) (2 * M₁ * ‖y - z‖ ^ α) := le_min hD1 hD2
      _ ≤ (2 * η₁) ^ (1 / 2 : ℝ) * ((2 * M₁) ^ (1 / 2 : ℝ) * ‖y - z‖ ^ α') := by
          rw [← hsplit]; exact hmin
      _ ≤ η' * ‖y - z‖ ^ α' := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hη₁b (Real.rpow_nonneg hd0 _)
  -- the second derivative of the field of the difference
  have hsub := hU.sub hR (hω.continuousOn s hs) (hω.eq_zero s hs) (hω.continuousOn t ht)
    (hω.eq_zero t ht)
  have hus := hω.contDiffOn_law_two hU hR hα hα1 hs
  have hut := hω.contDiffOn_law_two hU hR hα hα1 ht
  have hus1 : ContDiffOn ℝ 1 (fderivWithin ℝ (U (ω s)) H̄) H̄ :=
    hus.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hut1 : ContDiffOn ℝ 1 (fderivWithin ℝ (U (ω t)) H̄) H̄ :=
    hut.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have heq : EqOn (fderivWithin ℝ (U (ω s - ω t)) H̄)
      (fderivWithin ℝ (U (ω s)) H̄ - fderivWithin ℝ (U (ω t)) H̄) H̄ := fun z hz ↦ by
    have hcongr : fderivWithin ℝ (U (ω s - ω t)) H̄ z =
        fderivWithin ℝ (U (ω s) - U (ω t)) H̄ z :=
      fderivWithin_congr (fun w hw ↦ hsub w hw) (hsub z hz)
    rw [hcongr]
    exact fderivWithin_sub (uniqueDiffOn_closedUpper z hz)
      ((hus.differentiableOn (by norm_num)) z hz) ((hut.differentiableOn (by norm_num)) z hz)
  have hD2 : fderivWithin ℝ (fderivWithin ℝ (U (ω s - ω t)) H̄) H̄ y =
      fderivWithin ℝ (fderivWithin ℝ (U (ω s)) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (U (ω t)) H̄) H̄ y := by
    rw [fderivWithin_congr heq (heq hy)]
    exact fderivWithin_sub (uniqueDiffOn_closedUpper y hy)
      ((hus1.differentiableOn one_ne_zero) y hy) ((hut1.differentiableOn one_ne_zero) y hy)
  rw [← hD2, ← norm_iteratedFDerivWithin_two _ hy]
  refine (hU.norm_iteratedFDerivWithin_le (k := 1) le_rfl hα' hα'1 hR
    (by exact_mod_cast hgc) (fun z hz hzR ↦ by
      simp [hω.eq_zero s hs z hz hzR, hω.eq_zero t ht z hz hzR]) hN hM' 2 le_rfl y hy).trans hη'ε

/-- **The fields of the law of a `C¹` vorticity history form a `C²` field.** For `0 < α < 1` the
fields `lawField U ω t`, `t ∈ [a, b]`, and their first two derivatives are jointly continuous on
`[a, b] × ℝ²`, with the first derivatives bounded by `2 reflectionBound 2 1` times the Kato bound
and the second by `2 reflectionBound 2 2 · C 1 α · max B (max B₁ M₁)`. This is what the flow
theory needs for a flow with two spatial derivatives. Proof: at each time the field of the law
is `C²` within the closed half-plane by the Schauder estimate of the law, the weighted
reflection of order two keeps this regularity and the bounds, and the continuity in time of the
second derivatives is `exists_norm_fderivWithin_fderivWithin_law_sub_le`. -/
theorem isC2FieldOn_lawField (hU : IsVelocityLaw U R₀ C)
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1) :
    PDE.Analysis.ODE.IsC2FieldOn (lawField U ω) (lawFieldDeriv U ω) (lawFieldDeriv₂ U ω) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
        (C 0 α * (1 + B * Real.log (2 + M) + B))))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        (C 1 α * max B (max B₁ M₁)))) where
  toIsC1FieldOn := hω.toIsVorticityHistory.isC1FieldOn_extendedField_law hU hR hα hα1
    (by norm_num) fun _ ht ↦ hω.contDiffOn_law_two hU hR hα hα1 ht
  continuousOn_deriv₂ := by
    have hcomp (k : Fin 2) : ContinuousOn (fun p : ℝ × ℝ^2 ↦ fderiv ℝ (fderiv ℝ
        (weightedReflectionFun 1 2 (fun y ↦ U (ω p.1) y k))) p.2)
        (Icc a b ×ˢ univ) := by
      refine PDE.Analysis.continuousOn_fderiv_fderiv_weightedReflectionFun 1 le_rfl
        (f := fun t y ↦ U (ω t) y k)
        (fun t ht ↦ contDiffOn_apply (hω.contDiffOn_law_two hU hR hα hα1 ht) k)
        (fun t ht ε hε ↦ ?_)
      obtain ⟨δ, hδ, h⟩ := hω.exists_norm_fderivWithin_fderivWithin_law_sub_le hU hR hα hα1 ht hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      exact (norm_fderivWithin_fderivWithin_apply_sub_le hy
        (by exact_mod_cast hω.contDiffOn_law_two hU hR hα hα1 hs)
        (by exact_mod_cast hω.contDiffOn_law_two hU hR hα hα1 ht) k).trans
          (h s hs hst y hy)
    have heq : EqOn (Function.uncurry fun t x ↦ fderiv ℝ (fderiv ℝ (lawField U ω t)) x)
        (fun p : ℝ × ℝ^2 ↦ (toComponentL 0).comp (fderiv ℝ (fderiv ℝ
            (weightedReflectionFun 1 2 (fun y ↦ U (ω p.1) y 0))) p.2) +
          (toComponentL 1).comp (fderiv ℝ (fderiv ℝ
            (weightedReflectionFun 1 2 (fun y ↦ U (ω p.1) y 1))) p.2))
        (Icc a b ×ˢ univ) := fun p hp ↦ by
      change fderiv ℝ (fderiv ℝ (extendedField 2 (U (ω p.1)))) p.2 = _
      rw [fderiv_fderiv_extendedField le_rfl (hω.contDiffOn_law_two hU hR hα hα1 hp.1),
        Fin.sum_univ_two]
    refine ContinuousOn.congr ?_ heq
    have : ContinuousAdd (ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) :=
      (inferInstance : IsTopologicalAddGroup (ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2)).toContinuousAdd
    exact (((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2 →L[ℝ] ℝ) (ℝ^2 →L[ℝ] ℝ^2)
      (toComponentL 0)).continuous.comp_continuousOn (hcomp 0)).add
      ((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2 →L[ℝ] ℝ) (ℝ^2 →L[ℝ] ℝ^2)
        (toComponentL 1)).continuous.comp_continuousOn (hcomp 1)))
  hasFDerivAt_deriv t ht x := by
    have hE := (contDiff_extendedField (by norm_num)
      (hω.contDiffOn_law_two hU hR hα hα1 ht)).fderiv_right (m := 1) (by norm_num)
    exact ((hE.differentiable one_ne_zero) x).hasFDerivAt
  norm_deriv₂_le t ht x :=
    (norm_fderiv_fderiv_extendedField_le le_rfl
      (hω.contDiffOn_law_two hU hR hα hα1 ht)
      (fun _ hy ↦ hω.norm_fderivWithin_fderivWithin_law_le hU hR hα hα1 ht hy) x).trans
        (Real.le_coe_toNNReal _)

end IncompressibleFlow.IsC1VorticityHistory
