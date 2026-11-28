/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Field
public import PDE.Fluid.Incompressible.HalfPlane.VelocityFieldHigher

/-!
# The fields of a velocity law at level `k`

If the vorticity has `k` derivatives with a Hölder condition, the velocity has one derivative more.
This module shows that the gain is uniform and continuous in time along a history, so that the
extended velocity fields form a family whose flow has `k + 1` derivatives, and that the flow on the
closed half-plane `H̄` does not depend on the order of the extension across the boundary.

Let `U` be a velocity law up to the radius `R₀` (`IsVelocityLaw U R₀ C`) and `ω` a `C^{k,α}`
vorticity history (`IncompressibleFlow.IsCkVorticityHistory k`), `k ≥ 1`, `0 < α < 1`, supported in
the disc of radius `R ≤ R₀`. At every time the field `U (ω t)` is `C^{k+1}` within `H̄`, its
derivatives of order at most `k + 1` are at most `C k α · N` and the derivative of order `k + 1` is
`α`-Hölder with constant `C k α · N`. These derivatives are continuous in time uniformly on `H̄`:
the difference `ω s - ω t` is uniformly small in `C^k` on `H̄` and its derivative of order `k` is
`α`-Hölder with constant `2N`, hence it is small in `C^{k,α/2}`, and the bound of the law at the
exponent `α/2` applies to it.

The extensions `extendedField (k + 1) (U (ω t))` by the weighted reflection of order `k + 1` are
therefore a smooth family of order `k + 1` in the sense of `PDE.Analysis.IsSmoothFamilyOn` and a
`C¹` field on `[a, b] × ℝ²`. Extensions of different orders have the same flow and the same first
variation on `H̄`, since the flows preserve `H̄` and the fields and their derivatives agree there;
in particular, on `H̄`, the flow of `lawField U ω` is the flow of the extension of order `k + 1`.

## Main results

* `HalfPlaneSystem.iteratedFDeriv_extendedField_of_nonneg`: on `H̄` the derivatives of order at most
  `K` of the extension of order `K` are those of the field within `H̄`.
* `IncompressibleFlow.IsCkVorticityHistory.contDiffOn_law`,
  `IncompressibleFlow.IsCkVorticityHistory.norm_iteratedFDerivWithin_law_le`,
  `IncompressibleFlow.IsCkVorticityHistory.holder_iteratedFDerivWithin_law`: the bounds of the law
  at every time of the history.
* `IncompressibleFlow.IsCkVorticityHistory.exists_norm_iteratedFDerivWithin_law_sub_le`: continuity
  in time of the derivatives of order at most `k + 1`, uniformly on `H̄`.
* `IncompressibleFlow.IsCkVorticityHistory.isSmoothFamilyOn_extendedField_law`,
  `IncompressibleFlow.IsCkVorticityHistory.isC1FieldOn_extendedField_law`: the extensions of order
  `k + 1` are a smooth family of order `k + 1` and a `C¹` field.
* `HalfPlaneSystem.mapsTo_flowOn_extendedField`, `HalfPlaneSystem.flowOn_extendedField_eq`,
  `HalfPlaneSystem.variationOn_extendedField_eq`: the flow of an extension preserves `H̄`, and
  extensions of two orders have the same flow and the same first variation on `H̄`.
* `HalfPlaneSystem.flowOn_lawField_eq`, `HalfPlaneSystem.variationOn_lawField_eq`: the case of
  `lawField U ω`, the extension of order two, and the extension of order `k + 1`.

The bound `C k α · N` of the derivative of order `k + 1` uses the full norm `N` of the history;
`FieldHigherFlow.lean` proves the bound that is linear in the top order alone and derives the bounds
of the flow maps at level `k`. `CarriedHigher.lean` and `CarriedHigherForcing.lean` use the
identification of the flows, and `RegularField.lean` uses the smooth family for the field of a
regular solution.
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal
open IncompressibleFlow PDE.Analysis.ODE SobolevSpace.GraphSpace.HigherOrderReflection

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The extended field as the sum of its two components placed in the coordinate directions. -/
theorem extendedField_eq_sum (K : ℕ) (u : ℝ^2 → ℝ^2) :
    extendedField K u = fun x ↦
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          (weightedReflectionFun 1 K (fun y ↦ u y 0) x) +
        ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
          (weightedReflectionFun 1 K (fun y ↦ u y 1) x) := by
  funext x
  ext c
  fin_cases c <;> simp [extendedField_apply]

/-- On the closed half-plane the iterated derivatives of the extended field are those of the
field within the closed half-plane. -/
theorem iteratedFDeriv_extendedField_of_nonneg {u : ℝ^2 → ℝ^2} {K : ℕ} (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K u H̄) {m : ℕ} (hm : m ≤ K) {x : ℝ^2} (hx : 0 ≤ x 1) :
    iteratedFDeriv ℝ m (extendedField K u) x = iteratedFDerivWithin ℝ m u H̄ x := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_closedUpper
    (((contDiff_extendedField hK hu).of_le (by exact_mod_cast hm)).contDiffAt) hx]
  have h : EqOn (extendedField K u) u H̄ := fun y hy ↦ extendedField_of_nonneg K u hy
  exact iteratedFDerivWithin_congr h hx m

/-- A step common to finitely many orders: if for every order `i ≤ k` some positive step has the
property `P i`, and the properties pass to smaller steps, one positive step has all of them. -/
private theorem exists_pos_forall_le {k : ℕ} {P : ℕ → ℝ → Prop}
    (hP : ∀ i δ δ', δ' ≤ δ → P i δ → P i δ') (h : ∀ i ≤ k, ∃ δ > 0, P i δ) :
    ∃ δ > 0, ∀ i ≤ k, P i δ := by
  induction k with
  | zero =>
    obtain ⟨δ, hδ, h0⟩ := h 0 le_rfl
    exact ⟨δ, hδ, fun i hi ↦ by rw [Nat.le_zero.mp hi]; exact h0⟩
  | succ k ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih fun i hi ↦ h i (hi.trans (Nat.le_succ k))
    obtain ⟨δ₂, hδ₂, h₂⟩ := h (k + 1) le_rfl
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun i hi ↦ ?_⟩
    rcases Nat.lt_or_ge i (k + 1) with hik | hik
    · exact hP i δ₁ _ (min_le_left _ _) (h₁ i (by omega))
    · rw [show i = k + 1 by omega]
      exact hP (k + 1) δ₂ _ (min_le_right _ _) h₂

/-- **Interpolation of a small difference**: a quantity at most `2 η² / (4 (M + 1))` and at most
`2 M d^α` is at most `η d^{α/2}`. -/
private theorem le_mul_rpow_half {D η M d α : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hd : 0 ≤ d) (h1 : D ≤ 2 * (η ^ 2 / (4 * (M + 1)))) (h2 : D ≤ 2 * M * d ^ α) :
    D ≤ η * d ^ (α / 2) := by
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd α
  have hsq : (d ^ (α / 2)) ^ 2 = d ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
    norm_num
  have hM1 : 0 < M + 1 := by linarith
  have hDD : D * D ≤ 2 * (η ^ 2 / (4 * (M + 1))) * (2 * M * d ^ α) :=
    mul_le_mul h1 h2 hD (by positivity)
  have he : 2 * (η ^ 2 / (4 * (M + 1))) * (2 * M * d ^ α) = η ^ 2 * d ^ α * (M / (M + 1)) := by
    field_simp
    ring
  have hq : M / (M + 1) ≤ 1 := (div_le_one hM1).mpr (by linarith)
  have h3 : D ^ 2 ≤ (η * d ^ (α / 2)) ^ 2 := by
    rw [mul_pow, hsq, sq]
    nlinarith [mul_nonneg (sq_nonneg η) hdα]
  exact (pow_le_pow_iff_left₀ hD (by positivity) two_ne_zero).mp h3

end HalfPlaneSystem

namespace IncompressibleFlow.IsCkVorticityHistory

open HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {k : ℕ} {ω : ℝ → ℝ^2 → ℝ} {a b α R N : ℝ}

/-- At every time of a `C^{k,α}` history, `k ≥ 1`, the field of the law is `C^{k+1}` within the
closed half-plane. -/
theorem contDiffOn_law (hU : IsVelocityLaw U R₀ C) (hω : IsCkVorticityHistory k ω a b α R N)
    (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (U (ω t)) H̄ := by
  exact_mod_cast hU.contDiffOn_succ hk hα hα1 hR (hω.contDiffOn t ht) (hω.eq_zero t ht)
    (hω.norm_le t ht) (hω.holder t ht)

/-- At every time the derivatives of order at most `k + 1` of the field of the law are at most
`C k α · N` on the closed half-plane. -/
theorem norm_iteratedFDerivWithin_law_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {j : ℕ} (hj : j ≤ k + 1) {x : ℝ^2}
    (hx : 0 ≤ x 1) : ‖iteratedFDerivWithin ℝ j (U (ω t)) H̄ x‖ ≤ C k α * N :=
  hU.norm_iteratedFDerivWithin_le hk hα hα1 hR (hω.contDiffOn t ht) (hω.eq_zero t ht)
    (hω.norm_le t ht) (hω.holder t ht) j hj x hx

/-- At every time the derivative of order `k + 1` of the field of the law is `α`-Hölder on the
closed half-plane with constant `C k α · N`. -/
theorem holder_iteratedFDerivWithin_law (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖iteratedFDerivWithin ℝ (k + 1) (U (ω t)) H̄ x -
        iteratedFDerivWithin ℝ (k + 1) (U (ω t)) H̄ x'‖ ≤ C k α * N * ‖x - x'‖ ^ α :=
  hU.holder_iteratedFDerivWithin hk hα hα1 hR (hω.contDiffOn t ht) (hω.eq_zero t ht)
    (hω.norm_le t ht) (hω.holder t ht) x x' hx hx'

/-- **Continuity in time of the derivatives of the field of the law**, uniformly on the closed
half-plane, for every order `j ≤ k + 1`: for `s` close to `t` the difference `ω s - ω t` is small
in `C^k` and its derivative of order `k` is `α`-Hölder with constant `2N`, hence small in
`C^{k,α/2}`, and the bound of the law at the exponent `α/2` applies to it. -/
theorem exists_norm_iteratedFDerivWithin_law_sub_le (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {j : ℕ} (hj : j ≤ k + 1) {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (U (ω s)) H̄ y - iteratedFDerivWithin ℝ j (U (ω t)) H̄ y‖ ≤
        ε := by
  have hN := hω.nonneg ht
  set α' := α / 2 with hα'def
  have hα' : 0 < α' := by positivity
  have hα'1 : α' < 1 := by linarith
  have hC := hU.const_nonneg k α'
  set η := ε / (C k α' + 1) with hηdef
  have hη : 0 < η := by positivity
  have hηε : C k α' * η ≤ ε := by
    rw [hηdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  set η₁ := min η (η ^ 2 / (4 * (N + 1))) with hη₁def
  have hη₁ : 0 < η₁ := lt_min hη (by positivity)
  obtain ⟨δ, hδ, hδt⟩ := exists_pos_forall_le (k := k)
    (P := fun i δ ↦ ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ i (ω s) H̄ y - iteratedFDerivWithin ℝ i (ω t) H̄ y‖ ≤ η₁)
    (fun _ _ _ hδ' h s hs hst ↦ h s hs (hst.trans_le hδ'))
    (fun i hi ↦ hω.uniform i hi t ht η₁ hη₁)
  refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
  obtain ⟨hgc, -, hgd, hgM⟩ := hω.sub_data hs ht
  have hsmall : ∀ i ≤ k, ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ i (ω s - ω t) H̄ z‖ ≤ η₁ := fun i hi z hz ↦ by
    rw [hgd i hi z hz]; exact hδt i hi s hs hst z hz
  have hN' : ∀ i ≤ k, ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ i (ω s - ω t) H̄ z‖ ≤ η :=
    fun i hi z hz ↦ (hsmall i hi z hz).trans (min_le_left _ _)
  have hM' : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ k (ω s - ω t) H̄ z - iteratedFDerivWithin ℝ k (ω s - ω t) H̄ z'‖ ≤
        η * ‖z - z'‖ ^ α' := by
    intro z z' hz hz'
    refine le_mul_rpow_half (norm_nonneg _) hη.le hN (norm_nonneg _) ?_ (hgM z z' hz hz')
    have h1 := hsmall k le_rfl z hz
    have h2 := hsmall k le_rfl z' hz'
    have h3 := min_le_right η (η ^ 2 / (4 * (N + 1)))
    exact (norm_sub_le _ _).trans (by linarith)
  have hsub := hU.sub hR (hω.continuousOn hs) (hω.eq_zero s hs) (hω.continuousOn ht)
    (hω.eq_zero t ht)
  have hus := hω.contDiffOn_law hU hR hk hα hα1 hs
  have hut := hω.contDiffOn_law hU hR hk hα hα1 ht
  have heq : iteratedFDerivWithin ℝ j (U (ω s - ω t)) H̄ y =
      iteratedFDerivWithin ℝ j (U (ω s)) H̄ y - iteratedFDerivWithin ℝ j (U (ω t)) H̄ y := by
    have hE : EqOn (U (ω s - ω t)) (U (ω s) - U (ω t)) H̄ := fun z hz ↦ hsub z hz
    rw [iteratedFDerivWithin_congr hE hy j]
    exact iteratedFDerivWithin_sub_apply ((hus y hy).of_le (by exact_mod_cast hj))
      ((hut y hy).of_le (by exact_mod_cast hj)) uniqueDiffOn_closedUpper hy
  rw [← heq]
  exact (hU.norm_iteratedFDerivWithin_le hk hα' hα'1 hR hgc
    (fun z hz hzR ↦ by simp [hω.eq_zero s hs z hz hzR, hω.eq_zero t ht z hz hzR]) hN' hM' j hj
    y hy).trans hηε

/-- **The extended fields of the law of a `C^{k,α}` history are a smooth family of order
`k + 1`.** For `k ≥ 1` and `0 < α < 1` the fields `extendedField (k + 1) (U (ω t))`,
`t ∈ [a, b]`, are `C^{k+1}` and their derivatives of order at most `k + 1` are jointly continuous
on `[a, b] × ℝ²`. -/
theorem isSmoothFamilyOn_extendedField_law (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) :
    PDE.Analysis.IsSmoothFamilyOn (k + 1) (fun t ↦ extendedField (k + 1) (U (ω t)))
      (Icc a b) := by
  have hc (c : Fin 2) : PDE.Analysis.IsSmoothFamilyOn (k + 1)
      (fun t x ↦ weightedReflectionFun 1 (k + 1) (fun y ↦ U (ω t) y c) x) (Icc a b) := by
    refine ⟨fun t ht ↦ PDE.Analysis.contDiff_weightedReflectionFun 1 (by omega)
      (contDiffOn_apply (hω.contDiffOn_law hU hR hk hα hα1 ht) c), fun j hj ↦ ?_⟩
    refine PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 (by omega)
      (F := fun t y ↦ U (ω t) y c)
      (fun t ht ↦ contDiffOn_apply (hω.contDiffOn_law hU hR hk hα hα1 ht) c) hj
      (fun t ht ε hε ↦ ?_)
    obtain ⟨δ, hδ, h⟩ := hω.exists_norm_iteratedFDerivWithin_law_sub_le hU hR hk hα hα1 hj ht hε
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    exact (norm_iteratedFDerivWithin_apply_sub_apply_le
      ((hω.contDiffOn_law hU hR hk hα hα1 hs).of_le (by exact_mod_cast hj))
      ((hω.contDiffOn_law hU hR hk hα hα1 ht).of_le (by exact_mod_cast hj)) c hy).trans
        (h s hs hst y hy)
  refine ((((hc 0).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))).add
    ((hc 1).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))))).congr
    fun t _ ↦ ?_
  exact (extendedField_eq_sum (k + 1) (U (ω t))).symm

/-- The extended fields of order `k + 1` of the law of a `C^{k,α}` history form a `C¹` field on
`[a, b] × ℝ²`, with derivatives bounded by `2 reflectionBound (k + 1) 1` times the Kato bound. -/
theorem isC1FieldOn_extendedField_law (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) :
    IsC1FieldOn (fun t ↦ extendedField (k + 1) (U (ω t)))
      (fun t x ↦ fderiv ℝ (extendedField (k + 1) (U (ω t))) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound (k + 1) 1 *
        (C 0 α * (1 + N * Real.log (2 + 2 * N) + N)))) :=
  (hω.toIsVorticityHistory hα.le hα1.le).isC1FieldOn_extendedField_law hU hR hα hα1 (by omega)
    fun _ ht ↦ hω.contDiffOn_law hU hR hk hα hα1 ht

end IncompressibleFlow.IsCkVorticityHistory

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Extensions of different orders -/

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M : ℝ} {K K' : ℕ}

/-- The flow of an extension of the fields of the law of a vorticity history preserves the closed
half-plane. -/
theorem mapsTo_flowOn_extendedField (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) {L : ℝ≥0}
    (hv : IsLipschitzFieldOn (fun r ↦ extendedField K (U (ω r))) a b L) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    MapsTo (flowOn (fun r ↦ extendedField K (U (ω r))) a b s t) H̄ H̄ :=
  hv.mapsTo_flowOn_nonneg (j := 1) (fun _ hr _ hy ↦
    extendedField_normal_eq_zero K hy (hω.law_normal_eq_zero hU hR hr hy)) hs ht

/-- **Extensions of different orders have the same flow on the closed half-plane.** So the
flow of the system does not depend on the order of the reflection that extends the velocity.
Proof: both flows preserve the closed half-plane, where the two fields agree, and the flow of a
Lipschitz field is determined by the field on an invariant set. -/
theorem flowOn_extendedField_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    (hK : 1 ≤ K) (hK' : 1 ≤ K') (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (U (ω t)) H̄)
    (hu' : ∀ t ∈ Icc a b, ContDiffOn ℝ K' (U (ω t)) H̄) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    flowOn (fun r ↦ extendedField K (U (ω r))) a b s t x =
      flowOn (fun r ↦ extendedField K' (U (ω r))) a b s t x := by
  have hv := hω.isC1FieldOn_extendedField_law hU hR hα hα1 hK hu
  have hv' := hω.isC1FieldOn_extendedField_law hU hR hα hα1 hK' hu'
  refine flowOn_eq_of_eqOn hv.isLipschitzFieldOn hv'.isLipschitzFieldOn
    (fun s hs t ht ↦ mapsTo_flowOn_extendedField hU hω hR hv'.isLipschitzFieldOn hs ht)
    (fun r _ y hy ↦ ?_) hs ht hx
  rw [extendedField_of_nonneg K _ hy, extendedField_of_nonneg K' _ hy]

/-- **Extensions of different orders have the same first variation on the closed
half-plane.** -/
theorem variationOn_extendedField_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsVorticityHistory ω a b α R B M) (hR : R ≤ R₀) (hα : 0 < α) (hα1 : α < 1)
    (hK : 1 ≤ K) (hK' : 1 ≤ K') (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (U (ω t)) H̄)
    (hu' : ∀ t ∈ Icc a b, ContDiffOn ℝ K' (U (ω t)) H̄) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    variationOn (fun r ↦ extendedField K (U (ω r)))
        (fun r y ↦ fderiv ℝ (extendedField K (U (ω r))) y) a b s t x =
      variationOn (fun r ↦ extendedField K' (U (ω r)))
        (fun r y ↦ fderiv ℝ (extendedField K' (U (ω r))) y) a b s t x := by
  have hv := hω.isC1FieldOn_extendedField_law hU hR hα hα1 hK hu
  have hv' := hω.isC1FieldOn_extendedField_law hU hR hα hα1 hK' hu'
  refine hv.variationOn_eq_of_eqOn hv'
    (fun s hs t ht ↦ mapsTo_flowOn_extendedField hU hω hR hv'.isLipschitzFieldOn hs ht)
    (fun r _ y hy ↦ ?_) (fun r hr y hy ↦ ?_) hs ht hx
  · rw [extendedField_of_nonneg K _ hy, extendedField_of_nonneg K' _ hy]
  · change fderiv ℝ (extendedField K (U (ω r))) y = fderiv ℝ (extendedField K' (U (ω r))) y
    rw [fderiv_extendedField_of_nonneg hK (hu r hr) hy,
      fderiv_extendedField_of_nonneg hK' (hu' r hr) hy]

variable {k : ℕ} {N : ℝ}

/-- On the closed half-plane the flow of the field of a `C^{k,α}` history, `k ≥ 1`, is the flow
of the extension of order `k + 1`. -/
theorem flowOn_lawField_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    flowOn (lawField U ω) a b s t x =
      flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) a b s t x :=
  flowOn_extendedField_eq hU (hω.toIsVorticityHistory hα.le hα1.le) hR hα hα1 (K := 2)
    (K' := k + 1) (by norm_num) (by omega)
    (fun t ht ↦ (hω.contDiffOn_law hU hR hk hα hα1 ht).of_le
      (by exact_mod_cast (by omega : 2 ≤ k + 1)))
    (fun t ht ↦ hω.contDiffOn_law hU hR hk hα hα1 ht) hs ht hx

/-- On the closed half-plane the first variation of the flow of the field of a `C^{k,α}`
history, `k ≥ 1`, is that of the extension of order `k + 1`. -/
theorem variationOn_lawField_eq (hU : IsVelocityLaw U R₀ C)
    (hω : IsCkVorticityHistory k ω a b α R N) (hR : R ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    variationOn (lawField U ω) (lawFieldDeriv U ω) a b s t x =
      variationOn (fun r ↦ extendedField (k + 1) (U (ω r)))
        (fun r y ↦ fderiv ℝ (extendedField (k + 1) (U (ω r))) y) a b s t x :=
  variationOn_extendedField_eq hU (hω.toIsVorticityHistory hα.le hα1.le) hR hα hα1 (K := 2)
    (K' := k + 1) (by norm_num) (by omega)
    (fun t ht ↦ (hω.contDiffOn_law hU hR hk hα hα1 ht).of_le
      (by exact_mod_cast (by omega : 2 ≤ k + 1)))
    (fun t ht ↦ hω.contDiffOn_law hU hR hk hα hα1 ht) hs ht hx

end HalfPlaneSystem
