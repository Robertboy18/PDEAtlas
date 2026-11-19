/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Parts

/-!
# Riesz projections of bounded operators

For a bounded operator `T` on a complex Banach space `X` and a circle of radius `r > 0` that
carries no spectrum of `T`, the Riesz projection `P = rieszInner T r` splits `X` into the range
and the kernel of `P`. Both subspaces are invariant under `T`. The restriction
`rieszInnerPart T r` of `T` to the range has spectrum `σ(T) ∩ {‖z‖ < r}`, and the restriction
`rieszOuterPart T r` to the kernel has spectrum `σ(T) ∩ {‖z‖ > r}`. The powers of the inner part
decay like `ρⁿ` for some `ρ < r`. The outer part is invertible, and its inverse powers decay
like `ρ⁻ⁿ` for some `ρ > r`.

An eigenvector `T v = ν v` with `‖ν‖ < r` is fixed by `P`, and one with `‖ν‖ > r` lies in the
kernel of `P`.
-/

@[expose] public noncomputable section

open Complex Metric Set
open scoped Real

namespace PDE.Analysis.Spectral

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If `b` maps an invariant subspace `V` of `T` into itself and inverts `μ - T` on `V`, then
`μ` is not in the spectrum of the restriction of `T` to `V`. -/
theorem notMem_spectrum_restrict {V : Submodule ℂ X} {T b : X →L[ℂ] X}
    (hT : ∀ x ∈ V, T x ∈ V) (hb : ∀ x ∈ V, b x ∈ V) {μ : ℂ}
    (h₁ : ∀ x ∈ V, μ • b x - T (b x) = x) (h₂ : ∀ x ∈ V, b (μ • x - T x) = x) :
    μ ∉ spectrum ℂ (T.restrict hT) := by
  rw [spectrum.notMem_iff]
  refine ⟨⟨algebraMap ℂ _ μ - T.restrict hT, b.restrict hb, ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    simp [Algebra.algebraMap_eq_smul_one, h₁ x x.2]
  · refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    have h := h₂ x x.2
    rw [map_sub, map_smul] at h
    simpa [Algebra.algebraMap_eq_smul_one] using h

/-- The spectrum of the restriction of `T` to a subspace that is invariant under every operator
commuting with `T` lies in the spectrum of `T`. -/
theorem spectrum_restrict_subset {V : Submodule ℂ X} {T : X →L[ℂ] X} (hT : ∀ x ∈ V, T x ∈ V)
    (hV : ∀ S : X →L[ℂ] X, Commute S T → ∀ x ∈ V, S x ∈ V) :
    spectrum ℂ (T.restrict hT) ⊆ spectrum ℂ T := by
  intro μ hμ hz
  exact notMem_spectrum_restrict hT (hV _ (commute_resolvent (Commute.refl T) μ).symm)
    (fun x _ ↦ DFunLike.congr_fun (smul_one_sub_mul_resolvent hz) x)
    (fun x _ ↦ by
      have h := DFunLike.congr_fun (resolvent_mul_smul_one_sub hz) x
      rwa [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at h) hμ

/-- If `P` is idempotent and `μ - T` is invertible on the range and on the kernel of `P`,
both invariant under `T`, then `μ - T` is invertible. -/
theorem notMem_spectrum_of_restrict {P T : X →L[ℂ] X} (hP : IsIdempotentElem P)
    (hPT : Commute P T)
    (h₁ : ∀ x ∈ LinearMap.range P.toLinearMap, T x ∈ LinearMap.range P.toLinearMap)
    (h₂ : ∀ x ∈ LinearMap.ker P.toLinearMap, T x ∈ LinearMap.ker P.toLinearMap) {μ : ℂ}
    (hin : μ ∉ spectrum ℂ (T.restrict h₁)) (hout : μ ∉ spectrum ℂ (T.restrict h₂)) :
    μ ∉ spectrum ℂ T := by
  set V := LinearMap.range P.toLinearMap
  set W := LinearMap.ker P.toLinearMap
  rw [spectrum.notMem_iff] at hin hout ⊢
  obtain ⟨u, hu⟩ := hin
  obtain ⟨w, hw⟩ := hout
  have hPV : ∀ x, P x ∈ V := fun x ↦ ⟨x, rfl⟩
  have hQW : ∀ x, (1 - P) x ∈ W := fun x ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, mul_sub, mul_one,
      hP.eq, sub_self, zero_apply]
  have happ : ∀ {U : Submodule ℂ X} (hU : ∀ x ∈ U, T x ∈ U) (y : U),
      ((algebraMap ℂ (U →L[ℂ] U) μ - T.restrict hU) y : X) = μ • (y : X) - T y := by
    intro U hU y
    simp [Algebra.algebraMap_eq_smul_one]
  have hu₁ : ∀ y : V, μ • ((↑u⁻¹ : V →L[ℂ] V) y : X) - T ((↑u⁻¹ : V →L[ℂ] V) y) = y :=
    fun y ↦ by rw [← happ h₁, ← hu, ← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  have hw₁ : ∀ y : W, μ • ((↑w⁻¹ : W →L[ℂ] W) y : X) - T ((↑w⁻¹ : W →L[ℂ] W) y) = y :=
    fun y ↦ by rw [← happ h₂, ← hw, ← mul_apply_eq_comp, w.mul_inv, one_apply_eq_self]
  have hPapp : ∀ x, P (μ • x - T x) = μ • P x - T (P x) := fun x ↦ by
    rw [map_sub, map_smul, ← mul_apply_eq_comp, hPT.eq, mul_apply_eq_comp]
  have hu₂ : ∀ x, (↑u⁻¹ : V →L[ℂ] V) ⟨P (μ • x - T x), hPV _⟩ = ⟨P x, hPV x⟩ := fun x ↦ by
    have he : (⟨P (μ • x - T x), hPV _⟩ : V) = (↑u : V →L[ℂ] V) ⟨P x, hPV x⟩ :=
      Subtype.ext (by rw [hu, happ h₁]; exact hPapp x)
    rw [he, ← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  have hQapp : ∀ x, (1 - P) (μ • x - T x) = μ • (1 - P) x - T ((1 - P) x) := fun x ↦ by
    rw [map_sub, map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp T,
      ((Commute.one_left T).sub_left hPT).eq]
  have hw₂ : ∀ x, (↑w⁻¹ : W →L[ℂ] W) ⟨(1 - P) (μ • x - T x), hQW _⟩ = ⟨(1 - P) x, hQW x⟩ :=
    fun x ↦ by
      have he : (⟨(1 - P) (μ • x - T x), hQW _⟩ : W) = (↑w : W →L[ℂ] W) ⟨(1 - P) x, hQW x⟩ :=
        Subtype.ext (by rw [hw, happ h₂]; exact hQapp x)
      rw [he, ← mul_apply_eq_comp, w.inv_mul, one_apply_eq_self]
  let B : X →L[ℂ] X := V.subtypeL ∘L (↑u⁻¹ : V →L[ℂ] V) ∘L P.codRestrict V hPV +
    W.subtypeL ∘L (↑w⁻¹ : W →L[ℂ] W) ∘L (1 - P).codRestrict W hQW
  have hB : ∀ x, B x = ((↑u⁻¹ : V →L[ℂ] V) ⟨P x, hPV x⟩ : X) +
      ((↑w⁻¹ : W →L[ℂ] W) ⟨(1 - P) x, hQW x⟩ : X) := fun x ↦ rfl
  have hsum : ∀ x : X, P x + (1 - P) x = x := fun x ↦ by
    rw [sub_apply, one_apply_eq_self, add_sub_cancel]
  refine spectrum.mem_resolventSet_of_left_right_inverse (b := B) (c := B) ?_ ?_
  · refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp, sub_apply, smul_apply,
      one_apply_eq_self, hB, map_add, smul_add, add_sub_add_comm, hu₁, hw₁, one_apply_eq_self]
    exact hsum x
  · refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp, sub_apply, smul_apply,
      one_apply_eq_self, hB, hu₂, hw₂]
    exact hsum x

variable [CompleteSpace X] {T : X →L[ℂ] X} {r : ℝ}

omit [CompleteSpace X] in
/-- The Riesz projection of `T` commutes with `T`, applied to a vector. No completeness is
needed: if the operator algebra is not complete, every Bochner integral into it is `0`, and so
is the projection. -/
theorem rieszInner_apply_comm (T : X →L[ℂ] X) (r : ℝ) (x : X) :
    (rieszInner T r : X →L[ℂ] X) (T x) = T ((rieszInner T r : X →L[ℂ] X) x) := by
  by_cases hA : CompleteSpace (X →L[ℂ] X)
  · exact (DFunLike.congr_fun (commute_rieszInner (r := r) (Commute.refl T)).eq x).symm
  · have h0 : rieszInner T r = 0 := by
      simp [rieszInner, circleIntegral, intervalIntegral,
        MeasureTheory.integral_of_not_completeSpace hA]
    simp [h0]

omit [CompleteSpace X] in
/-- The range of the Riesz projection is invariant under `T`. -/
theorem mapsTo_range_rieszInner (T : X →L[ℂ] X) (r : ℝ) :
    ∀ x ∈ LinearMap.range (rieszInner T r).toLinearMap,
      T x ∈ LinearMap.range (rieszInner T r).toLinearMap := by
  rintro _ ⟨y, rfl⟩
  exact ⟨T y, rieszInner_apply_comm T r y⟩

omit [CompleteSpace X] in
/-- The kernel of the Riesz projection is invariant under `T`. -/
theorem mapsTo_ker_rieszInner (T : X →L[ℂ] X) (r : ℝ) :
    ∀ x ∈ LinearMap.ker (rieszInner T r).toLinearMap,
      T x ∈ LinearMap.ker (rieszInner T r).toLinearMap := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  rw [rieszInner_apply_comm, hx, map_zero]

/-- The part of `T` inside the circle of radius `r`: the restriction of `T` to the range of its
Riesz projection. -/
def rieszInnerPart (T : X →L[ℂ] X) (r : ℝ) :
    LinearMap.range (rieszInner T r).toLinearMap →L[ℂ]
      LinearMap.range (rieszInner T r).toLinearMap :=
  T.restrict (mapsTo_range_rieszInner T r)

/-- The part of `T` outside the circle of radius `r`: the restriction of `T` to the kernel of
its Riesz projection. -/
def rieszOuterPart (T : X →L[ℂ] X) (r : ℝ) :
    LinearMap.ker (rieszInner T r).toLinearMap →L[ℂ]
      LinearMap.ker (rieszInner T r).toLinearMap :=
  T.restrict (mapsTo_ker_rieszInner T r)

omit [CompleteSpace X] in
private theorem smul_one_sub_mul_apply (μ : ℂ) (b : X →L[ℂ] X) (x : X) :
    ((μ • (1 : X →L[ℂ] X) - T) * b) x = μ • b x - T (b x) := rfl

omit [CompleteSpace X] in
private theorem mul_smul_one_sub_apply (μ : ℂ) (b : X →L[ℂ] X) (x : X) :
    (b * (μ • (1 : X →L[ℂ] X) - T)) x = b (μ • x - T x) := by
  simp

/-- **The spectrum of the inner part lies in the open disc of radius `r`.** -/
theorem spectrum_rieszInnerPart_subset (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    spectrum ℂ (rieszInnerPart T r) ⊆ ball 0 r := by
  intro μ hμ
  rw [mem_ball_zero_iff]
  by_contra hle
  obtain ⟨b, h₁, h₂, h₃, -⟩ := exists_inner_resolvent hr hfree (not_lt.mp hle)
  have hfix : ∀ x ∈ LinearMap.range (rieszInner T r).toLinearMap,
      (rieszInner T r : X →L[ℂ] X) x = x := by
    rintro _ ⟨y, rfl⟩
    exact DFunLike.congr_fun (rieszInner_idem hfree).eq y
  refine notMem_spectrum_restrict (mapsTo_range_rieszInner T r) (b := b) ?_ ?_ ?_ hμ
  · intro x _
    exact ⟨b x, DFunLike.congr_fun h₃ x⟩
  · intro x hx
    rw [← smul_one_sub_mul_apply, h₁, hfix x hx]
  · intro x hx
    rw [← mul_smul_one_sub_apply, h₂, hfix x hx]

/-- **The spectrum of the outer part lies outside the closed disc of radius `r`.** -/
theorem spectrum_rieszOuterPart_subset (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    spectrum ℂ (rieszOuterPart T r) ⊆ (closedBall 0 r)ᶜ := by
  intro μ hμ hμc
  rw [mem_closedBall_zero_iff] at hμc
  obtain ⟨b, h₁, h₂, h₃, -⟩ := exists_outer_resolvent hr hfree hμc
  have hPb : rieszInner T r * b = 0 := by
    rw [← h₃, ← mul_assoc, mul_sub, mul_one, (rieszInner_idem hfree).eq, sub_self, zero_mul]
  have hfix : ∀ x ∈ LinearMap.ker (rieszInner T r).toLinearMap,
      (1 - rieszInner T r : X →L[ℂ] X) x = x := by
    intro x hx
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    simp [hx]
  refine notMem_spectrum_restrict (mapsTo_ker_rieszInner T r) (b := b) ?_ ?_ ?_ hμ
  · intro x _
    exact DFunLike.congr_fun hPb x
  · intro x hx
    rw [← smul_one_sub_mul_apply, h₁, hfix x hx]
  · intro x hx
    rw [← mul_smul_one_sub_apply, h₂, hfix x hx]

omit [CompleteSpace X] in
/-- The powers of the inner part act as the powers of `T`. -/
theorem rieszInnerPart_pow_apply (n : ℕ) (x : LinearMap.range (rieszInner T r).toLinearMap) :
    ((rieszInnerPart T r ^ n) x : X) = (T ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, rieszInnerPart, ContinuousLinearMap.coe_restrict_apply,
      ← rieszInnerPart, ih, pow_succ', mul_apply_eq_comp]

/-- **Power bound on the inner part.** `‖(T|_{range P})^n‖ ≤ C ρ^n` for some `0 < ρ < r`. -/
theorem exists_norm_rieszInnerPart_pow_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < r ∧ 0 ≤ C ∧ ∀ n : ℕ, ‖rieszInnerPart T r ^ n‖ ≤ C * ρ ^ n := by
  obtain ⟨ρ, C, hρ, hρr, hC, h⟩ := exists_norm_pow_mul_rieszInner_le hr hfree
  refine ⟨ρ, C, hρ, hρr, hC, fun n ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    fun x ↦ ?_⟩
  obtain ⟨_, y, rfl⟩ := x
  have hfix : (rieszInner T r : X →L[ℂ] X) ((rieszInner T r : X →L[ℂ] X) y) =
      (rieszInner T r : X →L[ℂ] X) y := DFunLike.congr_fun (rieszInner_idem hfree).eq y
  rw [← Submodule.norm_coe, rieszInnerPart_pow_apply]
  calc ‖(T ^ n) ((rieszInner T r).toLinearMap y)‖
      = ‖(T ^ n * rieszInner T r) ((rieszInner T r : X →L[ℂ] X) y)‖ := by
        rw [mul_apply_eq_comp, ContinuousLinearMap.coe_coe, hfix]
    _ ≤ ‖T ^ n * rieszInner T r‖ * ‖(rieszInner T r : X →L[ℂ] X) y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ρ ^ n * ‖(rieszInner T r).toLinearMap y‖ :=
        mul_le_mul_of_nonneg_right (h n) (norm_nonneg _)

/-- The kernel of the Riesz projection is invariant under the outer inverse. -/
theorem mapsTo_ker_rieszOuterInverse (T : X →L[ℂ] X) (r : ℝ) :
    ∀ x ∈ LinearMap.ker (rieszInner T r).toLinearMap,
      rieszOuterInverse T r x ∈ LinearMap.ker (rieszInner T r).toLinearMap := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  have hc := commute_rieszInner (r := r) (commute_rieszOuterInverse (Commute.refl T) r).symm
  rw [← mul_apply_eq_comp, ← hc.eq, mul_apply_eq_comp, hx, map_zero]

/-- The inverse of the outer part: the restriction of `rieszOuterInverse T r` to the kernel of
the Riesz projection. -/
def rieszOuterPartInverse (T : X →L[ℂ] X) (r : ℝ) :
    LinearMap.ker (rieszInner T r).toLinearMap →L[ℂ]
      LinearMap.ker (rieszInner T r).toLinearMap :=
  (rieszOuterInverse T r).restrict (mapsTo_ker_rieszOuterInverse T r)

/-- The outer part of `T` is invertible, with inverse `rieszOuterPartInverse T r`. -/
theorem rieszOuterPart_mul_rieszOuterPartInverse (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    rieszOuterPart T r * rieszOuterPartInverse T r = 1 ∧
      rieszOuterPartInverse T r * rieszOuterPart T r = 1 := by
  have hres := sphere_subset_resolventSet hfree
  have hfix : ∀ x ∈ LinearMap.ker (rieszInner T r).toLinearMap,
      (1 - rieszInner T r : X →L[ℂ] X) x = x := by
    intro x hx
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    simp [hx]
  constructor
  · refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    change (T * rieszOuterInverse T r) x = x
    rw [mul_rieszOuterInverse hr hres, hfix x x.2]
  · refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    change (rieszOuterInverse T r * T) x = x
    rw [rieszOuterInverse_mul hr hres, hfix x x.2]

/-- The powers of the inverse of the outer part act as the powers of the outer inverse. -/
theorem rieszOuterPartInverse_pow_apply (n : ℕ)
    (x : LinearMap.ker (rieszInner T r).toLinearMap) :
    ((rieszOuterPartInverse T r ^ n) x : X) = (rieszOuterInverse T r ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, rieszOuterPartInverse,
      ContinuousLinearMap.coe_restrict_apply, ← rieszOuterPartInverse, ih, pow_succ',
      mul_apply_eq_comp]

/-- **Inverse bound on the outer part.** `‖(T|_{ker P})^{-n}‖ ≤ C ρ^{-n}` for some `ρ > r`. -/
theorem exists_norm_rieszOuterPartInverse_pow_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    ∃ ρ C : ℝ, r < ρ ∧ 0 ≤ C ∧ ∀ n : ℕ, ‖rieszOuterPartInverse T r ^ n‖ ≤ C * (ρ ^ n)⁻¹ := by
  obtain ⟨ρ, C, hρ, hC, h⟩ := exists_norm_rieszOuterInverse_pow_mul_le hr hfree
  have hρ0 : 0 < ρ := hr.trans hρ
  refine ⟨ρ, C, hρ, hC, fun n ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    fun x ↦ ?_⟩
  have hfix : (1 - rieszInner T r : X →L[ℂ] X) x = x := by
    have hx := x.2
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    simp [hx]
  rw [← Submodule.norm_coe, rieszOuterPartInverse_pow_apply]
  calc ‖(rieszOuterInverse T r ^ n) (x : X)‖
      = ‖(rieszOuterInverse T r ^ n * (1 - rieszInner T r)) (x : X)‖ := by
        rw [mul_apply_eq_comp, hfix]
    _ ≤ ‖rieszOuterInverse T r ^ n * (1 - rieszInner T r)‖ * ‖(x : X)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * (ρ ^ n)⁻¹ * ‖(x : X)‖ := mul_le_mul_of_nonneg_right (h n) (norm_nonneg _)

/-- **Spectral decomposition.** If the circle of radius `r` carries no spectrum of `T`, the
spectrum of `T` is the union of the spectra of its inner and outer parts. -/
theorem spectrum_eq_union_rieszParts (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    spectrum ℂ T = spectrum ℂ (rieszInnerPart T r) ∪ spectrum ℂ (rieszOuterPart T r) := by
  have hPT : Commute (rieszInner T r) T := (commute_rieszInner (Commute.refl T)).symm
  refine Set.Subset.antisymm (fun μ hμ ↦ ?_) (Set.union_subset ?_ ?_)
  · by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    exact notMem_spectrum_of_restrict (rieszInner_idem hfree) hPT
      (mapsTo_range_rieszInner T r) (mapsTo_ker_rieszInner T r) hnot.1 hnot.2 hμ
  · refine spectrum_restrict_subset _ fun S hS ↦ ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨S y, (DFunLike.congr_fun (commute_rieszInner (r := r) hS).eq y).symm⟩
  · refine spectrum_restrict_subset _ fun S hS x hx ↦ ?_
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [← mul_apply_eq_comp, ← (commute_rieszInner (r := r) hS).eq, mul_apply_eq_comp, hx,
      map_zero]

/-- The spectrum of the inner part is the part of the spectrum of `T` in the open disc. -/
theorem spectrum_rieszInnerPart_eq (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    spectrum ℂ (rieszInnerPart T r) = spectrum ℂ T ∩ ball 0 r := by
  rw [spectrum_eq_union_rieszParts hfree]
  refine Set.Subset.antisymm (fun μ hμ ↦ ⟨Or.inl hμ, spectrum_rieszInnerPart_subset hr hfree hμ⟩)
    fun μ ⟨hμ, hb⟩ ↦ hμ.resolve_right fun h ↦
      spectrum_rieszOuterPart_subset hr hfree h (ball_subset_closedBall hb)

/-- The spectrum of the outer part is the part of the spectrum of `T` outside the closed
disc. -/
theorem spectrum_rieszOuterPart_eq (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    spectrum ℂ (rieszOuterPart T r) = spectrum ℂ T \ closedBall 0 r := by
  rw [spectrum_eq_union_rieszParts hfree]
  refine Set.Subset.antisymm (fun μ hμ ↦ ⟨Or.inr hμ, spectrum_rieszOuterPart_subset hr hfree hμ⟩)
    fun μ ⟨hμ, hb⟩ ↦ hμ.resolve_left fun h ↦
      hb (ball_subset_closedBall (spectrum_rieszInnerPart_subset hr hfree h))

omit [CompleteSpace X] in
/-- On an eigenvector `T v = ν v`, the resolvent acts as `(z - ν)⁻¹`. -/
theorem resolvent_apply_of_apply_eq_smul {v : X} {ν z : ℂ} (hv : T v = ν • v)
    (hz : z ∈ resolventSet ℂ T) (hzν : z ≠ ν) :
    resolvent T z v = (z - ν)⁻¹ • v := by
  have h := DFunLike.congr_fun (resolvent_mul_smul_one_sub hz) v
  rw [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, hv, ← sub_smul, map_smul]
    at h
  calc resolvent T z v = (z - ν)⁻¹ • ((z - ν) • resolvent T z v) := by
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hzν), one_smul]
    _ = (z - ν)⁻¹ • v := by rw [h]

/-- On an eigenvector `T v = ν v` with `‖ν‖ ≠ r`, the Riesz projection acts as the scalar
`(2πi)⁻¹ ∮_{|z| = r} (z - ν)⁻¹ dz`. -/
theorem rieszInner_apply_of_apply_eq_smul (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) {v : X} {ν : ℂ} (hv : T v = ν • v)
    (hν : ‖ν‖ ≠ r) :
    (rieszInner T r : X →L[ℂ] X) v = ((2 * π * I)⁻¹ * ∮ z in C(0, r), (z - ν)⁻¹) • v := by
  have hres := sphere_subset_resolventSet hfree
  have hRi : CircleIntegrable (resolvent T) 0 r :=
    (continuousOn_resolvent.mono hres).circleIntegrable hr.le
  have hP : rieszInner T r = (2 * π * I)⁻¹ • ∮ z in C(0, r), resolvent T z := by
    rw [rieszInner_eq_rieszIntegral]
    unfold rieszIntegral
    simp only [Pi.one_apply, one_smul]
  have hl := (ContinuousLinearMap.apply ℂ X v).map_circleIntegral hRi
  simp only [ContinuousLinearMap.apply_apply] at hl
  rw [hP, smul_apply, hl, circleIntegral.integral_congr hr.le fun z hz ↦
    resolvent_apply_of_apply_eq_smul hv (hres hz) fun h ↦ hν (by
      rw [← h]; exact mem_sphere_zero_iff_norm.mp hz),
    circleIntegral.integral_smul_const, smul_smul]

/-- An eigenvector whose eigenvalue lies inside the circle is fixed by the Riesz projection. -/
theorem rieszInner_apply_eq_self_of_apply_eq_smul (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) {v : X} {ν : ℂ} (hv : T v = ν • v)
    (hν : ‖ν‖ < r) : (rieszInner T r : X →L[ℂ] X) v = v := by
  rw [rieszInner_apply_of_apply_eq_smul hr hfree hv hν.ne,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hν),
    inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- An eigenvector whose eigenvalue lies outside the circle is annihilated by the Riesz
projection. -/
theorem rieszInner_apply_eq_zero_of_apply_eq_smul (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) {v : X} {ν : ℂ} (hv : T v = ν • v)
    (hν : r < ‖ν‖) : (rieszInner T r : X →L[ℂ] X) v = 0 := by
  have hd : ∀ z : ℂ, ‖z‖ ≤ r → DifferentiableAt ℂ (fun z : ℂ ↦ (z - ν)⁻¹) z := fun z hz ↦ by
    have hz' : z - ν ≠ 0 := fun h ↦ by rw [sub_eq_zero.mp h] at hz; linarith
    fun_prop (disch := exact hz')
  have hzero : (∮ z in C(0, r), (z - ν)⁻¹) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      (fun z hz ↦ (hd z (mem_closedBall_zero_iff.mp hz)).continuousAt.continuousWithinAt)
      (fun z hz ↦ hd z (mem_ball_zero_iff.mp hz.1).le)
  rw [rieszInner_apply_of_apply_eq_smul hr hfree hv hν.ne', hzero, mul_zero, zero_smul]

end PDE.Analysis.Spectral
