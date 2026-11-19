/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Complexification.Operator

/-!
# Spectrum and projections of complexified operators

Conjugation of operators is a ring automorphism, so the spectrum of `conjOp A` is the complex
conjugate of the spectrum of `A`, and conjugation carries the resolvent of `A` at `z` to the
resolvent of `conjOp A` at the conjugate point. A complexified real operator is fixed by
conjugation, so its spectrum is symmetric under complex conjugation. A real operator is invertible
exactly when its complexification is, so at real points the complex spectrum of `complexify T`
is the real spectrum of `T`.

A projection fixed by conjugation is the complexification of a real projection. The range of a
complexified operator consists of the vectors whose real and imaginary parts lie in the real
range, and it is finite-dimensional over `ℂ` exactly when the real range is finite-dimensional
over `ℝ`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem isUnit_conjOp_iff {A : Complexification H →L[ℂ] Complexification H} :
    IsUnit (conjOp A) ↔ IsUnit A :=
  isUnit_map_iff conjOp A

theorem conjOp_ringInverse (A : Complexification H →L[ℂ] Complexification H) :
    conjOp (Ring.inverse A) = Ring.inverse (conjOp A) :=
  map_ringInverse conjOp A

/-- The spectrum of the conjugated operator is the conjugate of the spectrum. -/
theorem mem_spectrum_conjOp_iff {A : Complexification H →L[ℂ] Complexification H} {z : ℂ} :
    z ∈ spectrum ℂ (conjOp A) ↔ starRingEnd ℂ z ∈ spectrum ℂ A := by
  have h : algebraMap ℂ (Complexification H →L[ℂ] Complexification H) z - conjOp A =
      conjOp (algebraMap ℂ _ (starRingEnd ℂ z) - A) := by
    simp
  rw [spectrum.mem_iff, spectrum.mem_iff, h, isUnit_conjOp_iff]

/-- Conjugation carries the resolvent at `z` to the resolvent of the conjugated operator at
the conjugate point. -/
theorem conjOp_resolvent (A : Complexification H →L[ℂ] Complexification H) (z : ℂ) :
    conjOp (resolvent A z) = resolvent (conjOp A) (starRingEnd ℂ z) := by
  simp [resolvent, conjOp_ringInverse]

/-- The conjugation identity for the resolvent in the form `(z • 1 - A)⁻¹`. -/
theorem conjOp_ringInverse_smul_one_sub (A : Complexification H →L[ℂ] Complexification H)
    (z : ℂ) :
    conjOp (Ring.inverse (z • 1 - A)) = Ring.inverse (starRingEnd ℂ z • 1 - conjOp A) := by
  simp [conjOp_ringInverse, conjOp_smul]

/-- The spectrum of a complexified real operator is symmetric under complex conjugation. -/
theorem spectrum_complexify_conj (T : H →L[ℝ] H) {z : ℂ} :
    starRingEnd ℂ z ∈ spectrum ℂ (complexify T) ↔ z ∈ spectrum ℂ (complexify T) := by
  rw [← mem_spectrum_conjOp_iff, conjOp_complexify]

/-- The resolvent of a complexified real operator at the conjugate point is the conjugate of
its resolvent. -/
theorem conjOp_resolvent_complexify (T : H →L[ℝ] H) (z : ℂ) :
    conjOp (resolvent (complexify T) z) = resolvent (complexify T) (starRingEnd ℂ z) := by
  rw [conjOp_resolvent, conjOp_complexify]

/-- A real operator is invertible exactly when its complexification is. -/
@[simp]
theorem isUnit_complexify_iff {T : H →L[ℝ] H} : IsUnit (complexify T) ↔ IsUnit T := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map complexifyRingHom⟩
  set B := Ring.inverse (complexify T) with hBdef
  have hB : conjOp B = B := by rw [hBdef, conjOp_ringInverse, conjOp_complexify]
  refine isUnit_iff_exists.mpr ⟨realOp B, complexify_injective ?_, complexify_injective ?_⟩
  · rw [complexify_mul, complexify_realOp hB, complexify_one, hBdef, Ring.mul_inverse_cancel _ h]
  · rw [complexify_mul, complexify_realOp hB, complexify_one, hBdef, Ring.inverse_mul_cancel _ h]

/-- At real points, the complex spectrum of `complexify T` is the real spectrum of `T`. -/
theorem ofReal_mem_spectrum_complexify_iff (T : H →L[ℝ] H) (r : ℝ) :
    (r : ℂ) ∈ spectrum ℂ (complexify T) ↔ r ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff, spectrum.mem_iff, ← complexify_algebraMap, ← complexify_sub,
    isUnit_complexify_iff]

/-- A real eigenvalue of `T` lies in the spectrum of `complexify T`. -/
theorem ofReal_mem_spectrum_complexify_of_apply_eq_smul {T : H →L[ℝ] H} {v : H} {ν : ℝ}
    (hv : v ≠ 0) (h : T v = ν • v) : (ν : ℂ) ∈ spectrum ℂ (complexify T) := by
  rw [ofReal_mem_spectrum_complexify_iff, spectrum.mem_iff]
  rintro ⟨u, hu⟩
  apply hv
  have hu0 : (u : H →L[ℝ] H) v = 0 := by
    rw [hu]
    simp [h]
  have hinv := congrArg (fun w ↦ ((u⁻¹ : (H →L[ℝ] H)ˣ) : H →L[ℝ] H) w) hu0
  simpa only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_zero] using hinv

theorem isIdempotentElem_complexify_iff {P : H →L[ℝ] H} :
    IsIdempotentElem (complexify P) ↔ IsIdempotentElem P := by
  simp only [IsIdempotentElem, ← complexify_mul, complexify_inj]

/-- The real part of a projection fixed by conjugation is a projection. -/
theorem isIdempotentElem_realOp {P : Complexification H →L[ℂ] Complexification H}
    (hP : IsIdempotentElem P) (hc : conjOp P = P) : IsIdempotentElem (realOp P) := by
  rwa [← isIdempotentElem_complexify_iff, complexify_realOp hc]

/-- A projection of the complexification fixed by conjugation is the complexification of a real
projection. -/
theorem exists_isIdempotentElem_complexify_eq {P : Complexification H →L[ℂ] Complexification H}
    (hP : IsIdempotentElem P) (hc : conjOp P = P) :
    ∃ Q : H →L[ℝ] H, IsIdempotentElem Q ∧ complexify Q = P :=
  ⟨realOp P, isIdempotentElem_realOp hP hc, complexify_realOp hc⟩

/-- A vector lies in the range of `complexify T` exactly when its real and imaginary parts lie in
the range of `T`. -/
theorem mem_range_complexify_iff {T : H →L[ℝ] H} {z : Complexification H} :
    z ∈ LinearMap.range (complexify T).toLinearMap ↔
      z.re ∈ LinearMap.range T.toLinearMap ∧ z.im ∈ LinearMap.range T.toLinearMap := by
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨w.re, rfl⟩, ⟨w.im, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨mk x y, by ext <;> simp [hx, hy]⟩

theorem ofReal_mem_range_complexify_iff {T : H →L[ℝ] H} {x : H} :
    ofReal x ∈ LinearMap.range (complexify T).toLinearMap ↔ x ∈ LinearMap.range T.toLinearMap := by
  rw [mem_range_complexify_iff, re_ofReal, im_ofReal]
  exact and_iff_left (Submodule.zero_mem _)

/-- If the range of `complexify T` is finite-dimensional over `ℂ`, then the range of `T` is
finite-dimensional over `ℝ`. -/
theorem finiteDimensional_range_of_complexify {T : H →L[ℝ] H}
    (h : FiniteDimensional ℂ (LinearMap.range (complexify T).toLinearMap)) :
    FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := by
  have : FiniteDimensional ℝ (LinearMap.range (complexify T).toLinearMap) :=
    FiniteDimensional.trans ℝ ℂ _
  let f : LinearMap.range T.toLinearMap →ₗ[ℝ] LinearMap.range (complexify T).toLinearMap :=
    { toFun x := ⟨ofReal x, ofReal_mem_range_complexify_iff.mpr x.2⟩
      map_add' x y := Subtype.ext (by simp)
      map_smul' r x := Subtype.ext (by simp) }
  exact FiniteDimensional.of_injective f fun x y hxy ↦
    Subtype.ext (ofReal_injective (congrArg Subtype.val hxy))

/-- If the range of `T` is finite-dimensional over `ℝ`, then the range of `complexify T` is
finite-dimensional over `ℂ`. -/
theorem finiteDimensional_range_complexify {T : H →L[ℝ] H}
    (h : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.range (complexify T).toLinearMap) := by
  let g : (LinearMap.range T.toLinearMap × LinearMap.range T.toLinearMap) →ₗ[ℝ]
      LinearMap.range (complexify T).toLinearMap :=
    { toFun p := ⟨mk p.1 p.2, mem_range_complexify_iff.mpr ⟨p.1.2, p.2.2⟩⟩
      map_add' p q := Subtype.ext (by ext <;> simp)
      map_smul' r p := Subtype.ext (by ext <;> simp) }
  have hg : Function.Surjective g := fun w ↦ by
    obtain ⟨hre, him⟩ := mem_range_complexify_iff.mp w.2
    exact ⟨(⟨w.1.re, hre⟩, ⟨w.1.im, him⟩), Subtype.ext rfl⟩
  have : Module.Finite ℝ (LinearMap.range (complexify T).toLinearMap) :=
    Module.Finite.of_surjective g hg
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

end PDE.Analysis.Complexification
