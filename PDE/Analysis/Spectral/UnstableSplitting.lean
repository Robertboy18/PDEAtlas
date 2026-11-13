/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.FiniteRank
public import PDE.Analysis.InnerProductSpace.Complexification.Riesz

/-!
# Unstable splitting of real operators

Let `T` be a bounded operator on a real Hilbert space `H`, and let the circle of radius `r > 0`
carry no spectrum of the complexification `complexify T`. The Riesz projection of
`complexify T` for this circle and the inverse of `complexify T` on its spectral part outside
the circle are fixed by conjugation, so both are complexifications of real operators:

* `unstableProjection T r`, the projection onto the spectral part of `T` outside the circle. It
  commutes with every operator commuting with `T` and fixes every eigenvector whose eigenvalue
  has modulus greater than `r`.
* `unstableInverse T r`, which inverts `T` on the range of this projection and commutes with
  every operator commuting with `T`.

With `P = unstableProjection T r` and `W = unstableInverse T r`, the powers satisfy
`‖Tⁿ (1 - P)‖ ≤ C ρⁿ` for some `ρ < r` and `‖Wⁿ P‖ ≤ C ρ⁻ⁿ` for some `ρ > r`.

For a compact perturbation `T = T₀ + K` with `‖T₀ⁿ‖ ≤ C qⁿ` and `r > q`, the projection has
finite rank. Every interval of growth rates above `log q` contains the logarithm of a radius
whose circle carries no spectrum, which gives the exponential dichotomy
`exists_unstable_splitting`. The splitting holds on every real normed space that is linearly
isometric to a real Hilbert space (`exists_unstable_splitting_of_linearIsometryEquiv`), such as
a Sobolev space of order zero, which carries no inner product instance.
-/

@[expose] public noncomputable section

open PDE.Analysis.Complexification

namespace PDE.Analysis.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The unstable projection of a real operator `T` for the circle of radius `r`: the real
operator whose complexification is `1 - rieszInner (complexify T) r`. For `r > 0` and a circle
that carries no spectrum of `complexify T` it is the idempotent onto the spectral part of `T`
outside the circle. -/
def unstableProjection (T : H →L[ℝ] H) (r : ℝ) : H →L[ℝ] H :=
  realOp (1 - rieszInner (complexify T) r)

/-- The unstable inverse of a real operator `T` for the circle of radius `r`: the real operator
whose complexification is `rieszOuterInverse (complexify T) r`. For `r > 0` and a circle that
carries no spectrum of `complexify T` it inverts `T` on the range of `unstableProjection T r`
and vanishes on its kernel. -/
def unstableInverse (T : H →L[ℝ] H) (r : ℝ) : H →L[ℝ] H :=
  realOp (rieszOuterInverse (complexify T) r)

/-- The complexification of the unstable projection is `1 - rieszInner (complexify T) r`. -/
theorem complexify_unstableProjection (T : H →L[ℝ] H) (r : ℝ) :
    complexify (unstableProjection T r) = 1 - rieszInner (complexify T) r :=
  complexify_realOp (by rw [map_sub, map_one, conjOp_rieszInner_complexify])

/-- The complexification of the unstable inverse is `rieszOuterInverse (complexify T) r`. -/
theorem complexify_unstableInverse (T : H →L[ℝ] H) (r : ℝ) :
    complexify (unstableInverse T r) = rieszOuterInverse (complexify T) r :=
  complexify_realOp (conjOp_rieszOuterInverse_complexify T r)

variable [CompleteSpace H]

/-- Every operator commuting with `T` commutes with the unstable projection. -/
theorem commute_unstableProjection {S T : H →L[ℝ] H} (h : Commute S T) (r : ℝ) :
    Commute S (unstableProjection T r) := by
  rw [← commute_complexify_iff, complexify_unstableProjection]
  exact (Commute.one_right _).sub_right (commute_rieszInner (commute_complexify_iff.mpr h))

/-- Every operator commuting with `T` commutes with the unstable inverse. -/
theorem commute_unstableInverse {S T : H →L[ℝ] H} (h : Commute S T) (r : ℝ) :
    Commute S (unstableInverse T r) := by
  rw [← commute_complexify_iff, complexify_unstableInverse]
  exact commute_rieszOuterInverse (commute_complexify_iff.mpr h) r

variable {T : H →L[ℝ] H} {r : ℝ}

/-- If the circle of radius `r` carries no spectrum of `complexify T`, the unstable projection
`P = unstableProjection T r` is idempotent. -/
theorem isIdempotentElem_unstableProjection
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    IsIdempotentElem (unstableProjection T r) := by
  have h : IsIdempotentElem (rieszInner (complexify T) r) := rieszInner_idem hfree
  rw [← isIdempotentElem_complexify_iff, complexify_unstableProjection]
  exact h.one_sub

/-- If `r > 0` and the circle of radius `r` carries no spectrum of `complexify T`, the unstable
inverse `W = unstableInverse T r` and the unstable projection `P = unstableProjection T r`
satisfy `T W = P`. -/
theorem mul_unstableInverse (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    T * unstableInverse T r = unstableProjection T r := by
  apply complexify_injective
  rw [complexify_mul, complexify_unstableInverse, complexify_unstableProjection]
  exact mul_rieszOuterInverse hr (sphere_subset_resolventSet hfree)

/-- If `r > 0` and the circle of radius `r` carries no spectrum of `complexify T`, the unstable
inverse `W = unstableInverse T r` and the unstable projection `P = unstableProjection T r`
satisfy `W T = P`. -/
theorem unstableInverse_mul (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    unstableInverse T r * T = unstableProjection T r := by
  apply complexify_injective
  rw [complexify_mul, complexify_unstableInverse, complexify_unstableProjection]
  exact rieszOuterInverse_mul hr (sphere_subset_resolventSet hfree)

/-- If `r > 0` and the circle of radius `r` carries no spectrum of `complexify T`, the unstable
projection `P = unstableProjection T r` and the unstable inverse `W = unstableInverse T r`
satisfy `P W = W`. -/
theorem unstableProjection_mul_unstableInverse (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    unstableProjection T r * unstableInverse T r = unstableInverse T r := by
  have h : rieszInner (complexify T) r * rieszOuterInverse (complexify T) r = 0 :=
    rieszInner_mul_rieszOuterInverse hr hfree
  apply complexify_injective
  rw [complexify_mul, complexify_unstableInverse, complexify_unstableProjection, sub_mul,
    one_mul, h, sub_zero]

/-- If `r > 0` and the circle of radius `r` carries no spectrum of `complexify T`, the unstable
inverse `W = unstableInverse T r` and the unstable projection `P = unstableProjection T r`
satisfy `W P = W`. -/
theorem unstableInverse_mul_unstableProjection (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    unstableInverse T r * unstableProjection T r = unstableInverse T r := by
  have h : rieszOuterInverse (complexify T) r * rieszInner (complexify T) r = 0 :=
    rieszOuterInverse_mul_rieszInner hr hfree
  apply complexify_injective
  rw [complexify_mul, complexify_unstableInverse, complexify_unstableProjection, mul_sub,
    mul_one, h, sub_zero]

/-- If `r > 0` and the circle of radius `r` carries no spectrum of `complexify T`, an
eigenvector of `T` whose eigenvalue has modulus greater than `r` is fixed by the unstable
projection `P = unstableProjection T r`. -/
theorem unstableProjection_apply_eq_self_of_apply_eq_smul (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) {v : H} {ν : ℝ}
    (hv : T v = ν • v) (hν : r < |ν|) : unstableProjection T r v = v := by
  have h := rieszInner_apply_eq_zero_of_apply_eq_smul hr hfree (complexify_ofReal_eq_smul hv)
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  have hc : complexify (unstableProjection T r) (ofReal v) = ofReal v := by
    rw [complexify_unstableProjection, sub_apply, one_apply_eq_self, h, sub_zero]
  rw [complexify_ofReal] at hc
  exact ofReal_injective hc

/-- **Decay on the stable part.** If `r > 0` and the circle of radius `r` carries no spectrum
of `complexify T`, the unstable projection `P = unstableProjection T r` satisfies
`‖Tⁿ (1 - P)‖ ≤ C ρⁿ` for some `0 < ρ < r`. -/
theorem exists_norm_pow_mul_one_sub_unstableProjection_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < r ∧ 0 ≤ C ∧
      ∀ n : ℕ, ‖T ^ n * (1 - unstableProjection T r)‖ ≤ C * ρ ^ n := by
  obtain ⟨ρ, C, hρ, hρr, hC, h⟩ :=
    exists_norm_pow_mul_rieszInner_le (a := complexify T) hr (by exact hfree)
  refine ⟨ρ, C, hρ, hρr, hC, fun n ↦ ?_⟩
  rw [← norm_complexify, complexify_mul, complexify_pow, complexify_sub, complexify_one,
    complexify_unstableProjection, sub_sub_cancel]
  exact h n

/-- **Growth on the unstable part.** If `r > 0` and the circle of radius `r` carries no
spectrum of `complexify T`, the unstable inverse `W = unstableInverse T r` and the unstable
projection `P = unstableProjection T r` satisfy `‖Wⁿ P‖ ≤ C ρ⁻ⁿ` for some `ρ > r`. -/
theorem exists_norm_unstableInverse_pow_mul_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    ∃ ρ C : ℝ, r < ρ ∧ 0 ≤ C ∧
      ∀ n : ℕ, ‖unstableInverse T r ^ n * unstableProjection T r‖ ≤ C * (ρ ^ n)⁻¹ := by
  obtain ⟨ρ, C, hρ, hC, h⟩ :=
    exists_norm_rieszOuterInverse_pow_mul_le (a := complexify T) hr (by exact hfree)
  refine ⟨ρ, C, hρ, hC, fun n ↦ ?_⟩
  rw [← norm_complexify, complexify_mul, complexify_pow, complexify_unstableInverse,
    complexify_unstableProjection]
  exact h n

/-- **Finite rank.** For `T = T₀ + K` with `K` compact, `‖T₀ⁿ‖ ≤ C qⁿ` and a circle of radius
`r > q` that carries no spectrum of `complexify T`, the unstable projection has finite rank. -/
theorem finiteDimensional_range_unstableProjection {T₀ K : H →L[ℝ] H} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ (complexify T)) :
    FiniteDimensional ℝ (LinearMap.range (unstableProjection T r).toLinearMap) := by
  apply finiteDimensional_range_of_complexify
  rw [complexify_unstableProjection]
  refine finiteDimensional_range_one_sub_rieszInner (T₀ := complexify T₀) (K := complexify K)
    (C := C) (by rw [hT, complexify_add]) (isCompactOperator_complexify hK) hq hqr (fun n ↦ ?_)
    hfree
  rw [← complexify_pow, norm_complexify]
  exact hT₀ n

/-- **Unstable splitting.** Let `T = T₀ + K` on a real Hilbert space, with `K` compact and
`‖T₀ⁿ‖ ≤ C qⁿ`, and let `T v = ν v` for some `v ≠ 0` and `ν > 1`. For growth rates
`log q < ω₁ < ω₂ ≤ log ν` there are a rate `ω ∈ (ω₁, ω₂)` and a finite-rank projection `P`
fixing `v` and commuting with every operator that commutes with `T`, such that
`‖Tⁿ (1 - P)‖ ≤ M exp (ω' n)` for some `M ≥ 0` and a rate `ω' < ω`, and `T` is invertible on
the range of `P`: some `W` commuting with every operator that commutes with `T` satisfies
`T W = W T = P` and `P W = W P = W`, and `‖Wⁿ P‖ ≤ M exp (-ω'' n)` for some `M ≥ 0` and a rate
`ω'' > ω`.

The bound `q` enters only through `log q < ω₁`, so it need not be below `1`, and `0 ≤ q`
follows from `v ≠ 0`. -/
theorem exists_unstable_splitting {C q ν ω₁ ω₂ : ℝ} {v : H} (T T₀ K : H →L[ℝ] H)
    (hT : T = T₀ + K) (hK : IsCompactOperator K) (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n)
    (hv : v ≠ 0) (hν : 1 < ν) (hTv : T v = ν • v) (hω : Real.log q < ω₁) (hω₁₂ : ω₁ < ω₂)
    (hω₂ : ω₂ ≤ Real.log ν) :
    ∃ (P : H →L[ℝ] H) (ω : ℝ), ω₁ < ω ∧ ω < ω₂ ∧ IsIdempotentElem P ∧
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧ P v = v ∧
      (∀ S : H →L[ℝ] H, Commute S T → Commute S P) ∧
      (∃ M ω' : ℝ, 0 ≤ M ∧ ω' < ω ∧ ∀ n : ℕ, ‖T ^ n * (1 - P)‖ ≤ M * Real.exp (ω' * n)) ∧
      ∃ W : H →L[ℝ] H, T * W = P ∧ W * T = P ∧ P * W = W ∧ W * P = W ∧
        (∀ S : H →L[ℝ] H, Commute S T → Commute S W) ∧
        ∃ M ω'' : ℝ, 0 ≤ M ∧ ω < ω'' ∧ ∀ n : ℕ, ‖W ^ n * P‖ ≤ M * Real.exp (-(ω'' * n)) := by
  have : Nontrivial H := nontrivial_of_ne v 0 hv
  have hC : 1 ≤ C := by simpa using hT₀ 0
  have hq : 0 ≤ q :=
    nonneg_of_mul_nonneg_right (by simpa using (norm_nonneg _).trans (hT₀ 1)) (by linarith)
  have hqa : q < Real.exp ω₁ := Real.lt_exp_of_log_lt hω
  have hTc : complexify T = complexify T₀ + complexify K := by rw [hT, complexify_add]
  have hT₀c : ∀ n : ℕ, ‖complexify T₀ ^ n‖ ≤ C * q ^ n := fun n ↦ by
    rw [← complexify_pow, norm_complexify]
    exact hT₀ n
  obtain ⟨r, har, hrb, hfree⟩ := exists_radius_notMem_spectrum_of_pow_bound hTc
    (isCompactOperator_complexify hK) hT₀c hq hqa (Real.exp_lt_exp.mpr hω₁₂)
  have hr : 0 < r := (Real.exp_pos ω₁).trans har
  have hν0 : 0 < ν := zero_lt_one.trans hν
  have hrν : r < |ν| := by
    rw [abs_of_pos hν0]
    calc r < Real.exp ω₂ := hrb
      _ ≤ Real.exp (Real.log ν) := Real.exp_le_exp.mpr hω₂
      _ = ν := Real.exp_log hν0
  have hexp : ∀ {ρ : ℝ}, 0 < ρ → ∀ n : ℕ, Real.exp (Real.log ρ * n) = ρ ^ n := fun hρ n ↦ by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hρ]
  refine ⟨unstableProjection T r, Real.log r, (Real.lt_log_iff_exp_lt hr).mpr har,
    (Real.log_lt_iff_lt_exp hr).mpr hrb, isIdempotentElem_unstableProjection hfree,
    finiteDimensional_range_unstableProjection hT hK hq (hqa.trans har) hT₀ hfree,
    unstableProjection_apply_eq_self_of_apply_eq_smul hr hfree hTv hrν,
    fun S hS ↦ commute_unstableProjection hS r, ?_, unstableInverse T r,
    mul_unstableInverse hr hfree, unstableInverse_mul hr hfree,
    unstableProjection_mul_unstableInverse hr hfree,
    unstableInverse_mul_unstableProjection hr hfree, fun S hS ↦ commute_unstableInverse hS r, ?_⟩
  · obtain ⟨ρ, M, hρ, hρr, hM, h⟩ := exists_norm_pow_mul_one_sub_unstableProjection_le hr hfree
    refine ⟨M, Real.log ρ, hM, Real.log_lt_log hρ hρr, fun n ↦ ?_⟩
    rw [hexp hρ n]
    exact h n
  · obtain ⟨ρ, M, hρ, hM, h⟩ := exists_norm_unstableInverse_pow_mul_le hr hfree
    refine ⟨M, Real.log ρ, hM, Real.log_lt_log hr hρ, fun n ↦ ?_⟩
    rw [Real.exp_neg, hexp (hr.trans hρ) n]
    exact h n

/-! ### Transfer through an isometry -/

section Isometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Conjugation by a linear isometry equivalence preserves operator norms. -/
theorem norm_conjContinuousAlgEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) :
    ‖φ.toContinuousLinearEquiv.conjContinuousAlgEquiv A‖ = ‖A‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x ↦ ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
    calc ‖A (φ.toContinuousLinearEquiv.symm x)‖ ≤ ‖A‖ * ‖φ.toContinuousLinearEquiv.symm x‖ :=
          A.le_opNorm _
      _ = ‖A‖ * ‖x‖ := by
          rw [show φ.toContinuousLinearEquiv.symm x = φ.symm x from rfl,
            LinearIsometryEquiv.norm_map]
  · have h : A x = φ.symm (φ.toContinuousLinearEquiv.conjContinuousAlgEquiv A (φ x)) := by
      rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
      simp
    rw [h, LinearIsometryEquiv.norm_map, ← LinearIsometryEquiv.norm_map φ x]
    exact ContinuousLinearMap.le_opNorm _ _

/-- **Unstable splitting through an isometry.** The conclusion of `exists_unstable_splitting`
holds for operators on a real normed space `E` that is linearly isometric to a real Hilbert
space `H`: conjugate by the isometry, split in `H` and conjugate back. -/
theorem exists_unstable_splitting_of_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] H) {C q ν ω₁ ω₂ : ℝ}
    {v : E} (T T₀ K : E →L[ℝ] E)
    (hT : T = T₀ + K) (hK : IsCompactOperator K) (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n)
    (hv : v ≠ 0) (hν : 1 < ν) (hTv : T v = ν • v) (hω : Real.log q < ω₁) (hω₁₂ : ω₁ < ω₂)
    (hω₂ : ω₂ ≤ Real.log ν) :
    ∃ (P : E →L[ℝ] E) (ω : ℝ), ω₁ < ω ∧ ω < ω₂ ∧ IsIdempotentElem P ∧
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧ P v = v ∧
      (∀ S : E →L[ℝ] E, Commute S T → Commute S P) ∧
      (∃ M ω' : ℝ, 0 ≤ M ∧ ω' < ω ∧ ∀ n : ℕ, ‖T ^ n * (1 - P)‖ ≤ M * Real.exp (ω' * n)) ∧
      ∃ W : E →L[ℝ] E, T * W = P ∧ W * T = P ∧ P * W = W ∧ W * P = W ∧
        (∀ S : E →L[ℝ] E, Commute S T → Commute S W) ∧
        ∃ M ω'' : ℝ, 0 ≤ M ∧ ω < ω'' ∧ ∀ n : ℕ, ‖W ^ n * P‖ ≤ M * Real.exp (-(ω'' * n)) := by
  set c := φ.toContinuousLinearEquiv.conjContinuousAlgEquiv with hc
  have hcK : IsCompactOperator (c K) :=
    (hK.clm_comp φ.toContinuousLinearEquiv.toContinuousLinearMap).comp_clm
      φ.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcv : c T (φ v) = ν • φ v := by
    rw [hc, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    simp [hTv]
  obtain ⟨P, ω, h₁, h₂, hP, hfin, hPv, hcomm, ⟨M, ω', hM, hω', hst⟩, W, hTW, hWT, hPW, hWP,
      hcommW, ⟨M', ω'', hM', hω'', hun⟩⟩ :=
    exists_unstable_splitting (c T) (c T₀) (c K) (by rw [hT, map_add]) hcK
      (fun n ↦ by rw [← map_pow, norm_conjContinuousAlgEquiv]; exact hT₀ n)
      (by simpa using hv) hν hcv hω hω₁₂ hω₂
  have hcs : ∀ A : H →L[ℝ] H, c (c.symm A) = A := c.apply_symm_apply
  have hcomm' : ∀ {S : E →L[ℝ] E} {A : H →L[ℝ] H}, Commute (c S) A → Commute S (c.symm A) :=
    fun {S A} h ↦ by
      have := h.map c.symm
      rwa [c.symm_apply_apply] at this
  refine ⟨c.symm P, ω, h₁, h₂, hP.map c.symm, ?_, ?_, fun S hS ↦ hcomm' (hcomm _ (hS.map c)),
    ⟨M, ω', hM, hω', fun n ↦ ?_⟩, c.symm W, ?_, ?_, ?_, ?_,
    fun S hS ↦ hcomm' (hcommW _ (hS.map c)), ⟨M', ω'', hM', hω'', fun n ↦ ?_⟩⟩
  · have hle : LinearMap.range (c.symm P).toLinearMap ≤
        (LinearMap.range P.toLinearMap).map φ.symm.toLinearEquiv.toLinearMap := by
      rintro _ ⟨x, rfl⟩
      exact ⟨P (φ x), ⟨φ x, rfl⟩, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · change φ.symm (P (φ v)) = v
    rw [hPv, LinearIsometryEquiv.symm_apply_apply]
  · rw [← norm_conjContinuousAlgEquiv φ, map_mul, map_pow, map_sub, map_one, hcs]
    exact hst n
  · rw [← c.symm_apply_apply T, ← map_mul, hTW]
  · rw [← c.symm_apply_apply T, ← map_mul, hWT]
  · rw [← map_mul, hPW]
  · rw [← map_mul, hWP]
  · rw [← norm_conjContinuousAlgEquiv φ, map_mul, map_pow, hcs, hcs]
    exact hun n

end Isometry

end PDE.Analysis.Spectral
