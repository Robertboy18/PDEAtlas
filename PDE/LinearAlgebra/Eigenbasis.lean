/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finset.Sort

/-!
# Eigenlines of a finite eigenbasis

For an operator diagonal in a finite basis with distinct eigenvalues, a nonzero
eigenvector has exactly one nonzero basis coordinate. The eigenvectors form a
basis, so their completeness is part of the hypothesis.
No norm or inner product is needed. Over an ordered field, a simple finite
eigenbasis can also be relabelled in increasing eigenvalue order.
-/

@[expose] public section

noncomputable section

namespace Module.Basis

/-- A finite eigenbasis with distinct eigenvalues can be relabelled so that its
eigenvalues are strictly increasing. Only the labels change. -/
theorem exists_ordered_eigenbasis
    {n : ℕ} {K E : Type*} [Field K] [LinearOrder K] [AddCommGroup E] [Module K E]
    (b : Basis (Fin n) K E) (A : E →ₗ[K] E) (eig : Fin n → K)
    (hinj : Function.Injective eig) (hA : ∀ k, A (b k) = eig k • b k) :
    ∃ c : Basis (Fin n) K E, ∃ a : Fin n → K,
      StrictMono a ∧ ∀ k, A (c k) = a k • c k := by
  classical
  let s : Finset K := Finset.univ.image eig
  have hcard : s.card = n := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  let e : Fin n ≃ s := Equiv.ofBijective
    (fun k ↦ ⟨eig k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro i j hij
        exact hinj (congrArg Subtype.val hij)
      · rintro ⟨z, hz⟩
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hz
        exact ⟨k, Subtype.ext hk⟩)
  let σ : Fin n ≃ Fin n := (s.orderIsoOfFin hcard).toEquiv.trans e.symm
  have hσ (k : Fin n) :
      eig (σ k) = (s.orderIsoOfFin hcard k : K) :=
    congrArg Subtype.val (e.apply_symm_apply (s.orderIsoOfFin hcard k))
  refine ⟨b.reindex σ.symm, fun k ↦ eig (σ k), ?_, ?_⟩
  · intro i j hij
    change eig (σ i) < eig (σ j)
    rw [hσ i, hσ j]
    exact (s.orderIsoOfFin hcard).strictMono hij
  · intro k
    simpa only [Basis.reindex_apply, Equiv.symm_symm] using hA (σ k)

/-- If a linear map multiplies each basis vector by a scalar, it multiplies the corresponding
coordinate of every vector by the same scalar. The scalars need not be distinct or nonzero. -/
theorem equivFun_apply_of_apply_basis_eq_smul
    {ι R E : Type*} [Finite ι] [CommSemiring R] [AddCommMonoid E] [Module R E]
    (b : Basis ι R E) (A : E →ₗ[R] E) (eig : ι → R)
    (hA : ∀ i, A (b i) = eig i • b i) (v : E) (j : ι) :
    b.equivFun (A v) j = eig j * b.equivFun v j := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  calc
    b.equivFun (A v) j =
        b.equivFun (A (∑ i, b.equivFun v i • b i)) j := by rw [b.sum_equivFun]
    _ = eig j * b.equivFun v j := by
      simp only [map_sum, map_smul, hA, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Basis.equivFun_self]
      simp [mul_comm]

/-- A nonzero eigenvector of an operator with a simple eigenbasis lies on one of its
basis lines. Its eigenvalue and scalar coefficient are determined by that basis.
No order on the field is needed, only distinct eigenvalues. -/
theorem exists_eq_smul_of_apply_eq_smul
    {ι K E : Type*} [Finite ι] [Field K] [AddCommGroup E] [Module K E]
    (b : Basis ι K E) (A : E →ₗ[K] E) (eig : ι → K)
    (hinj : Function.Injective eig) (hA : ∀ j, A (b j) = eig j • b j)
    {v : E} {a : K} (hv : v ≠ 0) (hav : A v = a • v) :
    ∃ k, a = eig k ∧ v = b.equivFun v k • b k := by
  classical
  have hcoord (j : ι) : eig j * b.equivFun v j = a * b.equivFun v j := by
    have hdiag := b.equivFun_apply_of_apply_basis_eq_smul A eig hA v j
    rw [hav, map_smul, Pi.smul_apply, smul_eq_mul] at hdiag
    exact hdiag.symm
  obtain ⟨k, hk⟩ : ∃ k, b.equivFun v k ≠ 0 := by
    by_contra! hz
    apply hv
    apply b.equivFun.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using hz j
  have heig : eig k = a := mul_right_cancel₀ hk (hcoord k)
  have hzero (j : ι) (hj : j ≠ k) : b.equivFun v j = 0 := by
    by_contra hne
    exact hj (hinj ((mul_right_cancel₀ hne (hcoord j)).trans heig.symm))
  refine ⟨k, heig.symm, ?_⟩
  apply b.equivFun.injective
  ext j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
  by_cases hj : j = k
  · subst j
    simp
  · simp [Ne.symm hj, hzero j hj]

/-- Increasing eigenvalue lists of two complete eigenbases of the same operator
coincide. Thus ordering removes the choice of eigenbasis from the eigenvalues. -/
theorem eq_eigenvalues_of_strictMono
    {n : ℕ} {K E : Type*} [Field K] [LinearOrder K] [AddCommGroup E] [Module K E]
    (b c : Basis (Fin n) K E) (A : E →ₗ[K] E) {eig speed : Fin n → K}
    (heig : StrictMono eig) (hspeed : StrictMono speed)
    (hb : ∀ k, A (b k) = eig k • b k)
    (hc : ∀ k, A (c k) = speed k • c k) :
    eig = speed := by
  apply heig.eq_of_range_eq hspeed
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj, _⟩ :=
      c.exists_eq_smul_of_apply_eq_smul A speed hspeed.injective hc (b.ne_zero k) (hb k)
    exact ⟨j, hj.symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj, _⟩ :=
      b.exists_eq_smul_of_apply_eq_smul A eig heig.injective hb (c.ne_zero k) (hc k)
    exact ⟨j, hj.symm⟩

/-- Two nonzero eigenvectors with the same eigenvalue in a simple complete
eigenbasis differ by a nonzero scalar. -/
theorem exists_ne_zero_smul_eq_of_eigenvectors
    {ι K E : Type*} [Finite ι] [Field K] [AddCommGroup E] [Module K E]
    (b : Basis ι K E) (A : E →ₗ[K] E) (eig : ι → K)
    (hinj : Function.Injective eig) (hA : ∀ j, A (b j) = eig j • b j)
    {v w : E} {a : K} (hv : v ≠ 0) (hw : w ≠ 0)
    (hav : A v = a • v) (haw : A w = a • w) :
    ∃ c : K, c ≠ 0 ∧ w = c • v := by
  obtain ⟨k, hk, hvk⟩ :=
    b.exists_eq_smul_of_apply_eq_smul A eig hinj hA hv hav
  obtain ⟨j, hj, hwj⟩ :=
    b.exists_eq_smul_of_apply_eq_smul A eig hinj hA hw haw
  have hjk : j = k := hinj (hj.symm.trans hk)
  subst j
  have hα : b.equivFun v k ≠ 0 := by
    intro hz
    exact hv (by simpa only [hz, zero_smul] using hvk)
  have hβ : b.equivFun w k ≠ 0 := by
    intro hz
    exact hw (by simpa only [hz, zero_smul] using hwj)
  refine ⟨b.equivFun w k / b.equivFun v k, div_ne_zero hβ hα, ?_⟩
  calc
    w = b.equivFun w k • b k := hwj
    _ = (b.equivFun w k / b.equivFun v k) • (b.equivFun v k • b k) := by
      rw [smul_smul, div_mul_cancel₀ _ hα]
    _ = (b.equivFun w k / b.equivFun v k) • v := by rw [← hvk]

/-- Normalizing a simple eigenvector by a linear functional is independent of
the chosen nonzero vector on its eigenline. If the functional vanishes on that
line, both sides are zero because `0⁻¹ = 0`. -/
theorem inv_apply_smul_eq_of_eigenvectors
    {ι K E : Type*} [Finite ι] [Field K] [AddCommGroup E] [Module K E]
    (b : Basis ι K E) (A : E →ₗ[K] E) (eig : ι → K)
    (hinj : Function.Injective eig) (hA : ∀ j, A (b j) = eig j • b j)
    (φ : E →ₗ[K] K) {v w : E} {a : K} (hv : v ≠ 0) (hw : w ≠ 0)
    (hav : A v = a • v) (haw : A w = a • w) :
    (φ v)⁻¹ • v = (φ w)⁻¹ • w := by
  obtain ⟨c, hc, rfl⟩ := b.exists_ne_zero_smul_eq_of_eigenvectors A eig hinj hA
    hv hw hav haw
  rw [map_smul, smul_eq_mul, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

end Module.Basis
