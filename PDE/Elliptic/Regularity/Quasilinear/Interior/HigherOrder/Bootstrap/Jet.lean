/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.WeakFlux
import PDE.FDeriv.Calculus

/-!
# The first derivative field in an autonomous divergence equation

Adjoining the first derivatives to a finite family of functions keeps the
principal matrix unchanged. The differentiated forcing is
`D F(v) ∂ₖv - D A(v) ∂ₖv Dv`, a smooth function of the enlarged field.
This formulation allows the same regularity step to be repeated at every
finite order without assuming a differentiated equation.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {I : Type*} [Fintype I]

/-- The original components together with their first coordinate derivatives. -/
def firstJet (v : ℝ^n → I → ℝ) (x : ℝ^n) : I ⊕ (I × Fin n) → ℝ :=
  Sum.elim (v x) (fun ik ↦ (∂[ik.2] (fun y ↦ v y ik.1)) x)

/-- Projection of a first derivative field to its original values. -/
def jetValue (p : I ⊕ (I × Fin n) → ℝ) : I → ℝ :=
  fun i ↦ p (.inl i)

/-- Projection to one coordinate derivative of the original field. -/
def jetDirection (p : I ⊕ (I × Fin n) → ℝ) (k : Fin n) : I → ℝ :=
  fun i ↦ p (.inr (i, k))

/-- The principal matrix in the enlarged system is the original matrix. -/
def prolongedCoefficient (a : Fin n → Fin n → (I → ℝ) → ℝ)
    (i j : Fin n) (p : I ⊕ (I × Fin n) → ℝ) : ℝ :=
  a i j (jetValue p)

/-- The divergence forcing after adjoining the first derivatives.
The minus sign is the coefficient commutator moved to the right-hand side. -/
def prolongedForcing (a : Fin n → Fin n → (I → ℝ) → ℝ)
    (f : I → Fin n → (I → ℝ) → ℝ)
    (l : I ⊕ (I × Fin n)) (i : Fin n) (p : I ⊕ (I × Fin n) → ℝ) : ℝ :=
  match l with
  | .inl j => f j i (jetValue p)
  | .inr (j, k) =>
    fderiv ℝ (f j i) (jetValue p) (jetDirection p k) -
      ∑ t, fderiv ℝ (a i t) (jetValue p) (jetDirection p k) *
        jetDirection p t j

/-- Projection to the values is smooth. -/
theorem contDiff_jetValue : ContDiff ℝ (⊤ : ℕ∞) (jetValue (n := n) (I := I)) :=
  contDiff_pi.mpr fun _ ↦ contDiff_apply ℝ (fun _ ↦ ℝ) _

/-- Projection to each derivative direction is smooth. -/
theorem contDiff_jetDirection (k : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : I ⊕ (I × Fin n) → ℝ ↦ jetDirection p k) :=
  contDiff_pi.mpr fun _ ↦ contDiff_apply ℝ (fun _ ↦ ℝ) _

/-- Enlarging the field preserves smoothness of the principal coefficients. -/
theorem contDiff_prolongedCoefficient
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (prolongedCoefficient a i j) :=
  (ha i j).comp contDiff_jetValue

/-- All terms in the differentiated forcing are smooth functions of the
enlarged field. No derivatives of that enlarged field occur in this source. -/
theorem contDiff_prolongedForcing
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hf : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i))
    (l : I ⊕ (I × Fin n)) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (prolongedForcing a f l i) := by
  cases l with
  | inl j => exact (hf j i).comp contDiff_jetValue
  | inr jk =>
    obtain ⟨j, k⟩ := jk
    apply ContDiff.sub
    · exact (((hf j i).fderiv_right (by simp)).comp contDiff_jetValue).clm_apply
        (contDiff_jetDirection k)
    · apply ContDiff.sum
      intro t _
      exact ((((ha i t).fderiv_right (by simp)).comp contDiff_jetValue).clm_apply
        (contDiff_jetDirection k)).mul
          (contDiff_apply ℝ (fun _ ↦ ℝ) (Sum.inr (j, t) : I ⊕ (I × Fin n)))

/-- A C² field has a C¹ first derivative field on its open domain. -/
theorem contDiffOn_one_firstJet {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 2 v Ω) :
    ContDiffOn ℝ 1 (firstJet v) Ω := by
  apply contDiffOn_pi.mpr
  intro l
  cases l with
  | inl i => exact (contDiffOn_pi.mp hv i).of_le (by norm_num)
  | inr ik =>
    intro x hx
    exact (contDiffAt_partialDeriv 1
      ((contDiffOn_pi.mp hv ik.1).contDiffAt (hΩ.mem_nhds hx)) ik.2).contDiffWithinAt

/-- Regularity of the first derivative field raises the regularity of the
original field by one. The input C¹ hypothesis supplies differentiability. -/
theorem contDiffOn_succ_of_firstJet (m : ℕ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hjet : ContDiffOn ℝ m (firstJet v) Ω) :
    ContDiffOn ℝ (m + 1) v Ω := by
  apply contDiffOn_pi.mpr
  intro i
  apply (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mpr
  refine ⟨(contDiffOn_pi.mp hv i).differentiableOn (by norm_num), by simp, ?_⟩
  have heq : fderiv ℝ (fun x ↦ v x i) =
      fun x ↦ ∑ k, (∂[k] (fun y ↦ v y i)) x •
        (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ) :=
    funext fun x ↦ fderiv_eq_sum_partialDeriv_smul_proj _ x
  rw [heq]
  apply ContDiffOn.sum
  intro k _
  exact (contDiffOn_pi.mp hjet (.inr (i, k))).smul contDiffOn_const

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
