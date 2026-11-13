/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.Jet
import PDE.FDeriv.Calculus

/-!
# Differentiating the autonomous system

The equation for the first derivative field follows from the original
distributional equation. The chain rule produces the prolonged forcing;
commutation of second derivatives preserves the principal matrix.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {I : Type*} {Ω : Set ℝ^n}

/-- Chain rule in a coordinate direction, written in terms of the first jet. -/
theorem partialDeriv_comp_eq_jetDirection [Finite I]
    {v : ℝ^n → I → ℝ} {g : (I → ℝ) → ℝ} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x) (hg : DifferentiableAt ℝ g (v x)) (k : Fin n) :
    (∂[k] (fun y ↦ g (v y))) x =
      fderiv ℝ g (v x) (jetDirection (firstJet v x) k) := by
  let := Fintype.ofFinite I
  change fderiv ℝ (g ∘ v) x _ = _
  rw [fderiv_comp x hg hv, ContinuousLinearMap.comp_apply]
  congr 1
  funext i
  change _ = fderiv ℝ (fun y ↦ v y i) x _
  rw [fderiv_apply hv]
  rfl

/-- The commutator is a smooth function of values and first derivatives. -/
theorem prolongedForcing_comp_firstJet [Finite I]
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    {v : ℝ^n → I → ℝ} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x)
    (ha : ∀ i j, DifferentiableAt ℝ (a i j) (v x))
    (hf : ∀ l i, DifferentiableAt ℝ (f l i) (v x))
    (l : I) (k i : Fin n) :
    prolongedForcing a f (.inr (l, k)) i (firstJet v x) =
      (∂[k] (fun y ↦ f l i (v y))) x -
        ∑ j, (∂[k] (fun y ↦ a i j (v y))) x *
          (∂[j] (fun y ↦ v y l)) x := by
  simp only [partialDeriv_comp_eq_jetDirection hv (hf l i),
    partialDeriv_comp_eq_jetDirection hv (ha i _)]
  rfl

/-- Every equation in the prolonged system is derived from the original
weak equations once the original field is C². -/
theorem hasZeroWeakDivergenceOn_firstJet [Fintype I]
    (hΩ : IsOpen Ω)
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hf : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i))
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (heq : ∀ l, HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, a i j (v x) * (∂[j] (fun y ↦ v y l)) x) - f l i (v x)))
    (l : I ⊕ (I × Fin n)) :
    HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, prolongedCoefficient a i j (firstJet v x) *
        (∂[j] (fun y ↦ firstJet v y l)) x) -
      prolongedForcing a f l i (firstJet v x)) := by
  cases l with
  | inl l => exact heq l
  | inr lk =>
    obtain ⟨l, k⟩ := lk
    have hvc := contDiffOn_pi.mp hv l
    have hd (j : Fin n) : ContDiffOn ℝ 1 (∂[j] (fun y ↦ v y l)) Ω := by
      intro x hx
      exact (contDiffAt_partialDeriv 1
        (hvc.contDiffAt (hΩ.mem_nhds hx)) j).contDiffWithinAt
    have hac (i j : Fin n) : ContDiffOn ℝ 1 (fun x ↦ a i j (v x)) Ω :=
      ((ha i j).of_le (by simp)).comp_contDiffOn (hv.of_le (by norm_num))
    have hfc (i : Fin n) : ContDiffOn ℝ 1 (fun x ↦ f l i (v x)) Ω :=
      ((hf l i).of_le (by simp)).comp_contDiffOn (hv.of_le (by norm_num))
    have hQ (i : Fin n) : ContDiffOn ℝ 1
        (fun x ↦ (∑ j, a i j (v x) * (∂[j] (fun y ↦ v y l)) x) -
          f l i (v x)) Ω :=
      (ContDiffOn.sum fun j _ ↦ (hac i j).mul (hd j)).sub (hfc i)
    apply ((heq l).partialDeriv hΩ hQ k).congr hΩ
    intro i x hx
    have hdx := fun j ↦ (hd j).differentiableOn (by norm_num) x hx
    have hax := fun j ↦ (hac i j).differentiableOn (by norm_num) x hx
    have hfx := (hfc i).differentiableOn (by norm_num) x hx
    have hdx' := fun j ↦ (hdx j).differentiableAt (hΩ.mem_nhds hx)
    have hax' := fun j ↦ (hax j).differentiableAt (hΩ.mem_nhds hx)
    rw [partialDeriv_sub
      (DifferentiableAt.fun_sum (u := Finset.univ) fun j _ ↦
        (hax' j).fun_mul (hdx' j))
      (hfx.differentiableAt (hΩ.mem_nhds hx)),
      partialDeriv_sum Finset.univ (fun j _ ↦ (hax' j).fun_mul (hdx' j))]
    simp_rw [partialDeriv_mul (hax' _) (hdx' _)]
    rw [prolongedForcing_comp_firstJet
      ((hv.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))
      (fun i j ↦ (ha i j).differentiable (by simp) _)
      (fun l i ↦ (hf l i).differentiable (by simp) _)]
    change _ = (∑ j, a i j (v x) *
      (∂[j] (∂[k] (fun y ↦ v y l))) x) - _
    simp_rw [partialDeriv_partialDeriv_comm_at k _
      (hvc.contDiffAt (hΩ.mem_nhds hx)), Finset.sum_add_distrib]
    ring

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
