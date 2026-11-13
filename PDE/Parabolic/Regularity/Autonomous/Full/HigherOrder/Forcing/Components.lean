/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing

/-!
# Finite components of a parabolic forcing tuple

The recursive tuple is equivalent to its ordinary finite family of Sobolev
fields. Its norm is the full finite sum, including the final order-zero field.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

private theorem norm_order_cast {r s : ℕ} (h : r = s)
    (F : Lp (W^{r,2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    ‖(h ▸ F : Lp (W^{s,2}(Ω)) 2 (volume.restrict (Ioc a b)))‖ = ‖F‖ := by
  subst s
  rfl

private theorem base_order_cast {r s : ℕ} (h : r = s)
    (F : Lp (W^{r,2}(Ω)) 2 (volume.restrict (Ioc a b))) (t : ℝ) :
    wkpBaseCoordinateCLM
      ((h ▸ F : Lp (W^{s,2}(Ω)) 2 (volume.restrict (Ioc a b))) t) =
      wkpBaseCoordinateCLM (F t) := by
  subst s
  rfl

/-- The component of index `k` has spatial order `2(m-k)`. The finite index
prevents truncation in natural subtraction from introducing extra components. -/
def component : {m : ℕ} → ForcingJet n Ω a b m → (k : Fin (m + 1)) →
    Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b))
  | 0, F, k => by
      have hk : k = 0 := Fin.fin_one_eq_zero k
      subst k
      exact F.head
  | m + 1, F, k => by
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · exact F.1
      · have h : 2 * (m - j.val) = 2 * (m + 1 - j.succ.val) := by
          simp only [Fin.val_succ, Nat.add_sub_add_right]
        exact h ▸ component F.2 j

/-- Index zero recovers the undifferentiated field. -/
@[simp]
theorem component_zero {m : ℕ} (F : ForcingJet n Ω a b m) :
    F.component 0 = F.head := by
  cases m <;> rfl

/-- The zeroth component and the head have the same underlying pivot field. -/
theorem base_component_zero {m : ℕ} (F : ForcingJet n Ω a b m) (t : ℝ) :
    wkpBaseCoordinateCLM (F.component 0 t) = wkpBaseCoordinateCLM (F.head t) := by
  cases m <;> rfl

/-- Deleting the head shifts the component index by one. -/
theorem norm_component_succ {m : ℕ} (F : ForcingJet n Ω a b (m + 1))
    (k : Fin (m + 1)) : ‖F.component k.succ‖ = ‖F.2.component k‖ := by
  exact norm_order_cast (by simp only [Fin.val_succ, Nat.add_sub_add_right])
    (F.2.component k)

/-- Shifting the finite index retains the underlying pivot field. -/
theorem base_component_succ {m : ℕ} (F : ForcingJet n Ω a b (m + 1))
    (k : Fin (m + 1)) (t : ℝ) :
    wkpBaseCoordinateCLM (F.component k.succ t) =
      wkpBaseCoordinateCLM (F.2.component k t) :=
  base_order_cast (by simp only [Fin.val_succ, Nat.add_sub_add_right])
    (F.2.component k) t

/-- The recursive norm sum is exactly the sum over all finite components. -/
theorem normSum_eq_sum {m : ℕ} (F : ForcingJet n Ω a b m) :
    F.normSum = ∑ k : Fin (m + 1), ‖F.component k‖ := by
  induction m with
  | zero =>
    change ‖F.head‖ = ∑ k : Fin 1, ‖F.component k‖
    rw [Fin.sum_univ_one, component_zero]
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [component_zero, norm_component_succ]
    exact congrArg (‖F.1‖ + ·) (ih F.2)

/-- Construct the recursive tuple from an ordinary finite family of fields. -/
def ofFamily : {m : ℕ} →
    ((k : Fin (m + 1)) →
      Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b))) →
    ForcingJet n Ω a b m
  | 0, f => f 0
  | m + 1, f =>
      (f 0, ofFamily (fun k ↦ by
        have h : 2 * (m + 1 - k.succ.val) = 2 * (m - k.val) := by
          simp only [Fin.val_succ, Nat.add_sub_add_right]
        exact h ▸ f k.succ))

/-- The finite family constructor retains the zeroth forcing field. -/
@[simp]
theorem head_ofFamily {m : ℕ}
    (f : (k : Fin (m + 1)) →
      Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    (ofFamily f).head = f 0 := by
  cases m <;> rfl

/-- The head of the constructed tuple represents the original zeroth field. -/
theorem base_head_ofFamily {m : ℕ}
    (f : (k : Fin (m + 1)) →
      Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b))) (t : ℝ) :
    wkpBaseCoordinateCLM ((ofFamily f).head t) = wkpBaseCoordinateCLM (f 0 t) := by
  cases m <;> rfl

/-- Constructing a tuple preserves the entire finite data norm sum. -/
theorem normSum_ofFamily {m : ℕ}
    (f : (k : Fin (m + 1)) →
      Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    (ofFamily f).normSum = ∑ k : Fin (m + 1), ‖f k‖ := by
  induction m with
  | zero => exact (Fin.sum_univ_one (fun k ↦ ‖f k‖)).symm
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    change ‖f 0‖ + (ofFamily _).normSum = _
    rw [ih]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact norm_order_cast _ (f k.succ)

/-- In the pivot space, each component of a regularity tuple is the weak
time derivative of the previous one. The stronger common Sobolev identity is retained
by `HasWeakDerivatives` itself. -/
theorem HasWeakDerivatives.components {m : ℕ} {F : ForcingJet n Ω a b m}
    (hF : F.HasWeakDerivatives) (k : Fin m) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (F.component k.castSucc t))
      (fun t ↦ wkpBaseCoordinateCLM (F.component k.succ t)) := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · apply hF.headBase.congr_ae_restrict measurableSet_Ioo
      · filter_upwards [F.headBase_ae.filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
        change F.headBase t = wkpBaseCoordinateCLM (F.component 0 t)
        rw [base_component_zero]
        exact ht
      · filter_upwards [F.2.headBase_ae.filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
        rw [base_component_succ, base_component_zero]
        exact ht
    · simpa only [Fin.castSucc_succ, base_component_succ] using ih hF.2 j

/-- Adjacent pivot weak derivatives of a finite forcing family give all
the common Sobolev derivative identities required by the induction. -/
theorem hasWeakDerivatives_ofFamily (hopen : IsOpen Ω) {m : ℕ}
    (f : (k : Fin (m + 1)) →
      Lp (W^{(2 * (m - k.val)),2}(Ω)) 2 (volume.restrict (Ioc a b)))
    (hf : ∀ k : Fin m, HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (f k.castSucc t))
      (fun t ↦ wkpBaseCoordinateCLM (f k.succ t))) :
    (ofFamily f).HasWeakDerivatives := by
  induction m with
  | zero => trivial
  | succ m ih =>
    apply HasWeakDerivatives.cons_of_base (m := m) hopen (f 0)
    · apply ih
      intro k
      simpa only [base_order_cast, Fin.castSucc_succ] using hf k.succ
    · apply (hf 0).congr_ae_restrict measurableSet_Ioo
      · exact Filter.EventuallyEq.rfl
      · filter_upwards [] with t
        rw [base_head_ofFamily]
        exact (base_order_cast (by simp only [Fin.val_succ, Nat.add_sub_add_right])
          (f (Fin.succ 0)) t).symm

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet
