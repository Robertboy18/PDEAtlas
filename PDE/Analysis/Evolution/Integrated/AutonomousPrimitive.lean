/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.WeakEquation
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.AbsolutelyContinuous
public import PDE.Analysis.Evolution.Time.FundamentalTheorem
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Reconstructing an autonomous evolution from its time derivative

If `v' + Bv = f'` and `v(a) = f(a) - Bg`, integration gives the original
equation for `g + ∫ v`. The operator is only required to be bounded and
autonomous. In particular it need not be symmetric.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Integration of the differentiated equation recovers the original
autonomous equation at every time, including both endpoints. -/
theorem ContinuousPivotEvolutionOn.autonomous_primitive_equation
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ} (hab : a ≤ b)
    (B : V →L[ℝ] StrongDual ℝ V)
    {v : Lp V 2 (volume.restrict (Ioc a b))}
    {dv : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ v t) (fun t ↦ dv t) a b)
    (df : Lp H 2 (volume.restrict (Ioc a b))) (f : ℝ → H) (g : V)
    (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, df s)
    (hinitial : T.pivotToDual (E.representative a) = T.pivotToDual (f a) - B g)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      dv t = T.pivotToDual (df t) - B (v t)) :
    ∀ t ∈ Icc a b,
      T.pivotToDual (E.representative t) + B (g + ∫ s in a..t, v s) =
        T.pivotToDual (f t) := by
  intro t ht
  have hvt := (intervalIntegrable_coeFn_L2_restrict_Ioc v hab).mono_set
    (uIcc_subset_uIcc_left (show t ∈ uIcc a b by rwa [uIcc_of_le hab]))
  have hft := (intervalIntegrable_coeFn_L2_restrict_Ioc df hab).mono_set
    (uIcc_subset_uIcc_left (show t ∈ uIcc a b by rwa [uIcc_of_le hab]))
  have hint : (∫ s in a..t, dv s) =
      T.pivotToDual (∫ s in a..t, df s) - B (∫ s in a..t, v s) := by
    have hfmap : IntervalIntegrable (fun s ↦ T.pivotToDual (df s)) volume a t :=
      ⟨T.pivotToDual.integrable_comp hft.1, T.pivotToDual.integrable_comp hft.2⟩
    have hvmap : IntervalIntegrable (fun s ↦ B (v s)) volume a t :=
      ⟨B.integrable_comp hvt.1, B.integrable_comp hvt.2⟩
    rw [← T.pivotToDual.intervalIntegral_comp_comm hft,
      ← B.intervalIntegral_comp_comm hvt,
      ← intervalIntegral.integral_sub hfmap hvmap]
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
    apply integral_congr_ae
    exact heq.filter_mono (ae_mono (volume.restrict_mono_set
      (Ioc_subset_Ioc_right ht.2)))
  have hE := E.integratedDerivative.eq_add_integral t
    (show t ∈ uIcc a b by rwa [uIcc_of_le hab])
  change T.pivotToDual (E.representative t) =
    T.pivotToDual (E.representative a) + ∫ s in a..t, dv s at hE
  rw [hE, hinitial, hint, hf t ht, map_add, map_add]
  abel

/-- The Bochner primitive of an energy-space `L²` curve is absolutely
continuous and has that curve as its strong derivative almost everywhere. -/
theorem exists_energy_primitive
    {a b : ℝ} (hab : a ≤ b)
    (v : Lp V 2 (volume.restrict (Ioc a b))) (g : V) :
    ∃ u : Lp V 2 (volume.restrict (Ioc a b)),
      let w := fun t ↦ g + ∫ s in a..t, v s
      AbsolutelyContinuousOnInterval w a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt w (v t) t) ∧
      (u : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] w := by
  let w := fun t ↦ g + ∫ s in a..t, v s
  have hv := intervalIntegrable_coeFn_L2_restrict_Ioc v hab
  have hw : AbsolutelyContinuousOnInterval w a b := by
    apply absolutelyContinuousOnInterval_of_eq_add_integral hv
    intro t _
    simp only [w, intervalIntegral.integral_same, add_zero]
  have hwmem : MemLp w 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn (by
      simpa only [uIcc_of_le hab] using hw.continuousOn)
  refine ⟨hwmem.toLp w, hw, ?_, hwmem.coeFn_toLp⟩
  have hd := IntervalIntegrable.ae_hasDerivAt_integral hv
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hd] with t ht hti
  have hti' : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hti.1.le, hti.2⟩
  simpa only [zero_add] using (ht hti' a left_mem_uIcc).const_add g

/-- Solving the differentiated equation with the correct initial velocity
constructs a weak solution of the original equation. Its energy-valued
primitive has the strong derivative `v` almost everywhere. -/
theorem ContinuousPivotEvolutionOn.exists_integrated_solution_of_derivative
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ} (hab : a < b)
    (B : V →L[ℝ] StrongDual ℝ V)
    {v : Lp V 2 (volume.restrict (Ioc a b))}
    {dv : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ v t) (fun t ↦ dv t) a b)
    (f df : Lp H 2 (volume.restrict (Ioc a b))) (g : V)
    {fRep : ℝ → H}
    (hfAC : AbsolutelyContinuousOnInterval fRep a b)
    (hfRep : fRep =ᵐ[volume.restrict (Ioc a b)] fun t ↦ f t)
    (hfDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt fRep (df t) t)
    (hinitial : T.pivotToDual (E.representative a) = T.pivotToDual (fRep a) - B g)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      dv t = T.pivotToDual (df t) - B (v t)) :
    ∃ u : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u (T.inclusion g) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) v) ∧
      (u : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] fun t ↦ g + ∫ s in a..t, v s := by
  have hfFTC : ∀ t ∈ Icc a b, fRep t = fRep a + ∫ s in a..t, df s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b :=
      uIcc_subset_uIcc_left (by rwa [uIcc_of_le hab.le])
    have hft := (intervalIntegrable_coeFn_L2_restrict_Ioc df hab.le).mono_set hsub
    have hfi : IntegrableOn (fun s ↦ df s) (Icc a t) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mp hft
    have hfd := hfDeriv.filter_mono
      (ae_mono (volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2)))
    have h := AbsolutelyContinuousOnInterval.intervalIntegral_eq_sub_of_ae_hasDerivAt_normedSpace
      ht.1 (hfAC.mono hsub) hfi hfd
    rw [h]
    abel
  obtain ⟨u, huAC, huDeriv, huRep⟩ := exists_energy_primitive hab.le v g
  let w := fun t ↦ g + ∫ s in a..t, v s
  have huWeak : HasGelfandWeakTimeDerivativeOn T u
      (T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) v) :=
    .of_absolutelyContinuousOnInterval T hab.le huAC huDeriv huRep
      (T.energyToDual.coeFn_compLpL v)
  have hpoint := E.autonomous_primitive_equation hab.le B df fRep g hfFTC hinitial heq
  have hERep := E.ae_eq_inclusion.filter_mono
    (ae_mono (volume.restrict_mono_set (show Ioc a b ⊆ uIcc a b by
      rw [uIcc_of_le hab.le]
      exact Ioc_subset_Icc_self)))
  have heqU : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) v) t + B (u t) =
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) t := by
    filter_upwards [hERep, huRep, hfRep, T.energyToDual.coeFn_compLpL v,
      T.pivotToDual.coeFn_compLpL f, ae_restrict_mem measurableSet_Ioc]
      with t hEt hut hft hvt hFt ht
    have hp := hpoint t ⟨ht.1.le, ht.2⟩
    rw [hEt, hft] at hp
    rw [hvt, hFt, hut]
    exact hp
  have hwC : ContinuousOn (fun t ↦ T.inclusion (w t)) (Icc a b) :=
    T.inclusion.continuous.comp_continuousOn (by
      simpa only [w, uIcc_of_le hab.le] using huAC.continuousOn)
  have hwRep : (fun t ↦ T.inclusion (w t)) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.inclusion (u t) :=
    huRep.symm.fun_comp T.inclusion
  have huSol := huWeak.integrated_solution_of_ae_equation hab hwC hwRep
    (fun _ ↦ aestronglyMeasurable_const) ‖B‖
    (Eventually.of_forall fun _ ↦ le_rfl) heqU
  simp only [w, intervalIntegral.integral_same, add_zero] at huSol
  exact ⟨u, huSol, huWeak, huRep⟩

/-- If the original integrated problem has a unique energy trajectory, the
solution of its differentiated equation is the trajectory's weak
time derivative. This identifies the constructed primitive with the given
solution rather than assuming additional trajectory regularity. -/
theorem ContinuousPivotEvolutionOn.has_weak_derivative_of_unique_solution
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ} (hab : a < b)
    (B : V →L[ℝ] StrongDual ℝ V)
    {v : Lp V 2 (volume.restrict (Ioc a b))}
    {dv : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ v t) (fun t ↦ dv t) a b)
    (f df : Lp H 2 (volume.restrict (Ioc a b))) (g : V)
    {fRep : ℝ → H}
    (hfAC : AbsolutelyContinuousOnInterval fRep a b)
    (hfRep : fRep =ᵐ[volume.restrict (Ioc a b)] fun t ↦ f t)
    (hfDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt fRep (df t) t)
    (hinitial : T.pivotToDual (E.representative a) = T.pivotToDual (fRep a) - B g)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      dv t = T.pivotToDual (df t) - B (v t))
    (u : Lp V 2 (volume.restrict (Ioc a b)))
    (hunique : ∀ w : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) w (T.inclusion g) →
      w = u) :
    HasGelfandWeakTimeDerivativeOn T u
      (T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) v) := by
  obtain ⟨w, hwSol, hwDeriv, _⟩ := E.exists_integrated_solution_of_derivative
    hab B f df g hfAC hfRep hfDeriv hinitial heq
  exact hunique w hwSol ▸ hwDeriv

end PDE.Analysis.Evolution
