/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.OperatorProduct
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion

/-!
# Differentiating an evolution equation in the dual space

Let `u ∈ L²(a, b; V)` have a `V`-valued weak derivative `v`, and suppose that
`energyToDual v(t) = L u(t) + pivotToDual (C(t) u(t) + F(t))` almost everywhere, where
`L : V → V*` is fixed, `C : [a, b] → L(V, H)` is absolutely continuous with continuous
derivative `C'`, and `F ∈ L²(a, b; H)` has weak derivative `F'`. Differentiating the right side
shows that `L v + pivotToDual (C' u + C v + F')` is the weak derivative of `v` in
`L²(a, b; V*)`. The Lions–Magenes theorem then gives a continuous pivot representative of the
velocity `v`, and the equation identifies its dual image at every time of `[a, b]`, endpoints
included, in terms of continuous representatives of `u` and `F`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

private theorem memLp_clm_apply_Ioc
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a b : ℝ} {C : ℝ → X →L[ℝ] Y}
    (hC : ContinuousOn C (Icc a b))
    {u : ℝ → X} (hu : MemLp u 2 (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ C t (u t)) 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (((hC.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).prodMk
      hu.aestronglyMeasurable)
  apply MemLp.of_le_mul (c := K) hu hm
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (C t).le_opNorm (u t) |>.trans
    (mul_le_mul_of_nonneg_right (hK t (Ioc_subset_Icc_self ht)) (norm_nonneg _))

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]

/-- Under the hypotheses of the module docstring, there is a weak derivative
`g = L v + pivotToDual (C' u + C v + F')` of `v` in `L²(a, b; V*)` and a continuous pivot
representative `E` of `v` with `pivotToDual (E t) = L z(t) + pivotToDual (C(t) z(t) + Fc(t))`
for every `t ∈ [a, b]`, where `z` and `Fc` are continuous representatives of `u` and `F`. -/
theorem exists_continuousPivotEvolutionOn_of_differentiated_equation
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} (hab : a < b)
    {u v : Lp V 2 (volume.restrict (Ioc a b))}
    (hu : HasWeakTimeDerivativeOn (Ioo a b) u v)
    {F dF : Lp H 2 (volume.restrict (Ioc a b))}
    (hF : HasWeakTimeDerivativeOn (Ioo a b) F dF)
    (L : V →L[ℝ] StrongDual ℝ V)
    {C dC : ℝ → V →L[ℝ] H}
    (hC : AbsolutelyContinuousOnInterval C a b)
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt C (dC t) t)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      T.energyToDual (v t) = L (u t) + T.pivotToDual (C t (u t) + F t))
    {z : ℝ → V} (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] u)
    {Fc : ℝ → H} (hFc : ContinuousOn Fc (Icc a b))
    (hFcF : Fc =ᵐ[volume.restrict (Ioc a b)] F) :
    ∃ (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
      (E : ContinuousPivotEvolutionOn T (fun t ↦ v t) (fun t ↦ g t) a b),
      ((fun t ↦ g t) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
        L (v t) + T.pivotToDual (dC t (u t) + C t (v t) + dF t)) ∧
      ∀ t ∈ Icc a b, T.pivotToDual (E.representative t) =
        L (z t) + T.pivotToDual (C t (z t) + Fc t) := by
  have hCcont : ContinuousOn C (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hC.continuousOn
  have hmprod := (memLp_clm_apply_Ioc hdC (Lp.memLp u)).add
    (memLp_clm_apply_Ioc hCcont (Lp.memLp v))
  let R : ℝ → StrongDual ℝ V := fun t ↦
    L (v t) + T.pivotToDual (dC t (u t) + C t (v t) + dF t)
  have hR : MemLp R 2 (volume.restrict (Ioc a b)) :=
    (L.comp_memLp v).add (T.pivotToDual.comp_memLp' (hmprod.add (Lp.memLp dF)))
  let g := hR.toLp R
  have hg : (fun t ↦ g t) =ᵐ[volume.restrict (Ioc a b)] R := hR.coeFn_toLp
  have hprod := hu.clm_apply_of_lp hC hderiv (hmprod.integrable (by norm_num))
  have hweak := (hu.map L).add ((hprod.add hF).map T.pivotToDual)
  have hmeasure : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hvelocity : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ T.energyToDual (v t)) (fun t ↦ g t) := by
    apply hweak.congr_ae_restrict measurableSet_Ioo
    · rw [hmeasure]
      filter_upwards [heq] with t ht using ht.symm
    · rw [hmeasure]
      exact hg.symm
  obtain ⟨Eopen⟩ := hvelocity.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp v) (Lp.memLp g)
  refine ⟨g, E, hg, ?_⟩
  have hae : (fun t ↦ T.pivotToDual (E.representative t))
      =ᵐ[volume.restrict (Icc a b)]
        fun t ↦ L (z t) + T.pivotToDual (C t (z t) + Fc t) := by
    have hE := E.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at hE
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc] at hE ⊢
    filter_upwards [hE, heq, hzu, hFcF] with t ht hte htz htf
    rw [ht, htz, htf]
    exact hte
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
    (T.pivotToDual.continuous.comp_continuousOn (by
      simpa only [uIcc_of_le hab.le] using E.continuousOn))
    ((L.continuous.comp_continuousOn hz).add
      (T.pivotToDual.continuous.comp_continuousOn ((hCcont.clm_apply hz).add hFc)))

end PDE.Analysis.Evolution
