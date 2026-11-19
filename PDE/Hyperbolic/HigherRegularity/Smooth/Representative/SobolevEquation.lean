/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.WeakIdentification
public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.Forcing

/-!
# The full wave equation on canonical Sobolev slices

The original weak equation and identification of its acceleration give the
spatial Sobolev equation almost everywhere in time. Continuity gives every
time in the closed interval. Differentiating that identity through the
bounded autonomous load gives all higher equations, including their endpoint
values. The operator is the same full signed divergence operator at every order.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity PDE.Analysis.Evolution
open SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (P : SmoothFullCoefficients n Ω)
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f U : SpaceTime n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hU : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hcont : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
  {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
  {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
  {w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
  {q₀ : H¹₀(Ω)} {p₀ : DerivLp n 2 Ω}
  (hweak : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
    (fun _ ↦ P.form hopen hbounded)
    (dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head)
    u v w q₀ p₀)
  (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
    (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
      baseRepresentative (h10SubtypeL (u t)))

include hcont hweak hae

/-- The original weak equation holds in every finite spatial Sobolev space
at every time, including both endpoints. -/
theorem sobolev_equation (r : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    sobolevCurve hopen hbounded hab hU r 2 t +
      P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU (r + 2) 0 t) =
        sobolevCurve hopen hbounded hab hf r 0 t := by
  have hq := sobolevCurve_ae_of_representative hopen hbounded hab hU hcont hae
  have hw := acceleration_ae hopen hbounded hab hU hcont hweak hae
  have heq : (fun s ↦ sobolevCurve hopen hbounded hab hU r 2 s +
      P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU (r + 2) 0 s))
      =ᵐ[volume.restrict (Ioc a b)] sobolevCurve hopen hbounded hab hf r 0 := by
    filter_upwards [hq, hw, hweak.equationAE,
      dirichletLoadTimeLp_apply_ae hopen (forcingJet hopen hbounded hab hf 0 0).head,
      sobolevTimeDerivative_ae hopen hbounded hab hf 0 0,
      ae_restrict_mem measurableSet_Ioc] with s hq hw heq hell hforcing hs
    have hsi := Ioc_subset_Icc_self hs
    have hbase : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU (r + 2) 0 s) =
        baseCoordCLM (u s) := by
      rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU (r + 2) 0 hsi,
        ← wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 1 0 hsi, hq]
      rfl
    have hform : P.form hopen hbounded (u s) = (h10L2GelfandTriple hopen).pivotToDual
          (wkpBaseCoordinateCLM
            (P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU (r + 2) 0 s))) := by
      ext z
      exact P.form_eq_load hopen hbounded r _ _ z hbase
    have hac : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU r 2 s) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 2 s) := by
      rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU r 2 hsi,
        wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 1 2 hsi]
    have hfc : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf r 0 s) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 s) := by
      rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r 0 hsi,
        wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf 0 0 hsi]
    rw [← hw, hform, hell] at heq
    change _ = loadFunctional
      (wkpBaseCoordinateCLM (sobolevTimeDerivative hopen hbounded hab hf 0 0 s)) at heq
    rw [hforcing] at heq
    have hload (z : DerivLp n 2 Ω) :
        loadFunctional z = (h10L2GelfandTriple hopen).pivotToDual z := by
      ext y
      rfl
    rw [hload] at heq
    apply wkpBaseCoordinateCLM_injective hopen
    apply (h10L2GelfandTriple hopen).pivotToDual_injective
    simpa only [map_add, hac, hfc] using heq
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne ((ae_restrict_congr_set Ioc_ae_eq_Icc).mp heq)
    ((continuousOn_sobolevCurve hopen hbounded hab hU r 2).add
      ((P.load hopen hbounded r).continuous.comp_continuousOn
        (continuousOn_sobolevCurve hopen hbounded hab hU (r + 2) 0)))
    (continuousOn_sobolevCurve hopen hbounded hab hf r 0) ht

/-- Every time derivative satisfies the differentiated full equation in every
finite Sobolev space, with its canonical initial and final values. -/
theorem sobolev_equation_timeDerivative (j r : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    sobolevCurve hopen hbounded hab hU r (j + 2) t +
      P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU (r + 2) j t) =
        sobolevCurve hopen hbounded hab hf r j t := by
  induction j generalizing t with
  | zero => exact sobolev_equation P hopen hbounded hab hf hU hcont hweak hae r ht
  | succ j ih =>
    have hd := (hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU r (j + 2)).add
      ((hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU (r + 2) j).map
        (P.load hopen hbounded r))
    have hd' : HasWeakTimeDerivativeOn (Ioo a b) (sobolevCurve hopen hbounded hab hf r j)
        (fun s ↦ sobolevCurve hopen hbounded hab hU r (j + 1 + 2) s +
          P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU (r + 2) (j + 1) s)) := by
      apply hd.congr_ae_restrict measurableSet_Ioo ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact ih (Ioo_subset_Icc_self hs)
      · exact Filter.Eventually.of_forall fun s ↦ by
          dsimp only [Function.comp_apply]
    have heq := hd'.ae_eq isOpen_Ioo
      (hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hf r j)
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne ((ae_restrict_congr_set Ioo_ae_eq_Icc).mp heq)
      ((continuousOn_sobolevCurve hopen hbounded hab hU r (j + 1 + 2)).add
        ((P.load hopen hbounded r).continuous.comp_continuousOn
          (continuousOn_sobolevCurve hopen hbounded hab hU (r + 2) (j + 1))))
      (continuousOn_sobolevCurve hopen hbounded hab hf r (j + 1)) ht

end Hyperbolic.HigherRegularity.SmoothWave
