/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.CompactDomain
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.Analysis.Calculus.Jet.Composition

/-!
# Nonlinear second variation on a bounded domain

Differentiating the first variation gives the integral of the density's
Hessian on the perturbed jet. All matrix and value coordinates may be coupled.
The density has a continuous second jet up to the boundary; compactness supplies
the bounds needed to differentiate under the integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- The derivative of the action's first derivative is the integral Hessian.
The directions include both the Jacobian and the value of the variation, so this
formula includes the mixed matrix–value terms for a general coupled density. -/
theorem hasDerivAt_deriv_lagrangianAction
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (t : ℝ) :
    HasDerivAt
      (deriv (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • v x)))
      (∫ x in Ω, fderiv ℝ (fderiv ℝ
        (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2))
        (jacobianMatrix u x + t • jacobianMatrix v x, (u x + t • v x, x))
        (jacobianMatrix v x, (v x, 0)) (jacobianMatrix v x, (v x, 0))) t := by
  let J := Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n)
  let q (s : ℝ) (x : ℝ^n) : J :=
    (jacobianMatrix u x + s • jacobianMatrix v x, (u x + s • v x, x))
  let w (x : ℝ^n) : J := (jacobianMatrix v x, (v x, 0))
  let F (s : ℝ) (x : ℝ^n) := hL.first (q s x) (w x)
  let D (s : ℝ) (x : ℝ^n) :=
    ContinuousLinearMap.toSpanSingleton ℝ (hL.second (q s x) (w x) (w x))
  have hju : Continuous (jacobianMatrix u) := (contDiff_jacobianMatrix hu).continuous
  have hjv : Continuous (jacobianMatrix v) := (contDiff_jacobianMatrix hv).continuous
  have hq : Continuous q.uncurry :=
    ((hju.comp continuous_snd).add
      (continuous_fst.smul (hjv.comp continuous_snd))).prodMk
        (((hu.continuous.comp continuous_snd).add
          (continuous_fst.smul (hv.continuous.comp continuous_snd))).prodMk continuous_snd)
  have hw : Continuous w := hjv.prodMk (hv.continuous.prodMk continuous_const)
  have hmap : MapsTo q.uncurry (univ ×ˢ closure Ω) (closure {a : J | a.2.2 ∈ Ω}) := by
    intro z hz
    have hm : MapsTo (q z.1) Ω {a : J | a.2.2 ∈ Ω} := fun _ hx ↦ hx
    exact hm.closure (hq.comp (continuous_const.prodMk continuous_id)) hz.2
  have hF : ContinuousOn F.uncurry (univ ×ˢ closure Ω) :=
    (hL.continuousOn_first.comp hq.continuousOn hmap).clm_apply
      (hw.comp continuous_snd).continuousOn
  have hH : ContinuousOn
      (fun z : ℝ × ℝ^n ↦ hL.second (q z.1 z.2) (w z.2) (w z.2))
      (univ ×ˢ closure Ω) :=
    ((hL.continuousOn_second.comp hq.continuousOn hmap).clm_apply
      (hw.comp continuous_snd).continuousOn).clm_apply
        (hw.comp continuous_snd).continuousOn
  have hD : ContinuousOn D.uncurry (univ ×ˢ closure Ω) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hH
  have hd (x : ℝ^n) (hx : x ∈ Ω) (s : ℝ) :
      HasFDerivAt (fun r ↦ F r x) (D s x) s := by
    have hjet := (((hasDerivAt_id s).smul_const (jacobianMatrix v x)).const_add
      (jacobianMatrix u x)).prodMk
        ((((hasDerivAt_id s).smul_const (v x)).const_add (u x)).prodMk
          (hasDerivAt_const s x))
    have hfirst := (Analysis.ContinuousSecondJetOn.hasFDerivAt_first hL
      (hopen.preimage (continuous_snd.comp continuous_snd))
      (show q s x ∈ {a : J | a.2.2 ∈ Ω} from hx)).comp s hjet.hasFDerivAt
    have heval := hfirst.hasDerivAt.clm_apply (hasDerivAt_const s (w x))
    simpa [F, D, q, w, Function.comp_def] using heval.hasFDerivAt
  have hfinite : volume Ω ≠ ⊤ :=
    ne_top_of_le_ne_top hbounded.isCompact_closure.measure_ne_top
      (measure_mono subset_closure)
  have hi := (hasFDerivAt_setIntegral_of_compact_closure hopen.measurableSet
    hbounded.isCompact_closure hfinite hF hD hd t).hasDerivAt
  have hDi : IntegrableOn (D t) Ω :=
    (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨mem_univ _, hx⟩)).integrableOn_of_subset_isCompact
        hbounded.isCompact_closure hopen.measurableSet subset_closure hfinite
  rw [ContinuousLinearMap.integral_apply hDi] at hi
  simp only [D, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hi
  have heq : deriv (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • v x)) =
      fun s ↦ ∫ x in Ω, F s x := by
    funext s
    rw [(hasDerivAt_lagrangianAction hopen hbounded hL hu hv s).deriv]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    exact congrArg (fun A ↦ A (w x))
      (hL.first_eq (show q s x ∈ {a : J | a.2.2 ∈ Ω} from hx)) |>.symm
  rw [heq]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  exact congrArg (fun A ↦ A (w x) (w x))
    (hL.second_eq (show q t x ∈ {a : J | a.2.2 ∈ Ω} from hx)) |>.symm

end PDE.CalculusOfVariations
