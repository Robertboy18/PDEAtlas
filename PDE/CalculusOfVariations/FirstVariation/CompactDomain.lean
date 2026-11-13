/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Calculus
public import PDE.Analysis.Calculus.Jet.Closure
public import PDE.Analysis.Calculus.CompactParametricIntegral.AlmostEverywhere
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# First variation on a bounded domain

The action uses the Jacobian and the full density `L(P,z,x)`. Continuous
extensions of the density derivatives suffice at boundary points. A compact set of
perturbed jets supplies the domination needed for differentiation under the integral;
no growth condition on the density or compact support of the variation is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u v : ℝ^n → ℝ^m}

/-- The integral action of a first-order density on a Euclidean domain. -/
def lagrangianAction (Ω : Set (ℝ^n))
    (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ) (u : ℝ^n → ℝ^m) : ℝ :=
  ∫ x in Ω, L (jacobianMatrix u x) (u x) x

/-- The action depends only on the map in the open domain, including its
Jacobian there. Assigned values outside the domain do not affect the integral. -/
theorem lagrangianAction_congr (hopen : IsOpen Ω) (huv : EqOn u v Ω) :
    lagrangianAction Ω L u = lagrangianAction Ω L v := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  rw [jacobianMatrix_eq_of_eventuallyEq (huv.eventuallyEq_of_mem (hopen.mem_nhds hx)),
    huv hx]

/-- Differentiate the action along an affine family of classical maps.
The density is only required to have a continuous classical second jet up to the
spatial boundary; it need not extend differentiably across that boundary. -/
theorem hasDerivAt_lagrangianAction
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • v x))
      (∫ x in Ω,
        fderiv ℝ (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
          L a.1 a.2.1 a.2.2)
          (jacobianMatrix u x + t • jacobianMatrix v x, (u x + t • v x, x))
          (jacobianMatrix v x, (v x, 0))) t := by
  let J := Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n)
  let q (s : ℝ) (x : ℝ^n) : J :=
    (jacobianMatrix u x + s • jacobianMatrix v x, (u x + s • v x, x))
  let w (x : ℝ^n) : J := (jacobianMatrix v x, (v x, 0))
  let F (s : ℝ) (x : ℝ^n) := L (q s x).1 (q s x).2.1 (q s x).2.2
  let D (s : ℝ) (x : ℝ^n) :=
    (hL.first (q s x)).comp (ContinuousLinearMap.toSpanSingleton ℝ (w x))
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
    hL.continuousOn.comp hq.continuousOn hmap
  have hD : ContinuousOn D.uncurry (univ ×ˢ closure Ω) :=
    (hL.continuousOn_first.comp hq.continuousOn hmap).clm_comp
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ J).continuous.comp
        (hw.comp continuous_snd)).continuousOn)
  have hd (x : ℝ^n) (hx : x ∈ Ω) (s : ℝ) :
      HasFDerivAt (fun r ↦ F r x) (D s x) s := by
    have hjet := (((hasDerivAt_id s).smul_const (jacobianMatrix v x)).const_add
      (jacobianMatrix u x)).prodMk
        ((((hasDerivAt_id s).smul_const (v x)).const_add (u x)).prodMk
          (hasDerivAt_const s x))
    simpa [F, D, q, w, Function.comp_def] using
      (hL.hasFDerivAt (hopen.preimage (continuous_snd.comp continuous_snd))
        (show q s x ∈ {a : J | a.2.2 ∈ Ω} from hx)).comp s hjet.hasFDerivAt
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
  simp only [D, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hi
  have heq : (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • v x)) =
      fun s ↦ ∫ x in Ω, F s x := by
    funext s
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      dsimp [lagrangianAction, F, q]
      have hvs : DifferentiableAt ℝ (fun y ↦ s • v y) x := by
        exact (differentiableAt_const s).smul (hv.differentiable (by norm_num) x)
      rw [jacobianMatrix_add (hu.differentiable (by norm_num) x)
        hvs, jacobianMatrix_const_smul]
  rw [heq]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  exact congrArg (fun A ↦ A (w x)) (hL.first_eq (show q t x ∈ {a : J | a.2.2 ∈ Ω} from hx))
    |>.symm

end PDE.CalculusOfVariations
