/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.InitialTrace
import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives

/-!
# Forcing representatives for Evans's differentiated wave chain

Evans's higher-regularity argument for the wave equation (Evans, §7.2.3,
Theorem 6) differentiates the equation `m` times in time.  The `k`-th
differentiated equation is forced by `∂ₜᵏ f`, which an order-`m`
`SobolevTimeJet` supplies only as an `L²_t H^{m-k}_x` class.  The Galerkin
construction needs more: each forcing as a function of time with
values in the Dirichlet dual `(H¹₀)*`, absolutely continuous in `t`, whose
derivative is the next member of the chain.  We choose such
representatives and prove the facts about them that the ODE and energy
steps use.

Members of the chain are indexed in reverse by `r : Fin (m + 1)`: `Fin.last m`
is the original forcing and each `castSucc` step takes one more time
derivative, so index `0` carries `∂ₜᵐ f`.  This matches the induction on `m`
used throughout the higher-regularity development.

## Main results

* `SobolevTimeJet.iteratedTimeDerivative`: the jet tail of remaining order `r`.
* `SobolevTimeJet.exists_dirichletLoadRepresentatives`: one successor step of
  a jet has an absolutely continuous Dirichlet-dual representative whose
  derivative represents the next jet entry almost everywhere.
* `SobolevTimeJet.exists_dirichletLoadForcingChain`: a coherent family of such
  representatives for the whole jet.
* `SobolevTimeJet.initialValue_eq_dirichletLoadTrace`: any absolutely
  continuous representative takes the canonical Lions-Magenes initial trace at
  `t0`, so the compatibility conditions see the right value of `f(0)`.
* `SobolevTimeJet.integrableOn_dirichletLoadForcing` and
  `SobolevTimeJet.intervalIntegrable_norm_sq_baseCoordinateTimeLp`: the
  integrability facts needed by the Carathéodory ODE step and the energy
  budget.

## Implementation notes

Representatives are compared only almost everywhere on `(t0, t1]`, the measure
carried by the jet's `Lp` classes; passing to `[t0, t1]` changes a null set.
The value at `t0` is pinned down by continuity of the chosen representative,
never by evaluating an `Lp` class at a point.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and step 2 of its proof,
  equations (67)-(69).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

namespace SobolevTimeJet

private theorem continuousOn_Icc_of_absolutelyContinuousOnInterval
    {Y : Type*} [SeminormedAddCommGroup Y] {f : ℝ → Y} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    ContinuousOn f (Set.Icc a b) := by
  rw [← Set.uIcc_of_le hab]
  exact hf.continuousOn

private theorem strongDual_eqOn_Icc_of_ae_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : ℝ → StrongDual ℝ V} {a b t : ℝ} (hab : a ≠ b)
    (hfg : f =ᵐ[volume.restrict (Set.Icc a b)] g) (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b)) (ht : t ∈ Set.Icc a b) :
    f t = g t := by
  ext w
  let eval : StrongDual ℝ V →L[ℝ] ℝ :=
    (@ContinuousLinearMap.apply ℝ V ℝ inferInstance inferInstance inferInstance
      inferInstance inferInstance) w
  exact Measure.eqOn_Icc_of_ae_eq volume hab (hfg.fun_comp fun h ↦ h w)
    (eval.continuous.comp_continuousOn hf) (eval.continuous.comp_continuousOn hg) ht

private theorem strongDual_mappedRepresentative_eq_at_initial {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (L : W →L[ℝ] StrongDual ℝ V)
    {forcing : ℝ → StrongDual ℝ V} {representative : ℝ → W} {a b : ℝ} (hab : a < b)
    (hforcingAC : AbsolutelyContinuousOnInterval forcing a b)
    (hrepresentativeContinuous : ContinuousOn representative (Set.Icc a b))
    (heq : forcing =ᵐ[volume.restrict (Set.Ioc a b)] fun t ↦ L (representative t)) :
    forcing a = L (representative a) := by
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at heq
  exact strongDual_eqOn_Icc_of_ae_eq hab.ne heq
    (continuousOn_Icc_of_absolutelyContinuousOnInterval hforcingAC hab.le)
    (L.continuous.comp_continuousOn hrepresentativeContinuous) ⟨le_rfl, hab.le⟩

/--
Select the jet tail whose remaining Sobolev order is the given reverse
index.  In particular, `Fin.last m` selects the original order-`m` jet.
-/
def iteratedTimeDerivative :
    {m : ℕ} → (F : SobolevTimeJet n m Omega t0 t1) → (r : Fin (m + 1)) →
      SobolevTimeJet n r.1 Omega t0 t1
  | 0, F, r => Fin.lastCases F (fun i ↦ Fin.elim0 i) r
  | m + 1, F, r =>
      Fin.lastCases F (fun i : Fin (m + 1) ↦ iteratedTimeDerivative F.timeDerivative i) r

/-- The reverse index `Fin.last m` takes no time derivatives: it returns the jet itself. -/
@[simp]
theorem iteratedTimeDerivative_last (F : SobolevTimeJet n m Omega t0 t1) :
    F.iteratedTimeDerivative (Fin.last m) = F := by
  cases m <;> exact Fin.lastCases_last

/--
Iterating at the index `r.castSucc` of a successor jet is the same as first
taking one time derivative and then iterating at `r`.  Together with
`iteratedTimeDerivative_last` this is the recursion that `Fin.lastCases`
arguments over the chain unfold.
-/
@[simp]
theorem iteratedTimeDerivative_castSucc
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (r : Fin (m + 1)) :
    F.iteratedTimeDerivative r.castSucc = F.timeDerivative.iteratedTimeDerivative r := by
  simp [iteratedTimeDerivative]

private theorem dirichletLoadTimeLp_eq_load_of_loweredRepresentative
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (hOmegaOpen : IsOpen Omega)
    (representative : ℝ → W^{m,2}(Omega))
    (hrepresentative : representative =ᵐ[volume.restrict (Set.Ioc t0 t1)]
      fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (F.head t)) :
    (dirichletLoadTimeLp hOmegaOpen F.head : ℝ → StrongDual ℝ (H¹₀(Omega)))
      =ᵐ[volume.restrict (Set.Ioc t0 t1)]
        fun t ↦ loadFunctional (n := n) (Ω := Omega)
          (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (representative t)) := by
  filter_upwards [dirichletLoadTimeLp_apply_ae hOmegaOpen F.head, hrepresentative] with
    t hload hrepresentative
  rw [hload, hrepresentative]
  simp only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]

private theorem forcing_eq_load_of_representative_at_initial
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (hOmegaOpen : IsOpen Omega) (ht : t0 < t1)
    (forcing : ℝ → StrongDual ℝ (H¹₀(Omega))) (representative : ℝ → W^{m,2}(Omega))
    (hrepresentativeContinuous : ContinuousOn representative (Set.Icc t0 t1))
    (hrepresentativeAE : representative =ᵐ[volume.restrict (Set.Ioc t0 t1)]
      fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (F.head t))
    (hforcingAC : AbsolutelyContinuousOnInterval forcing t0 t1)
    (hforcingRepresents : (dirichletLoadTimeLp hOmegaOpen F.head :
      ℝ → StrongDual ℝ (H¹₀(Omega))) =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing) :
    forcing t0 = loadFunctional (n := n) (Ω := Omega)
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (representative t0)) := by
  let L : W^{m,2}(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)) :=
    (loadFunctionalCLM (n := n) (Ω := Omega)).comp
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega))
  simpa only [L, ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply] using
    strongDual_mappedRepresentative_eq_at_initial L ht hforcingAC hrepresentativeContinuous
      (hforcingRepresents.symm.trans (by
        simpa only [L, ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply] using
          dirichletLoadTimeLp_eq_load_of_loweredRepresentative F hOmegaOpen representative
            hrepresentativeAE))

/--
An absolutely continuous Dirichlet-load representative takes the canonical
Lions-Magenes forcing trace at the initial time.

Thus differentiating a Galerkin trajectory uses Evans's compatibility
value, rather than a freely chosen value of an `Lp` representative at one
point.
-/
theorem initialValue_eq_dirichletLoadTrace
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (traces : InitialTraceData (F := F))
    (hOmegaOpen : IsOpen Omega) (ht : t0 < t1) (forcing : ℝ → StrongDual ℝ (H¹₀(Omega)))
    (hforcingAC : AbsolutelyContinuousOnInterval forcing t0 t1)
    (hforcingRepresents : (dirichletLoadTimeLp hOmegaOpen F.head :
      ℝ → StrongDual ℝ (H¹₀(Omega))) =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing) :
    forcing t0 = loadFunctional (n := n) (Ω := Omega)
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) traces.head) := by
  obtain ⟨representative, hrepresentativeContinuous, hrepresentativeAE, hrepresentativeInitial⟩ :=
    traces.head_isInitialTrace
  rw [← hrepresentativeInitial]
  exact forcing_eq_load_of_representative_at_initial F hOmegaOpen ht forcing representative
    hrepresentativeContinuous hrepresentativeAE hforcingAC hforcingRepresents

/--
Map one successor step of a Sobolev forcing jet into the Dirichlet dual
forcing used by the Galerkin wave equation.

The returned representative is absolutely continuous, agrees almost
everywhere with the original dual-valued Bochner forcing, and has a
representative of the next jet entry as its strong derivative almost
everywhere. The construction concerns the forcing data alone.
-/
theorem exists_dirichletLoadRepresentatives
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (hOmegaOpen : IsOpen Omega) (ht : t0 < t1) :
    ∃ forcing forcingDot : ℝ → StrongDual ℝ (H¹₀(Omega)),
      AbsolutelyContinuousOnInterval forcing t0 t1 ∧
      (dirichletLoadTimeLp hOmegaOpen F.head : ℝ → StrongDual ℝ (H¹₀(Omega)))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing ∧
      (dirichletLoadTimeLp hOmegaOpen F.timeDerivative.head : ℝ → StrongDual ℝ (H¹₀(Omega)))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcingDot ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), HasDerivAt forcing (forcingDot t) t := by
  cases F with
  | mk head derivatives =>
    cases derivatives with
    | succ _ df hderiv tail =>
      let L : W^{m,2}(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)) :=
        (loadFunctionalCLM (n := n) (Ω := Omega)).comp
          (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega))
      obtain ⟨forcing, hAC, hforcing, hstrong⟩ := exists_clmRepresentative_of_weakTimeDerivative
        (Y := StrongDual ℝ (H¹₀(Omega))) L head df hderiv ht
      refine ⟨forcing, fun t ↦ L (df t), hAC, ?_, ?_, hstrong⟩
      · filter_upwards [dirichletLoadTimeLp_apply_ae hOmegaOpen head, hforcing] with
          t hload hforcing
        rw [hload, hforcing]
        simp only [L, ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply,
          wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
      · change (dirichletLoadTimeLp hOmegaOpen df : ℝ → StrongDual ℝ (H¹₀(Omega)))
          =ᵐ[volume.restrict (Set.Ioc t0 t1)] _
        filter_upwards [dirichletLoadTimeLp_apply_ae hOmegaOpen df] with t hload
        rw [hload]
        simp only [L, ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply]

/--
Choose one coherent finite family of dual-valued Dirichlet forcing
representatives from an order-`m` Sobolev time jet.

At reverse index `r`, the chosen function represents the Dirichlet load of
the corresponding iterated jet tail.  For every adjacent pair, the
higher-index function is absolutely continuous and its strong derivative is
the lower-index function almost everywhere.
-/
theorem exists_dirichletLoadForcingChain
    (F : SobolevTimeJet n m Omega t0 t1) (hOmegaOpen : IsOpen Omega) (ht : t0 < t1) :
    ∃ forcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)),
      (∀ r : Fin (m + 1),
        (dirichletLoadTimeLp hOmegaOpen (F.iteratedTimeDerivative r).head :
            ℝ → StrongDual ℝ (H¹₀(Omega)))
          =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing r) ∧
      ∀ r : Fin m,
        AbsolutelyContinuousOnInterval (forcing r.succ) t0 t1 ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
          HasDerivAt (forcing r.succ) (forcing r.castSucc t) t := by
  induction m with
  | zero =>
    exact ⟨fun _ ↦ dirichletLoadTimeLp hOmegaOpen F.head,
      fun r ↦ Fin.lastCases .rfl (fun i ↦ i.elim0) r, fun r ↦ r.elim0⟩
  | succ m ih =>
    obtain ⟨tailForcing, htailRepresents, htailAdjacent⟩ := ih F.timeDerivative
    obtain ⟨originalForcing, derivativeForcing, hOriginalAC, hOriginalRepresents,
      hDerivativeRepresents, hOriginalDerivative⟩ :=
      F.exists_dirichletLoadRepresentatives hOmegaOpen ht
    have hDerivativeTail := hDerivativeRepresents.symm.trans
      (by simpa only [iteratedTimeDerivative_last] using htailRepresents (Fin.last m))
    refine ⟨Fin.lastCases originalForcing tailForcing, fun r ↦ ?_, fun r ↦ ?_⟩
    · refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simpa only [Fin.lastCases_last, iteratedTimeDerivative_last] using hOriginalRepresents
      · simpa only [Fin.lastCases_castSucc, iteratedTimeDerivative_castSucc] using htailRepresents s
    · refine Fin.lastCases ⟨by simpa only [Fin.succ_last, Fin.lastCases_last] using hOriginalAC,
        ?_⟩ (fun s ↦ ?_) r
      · filter_upwards [hOriginalDerivative, hDerivativeTail] with t hderiv htail
        simpa only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc, htail] using hderiv
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using htailAdjacent s

/--
Every member of a Dirichlet-load forcing chain is the pivot embedding of
the base coordinate of the corresponding iterated Sobolev jet, almost
everywhere in time.
-/
theorem forcing_eq_pivotToDual_baseCoordinateTimeLp (F : SobolevTimeJet n m Omega t0 t1)
    (hOmegaOpen : IsOpen Omega) (forcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)))
    (hforcingRepresents : ∀ r : Fin (m + 1), (dirichletLoadTimeLp hOmegaOpen
      (F.iteratedTimeDerivative r).head : ℝ → StrongDual ℝ (H¹₀(Omega)))
      =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing r) :
    ∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      forcing r t = (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).pivotToDual
        (baseCoordinateTimeLp (F.iteratedTimeDerivative r).head t) := by
  intro r
  filter_upwards [hforcingRepresents r,
    dirichletLoadTimeLp_apply_ae hOmegaOpen (F.iteratedTimeDerivative r).head,
    baseCoordinateTimeLp_apply_ae (F.iteratedTimeDerivative r).head] with t hforcing hload hbase
  rw [← hforcing, hload, hbase]
  rfl

/--
Every chosen Dirichlet-load representative is integrable on the closed time
interval.  This is the forcing hypothesis required by the finite-dimensional
Carathéodory construction.

The canonical load belongs to Bochner `L²` on `(t0,t1]`, hence to `L¹` on
the finite interval.  Almost-everywhere equality transfers integrability to
the chosen representative, and changing `(t0,t1]` to `[t0,t1]` only changes
a null set.
-/
theorem integrableOn_dirichletLoadForcing (F : SobolevTimeJet n m Omega t0 t1)
    (hOmegaOpen : IsOpen Omega) (ht : t0 ≤ t1)
    (forcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)))
    (hforcingRepresents : ∀ r : Fin (m + 1), (dirichletLoadTimeLp hOmegaOpen
      (F.iteratedTimeDerivative r).head : ℝ → StrongDual ℝ (H¹₀(Omega)))
      =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing r) :
    ∀ r : Fin (m + 1), IntegrableOn (forcing r) (Set.Icc t0 t1) volume := by
  intro r
  have hforcing : Integrable (forcing r) (volume.restrict (Set.Ioc t0 t1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (PDE.Analysis.Evolution.intervalIntegrable_coeFn_L2_restrict_Ioc
        (dirichletLoadTimeLp hOmegaOpen (F.iteratedTimeDerivative r).head) ht)).congr
      (hforcingRepresents r)
  rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hforcing

/--
The squared pivot norm of every iterated Sobolev forcing is interval
integrable.  This is the analytic input for the common finite-family
forcing budget.
-/
theorem intervalIntegrable_norm_sq_baseCoordinateTimeLp
    (F : SobolevTimeJet n m Omega t0 t1) (ht : t0 ≤ t1) :
    ∀ r : Fin (m + 1), IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) *
      ‖baseCoordinateTimeLp (F.iteratedTimeDerivative r).head t‖ ^ 2) volume t0 t1 := by
  intro r
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  exact ((MeasureTheory.Lp.memLp (baseCoordinateTimeLp
    (F.iteratedTimeDerivative r).head)).integrable_norm_pow (by norm_num)).const_mul (1 / 2 : ℝ)

end SobolevTimeJet

end Hyperbolic.HigherRegularity
