/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import PDE.Analysis.Evolution.LionsMagenes.Basic.Continuity
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval

/-!
# Initial traces of Sobolev time jets

A successor step in a Sobolev time jet is weakly differentiable after lowering
one spatial order. Lions-Magenes endpoint regularity therefore supplies an
absolutely continuous representative and a canonical value at the initial
time. `InitialTraceData` records these values recursively for every
nonterminal member of a jet.

These traces are the values `∂ₜᵏ f(0) ∈ H^{m-1-k}` that enter Evans's
compatibility recurrence for higher regularity of the wave equation (Evans,
PDE, §7.2.3, Theorem 6).  Because an `L²_t` class has no value at a point,
the trace is defined through a continuous representative on `[t0, t1]`, and
`head_eq_of_continuousRepresentative` shows that any such representative gives
the same value.

## Main results

* `exists_absolutelyContinuousRepresentative_of_weakTimeDerivative`: an
  `L²_t H^{m+1}` trajectory with weak time derivative in `L²_t H^m` has an
  absolutely continuous `H^m`-valued representative with that derivative.
* `IsInitialTrace`, `exists_initialTrace_of_weakTimeDerivative`: the
  canonical value at `t0`.
* `InitialTraceData`, `InitialTraceData.ofJet`: the traces of every
  nonterminal member of a jet, built by recursion on the jet.
* `InitialTraceData.forcingAtZero`: the trace of `∂ₜᵏ f` as an `L²(Omega)`
  element, the form in which the compatibility values are compared.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, the Remark after Theorem 6, equation (65),
  and §5.9.2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
One weakly differentiable step of a Sobolev time jet has an absolutely
continuous representative in the lower spatial Sobolev space.

The representative agrees almost everywhere with the lowered head and has
the next jet entry as its strong derivative almost everywhere.
-/
theorem exists_absolutelyContinuousRepresentative_of_weakTimeDerivative
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (df : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (hderiv : PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
      (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega))) (lowerOrderTimeLp f)
      (PDE.Analysis.Evolution.rieszToDualLp df))
    (ht : t0 < t1) :
    ∃ representative : ℝ → W^{m,2}(Omega), AbsolutelyContinuousOnInterval representative t0 t1 ∧
      representative =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        (fun t ↦
          lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), HasDerivAt representative (df t) t := by
  let X := W^{m,2}(Omega)
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let T := GelfandTriple.identity X
  let Eopen := Classical.choice
    (hderiv.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen ht)
  let E := Classical.choice <| Eopen.toContinuousPivotEvolutionOn T ht
    (Lp.memLp (lowerOrderTimeLp f)) (Lp.memLp (rieszToDualLp df))
  let dfRep : ℝ → X := fun t ↦ (InnerProductSpace.toDual ℝ X).symm (rieszToDualLp df t)
  have hdf : dfRep =ᵐ[volume.restrict (Set.Ioc t0 t1)] fun t ↦ df t := by
    filter_upwards [rieszToDualLp_apply_ae df] with t hdf
    simp only [dfRep, hdf]
    exact (InnerProductSpace.toDual ℝ X).symm_apply_apply (df t)
  have hdfIntegrable : IntervalIntegrable dfRep volume t0 t1 :=
    (intervalIntegrable_coeFn_L2_restrict_Ioc df ht.le).congr_ae
      (by simpa only [Set.uIoc_of_le ht.le] using hdf.symm)
  have hrep : ∀ t ∈ Set.uIcc t0 t1, RepresentsPivotDerivative T (rieszToDualLp df t) (dfRep t) :=
    fun t _ v ↦ InnerProductSpace.toDual_symm_apply.symm
  have hE := E.ae_eq_inclusion
  rw [Set.uIcc_of_le ht.le] at hE
  refine ⟨E.representative,
    E.integratedDerivative.absolutelyContinuousOnInterval_of_pivotDerivative dfRep hdfIntegrable
      hrep, Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
        hE) (lowerOrderTimeLp_apply_ae f), ?_⟩
  filter_upwards [E.integratedDerivative.ae_hasDerivAt_of_pivotDerivative ht dfRep hdfIntegrable
    hrep, hdf] with t hstrong hdf
  simpa only [hdf] using hstrong

/--
Continuous linear maps preserve the absolutely continuous representative
and its almost-everywhere strong derivative.
-/
theorem exists_clmRepresentative_of_weakTimeDerivative {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (L : W^{m,2}(Omega) →L[ℝ] Y)
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (df : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (hderiv : PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
      (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega))) (lowerOrderTimeLp f)
      (PDE.Analysis.Evolution.rieszToDualLp df))
    (ht : t0 < t1) :
    ∃ representative : ℝ → Y, AbsolutelyContinuousOnInterval representative t0 t1 ∧
      representative =ᵐ[volume.restrict (Set.Ioc t0 t1)]
        (fun t ↦
          L (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t))) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), HasDerivAt representative (L (df t)) t := by
  obtain ⟨representative, hAC, hrepresentative, hstrong⟩ :=
    exists_absolutelyContinuousRepresentative_of_weakTimeDerivative f df hderiv ht
  exact ⟨L ∘ representative, L.lipschitzWith.comp_absolutelyContinuousOnInterval hAC,
    hrepresentative.mono fun t ht ↦ congrArg L ht,
    hstrong.mono fun t ht ↦ L.hasFDerivAt.comp_hasDerivAt t ht⟩

/--
`x` is the initial trace at `t0` of a Bochner trajectory `f` on `(t0,t1]`
when `f` has a representative continuous on `[t0,t1]` whose value at `t0`
is `x`.
-/
def IsInitialTrace {X : Type*} [TopologicalSpace X] (t0 t1 : ℝ) (f : ℝ → X) (x : X) : Prop :=
  ∃ fContinuous : ℝ → X,
    ContinuousOn fContinuous (Set.Icc t0 t1) ∧ fContinuous =ᵐ[(volume.restrict (Set.Ioc t0 t1))] f ∧
      fContinuous t0 = x

/--
One step of a Sobolev time jet has a canonical initial trace in the lower
spatial Sobolev space.
-/
theorem exists_initialTrace_of_weakTimeDerivative
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (df : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (hderiv : PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
      (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega))) (lowerOrderTimeLp f)
      (PDE.Analysis.Evolution.rieszToDualLp df))
    (ht : t0 < t1) :
    ∃ initial : W^{m,2}(Omega), IsInitialTrace t0 t1
      (fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t)) initial := by
  obtain ⟨representative, hAC, hae, _hderiv⟩ :=
    exists_absolutelyContinuousRepresentative_of_weakTimeDerivative f df hderiv ht
  exact ⟨representative t0, representative,
    by simpa only [Set.uIcc_of_le ht.le] using hAC.continuousOn, hae, rfl⟩

namespace SobolevTimeJet

/--
A successor Sobolev time jet automatically bounds its head after lowering
one spatial order.
-/
theorem exists_lowerOrder_head_bound (F : SobolevTimeJet n (m + 1) Omega t0 t1) (ht : t0 < t1) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
      ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (F.head t)‖ ≤ C := by
  cases F with
  | mk head derivatives =>
    cases derivatives with
    | succ _ df hderiv _ =>
      obtain ⟨_, g, hg, hae, -⟩ := exists_initialTrace_of_weakTimeDerivative head df hderiv ht
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
      refine ⟨C, ?_⟩
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t heq htIoc
      exact heq ▸ hC t (Set.Ioc_subset_Icc_self htIoc)

end SobolevTimeJet

/--
Endpoint traces for every nonterminal member of a Sobolev time jet.

For an order-`m` forcing jet this stores the traces of
`f, f_t, ..., ∂ₜ^{m-1}f` in `H^{m-1}, H^{m-2}, ..., H^0`, respectively.
-/
inductive InitialTraceData : {m : ℕ} → (F : SobolevTimeJet n m Omega t0 t1) → Type
  | zero (f : Lp (W^{0,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
      InitialTraceData (F := SobolevTimeJet.zero f)
  | succ {m : ℕ} (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
      (dF : SobolevTimeJet n m Omega t0 t1)
      (hderiv : PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
          (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega)))
          (lowerOrderTimeLp f) (PDE.Analysis.Evolution.rieszToDualLp dF.head))
      (initial : W^{m,2}(Omega))
      (isTrace : IsInitialTrace t0 t1
          (fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t)) initial)
      (tail : InitialTraceData (F := dF)) :
      InitialTraceData (F := SobolevTimeJet.succ f dF hderiv)

namespace InitialTraceData

/--
Construct every forcing trace required by Evans's compatibility recurrence
from the verified Sobolev time jet.
-/
noncomputable def ofJet (F : SobolevTimeJet n m Omega t0 t1) (ht : t0 < t1) :
    InitialTraceData (F := F) := by
  cases F with
  | mk head derivatives =>
    induction derivatives with
    | zero f => exact .zero f
    | @succ m f df hderiv tail ih =>
      have h := exists_initialTrace_of_weakTimeDerivative f df hderiv ht
      exact .succ f ⟨df, tail⟩ hderiv h.choose h.choose_spec ih

/-- Take the endpoint traces belonging to the time-differentiated forcing jet. -/
def timeDerivative {F : SobolevTimeJet n (m + 1) Omega t0 t1} (T : InitialTraceData (F := F)) :
    InitialTraceData (F := F.timeDerivative) := by
  cases T with
  | succ _ _ _ _ _ tail => exact tail

/--
Automatically constructed traces commute with taking the time-derivative
tail.
-/
@[simp]
theorem ofJet_timeDerivative (F : SobolevTimeJet n (m + 1) Omega t0 t1) (ht : t0 < t1) :
    (ofJet F ht).timeDerivative = ofJet F.timeDerivative ht := by
  cases F with
  | mk head derivatives => cases derivatives with
    | succ => rfl

/-- The leading forcing trace with its exact Sobolev regularity. -/
def head {F : SobolevTimeJet n (m + 1) Omega t0 t1} (T : InitialTraceData (F := F)) :
    W^{m,2}(Omega) := by
  cases T with
  | succ _ _ _ initial _ _ => exact initial

/-- The leading stored value is witnessed by its continuous representative. -/
theorem head_isInitialTrace {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    (T : InitialTraceData (F := F)) :
    IsInitialTrace t0 t1 (fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m)
      (F.head t)) T.head := by
  cases T with
  | succ _ _ _ _ isTrace _ => exact isTrace

/--
Every continuous representative of the lowered jet head takes the stored
Evans trace as its initial value.
-/
theorem head_eq_of_continuousRepresentative {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    (T : InitialTraceData (F := F)) (representative : ℝ → W^{m,2}(Omega))
    (hcontinuous : ContinuousOn representative (Set.Icc t0 t1))
    (hae : representative =ᵐ[volume.restrict (Set.Ioc t0 t1)] fun t ↦
      lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (F.head t))
    (ht : t0 < t1) :
    representative t0 = T.head := by
  cases T with
  | succ f dF hderiv initial isTrace tail =>
    obtain ⟨g, hg, hgae, hg0⟩ := isTrace
    have haeIcc := hae.trans hgae.symm
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at haeIcc
    exact (Measure.eqOn_Icc_of_ae_eq volume ht.ne haeIcc hcontinuous hg ⟨le_rfl, ht.le⟩).trans hg0

/-- Initial forcing traces as underlying `L²(Omega)` representatives. -/
def baseList :
    {m : ℕ} → {F : SobolevTimeJet n m Omega t0 t1} → InitialTraceData (F := F) →
      List (DerivLp n 2 Omega)
  | 0, _, .zero _ => []
  | _ + 1, _, .succ _ _ _ initial _ tail =>
      wkpBaseCoordinateCLM (n := n) (p := 2) (Ω := Omega) initial :: baseList tail

/-- An order-`m` jet has exactly `m` nonterminal members, hence `m` stored traces. -/
@[simp]
theorem length_baseList {F : SobolevTimeJet n m Omega t0 t1} (T : InitialTraceData (F := F)) :
    T.baseList.length = m := by
  induction T with
  | zero => rfl
  | succ _ _ _ _ _ tail ih => exact congrArg Nat.succ ih

/-- The initial trace of `∂ₜᵏf`, represented in `L²(Omega)`. -/
def forcingAtZero {F : SobolevTimeJet n m Omega t0 t1} (T : InitialTraceData (F := F)) (k : Fin m) :
    DerivLp n 2 Omega :=
  T.baseList.get ⟨k.1, by simpa only [length_baseList] using k.2⟩

/-- The `L²` trace of the undifferentiated forcing is the base coordinate of the head trace. -/
@[simp]
theorem forcingAtZero_zero {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    (T : InitialTraceData (F := F)) :
    T.forcingAtZero 0 = wkpBaseCoordinateCLM (n := n) (p := 2) (Ω := Omega) T.head := by
  cases T with
  | succ => rfl

/--
The `k`-th trace of the time-differentiated jet is the `(k+1)`-st trace of the
original jet: differentiating once shifts the list of initial traces by one.
-/
@[simp]
theorem forcingAtZero_timeDerivative {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    (T : InitialTraceData (F := F)) (k : Fin m) :
    T.timeDerivative.forcingAtZero k = T.forcingAtZero ⟨k.1 + 1, by omega⟩ := by
  cases T with
  | succ => rfl

end InitialTraceData

end Hyperbolic.HigherRegularity
