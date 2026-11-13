/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Prod.SliceDerivative
public import PDE.Common.Euclidean.SpaceTime
public import PDE.FDeriv.PartialDeriv

/-!
# Calculus for Euclidean spacetime slices

LeanPDE stores a spacetime point of `ℝ^(n + 1)` with time in coordinate `0` and space in the
remaining `n` coordinates (`timeSpaceCons t x`), and also works with the product convention
`ℝ^n × ℝ` through `joinSpaceTime` and `spaceTimeUncurry`. Evolution equations are most naturally
stated slice by slice: `∂ₜ u` is the derivative of the time trace `s ↦ u (timeSpaceCons s x)`, and
spatial operators act on the fixed-time slice `y ↦ u (timeSpaceCons t y)`. The chain-rule
identities below identify those slice derivatives with coordinate derivatives of the joint field,
so that a hypothesis on the spacetime field can be used in either picture.

Everything here follows from the chain rule for `fderiv` and the symmetry of the second
derivative of a `C²` map.

## Main results

* `contDiff_comp_joinSpaceTime_iff`, `contDiff_spaceTimeUncurry_iff`: smoothness is the same in
  the canonical and product conventions.
* `partialDeriv_prod_spaceSlice`: a coordinate derivative of a fixed-time slice is the joint
  derivative in the direction `(eᵢ, 0)`. The time analogue `deriv_prod_timeSlice`, with
  direction `(0, 1)`, comes from the imported `PDE.Analysis.Calculus.Prod.SliceDerivative`.
* `contDiff_partialDeriv_timeTrace`: a first-order spatial slice derivative of a `C^(m+1)`
  field is `C^m` in time; `contDiff_secondPartialDeriv_timeTrace` needs `C^(m+2)` for a
  second-order one.
* `deriv_partialDeriv_timeSlice_comm`, `deriv_secondPartialDeriv_timeSlice_comm`: for a global
  `C²` (respectively `C³`) field, time differentiation of a trace commutes with one (two) spatial
  coordinate derivatives.
* `partialDeriv_timeSpaceCons_spatial`, `partialDeriv_timeSpaceCons_eq_deriv`,
  `fderiv_joinSpaceTime_time`, `fderiv_joinSpaceTime_spatial`: the coordinate derivatives
  `∂₀` and `∂_{i.succ}` of a canonical spacetime field are the time-trace derivative and the
  spatial slice derivative `∂ᵢ`.
* `differentiableAt_time_slice_of_contDiffOn`: joint `C¹` regularity on an open time interval
  already gives differentiability of every time trace, so classical-solution predicates need not
  record it separately.
* `exists_norm_le_on_timeSpaceCylinder`: a continuous field is bounded on every compact cylinder
  `Icc a b × closedBall c r`.
-/

@[expose] public section

noncomputable section

open PDE (SpaceTime partialDeriv)
open PDE.Common

namespace PDE.Common

/-- Smoothness is invariant under the explicit conversion from canonical
spacetime to the `(x, t)` product convention. -/
theorem contDiff_comp_joinSpaceTime_iff
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ∞} (u : SpaceTime n → E) :
    ContDiff ℝ m (fun p : ℝ^n × ℝ ↦ u (joinSpaceTime p)) ↔
      ContDiff ℝ m u := by
  constructor
  · intro hu
    rw [show u =
      (fun p : ℝ^n × ℝ ↦ u (joinSpaceTime p)) ∘
          spaceTimeContinuousLinearEquiv n by
      funext xt
      simp]
    exact hu.comp (spaceTimeContinuousLinearEquiv n).contDiff
  · intro hu
    exact hu.comp (spaceTimeContinuousLinearEquiv n).symm.contDiff

/-- Joint smoothness of a curried `u x t` field is equivalent to smoothness
after encoding it on canonical Euclidean spacetime. -/
theorem contDiff_spaceTimeUncurry_iff
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ∞} (u : ℝ^n → ℝ → E) :
    ContDiff ℝ m (spaceTimeUncurry u) ↔
      ContDiff ℝ m (fun p : ℝ^n × ℝ ↦ u p.1 p.2) := by
  simpa [spaceTimeUncurry, splitSpaceTime, joinSpaceTime] using
    (contDiff_comp_joinSpaceTime_iff (m := m) (spaceTimeUncurry u)).symm

/-- The fixed-time embedding `x ↦ (t, x)` has derivative `x ↦ (0, x)`. -/
theorem hasFDerivAt_timeSpaceCons_spatial (n : ℕ) (t : ℝ) (x : ℝ^n) :
    HasFDerivAt (timeSpaceCons (n := n) t) (embedWithTimeZeroCLM n) x := by
  have hrepr :
      timeSpaceCons (n := n) t =
        fun y ↦ timeSpaceCons (n := n) t 0 + embedWithTimeZeroCLM n y := by
    funext y
    ext i
    cases i using Fin.cases <;> simp
  rw [hrepr]
  exact (embedWithTimeZeroCLM n).hasFDerivAt.const_add
    (timeSpaceCons (n := n) t 0)

/-- The fixed-time embedding `x ↦ (t, x)` is smooth. -/
theorem contDiff_timeSpaceCons_spatial
    (n : ℕ) (t : ℝ) {m : ℕ∞} :
    ContDiff ℝ m (timeSpaceCons (n := n) t) := by
  have hrepr :
      timeSpaceCons (n := n) t =
        fun x ↦
          timeSpaceCons (n := n) t 0 + embedWithTimeZeroCLM n x := by
    funext x
    ext i
    cases i using Fin.cases <;> simp
  rw [hrepr]
  exact contDiff_const.add (embedWithTimeZeroCLM n).contDiff

/-- The joint spacetime assembly map `(t, x) ↦ (t, x)` is smooth. -/
theorem contDiff_timeSpaceCons_uncurry
    (n : ℕ) {m : ℕ∞} :
    ContDiff ℝ m
      (fun p : ℝ × ℝ^n ↦ timeSpaceCons (n := n) p.1 p.2) := by
  let e₀ : ℝ^(n + 1) :=
    EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have hrepr :
      (fun p : ℝ × ℝ^n ↦ timeSpaceCons (n := n) p.1 p.2) =
        fun p ↦ p.1 • e₀ + embedWithTimeZeroCLM n p.2 := by
    funext p
    ext i
    cases i using Fin.cases <;> simp [e₀]
  rw [hrepr]
  exact (contDiff_fst.smul contDiff_const).add
    ((embedWithTimeZeroCLM n).contDiff.comp contDiff_snd)

/-- A continuous spacetime field is uniformly bounded on every compact
time-space cylinder `Icc a b × closedBall c r`. -/
theorem exists_norm_le_on_timeSpaceCylinder
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : ℝ^(n + 1) → E) (hf : Continuous f)
    (a b : ℝ) (c : ℝ^n) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.Icc a b, ∀ x ∈ Metric.closedBall c r,
        ‖f (timeSpaceCons (n := n) t x)‖ ≤ C := by
  have hcontinuous :
      Continuous
        (fun p : ℝ × ℝ^n ↦
          f (timeSpaceCons (n := n) p.1 p.2)) :=
    hf.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall c r))
      |>.exists_bound_of_continuousOn hcontinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

/-- The spatial embedding sends a spatial basis vector to the corresponding
spacetime basis vector. -/
@[simp]
theorem embedWithTimeZeroCLM_single_one (n : ℕ) (i : Fin n) :
    embedWithTimeZeroCLM n (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single i.succ (1 : ℝ) := by
  ext j
  cases j using Fin.cases <;> simp

/-- The curve `t ↦ (t, x)` has velocity equal to the time basis vector. -/
theorem hasDerivAt_timeSpaceCons_time (n : ℕ) (t : ℝ) (x : ℝ^n) :
    HasDerivAt (fun s ↦ timeSpaceCons (n := n) s x)
      (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) t := by
  have hline :
      (fun s ↦ timeSpaceCons (n := n) s x) =
        coordinateLine (0 : Fin (n + 1)) (timeSpaceCons t x) := by
    funext s
    ext i
    cases i using Fin.cases <;>
      simp [coordinateLine]
  rw [hline]
  exact hasDerivAt_coordinateLine 0 (timeSpaceCons t x) t

end PDE.Common

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- A coordinate derivative of a fixed-time spatial slice is the derivative
of the joint spacetime field in the corresponding spatial direction. -/
theorem partialDeriv_prod_spaceSlice
    (i : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x, t)) :
    (∂[i] (fun y ↦ f (y, t))) x =
      fderiv ℝ f (x, t)
        (EuclideanSpace.single i (1 : ℝ), 0) := by
  simpa only [partialDeriv] using
    fderiv_prod_firstSlice f x (EuclideanSpace.single i (1 : ℝ)) t hf

/-- A spatial derivative of a jointly smooth spacetime field, evaluated at
the varying spacetime point, has one fewer derivative. -/
theorem contDiff_partialDeriv_prod_spaceSlice
    {m : ℕ} (i : Fin n) (f : ℝ^n × ℝ → E)
    (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m
      (fun xt : ℝ^n × ℝ ↦
        (∂[i] (fun y ↦ f (y, xt.2))) xt.1) := by
  simpa only [partialDeriv] using
    contDiff_fderiv_prod_firstSlice (m := m) hf
      (EuclideanSpace.single i (1 : ℝ))

/-- A spatial derivative evaluated at a fixed point inherits one fewer
derivative as a function of time. -/
theorem contDiff_partialDeriv_timeTrace
    {m : ℕ} (i : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n)
    (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m
      (fun t ↦ (∂[i] (fun y ↦ f (y, t))) x) := by
  have hpath : ContDiff ℝ m (fun t : ℝ ↦ (x, t)) :=
    contDiff_const.prodMk contDiff_id
  exact (contDiff_partialDeriv_prod_spaceSlice i f hf).comp hpath

/-- Two spatial derivatives evaluated at a fixed point inherit two fewer
derivatives as a function of time. -/
theorem contDiff_secondPartialDeriv_timeTrace
    {m : ℕ} (i j : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n)
    (hf : ContDiff ℝ (m + 2) f) :
    ContDiff ℝ m
      (fun t ↦
        (∂[i] (fun y ↦ (∂[j] (fun z ↦ f (z, t))) y)) x) := by
  let ej : ℝ^n := EuclideanSpace.single j (1 : ℝ)
  let spaceDerivative : ℝ^n × ℝ → E :=
    fun q ↦ fderiv ℝ f q (ej, 0)
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hspace :
      (fun q : ℝ^n × ℝ ↦
        (∂[j] (fun z ↦ f (z, q.2))) q.1) =
        spaceDerivative := by
    funext q
    exact partialDeriv_prod_spaceSlice j f q.1 q.2 (hfDiff q)
  have hspaceContDiff : ContDiff ℝ (m + 1) spaceDerivative :=
    (hf.fderiv_right (m := m + 1) (n := m + 2)
      (by norm_num [add_assoc])).clm_apply contDiff_const
  rw [show
      (fun t ↦
        (∂[i] (fun y ↦ (∂[j] (fun z ↦ f (z, t))) y)) x) =
        fun t ↦ (∂[i] (fun y ↦ spaceDerivative (y, t))) x by
    funext t
    congr 1
    funext y
    exact congrFun hspace (y, t)]
  exact contDiff_partialDeriv_timeTrace i spaceDerivative x hspaceContDiff

/-- For a globally `C²` spacetime field, one spatial derivative commutes
with differentiation of a fixed-space time trace. -/
theorem deriv_partialDeriv_timeSlice_comm
    (i : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n) (t : ℝ)
    (hf : ContDiff ℝ 2 f) :
    deriv (fun s ↦ (∂[i] (fun y ↦ f (y, s))) x) t =
      (∂[i] (fun y ↦ deriv (fun s ↦ f (y, s)) t)) x := by
  simpa only [partialDeriv] using
    (fderiv_deriv_prod_comm hf x (EuclideanSpace.single i (1 : ℝ)) t).symm

/-- For a globally `C³` spacetime field, two spatial derivatives commute
with differentiation of a fixed-space time trace. -/
theorem deriv_secondPartialDeriv_timeSlice_comm
    (i j : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n) (t : ℝ)
    (hf : ContDiff ℝ 3 f) :
    deriv
        (fun s ↦
          (∂[i] (fun y ↦ (∂[j] (fun z ↦ f (z, s))) y)) x) t =
      (∂[i] (fun y ↦
          (∂[j] (fun z ↦ deriv (fun s ↦ f (z, s)) t)) y)) x := by
  let ej : ℝ^n := EuclideanSpace.single j (1 : ℝ)
  let spaceDerivative : ℝ^n × ℝ → E :=
    fun q ↦ fderiv ℝ f q (ej, 0)
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hspace :
      (fun q : ℝ^n × ℝ ↦
        (∂[j] (fun z ↦ f (z, q.2))) q.1) =
        spaceDerivative := by
    funext q
    exact partialDeriv_prod_spaceSlice j f q.1 q.2 (hfDiff q)
  have hspaceContDiff : ContDiff ℝ 2 spaceDerivative := by
    exact (hf.fderiv_right (m := 2) (n := 3) (by norm_num)).clm_apply
      contDiff_const
  rw [show
      (fun s ↦
        (∂[i] (fun y ↦ (∂[j] (fun z ↦ f (z, s))) y)) x) =
        fun s ↦ (∂[i] (fun y ↦ spaceDerivative (y, s))) x by
    funext s
    congr 1
    funext y
    exact congrFun hspace (y, s)]
  rw [deriv_partialDeriv_timeSlice_comm i spaceDerivative x t
    hspaceContDiff]
  congr 1
  funext y
  rw [show
      (fun s ↦ spaceDerivative (y, s)) =
        fun s ↦ (∂[j] (fun z ↦ f (z, s))) y by
    funext s
    exact (congrFun hspace (y, s)).symm]
  exact deriv_partialDeriv_timeSlice_comm j f y t
    (hf.of_le (by norm_num))

/-- Joint `C¹` regularity on an open spacetime cylinder implies differentiability of every
fixed-space time curve.

So classical solution predicates need not assume time differentiability separately: it follows
from joint spacetime regularity. -/
theorem differentiableAt_time_slice_of_contDiffOn
    {I : Set ℝ} (hI : IsOpen I) (u : ℝ^n × ℝ → E)
    (hu : ContDiffOn ℝ 1 u (Set.univ ×ˢ I))
    (x : ℝ^n) {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ u (x, s)) t := by
  have hu_at : ContDiffAt ℝ 1 u (x, t) :=
    (hu (x, t) ⟨Set.mem_univ x, ht⟩).contDiffAt
      ((isOpen_univ.prod hI).mem_nhds ⟨Set.mem_univ x, ht⟩)
  exact (hu_at.differentiableAt (by norm_num)).comp t (by fun_prop)

/-- A spatial coordinate derivative of a fixed-time slice is the corresponding
spacetime coordinate derivative. -/
theorem partialDeriv_timeSpaceCons_spatial
    (i : Fin n) (u : ℝ^(n + 1) → E) (t : ℝ) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    (∂[i] (fun y ↦ u (timeSpaceCons t y))) x =
      (∂[i.succ] u) (timeSpaceCons t x) := by
  have hcomp := hu.hasFDerivAt.comp x
    (PDE.Common.hasFDerivAt_timeSpaceCons_spatial n t x)
  unfold partialDeriv
  change
    fderiv ℝ (u ∘ timeSpaceCons t) x (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ u (timeSpaceCons t x) (EuclideanSpace.single i.succ (1 : ℝ))
  rw [hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply,
    PDE.Common.embedWithTimeZeroCLM_single_one]

/-- The derivative along a fixed spatial point is the time-coordinate
derivative of the spacetime field. -/
theorem hasDerivAt_timeSpaceCons
    (u : ℝ^(n + 1) → E) (t : ℝ) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    HasDerivAt (fun s ↦ u (timeSpaceCons s x))
      ((∂[0] u) (timeSpaceCons t x)) t := by
  simpa [Function.comp_def, partialDeriv] using
    hu.hasFDerivAt.comp_hasDerivAt t
      (PDE.Common.hasDerivAt_timeSpaceCons_time n t x)

/-- Applying the derivative of a spacetime pullback in the time direction
recovers the zeroth coordinate derivative of the original field. -/
theorem fderiv_timeSpaceCons_time
    (u : ℝ^(n + 1) → E) (t : ℝ) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    fderiv ℝ
        (fun p : ℝ × ℝ^n ↦ u (timeSpaceCons (n := n) p.1 p.2))
        (t, x) ((1 : ℝ), (0 : ℝ^n)) =
      (∂[0] u) (timeSpaceCons t x) := by
  let U : ℝ × ℝ^n → E := fun p ↦
    u (timeSpaceCons (n := n) p.1 p.2)
  have hcons :
      DifferentiableAt ℝ
        (fun p : ℝ × ℝ^n ↦ timeSpaceCons (n := n) p.1 p.2) (t, x) :=
    ((PDE.Common.contDiff_timeSpaceCons_uncurry n (m := 1)).differentiable
      one_ne_zero).differentiableAt
  have hU : DifferentiableAt ℝ U (t, x) :=
    hu.comp (t, x) hcons
  have hpath :
      HasDerivAt (fun s : ℝ ↦ (s, x))
        ((1 : ℝ), (0 : ℝ^n)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hleft :
      HasDerivAt (fun s ↦ u (timeSpaceCons (n := n) s x))
        (fderiv ℝ U (t, x) ((1 : ℝ), (0 : ℝ^n))) t := by
    simpa [U, Function.comp_def] using
      hU.hasFDerivAt.comp_hasDerivAt t hpath
  have hright := hasDerivAt_timeSpaceCons u t x hu
  change fderiv ℝ U (t, x) ((1 : ℝ), (0 : ℝ^n)) = _
  exact hleft.unique hright

/-- The time-coordinate partial derivative is the derivative of the fixed-space
time curve. -/
theorem partialDeriv_timeSpaceCons_eq_deriv
    (u : ℝ^(n + 1) → E) (x : ℝ^n) (t : ℝ)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    (∂[0] u) (timeSpaceCons t x) =
      deriv (fun s ↦ u (timeSpaceCons s x)) t :=
  (hasDerivAt_timeSpaceCons u t x hu).deriv.symm

/-- The time direction of the `(x,t)` product pullback is coordinate zero in
canonical Euclidean spacetime. -/
theorem fderiv_joinSpaceTime_time
    (u : SpaceTime n → E) (x : ℝ^n) (t : ℝ)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    fderiv ℝ (fun p : ℝ^n × ℝ ↦ u (joinSpaceTime p))
        (x, t) ((0 : ℝ^n), (1 : ℝ)) =
      (∂[0] u) (timeSpaceCons t x) := by
  let U : ℝ^n × ℝ → E := fun p ↦ u (joinSpaceTime p)
  have hU : DifferentiableAt ℝ U (x, t) :=
    hu.comp (x, t) (spaceTimeContinuousLinearEquiv n).symm.differentiableAt
  calc
    fderiv ℝ U (x, t) ((0 : ℝ^n), (1 : ℝ)) =
        deriv (fun s ↦ U (x, s)) t :=
      (deriv_prod_timeSlice U x t hU).symm
    _ = (∂[0] u) (timeSpaceCons t x) := by
      simpa [U, joinSpaceTime] using
        (partialDeriv_timeSpaceCons_eq_deriv u x t hu).symm

/-- A spatial direction of the `(x,t)` product pullback is coordinate `i+1`
in canonical Euclidean spacetime. -/
theorem fderiv_joinSpaceTime_spatial
    (i : Fin n) (u : SpaceTime n → E) (x : ℝ^n) (t : ℝ)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    fderiv ℝ (fun p : ℝ^n × ℝ ↦ u (joinSpaceTime p))
        (x, t) (EuclideanSpace.single i (1 : ℝ), 0) =
      (∂[i.succ] u) (timeSpaceCons t x) := by
  let U : ℝ^n × ℝ → E := fun p ↦ u (joinSpaceTime p)
  have hU : DifferentiableAt ℝ U (x, t) :=
    hu.comp (x, t) (spaceTimeContinuousLinearEquiv n).symm.differentiableAt
  calc
    fderiv ℝ U (x, t) (EuclideanSpace.single i (1 : ℝ), 0) =
        (∂[i] (fun y ↦ U (y, t))) x :=
      (partialDeriv_prod_spaceSlice i U x t hU).symm
    _ = (∂[i.succ] u) (timeSpaceCons t x) := by
      simpa [U, joinSpaceTime] using
        partialDeriv_timeSpaceCons_spatial i u t x hu

end PDE

section LocalGerms

open Filter
open scoped Topology

namespace PDE

/-- A joint C² germ suffices to differentiate a spatial partial in time. The resulting
mixed derivative is the spatial partial of the time derivative. No global regularity
or separate mixed-derivative hypothesis is needed. -/
theorem hasDerivAt_partialDeriv_timeSlice_of_contDiffAt_two
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n × ℝ → E) (x : ℝ^n) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (x, t)) :
    HasDerivAt (fun s ↦ (∂[i] (fun y ↦ f (y, s))) x)
      ((∂[i] (fun y ↦ deriv (fun s ↦ f (y, s)) t)) x) t := by
  let ei : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  let spaceDerivative : ℝ^n × ℝ → E := fun q ↦ fderiv ℝ f q (ei, 0)
  let timeDerivative : ℝ^n × ℝ → E := fun q ↦ fderiv ℝ f q (0, 1)
  have hfDiff : ∀ᶠ q in 𝓝 (x, t), DifferentiableAt ℝ f q :=
    (hf.eventually (by norm_num)).mono fun q hq ↦ hq.differentiableAt (by norm_num)
  have hspaceDiff : DifferentiableAt ℝ spaceDerivative (x, t) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have htimeDiff : DifferentiableAt ℝ timeDerivative (x, t) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hleft : (fun s ↦ (∂[i] (fun y ↦ f (y, s))) x) =ᶠ[𝓝 t]
      fun s ↦ spaceDerivative (x, s) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hfDiff]
      with s hs
    exact partialDeriv_prod_spaceSlice i f x s hs
  have hright : (fun y ↦ deriv (fun s ↦ f (y, s)) t) =ᶠ[𝓝 x]
      fun y ↦ timeDerivative (y, t) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hfDiff]
      with y hy
    exact deriv_prod_timeSlice f y t hy
  have hvalue : (∂[i] (fun y ↦ deriv (fun s ↦ f (y, s)) t)) x =
      fderiv ℝ spaceDerivative (x, t) (0, 1) := by
    change fderiv ℝ (fun y ↦ deriv (fun s ↦ f (y, s)) t) x ei = _
    rw [hright.fderiv_eq]
    change (∂[i] (fun y ↦ timeDerivative (y, t))) x = _
    rw [partialDeriv_prod_spaceSlice i timeDerivative x t htimeDiff]
    exact (fderiv_fderiv_apply_comm f (x, t) (ei, 0) (0, 1) hf).symm
  have hinsert : HasDerivAt (fun s : ℝ ↦ (x, s)) ((0 : ℝ^n), (1 : ℝ)) t :=
    (hasDerivAt_const (x := t) (c := x)).prodMk (hasDerivAt_id t)
  rw [hvalue]
  exact (hspaceDiff.hasFDerivAt.comp_hasDerivAt t hinsert)
    |>.congr_of_eventuallyEq hleft

/-- One spatial derivative costs one derivative of the joint germ. -/
theorem contDiffAt_partialDeriv_prod_spaceSlice
    (i : Fin n) (f : ℝ^n × ℝ → E) (m : ℕ) (xt : ℝ^n × ℝ)
    (hf : ContDiffAt ℝ (m + 1) f xt) :
    ContDiffAt ℝ m
      (fun q : ℝ^n × ℝ ↦ (∂[i] (fun y ↦ f (y, q.2))) q.1) xt := by
  have hd : ∀ᶠ q in 𝓝 xt, DifferentiableAt ℝ f q :=
    (hf.eventually (by norm_num)).mono fun q hq ↦ hq.differentiableAt (by norm_num)
  have heq : (fun q : ℝ^n × ℝ ↦ (∂[i] (fun y ↦ f (y, q.2))) q.1) =ᶠ[𝓝 xt]
      fun q ↦ fderiv ℝ f q (EuclideanSpace.single i (1 : ℝ), 0) :=
    hd.mono fun q hq ↦ partialDeriv_prod_spaceSlice i f q.1 q.2 hq
  exact ((hf.fderiv_right (m := m) (by norm_num)).clm_apply contDiffAt_const)
    |>.congr_of_eventuallyEq heq

end PDE

end LocalGerms
