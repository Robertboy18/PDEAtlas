/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Analysis.Calculus.LocalExtension
import PDE.Analysis.ODE.SmoothDependence.InitialData
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Equation
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.InitialMomentum
public import
  PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local uniqueness on a noncharacteristic momentum branch

Two C² classical solutions with the same boundary values and the same initial
momentum agree near a noncharacteristic boundary point. The Hamiltonian need
only be C² near that initial phase.

The proof constructs spatial characteristics for each solution. Their lifts
`(Du,u,x)` satisfy the phase ODE by differentiating the PDE. The implicit
momentum theorem identifies their initial states, and ODE uniqueness identifies
the lifts. The noncharacteristic inverse function theorem turns this equality
along characteristics into equality on a spatial neighborhood.

The base momentum matters: a nonlinear equation can admit distinct
noncharacteristic momentum branches for the same boundary values.
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime)

noncomputable section

open Filter Metric Set
open scoped NNReal RealInnerProductSpace Topology

namespace NonlinearFirstOrder

variable {k : ℕ}

/-- Every neighborhood of `(y0, 0)` contains an open parameter neighborhood times
a symmetric time interval of positive length. The parameter space only needs a topology. -/
private theorem exists_open_time_box {Y : Type*} [TopologicalSpace Y] {y0 : Y} {S : Set (Y × ℝ)}
    (hS : S ∈ 𝓝 (y0, (0 : ℝ))) :
    ∃ W : Set Y, IsOpen W ∧ y0 ∈ W ∧ ∃ T : ℝ, 0 < T ∧ W ×ˢ Ioo (-T) T ⊆ S := by
  obtain ⟨U, hU, J, hJ, hprod⟩ := mem_nhds_prod_iff.mp hS
  obtain ⟨W, hWU, hW, hyW⟩ := _root_.mem_nhds_iff.mp hU
  obtain ⟨T, hT, hball⟩ := Metric.mem_nhds_iff.mp hJ
  have htime : Ioo (-T) T ⊆ J := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hball
  exact ⟨W, hW, hyW, T, hT, fun q hq ↦ hprod ⟨hWU hq.1, htime hq.2⟩⟩

/-- Construct a jointly C¹ spatial characteristic family from a C² function.
The curves stay in its open regularity domain and solve the spatial
characteristic equation for its value and gradient.

Only the spatial vector field's germ is extended. The neighborhood is
restricted afterwards, so its curves solve the original spatial equation. -/
theorem exists_spatial_characteristics_of_contDiff_two (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 2 (phaseFunction F)) (u : SpaceTime k → ℝ) (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (boundary : ℝ^k → SpaceTime k) (W : Set (ℝ^k))
    (hW : IsOpen W) (hb : ContDiffOn ℝ 1 boundary W) (y0 : ℝ^k) (hy0 : y0 ∈ W)
    (hx0 : boundary y0 ∈ Ω) :
    ∃ U : Set (ℝ^k), IsOpen U ∧ y0 ∈ U ∧ U ⊆ W ∧
      ∃ T : ℝ, 0 < T ∧ ∃ X : ℝ^k × ℝ → SpaceTime k,
        ContDiffOn ℝ 1 X (U ×ˢ Ioo (-T) T) ∧
        (∀ y ∈ U, X (y, 0) = boundary y) ∧
        ∀ y ∈ U, ∀ t ∈ Ioo (-T) T,
          X (y, t) ∈ Ω ∧
          HasDerivAt (fun s ↦ X (y, s))
            (momentumGradient F (∇ u (X (y, t))) (u (X (y, t))) (X (y, t))) t := by
  let spatial : SpaceTime k → SpaceTime k := fun x ↦ characteristicDp F (∇ u x, (u x, x))
  have hspatial : ContDiffOn ℝ 1 spatial Ω := ((contDiff_characteristicVectorField F
    hF).comp_contDiffOn (contDiffOn_solution_phase u Ω hΩ hu)).snd.snd
  obtain ⟨v, hv, _, heq⟩ :=
    (hspatial.contDiffAt (hΩ.mem_nhds hx0)).exists_contDiff_compactSupport_eventuallyEq
  obtain ⟨U, hU, hyU, hUW, T, hT, X, hX, hflow⟩ :=
    PDE.Analysis.ODE.exists_local_contDiff_one_family_with_initialData v hv boundary W hW hb y0 hy0
  have hbox0 := (hU.prod isOpen_Ioo).mem_nhds (mk_mem_prod hyU ⟨neg_lt_zero.mpr hT, hT⟩)
  -- Near `(y0, 0)` the curves stay in `Ω`, where the extended field is the spatial one.
  have hgood : {q : ℝ^k × ℝ | X q ∈ Ω ∧ spatial (X q) = v (X q)} ∈ 𝓝 (y0, (0 : ℝ)) :=
    (hX.contDiffAt hbox0).continuousAt
      (by rw [(hflow y0 hyU).1]; exact (hΩ.eventually_mem hx0).and heq)
  obtain ⟨U₀, hU₀, hyU₀, δ, hδ, hsub⟩ := exists_open_time_box (inter_mem hbox0 hgood)
  have hU₀U : U₀ ⊆ U := fun y hy ↦ (hsub (mk_mem_prod hy ⟨neg_lt_zero.mpr hδ, hδ⟩)).1.1
  refine ⟨U₀, hU₀, hyU₀, hU₀U.trans hUW, δ, hδ, X, hX.mono fun q hq ↦ (hsub hq).1,
    fun y hy ↦ (hflow y (hU₀U hy)).1, fun y hy t ht ↦ ?_⟩
  have hqt := hsub (mk_mem_prod hy ht)
  have hd := ((hflow y hqt.1.1).2 t hqt.1.2).1
  rw [← hqt.2.2] at hd
  exact ⟨hqt.2.1, by
    simpa only [spatial, characteristicDp_eq_DpF F (hF.differentiable (by norm_num))] using hd⟩

/-- Two classical traces with the same base momentum select the same nearby
implicit momentum branch. Equality of boundary gradients is derived from
compatibility and the implicit function theorem. -/
theorem eventuallyEq_boundary_gradient_of_classical_trace (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 1 (phaseFunction F)) (u v : SpaceTime k → ℝ) (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hupde : ∀ x ∈ Ω, F (∇ u x) (u x) x = 0) (hvpde : ∀ x ∈ Ω, F (∇ v x) (v x) x = 0)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W)
    (hb : ContDiffOn ℝ 2 boundary W) (hg : ContDiffOn ℝ 2 data W) (y0 : ℝ^k) (hy0 : y0 ∈ W)
    (p0 : SpaceTime k)
    (htrace : ∀ y ∈ W, boundary y ∈ Ω ∧ u (boundary y) = data y ∧ v (boundary y) = data y)
    (hup : ∇ u (boundary y0) = p0) (hvp : ∇ v (boundary y0) = p0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 (data y0)) :
    (fun y ↦ ∇ u (boundary y)) =ᶠ[𝓝 y0] fun y ↦ ∇ v (boundary y) := by
  have compatible (w : SpaceTime k → ℝ) (hw : ContDiffOn ℝ 2 w Ω)
      (hpde : ∀ x ∈ Ω, F (∇ w x) (w x) x = 0) (hvalue : ∀ y ∈ W, w (boundary y) = data y)
      (y : ℝ^k) (hy : y ∈ W) :
      IsCompatibleInitialGradientAt F boundary data y (∇ w (boundary y)) := by
    refine isCompatibleInitialGradientAt_of_classical_trace F boundary data w y
      ((hb.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num))
      ((hw.contDiffAt (hΩ.mem_nhds (htrace y hy).1)).differentiableAt (by norm_num))
      ?_ (hpde _ (htrace y hy).1)
    filter_upwards [hW.eventually_mem hy] with z hz using (hvalue z hz).symm
  have hcu := compatible u hu hupde (fun y hy ↦ (htrace y hy).2.1)
  have hcv := compatible v hv hvpde (fun y hy ↦ (htrace y hy).2.2)
  have hbase : IsCompatibleInitialGradientAt F boundary data y0 p0 := by
    simpa only [hup] using hcu y0 hy0
  obtain ⟨_, _, _, _, p, _, _, _, hbranch⟩ :=
    exists_local_compatible_initialGradient 1 (by norm_num) F hF
      boundary data W hW hb hg y0 hy0 p0 hbase hnonchar
  have ht (w : SpaceTime k → ℝ) (hw : ContDiffOn ℝ 2 w Ω) (hwp : ∇ w (boundary y0) = p0) :
      Tendsto (fun y ↦ (y, ∇ w (boundary y))) (𝓝 y0) (𝓝 (y0, p0)) := by
    have := ((contDiffOn_solution_phase w Ω hΩ hw).contDiffAt
      (hΩ.mem_nhds (htrace y0 hy0).1)).continuousAt.fst.comp
        (hb.contDiffAt (hW.mem_nhds hy0)).continuousAt
    simpa only [id_eq, Function.comp_apply, hwp] using (continuousAt_id.prodMk this).tendsto
  filter_upwards [(ht u hu hup).eventually hbranch, (ht v hv hvp).eventually hbranch,
    hW.eventually_mem hy0] with y hyu hyv hy
  exact ((hyu.mp (hcu y hy)).symm).trans (hyv.mp (hcv y hy))

/-- Initial positions and the time-zero characteristic velocity determine the
derivative of a spatial characteristic family. Differentiability and agreement
with the boundary germ identify its tangential component. -/
private theorem hasFDerivAt_spatial_characteristics_initial (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (y0 : ℝ^k) (p0 : SpaceTime k) (z0 : ℝ)
    (X : ℝ^k × ℝ → SpaceTime k) (hX : DifferentiableAt ℝ X (y0, 0))
    (hinit : (fun y ↦ X (y, 0)) =ᶠ[𝓝 y0] boundary)
    (htime : HasDerivAt (fun t ↦ X (y0, t)) (momentumGradient F p0 z0 (boundary y0)) 0) :
    HasFDerivAt X (characteristicInitialDerivative F boundary y0 p0 z0) (y0, 0) := by
  have hspace (dy : ℝ^k) :
      fderiv ℝ X (y0, 0) (dy, 0) = fderiv ℝ boundary y0 dy := by
    rw [← fderiv_boundary_slice X y0 0 hX dy]
    exact congrArg (fun L : ℝ^k →L[ℝ] SpaceTime k ↦ L dy) hinit.fderiv_eq
  have ht : fderiv ℝ X (y0, 0) (0, 1) = momentumGradient F p0 z0 (boundary y0) :=
    (deriv_time_slice X y0 0 hX).symm.trans htime.deriv
  apply hX.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  rintro ⟨dy, s⟩
  rw [characteristicInitialDerivative_apply]
  calc
    fderiv ℝ X (y0, 0) (dy, s) =
        fderiv ℝ X (y0, 0) ((dy, 0) + s • ((0 : ℝ^k), (1 : ℝ))) := by
      congr 1
      simp
    _ = fderiv ℝ boundary y0 dy +
        s • momentumGradient F p0 z0 (boundary y0) := by
      rw [map_add, map_smul, hspace, ht]

/-- Near `(y0, 0)`, the phase lift `(Dw, w, x)` of a spatial characteristic family of a C²
solution `w` lies in a given neighborhood `N` of the initial phase and solves the characteristic
ODE. The family starts on the boundary. -/
private theorem exists_phase_characteristics (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 2 (phaseFunction F)) (w : SpaceTime k → ℝ) (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (hw : ContDiffOn ℝ 2 w Ω) (hwpde : ∀ x ∈ Ω, F (∇ w x) (w x) x = 0)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W)
    (hb : ContDiffOn ℝ 2 boundary W) (y0 : ℝ^k) (hy0 : y0 ∈ W) (p0 : SpaceTime k)
    (hx0 : boundary y0 ∈ Ω) (hwp : ∇ w (boundary y0) = p0) (hwv : w (boundary y0) = data y0)
    {N : Set (SpaceTime k × (ℝ × SpaceTime k))} (hN : N ∈ 𝓝 (p0, (data y0, boundary y0))) :
    ∃ X : ℝ^k × ℝ → SpaceTime k, ContDiffAt ℝ 1 X (y0, 0) ∧
      HasDerivAt (fun t ↦ X (y0, t)) (momentumGradient F p0 (data y0) (boundary y0)) 0 ∧
      ∃ S ∈ 𝓝 ((y0, 0) : ℝ^k × ℝ), ∀ y t, (y, t) ∈ S → y ∈ W ∧ X (y, 0) = boundary y ∧
        (∇ w (X (y, t)), (w (X (y, t)), X (y, t))) ∈ N ∧
        HasDerivAt (fun s ↦ (∇ w (X (y, s)), (w (X (y, s)), X (y, s))))
          (characteristicVectorField F (∇ w (X (y, t)), (w (X (y, t)), X (y, t)))) t := by
  obtain ⟨U, hU, hyU, hUW, T, hT, X, hX, hXi, hXf⟩ :=
    exists_spatial_characteristics_of_contDiff_two F hF w Ω hΩ hw boundary W hW
      (hb.of_le (by norm_num)) y0 hy0 hx0
  have hz : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hbox := (hU.prod isOpen_Ioo).mem_nhds (mk_mem_prod hyU hz)
  have hXAt : ContDiffAt ℝ 1 X (y0, 0) := hX.contDiffAt hbox
  have hP : ContinuousAt (fun q ↦ (∇ w (X q), (w (X q), X q))) (y0, 0) :=
    ((contDiffOn_solution_phase w Ω hΩ hw).contDiffAt
      (hΩ.mem_nhds (hXf y0 hyU 0 hz).1)).continuousAt.comp hXAt.continuousAt
  refine ⟨X, hXAt, by simpa only [hXi y0 hyU, hwp, hwv] using (hXf y0 hyU 0 hz).2,
    _, inter_mem hbox (hP (by simpa only [hXi y0 hyU, hwp, hwv] using hN)),
    fun y t hq ↦ ⟨hUW hq.1.1, hXi y hq.1.1, hq.2, ?_⟩⟩
  exact hasDerivAt_solution_phase_of_spatial_characteristic F (hF.of_le (by norm_num)) w Ω hΩ
    hw hwpde (fun s ↦ X (y, s)) t (hXf y hq.1.1 t hq.1.2).1 (hXf y hq.1.1 t hq.1.2).2

/-- For a globally C² Hamiltonian, C² solutions with the same C² boundary trace and
base momentum agree near a noncharacteristic point. The implicit momentum branch
identifies their initial phases; ODE uniqueness and inverse coordinates then
identify their values on a spatial neighborhood. -/
private theorem eventuallyEq_classical_solutions_of_global_hamiltonian
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (hF : ContDiff ℝ 2 (phaseFunction F))
    (u v : SpaceTime k → ℝ) (Ω : Set (SpaceTime k)) (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hv : ContDiffOn ℝ 2 v Ω) (hupde : ∀ x ∈ Ω, F (∇ u x) (u x) x = 0)
    (hvpde : ∀ x ∈ Ω, F (∇ v x) (v x) x = 0) (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (W : Set (ℝ^k)) (hW : IsOpen W) (hb : ContDiffOn ℝ 2 boundary W) (hg : ContDiffOn ℝ 2 data W)
    (y0 : ℝ^k) (hy0 : y0 ∈ W) (p0 : SpaceTime k)
    (htrace : ∀ y ∈ W, boundary y ∈ Ω ∧ u (boundary y) = data y ∧ v (boundary y) = data y)
    (hup : ∇ u (boundary y0) = p0) (hvp : ∇ v (boundary y0) = p0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 (data y0)) :
    u =ᶠ[𝓝 (boundary y0)] v := by
  have hbranch := eventuallyEq_boundary_gradient_of_classical_trace F (hF.of_le (by norm_num))
    u v Ω hΩ hu hv hupde hvpde boundary data W hW hb hg y0 hy0 p0 htrace hup hvp hnonchar
  obtain ⟨K, N, hN, hLip⟩ := ((contDiff_characteristicVectorField F hF).contDiffAt
    (x := (p0, (data y0, boundary y0)))).exists_lipschitzOnWith
  obtain ⟨Xu, hXuAt, htime, Su, hSu, hXu⟩ := exists_phase_characteristics F hF u Ω hΩ hu hupde
    boundary data W hW hb y0 hy0 p0 (htrace y0 hy0).1 hup (htrace y0 hy0).2.1 hN
  obtain ⟨Xv, -, -, Sv, hSv, hXv⟩ := exists_phase_characteristics F hF v Ω hΩ hv hvpde
    boundary data W hW hb y0 hy0 p0 (htrace y0 hy0).1 hvp (htrace y0 hy0).2.2 hN
  obtain ⟨U, hU, hyU, T, hT, hsub⟩ := exists_open_time_box (inter_mem hSu (inter_mem hSv
    ((continuousAt_fst (p := ((y0, 0) : ℝ^k × ℝ))).tendsto.eventually hbranch)))
  have hz : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  -- ODE uniqueness identifies the two phase lifts along each characteristic.
  have heqAlong : ∀ y ∈ U, ∀ t ∈ Ioo (-T) T, u (Xu (y, t)) = v (Xu (y, t)) := by
    intro y hy t ht
    have h (t) (ht : t ∈ Ioo (-T) T) := hsub (mk_mem_prod hy ht)
    obtain ⟨hyW, hXu0, -, -⟩ := hXu y 0 (h 0 hz).1
    have hgrad : ∇ u (boundary y) = ∇ v (boundary y) := (h 0 hz).2.2
    have heq := ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ characteristicVectorField F)
      (s := fun _ ↦ N) (K := K) (fun _ _ ↦ hLip) hz
      (fun t ht ↦ ⟨(hXu y t (h t ht).1).2.2.2, (hXu y t (h t ht).1).2.2.1⟩)
      (fun t ht ↦ ⟨(hXv y t (h t ht).2.1).2.2.2, (hXv y t (h t ht).2.1).2.2.1⟩)
      (by simp only [hXu0, (hXv y 0 (h 0 hz).2.1).2.1, hgrad, (htrace y hyW).2.1,
        (htrace y hyW).2.2]) ht
    exact (congrArg (·.2.1) heq).trans (congrArg v (congrArg (·.2.2) heq).symm)
  -- The initial spatial derivative is the noncharacteristic matrix.
  have hinit : (fun y ↦ Xu (y, 0)) =ᶠ[𝓝 y0] boundary := by
    filter_upwards [hU.eventually_mem hyU] with y hy
    exact (hXu y 0 (hsub (mk_mem_prod hy hz)).1).2.1
  obtain ⟨e, he⟩ := hnonchar
  have hDe : HasFDerivAt Xu (e : (ℝ^k × ℝ) →L[ℝ] SpaceTime k) (y0, 0) := he ▸
    hasFDerivAt_spatial_characteristics_initial F boundary y0 p0 (data y0) Xu
      (hXuAt.differentiableAt (by norm_num)) hinit htime
  let chart := hXuAt.toOpenPartialHomeomorph Xu hDe one_ne_zero
  have hmap : Filter.map Xu (𝓝 (y0, 0)) = 𝓝 (boundary y0) := by
    simpa only [show ⇑chart = Xu from rfl, hinit.self_of_nhds] using
      chart.map_nhds_eq (hXuAt.mem_toOpenPartialHomeomorph_source hDe one_ne_zero)
  rw [← hmap]
  exact Filter.eventually_map.2 (((hU.prod isOpen_Ioo).eventually_mem (mk_mem_prod hyU hz)).mono
    fun q hq ↦ heqAlong q.1 hq.1 q.2 hq.2)

/-- Local uniqueness of C² classical solutions on a fixed noncharacteristic
momentum branch.

The two solutions have the same values on a C² parametrized initial surface
and the same gradient `p0` at its base point. The Hamiltonian is assumed C²
only near `(p0,data(y0),boundary(y0))`. The conclusion is equality on a
neighborhood of the spatial base point, not global uniqueness.

Compatibility of the initial momentum is derived from the classical PDE and
boundary trace. The proof constructs both spatial characteristic families,
derives the phase equations for their gradients and values, and uses
ODE uniqueness followed by noncharacteristic inverse coordinates. -/
theorem eventuallyEq_classical_solutions_of_same_initial_momentum
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (u v : SpaceTime k → ℝ) (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hupde : IsClassicalSolution (n := k + 1) { F := F, domain := Ω } u)
    (hvpde : IsClassicalSolution (n := k + 1) { F := F, domain := Ω } v)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W)
    (hb : ContDiffOn ℝ 2 boundary W) (hg : ContDiffOn ℝ 2 data W) (y0 : ℝ^k) (hy0 : y0 ∈ W)
    (p0 : SpaceTime k) (hF : ContDiffAt ℝ 2 (phaseFunction F) (p0, (data y0, boundary y0)))
    (htrace : ∀ y ∈ W, boundary y ∈ Ω ∧ u (boundary y) = data y ∧ v (boundary y) = data y)
    (hup : ∇ u (boundary y0) = p0) (hvp : ∇ v (boundary y0) = p0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 (data y0)) :
    u =ᶠ[𝓝 (boundary y0)] v := by
  obtain ⟨G, hG, _, heq⟩ := hF.exists_contDiff_compactSupport_eventuallyEq
  let FG : SpaceTime k → ℝ → SpaceTime k → ℝ := fun p z x ↦ G (p, (z, x))
  have hphaseFG : phaseFunction FG = G := rfl
  have heqFG : phaseFunction F =ᶠ[𝓝 (p0, (data y0, boundary y0))] phaseFunction FG := heq
  have hpFG := momentumGradient_eq_of_phaseFunction_eventuallyEq F FG p0 (data y0)
    (boundary y0) heqFG
  have hnoncharFG : IsNoncharacteristicAt FG boundary y0 p0 (data y0) := by
    simpa only [IsNoncharacteristicAt, characteristicInitialDerivative, hpFG] using hnonchar
  have hx0 : boundary y0 ∈ Ω := (htrace y0 hy0).1
  -- Near the base point each solution's phase stays where `F` and `FG` agree.
  have hagree (w : SpaceTime k → ℝ) (hw : ContDiffOn ℝ 2 w Ω) (hwp : ∇ w (boundary y0) = p0)
      (hwv : w (boundary y0) = data y0) :
      {x | F (∇ w x) (w x) x = FG (∇ w x) (w x) x} ∈ 𝓝 (boundary y0) :=
    (show Tendsto (fun x ↦ (∇ w x, (w x, x))) (𝓝 (boundary y0))
        (𝓝 (p0, (data y0, boundary y0))) by
      simpa only [hwp, hwv] using ((contDiffOn_solution_phase w Ω hΩ hw).contDiffAt
        (hΩ.mem_nhds hx0)).continuousAt.tendsto).eventually heqFG
  obtain ⟨Ω₀, hΩ₀sub, hΩ₀, hxΩ₀⟩ := _root_.mem_nhds_iff.mp (inter_mem (hΩ.mem_nhds hx0)
    (inter_mem (hagree u hu hup (htrace y0 hy0).2.1) (hagree v hv hvp (htrace y0 hy0).2.2)))
  have hΩ₀Ω : Ω₀ ⊆ Ω := fun x hx ↦ (hΩ₀sub hx).1
  exact eventuallyEq_classical_solutions_of_global_hamiltonian FG (hphaseFG ▸ hG) u v Ω₀ hΩ₀
    (hu.mono hΩ₀Ω) (hv.mono hΩ₀Ω) (fun x hx ↦ (hΩ₀sub hx).2.1.symm.trans (hupde x (hΩ₀Ω hx)).2)
    (fun x hx ↦ (hΩ₀sub hx).2.2.symm.trans (hvpde x (hΩ₀Ω hx)).2) boundary data
    (W ∩ boundary ⁻¹' Ω₀) (hb.continuousOn.isOpen_inter_preimage hW hΩ₀)
    (hb.mono inter_subset_left) (hg.mono inter_subset_left) y0 ⟨hy0, hxΩ₀⟩ p0
    (fun y hy ↦ ⟨hy.2, (htrace y hy.1).2⟩) hup hvp hnoncharFG

end NonlinearFirstOrder

end
