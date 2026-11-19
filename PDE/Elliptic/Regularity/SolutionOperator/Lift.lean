/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Generic elliptic regularity lifts

Let `S : L²(Omega) →L H¹₀(Omega)` be a bounded weak-solution operator such that the weak solution of
every `H^m` forcing has an `H^{m+2}` representative (`HasHigherSolutionLift`). Then `S` lifts to a
bounded linear solution operator `H^m(Omega) →L H^{m+2}(Omega)` that represents the weak solution
(`higherSolutionOperator`, `higherSolutionOperator_base`). The same operator acts on Bochner
trajectories (`higherSolutionOperatorLp`, `higherSolutionOperatorLp_base`,
`higherSolutionOperatorLp_memLp_top`), and an almost-everywhere family of weak solutions becomes one
`L∞_t H^{m+2}_x` trajectory (`exists_higherSolutionTrajectory_of_weak_solution`). At order zero the
hypothesis is an `L² → H²` representative theorem (`hasHigherSolutionLift_zero`). The global
regularity theorems are connected to this construction in
`PDE.Elliptic.Regularity.SolutionOperator.H2` and
`PDE.Elliptic.Regularity.SolutionOperator.HigherOrder`.

The bound `‖u‖_{H^{m+2}} ≤ C ‖f‖_{H^m}` given by the operator norm is the estimate in the remark
after Evans's §6.3.2, Theorem 5, for a unique weak solution. Evans applies the elliptic estimate at
almost every time in step 3 of his proof of §7.1.3, Theorem 5, (49), and in step 3 of his proof of
§7.2.3, Theorem 6, with `Lu = f - u''`.

## How it works

Evans proves the estimate (77), which carries the extra term `‖u‖_{L²(U)}`, by induction on `m` from
the difference-quotient argument of Theorem 4, and drops that term for a unique solution; for
`m = 0`, Remark (i) after Theorem 4 derives this from §6.2.3, Theorem 6. We take only the
qualitative statement as input and obtain the estimate from the closed graph theorem. Uniqueness of
weak derivatives makes the chosen representative depend linearly on the forcing
(`qualitativeHigherLiftLinearMap`). The graph is closed because convergence in `H^{m+2}` controls
the base coordinate, while continuity of `S` identifies the limiting base function, so the map is
bounded (`higherSolutionOperator`); the constant is not explicit. A continuous linear map acts on
Bochner classes by composition, so the trajectory statements need no measurable selection of
pointwise representatives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 6 (Boundedness of the inverse), p. 324;
  §6.3.2, Theorem 4 (Boundary H²-regularity) and Remark (i) after it, pp. 334-335, and Theorem 5
  (Higher boundary regularity), (77), and the remark after it, pp. 340-341; §7.1.3, step 3 of the
  proof of Theorem 5, (49), p. 384; §7.2.3, step 3 of the proof of Theorem 6, p. 414.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (iteratedPartialDeriv)
open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory
open scoped ENNReal Topology

variable {n m : ℕ} {Omega : Set (ℝ^n)}

/-! ## The canonical order-zero Sobolev space -/

section OrderZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Place an `L^p(Omega)` class in the unique coordinate of the order-zero ambient space. -/
noncomputable def orderZeroAmbientCLM :
    DerivLp n p Omega →L[ℝ] WkpAmbientOn n 0 p Omega := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n 0 ↦ DerivLp n p Omega)
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ
      (fun _ : DerivIndex n 0 ↦ DerivLp n p Omega)
      (baseIndex n 0))

/-- The order-zero ambient embedding of an `L^p(Omega)` class is a `W^{0,p}(Omega)` family. -/
theorem orderZeroAmbientCLM_mem (f : DerivLp n p Omega) :
    IsWkpOn (n := n) (k := 0) (p := p) (Ω := Omega)
      (orderZeroAmbientCLM (n := n) (p := p) (Omega := Omega) f) := by
  intro a
  have ha : a = baseIndex n 0 := DerivIndex.eq_baseIndex_of_order_zero a
  subst a
  have hloc := memLp_locallyIntegrableOn_domain
    (MeasureTheory.Lp.memLp
      ((orderZeroAmbientCLM (n := n) (p := p) (Omega := Omega) f)
        (baseIndex n 0)))
    (Fact.out : (1 : ℝ≥0∞) ≤ p)
  refine ⟨hloc, hloc, ?_⟩
  intro φ _
  simp [iteratedPartialDeriv]

/--
Package an `L^p(Omega)` class as the unique-coordinate element of
`W^{0,p}(Omega)`.

This bounded map is the canonical input conversion used when the generic
higher-order lift is specialized to `m = 0`.
-/
noncomputable def orderZeroSobolevCLM :
    DerivLp n p Omega →L[ℝ] W^{0,p}(Omega) :=
  ContinuousLinearMap.codRestrict
    (orderZeroAmbientCLM (n := n) (p := p) (Omega := Omega))
    (wkpSubmoduleOn n 0 p Omega)
    (orderZeroAmbientCLM_mem (n := n) (p := p) (Omega := Omega))

/-- The base coordinate of the `W^{0,p}` element built from `f` is `f` itself. -/
theorem orderZeroSobolevCLM_base (f : DerivLp n p Omega) :
    wkpBaseCoordinateCLM
        (n := n) (m := 0) (p := p) (Ω := Omega)
        (orderZeroSobolevCLM (n := n) (p := p) (Omega := Omega) f) = f := by
  classical
  simp [orderZeroSobolevCLM, orderZeroAmbientCLM,
    wkpBaseCoordinateCLM, wkpCoordinateCLM]

end OrderZero

section

variable (hOmegaOpen : IsOpen Omega)

local notation "L2" => DerivLp n 2 Omega

/--
The `L²` base function of the weak Dirichlet solution corresponding to an
`H^m` forcing.

The construction is a composition of bounded maps:

`H^m → L² → H¹₀ → H¹ → L²`.
-/
noncomputable def higherWeakSolutionBaseCLM
    (S : L2 →L[ℝ] H¹₀(Omega)) : W^{m,2}(Omega) →L[ℝ] L2 :=
  (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 2) (Ω := Omega)).comp
    ((h10SubtypeL
        (n := n) (Ω := Omega)).comp
      (S.comp
        (wkpBaseCoordinateCLM
          (n := n) (m := m) (p := 2) (Ω := Omega))))

/-- Evaluating the lifted base map applies the weak solver to the forcing's
zeroth Sobolev coordinate and then takes the solution's base coordinate. -/
@[simp]
theorem higherWeakSolutionBaseCLM_apply
    (S : L2 →L[ℝ] H¹₀(Omega)) (f : W^{m,2}(Omega)) :
    higherWeakSolutionBaseCLM S f =
      baseCoordCLM
        (n := n) (Ω := Omega)
        (S (wkpBaseCoordinateCLM
          (n := n) (m := m) (p := 2) (Ω := Omega) f)) :=
  rfl

/--
Qualitative elliptic regularity for the weak solution operator at forcing
order `m`.

This is the hypothesis of the closed-graph construction `higherSolutionOperator`:
every `H^m` forcing has an `H^{m+2}` representative of its weak solution.
-/
def HasHigherSolutionLift
    (order : ℕ)
    (S : DerivLp n 2 Omega →L[ℝ]
      H¹₀(Omega)) : Prop :=
  ∀ f : W^{order,2}(Omega),
    ∃ representative : W^{order + 2,2}(Omega),
      wkpBaseCoordinateCLM
          (n := n) (m := order + 2) (p := 2) (Ω := Omega)
          representative =
        higherWeakSolutionBaseCLM S f

/--
Qualitative higher-order lift of the weak-solution operator.

The selected `H^{m+2}` representative is unique: on an open domain, its base
function determines every weak derivative coordinate.
-/
noncomputable def qualitativeHigherLift
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (f : W^{m,2}(Omega)) : W^{m + 2,2}(Omega) :=
  Classical.choose (hreg f)

/-- The chosen `H^{m+2}` representative has base coordinate equal to the base function of the
weak solution, `higherWeakSolutionBaseCLM S f`. This is the defining property extracted from
`HasHigherSolutionLift`. -/
theorem qualitativeHigherLift_base
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (f : W^{m,2}(Omega)) :
    wkpBaseCoordinateCLM
        (n := n) (m := m + 2) (p := 2) (Ω := Omega)
        (qualitativeHigherLift S hreg f) =
      higherWeakSolutionBaseCLM S f :=
  Classical.choose_spec (hreg f)

/-- The qualitative higher-order lift as a linear map. Linearity follows from the weak solver
and uniqueness from the base coordinate; the map is used only in the closed-graph proof. -/
noncomputable def qualitativeHigherLiftLinearMap
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S) :
    W^{m,2}(Omega) →ₗ[ℝ] W^{m + 2,2}(Omega) where
  toFun := qualitativeHigherLift S hreg
  map_add' f g := by
    apply wkpBaseCoordinateCLM_injective hOmegaOpen
    rw [map_add, qualitativeHigherLift_base,
      map_add, qualitativeHigherLift_base, qualitativeHigherLift_base]
  map_smul' c f := by
    apply wkpBaseCoordinateCLM_injective hOmegaOpen
    rw [map_smul, qualitativeHigherLift_base,
      map_smul, qualitativeHigherLift_base]
    simp

/--
The bounded solution operator

`H^m(Omega) → H^{m+2}(Omega)`

obtained from the qualitative hypothesis `HasHigherSolutionLift` by the closed graph
theorem. Its operator norm is a constant for the estimate of the remark after Evans's
§6.3.2, Theorem 5.
-/
noncomputable def higherSolutionOperator
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S) :
    W^{m,2}(Omega) →L[ℝ] W^{m + 2,2}(Omega) := by
  let g := qualitativeHigherLiftLinearMap hOmegaOpen S hreg
  let baseOut :=
    wkpBaseCoordinateCLM
      (n := n) (m := m + 2) (p := 2) (Ω := Omega)
  let baseWeak : W^{m,2}(Omega) →L[ℝ] L2 :=
    higherWeakSolutionBaseCLM (m := m) S
  exact ContinuousLinearMap.ofSeqClosedGraph (g := g) (by
    intro fs f W hfs hgf
    have hOut :
        Tendsto (fun k ↦ baseOut (g (fs k))) atTop
          (𝓝 (baseOut W)) :=
      (baseOut.continuous.tendsto W).comp hgf
    have hWeak :
        Tendsto (fun k ↦ baseWeak (fs k)) atTop
          (𝓝 (baseWeak f)) :=
      (baseWeak.continuous.tendsto f).comp hfs
    have heq : ∀ k, baseOut (g (fs k)) = baseWeak (fs k) := by
      intro k
      exact qualitativeHigherLift_base S hreg (fs k)
    have hOut' :
        Tendsto (fun k ↦ baseOut (g (fs k))) atTop
          (𝓝 (baseWeak f)) := by
      simpa only [heq] using hWeak
    have hbase : baseOut W = baseWeak f :=
      tendsto_nhds_unique hOut hOut'
    apply wkpBaseCoordinateCLM_injective hOmegaOpen
    change baseOut W = baseOut (g f)
    exact hbase.trans
      (qualitativeHigherLift_base S hreg f).symm)

/-- The bounded solution operator agrees pointwise with the qualitative lift: the closed graph
theorem supplies boundedness without changing any value. -/
@[simp]
theorem higherSolutionOperator_apply
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (f : W^{m,2}(Omega)) :
    higherSolutionOperator hOmegaOpen S hreg f =
      qualitativeHigherLift S hreg f :=
  by
    change
      qualitativeHigherLiftLinearMap hOmegaOpen S hreg f =
        qualitativeHigherLift S hreg f
    rfl

/-- The higher-order solution operator represents the original weak solution. -/
theorem higherSolutionOperator_base
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (f : W^{m,2}(Omega)) :
    wkpBaseCoordinateCLM
        (n := n) (m := m + 2) (p := 2) (Ω := Omega)
        (higherSolutionOperator hOmegaOpen S hreg f) =
      higherWeakSolutionBaseCLM S f := by
  simpa using qualitativeHigherLift_base S hreg f

/-! ## Bochner trajectories and essential bounds -/

/--
Apply the higher-order elliptic solution operator at almost every time.

For a trajectory `r(t) ∈ H^m(Omega)`, the returned Bochner class is the
trajectory `S_{m+2}(r(t)) ∈ H^{m+2}(Omega)`. The construction uses the
action of a continuous linear map on `L²` by composition; it makes no
measurable-selection choice. Evans applies the elliptic estimate at almost every time
in step 3 of his proof of §7.1.3, Theorem 5, (49), and in step 3 of his proof of
§7.2.3, Theorem 6.
-/
noncomputable def higherSolutionOperatorLp
    (μ : Measure ℝ)
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S) :
    Lp W^{m,2}(Omega) 2 μ →L[ℝ] Lp W^{m + 2,2}(Omega) 2 μ :=
  (higherSolutionOperator hOmegaOpen S hreg).compLpL 2 μ

/-- The Bochner higher-order solver acts pointwise almost everywhere. -/
theorem higherSolutionOperatorLp_apply_ae
    (μ : Measure ℝ)
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (r : Lp W^{m,2}(Omega) 2 μ) :
    (higherSolutionOperatorLp hOmegaOpen μ S hreg r : ℝ → W^{m + 2,2}(Omega))
      =ᵐ[μ] fun t ↦ higherSolutionOperator hOmegaOpen S hreg (r t) :=
  (higherSolutionOperator hOmegaOpen S hreg).coeFn_compLpL r

/--
The Bochner lift represents the weak solution pointwise in its base
`L²(Omega)` coordinate.

This identity makes precise the step
"apply elliptic regularity to `Lu(t)=r(t)` for a.e. `t`".
-/
theorem higherSolutionOperatorLp_base
    (μ : Measure ℝ)
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (r : Lp W^{m,2}(Omega) 2 μ) :
    (fun t ↦
        wkpBaseCoordinateCLM
          (n := n) (m := m + 2) (p := 2) (Ω := Omega)
          (higherSolutionOperatorLp hOmegaOpen μ S hreg r t))
      =ᵐ[μ]
    fun t ↦ higherWeakSolutionBaseCLM S (r t) := by
  filter_upwards [higherSolutionOperatorLp_apply_ae hOmegaOpen μ S hreg r] with
    t ht
  rw [ht]
  exact higherSolutionOperator_base hOmegaOpen S hreg (r t)

/--
An essentially bounded `H^m` right-hand side produces an essentially
bounded `H^{m+2}` elliptic solution trajectory, with the same operator-norm
constant as the stationary estimate.

This is the estimate of step 3 of Evans's proof of §7.2.3, Theorem 6, where
`Lu = f - u'' =: h` for a.e. `t` and the essential supremum in `t` is taken.
-/
theorem higherSolutionOperatorLp_memLp_top
    (μ : Measure ℝ)
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (r : Lp W^{m,2}(Omega) 2 μ) (C : ℝ)
    (hr : ∀ᵐ t ∂μ, ‖r t‖ ≤ C) :
    MemLp
      (fun t ↦ higherSolutionOperatorLp hOmegaOpen μ S hreg r t)
      (⊤ : ℝ≥0∞) μ ∧
      (∀ᵐ t ∂μ,
        ‖higherSolutionOperatorLp hOmegaOpen μ S hreg r t‖ ≤
          ‖higherSolutionOperator hOmegaOpen S hreg‖ * C) := by
  have hpoint :
      ∀ᵐ t ∂μ,
        ‖higherSolutionOperatorLp hOmegaOpen μ S hreg r t‖ ≤
          ‖higherSolutionOperator hOmegaOpen S hreg‖ * C := by
    filter_upwards
      [higherSolutionOperatorLp_apply_ae hOmegaOpen μ S hreg r, hr] with
      t ht hrt
    rw [ht]
    have hsolve_nonneg :
        0 ≤ ‖(higherSolutionOperator hOmegaOpen S hreg :
          W^{m,2}(Omega) →L[ℝ] W^{m + 2,2}(Omega))‖ :=
      (higherSolutionOperator hOmegaOpen S hreg).opNorm_nonneg
    exact ((higherSolutionOperator hOmegaOpen S hreg).le_opNorm (r t)).trans
      (mul_le_mul_of_nonneg_left hrt hsolve_nonneg)
  exact
    ⟨memLp_top_of_bound
        (Lp.aestronglyMeasurable
          (higherSolutionOperatorLp hOmegaOpen μ S hreg r))
        (‖higherSolutionOperator hOmegaOpen S hreg‖ * C)
        hpoint,
      hpoint⟩

/--
Lift an almost-everywhere family of weak elliptic solutions to one
`L∞_t H^{m+2}_x` trajectory.

The hypothesis identifies the base coordinate of the given
`H¹₀(Omega)`-valued trajectory with the weak solution selected by `S` for
the right-hand side `r(t)`. The conclusion collects the pointwise
regularity theorem into a single Bochner class and retains both the
almost-everywhere identification and its uniform norm estimate.

For the wave equation, the caller takes `r = f - u_tt`; the weak wave
identity proves `hweak`, and the differentiated induction estimate proves
`hr`.
-/
theorem exists_higherSolutionTrajectory_of_weak_solution
    (μ : Measure ℝ)
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg : HasHigherSolutionLift m S)
    (r : Lp W^{m,2}(Omega) 2 μ)
    (u : Lp H¹₀(Omega) 2 μ)
    (hweak : ∀ᵐ t ∂μ,
      higherWeakSolutionBaseCLM S ((r : ℝ → W^{m,2}(Omega)) t) =
        wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL
            (n := n) (Ω := Omega)
            ((u : ℝ → H¹₀(Omega)) t)))
    (C : ℝ) (hr : ∀ᵐ t ∂μ, ‖(r : ℝ → W^{m,2}(Omega)) t‖ ≤ C) :
    ∃ U : Lp W^{m + 2,2}(Omega) 2 μ,
      ((fun t ↦
          wkpBaseCoordinateCLM
            (n := n) (m := m + 2) (p := 2) (Ω := Omega)
            ((U : ℝ → W^{m + 2,2}(Omega)) t))
        =ᵐ[μ]
        fun t ↦
          wkpBaseCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Omega)
            (h10SubtypeL
              (n := n) (Ω := Omega)
              ((u : ℝ → H¹₀(Omega)) t))) ∧
      MemLp (fun t ↦ (U : ℝ → W^{m + 2,2}(Omega)) t) (⊤ : ℝ≥0∞) μ ∧
      ∀ᵐ t ∂μ, ‖(U : ℝ → W^{m + 2,2}(Omega)) t‖ ≤
        ‖higherSolutionOperator hOmegaOpen S hreg‖ * C := by
  let U : Lp W^{m + 2,2}(Omega) 2 μ :=
    higherSolutionOperatorLp hOmegaOpen μ S hreg r
  have hbase :=
    (higherSolutionOperatorLp_base hOmegaOpen μ S hreg r).trans hweak
  obtain ⟨hUtop, hUbound⟩ :=
    higherSolutionOperatorLp_memLp_top hOmegaOpen μ S hreg r C hr
  exact ⟨U, hbase, hUtop, hUbound⟩

/-! ## The proved `m = 0` base case -/

/--
The qualitative `L² → H²` theorem supplies
`HasHigherSolutionLift` at order zero.

An `H^0` Sobolev family contains only its base `L²` coordinate, so the
representative theorem gives the required existential statement
directly.
-/
theorem hasHigherSolutionLift_zero
    (S : L2 →L[ℝ] H¹₀(Omega))
    (hreg0 : ∀ f : L2, ∃ W : W^{2,2}(Omega),
      ⇑(wkpBaseCoordinateCLM
          (n := n) (m := 2) (p := 2) (Ω := Omega) W)
        =ᵐ[domainMeasure n Omega]
          ⇑(wkpBaseCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Omega)
            (h10SubtypeL
              (n := n) (Ω := Omega) (S f)))) :
    HasHigherSolutionLift (n := n) (Omega := Omega) 0 S := by
  intro f
  obtain ⟨W, hW⟩ :=
    hreg0
      (wkpBaseCoordinateCLM
        (n := n) (m := 0) (p := 2) (Ω := Omega) f)
  refine ⟨W, ?_⟩
  apply Lp.ext
  simpa [higherWeakSolutionBaseCLM] using hW

end

attribute [inherit_doc orderZeroAmbientCLM] orderZeroAmbientCLM.eq_1
attribute [inherit_doc orderZeroSobolevCLM] orderZeroSobolevCLM.eq_1
attribute [inherit_doc higherWeakSolutionBaseCLM] higherWeakSolutionBaseCLM.eq_1

end SobolevSpace.GraphSpace
