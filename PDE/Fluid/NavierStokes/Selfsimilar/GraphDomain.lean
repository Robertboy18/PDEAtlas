/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.DilationDrift
public import PDE.Analysis.Evolution.Galerkin.Restriction

/-!
# The graph domain of the self-similar linearization

The linearization of the self-similar Navier–Stokes equation contains the dilation drift `-½ x·∇`,
which is not a bounded form on `H¹(ℝⁿ)ⁿ`: translates of a fixed field far from the origin make
`∫ (x·∇h)·k` arbitrarily large compared with `‖h‖ ‖k‖`. Its weak realization therefore lives on a
graph domain. For coefficients with bounded components every other term of the linearization is
bounded on the energy space, so the graph domain of the drift is the graph domain of the
linearization for each such coefficient.

## Main definitions

* `DilationTestSpace`: a linear space of smooth compactly supported vector fields on `ℝⁿ` that is
  invariant under the dilations `φ ↦ φ(s ·)`, `s > 0`, for example all divergence-free test fields
  or the test fields of a symmetry sector. Its closed span `E` in vector `H¹`
  (`DilationTestSpace.space`) is the energy space.
* `testedDrift`: the tested drift `h ↦ ∫ (x·∇h)·φ`, a continuous linear functional on vector `H¹`
  for each test field `φ`.
* `DilationTestSpace.graphDomain`: the `h ∈ E` for which `φ ↦ ∫ (x·∇h)·φ` extends from the test
  fields to a continuous linear functional `DilationTestSpace.dilationDrift h` on `E`.
* `DilationTestSpace.ballSpace`: the closed span of the test fields supported in the ball of radius
  `R`.

## Main results

* `DilationTestSpace.dilationDrift_self`: the formal identity `⟨x·∇h, h⟩ = -(n/2) ‖h‖²_{L²}` on the
  graph domain, with no weight on `h`; `inner_dilation_eq` writes the mass as a squared norm.
* `DilationTestSpace.mem_graphDomain_of_mem_ballSpace` and
  `DilationTestSpace.dilationDrift_of_mem_ballSpace`: each ball space lies in the graph domain, and
  on it the drift is the bounded truncated form `cutoffDrift R`.

## How it works

On a test field the drift moves across by integration by parts, `⟨h, x·∇φ⟩ = -∫ (x·∇h)·φ - n ∫ h·φ`
(`sum_integral_base_mul_fderiv_apply_self`). For `h` in the graph domain the pairing `φ ↦ ⟨h, x·∇φ⟩`
therefore agrees on the test fields with a continuous linear functional on `E`, which we extend to
vector `H¹` by the orthogonal projection onto `E`. The dilation identity
`drift_eq_neg_half_mul_massPairing` then gives `DilationTestSpace.dilationDrift_self`; it integrates
the drift along the dilation group and compares two one-sided inequalities. For the ball spaces the
weight `xⱼ` is bounded on the ball, so `cutoffDrift R` is a bounded bilinear form. It equals the
tested drift on test fields supported in the ball (`cutoffDrift_testFieldH1`), and continuity
carries this to the closed span (`DilationTestSpace.cutoffDrift_toH1`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- A space of test fields for the self-similar linearization: a linear space of smooth
compactly supported vector fields on `ℝ^n` that is invariant under the dilations
`φ ↦ φ(s ·)`, `s > 0`. -/
structure DilationTestSpace (n : ℕ) where
  /-- The test fields. -/
  carrier : Submodule ℝ (ℝ^n → ℝ^n)
  contDiff : ∀ φ ∈ carrier, ContDiff ℝ ∞ φ
  hasCompactSupport : ∀ φ ∈ carrier, HasCompactSupport φ
  comp_smul_mem : ∀ φ ∈ carrier, ∀ s : ℝ, 0 < s → (fun x ↦ φ (s • x)) ∈ carrier

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The `H¹` field of a test field. -/
def toH1 (φ : T.carrier) : H :=
  testFieldH1 φ (T.contDiff φ φ.2) (T.hasCompactSupport φ φ.2)

/-- The `H¹` embedding of the test fields as a linear map. -/
def toH1Linear : T.carrier →ₗ[ℝ] H where
  toFun := T.toH1
  map_add' _ _ := testFieldH1_add _ _ _ _ _ _
  map_smul' c _ := testFieldH1_smul c _ _ _ _

theorem toH1Linear_apply (φ : T.carrier) : T.toH1Linear φ = T.toH1 φ :=
  rfl

/-- The closed span of the test fields in vector `H¹`. -/
def space : Submodule ℝ H :=
  (LinearMap.range T.toH1Linear).topologicalClosure

instance : CompleteSpace T.space :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- A test field as a point of the closed span. -/
def point (φ : T.carrier) : T.space :=
  ⟨T.toH1 φ, Submodule.le_topologicalClosure _ ⟨φ, rfl⟩⟩

@[simp]
theorem coe_point (φ : T.carrier) : (T.point φ : H) = T.toH1 φ :=
  rfl

theorem point_add (φ ψ : T.carrier) : T.point (φ + ψ) = T.point φ + T.point ψ :=
  Subtype.ext (T.toH1Linear.map_add φ ψ)

theorem point_smul (c : ℝ) (φ : T.carrier) : T.point (c • φ) = c • T.point φ :=
  Subtype.ext (T.toH1Linear.map_smul c φ)

/-- The test fields are dense in their closed span. -/
theorem denseRange_point : DenseRange T.point := by
  intro v
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage,
    ← Set.range_comp]
  have hv : (v : H) ∈ ((LinearMap.range T.toH1Linear).topologicalClosure : Set H) := v.2
  rw [Submodule.topologicalClosure_coe, LinearMap.coe_range] at hv
  exact hv

/-- Continuous linear functionals on the closed span agree once they agree on test fields. -/
theorem ext_point {f g : StrongDual ℝ T.space} (h : ∀ φ, f (T.point φ) = g (T.point φ)) :
    f = g :=
  ContinuousLinearMap.ext fun v ↦ congrFun (Continuous.ext_on T.denseRange_point f.continuous
    g.continuous (by rintro _ ⟨φ, rfl⟩; exact h φ)) v

/-- The closed span is the closed span of the test fields in the form used by the dilation
identity. -/
theorem span_testFieldsOf :
    Submodule.span ℝ (testFieldsOf (· ∈ T.carrier)) = LinearMap.range T.toH1Linear := by
  have hset : testFieldsOf (n := n) (· ∈ T.carrier) = (LinearMap.range T.toH1Linear : Set H) := by
    ext v
    constructor
    · rintro ⟨φ, _, _, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨φ, T.contDiff φ φ.2, T.hasCompactSupport φ φ.2, φ.2, rfl⟩
  rw [hset, Submodule.span_eq]

end DilationTestSpace

/-! ### The tested drift -/

section TestedDrift

variable {φ : ℝ^n → ℝ^n}

theorem memLp_driftWeight (hφ : Continuous φ) (hc : HasCompactSupport φ) (i j : Fin n) :
    MemLp (fun x : ℝ^n ↦ x j * φ x i) 2 (domainMeasure n univ) := by
  have hcont : Continuous (fun x : ℝ^n ↦ x j * φ x i) :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).continuous.mul
      ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).continuous.comp hφ)
  have hsupp : HasCompactSupport (fun x : ℝ^n ↦ x j * φ x i) :=
    (hasCompactSupport_component hc i).mul_left (f := fun x : ℝ^n ↦ x j)
  simpa [domainMeasure] using hcont.memLp_of_hasCompactSupport hsupp

/-- The weight `x ↦ xⱼ φᵢ(x)` of the tested drift, as an `L²` function. -/
def driftWeight (hφ : Continuous φ) (hc : HasCompactSupport φ) (i j : Fin n) :
    DerivLp n 2 univ :=
  (memLp_driftWeight hφ hc i j).toLp _

theorem driftWeight_ae (hφ : Continuous φ) (hc : HasCompactSupport φ) (i j : Fin n) :
    (driftWeight hφ hc i j : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ x j * φ x i := by
  have h := MemLp.coeFn_toLp (memLp_driftWeight hφ hc i j)
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The tested dilation drift `v ↦ ∫ (x·∇v)·φ = Σᵢⱼ ∫ xⱼ ∂ⱼvᵢ φᵢ` against a continuous
compactly supported field `φ`, a continuous linear functional of `v` in vector `H¹`. -/
def testedDrift (hφ : Continuous φ) (hc : HasCompactSupport φ) : StrongDual ℝ H :=
  ∑ i, ∑ j, (innerSL ℝ (driftWeight hφ hc i j)).comp
    ((wkpCoordinateCLM (singleDerivIndex n j)).comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i))

theorem testedDrift_apply_inner (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : H) :
    testedDrift hφ hc v = ∑ i, ∑ j,
      inner ℝ (driftWeight hφ hc i j) (wkpCoordinateCLM (singleDerivIndex n j) (v i)) := by
  simp only [testedDrift, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    PiLp.proj_apply]

theorem testedDrift_apply (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : H) :
    testedDrift hφ hc v = ∑ i, ∑ j, ∫ x, x j *
      (wkpCoordinateCLM (singleDerivIndex n j) (v i) : ℝ^n → ℝ) x * φ x i := by
  simp only [testedDrift, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_eq_integral_mul_of_ae (driftWeight_ae hφ hc i j) (Filter.EventuallyEq.refl _ _)]
  congr 1
  funext x
  ring

/-- Integration by parts in the drift pairing:
`Σᵢ ∫ vᵢ (Dφ(x) x)ᵢ = -∫ (x·∇v)·φ - n ∫ v·φ`. -/
theorem sum_integral_base_mul_fderiv_apply_self (v : H) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (v i) : ℝ^n → ℝ) x * fderiv ℝ φ x x i =
      -testedDrift hφ.continuous hc v - n * massPairing v (testFieldH1 φ hφ hc) := by
  rw [testedDrift_apply, massPairing_testFieldH1, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set b : ℝ^n → ℝ := (wkpBaseCoordinateCLM (v i) : ℝ^n → ℝ)
  set f : ℝ^n → ℝ := fun y ↦ φ y i
  have hf : ContDiff ℝ ∞ f := contDiff_component hφ i
  have hfc : HasCompactSupport f := hasCompactSupport_component hc i
  have hproj : ∀ j : Fin n, ContDiff ℝ ∞ (fun x : ℝ^n ↦ x j) := fun j ↦
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).contDiff
  have hψ : ∀ j : Fin n, ContDiff ℝ ∞ (fun x : ℝ^n ↦ x j * f x) := fun j ↦ (hproj j).mul hf
  have hψc : ∀ j : Fin n, HasCompactSupport (fun x : ℝ^n ↦ x j * f x) := fun j ↦
    hfc.mul_left (f := fun x : ℝ^n ↦ x j)
  have hderiv : ∀ (j : Fin n) (x : ℝ^n),
      PDE.partialDeriv j (fun y : ℝ^n ↦ y j * f y) x = f x + x j * PDE.partialDeriv j f x := by
    intro j x
    rw [PDE.partialDeriv_mul ((hproj j).differentiable (by simp) x)
      (hf.differentiable (by simp) x), PDE.partialDeriv_coord]
    simp
  have hfd : ∀ x, fderiv ℝ φ x x i = ∑ j, x j * PDE.partialDeriv j f x := by
    intro x
    have hcomp : fderiv ℝ φ x x i = fderiv ℝ f x x := by
      have := ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp x
        ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv
      rw [show f = (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) ∘ φ from rfl, this]
      rfl
    rw [hcomp, PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hdcont : ∀ j : Fin n, Continuous (fun x : ℝ^n ↦ x j * PDE.partialDeriv j f x) :=
    fun j ↦ (hproj j).continuous.mul (PDE.contDiff_top_partialDeriv (i := j) hf).continuous
  have hint1 : ∀ j : Fin n, Integrable (fun x ↦ b x * (x j * PDE.partialDeriv j f x)) :=
    fun j ↦ integrable_base_mul (v i) (hdcont j) ((hfc.partialDeriv j).mul_left)
  have hint2 : Integrable (fun x ↦ b x * f x) := integrable_base_mul (v i) hf.continuous hfc
  have hstep : ∀ j : Fin n, ∫ x, b x * (x j * PDE.partialDeriv j f x) =
      -(∫ x, x j * (wkpCoordinateCLM (singleDerivIndex n j) (v i) : ℝ^n → ℝ) x * f x) -
        ∫ x, b x * f x := by
    intro j
    have hibp := integral_base_mul_partialDeriv (v i) j (hψ j) (hψc j)
    have hsplit : ∫ x, b x * PDE.partialDeriv j (fun y : ℝ^n ↦ y j * f y) x =
        (∫ x, b x * f x) + ∫ x, b x * (x j * PDE.partialDeriv j f x) := by
      have hfun : (fun x ↦ b x * PDE.partialDeriv j (fun y : ℝ^n ↦ y j * f y) x) =
          fun x ↦ b x * f x + b x * (x j * PDE.partialDeriv j f x) := by
        funext x
        rw [hderiv, mul_add]
      rw [hfun]
      exact integral_add hint2 (hint1 j)
    have hswap : ∫ x, (wkpCoordinateCLM (singleDerivIndex n j) (v i) : ℝ^n → ℝ) x *
        (x j * f x) = ∫ x, x j * (wkpCoordinateCLM (singleDerivIndex n j) (v i) : ℝ^n → ℝ) x *
          f x := by
      congr 1
      funext x
      ring
    rw [hsplit, hswap] at hibp
    linarith
  calc ∫ x, b x * fderiv ℝ φ x x i = ∫ x, ∑ j, b x * (x j * PDE.partialDeriv j f x) := by
        congr 1
        funext x
        rw [hfd, Finset.mul_sum]
    _ = ∑ j, ∫ x, b x * (x j * PDE.partialDeriv j f x) :=
        integral_finsetSum _ fun j _ ↦ hint1 j
    _ = ∑ j, (-(∫ x, x j * (wkpCoordinateCLM (singleDerivIndex n j) (v i) : ℝ^n → ℝ) x * f x) -
          ∫ x, b x * f x) := Finset.sum_congr rfl fun j _ ↦ hstep j
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]

end TestedDrift

/-! ### Bilinear forms on the closed span -/

/-- The `L²` pairing `(u, v) ↦ ∫ u·v` on vector `H¹`. -/
def massForm : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp massCLM massCLM

theorem massForm_apply (u v : H) : massForm u v = massPairing u v := by
  simp only [massForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    PiLp.inner_apply, massPairing]
  rfl

theorem massPairing_self_eq_norm_sq (u : H) : massPairing u u = ‖massCLM u‖ ^ 2 := by
  rw [← massForm_apply, massForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The tested drift `h ↦ ∫ (x·∇h)·φ` at a test field `φ` of the space. -/
def driftAt (φ : T.carrier) : StrongDual ℝ H :=
  testedDrift (T.contDiff φ φ.2).continuous (T.hasCompactSupport φ φ.2)

/-- The graph domain of the weak self-similar linearization on the closed span `E` of the test
fields: the fields `h ∈ E` whose tested drift `φ ↦ ∫ (x·∇h)·φ` extends from the test fields to a
continuous linear functional on `E`. -/
def graphDomain : Submodule ℝ T.space where
  carrier := {h | ∃ g : StrongDual ℝ T.space, ∀ φ, g (T.point φ) = T.driftAt φ (h : H)}
  add_mem' := by
    rintro u v ⟨g, hg⟩ ⟨g', hg'⟩
    exact ⟨g + g', fun φ ↦ by
      rw [add_apply, hg, hg', Submodule.coe_add, map_add]⟩
  zero_mem' := ⟨0, fun φ ↦ by rw [zero_apply, ZeroMemClass.coe_zero,
    map_zero]⟩
  smul_mem' := by
    rintro c u ⟨g, hg⟩
    exact ⟨c • g, fun φ ↦ by
      rw [smul_apply, hg, Submodule.coe_smul, map_smul]⟩

theorem exists_dilationDrift (h : T.graphDomain) :
    ∃ g : StrongDual ℝ T.space, ∀ φ, g (T.point φ) = T.driftAt φ ((h : T.space) : H) :=
  h.2

/-- The dilation drift `⟨x·∇h, ·⟩` of a field of the graph domain: the continuous linear
functional on `E` extending its tested drift. -/
def dilationDrift : T.graphDomain →ₗ[ℝ] StrongDual ℝ T.space where
  toFun h := (T.exists_dilationDrift h).choose
  map_add' u v := T.ext_point fun φ ↦ by
    rw [(T.exists_dilationDrift (u + v)).choose_spec φ, add_apply,
      (T.exists_dilationDrift u).choose_spec φ, (T.exists_dilationDrift v).choose_spec φ,
      Submodule.coe_add, Submodule.coe_add, map_add]
  map_smul' c u := T.ext_point fun φ ↦ by
    rw [(T.exists_dilationDrift (c • u)).choose_spec φ, RingHom.id_apply,
      smul_apply, (T.exists_dilationDrift u).choose_spec φ,
      Submodule.coe_smul, Submodule.coe_smul, map_smul]

theorem dilationDrift_point (h : T.graphDomain) (φ : T.carrier) :
    T.dilationDrift h (T.point φ) = T.driftAt φ ((h : T.space) : H) :=
  (T.exists_dilationDrift h).choose_spec φ

/-- The dilation drift is the only continuous extension of the tested drift. -/
theorem dilationDrift_eq (h : T.graphDomain) {g : StrongDual ℝ T.space}
    (hg : ∀ φ, g (T.point φ) = T.driftAt φ ((h : T.space) : H)) : T.dilationDrift h = g :=
  T.ext_point fun φ ↦ by rw [dilationDrift_point, hg]

/-- The dilation identity `⟨x·∇h, h⟩ = -(n/2) ‖h‖²_{L²}` on the graph domain. -/
theorem dilationDrift_self (h : T.graphDomain) :
    T.dilationDrift h h =
      -((n : ℝ) / 2) * massPairing ((h : T.space) : H) ((h : T.space) : H) := by
  set Ψ₀ : StrongDual ℝ T.space := -T.dilationDrift h - (n : ℝ) • restrictForm T.space massForm h
  set Ψ : StrongDual ℝ H := Ψ₀.comp T.space.orthogonalProjectionOnto
  have hΨ : ∀ v : T.space, Ψ v = Ψ₀ v := fun v ↦ by
    simp only [Ψ, ContinuousLinearMap.comp_apply,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hΨ₀ : ∀ v : T.space,
      Ψ₀ v = -T.dilationDrift h v - n * massPairing ((h : T.space) : H) v := by
    intro v
    simp only [Ψ₀, sub_apply, neg_apply,
      smul_apply, restrictForm_apply, massForm_apply, smul_eq_mul]
  have hΛ : ∀ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      φ ∈ T.carrier → ∑ i, ∫ x, (wkpBaseCoordinateCLM (((h : T.space) : H) i) : ℝ^n → ℝ) x *
        fderiv ℝ φ x x i = Ψ (testFieldH1 φ hφ hc) := by
    intro φ hφ hc hT
    rw [sum_integral_base_mul_fderiv_apply_self _ hφ hc]
    have hpt : testFieldH1 φ hφ hc = (T.point ⟨φ, hT⟩ : H) := rfl
    rw [hpt, hΨ, hΨ₀, dilationDrift_point]
    rfl
  have hd : ((h : T.space) : H) ∈
      (Submodule.span ℝ (testFieldsOf (· ∈ T.carrier))).topologicalClosure := by
    rw [T.span_testFieldsOf]
    exact (h : T.space).2
  have hid := drift_eq_neg_half_mul_massPairing (· ∈ T.carrier)
    (fun φ _ hφ s hs ↦ T.comp_smul_mem φ hφ s hs) _ Ψ hΛ hd
  rw [hΨ (h : T.space), hΨ₀] at hid
  linarith

end DilationTestSpace

/-! ### The drift truncated to a ball -/

section Cutoff

theorem memLp_ballWeight (R : ℝ) (j : Fin n) :
    MemLp ((Metric.ball (0 : ℝ^n) R).indicator fun x ↦ x j) ∞ (domainMeasure n univ) := by
  refine memLp_top_of_bound ?_ |R| ?_
  · exact ((EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).continuous.measurable.indicator
      Metric.isOpen_ball.measurableSet).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ Metric.ball (0 : ℝ^n) R
    · rw [indicator_of_mem hx]
      have hxR : ‖x‖ < R := by simpa using hx
      exact (PiLp.norm_apply_le x j).trans (hxR.le.trans (le_abs_self R))
    · rw [indicator_of_notMem hx, norm_zero]
      exact abs_nonneg R

/-- The bounded weight `x ↦ xⱼ` on the ball of radius `R`, extended by zero. -/
def ballWeight (R : ℝ) (j : Fin n) : DerivLp n ∞ univ :=
  (memLp_ballWeight R j).toLp _

theorem ballWeight_ae (R : ℝ) (j : Fin n) :
    (ballWeight R j : ℝ^n → ℝ) =ᵐ[volume] (Metric.ball (0 : ℝ^n) R).indicator fun x ↦ x j := by
  have h := MemLp.coeFn_toLp (memLp_ballWeight (n := n) R j)
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The drift truncated to the ball of radius `R`, `(v, w) ↦ Σᵢⱼ ∫_{|x| < R} xⱼ ∂ⱼvᵢ wᵢ`, a
bounded bilinear form on vector `H¹`. -/
def cutoffDrift (R : ℝ) : H →L[ℝ] H →L[ℝ] ℝ :=
  ∑ i, ∑ j, (innerSL ℝ).bilinearComp
    ((mulLpLeft (ballWeight R j)).comp ((wkpCoordinateCLM (singleDerivIndex n j)).comp
      (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i)))
    (wkpBaseCoordinateCLM.comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i))

/-- For a test field supported in the ball, the truncated drift is the tested drift. -/
theorem cutoffDrift_testFieldH1 {R : ℝ} {φ ψ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφR : tsupport φ ⊆ Metric.ball 0 R) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    cutoffDrift R (testFieldH1 φ hφ hcφ) (testFieldH1 ψ hψ hcψ) =
      testedDrift hψ.continuous hcψ (testFieldH1 φ hφ hcφ) := by
  rw [testedDrift_apply]
  simp only [cutoffDrift, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hmul := mulLpLeft_apply_ae (ballWeight R j)
    (wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hcφ i))
  simp only [domainMeasure, Measure.restrict_univ] at hmul
  rw [inner_eq_integral_mul_of_ae hmul (testFieldH1_base_ae hψ hcψ i)]
  apply integral_congr_ae
  filter_upwards [ballWeight_ae (n := n) R j, testFieldH1_partial_ae hφ hcφ i j] with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ Metric.ball (0 : ℝ^n) R
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hxφ : x ∉ tsupport (fun y ↦ φ y i) := fun hmem ↦
      hx (hφR (tsupport_comp_subset (g := fun v : ℝ^n ↦ v i) (by simp) φ hmem))
    have hzero : PDE.partialDeriv j (fun y ↦ φ y i) x = 0 := by
      simp [PDE.partialDeriv, fderiv_of_notMem_tsupport ℝ hxφ]
    rw [hzero]
    ring

end Cutoff

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The closed span of the test fields supported in the ball of radius `R`. -/
def ballSpace (R : ℝ) : Submodule ℝ T.space :=
  (Submodule.span ℝ {v | ∃ φ : T.carrier, tsupport (φ : ℝ^n → ℝ^n) ⊆ Metric.ball 0 R ∧
    T.point φ = v}).topologicalClosure

instance (R : ℝ) : CompleteSpace (T.ballSpace R) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem point_mem_ballSpace {R : ℝ} {φ : T.carrier}
    (h : tsupport (φ : ℝ^n → ℝ^n) ⊆ Metric.ball 0 R) : T.point φ ∈ T.ballSpace R :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, h, rfl⟩)

/-- Every test field lies in the ball spaces of all large radii. -/
theorem eventually_point_mem_ballSpace (φ : T.carrier) :
    ∀ᶠ R : ℕ in atTop, T.point φ ∈ T.ballSpace R := by
  obtain ⟨r, hr⟩ := (T.hasCompactSupport φ φ.2).isCompact.isBounded.subset_ball 0
  obtain ⟨N, hN⟩ := exists_nat_ge r
  filter_upwards [eventually_ge_atTop N] with R hR
  exact T.point_mem_ballSpace
    (hr.trans (Metric.ball_subset_ball (hN.trans (by exact_mod_cast hR))))

/-- On the ball space of radius `R`, the truncated drift agrees with the tested drift. -/
theorem cutoffDrift_toH1 {R : ℝ} {v : T.space} (hv : v ∈ T.ballSpace R) (ψ : T.carrier) :
    cutoffDrift R (v : H) (T.toH1 ψ) = T.driftAt ψ (v : H) := by
  set g : StrongDual ℝ T.space := ((cutoffDrift R).flip (T.toH1 ψ)).comp T.space.subtypeL -
    (T.driftAt ψ).comp T.space.subtypeL
  have hle : T.ballSpace R ≤ g.ker := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) g.isClosed_ker
    rintro _ ⟨φ, hφ, rfl⟩
    change g (T.point φ) = 0
    simp only [g, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      Submodule.subtypeL_apply, coe_point]
    rw [sub_eq_zero]
    exact cutoffDrift_testFieldH1 _ _ hφ _ _
  have h0 : g v = 0 := hle hv
  simp only [g, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Submodule.subtypeL_apply] at h0
  exact sub_eq_zero.mp h0

/-- Fields of a ball space lie in the graph domain. -/
theorem mem_graphDomain_of_mem_ballSpace {R : ℝ} {v : T.space} (hv : v ∈ T.ballSpace R) :
    v ∈ T.graphDomain :=
  ⟨restrictForm T.space (cutoffDrift R) v, fun ψ ↦ T.cutoffDrift_toH1 hv ψ⟩

/-- On a ball space the dilation drift is the truncated drift. -/
theorem dilationDrift_of_mem_ballSpace {R : ℝ} (h : T.graphDomain)
    (hv : (h : T.space) ∈ T.ballSpace R) :
    T.dilationDrift h = restrictForm T.space (cutoffDrift R) h :=
  T.dilationDrift_eq h fun ψ ↦ T.cutoffDrift_toH1 hv ψ

theorem point_mem_graphDomain (φ : T.carrier) : T.point φ ∈ T.graphDomain := by
  obtain ⟨R, hR⟩ := (T.eventually_point_mem_ballSpace φ).exists
  exact T.mem_graphDomain_of_mem_ballSpace hR

/-- A test field as a point of the graph domain. -/
def graphPoint (φ : T.carrier) : T.graphDomain :=
  ⟨T.point φ, T.point_mem_graphDomain φ⟩

@[simp]
theorem coe_graphPoint (φ : T.carrier) : (T.graphPoint φ : T.space) = T.point φ :=
  rfl

end DilationTestSpace

/-- `dilationDrift_self` with the mass written as the squared `L²` norm, the form
`⟨x·∇h, h⟩ = -(n/2) ‖h‖²` of the package statement. -/
theorem inner_dilation_eq (T : DilationTestSpace n) (h : T.graphDomain) :
    T.dilationDrift h h = -((n : ℝ) / 2) * ‖massCLM ((h : T.space) : H)‖ ^ 2 :=
  (T.dilationDrift_self h).trans (by rw [massPairing_self_eq_norm_sq])

end NavierStokes.Selfsimilar
