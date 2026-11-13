/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphLinearization
public import PDE.Fluid.NavierStokes.Nonuniqueness.WeakEquations
public import PDE.FDeriv.Calculus

/-!
# The graph-domain linearization and the weak eigenvalue equation

`solenoidalTestSpace n` is the space of smooth compactly supported divergence-free fields; for
`n ≥ 1` its closed span is the divergence-free part of vector `H¹`
(`mem_space_solenoidalTestSpace_iff`).

In three dimensions, with `b` the `L∞` class of a field `U`, the weak eigenvalue density
`weakEigenDensity U μ v φ` of `WeakEigenEquation` is integrable and integrates to the tested
form `⟨L_b v, φ⟩ + μ ∫ v·φ` (`integral_weakEigenDensity`). Consequently a solution of
`L_b h + μ J h = 0` in the graph domain satisfies the weak eigenvalue equation against every
test field of its space, and for the solenoidal test fields it satisfies
`WeakEigenEquation U μ h` (`weakEigenEquation_of_linearization_eq`). Conversely a
divergence-free weak eigenfunction lies in the graph domain and solves `L_b h + μ J h = 0`
(`linearization_eq_zero_of_weakEigenEquation`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

section Solenoidal

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- The smooth compactly supported divergence-free vector fields on `ℝ^n`, a dilation-invariant
space of test fields. -/
def solenoidalTestSpace (n : ℕ) : DilationTestSpace n where
  carrier :=
    { carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ∀ x, PDE.divergence φ x = 0}
      add_mem' := fun {φ ψ} hφ hψ ↦ ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, fun x ↦ by
        rw [show φ + ψ = fun y ↦ φ y + ψ y from rfl,
          PDE.divergence_add_of_differentiableAt (hφ.1.differentiable (by simp) x)
            (hψ.1.differentiable (by simp) x),
          hφ.2.2, hψ.2.2, add_zero]⟩
      zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun x ↦ by
        simp [PDE.divergence, PDE.partialDeriv]⟩
      smul_mem' := fun c φ hφ ↦ ⟨hφ.1.const_smul c, hφ.2.1.smul_left, fun x ↦ by
        rw [show c • φ = fun y ↦ c • φ y from rfl, PDE.divergence_const_smul, hφ.2.2,
          mul_zero]⟩ }
  contDiff _ hφ := hφ.1
  hasCompactSupport _ hφ := hφ.2.1
  comp_smul_mem φ hφ s hs := ⟨contDiff_comp_smul hφ.1 s, hasCompactSupport_comp_smul hφ.2.1 hs.ne',
    divergence_comp_smul hφ.1 hφ.2.2 s⟩

theorem mem_solenoidalTestSpace_iff {φ : ℝ^n → ℝ^n} :
    φ ∈ (solenoidalTestSpace n).carrier ↔
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ∀ x, PDE.divergence φ x = 0 :=
  Iff.rfl

/-- For `n ≥ 1` the closed span of the solenoidal test fields is the divergence-free part of
vector `H¹`. -/
theorem mem_space_solenoidalTestSpace_iff (hn : 0 < n) (v : H) :
    v ∈ (solenoidalTestSpace n).space ↔ divergenceCLM v = 0 := by
  have hset : solenoidalTestFields n = testFieldsOf (· ∈ (solenoidalTestSpace n).carrier) := by
    rw [solenoidalTestFields_eq_testFieldsOf]
    ext w
    exact exists_congr fun φ ↦ exists_congr fun hφ ↦ exists_congr fun hc ↦
      and_congr_left' ⟨fun hdiv ↦ ⟨hφ, hc, hdiv⟩, fun hT ↦ hT.2.2⟩
  constructor
  · intro hv
    have hle : (solenoidalTestSpace n).space ≤ (divergenceCLM (n := n)).ker := by
      refine Submodule.topologicalClosure_minimal _ ?_ (divergenceCLM (n := n)).isClosed_ker
      rintro _ ⟨φ, rfl⟩
      exact divergenceCLM_testFieldH1 φ.2.1 φ.2.2.1 φ.2.2.2
    exact hle hv
  · intro hv
    have h := mem_topologicalClosure_span_solenoidalTestFields hn v hv
    rwa [hset, DilationTestSpace.span_testFieldsOf] at h

end Solenoidal

/-! ### The tested linearization as an integral -/

section WeakForm

variable {n : ℕ}

private theorem integrable_and_integral_add {f g : ℝ^n → ℝ} {I J : ℝ}
    (hf : Integrable f ∧ ∫ x, f x = I) (hg : Integrable g ∧ ∫ x, g x = J) :
    Integrable (fun x ↦ f x + g x) ∧ ∫ x, f x + g x = I + J :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2]⟩

private theorem integrable_and_integral_sub {f g : ℝ^n → ℝ} {I J : ℝ}
    (hf : Integrable f ∧ ∫ x, f x = I) (hg : Integrable g ∧ ∫ x, g x = J) :
    Integrable (fun x ↦ f x - g x) ∧ ∫ x, f x - g x = I - J :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1 hg.1, hf.2, hg.2]⟩

private theorem integrable_and_integral_const_mul {f : ℝ^n → ℝ} {I : ℝ} (c : ℝ)
    (hf : Integrable f ∧ ∫ x, f x = I) :
    Integrable (fun x ↦ c * f x) ∧ ∫ x, c * f x = c * I :=
  ⟨hf.1.const_mul c, by rw [integral_const_mul, hf.2]⟩

private theorem integrable_and_integral_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ^n → ℝ} {I : ι → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) ∧ ∫ x, f i x = I i) :
    Integrable (fun x ↦ ∑ i ∈ s, f i x) ∧ ∫ x, ∑ i ∈ s, f i x = ∑ i ∈ s, I i :=
  ⟨integrable_finsetSum s fun i hi ↦ (hf i hi).1, by
    rw [integral_finsetSum s fun i hi ↦ (hf i hi).1]
    exact Finset.sum_congr rfl fun i hi ↦ (hf i hi).2⟩

end WeakForm

section WeakEigen

variable (U : ℝ^3 → ℝ^3) (b : Fin 3 → DerivLp 3 ∞ univ)

/-- The weak eigenvalue density of `WeakEigenEquation` integrates to the tested linearization
with coefficient `b`, when `b` is the `L∞` class of `U`. -/
theorem integral_weakEigenDensity (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i)
    (μ : ℝ) (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    Integrable (Nonuniqueness.weakEigenDensity U μ v φ) ∧
      ∫ x, Nonuniqueness.weakEigenDensity U μ v φ x =
        boundedPart b v (testFieldH1 φ hφ hc) - (1 / 2) * testedDrift hφ.continuous hc v +
          μ * massPairing v (testFieldH1 φ hφ hc) := by
  set r : ℝ^3 → Fin 3 → ℝ := fun x i ↦ Stationary.representative v x i
  set g : ℝ^3 → Fin 3 → Fin 3 → ℝ := fun x i j ↦ Stationary.gradientRepresentative v x i j
  set dφ : ℝ^3 → Fin 3 → Fin 3 → ℝ := fun x i j ↦ PDE.partialDeriv j (fun y ↦ φ y i) x
  have hg : ∀ x i j, g x i j = (wkpCoordinateCLM (singleDerivIndex 3 j) (v i) : ℝ^3 → ℝ) x :=
    fun _ _ _ ↦ rfl
  have hmul (j : Fin 3) (u : DerivLp 3 2 univ) :
      (mulLpLeft (b j) u : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x j * (u : ℝ^3 → ℝ) x := by
    have h := mulLpLeft_apply_ae (b j) u
    simp only [domainMeasure, Measure.restrict_univ] at h
    filter_upwards [h, hb j] with x h1 h2
    rw [h1, h2]
  -- the six kinds of terms
  have a1 : ∀ i, Integrable (fun x ↦ r x i * φ x i) ∧ ∫ x, r x i * φ x i =
      inner ℝ (wkpBaseCoordinateCLM (v i)) (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i)) :=
    fun i ↦ integrable_and_integral_eq_inner (Filter.EventuallyEq.refl _ _)
      (testFieldH1_base_ae hφ hc i) (Eventually.of_forall fun x ↦ rfl)
  have a2 : ∀ i j, Integrable (fun x ↦ U x j * g x i j * φ x i) ∧
      ∫ x, U x j * g x i j * φ x i =
        inner ℝ (mulLpLeft (b j) (wkpCoordinateCLM (singleDerivIndex 3 j) (v i)))
          (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i)) :=
    fun i j ↦ integrable_and_integral_eq_inner (hmul j _) (testFieldH1_base_ae hφ hc i)
      (Eventually.of_forall fun x ↦ rfl)
  have a3 : ∀ i j, Integrable (fun x ↦ x j * g x i j * φ x i) ∧
      ∫ x, x j * g x i j * φ x i =
        inner ℝ (driftWeight hφ.continuous hc i j)
          (wkpCoordinateCLM (singleDerivIndex 3 j) (v i)) :=
    fun i j ↦ integrable_and_integral_eq_inner (driftWeight_ae hφ.continuous hc i j)
      (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by rw [hg]; ring)
  have a4 : ∀ i j, Integrable (fun x ↦ U x i * g x j j * φ x i) ∧
      ∫ x, U x i * g x j j * φ x i =
        inner ℝ (mulLpLeft (b i) (wkpCoordinateCLM (singleDerivIndex 3 j) (v j)))
          (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i)) :=
    fun i j ↦ integrable_and_integral_eq_inner (hmul i _) (testFieldH1_base_ae hφ hc i)
      (Eventually.of_forall fun x ↦ rfl)
  have a5 : ∀ i j, Integrable (fun x ↦ U x i * r x j * dφ x i j) ∧
      ∫ x, U x i * r x j * dφ x i j =
        inner ℝ (mulLpLeft (b i) (wkpBaseCoordinateCLM (v j)))
          (wkpCoordinateCLM (singleDerivIndex 3 j) (testFieldH1 φ hφ hc i)) :=
    fun i j ↦ integrable_and_integral_eq_inner (hmul i _) (testFieldH1_partial_ae hφ hc i j)
      (Eventually.of_forall fun x ↦ rfl)
  have a6 : ∀ i j, Integrable (fun x ↦ g x i j * dφ x i j) ∧
      ∫ x, g x i j * dφ x i j =
        inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 j) (v i))
          (wkpCoordinateCLM (singleDerivIndex 3 j) (testFieldH1 φ hφ hc i)) :=
    fun i j ↦ integrable_and_integral_eq_inner (Filter.EventuallyEq.refl _ _)
      (testFieldH1_partial_ae hφ hc i j) (Eventually.of_forall fun x ↦ rfl)
  -- the density as a structured sum of these terms
  have hdens : Nonuniqueness.weakEigenDensity U μ v φ = fun x ↦
      ∑ i, ((μ - 1 / 2) * (r x i * φ x i) +
      ∑ j, (U x j * g x i j * φ x i - (1 / 2) * (x j * g x i j * φ x i) -
        U x i * g x j j * φ x i - U x i * r x j * dφ x i j + g x i j * dφ x i j)) := by
    funext x
    rw [Nonuniqueness.weakEigenDensity_eq_sum U μ v (hφ.of_le (by simp)) x]
    simp only [r, g, dφ, Fin.sum_univ_three]
    ring
  obtain ⟨hint, hval⟩ := integrable_and_integral_sum Finset.univ fun i _ ↦
    integrable_and_integral_add (integrable_and_integral_const_mul (μ - 1 / 2) (a1 i))
      (integrable_and_integral_sum _ fun j _ ↦ integrable_and_integral_add
        (integrable_and_integral_sub (integrable_and_integral_sub (integrable_and_integral_sub
          (a2 i j) (integrable_and_integral_const_mul (1 / 2) (a3 i j))) (a4 i j)) (a5 i j))
        (a6 i j))
  rw [hdens]
  refine ⟨hint, ?_⟩
  rw [hval, boundedPart_apply, gradientForm_apply, convectionForm_apply, testedDrift_apply_inner,
    massPairing]
  simp only [Fin.sum_univ_three]
  ring

namespace DilationTestSpace

variable (T : DilationTestSpace 3)

/-- Tested against a test field, the shifted linearization on the graph domain is the integral
of the weak eigenvalue density. -/
theorem integral_weakEigenDensity_point (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i)
    (μ : ℝ) (h : T.graphDomain) (φ : T.carrier) :
    Integrable (Nonuniqueness.weakEigenDensity U μ ((h : T.space) : _) φ) ∧
      ∫ x, Nonuniqueness.weakEigenDensity U μ ((h : T.space) : _) φ x =
        (T.linearization b h + μ • T.l2Form h) (T.point φ) := by
  obtain ⟨hint, hval⟩ := integral_weakEigenDensity U b hb μ ((h : T.space) : _)
    (T.contDiff φ φ.2) (T.hasCompactSupport φ φ.2)
  refine ⟨hint, hval.trans ?_⟩
  rw [add_apply, T.linearization_point, smul_apply, smul_eq_mul, l2Form_apply]
  rfl

/-- A solution of `L h + μ J h = 0` in the graph domain satisfies the weak eigenvalue equation
against every test field of the space. -/
theorem weakEigen_of_linearization_eq (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i)
    {μ : ℝ} {h : T.graphDomain} (heq : T.linearization b h + μ • T.l2Form h = 0)
    (φ : T.carrier) :
    Integrable (Nonuniqueness.weakEigenDensity U μ ((h : T.space) : _) φ) ∧
      ∫ x, Nonuniqueness.weakEigenDensity U μ ((h : T.space) : _) φ x = 0 := by
  obtain ⟨hint, hval⟩ := T.integral_weakEigenDensity_point U b hb μ h φ
  rw [heq, zero_apply] at hval
  exact ⟨hint, hval⟩

/-- A field of the closed span whose weak eigenvalue density integrates to zero against every
test field lies in the graph domain. -/
theorem mem_graphDomain_of_weakEigen (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i)
    {μ : ℝ} {v : T.space}
    (hv : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U μ (v : _) φ x = 0) :
    v ∈ T.graphDomain := by
  refine ⟨(2 : ℝ) • (restrictForm T.space (boundedPart b) v + μ • T.l2Form v), fun φ ↦ ?_⟩
  have h := (integral_weakEigenDensity U b hb μ (v : _) (T.contDiff φ φ.2)
    (T.hasCompactSupport φ φ.2)).2
  rw [hv φ] at h
  rw [smul_apply, add_apply, smul_apply, smul_eq_mul, smul_eq_mul, restrictForm_apply, l2Form_apply]
  change 2 * (boundedPart b (v : _) (T.toH1 φ) + μ * massPairing (v : _) (T.toH1 φ)) =
    T.driftAt φ (v : _)
  change 0 = boundedPart b (v : _) (T.toH1 φ) - 1 / 2 * T.driftAt φ (v : _) +
    μ * massPairing (v : _) (T.toH1 φ) at h
  linarith

/-- A field of the closed span whose weak eigenvalue density integrates to zero against every
test field solves `L h + μ J h = 0` in the graph domain. -/
theorem linearization_eq_zero_of_weakEigen (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i)
    {μ : ℝ} {v : T.space}
    (hv : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U μ (v : _) φ x = 0) :
    T.linearization b ⟨v, T.mem_graphDomain_of_weakEigen U b hb hv⟩ + μ • T.l2Form v = 0 :=
  T.ext_point fun φ ↦ by
    rw [← (T.integral_weakEigenDensity_point U b hb μ ⟨v, T.mem_graphDomain_of_weakEigen U b hb hv⟩
      φ).2, zero_apply]
    exact hv φ

end DilationTestSpace

/-- For the solenoidal test fields, a solution of `L h + μ J h = 0` in the graph domain is a
weak eigenfunction: `WeakEigenEquation U μ h`. -/
theorem weakEigenEquation_of_linearization_eq
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i) {μ : ℝ}
    {h : (solenoidalTestSpace 3).graphDomain}
    (heq : (solenoidalTestSpace 3).linearization b h + μ • (solenoidalTestSpace 3).l2Form h = 0) :
    Nonuniqueness.WeakEigenEquation U μ ((h : (solenoidalTestSpace 3).space) : _) :=
  fun φ hφ ↦ (solenoidalTestSpace 3).weakEigen_of_linearization_eq U b hb heq ⟨φ, hφ⟩

/-- A divergence-free weak eigenfunction lies in the graph domain of the solenoidal test fields
and solves `L h + μ J h = 0` there. -/
theorem linearization_eq_zero_of_weakEigenEquation
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i) {μ : ℝ}
    {v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hdiv : divergenceCLM v = 0)
    (hv : Nonuniqueness.WeakEigenEquation U μ v) :
    ∃ h : (solenoidalTestSpace 3).graphDomain, ((h : (solenoidalTestSpace 3).space) : _) = v ∧
      (solenoidalTestSpace 3).linearization b h + μ • (solenoidalTestSpace 3).l2Form h = 0 := by
  have hmem : v ∈ (solenoidalTestSpace 3).space :=
    (mem_space_solenoidalTestSpace_iff (by norm_num) v).mpr hdiv
  have hv' : ∀ φ : (solenoidalTestSpace 3).carrier,
      ∫ x, Nonuniqueness.weakEigenDensity U μ v φ x = 0 := fun φ ↦ (hv φ φ.2).2
  exact ⟨⟨⟨v, hmem⟩, (solenoidalTestSpace 3).mem_graphDomain_of_weakEigen U b hb
    (v := ⟨v, hmem⟩) hv'⟩, rfl,
    (solenoidalTestSpace 3).linearization_eq_zero_of_weakEigen U b hb (v := ⟨v, hmem⟩) hv'⟩

end WeakEigen

end NavierStokes.Selfsimilar
