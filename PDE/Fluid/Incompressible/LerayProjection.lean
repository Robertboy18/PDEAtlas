/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# The whole-space Leray projection

The divergence-free `L²` subspace is the orthogonal complement of the span of
smooth compactly supported scalar gradients. Membership is proved equivalent
to the library's distributional incompressibility condition, including its
integrability clause. Orthogonal projection gives the concrete whole-space
Leray operator, preserves pairings with divergence-free tests, and is contractive.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory
open scoped BigOperators ENNReal Distributions Sobolev RealInnerProductSpace

/-- The whole-space Euclidean `L²` pivot, with the library's univ-domain measure. -/
abbrev WholeSpaceL2 (n : ℕ) := Lp (ℝ^n) 2 (domainMeasure n Set.univ)

/-- The `L²` gradient of a smooth compactly supported scalar test. -/
def l2TestGradient {n : ℕ} (φ : TestFunctionOn n Set.univ) : WholeSpaceL2 n :=
  gradientCLM (testFunctionToH10 φ)

/-- Test gradients retain all classical partial derivatives almost everywhere. -/
theorem l2TestGradient_apply_ae {n : ℕ} (φ : TestFunctionOn n Set.univ) :
    ∀ᵐ x ∂domainMeasure n Set.univ, ∀ i : Fin n,
      l2TestGradient φ x i = PDE.partialDeriv i φ.1.toFun x := by
  filter_upwards [gradientCLM_apply_ae (testFunctionToH10 φ),
    ae_all_iff.mpr (fun i ↦ derivCoordCLM_testFunction_apply_ae i φ)] with x hg hd
  exact fun i ↦ (hg i).trans (hd i)

/-- Pairing with the `L²` test gradient agrees with the physical weak divergence density. -/
theorem inner_l2TestGradient_ae {n : ℕ} (v : WholeSpaceL2 n)
    (φ : TestFunctionOn n Set.univ) :
    (fun x ↦ inner ℝ (v x) (l2TestGradient φ x)) =ᵐ[volume]
      weakDivergencePairingDensity (fun x ↦ v x) φ.1.toFun := by
  have hgrad := l2TestGradient_apply_ae φ
  simp only [domainMeasure, Measure.restrict_univ] at hgrad
  filter_upwards [hgrad] with x hx
  rw [weakDivergencePairingDensity_eq_sum, PiLp.inner_apply]
  simp only [Real.inner_apply, hx]

/-- Every weak divergence test density of an `L²` field is integrable. -/
theorem integrable_weakDivergencePairingDensity_l2 {n : ℕ} (v : WholeSpaceL2 n)
    (φ : TestFunctionOn n Set.univ) :
    Integrable (weakDivergencePairingDensity (fun x ↦ v x) φ.1.toFun) volume := by
  have hi := L2.integrable_inner (𝕜 := ℝ) v (l2TestGradient φ)
  simp only [domainMeasure, Measure.restrict_univ] at hi
  exact hi.congr (inner_l2TestGradient_ae v φ)

/-- The Hilbert pairing with a test gradient is the physical weak divergence pairing. -/
theorem inner_l2TestGradient_eq_weakDivergencePairing {n : ℕ} (v : WholeSpaceL2 n)
    (φ : TestFunctionOn n Set.univ) :
    inner ℝ v (l2TestGradient φ) = weakDivergencePairing (fun x ↦ v x) φ.1.toFun := by
  rw [L2.inner_def, weakDivergencePairing]
  simp only [domainMeasure, Measure.restrict_univ]
  exact integral_congr_ae (inner_l2TestGradient_ae v φ)

/-- The whole-space divergence-free `L²` submodule. -/
def l2Solenoidal (n : ℕ) : Submodule ℝ (WholeSpaceL2 n) :=
  (Submodule.span ℝ (Set.range (l2TestGradient (n := n)))).orthogonal

/-- Solenoidal membership is vanishing against every smooth compactly supported gradient. -/
theorem mem_l2Solenoidal_iff_inner {n : ℕ} (v : WholeSpaceL2 n) :
    v ∈ l2Solenoidal n ↔ ∀ φ : TestFunctionOn n Set.univ,
      inner ℝ v (l2TestGradient φ) = 0 := by
  constructor
  · intro hv φ
    exact (Submodule.mem_orthogonal' _ v).mp hv (l2TestGradient φ)
      (Submodule.subset_span (Set.mem_range_self φ))
  · intro hv
    apply (Submodule.mem_orthogonal' _ v).mpr
    have hspan : Submodule.span ℝ (Set.range (l2TestGradient (n := n))) ≤
        (innerSL ℝ v).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨φ, rfl⟩
      exact hv φ
    intro w hw
    exact (innerSL ℝ v).mem_ker.mp (hspan hw)

/-- The closed Hilbert subspace agrees exactly with distributional incompressibility. -/
theorem mem_l2Solenoidal_iff_distributionallyDivergenceFree {n : ℕ} (v : WholeSpaceL2 n) :
    v ∈ l2Solenoidal n ↔ DistributionallyDivergenceFree (fun x ↦ v x) := by
  rw [mem_l2Solenoidal_iff_inner]
  constructor
  · intro hv ψ hψ hc
    let φ : TestFunctionOn n Set.univ :=
      ⟨TestFunction.mk ψ hψ hc (Set.subset_univ _), Set.subset_univ _⟩
    refine ⟨integrable_weakDivergencePairingDensity_l2 v φ, ?_⟩
    change weakDivergencePairing (fun x ↦ v x) φ.1.toFun = 0
    rw [← inner_l2TestGradient_eq_weakDivergencePairing]
    exact hv φ
  · intro hv φ
    rw [inner_l2TestGradient_eq_weakDivergencePairing]
    exact (hv φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport).2

/-- The `L²` class of a square-integrable field that is incompressible in distributions lies
in the closed solenoidal subspace. -/
theorem toLp_mem_l2Solenoidal {n : ℕ} {u : ℝ^n → ℝ^n}
    (hu : MemLp u 2 (domainMeasure n Set.univ)) (hdiv : DistributionallyDivergenceFree u) :
    hu.toLp u ∈ l2Solenoidal n := by
  apply (mem_l2Solenoidal_iff_distributionallyDivergenceFree _).mpr
  intro ψ hψ hs
  have hv := hdiv ψ hψ hs
  have hae : (fun x ↦ hu.toLp u x) =ᵐ[volume] u := by
    simpa only [domainMeasure, Measure.restrict_univ] using hu.coeFn_toLp
  have hdensity : weakDivergencePairingDensity (fun x ↦ hu.toLp u x) ψ
      =ᵐ[volume] weakDivergencePairingDensity u ψ := by
    filter_upwards [hae] with x hx
    simp only [weakDivergencePairingDensity, hx]
  refine ⟨hv.1.congr hdensity.symm, ?_⟩
  change (∫ x, weakDivergencePairingDensity (fun x ↦ hu.toLp u x) ψ x) = 0
  exact (integral_congr_ae hdensity).trans hv.2

/-- Distributionally divergence-free `L²` fields form a closed subspace. -/
theorem isClosed_l2Solenoidal (n : ℕ) : IsClosed (l2Solenoidal n : Set (WholeSpaceL2 n)) :=
  (Submodule.span ℝ (Set.range (l2TestGradient (n := n)))).isClosed_orthogonal

/-- The divergence-free subspace is complete for the inherited `L²` metric. -/
instance l2Solenoidal_completeSpace (n : ℕ) : CompleteSpace (l2Solenoidal n) :=
  (isClosed_l2Solenoidal n).completeSpace_coe

/-- The canonical whole-space Leray projection. -/
def lerayProjection (n : ℕ) : WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  (l2Solenoidal n).starProjection

/-- The projection takes values in the actual distributionally divergence-free subspace. -/
theorem lerayProjection_mem (n : ℕ) (v : WholeSpaceL2 n) :
    lerayProjection n v ∈ l2Solenoidal n :=
  (l2Solenoidal n).starProjection_apply_mem v

/-- The projected representative is incompressible in distributions. -/
theorem distributionallyDivergenceFree_lerayProjection (n : ℕ) (v : WholeSpaceL2 n) :
    DistributionallyDivergenceFree (fun x ↦ lerayProjection n v x) :=
  (mem_l2Solenoidal_iff_distributionallyDivergenceFree _).mp (lerayProjection_mem n v)

/-- Leray projection is contractive in the physical `L²` norm. -/
theorem norm_lerayProjection_le (n : ℕ) (v : WholeSpaceL2 n) :
    ‖lerayProjection n v‖ ≤ ‖v‖ :=
  (l2Solenoidal n).norm_starProjection_apply_le v

/-- The projection acts as the identity on solenoidal fields. -/
theorem lerayProjection_eq_self {n : ℕ} {v : WholeSpaceL2 n} (hv : v ∈ l2Solenoidal n) :
    lerayProjection n v = v :=
  (l2Solenoidal n).starProjection_eq_self_iff.mpr hv

/-- Leray projection is idempotent. -/
theorem lerayProjection_lerayProjection (n : ℕ) (v : WholeSpaceL2 n) :
    lerayProjection n (lerayProjection n v) = lerayProjection n v :=
  lerayProjection_eq_self (lerayProjection_mem n v)

/-- Orthogonal projection removes the pressure component in solenoidal weak pairings. -/
theorem inner_lerayProjection_eq {n : ℕ} (v w : WholeSpaceL2 n) (hw : w ∈ l2Solenoidal n) :
    inner ℝ (lerayProjection n v) w = inner ℝ v w := by
  have h := (l2Solenoidal n).starProjection_inner_eq_zero v w hw
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

/-- Solenoidal `L²` fields annihilate weak gradients of every whole-space `H¹` pressure. -/
theorem inner_solenoidal_wkpGradient_eq_zero {n : ℕ} (v : WholeSpaceL2 n)
    (hv : v ∈ l2Solenoidal n) (p : H¹(ℝ^n)) : inner ℝ v (wkpGradientCLM p) = 0 := by
  have hp : p ∈ (h10SubmoduleOn (n := n) (Ω := Set.univ)).toSubmodule := by
    simpa only [h10SubmoduleOn] using wkpSpace_mem_Wkp0_univ (by norm_num) p
  let p₀ : H¹₀(ℝ^n) := ⟨p, hp⟩
  let T : H¹₀(ℝ^n) →L[ℝ] ℝ := (innerSL ℝ v).comp gradientCLM
  have htest : (fun φ : TestFunctionOn n Set.univ ↦ T (testFunctionToH10Linear φ)) =
      (fun _ : TestFunctionOn n Set.univ ↦ (0 : ℝ)) := by
    funext φ
    change inner ℝ v (l2TestGradient φ) = 0
    exact (mem_l2Solenoidal_iff_inner v).mp hv φ
  have hzero : (T : H¹₀(ℝ^n) → ℝ) = fun _ ↦ 0 :=
    (denseRange_testFunctionToH10Linear (n := n) (Ω := Set.univ)).equalizer
      T.continuous continuous_const htest
  exact congrFun hzero p₀

/-- The Leray projector annihilates the weak gradient of an arbitrary `H¹` pressure. -/
theorem lerayProjection_wkpGradient_eq_zero {n : ℕ} (p : H¹(ℝ^n)) :
    lerayProjection n (wkpGradientCLM p) = 0 := by
  apply (l2Solenoidal n).eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.zero_mem _)
  intro v hv
  rw [sub_zero, real_inner_comm]
  exact inner_solenoidal_wkpGradient_eq_zero v hv p

end IncompressibleFlow
