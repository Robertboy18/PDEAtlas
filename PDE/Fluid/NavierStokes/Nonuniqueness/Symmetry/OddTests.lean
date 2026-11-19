/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.EigenTests
public import PDE.Fluid.NavierStokes.Selfsimilar.GraphDomain
import PDE.Fluid.NavierStokes.Stationary.TestFieldRepresentative
import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Closed
import PDE.Fluid.NavierStokes.Selfsimilar.GraphWeakForm
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Odd axisymmetric solenoidal test fields

The smooth compactly supported divergence-free fields on `ℝ^3` that are odd axisymmetric form a
linear space closed under the dilations `φ ↦ φ(s ·)`, `s > 0`, since rotations and the
equatorial reflection are linear and commute with scaling (`oddSolenoidalTestSpace`). Its
closed span in the whole-space `H¹` velocity space is the divergence-free part of the odd
sector `oddSectorH1` (`mem_space_oddSolenoidalTestSpace_iff`).

The closed span lies in the odd sector and in the kernel of the divergence, and both are
closed. For the converse let `w` be odd and divergence free and let `w'` be its component
orthogonal to the closed span. The `H¹` pairing with a test field is the integral of a jet
density, `⟪w', φ⟫ = ∫ V·φ + Σⱼ Gⱼ·∂ⱼφ` with `V` the representative of `w'` and `Gⱼ` the
column `j` of its weak gradient (`inner_testFieldH1_eq_integral_jetDensity`). For odd `w'`
these coefficients are equivariant with the odd character, so the pairing vanishes on every
solenoidal test field once it vanishes on the odd ones
(`inner_testFieldH1_eq_zero_of_symmetric_tests`). Being divergence free, `w'` lies in the
closed span of the solenoidal test fields, hence `⟪w', w'⟫ = 0` and `w` lies in the closed span
of the odd ones.
-/

@[expose] public noncomputable section

open MeasureTheory Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.CoordinateSystems (axialRotation equatorialReflection)
open NavierStokes.Nonuniqueness
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-! ### The test space -/

/-- Dilations preserve the odd axisymmetry of continuous fields. -/
theorem _root_.NavierStokes.Nonuniqueness.IsOddAxisymmetric.comp_smul {φ : ℝ^3 → ℝ^3}
    (hφ : IsOddAxisymmetric φ) (hc : Continuous φ) (s : ℝ) :
    IsOddAxisymmetric (fun x ↦ φ (s • x)) := by
  refine ⟨fun θ ↦ Eventually.of_forall fun x ↦ ?_, Eventually.of_forall fun x ↦ ?_⟩
  · have hf : Continuous (fun x ↦ axialRotation θ (φ ((axialRotation θ).symm x))) :=
      (axialRotation θ).continuous.comp (hc.comp (axialRotation θ).symm.continuous)
    have h := congrFun ((Continuous.ae_eq_iff_eq volume hf hc).mp (hφ.1 θ)) (s • x)
    simpa only [map_smul] using h
  · have hf : Continuous (fun x ↦ equatorialReflection (φ (equatorialReflection x))) :=
      equatorialReflection.continuous.comp (hc.comp equatorialReflection.continuous)
    have h := congrFun ((Continuous.ae_eq_iff_eq volume hf hc.neg).mp hφ.2) (s • x)
    simpa only [map_smul, Pi.neg_apply] using h

/-- The odd axisymmetric smooth compactly supported solenoidal fields, a dilation test space. -/
def oddSolenoidalTestSpace : Selfsimilar.DilationTestSpace 3 where
  carrier :=
    { carrier := {φ | IsSolenoidalTestField φ ∧ IsOddAxisymmetric φ}
      add_mem' := fun hφ hψ ↦ ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
      zero_mem' := ⟨⟨contDiff_const, HasCompactSupport.zero, fun x ↦ by
        simp [PDE.divergence, PDE.partialDeriv]⟩, isOddAxisymmetric_zero⟩
      smul_mem' := fun c _ hφ ↦ ⟨hφ.1.smul c, hφ.2.smul c⟩ }
  contDiff _ hφ := hφ.1.1
  hasCompactSupport _ hφ := hφ.1.2.1
  comp_smul_mem φ hφ s hs :=
    ⟨⟨Stationary.contDiff_comp_smul hφ.1.1 s,
      Stationary.hasCompactSupport_comp_smul hφ.1.2.1 hs.ne',
      Stationary.divergence_comp_smul hφ.1.1 hφ.1.2.2 s⟩, hφ.2.comp_smul hφ.1.1.continuous s⟩

/-- Membership in the odd solenoidal test space. -/
theorem mem_oddSolenoidalTestSpace_iff {φ : ℝ^3 → ℝ^3} :
    φ ∈ oddSolenoidalTestSpace.carrier ↔
      Nonuniqueness.IsSolenoidalTestField φ ∧ Nonuniqueness.IsOddAxisymmetric φ :=
  Iff.rfl

/-! ### The `H¹` pairing as a jet density -/

/-- With zero base field, the first-order coefficient `eigenFirst 0 w x j` is the column `j` of
the weak gradient. -/
theorem inner_eigenFirst_zero (w : H) (x u : ℝ^3) (j : Fin 3) :
    ⟪eigenFirst 0 w x j, u⟫ = ∑ i, Stationary.gradientRepresentative w x i j * u i := by
  simp [eigenFirst, EuclideanSpace.real_inner_eq_sum]

/-- The `H¹` pairing with a test field is the integral of the jet density with coefficients the
representative `V`, the columns `Gⱼ` of the weak gradient and zero:
`⟪w, φ⟫ = ∫ V·φ + Σⱼ Gⱼ·∂ⱼφ`. -/
theorem inner_testFieldH1_eq_integral_jetDensity (w : H) {φ : ℝ^3 → ℝ^3}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ⟪w, Stationary.testFieldH1 φ hφ hc⟫ =
      ∫ x, jetDensity (Stationary.representative w) (eigenFirst 0 w) 0 φ x := by
  set T := Stationary.testFieldH1 φ hφ hc
  set V := Stationary.representative w
  set G := Stationary.gradientRepresentative w
  have hbase (i : Fin 3) := integrable_and_integral_eq_inner
    (f := fun x ↦ V x i * φ x i) (u := wkpBaseCoordinateCLM (w i))
    (w := wkpBaseCoordinateCLM (T i)) (F := fun x ↦ V x i) (Eventually.of_forall fun _ ↦ rfl)
    (Stationary.testFieldH1_base_ae hφ hc i) (Eventually.of_forall fun _ ↦ rfl)
  have hder (i j : Fin 3) := integrable_and_integral_eq_inner
    (f := fun x ↦ G x i j * PDE.partialDeriv j (fun y ↦ φ y i) x)
    (u := wkpCoordinateCLM (singleDerivIndex 3 j) (w i))
    (w := wkpCoordinateCLM (singleDerivIndex 3 j) (T i)) (F := fun x ↦ G x i j)
    (Eventually.of_forall fun _ ↦ rfl) (Stationary.testFieldH1_partial_ae hφ hc i j)
    (Eventually.of_forall fun _ ↦ rfl)
  have hpt (x : ℝ^3) : jetDensity V (eigenFirst 0 w) 0 φ x =
      ∑ i, (V x i * φ x i + ∑ j, G x i j * PDE.partialDeriv j (fun y ↦ φ y i) x) := by
    have hpart (i j : Fin 3) :
        PDE.partialDeriv j φ x i = PDE.partialDeriv j (fun y ↦ φ y i) x :=
      PDE.partialDeriv_apply j i ((hφ.differentiable (by simp)) x)
    simp only [jetDensity, inner_eigenFirst_zero, Pi.zero_apply, inner_zero_left, add_zero,
      hpart]
    rw [EuclideanSpace.real_inner_eq_sum, Finset.sum_add_distrib]
    exact congrArg _ Finset.sum_comm
  have hint (i : Fin 3) : Integrable (fun x ↦ V x i * φ x i +
      ∑ j, G x i j * PDE.partialDeriv j (fun y ↦ φ y i) x) :=
    (hbase i).1.add (integrable_finsetSum _ fun j _ ↦ (hder i j).1)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun i _ ↦ hint i,
    PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_add (hbase i).1 (integrable_finsetSum _ fun j _ ↦ (hder i j).1),
    integral_finsetSum _ fun j _ ↦ (hder i j).1, (hbase i).2]
  simp only [(hder i _).2]
  change inner ℝ (w i : WkpAmbientOn 3 1 2 Set.univ) (T i : WkpAmbientOn 3 1 2 Set.univ) = _
  rw [ambient_inner_eq_base_add_sum_deriv]
  rfl

/-- The coefficients of the `H¹` pairing are equivariant with the odd character when the
representative is odd axisymmetric. -/
theorem isEquivariantJet_inner {w : H} (hw : w ∈ oddSectorH1) :
    IsEquivariantJet true (Stationary.representative w) (eigenFirst 0 w) 0 := by
  have hV : IsOddAxisymmetric (Stationary.representative w) := mem_oddSectorH1_iff.mp hw
  have hE := isEquivariantJet_eigen (μ := 0) isEvenAxisymmetric_zero hV hV.isOddGradient
  exact ⟨fun θ s ↦ by simpa only [Bool.true_and] using hV.ae_comp_groupElement θ s, hE.b_comp,
    hE.c_comp⟩

/-- The coefficients of the `H¹` pairing are locally integrable. -/
theorem isLocallyIntegrableJet_inner (w : H) :
    IsLocallyIntegrableJet (Stationary.representative w) (eigenFirst 0 w) 0 := by
  have hJ := isLocallyIntegrableJet_eigen (U := 0) 0 w aestronglyMeasurable_zero
    (by simpa using (locallyIntegrable_const (0 : ℝ)))
  have hV := Stationary.memLp_representative w
  exact ⟨hV.aestronglyMeasurable, hJ.measurable_b, hJ.measurable_c,
    hV.norm.locallyIntegrable (by norm_num), hJ.integrable_b, hJ.integrable_c⟩

/-- A field of the odd sector that is orthogonal to the odd solenoidal test fields is
orthogonal to every solenoidal test field. -/
theorem inner_testFieldH1_eq_zero_of_symmetric_tests {w : H} (hw : w ∈ oddSectorH1)
    (h : ∀ ψ (hψ : IsSolenoidalTestField ψ), IsOddAxisymmetric ψ →
      ⟪w, Stationary.testFieldH1 ψ hψ.1 hψ.2.1⟫ = 0)
    {φ : ℝ^3 → ℝ^3} (hφ : IsSolenoidalTestField φ) :
    ⟪w, Stationary.testFieldH1 φ hφ.1 hφ.2.1⟫ = 0 := by
  rw [inner_testFieldH1_eq_integral_jetDensity]
  refine (weak_eq_of_symmetric_tests true (isLocallyIntegrableJet_inner w)
    (isEquivariantJet_inner hw) (fun ψ hψ hsec ↦ ?_) φ hφ).2
  rw [← inner_testFieldH1_eq_integral_jetDensity w hψ.1 hψ.2.1]
  exact h ψ hψ (isInSector_true_iff.mp hsec)

/-! ### Density -/

/-- The closed span of the odd solenoidal test fields is the divergence-free part of the odd
sector. -/
theorem mem_space_oddSolenoidalTestSpace_iff (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) :
    v ∈ oddSolenoidalTestSpace.space ↔
      Stationary.divergenceCLM v = 0 ∧ v ∈ Nonuniqueness.oddSectorH1 := by
  set K := oddSolenoidalTestSpace.space
  have hle : K ≤ (Stationary.divergenceCLM (n := 3)).ker ⊓ oddSectorH1 := by
    refine Submodule.topologicalClosure_minimal _ ?_
      ((Stationary.divergenceCLM (n := 3)).isClosed_ker.inter oddSectorH1_isClosed)
    rintro _ ⟨φ, rfl⟩
    exact ⟨Stationary.divergenceCLM_testFieldH1 φ.2.1.1 φ.2.1.2.1 φ.2.1.2.2,
      φ.2.2.congr_ae (Stationary.representative_testFieldH1_ae φ.2.1.1 φ.2.1.2.1).symm⟩
  refine ⟨fun hv ↦ hle hv, fun ⟨hdiv, hodd⟩ ↦ ?_⟩
  set w := v - K.starProjection v
  have hwK : w ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hPv := hle (K.starProjection_apply_mem v)
  have hPdiv : Stationary.divergenceCLM (K.starProjection v) = 0 := hPv.1
  have hwdiv : Stationary.divergenceCLM w = 0 := by
    rw [map_sub, hdiv, hPdiv, sub_zero]
  have hwodd : w ∈ oddSectorH1 := oddSectorH1.sub_mem hodd hPv.2
  have hodd_tests (ψ : ℝ^3 → ℝ^3) (hψ : IsSolenoidalTestField ψ) (hψo : IsOddAxisymmetric ψ) :
      ⟪w, Stationary.testFieldH1 ψ hψ.1 hψ.2.1⟫ = 0 := by
    have hmem : Stationary.testFieldH1 ψ hψ.1 hψ.2.1 ∈ K :=
      Submodule.le_topologicalClosure _ ⟨⟨ψ, hψ, hψo⟩, rfl⟩
    exact (K.mem_orthogonal' w).mp hwK _ hmem
  have hwS : w ∈ (Selfsimilar.solenoidalTestSpace 3).space :=
    (Selfsimilar.mem_space_solenoidalTestSpace_iff (by norm_num) w).mpr hwdiv
  have hperp : (Selfsimilar.solenoidalTestSpace 3).space ≤ (innerSL ℝ w).ker := by
    refine Submodule.topologicalClosure_minimal _ ?_ (innerSL ℝ w).isClosed_ker
    rintro _ ⟨φ, rfl⟩
    rw [LinearMap.mem_ker]
    exact inner_testFieldH1_eq_zero_of_symmetric_tests hwodd hodd_tests φ.2
  have hw0 : w = 0 := inner_self_eq_zero.mp (LinearMap.mem_ker.mp (hperp hwS))
  rw [sub_eq_zero.mp hw0]
  exact K.starProjection_apply_mem v

end NavierStokes.Symmetry
