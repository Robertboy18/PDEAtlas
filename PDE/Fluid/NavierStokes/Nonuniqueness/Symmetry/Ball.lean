/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Action
public import PDE.Spaces.Sobolev.Calculus.Pullback.Isometry
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# The axisymmetry group acting on zero-boundary velocities on a ball

Every element of the axisymmetry group maps the centred ball `B(0,ρ)` onto itself, so
`w ↦ g ∘ w ∘ g⁻¹` is a linear isometry equivalence `actBall ρ θ s` of `H¹₀(B(0,ρ); ℝ^3)`
(`SobolevSpace.GraphSpace.zeroBoundaryVelocityIsometry`). It preserves vanishing divergence
(`actBall_mem_solenoidal`), its zero extension is the pointwise action on the zero extension
(`ballField_actBall`), and the even and odd sectors on the ball are exactly the fixed fields of
the action and the fields on which it acts by the character `parity`
(`mem_evenSector_iff_actBall`, `mem_oddSector_iff_actBall`).

Two bridges connect the sectors on the ball with the whole-space sectors and the tests. The
componentwise zero extension `zeroExtendBall ρ` to whole-space `H¹` has `ballField ρ u` as its
representative, so it maps `evenSector ρ` into `evenSectorH1` and `oddSector ρ` into `oddSectorH1`
(`zeroExtendBall_mem_evenSectorH1`). A smooth solenoidal test field supported in `B(0,ρ)` is a
solenoidal zero-boundary velocity `ballTest` on the ball with zero extension equal to the field,
so even and odd tests give elements of `evenSector ρ` and `oddSector ρ`
(`ballTest_mem_evenSector`, `ballTest_mem_oddSector`).
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory SobolevSpace SobolevSpace.GraphSpace NavierStokes.Nonuniqueness
open scoped Sobolev ENNReal

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

/-- Every group element maps a centred ball onto itself. -/
theorem isIsometryInvariant_ball (θ : ℝ) (s : Bool) (ρ : ℝ) :
    IsIsometryInvariant (groupElement θ s) (Metric.ball (0 : ℝ^3) ρ) :=
  ⟨measurableSet_ball, fun x ↦ by
    simp only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]⟩

/-- The action of a group element on zero-boundary velocity fields on the ball `B(0,ρ)`,
`w ↦ g ∘ w ∘ g⁻¹`. -/
def actBall (ρ θ : ℝ) (s : Bool) :
    H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3) ≃ₗᵢ[ℝ] H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3) :=
  zeroBoundaryVelocityIsometry (groupElement θ s) (isIsometryInvariant_ball θ s ρ)
    Metric.isOpen_ball

/-- The action on the ball preserves vanishing divergence. -/
theorem actBall_mem_solenoidal (ρ θ : ℝ) (s : Bool) {u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)}
    (hu : ZeroBoundaryVectorSpace.divergence u = 0) :
    ZeroBoundaryVectorSpace.divergence (actBall ρ θ s u) = 0 :=
  zeroBoundaryVelocityIsometry_mem_solenoidal _ _ _ hu

/-- The base coordinates of the transformed field. -/
private theorem baseCoordCLM_actBall (ρ θ : ℝ) (s : Bool)
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (i : Fin 3) :
    baseCoordCLM (actBall ρ θ s u i) = ∑ k, (groupElement θ s (EuclideanSpace.single k 1)) i •
      l2CompSymm (groupElement θ s) (isIsometryInvariant_ball θ s ρ) (baseCoordCLM (u k)) := by
  change baseCoordCLM (zeroBoundaryVelocityIsometry (groupElement θ s)
    (isIsometryInvariant_ball θ s ρ) Metric.isOpen_ball u i) = _
  rw [zeroBoundaryVelocityIsometry_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul]
  congr 1
  change ((h1CompSymmCLM (groupElement θ s) (isIsometryInvariant_ball θ s ρ)
    ((u k : H¹₀(Metric.ball (0 : ℝ^3) ρ)) : H¹(Metric.ball (0 : ℝ^3) ρ)) :
      WkpAmbientOn 3 1 2 (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1)) = _
  rw [h1CompSymmCLM_coe, h1CompSymmAmbient_base]
  rfl

/-- The zero extension of the transformed field is the pointwise action on the zero
extension. -/
theorem ballField_actBall (ρ θ : ℝ) (s : Bool) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ballField ρ (actBall ρ θ s u) =ᵐ[volume] act θ s (ballField ρ u) := by
  have hg := isIsometryInvariant_ball θ s ρ
  have hsum (i : Fin 3) := Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦
    (groupElement θ s (EuclideanSpace.single k 1)) i •
      l2CompSymm (groupElement θ s) hg (baseCoordCLM (u k)))
  have hsmul (i k : Fin 3) := Lp.coeFn_smul ((groupElement θ s (EuclideanSpace.single k 1)) i)
    (l2CompSymm (groupElement θ s) hg (baseCoordCLM (u k)))
  have hcomp (k : Fin 3) := l2CompSymm_ae (groupElement θ s) hg (baseCoordCLM (u k))
  have hpull := hg.symm.measurePreserving.quasiMeasurePreserving.ae
    (ZeroBoundaryVectorSpace.toLp_apply_ae u)
  have hrestrict : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) ρ)),
      ZeroBoundaryVectorSpace.toLp (actBall ρ θ s u) x =
        groupElement θ s (ZeroBoundaryVectorSpace.toLp u ((groupElement θ s).symm x)) := by
    filter_upwards [ZeroBoundaryVectorSpace.toLp_apply_ae (actBall ρ θ s u), ae_all_iff.mpr hsum,
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hsmul i), ae_all_iff.mpr hcomp, hpull]
      with x hx hsx hkx hcx hux
    ext i
    rw [hx i, baseCoordCLM_actBall, hsx i, linearIsometryEquiv_apply_coord]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hkx i k, Pi.smul_apply, hcx k, smul_eq_mul, mul_comm, hux k]
  rw [ae_restrict_iff' measurableSet_ball] at hrestrict
  filter_upwards [hrestrict] with x hx
  by_cases hxB : x ∈ Metric.ball (0 : ℝ^3) ρ
  · have hxB' : (groupElement θ s).symm x ∈ Metric.ball (0 : ℝ^3) ρ :=
      (hg.symm.mem_iff x).mpr hxB
    rw [ballField, Set.indicator_of_mem hxB, hx hxB, act_apply, ballField,
      Set.indicator_of_mem hxB']
  · have hxB' : (groupElement θ s).symm x ∉ Metric.ball (0 : ℝ^3) ρ :=
      fun h ↦ hxB ((hg.symm.mem_iff x).mp h)
    rw [ballField, Set.indicator_of_notMem hxB, act_apply, ballField,
      Set.indicator_of_notMem hxB', map_zero]

/-- A zero-boundary field on a ball is determined by the almost-everywhere class of its zero
extension. -/
theorem eq_of_ballField_ae {ρ : ℝ} {u v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)}
    (h : ballField ρ u =ᵐ[volume] ballField ρ v) : u = v := by
  have hB : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) ρ)),
      ZeroBoundaryVectorSpace.toLp u x = ZeroBoundaryVectorSpace.toLp v x := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [h] with x hx hxB
    simpa only [ballField, Set.indicator_of_mem hxB] using hx
  ext1 i
  refine Subtype.ext (wkpBaseCoordinateCLM_injective Metric.isOpen_ball (Lp.ext ?_))
  filter_upwards [hB, ZeroBoundaryVectorSpace.toLp_apply_ae u,
    ZeroBoundaryVectorSpace.toLp_apply_ae v] with x hx hu hv
  have := (hu i).symm.trans ((congrArg (fun z : ℝ^3 ↦ z i) hx).trans (hv i))
  exact this

/-- The action on the ball equals a given field exactly when the zero extensions agree
almost everywhere. -/
theorem actBall_eq_iff {ρ θ : ℝ} {s : Bool} {u v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)} :
    actBall ρ θ s u = v ↔ act θ s (ballField ρ u) =ᵐ[volume] ballField ρ v := by
  constructor
  · rintro rfl
    exact (ballField_actBall ρ θ s u).symm
  · intro h
    exact eq_of_ballField_ae ((ballField_actBall ρ θ s u).trans h)

/-- The even sector on a ball consists of the fields fixed by every group element. -/
theorem mem_evenSector_iff_actBall {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))} :
    u ∈ evenSector ρ ↔ ∀ θ s, actBall ρ θ s u = u := by
  rw [mem_evenSector_iff, isEvenAxisymmetric_iff_act]
  exact forall₂_congr fun θ s ↦ actBall_eq_iff.symm

/-- The odd sector on a ball consists of the fields on which every group element acts by the
character `parity`. -/
theorem mem_oddSector_iff_actBall {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))} :
    u ∈ oddSector ρ ↔
      ∀ θ s, actBall ρ θ s u = parity s • (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) := by
  rw [mem_oddSector_iff, isOddAxisymmetric_iff_act]
  refine forall₂_congr fun θ s ↦ ?_
  rw [actBall_eq_iff]
  have hsm := ballField_smul_ae ρ (parity s) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
  constructor
  · intro h
    exact h.trans hsm.symm
  · intro h
    exact h.trans hsm

/-! ### Zero extension to the whole space -/

/-- The componentwise zero extension of a zero-boundary velocity on `B(0,ρ)` to a whole-space
`H¹` velocity. -/
def zeroExtendBall (ρ : ℝ) :
    H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3) →L[ℝ] PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ ZeroTrace.zeroExtendH10 measurableSet_ball

/-- The representative of the zero extension is the zero extension `ballField ρ u` of the
value, almost everywhere. -/
theorem representative_zeroExtendBall (ρ : ℝ) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    Stationary.representative (zeroExtendBall ρ u) =ᵐ[volume] ballField ρ u := by
  have hext (i : Fin 3) := ZeroTrace.zeroExtendH10_coordinate_apply_ae measurableSet_ball (u i)
    (baseIndex 3 1)
  have hval : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : ℝ^3) ρ →
      ∀ i, ZeroBoundaryVectorSpace.toLp u x i = baseCoordCLM (u i) x :=
    (ae_restrict_iff' measurableSet_ball).mp (ZeroBoundaryVectorSpace.toLp_apply_ae u)
  filter_upwards [ae_all_iff.mpr hext, hval] with x hx hv
  ext i
  change ((((ZeroTrace.zeroExtendH10 measurableSet_ball (u i) : H¹(ℝ^3)) :
    WkpAmbientOn 3 1 2 Set.univ) (baseIndex 3 1) : DerivLp 3 2 Set.univ) : ℝ^3 → ℝ) x = _
  rw [hx i]
  by_cases hxB : x ∈ Metric.ball (0 : ℝ^3) ρ
  · rw [Set.indicator_of_mem hxB, ballField, Set.indicator_of_mem hxB, hv hxB i]
    rfl
  · rw [Set.indicator_of_notMem hxB, ballField, Set.indicator_of_notMem hxB]
    rfl

/-- The zero extension of a field in the even sector on a ball lies in the even whole-space
sector. -/
theorem zeroExtendBall_mem_evenSectorH1 {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))}
    (hu : u ∈ evenSector ρ) : zeroExtendBall ρ u ∈ evenSectorH1 :=
  mem_evenSectorH1_iff.mpr ((mem_evenSector_iff.mp hu).congr_ae
    (representative_zeroExtendBall ρ u).symm)

/-- The zero extension of a field in the odd sector on a ball lies in the odd whole-space
sector. -/
theorem zeroExtendBall_mem_oddSectorH1 {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))}
    (hu : u ∈ oddSector ρ) : zeroExtendBall ρ u ∈ oddSectorH1 :=
  mem_oddSectorH1_iff.mpr ((mem_oddSector_iff.mp hu).congr_ae
    (representative_zeroExtendBall ρ u).symm)

/-! ### Test fields supported in the ball -/

variable {ρ : ℝ} {φ : ℝ^3 → ℝ^3}

/-- A component of a smooth compactly supported field with support in `B(0,ρ)`, as a test
function on the ball. -/
def ballTestComponent (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ)
    (i : Fin 3) : TestFunctionOn 3 (Metric.ball (0 : ℝ^3) ρ) :=
  ⟨_root_.TestFunction.mk (fun x ↦ φ x i)
    ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ.1)
    (hφ.2.1.comp_left (g := fun v : ℝ^3 ↦ v i) rfl) (Set.subset_univ _),
    (tsupport_comp_subset (g := fun v : ℝ^3 ↦ v i) rfl φ).trans hsupp⟩

/-- The zero-boundary velocity on the ball of a smooth field supported in `B(0,ρ)`. -/
def ballTestField (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3) :=
  WithLp.toLp 2 fun i ↦ testFunctionToH10 (ballTestComponent hφ hsupp i)

/-- The coordinates of the test velocity are the classical derivatives of the components. -/
theorem coord_ballTestField_ae (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) (i : Fin 3) (a : DerivIndex 3 1) :
    ((((ballTestField hφ hsupp i : H¹₀(Metric.ball (0 : ℝ^3) ρ)) : H¹(Metric.ball (0 : ℝ^3) ρ)) :
      WkpAmbientOn 3 1 2 (Metric.ball (0 : ℝ^3) ρ)) a : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ iteratedPartialDeriv a.toList (fun y ↦ φ y i) x :=
  testFunctionToWkp_coordinate_ae (k := 1) (p := 2) (ballTestComponent hφ hsupp i) a

/-- The test velocity is divergence free. -/
theorem divergence_ballTestField (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    ZeroBoundaryVectorSpace.divergence (ballTestField hφ hsupp) = 0 := by
  change ∇· (ballTestField hφ hsupp) = 0
  rw [ZeroBoundaryVectorSpace.divergence_apply]
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ derivCoordCLM i (ballTestField hφ hsupp i))
  filter_upwards [hsum, ae_all_iff.mpr fun i ↦ coord_ballTestField_ae hφ hsupp i
    (singleDerivIndex 3 i), Lp.coeFn_zero ℝ 2 (domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ))]
    with x hx hk h0
  rw [hx, h0, Pi.zero_apply]
  have hterm (i : Fin 3) : (derivCoordCLM i (ballTestField hφ hsupp i) : ℝ^3 → ℝ) x =
      PDE.partialDeriv i (fun y ↦ φ y i) x := by
    rw [derivCoordCLM_apply, hk i]
    simp [iteratedPartialDeriv]
  simp only [hterm]
  exact hφ.2.2 x

/-- A smooth solenoidal test field supported in `B(0,ρ)`, as a solenoidal zero-boundary velocity
on the ball. -/
def ballTest (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    IncompressibleFlow.SolenoidalSpace
      (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ)) :=
  ⟨ballTestField hφ hsupp, divergence_ballTestField hφ hsupp⟩

/-- The zero extension of the test velocity is the test field, almost everywhere. -/
theorem ballField_ballTest (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    ballField ρ (ballTest hφ hsupp) =ᵐ[volume] φ := by
  have hb : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) ρ)),
      ∀ i, ZeroBoundaryVectorSpace.toLp (ballTestField hφ hsupp) x i = φ x i := by
    filter_upwards [ZeroBoundaryVectorSpace.toLp_apply_ae (ballTestField hφ hsupp),
      ae_all_iff.mpr fun i ↦ coord_ballTestField_ae hφ hsupp i (baseIndex 3 1)] with x hx hk i
    rw [hx i, baseCoordCLM_apply, hk i]
    simp [iteratedPartialDeriv]
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hb] with x hx
  by_cases hxB : x ∈ Metric.ball (0 : ℝ^3) ρ
  · rw [ballField, Set.indicator_of_mem hxB]
    ext i
    exact hx hxB i
  · rw [ballField, Set.indicator_of_notMem hxB]
    exact (image_eq_zero_of_notMem_tsupport fun h ↦ hxB (hsupp h)).symm

/-- An even axisymmetric smooth solenoidal test field supported in `B(0,ρ)` gives an element of
the even sector on the ball. -/
theorem ballTest_mem_evenSector (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) (he : IsEvenAxisymmetric φ) :
    ballTest hφ hsupp ∈ evenSector ρ :=
  mem_evenSector_iff.mpr (he.congr_ae (ballField_ballTest hφ hsupp).symm)

/-- An odd axisymmetric smooth solenoidal test field supported in `B(0,ρ)` gives an element of
the odd sector on the ball. -/
theorem ballTest_mem_oddSector (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) (ho : IsOddAxisymmetric φ) :
    ballTest hφ hsupp ∈ oddSector ρ :=
  mem_oddSector_iff.mpr (ho.congr_ae (ballField_ballTest hφ hsupp).symm)

end NavierStokes.Symmetry
