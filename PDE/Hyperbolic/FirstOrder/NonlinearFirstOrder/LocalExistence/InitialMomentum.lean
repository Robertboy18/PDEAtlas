/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ImplicitFunction
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Constructing compatible momentum on a noncharacteristic initial surface

For the boundary parametrization `b` and prescribed values `g`, an initial
momentum must solve both `F(p,g(y),b(y)) = 0` and
`⟨p,Db(y)dy⟩ = Dg(y)dy`. Combine these equations into a covector on the
boundary directions together with one scalar direction. Its derivative
in `p` is the Riesz map followed by pullback along the noncharacteristic
linear map. It is therefore invertible.

The implicit function theorem constructs a local compatible momentum
branch through a single compatible base momentum. Cⁿ⁺¹ boundary and value
data give Cⁿ momentum, for every finite positive `n`. In particular, C²
data give the C¹ momentum used by `SmoothConstruction` to construct a local
C² classical solution.

This is the compatibility construction of Evans, §3.2.3: Lemma 1 solves the compatibility
conditions (34) by the implicit function theorem on a flat boundary, and (36) is the
noncharacteristic condition on a curved one. The application uses contact transport for the
constructed C¹ characteristic family and its first variation, so one derivative of the momentum
suffices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, Lemma 1, equations (29)-(30) and (33)-(36).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open Filter Set
open scoped ContDiff RealInnerProductSpace Topology

variable {k : ℕ}

/-- The tangential compatibility equations and the PDE residual, combined
as a covector on `(dy,s)`. Its vanishing says that `p` is compatible with
the prescribed boundary values at `y`. -/
def initialMomentumResidual
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (yp : ℝ^k × SpaceTime k) : (ℝ^k × ℝ) →L[ℝ] ℝ :=
  (((innerSL ℝ yp.2).comp (fderiv ℝ boundary yp.1) -
      fderiv ℝ data yp.1).comp (ContinuousLinearMap.fst ℝ ℝ^k ℝ)) +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ^k ℝ)
      (F yp.2 (data yp.1) (boundary yp.1))

/-- Evaluating the compatibility covector displays its tangential and
scalar equations. -/
@[simp]
theorem initialMomentumResidual_apply (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (y : ℝ^k) (p : SpaceTime k) (dy : ℝ^k) (s : ℝ) :
    initialMomentumResidual F boundary data (y, p) (dy, s) = inner ℝ p (fderiv ℝ boundary y dy) -
      fderiv ℝ data y dy + s * F p (data y) (boundary y) := by
  rfl

/-- Vanishing of the covector is exactly Evans's PDE and tangential
compatibility conditions, with no differentiability assumption needed
for this algebraic identification. -/
theorem initialMomentumResidual_eq_zero_iff (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (y : ℝ^k) (p : SpaceTime k) :
    initialMomentumResidual F boundary data (y, p) = 0 ↔
      IsCompatibleInitialGradientAt F boundary data y p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hscalar := congrArg (fun L : (ℝ^k × ℝ) →L[ℝ] ℝ ↦ L (0, 1)) h
      simpa using hscalar
    · intro dy
      have htangent := congrArg (fun L : (ℝ^k × ℝ) →L[ℝ] ℝ ↦ L (dy, 0)) h
      exact (sub_eq_zero.mp (by simpa using htangent)).symm
  · rintro ⟨hF, htangent⟩
    apply ContinuousLinearMap.ext
    rintro ⟨dy, s⟩
    simp [initialMomentumResidual_apply, hF, htangent dy]

/-- One derivative is lost when the boundary compatibility equations are
formed: Cⁿ⁺¹ boundary and value data produce a Cⁿ residual. -/
theorem contDiffOn_initialMomentumResidual (n : ℕ) (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ n (phaseFunction (n := k + 1) F)) (boundary : ℝ^k → SpaceTime k)
    (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W) (hboundary : ContDiffOn ℝ (n + 1) boundary W)
    (hdata : ContDiffOn ℝ (n + 1) data W) :
    ContDiffOn ℝ n (initialMomentumResidual F boundary data)
      (W ×ˢ (Set.univ : Set (SpaceTime k))) := by
  have hDb : ContDiffOn ℝ n (fderiv ℝ boundary) W :=
    hboundary.fderiv_of_isOpen hW (by simp)
  have hDg : ContDiffOn ℝ n (fderiv ℝ data) W :=
    hdata.fderiv_of_isOpen hW (by simp)
  have hb : ContDiffOn ℝ n boundary W := hboundary.of_le (by simp)
  have hg : ContDiffOn ℝ n data W := hdata.of_le (by simp)
  have hfirst : MapsTo (Prod.fst : ℝ^k × SpaceTime k → ℝ^k)
      (W ×ˢ (Set.univ : Set (SpaceTime k))) W := fun _ hy ↦ hy.1
  have htangent : ContDiffOn ℝ n (fun yp : ℝ^k × SpaceTime k ↦
        (innerSL ℝ yp.2).comp (fderiv ℝ boundary yp.1) - fderiv ℝ data yp.1)
      (W ×ˢ (Set.univ : Set (SpaceTime k))) :=
    (((innerSL ℝ).contDiff.comp_contDiffOn contDiffOn_snd).clm_comp
      (hDb.comp contDiffOn_fst hfirst)).sub (hDg.comp contDiffOn_fst hfirst)
  have hresidual : ContDiffOn ℝ n (fun yp : ℝ^k × SpaceTime k ↦ F yp.2 (data yp.1) (boundary yp.1))
      (W ×ˢ (Set.univ : Set (SpaceTime k))) := hF.comp_contDiffOn (contDiffOn_snd.prodMk
        ((hg.comp contDiffOn_fst hfirst).prodMk (hb.comp contDiffOn_fst hfirst)))
  exact (htangent.clm_comp contDiffOn_const).add ((ContinuousLinearMap.smulRightL ℝ (ℝ^k × ℝ) ℝ
      (ContinuousLinearMap.snd ℝ ℝ^k ℝ)).contDiff.comp_contDiffOn hresidual)

/-- The derivative of the compatibility covector with respect to momentum
is the Riesz map followed by pullback along the characteristic initial
derivative. Boundary and value derivatives are fixed in this partial
derivative. -/
theorem hasFDerivAt_initialMomentumResidual_snd (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (y : ℝ^k) (p : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (data y, boundary y))) :
    HasFDerivAt (fun q ↦ initialMomentumResidual F boundary data (y, q))
      (((ContinuousLinearMap.compL ℝ (ℝ^k × ℝ) (SpaceTime k) ℝ).flip
        (characteristicInitialDerivative F boundary y p (data y))).comp (innerSL ℝ)) p := by
  let A : SpaceTime k →L[ℝ] (ℝ^k →L[ℝ] ℝ) := ((ContinuousLinearMap.compL ℝ ℝ^k (SpaceTime k) ℝ).flip
      (fderiv ℝ boundary y)).comp (innerSL ℝ)
  let C : (ℝ^k →L[ℝ] ℝ) →L[ℝ] ((ℝ^k × ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ℝ^k × ℝ) ℝ^k ℝ).flip (ContinuousLinearMap.fst ℝ ℝ^k ℝ)
  let D : ℝ →L[ℝ] ((ℝ^k × ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.smulRightL ℝ (ℝ^k × ℝ) ℝ
      (ContinuousLinearMap.snd ℝ ℝ^k ℝ)
  have hFp : HasFDerivAt (fun q ↦ F q (data y) (boundary y))
      (innerSL ℝ (momentumGradient (n := k + 1) F p (data y) (boundary y))) p := by
    have h := hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (data y, boundary y))
    apply h.congr_fderiv
    refine ContinuousLinearMap.ext fun dp ↦ ?_
    change fderiv ℝ (phaseFunction (n := k + 1) F) (p, (data y, boundary y))
        (dp, ((0 : ℝ), (0 : SpaceTime k))) =
      inner ℝ (momentumGradient (n := k + 1) F p (data y) (boundary y)) dp
    simpa only [mul_zero, inner_zero_right, add_zero] using
      fderiv_phaseFunction_apply_eq_characteristic_components F p dp (data y) 0 (boundary y) 0 hF
  have hderiv := ((C.hasFDerivAt (x := A p - fderiv ℝ data y)).comp p
    ((A.hasFDerivAt (x := p)).sub_const (fderiv ℝ data y))).add
      ((D.hasFDerivAt (x := F p (data y) (boundary y))).comp p hFp)
  change HasFDerivAt (fun q ↦ initialMomentumResidual F boundary data (y, q)) (C.comp A + D.comp
      (innerSL ℝ (momentumGradient (n := k + 1) F p (data y) (boundary y)))) p at hderiv
  apply hderiv.congr_fderiv
  refine ContinuousLinearMap.ext fun dp ↦ ?_
  apply ContinuousLinearMap.ext
  rintro ⟨dy, s⟩
  change inner ℝ dp (fderiv ℝ boundary y dy) +
      s * inner ℝ (momentumGradient (n := k + 1) F p (data y) (boundary y)) dp =
    inner ℝ dp (characteristicInitialDerivative F boundary y p (data y) (dy, s))
  simp only [characteristicInitialDerivative_apply, inner_add_right, inner_smul_right]
  rw [real_inner_comm (momentumGradient (n := k + 1) F p (data y) (boundary y)) dp]

/-- Noncharacteristicity makes the momentum Jacobian invertible. Pullback
along the noncharacteristic equivalence is inverted by pullback along its
inverse, and the Riesz map identifies momenta with covectors. -/
theorem isInvertible_initialMomentumResidual_snd (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (y : ℝ^k) (p : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (data y, boundary y)))
    (hresidual : DifferentiableAt ℝ (initialMomentumResidual F boundary data) (y, p))
    (hnonchar : IsNoncharacteristicAt F boundary y p (data y)) :
    ((fderiv ℝ (initialMomentumResidual F boundary data) (y, p)).comp
      (ContinuousLinearMap.inr ℝ ℝ^k (SpaceTime k))).IsInvertible := by
  have hpartial := hresidual.hasFDerivAt.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) y p)
  have hidentified := (hasFDerivAt_initialMomentumResidual_snd
    F boundary data y p hF).unique hpartial
  rw [← hidentified]
  obtain ⟨e, he⟩ := hnonchar
  rw [← he]
  let P : (SpaceTime k →L[ℝ] ℝ) →L[ℝ] ((ℝ^k × ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ℝ^k × ℝ) (SpaceTime k) ℝ).flip (e : (ℝ^k × ℝ) →L[ℝ] SpaceTime k)
  let Q : ((ℝ^k × ℝ) →L[ℝ] ℝ) →L[ℝ] (SpaceTime k →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (SpaceTime k) (ℝ^k × ℝ) ℝ).flip
      (e.symm : SpaceTime k →L[ℝ] (ℝ^k × ℝ))
  have hP : P.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := Q)
    · refine ContinuousLinearMap.ext fun f ↦ ?_
      refine ContinuousLinearMap.ext fun v ↦ ?_
      change f (e.symm (e v)) = f v
      rw [e.symm_apply_apply]
    · refine ContinuousLinearMap.ext fun f ↦ ?_
      refine ContinuousLinearMap.ext fun v ↦ ?_
      change f (e (e.symm v)) = f v
      rw [e.apply_symm_apply]
  have hRiesz : (innerSL ℝ : SpaceTime k →L[ℝ] (SpaceTime k →L[ℝ] ℝ)).IsInvertible :=
    ⟨(InnerProductSpace.toDual ℝ (SpaceTime k)).toContinuousLinearEquiv, rfl⟩
  exact hP.comp hRiesz

/-- Construct a compatible Cⁿ momentum field near a noncharacteristic
point from Cⁿ⁺¹ boundary/value data and one compatible base momentum.

The branch has the prescribed base value and is unique among nearby
momenta: in a neighborhood of `(y₀,p₀)`, compatibility is equivalent to
being on the constructed graph. Compatible momentum need not be
globally unique. -/
theorem exists_local_compatible_initialGradient (n : ℕ) (hn : 0 < n)
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (hF : ContDiff ℝ n (phaseFunction (n := k + 1) F))
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W)
    (hboundary : ContDiffOn ℝ (n + 1) boundary W) (hdata : ContDiffOn ℝ (n + 1) data W) (y0 : ℝ^k)
    (hy0 : y0 ∈ W) (p0 : SpaceTime k)
    (hcompat : IsCompatibleInitialGradientAt F boundary data y0 p0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 (data y0)) :
    ∃ U : Set (ℝ^k), IsOpen U ∧ y0 ∈ U ∧ U ⊆ W ∧
      ∃ initialGradient : ℝ^k → SpaceTime k,
        ContDiffOn ℝ n initialGradient U ∧ initialGradient y0 = p0 ∧
        (∀ y ∈ U,
          IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) ∧
        ∀ᶠ yp : ℝ^k × SpaceTime k in 𝓝 (y0, p0),
          IsCompatibleInitialGradientAt F boundary data yp.1 yp.2 ↔
            initialGradient yp.1 = yp.2 := by
  have hn0 : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hΨ : ContDiffAt ℝ n (initialMomentumResidual F boundary data) (y0, p0) :=
    (contDiffOn_initialMomentumResidual n F hF boundary data W hW hboundary hdata).contDiffAt
      ((hW.prod isOpen_univ).mem_nhds ⟨hy0, mem_univ p0⟩)
  have hJac := isInvertible_initialMomentumResidual_snd F boundary data y0 p0
    (hF.contDiffAt.differentiableAt hn0) (hΨ.differentiableAt hn0) hnonchar
  let initialGradient : ℝ^k → SpaceTime k := hΨ.implicitFunction hn0 hJac
  have hbase : initialGradient y0 = p0 := hΨ.implicitFunction_apply_self hn0 hJac
  have hzero : initialMomentumResidual F boundary data (y0, p0) = 0 :=
    (initialMomentumResidual_eq_zero_iff F boundary data y0 p0).mpr hcompat
  have hbranch : ∀ᶠ y in 𝓝 y0,
      IsCompatibleInitialGradientAt F boundary data y (initialGradient y) := by
    filter_upwards [hΨ.eventually_apply_implicitFunction hn0 hJac] with y hy
    exact (initialMomentumResidual_eq_zero_iff F boundary data y (initialGradient y)).mp
      (hy.trans hzero)
  have hregular : ContDiffAt ℝ n initialGradient y0 := hΨ.contDiffAt_implicitFunction hn0 hJac
  obtain ⟨V, hV, hVregular⟩ := hregular.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUsub, hUopen, hyU⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem (inter_mem (hW.mem_nhds hy0) hV) hbranch)
  refine ⟨U, hUopen, hyU, fun y hy ↦ (hUsub hy).1.1,
    initialGradient, hVregular.mono (fun y hy ↦ (hUsub hy).1.2), hbase, fun y hy ↦ (hUsub hy).2, ?_⟩
  filter_upwards [hΨ.eventually_apply_eq_iff_implicitFunction hn0 hJac] with yp hyp
  rw [hzero] at hyp
  exact (initialMomentumResidual_eq_zero_iff F boundary data yp.1 yp.2).symm.trans hyp

end

end NonlinearFirstOrder
