/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Inverse.Interval
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Normalization

/-!
# Parametrizing a whole characteristic curve segment by speed

The inverse is taken on a prescribed open parameter interval. Its image need not
be all of the real line, and either orientation of the original parameter is
allowed. The state profile has a continuous derivative even for a discontinuous
choice of eigenvector field, because that derivative is the invariant normalized
characteristic direction.

In the notation of the proof of Evans, §11.2.2, Theorem 1, `speedInverse C v l r` is
`G_k = (F_k')^{-1}`, since `F_k'(w) = λ_k(v(w))` by (8)-(9), and `speedProfile C v l r` is
`v ∘ G_k`, which gives the state `u(x, t) = v(G_k(x/t))` of the rarefaction wave inside the
fan. By (10), `λ_k ∘ v` has derivative `Dλ_k(v) · r_k(v)`, which is nonzero under genuine
nonlinearity (11), so the inverse exists on the parameter interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (6)-(11); §11.2.2, Theorem 1 and its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

namespace CharacteristicField

variable {m : ℕ} {flux : ℝ^m → ℝ^m}

/-- The inverse of characteristic speed along a curve, on its parameter
interval. Values outside the speed image are immaterial. -/
def speedInverse (C : CharacteristicField flux) (v : ℝ → ℝ^m) (l r : ℝ) : ℝ → ℝ :=
  Function.invFunOn (C.speed ∘ v) (Ioo l r)

/-- The same geometric curve parametrized by characteristic speed. -/
def speedProfile (C : CharacteristicField flux) (v : ℝ → ℝ^m) (l r : ℝ) : ℝ → ℝ^m :=
  v ∘ C.speedInverse v l r

/-- The derivative of speed along an open-interval integral curve. -/
theorem hasDerivAt_speed_comp (C : CharacteristicField flux) {v : ℝ → ℝ^m} {I : Set ℝ}
    (hI : IsOpen I) (hv : IsIntegralCurveOn v C.vectorField I) (hgn : C.IsGenuinelyNonlinear)
    {s : ℝ} (hs : s ∈ I) :
    HasDerivAt (C.speed ∘ v) (fderiv ℝ C.speed (v s) (C.rightEigenvector (v s))) s :=
  (hgn (v s)).1.hasFDerivAt.comp_hasDerivAt s (hv.isIntegralCurveAt (hI.mem_nhds hs)).hasDerivAt

/-- A genuinely nonlinear speed is injective along any interval
trajectory, without continuity of the selected eigenvectors. -/
theorem injOn_speed_comp (C : CharacteristicField flux) {v : ℝ → ℝ^m} {I : Set ℝ} (hI : IsOpen I)
    (hconn : OrdConnected I) (hv : IsIntegralCurveOn v C.vectorField I)
    (hgn : C.IsGenuinelyNonlinear) :
    InjOn (C.speed ∘ v) I :=
  PDE.Analysis.injOn_of_hasDerivAt_ne_zero hconn (fun _ hs ↦ C.hasDerivAt_speed_comp hI hv hgn hs)
    (fun s _ ↦ (hgn (v s)).2)

/-- The inverse retains its source interval and is a right inverse on the
speed image. -/
theorem speedInverse_mem_and_eq (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r ξ : ℝ}
    (hξ : ξ ∈ (C.speed ∘ v) '' Ioo l r) :
    C.speedInverse v l r ξ ∈ Ioo l r ∧ C.speed (C.speedProfile v l r ξ) = ξ :=
  ⟨Function.invFunOn_mem hξ, Function.invFunOn_eq hξ⟩

/-- The chosen inverse is also a left inverse at every parameter value. -/
theorem speedInverse_speed (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r s : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (hs : s ∈ Ioo l r) :
    C.speedInverse v l r (C.speed (v s)) = s :=
  (C.injOn_speed_comp isOpen_Ioo ordConnected_Ioo hv hgn).leftInvOn_invFunOn hs

/-- The reciprocal derivative of the original curve parameter. The parameter
need not be continuously differentiable. -/
theorem hasDerivAt_speedInverse (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r ξ : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (hξ : ξ ∈ (C.speed ∘ v) '' Ioo l r) :
    HasDerivAt (C.speedInverse v l r) (fderiv ℝ C.speed (C.speedProfile v l r ξ)
      (C.rightEigenvector (C.speedProfile v l r ξ)))⁻¹ ξ :=
  PDE.Analysis.hasDerivAt_invFunOn_Ioo (fun _ hs ↦ C.hasDerivAt_speed_comp isOpen_Ioo hv hgn hs)
    (fun s _ ↦ (hgn (v s)).2) hξ

/-- Reparametrization cancels the arbitrary scale of the original eigenfield. -/
theorem hasDerivAt_speedProfile (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r ξ : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (hξ : ξ ∈ (C.speed ∘ v) '' Ioo l r) :
    HasDerivAt (C.speedProfile v l r) (C.speedNormalizedField (C.speedProfile v l r ξ)) ξ :=
  (hv.isIntegralCurveAt (isOpen_Ioo.mem_nhds (C.speedInverse_mem_and_eq hξ).1)).hasDerivAt.scomp ξ
    (C.hasDerivAt_speedInverse hv hgn hξ)

/-- The invariant state profile is `C¹` throughout the open speed image. This
conclusion needs no continuity assumption on the original characteristic field. -/
theorem contDiffOn_speedProfile {k : Fin m} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (hgn : IsGenuinelyNonlinearFamily flux k)
    (C : CharacteristicField flux) (hspeed : C.speed = characteristicSpeed flux k) {v : ℝ → ℝ^m}
    {l r : ℝ} (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) :
    ContDiffOn ℝ 1 (C.speedProfile v l r) ((C.speed ∘ v) '' Ioo l r) := by
  have hC := (isGenuinelyNonlinearFamily_iff hhyper k C hspeed).mp hgn
  have hf : ContinuousOn (C.speed ∘ v) (Ioo l r) :=
    fun s hs ↦ (C.hasDerivAt_speed_comp isOpen_Ioo hv hC hs).continuousAt.continuousWithinAt
  have hopen := PDE.Analysis.isOpen_image_Ioo_of_continuousOn_injOn hf
    (C.injOn_speed_comp isOpen_Ioo ordConnected_Ioo hv hC)
  have hderiv := fun ξ hξ ↦ C.hasDerivAt_speedProfile hv hC (ξ := ξ) hξ
  have hP : ContinuousOn (C.speedProfile v l r) ((C.speed ∘ v) '' Ioo l r) :=
    fun ξ hξ ↦ (hderiv ξ hξ).continuousAt.continuousWithinAt
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hopen]
  refine ⟨fun ξ hξ ↦ (hderiv ξ hξ).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply contDiffOn_zero.mpr
  apply ((C.continuous_speedNormalizedField hflux hhyper hgn hspeed).comp_continuousOn hP).congr
  exact fun ξ hξ ↦ (hderiv ξ hξ).deriv

/-- The speed-parametrized state satisfies the conservative similarity ODE. -/
theorem fderiv_flux_speedProfile (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r ξ : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (hξ : ξ ∈ (C.speed ∘ v) '' Ioo l r) :
    fderiv ℝ flux (C.speedProfile v l r ξ) (deriv (C.speedProfile v l r) ξ) =
      ξ • deriv (C.speedProfile v l r) ξ := by
  rw [(C.hasDerivAt_speedProfile hv hgn hξ).deriv,
    C.fderiv_flux_speedNormalizedField, (C.speedInverse_mem_and_eq hξ).2]

/-- The speed image of the entire prescribed segment is the entire expansion
interval, including when the original parameter decreases from left to right. -/
theorem speed_image_uIcc (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) :
    (C.speed ∘ v) '' uIcc a b = Icc (C.speed (v a)) (C.speed (v b)) := by
  rw [PDE.Analysis.image_uIcc_of_continuousOn_injOn_Ioo
    (fun s hs ↦ (C.hasDerivAt_speed_comp isOpen_Ioo hv hgn hs).continuousAt.continuousWithinAt)
    (C.injOn_speed_comp isOpen_Ioo ordConnected_Ioo hv hgn) ha hb]
  exact uIcc_of_le hexpands

/-- The inverse traverses exactly the prescribed parameter segment. -/
theorem speedInverse_image_Icc (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) :
    C.speedInverse v l r '' Icc (C.speed (v a)) (C.speed (v b)) = uIcc a b := by
  rw [← C.speed_image_uIcc hv hgn ha hb hexpands]
  exact (C.injOn_speed_comp isOpen_Ioo ordConnected_Ioo hv hgn).invFunOn_image
    (ordConnected_Ioo.uIcc_subset ha hb)

/-- The speed profile has precisely the image of the whole original curve
segment. In particular no local neighborhood truncates the fan. -/
theorem speedProfile_image_Icc (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) :
    C.speedProfile v l r '' Icc (C.speed (v a)) (C.speed (v b)) = v '' uIcc a b := by
  rw [speedProfile, Set.image_comp, C.speedInverse_image_Icc hv hgn ha hb hexpands]

/-- If the original eigenvectors are continuous along the trajectory, the
original parameterization itself is `C¹`. This additional regularity is kept
separate from the choice-independent state-profile theorem. -/
theorem contDiffOn_integralCurve_of_continuousOn (C : CharacteristicField flux) {v : ℝ → ℝ^m}
    {I : Set ℝ} (hI : IsOpen I) (hv : IsIntegralCurveOn v C.vectorField I)
    (hr : ContinuousOn C.rightEigenvector (v '' I)) :
    ContDiffOn ℝ 1 v I := by
  have hderiv : ∀ s ∈ I, HasDerivAt v (C.rightEigenvector (v s)) s :=
    fun _ hs ↦ (hv.isIntegralCurveAt (hI.mem_nhds hs)).hasDerivAt
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply contDiffOn_zero.mpr
  apply (hr.comp hv.continuousOn (mapsTo_image v I)).congr
  exact fun s hs ↦ (hderiv s hs).deriv

/-- With a continuous original eigenfield the same interval inverse is `C¹`. -/
theorem contDiffOn_speedInverse_of_continuousOn {k : Fin m} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (hgn : IsGenuinelyNonlinearFamily flux k)
    (C : CharacteristicField flux) (hspeed : C.speed = characteristicSpeed flux k) {v : ℝ → ℝ^m}
    {l r : ℝ} (hv : IsIntegralCurveOn v C.vectorField (Ioo l r))
    (hr : ContinuousOn C.rightEigenvector (v '' Ioo l r)) :
    ContDiffOn ℝ 1 (C.speedInverse v l r) ((C.speed ∘ v) '' Ioo l r) := by
  have hC := (isGenuinelyNonlinearFamily_iff hhyper k C hspeed).mp hgn
  have heig : ContDiffOn ℝ 1 C.speed (v '' Ioo l r) := by
    intro q _
    rw [hspeed]
    exact (contDiffAt_characteristicSpeed hflux (hhyper q) k).contDiffWithinAt
  apply PDE.Analysis.contDiffOn_invFunOn_Ioo
    (heig.comp (C.contDiffOn_integralCurve_of_continuousOn isOpen_Ioo hv hr)
      (mapsTo_image v (Ioo l r)))
  intro s hs
  rw [(C.hasDerivAt_speed_comp isOpen_Ioo hv hC hs).deriv]
  exact (hC (v s)).2

end CharacteristicField

end PDE.Hyperbolic.ConservationLaw.System
