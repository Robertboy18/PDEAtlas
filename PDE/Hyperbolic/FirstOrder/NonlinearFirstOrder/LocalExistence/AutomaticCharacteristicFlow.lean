/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ImplicitFunction
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.ExistUnique
import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Automatic characteristic flows for nonlinear first-order PDE

We construct the characteristic ODE (31) used in Evans, §3.2.4, directly from the Hamiltonian

`F(Du(x), u(x), x) = 0`.

For the characteristic state `q = (p,z,x)`, the autonomous vector field is

`q' = (-DₓF - F_z p, p · DₚF, DₚF)`.

Mathlib's Picard–Lindelöf theorem, applied to this vector field, gives local ODE
existence, the initial conditions, joint continuity of the selected flow, and all three
characteristic equations. The final theorem also propagates compatible initial data
along the flow, proving that the characteristic residual remains zero.

Conversely, a spatial characteristic of a C² classical solution lifts to
a solution of this phase ODE through its gradient and value. The
phase-lift theorem requires only a C¹ Hamiltonian; its momentum equation
follows from differentiating the PDE. This is Theorem 1 of Evans, §3.2.1, and the propagation
of compatible data is step 2, equations (39)-(40), of the proof of Theorem 2 in §3.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.1, Theorem 1, equation (11); §3.2.4, equations (31)-(32)
  and the proof of Theorem 2, equations (39)-(40).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open scoped NNReal RealInnerProductSpace Topology
open Metric Set

variable {k : ℕ}

/-- Direction in phase space which varies the momentum coordinate `i`. -/
noncomputable def momentumDirection (i : Fin (k + 1)) :
    SpaceTime k × (ℝ × SpaceTime k) :=
  (EuclideanSpace.single i 1, (0, 0))

/-- Direction in phase space which varies the height coordinate. -/
noncomputable def heightDirection : (SpaceTime k × (ℝ × SpaceTime k)) :=
  (0, (1, 0))

/-- Direction in phase space which varies the spatial coordinate `i`. -/
noncomputable def spatialDirection (i : Fin (k + 1)) :
    (SpaceTime k × (ℝ × SpaceTime k)) :=
  (0, (0, EuclideanSpace.single i 1))

/-- The momentum derivative of `F`, read directly from the Fréchet
derivative of the uncurried Hamiltonian. -/
noncomputable def characteristicDp
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (q : (SpaceTime k × (ℝ × SpaceTime k))) : SpaceTime k :=
  WithLp.toLp 2 fun i ↦
    fderiv ℝ (phaseFunction (n := k + 1) F) q (momentumDirection i)

/-- The height derivative of `F`, read directly from the Fréchet derivative
of the uncurried Hamiltonian. -/
noncomputable def characteristicDz
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (q : (SpaceTime k × (ℝ × SpaceTime k))) : ℝ :=
  fderiv ℝ (phaseFunction (n := k + 1) F) q heightDirection

/-- The spatial derivative of `F`, read directly from the Fréchet
derivative of the uncurried Hamiltonian. -/
noncomputable def characteristicDx
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (q : (SpaceTime k × (ℝ × SpaceTime k))) : SpaceTime k :=
  WithLp.toLp 2 fun i ↦
    fderiv ℝ (phaseFunction (n := k + 1) F) q (spatialDirection i)

/-- Evans's autonomous characteristic vector field (equation (11), repeated as (31)) on
`(p,z,x)` phase space. -/
noncomputable def characteristicVectorField
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) :
    (SpaceTime k × (ℝ × SpaceTime k)) → (SpaceTime k × (ℝ × SpaceTime k)) :=
  fun q ↦
    (-characteristicDx F q - characteristicDz F q • q.1,
      (inner ℝ (characteristicDp F q) q.1, characteristicDp F q))

/-- Boundary data lifted to the initial characteristic state. -/
noncomputable def characteristicInitialState
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (initialGradient : ℝ^k → SpaceTime k) :
    ℝ^k → (SpaceTime k × (ℝ × SpaceTime k)) :=
  fun y ↦ (initialGradient y, (data y, boundary y))

private theorem fderiv_phaseFunction_momentum (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (p : SpaceTime k) (z : ℝ) (x dp : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (z, x))) :
    fderiv ℝ (phaseFunction (n := k + 1) F) (p, (z, x)) (dp, (0, 0)) =
      fderiv ℝ (fun q : SpaceTime k ↦ F q z x) p dp :=
  (congrArg (· dp) (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (z, x))).fderiv).symm

private theorem fderiv_phaseFunction_height (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (p : SpaceTime k) (z dz : ℝ) (x : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (z, x))) :
    fderiv ℝ (phaseFunction (n := k + 1) F) (p, (z, x)) (0, (dz, 0)) =
      fderiv ℝ (fun r : ℝ ↦ F p r x) z dz :=
  (congrArg (· dz) (hF.hasFDerivAt.comp z ((hasFDerivAt_prodMk_right (𝕜 := ℝ) p (z, x)).comp z
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z x))).fderiv).symm

private theorem fderiv_phaseFunction_spatial (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (p : SpaceTime k) (z : ℝ) (x dx : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (z, x))) :
    fderiv ℝ (phaseFunction (n := k + 1) F) (p, (z, x)) (0, (0, dx)) =
      fderiv ℝ (fun y : SpaceTime k ↦ F p z y) x dx :=
  (congrArg (· dx) (hF.hasFDerivAt.comp x ((hasFDerivAt_prodMk_right (𝕜 := ℝ) p (z, x)).comp x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z x))).fderiv).symm

/-- The phase-space momentum derivative agrees with LeanPDE's `momentumGradient`. -/
theorem characteristicDp_eq_DpF (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F)) (q : (SpaceTime k × (ℝ × SpaceTime k))) :
    characteristicDp F q = momentumGradient (n := k + 1) F q.1 q.2.1 q.2.2 := by
  rcases q with ⟨p, z, x⟩
  ext i
  exact (fderiv_phaseFunction_momentum F p z x _ (hF (p, (z, x)))).trans
    (PDE.fderiv_apply_single_one_eq_gradient_apply (fun q ↦ F q z x) p i)

/-- The phase-space height derivative agrees with LeanPDE's `valueDerivative`. -/
theorem characteristicDz_eq_DzF (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F)) (q : (SpaceTime k × (ℝ × SpaceTime k))) :
    characteristicDz F q = valueDerivative (n := k + 1) F q.1 q.2.1 q.2.2 := by
  rcases q with ⟨p, z, x⟩
  simpa [characteristicDz, heightDirection, valueDerivative, fderiv_eq_smul_deriv] using
    fderiv_phaseFunction_height F p z 1 x (hF (p, (z, x)))

/-- The phase-space spatial derivative agrees with LeanPDE's `positionGradient`. -/
theorem characteristicDx_eq_DxF (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F)) (q : (SpaceTime k × (ℝ × SpaceTime k))) :
    characteristicDx F q = positionGradient (n := k + 1) F q.1 q.2.1 q.2.2 := by
  rcases q with ⟨p, z, x⟩
  ext i
  exact (fderiv_phaseFunction_spatial F p z x _ (hF (p, (z, x)))).trans
    (PDE.fderiv_apply_single_one_eq_gradient_apply (fun y ↦ F p z y) x i)

/-- Expand the differential of the Hamiltonian into its momentum, height,
and spatial components.

This is the coordinate-free form of the first-order chain rule used
throughout Evans's characteristic calculation:

`DF(p,z,x)[dp,dz,dx] = DₚF · dp + F_z dz + DₓF · dx`. -/
theorem fderiv_phaseFunction_apply_eq_characteristic_components
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (p dp : SpaceTime k) (z dz : ℝ) (x dx : SpaceTime k)
    (hF : DifferentiableAt ℝ (phaseFunction (n := k + 1) F) (p, (z, x))) :
    fderiv ℝ (phaseFunction (n := k + 1) F) (p, (z, x)) (dp, (dz, dx)) =
      inner ℝ (momentumGradient (n := k + 1) F p z x) dp + valueDerivative (n := k + 1) F p z x *
      dz + inner ℝ (positionGradient (n := k + 1) F p z x) dx := by
  rw [show (dp, (dz, dx)) = (dp, ((0 : ℝ), (0 : SpaceTime k))) + (0, (dz, (0 : SpaceTime k))) +
      (0, ((0 : ℝ), dx)) by ext <;> simp, map_add, map_add,
    fderiv_phaseFunction_momentum F p z x dp hF, fderiv_phaseFunction_height F p z dz x hF,
    fderiv_phaseFunction_spatial F p z x dx hF, ← inner_gradient_left (𝕜 := ℝ),
    fderiv_eq_deriv_mul, ← inner_gradient_left (𝕜 := ℝ)]
  simp [momentumGradient, valueDerivative, positionGradient, add_assoc]

/-- The three phase-space derivatives of a `Cᵐ⁺¹` Hamiltonian are `Cᵐ`. -/
private theorem contDiff_characteristicDerivatives {m : ℕ} (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ (m + 1) (phaseFunction (n := k + 1) F)) :
    ContDiff ℝ m (characteristicDp F) ∧ ContDiff ℝ m (characteristicDz F) ∧
      ContDiff ℝ m (characteristicDx F) := by
  have h (v : SpaceTime k × (ℝ × SpaceTime k)) :
      ContDiff ℝ m fun q ↦ fderiv ℝ (phaseFunction (n := k + 1) F) q v :=
    (hF.fderiv_right le_rfl).clm_apply contDiff_const
  exact ⟨contDiff_piLp _ |>.2 fun i ↦ h _, h _, contDiff_piLp _ |>.2 fun i ↦ h _⟩

/-- A `C²` Hamiltonian has a `C¹` height derivative along phase space. -/
theorem contDiff_characteristicDz (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) :
    ContDiff ℝ 1 (characteristicDz F) :=
  (contDiff_characteristicDerivatives (m := 1) F hF).2.1

/-- A `C²` Hamiltonian produces a `C¹` characteristic vector field. -/
theorem contDiff_characteristicVectorField (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) :
    ContDiff ℝ 1 (characteristicVectorField F) := by
  obtain ⟨hp, hz, hx⟩ := contDiff_characteristicDerivatives (m := 1) F hF
  exact (hx.neg.sub (hz.smul contDiff_fst)).prodMk ((hp.inner ℝ contDiff_fst).prodMk hp)

/-- A `C³` Hamiltonian produces a `C²` characteristic vector field. -/
theorem contDiff_two_characteristicVectorField (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 3 (phaseFunction (n := k + 1) F)) :
    ContDiff ℝ 2 (characteristicVectorField F) := by
  obtain ⟨hp, hz, hx⟩ := contDiff_characteristicDerivatives (m := 2) F hF
  exact (hx.neg.sub (hz.smul contDiff_fst)).prodMk ((hp.inner ℝ contDiff_fst).prodMk hp)

/-- The lifted boundary state is `C¹` when the boundary, boundary value, and
compatible initial-gradient field are `C¹`. -/
theorem contDiff_characteristicInitialState (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (initialGradient : ℝ^k → SpaceTime k) (hboundary : ContDiff ℝ 1 boundary)
    (hdata : ContDiff ℝ 1 data) (hgradient : ContDiff ℝ 1 initialGradient) :
    ContDiff ℝ 1 (characteristicInitialState boundary data initialGradient) :=
  hgradient.prodMk (hdata.prodMk hboundary)

/-- Automatic local characteristic family obtained from Picard–Lindelöf.

The selected map `flow q s` is jointly continuous on a phase-space ball
times a common time interval.  For every initial state in the ball it
starts at that state and solves Evans's characteristic ODE. -/
theorem exists_local_characteristic_flow (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) (q0 : (SpaceTime k × (ℝ × SpaceTime k))) :
    ∃ r : ℝ, 0 < r ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ flow : (SpaceTime k × (ℝ × SpaceTime k)) × ℝ → (SpaceTime k × (ℝ × SpaceTime k)),
          ContinuousOn flow (closedBall q0 r ×ˢ Icc (-ε) ε) ∧
          ∀ q ∈ closedBall q0 r,
            flow (q, 0) = q ∧
              ∀ s ∈ Ioo (-ε) ε,
                HasDerivAt (fun τ ↦ flow (q, τ))
                  (characteristicVectorField F (flow (q, s))) s := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (contDiff_characteristicVectorField F hF).contDiffAt
  obtain ⟨flow, hflow, hcontinuous⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, ε, hε, flow, by simpa using hcontinuous, fun q hq ↦
    ⟨by simpa using (hflow q hq).1, fun s hs ↦ ?_⟩⟩
  have hs' : s ∈ Ioo (0 - ε) (0 + ε) := by simpa only [zero_sub, zero_add] using hs
  exact ((hflow q hq).2 s (Ioo_subset_Icc_self hs')).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)

/-- Automatic characteristic curves issued from a `C¹` family of boundary
phase states.

The theorem shrinks the boundary-parameter neighborhood so all initial
states lie in the common Picard–Lindelöf ball. It is a separate hypothesis of the PDE construction
in `ClassicalSolution`. -/
theorem exists_local_characteristic_family (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k) (y0 : ℝ^k)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) (hboundary : ContDiff ℝ 1 boundary)
    (hdata : ContDiff ℝ 1 data) (hgradient : ContDiff ℝ 1 initialGradient) :
    ∃ W : Set (ℝ^k), IsOpen W ∧ y0 ∈ W ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ curve : ℝ^k × ℝ → (SpaceTime k × (ℝ × SpaceTime k)),
          ContinuousOn curve (W ×ˢ Icc (-ε) ε) ∧
          ∀ y ∈ W, curve (y, 0) = characteristicInitialState boundary data initialGradient y ∧
            ∀ s ∈ Ioo (-ε) ε,
              HasDerivAt (fun τ ↦ curve (y, τ)) (characteristicVectorField F (curve (y, s))) s := by
  let initial := characteristicInitialState boundary data initialGradient
  have hinitial : ContDiff ℝ 1 initial :=
    contDiff_characteristicInitialState boundary data initialGradient hboundary hdata hgradient
  obtain ⟨r, hr, ε, hε, flow, hflowCont, hflow⟩ :=
    exists_local_characteristic_flow F hF (initial y0)
  have hball {y} (hy : y ∈ initial ⁻¹' ball (initial y0) r) :
      initial y ∈ closedBall (initial y0) r := mem_closedBall.mpr (mem_ball.mp hy).le
  exact ⟨initial ⁻¹' ball (initial y0) r, isOpen_ball.preimage hinitial.continuous,
    mem_ball_self hr, ε, hε, fun ys ↦ flow (initial ys.1, ys.2),
    hflowCont.comp ((hinitial.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun ys hys ↦ ⟨hball hys.1, hys.2⟩,
    fun y hy ↦ ⟨(hflow (initial y) (hball hy)).1, (hflow (initial y) (hball hy)).2⟩⟩

/-- The automatically generated phase-space ODE, written as Evans's three
component equations (11), repeated as system (31). -/
theorem characteristic_equations_of_hasDerivAt (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F))
    (curve : ℝ → (SpaceTime k × (ℝ × SpaceTime k))) (s : ℝ)
    (hcurve : HasDerivAt curve (characteristicVectorField F (curve s)) s) :
    HasDerivAt (fun τ ↦ (curve τ).1)
        (-positionGradient (n := k + 1) F (curve s).1 (curve s).2.1 (curve s).2.2 -
          valueDerivative (n := k + 1) F (curve s).1 (curve s).2.1 (curve s).2.2 •
            (curve s).1) s ∧
      HasDerivAt (fun τ ↦ (curve τ).2.1)
        (inner ℝ
          (momentumGradient (n := k + 1) F (curve s).1 (curve s).2.1 (curve s).2.2)
          (curve s).1) s ∧
      HasDerivAt (fun τ ↦ (curve τ).2.2)
        (momentumGradient (n := k + 1) F
          (curve s).1 (curve s).2.1 (curve s).2.2) s := by
  have hp : HasDerivAt (fun τ ↦ (curve τ).1)
      (-characteristicDx F (curve s) - characteristicDz F (curve s) • (curve s).1) s := by
    simpa [characteristicVectorField] using hcurve.hasFDerivAt.fst.hasDerivAt
  have hz : HasDerivAt (fun τ ↦ (curve τ).2.1)
      (inner ℝ (characteristicDp F (curve s)) (curve s).1) s := by
    simpa [characteristicVectorField] using hcurve.hasFDerivAt.snd.fst.hasDerivAt
  have hx : HasDerivAt (fun τ ↦ (curve τ).2.2) (characteristicDp F (curve s)) s := by
    simpa [characteristicVectorField] using hcurve.hasFDerivAt.snd.snd.hasDerivAt
  rw [characteristicDz_eq_DzF F hF (curve s), characteristicDx_eq_DxF F hF (curve s)] at hp
  rw [characteristicDp_eq_DpF F hF (curve s)] at hz hx
  exact ⟨hp, hz, hx⟩

section SolutionPhase

/-- A spatial characteristic of a C² classical solution lifts to a
solution of the full phase ODE. The momentum equation follows from the
differentiated PDE, rather than a supplied contact or consistency condition. -/
theorem hasDerivAt_solution_phase_of_spatial_characteristic (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 1 (phaseFunction F)) (u : SpaceTime k → ℝ) (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hpde : ∀ x ∈ Ω, F (∇ u x) (u x) x = 0)
    (X : ℝ → SpaceTime k) (t : ℝ) (hx : X t ∈ Ω)
    (hX : HasDerivAt X (momentumGradient F (∇ u (X t)) (u (X t)) (X t)) t) :
    HasDerivAt (fun s ↦ (∇ u (X s), (u (X s), X s)))
      (characteristicVectorField F (∇ u (X t), (u (X t), X t))) t := by
  have huAt : ContDiffAt ℝ 2 u (X t) := hu.contDiffAt (hΩ.mem_nhds hx)
  have hpDiff : DifferentiableAt ℝ (fun s ↦ ∇ u (X s)) t :=
    (differentiableAt_gradient u (X t) huAt).comp t hX.differentiableAt
  have hzDiff : DifferentiableAt ℝ (fun s ↦ u (X s)) t :=
    (huAt.differentiableAt (by norm_num)).comp t hX.differentiableAt
  obtain ⟨hz, hp, _⟩ :=
    characteristic_equations_at F u X t hΩ hx hF hu hpde hX.differentiableAt hX.deriv
  have hphase := hpDiff.hasDerivAt.prodMk (hzDiff.hasDerivAt.prodMk hX)
  rw [hp, hz] at hphase
  simpa only [characteristicVectorField,
    characteristicDp_eq_DpF F (hF.differentiable (by norm_num)),
    characteristicDx_eq_DxF F (hF.differentiable (by norm_num)),
    characteristicDz_eq_DzF F (hF.differentiable (by norm_num))] using hphase

end SolutionPhase

/-- The Hamiltonian residual has zero derivative along an automatically
generated characteristic. -/
theorem hasDerivAt_residual_zero_of_characteristic (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 1 (phaseFunction (n := k + 1) F))
    (curve : ℝ → (SpaceTime k × (ℝ × SpaceTime k))) (s : ℝ)
    (hcurve : HasDerivAt curve (characteristicVectorField F (curve s)) s) :
    HasDerivAt (fun τ ↦ F (curve τ).1 (curve τ).2.1 (curve τ).2.2) 0 s := by
  obtain ⟨hp, hz, hx⟩ := characteristic_equations_of_hasDerivAt F
    (hF.differentiable (by norm_num)) curve s hcurve
  exact (((hF.differentiable (by norm_num) (curve s)).comp s hcurve.differentiableAt).hasDerivAt :
    HasDerivAt (fun τ ↦ F (curve τ).1 (curve τ).2.1 (curve τ).2.2) _ s).congr_deriv
    (deriv_residual_along_characteristic_eq_zero (n := k + 1) (F := F) (p := fun τ ↦ (curve τ).1)
      (z := fun τ ↦ (curve τ).2.1) (xcurve := fun τ ↦ (curve τ).2.2) s
      (hF.contDiffAt.differentiableAt (by norm_num)) hp.differentiableAt hz.differentiableAt
      hx.differentiableAt hp.deriv hz.deriv hx.deriv)

/-- Compatible initial data remain on the hypersurface `F=0` throughout
the automatically generated characteristic interval. -/
theorem residual_eq_zero_of_characteristic (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (hF : ContDiff ℝ 1 (phaseFunction (n := k + 1) F))
    (curve : ℝ → (SpaceTime k × (ℝ × SpaceTime k))) (ε : ℝ) (hε : 0 < ε)
    (hcurve : ∀ s ∈ Ioo (-ε) ε, HasDerivAt curve (characteristicVectorField F (curve s)) s)
    (hinitial : F (curve 0).1 (curve 0).2.1 (curve 0).2.2 = 0) {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    F (curve s).1 (curve s).2.1 (curve s).2.2 = 0 := by
  have hd (τ) (hτ : τ ∈ Ioo (-ε) ε) :=
    hasDerivAt_residual_zero_of_characteristic F hF curve τ (hcurve τ hτ)
  rw [isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun τ hτ ↦ (hd τ hτ).differentiableAt.differentiableWithinAt) (fun τ hτ ↦ (hd τ hτ).deriv) hs
    ⟨neg_lt_zero.mpr hε, hε⟩, hinitial]

/-- Picard–Lindelöf produces Evans's characteristic system from the
`C²` Hamiltonian and `C¹` boundary data.

Unlike `exists_local_characteristic_family`, this formulation exposes the
three component equations directly in terms of `momentumGradient`, `valueDerivative`, and
`positionGradient`.
-/
theorem exists_local_evans_characteristics (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k) (y0 : ℝ^k)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) (hboundary : ContDiff ℝ 1 boundary)
    (hdata : ContDiff ℝ 1 data) (hgradient : ContDiff ℝ 1 initialGradient) :
    ∃ W : Set (ℝ^k), IsOpen W ∧ y0 ∈ W ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ curve : ℝ^k × ℝ → (SpaceTime k × (ℝ × SpaceTime k)),
          ContinuousOn curve (W ×ˢ Icc (-ε) ε) ∧
          ∀ y ∈ W, curve (y, 0) = characteristicInitialState boundary data initialGradient y ∧
            ∀ s ∈ Ioo (-ε) ε,
              HasDerivAt (fun τ ↦ (curve (y, τ)).1)
                  (-positionGradient (n := k + 1) F (curve (y, s)).1 (curve (y, s)).2.1
                      (curve (y, s)).2.2 -
                    valueDerivative (n := k + 1) F (curve (y, s)).1 (curve (y, s)).2.1
                        (curve (y, s)).2.2 • (curve (y, s)).1) s ∧
                HasDerivAt (fun τ ↦ (curve (y, τ)).2.1) (inner ℝ (momentumGradient (n := k + 1) F
                  (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2) (curve (y, s)).1) s ∧
                HasDerivAt (fun τ ↦ (curve (y, τ)).2.2) (momentumGradient (n := k + 1) F
                  (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2) s := by
  obtain ⟨W, hW, hy0, ε, hε, curve, hcont, hcurve⟩ :=
    exists_local_characteristic_family F boundary data initialGradient y0
      hF hboundary hdata hgradient
  exact ⟨W, hW, hy0, ε, hε, curve, hcont, fun y hy ↦ ⟨(hcurve y hy).1, fun s hs ↦
    characteristic_equations_of_hasDerivAt F (hF.differentiable (by norm_num))
      (fun τ ↦ curve (y, τ)) s ((hcurve y hy).2 s hs)⟩⟩

/-- The automatically generated Evans characteristics preserve compatible
initial residual data.

This is the complete ODE-existence and constraint-preservation part of the
method of characteristics. -/
theorem exists_local_characteristics_preserving_residual (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k) (y0 : ℝ^k)
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F)) (hboundary : ContDiff ℝ 1 boundary)
    (hdata : ContDiff ℝ 1 data) (hgradient : ContDiff ℝ 1 initialGradient)
    (hcompat : ∀ᶠ y in 𝓝 y0, IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) :
    ∃ W : Set (ℝ^k), IsOpen W ∧ y0 ∈ W ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ curve : ℝ^k × ℝ → (SpaceTime k × (ℝ × SpaceTime k)),
          ContinuousOn curve (W ×ˢ Icc (-ε) ε) ∧
          (∀ y ∈ W, curve (y, 0) = characteristicInitialState boundary data initialGradient y) ∧
          (∀ y ∈ W, ∀ s ∈ Ioo (-ε) ε,
            HasDerivAt (fun τ ↦ curve (y, τ)) (characteristicVectorField F (curve (y, s))) s) ∧
          ∀ y ∈ W, ∀ s ∈ Ioo (-ε) ε,
            F (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2 = 0 := by
  obtain ⟨W, hW, hy0, ε, hε, curve, hcont, hcurve⟩ :=
    exists_local_characteristic_family F boundary data initialGradient y0
      hF hboundary hdata hgradient
  obtain ⟨U, hUcompat, hUopen, hy0U⟩ := _root_.mem_nhds_iff.mp hcompat
  refine ⟨W ∩ U, hW.inter hUopen, ⟨hy0, hy0U⟩, ε, hε, curve,
    hcont.mono (prod_mono inter_subset_left Subset.rfl), fun y hy ↦ (hcurve y hy.1).1,
    fun y hy s hs ↦ (hcurve y hy.1).2 s hs, fun y hy s hs ↦ ?_⟩
  refine residual_eq_zero_of_characteristic F (hF.of_le (by norm_num)) (fun τ ↦ curve (y, τ)) ε hε
    (fun τ hτ ↦ (hcurve y hy.1).2 τ hτ) ?_ hs
  simpa [(hcurve y hy.1).1, characteristicInitialState] using (hUcompat hy.2).1

end

end NonlinearFirstOrder
