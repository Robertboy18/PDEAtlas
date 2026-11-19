/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy
public import PDE.Fluid.DeGregorio.Energy.Difference.Spatial
public import PDE.Fluid.DeGregorio.Model
import PDE.Representations.Similarity.Dynamic
import CAS.ExactTactic

/-!
# The rate of the vorticity difference energy

The same subtraction and spatial integration by parts apply to physical and
rescaled transport, with either global or interior time regularity. The derivative
of the energy enters `deriv_differenceEnergy_eq` as a hypothesis, so the identity
applies under either kind of time regularity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped ContDiff Topology

namespace DeGregorio

private theorem continuous_time_deriv {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    Continuous (fun p : ℝ × ℝ ↦ deriv (f p.1) p.2) := by
  have hD : Continuous (fun p : ℝ × ℝ ↦
      fderiv ℝ (Function.uncurry f) p (0, 1)) :=
    (hf.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  convert hD using 1
  funext p
  rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod f p.1 0 p.2 1
    (hf.differentiable (by simp)).differentiableAt]
  simp [fderiv_eq_smul_deriv]

/-- Joint `C¹` regularity derives the local domination needed to differentiate
the square integral over any fixed bounded spatial interval. -/
theorem hasDerivAt_integral_sq_Icc_of_contDiff {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (a b t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x in Icc a b, f x s ^ 2)
      (2 * ∫ x in Icc a b, f x t * deriv (f x) t) t := by
  have htime := continuous_time_deriv hf
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc (t - 1) (t + 1)) hf.continuous.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc (t - 1) (t + 1)) htime.continuousOn
  apply hasDerivAt_integral_sq_of_memLp_bounds
    (s := Ioo (t - 1) (t + 1)) (A := fun _ ↦ A) (B := fun _ ↦ B)
  · exact Ioo_mem_nhds (sub_lt_self t zero_lt_one) (lt_add_one t)
  · exact Eventually.of_forall fun s ↦
      (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (htime.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact memLp_const A
  · exact memLp_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro s hs
    exact ⟨hA (x, s) ⟨hx, hs.1.le, hs.2.le⟩, hB (x, s) ⟨hx, hs.1.le, hs.2.le⟩⟩
  · filter_upwards with x
    intro s _
    have hslice : ContDiff ℝ 1 (f x) := hf.comp (contDiff_const.prodMk contDiff_id)
    exact (hslice.differentiable (by norm_num) s).hasDerivAt

/-- Squared `L²` distance of two vorticities on a fixed spatial interval. -/
def differenceEnergy (fields other : Fields) (L t : ℝ) : ℝ :=
  ∫ x in Icc (-L) L, (fields.vorticity x t - other.vorticity x t) ^ 2

/-- The difference energy is nonnegative. -/
theorem differenceEnergy_nonneg (fields other : Fields) (L t : ℝ) :
    0 ≤ differenceEnergy fields other L t :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- Differentiation under the integral for two jointly `C¹` vorticities. -/
theorem hasDerivAt_differenceEnergy {fields other : Fields}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity)) (L t : ℝ) :
    HasDerivAt (differenceEnergy fields other L)
      (2 * ∫ x in Icc (-L) L,
        (fields.vorticity x t - other.vorticity x t) *
          deriv (fun s ↦ fields.vorticity x s - other.vorticity x s) t) t :=
  hasDerivAt_integral_sq_Icc_of_contDiff
    (f := fun x s ↦ fields.vorticity x s - other.vorticity x s) (hf.sub hg) (-L) L t

/-- Subtraction of two transport equations gives one energy-rate identity.
The spatial slices are C¹; time differentiation is required only at the time
under consideration. -/
theorem deriv_differenceEnergy_eq {fields other : Fields} {L t cl cw : ℝ}
    (hf : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t))
    (hg : ContDiff ℝ 1 (fun x ↦ other.vorticity x t))
    (hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hft : ∀ x, DifferentiableAt ℝ (fields.vorticity x) t)
    (hgt : ∀ x, DifferentiableAt ℝ (other.vorticity x) t)
    (henergy : HasDerivAt (differenceEnergy fields other L)
      (2 * ∫ x in Icc (-L) L, (fields.vorticity x t - other.vorticity x t) *
        deriv (fun s ↦ fields.vorticity x s - other.vorticity x s) t) t)
    (hsol : ∀ x, deriv (fields.vorticity x) t +
      (cl * x + fields.velocity x t) * deriv (fun y ↦ fields.vorticity y t) x =
        (cw + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t)
    (hother : ∀ x, deriv (other.vorticity x) t +
      (cl * x + other.velocity x t) * deriv (fun y ↦ other.vorticity y t) x =
        (cw + deriv (fun y ↦ other.velocity y t) x) * other.vorticity x t)
    (hleft : fields.vorticity (-L) t = other.vorticity (-L) t)
    (hright : fields.vorticity L t = other.vorticity L t) :
    let d := fun x ↦ fields.vorticity x t - other.vorticity x t
    let u := fun x ↦ fields.velocity x t
    let v := fun x ↦ fields.velocity x t - other.velocity x t
    let w := fun x ↦ other.vorticity x t
    deriv (differenceEnergy fields other L) t =
      (∫ x in Icc (-L) L, 3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x) + (2 * cw + cl) * differenceEnergy fields other L t := by
  rcases lt_or_ge L 0 with hL | hL
  · have he : Icc (-L) L = ∅ := Icc_eq_empty (by linarith)
    have h0 : differenceEnergy fields other L = fun _ ↦ 0 := by
      funext s
      simp [differenceEnergy, he]
    simp [h0, he]
  let d := fun x ↦ fields.vorticity x t - other.vorticity x t
  let u := fun x ↦ fields.velocity x t
  let v := fun x ↦ fields.velocity x t - other.velocity x t
  let w := fun x ↦ other.vorticity x t
  have hd : ContDiff ℝ 1 d := hf.sub hg
  have hv' : ContDiff ℝ 1 v := hu.sub hv
  have hres (x : ℝ) :
      deriv (fun s ↦ fields.vorticity x s - other.vorticity x s) t =
        (deriv u x * d x + deriv v x * w x - u x * deriv d x - v x * deriv w x) +
          (cw * d x - cl * x * deriv d x) := by
    have hdiffv : deriv v x = deriv (fun y ↦ fields.velocity y t) x -
        deriv (fun y ↦ other.velocity y t) x :=
      deriv_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)
    have hdiffd : deriv d x = deriv (fun y ↦ fields.vorticity y t) x -
        deriv (fun y ↦ other.vorticity y t) x :=
      deriv_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)
    change deriv (fields.vorticity x - other.vorticity x) t = _
    rw [deriv_sub (hft x) (hgt x), hdiffv, hdiffd]
    rw [eq_sub_of_add_eq (hsol x), eq_sub_of_add_eq (hother x)]
    dsimp only [u, v, d, w]
    cas
  rw [henergy.deriv]
  simp_rw [hres]
  have hD := hd.continuous_deriv le_rfl
  have hU := hu.continuous_deriv le_rfl
  have hV := hv'.continuous_deriv le_rfl
  have hW := hg.continuous_deriv le_rfl
  have hbase : Continuous (fun x ↦ d x *
      (deriv u x * d x + deriv v x * w x - u x * deriv d x - v x * deriv w x)) := by
    fun_prop
  have hlinear : Continuous (fun x ↦ d x * (cw * d x - cl * x * deriv d x)) := by
    fun_prop
  simp_rw [mul_add]
  rw [integral_add hbase.integrableOn_Icc hlinear.integrableOn_Icc, mul_add,
    integral_difference_transport_energy hd hu hv' hg hL
      (sub_eq_zero.mpr hleft) (sub_eq_zero.mpr hright),
    integral_linear_rescaling_energy hd hL (sub_eq_zero.mpr hleft) (sub_eq_zero.mpr hright)]
  rfl

/-- The vorticity difference of two Hilbert pairs with differentiable velocities
is paired with the derivative of the velocity difference. -/
theorem isHilbertPair_sub_of_differentiable {f g u v : ℝ → ℝ}
    (hu : ∀ x, DifferentiableAt ℝ u x) (hv : ∀ x, DifferentiableAt ℝ v x)
    (hf : IsHilbertPair f (deriv u)) (hg : IsHilbertPair g (deriv v)) :
    IsHilbertPair (f - g) (deriv fun x ↦ u x - v x) := by
  rw [show (deriv fun x ↦ u x - v x) = deriv u - deriv v from
    funext fun x ↦ deriv_sub (hu x) (hv x)]
  exact hf.sub hg

end DeGregorio
