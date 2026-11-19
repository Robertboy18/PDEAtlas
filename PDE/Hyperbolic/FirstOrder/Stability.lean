/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Stability
public import PDE.Hyperbolic.FirstOrder.SobolevEnergy
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# L2 stability for the original symmetric transport equation

The difference estimate below uses the spatial weak derivatives of H1 states and
absolutely continuous L2 representatives satisfying the original equation almost everywhere.
The forcing difference is only L2 in time and space. The exponential constant contains the
coefficient divergence bound and no H1 norm of either state or forcing.

The theorem assumes absolutely continuous representatives and their a.e. drift equations.
For the H1 Cauchy construction these come from the identity-triple evolution; for
L2 weak solutions see `L2Uniqueness`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

/-- Two solutions of the same symmetric transport system obey the L2 difference estimate.
The a.e. equations use weak spatial derivatives of H1 states. Their L2 representatives
are absolutely continuous; only the L2 forcing difference is required. Symmetry and the
coefficient divergence bound need hold only almost everywhere in time. -/
theorem norm_sub_sq_le_exp_of_symmetric_transport {n : ℕ} {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a ≤ b) (A : ℝ → Fin n → ι → ι → W^{1,∞}((univ : Set (ℝ^n))))
    (hsym : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ)
      (baseIndex n 1) = (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hdiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (∑ j, ∑ p, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) ≤ C)
    {u v f g : ℝ → PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)} {U V : ℝ → ι → H¹(ℝ^n)}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hfg : MemLp (fun t ↦ f t - g t) 2 (volume.restrict (Ioc a b))) :
    let base := fun W : ι → H¹(ℝ^n) ↦
      WithLp.toLp 2 (fun p ↦ wkpCoordinateCLM (baseIndex n 1) (W p));
    let drift := fun t (W : ι → H¹(ℝ^n)) ↦
      WithLp.toLp 2 (fun p ↦ -(∑ j, ∑ q,
        ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          wkpCoordinateCLM (singleDerivIndex n j) (W q)));
    (u =ᵐ[volume.restrict (Ioc a b)] fun t ↦ base (U t)) →
    (v =ᵐ[volume.restrict (Ioc a b)] fun t ↦ base (V t)) →
    (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (drift t (U t) + f t) t) →
    (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt v (drift t (V t) + g t) t) →
    ∀ t ∈ Icc a b,
      ‖u t - v t‖ ^ 2 ≤
        (‖u a - v a‖ ^ 2 + ∫ s in a..b, ‖f s - g s‖ ^ 2) *
          Real.exp ((C + 1) * (t - a)) := by
  intro base drift hU hV heu hev
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ X Y : ι → H¹(ℝ^n),
      2 * ⟪drift t X - drift t Y, base X - base Y⟫_ℝ ≤
        C * ‖base X - base Y‖ ^ 2 := by
    filter_upwards [hsym, hdiv] with t htSym htDiv
    intro X Y
    have hspatial : 2 * ⟪drift t X - drift t Y, base X - base Y⟫_ℝ ≤ (∑ j, ∑ p, ∑ q,
            ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) *
              ‖base X - base Y‖ ^ 2 :=
      symmetric_system_transport_difference_energy_le (n := n) (ι := ι) (A t) htSym X Y
    exact hspatial.trans (mul_le_mul_of_nonneg_right htDiv (sq_nonneg ‖base X - base Y‖))
  exact norm_sub_sq_le_exp_of_ae_drift_equations
    (H := PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) (S := ι → H¹(ℝ^n))
    (u := u) (v := v) (U := U) (V := V) (f := f) (g := g) (C := C)
    hab base drift hu hv hU hV heu hev hfg hC hbound

end PDE.Hyperbolic.FirstOrder
