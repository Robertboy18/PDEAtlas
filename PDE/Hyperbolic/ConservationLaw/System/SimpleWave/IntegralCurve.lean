/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Local
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

/-!
# Local characteristic integral curves

A C² flux near a strictly hyperbolic state determines local C¹ ordered eigenfields.
The local ODE flow constructs a curve through that state for each characteristic
family. The curve is C²: its derivative is the C¹ eigenfield evaluated along the
C¹ trajectory. The characteristic speed along the curve is C¹.

The eigenfields come from the same normalized local spectral frame used for
Riemann invariant coordinates.

The curve is the rarefaction curve `Rₖ(z₀)` of Evans, §11.2.1, the path of the solution of (6)
through the base state, up to reparametrization: Evans normalizes the eigenvectors to unit
length, while ours are normalized by a coordinate in the base eigenbasis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equation (6) and the definition of rarefaction
  curves.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Construct a nonstationary integral curve of an ordered characteristic field
from a C² flux germ. Both the eigenfield and the curve are outputs; all states
on the displayed interval remain strictly hyperbolic. -/
theorem exists_local_characteristic_integral_curve {m : ℕ} {flux : ℝ^m → ℝ^m} {q₀ : ℝ^m}
    (hflux : ContDiffAt ℝ 2 flux q₀) (hhyper : IsStrictlyHyperbolicAt flux q₀) (k : Fin m) :
    ∃ r : ℝ^m → ℝ^m, ∃ R : ℝ → ℝ^m, ∃ ε : ℝ,
      0 < ε ∧ R 0 = q₀ ∧ ContDiffAt ℝ 1 r q₀ ∧
      ContDiffOn ℝ 2 R (Ioo (-ε) ε) ∧
      ContDiffOn ℝ 1 (characteristicSpeed flux k ∘ R) (Ioo (-ε) ε) ∧
      ∀ s ∈ Ioo (-ε) ε,
        IsStrictlyHyperbolicAt flux (R s) ∧
        HasDerivAt R (r (R s)) s ∧
        Module.End.HasEigenvector (fderiv ℝ flux (R s)).toLinearMap
          (characteristicSpeed flux k (R s)) (r (R s)) := by
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec hhyper
  obtain ⟨ψ, hbase, U, hU, hAU, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux q₀) (fun i ↦ characteristicSpeed flux i q₀) hb horder
  let r : ℝ^m → ℝ^m := fun q ↦ (ψ k (fderiv ℝ flux q)).1
  let a : ℝ^m → ℝ := fun q ↦ (ψ k (fderiv ℝ flux q)).2
  have hD : ContDiffAt ℝ 1 (fderiv ℝ flux) q₀ := hflux.fderiv_right le_rfl
  have hr : ContDiffAt ℝ 1 r q₀ :=
    ((((hframe _ hAU).2.1 k).1.of_le (by simp)).comp q₀ hD).fst
  have hnear : ∀ᶠ q in 𝓝 q₀, IsStrictlyHyperbolicAt flux q ∧ ContDiffAt ℝ 1 r q ∧
      ContDiffAt ℝ 1 a q ∧ a q = characteristicSpeed flux k q ∧
      Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
        (characteristicSpeed flux k q) (r q) := by
    filter_upwards [hflux.eventually (by simp),
      hD.continuousAt.eventually (hU.mem_nhds hAU)] with q hfq hqU
    obtain ⟨hord, hvec, bq, hbq⟩ := hframe _ hqU
    have hcanonical := characteristicSpeed_eq_of_eigenbasis bq hord
      (fun i ↦ by rw [hbq i]; exact (hvec i).2.1.apply_eq_smul)
    have hreg := ((hvec k).1.of_le (show (1 : ℕ∞ω) ≤ ω by simp)).comp q (hfq.fderiv_right le_rfl)
    exact ⟨⟨hfq.differentiableAt (by simp), bq, _, hord.injective,
        fun i ↦ by rw [hbq i]; exact (hvec i).2.1⟩,
      hreg.fst, hreg.snd, (congrFun hcanonical k).symm, congrFun hcanonical k ▸ (hvec k).2.1⟩
  obtain ⟨flow, hflow₀, hflowreg, _, hflow⟩ := PDE.Analysis.ODE.exists_local_flow_of_contDiffAt hr
  let R : ℝ → ℝ^m := fun s ↦ flow (s, q₀)
  have hR₀ : R 0 = q₀ := hflow₀
  have hR : ContDiffAt ℝ 1 R 0 := hflowreg.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hgood : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 1 R s ∧ HasDerivAt R (r (R s)) s ∧
      IsStrictlyHyperbolicAt flux (R s) ∧ ContDiffAt ℝ 1 r (R s) ∧
      ContDiffAt ℝ 1 a (R s) ∧ a (R s) = characteristicSpeed flux k (R s) ∧
      Module.End.HasEigenvector (fderiv ℝ flux (R s)).toLinearMap
        (characteristicSpeed flux k (R s)) (r (R s)) := by
    filter_upwards [hR.eventually (by simp),
      (continuousAt_id.prodMk continuousAt_const).tendsto.eventually hflow,
      hR.continuousAt.eventually (hR₀.symm ▸ hnear)] with s hs hds hspec
    exact ⟨hs, hds, hspec⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hinterval {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : ContDiffAt ℝ 1 R s ∧ HasDerivAt R (r (R s)) s ∧
      IsStrictlyHyperbolicAt flux (R s) ∧ ContDiffAt ℝ 1 r (R s) ∧
      ContDiffAt ℝ 1 a (R s) ∧ a (R s) = characteristicSpeed flux k (R s) ∧
      Module.End.HasEigenvector (fderiv ℝ flux (R s)).toLinearMap
        (characteristicSpeed flux k (R s)) (r (R s)) :=
    hball (by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs)
  refine ⟨r, R, ε, hε, hR₀, hr, ?_, ?_, ?_⟩
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun s hs ↦ (hinterval hs).2.1.differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (show ContDiffOn ℝ 1 (r ∘ R) (Ioo (-ε) ε) from
      fun s hs ↦ ((hinterval hs).2.2.2.1.comp s (hinterval hs).1).contDiffWithinAt).congr
    exact fun s hs ↦ (hinterval hs).2.1.deriv
  · apply (show ContDiffOn ℝ 1 (a ∘ R) (Ioo (-ε) ε) from
      fun s hs ↦ ((hinterval hs).2.2.2.2.1.comp s (hinterval hs).1).contDiffWithinAt).congr
    exact fun s hs ↦ (hinterval hs).2.2.2.2.2.1.symm
  · exact fun s hs ↦ ⟨(hinterval hs).2.2.1, (hinterval hs).2.1, (hinterval hs).2.2.2.2.2.2⟩

end PDE.Hyperbolic.ConservationLaw.System
