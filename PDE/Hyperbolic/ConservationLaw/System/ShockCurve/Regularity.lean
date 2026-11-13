/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve
public import PDE.Analysis.Calculus.ImplicitRay.Regularity
public import PDE.Analysis.Calculus.LocalSpectralFrame.Eigenline

/-!
# Higher regularity of physical shock curves

The local `C²` construction already supplies the physical curves and classifies
every nearby nonzero Rankine–Hugoniot jump. A continuous speed selects the same
normalized eigenline of the averaged Jacobian. The implicit equation then improves
the regularity of those same curves, on one neighborhood even at infinite order.

`exists_local_shock_curves_of_contDiffOn` is Evans, §11.2.3, Theorem 2(i)-(ii), at higher
regularity: for a `C^(n+1)` flux, `1 ≤ n ≤ ∞`, that is strictly hyperbolic at `u₀`, the shock
set `S(u₀)` near `u₀` is the union of `m` curves `S_k(u₀)` of class `C^n`, the `k`-th through
`u₀` with tangent `r_k(u₀)` and with a `C^n` speed `σ` equal to `λ_k(u₀)` at `u₀`. The averaged
Jacobian `B(z)` of (15) is then `C^n`, and so are its eigenvectors `r̂_k` and the solutions of
the implicit equation `u - u₀ = s • r̂_k(u)`, the form (24) of the curves in Evans's proof.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, the definition of the shock set `S(z₀)`, Theorem
  2 and its proof, equations (15) and (24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

/-- A normalized physical `C¹` shock branch inherits every available derivative
of the averaged Jacobian. Both state and speed have the stated regularity on one
open interval, including when the order is infinite. -/
theorem exists_contDiffOn_shock_curve {m : ℕ} {n : ℕ∞} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m}
    (hn : 1 ≤ n) (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ ((n : ℕ∞ω) + 1) flux U)
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ) (horder : StrictMono eig)
    (heigen : ∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) {k : Fin m} {S : ℝ → ℝ^m} {speed : ℝ → ℝ}
    (hS₀ : S 0 = u₀) (ha₀ : speed 0 = eig k) (hS : ContDiffAt ℝ 1 S 0) (ha : ContDiffAt ℝ 1 speed 0)
    (hshock : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (S s) (speed s) ∧ b.equivFun (S s - u₀) k = s) :
    ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ContDiffOn ℝ n S I ∧ ContDiffOn ℝ n speed I := by
  obtain ⟨ψ, V, hV, huV, _hVU, hbase, hψ, hframe⟩ :=
    exists_local_averaged_spectral_frame_of_basis hU hu₀ hflux b eig horder heigen
  have hSV : ∀ᶠ s in 𝓝 0, S s ∈ V := hS.continuousAt (hS₀.symm ▸ hV.mem_nhds huV)
  have heigennear : ∀ᶠ s in 𝓝 0,
      PDE.Analysis.averagedFDeriv flux u₀ (S s) (S s - u₀) = speed s • (S s - u₀) ∧
        b.equivFun (S s - u₀) k = s := by
    filter_upwards [hshock, hSV] with s hs hsV using ⟨((hframe (S s) hsV).1).trans hs.1, hs.2⟩
  have hray := PDE.Analysis.Calculus.SimpleEigenpair.eventually_eq_normalized_eigenline
    hbase horder (hV.mem_nhds huV) (fun j ↦ ((hψ j).contDiffAt (hV.mem_nhds huV)).continuousAt)
    (fun z hz ↦ (hframe z hz).2) hS.continuousAt hS₀ ha.continuousAt ha₀ heigennear
  obtain ⟨I, hIsub, hI, hI₀⟩ := _root_.mem_nhds_iff.mp
    ((hS.eventually (by simp)).and (hSV.and hray))
  have hn₀ : (n : ℕ∞ω) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hn))
  obtain ⟨J, hJ, hJ₀, hJI, hSJ⟩ :=
    PDE.Analysis.exists_contDiffOn_implicit_ray hn₀ hV (hψ k).fst hI hI₀
      (fun s hs ↦ (hIsub hs).1.continuousAt.continuousWithinAt) hS₀
      (fun s hs ↦ (hIsub hs).2.1) (fun s hs ↦ (hIsub hs).2.2.1)
  refine ⟨J, hJ, hJ₀, hSJ, ?_⟩
  refine ((hψ k).snd.comp hSJ (fun s hs ↦ (hIsub (hJI hs)).2.1)).congr fun s hs ↦ ?_
  exact (hIsub (hJI hs)).2.2.2

/-- Shrinking the parameter neighborhood preserves complete local jump
classification after shrinking the state neighborhood by its base coordinates.
This is used both for higher regularity and for uniform speed estimates. -/
theorem exists_shock_classification_on_parameter_neighborhood {m : ℕ} {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m}
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) {S : Fin m → ℝ → ℝ^m} {speed : Fin m → ℝ → ℝ} {I₀ I : Set ℝ}
    {V₀ : Set (ℝ^m)} (hI : IsOpen I) (hIzero : 0 ∈ I) (hII₀ : I ⊆ I₀) (hV₀ : IsOpen V₀)
    (huV₀ : u₀ ∈ V₀) (hcoord : ∀ k s, s ∈ I₀ → b.equivFun (S k s - u₀) k = s)
    (hclass : ∀ u ∈ V₀, ∀ a : ℝ, u ≠ u₀ →
      (RankineHugoniot flux u₀ u a ↔ ∃ k s, s ∈ I₀ ∧ s ≠ 0 ∧ u = S k s ∧ a = speed k s)) :
    ∃ V : Set (ℝ^m), IsOpen V ∧ u₀ ∈ V ∧ V ⊆ V₀ ∧
      ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ → (RankineHugoniot flux u₀ u a ↔ ∃ k s, s ∈ I ∧ s ≠ 0 ∧ u = S k s ∧
        a = speed k s) := by
  let c (k : Fin m) : ℝ^m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  have hnear (k : Fin m) : ∀ᶠ u in 𝓝 u₀, c k (u - u₀) ∈ I := by
    have hc : ContinuousAt (fun u ↦ c k (u - u₀)) u₀ :=
      (c k).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    exact hc (by simpa only [sub_self, map_zero] using hI.mem_nhds hIzero)
  obtain ⟨V, hVsub, hV, huV⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hV₀.mem_nhds huV₀) (Filter.eventually_all.mpr hnear))
  refine ⟨V, hV, huV, fun _ hu ↦ (hVsub hu).1, fun u hu a hune ↦ ?_⟩
  constructor
  · intro hRH
    obtain ⟨k, s, hs, hsne, hstate, ha⟩ := (hclass u (hVsub hu).1 a hune).mp hRH
    refine ⟨k, s, ?_, hsne, hstate, ha⟩
    have hscoord : c k (u - u₀) = s := by
      rw [hstate]
      exact hcoord k s hs
    exact hscoord ▸ (hVsub hu).2 k
  · rintro ⟨k, s, hs, hsne, hstate, ha⟩
    exact (hclass u (hVsub hu).1 a hune).mpr ⟨k, s, hII₀ hs, hsne, hstate, ha⟩

/-- Higher-regularity local shock curves, retaining the complete
classification of all nearby nonzero Rankine–Hugoniot jumps and every speed.
The common parameter neighborhood supports all derivative orders when `n = ∞`;
the state neighborhood is shrunk with it, so classification is not lost. -/
theorem exists_local_shock_curves_of_contDiffOn {m : ℕ} {n : ℕ∞} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)}
    {u₀ : ℝ^m} (hn : 1 ≤ n) (hU : IsOpen U) (hu₀ : u₀ ∈ U)
    (hflux : ContDiffOn ℝ ((n : ℕ∞ω) + 1) flux U) (hhyper : IsStrictlyHyperbolicAt flux u₀) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
    ∃ eig : Fin m → ℝ,
    ∃ S : Fin m → ℝ → ℝ^m,
    ∃ speed : Fin m → ℝ → ℝ,
    ∃ I : Set ℝ, ∃ V : Set (ℝ^m),
      StrictMono eig ∧
      (∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) ∧
      IsOpen I ∧ 0 ∈ I ∧ IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧
      (∀ k,
        S k 0 = u₀ ∧ speed k 0 = eig k ∧
        ContDiffOn ℝ n (S k) I ∧ ContDiffOn ℝ n (speed k) I ∧
        HasDerivAt (S k) (b k) 0 ∧
        ∀ s ∈ I, S k s ∈ U ∧
          RankineHugoniot flux u₀ (S k s) (speed k s) ∧
          b.equivFun (S k s - u₀) k = s) ∧
      ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
        (RankineHugoniot flux u₀ u a ↔
          ∃ k s, s ∈ I ∧ s ≠ 0 ∧ u = S k s ∧ a = speed k s) := by
  have htwo : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) + 1 := by
    simpa only [one_add_one_eq_two, add_comm] using
      add_le_add_right (show (1 : ℕ∞ω) ≤ n by exact_mod_cast hn) 1
  obtain ⟨b, eig, S, speed, I₀, V₀, horder, heigen, hI₀, hzero, hV₀, huV₀, hV₀U, hcurves, hclass⟩ :=
    exists_local_shock_curves hU hu₀ (hflux.of_le htwo) hhyper
  have hregular (k : Fin m) : ∃ J : Set ℝ, IsOpen J ∧ 0 ∈ J ∧
        ContDiffOn ℝ n (S k) J ∧ ContDiffOn ℝ n (speed k) J := by
    apply exists_contDiffOn_shock_curve hn hU hu₀ hflux b eig horder heigen
      (hcurves k).1 (hcurves k).2.1 ((hcurves k).2.2.1.contDiffAt (hI₀.mem_nhds hzero))
      ((hcurves k).2.2.2.1.contDiffAt (hI₀.mem_nhds hzero))
    filter_upwards [hI₀.mem_nhds hzero] with s hs using ((hcurves k).2.2.2.2.2 s hs).2
  choose J hJ hJ₀ hSJ haJ using hregular
  obtain ⟨I, hIsub, hI, hIzero⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hI₀.mem_nhds hzero) (Filter.eventually_all.mpr
      (fun k ↦ (hJ k).mem_nhds (hJ₀ k))))
  obtain ⟨V, hV, huV, hVV₀, hclassI⟩ :=
    exists_shock_classification_on_parameter_neighborhood b hI hIzero
      (fun s hs ↦ (hIsub hs).1) hV₀ huV₀ (fun k s hs ↦ ((hcurves k).2.2.2.2.2 s hs).2.2) hclass
  refine ⟨b, eig, S, speed, I, V, horder, heigen, hI, hIzero, hV, huV,
    fun u hu ↦ hV₀U (hVV₀ hu), ?_, hclassI⟩
  exact fun k ↦ ⟨(hcurves k).1, (hcurves k).2.1, (hSJ k).mono (fun s hs ↦ (hIsub hs).2 k),
    (haJ k).mono (fun s hs ↦ (hIsub hs).2 k), (hcurves k).2.2.2.2.1,
    fun s hs ↦ (hcurves k).2.2.2.2.2 s (hIsub hs).1⟩

end PDE.Hyperbolic.ConservationLaw.System
