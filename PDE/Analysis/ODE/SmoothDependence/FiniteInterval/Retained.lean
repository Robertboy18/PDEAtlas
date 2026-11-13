/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.AnchoredEvent
public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.Identification

/-!
# Extending retained flows to a common time interval

A complete reference trajectory supplies actual nearby flows on a larger compact
interval. ODE uniqueness identifies them with the supplied flows on their entire
old intervals, using the same initial speed sections at the original anchors.
Only the speed neighborhood shrinks.

The outgoing interval `[0, H]` and incoming interval `[2e - H, 2e]` need not contain
the same gate. Their compact hull contains every gate in `(0, e)`. The extension
keeps the original event maps: equality on the native intervals preserves their
moving states and hence the mismatch germ and its speed derivatives.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E]

/-- Agreement on the entire time domains preserves a moving mismatch near zero
speed. The events are supplied functions and stay in their respective old domains;
no new event is selected and no regularity of the event maps is needed here. -/
theorem moving_event_mismatch_eventuallyEq_of_eqOn
    {F G F' G' : ℝ → ℝ → E} {τ υ : ℝ → ℝ} {s t I : Set ℝ}
    (hI : I ∈ 𝓝 (0 : ℝ))
    (hF : ∀ μ ∈ I, EqOn (fun u ↦ F' u μ) (fun u ↦ F u μ) s)
    (hG : ∀ μ ∈ I, EqOn (fun u ↦ G' u μ) (fun u ↦ G u μ) t)
    (hτ : ∀ μ ∈ I, τ μ ∈ s) (hυ : ∀ μ ∈ I, υ μ ∈ t) :
    (fun μ ↦ F' (τ μ) μ - G' (υ μ) μ) =ᶠ[𝓝 (0 : ℝ)]
      (fun μ ↦ F (τ μ) μ - G (υ μ) μ) := by
  filter_upwards [hI] with μ hμ
  exact congrArg₂ (fun x y : E ↦ x - y)
    (hF μ hμ (hτ μ hμ)) (hG μ hμ (hυ μ hμ))

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Extend an actual speed family to a larger closed time interval about the same
complete reference. The new global smooth representative agrees with the old
family at every old time on one open speed neighborhood. Its initial section at
`c` agrees for every speed, including speeds outside that neighborhood.

The linear section is used by the existing anchored constructor. Its new event
map is discarded. The reference event only needs to lie inside the larger
interval; the old anchor may be either endpoint of the old interval. -/
theorem exists_retained_flux_flow_extension
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {loOld hiOld lo hi c e : ℝ}
    (hinterval : Icc loOld hiOld ⊆ Icc lo hi)
    (hc : c ∈ Icc loOld hiOld) (he : e ∈ Ioo lo hi)
    (F : ℝ → ℝ → E) (hF : ContDiff ℝ ∞ F.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFinit0 : F c 0 = q c)
    (hFode : ∀ μ ∈ I₀, ∀ t ∈ Icc loOld hiOld,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (ell : E →L[ℝ] ℝ) (htransverse : ell (f (q e)) ≠ 0) :
    ∃ (G : ℝ → ℝ → E) (I : Set ℝ),
      ContDiff ℝ ∞ G.uncurry ∧ IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
      (∀ μ, G c μ = F c μ) ∧
      EqOn (fun t ↦ G t 0) q (Icc lo hi) ∧
      (∀ μ ∈ I, ∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t) ∧
      (∀ μ ∈ I, EqOn (fun t ↦ G t μ) (fun t ↦ F t μ) (Icc loOld hiOld)) ∧
      ∀ t ∈ Icc loOld hiOld, G t =ᶠ[𝓝 (0 : ℝ)] F t := by
  obtain ⟨Φ, _, J, hΦ, hJ, h0J, hinit, hbase, hode, _, _, _, _⟩ :=
    exists_anchored_flux_flow_event f hf q hq (F c) (hF.comp (contDiff_const.prodMk contDiff_id))
      (hinterval hc) he hFinit0 ell htransverse
  let G : ℝ → ℝ → E := fun t μ ↦ Φ (t, μ)
  have hI : IsOpen (I₀ ∩ J) := hI₀.inter hJ
  have h0I : (0 : ℝ) ∈ I₀ ∩ J := ⟨h0I₀, h0J⟩
  -- Restrict the new ODE to the old interval. The old ODE is never extended
  -- by smoothness; endpoint uniqueness supplies equality on the whole interval.
  obtain ⟨hagree, _⟩ := eqOn_speed_families_of_common_initial_data (F := F) (G := G) (f := f)
    (lo := loOld) (hi := hiOld) (c := c) (I := I₀ ∩ J) hc (hf.of_le (by simp)) (hI.mem_nhds h0I)
    (fun μ hμ t ht ↦ hFode μ hμ.1 t ht) (fun μ hμ t ht ↦ hode μ hμ.2 t (hinterval ht))
    (fun μ _ ↦ hinit μ)
  exact ⟨G, I₀ ∩ J, hΦ, hI, h0I, inter_subset_left, hinit, hbase, fun μ hμ ↦ hode μ hμ.2, hagree,
    fun t ht ↦ eventually_of_mem (hI.mem_nhds h0I) fun μ hμ ↦ hagree μ hμ ht⟩

/-- Put actual outgoing and incoming branches on the compact hull of their native
intervals while retaining their original events and full initial sections.

The field `f` is already fixed; in the selected application it is the corrected
field. The two supplied families must solve this same field on `[0, H]` and
`[2e - H, 2e]`. No relation between `2e` and `H` is required.

The output includes equality of each old time-slice germ and of the moving
mismatch germ, together with its value and first two derivatives at speed zero.
Any smoothness or section equation of a supplied event restricts to the returned
speed neighborhood; the output event-state equalities transfer those equations. -/
theorem exists_common_interval_retained_flux_flows
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {H e tStar : ℝ} (he : e ∈ Ioo (0 : ℝ) H) (htStar : tStar ∈ Ioo (0 : ℝ) e)
    (Fout Fincoming : ℝ → ℝ → E)
    (hFout : ContDiff ℝ ∞ Fout.uncurry) (hFin : ContDiff ℝ ∞ Fincoming.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFoutBase : EqOn (fun t ↦ Fout t 0) q (Icc (0 : ℝ) H))
    (hFinBase : EqOn (fun t ↦ Fincoming t 0) q (Icc (e + e - H) (e + e)))
    (hFoutOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t)
    (hFinOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (e + e - H) (e + e),
      HasDerivAt (fun s ↦ Fincoming s μ)
        (f (Fincoming t μ) - μ • Fincoming t μ) t)
    (τout τin : ℝ → ℝ)
    (hτoutNative : ∀ μ ∈ I₀, τout μ ∈ Ioo (0 : ℝ) H)
    (hτinNative : ∀ μ ∈ I₀, τin μ ∈ Ioo (e + e - H) (e + e))
    (ell : E →L[ℝ] ℝ) (htransverse : ell (f (q e)) ≠ 0) :
    let lo := min 0 (e + e - H)
    let hi := max H (e + e)
    let Mold : ℝ → E := fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ
    e ∈ Ioo lo hi ∧ tStar ∈ Ioo lo hi ∧
      ∃ (Gout Gin : ℝ → ℝ → E) (I : Set ℝ),
        let M : ℝ → E := fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ
        ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
        IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
        (∀ μ, Gout 0 μ = Fout 0 μ ∧ Gin (e + e) μ = Fincoming (e + e) μ) ∧
        EqOn (fun t ↦ Gout t 0) q (Icc lo hi) ∧
        EqOn (fun t ↦ Gin t 0) q (Icc lo hi) ∧
        (∀ μ ∈ I,
          (∀ t ∈ Icc lo hi,
            HasDerivAt (fun s ↦ Gout s μ) (f (Gout t μ) - μ • Gout t μ) t) ∧
          (∀ t ∈ Icc lo hi,
            HasDerivAt (fun s ↦ Gin s μ) (f (Gin t μ) - μ • Gin t μ) t)) ∧
        (∀ μ ∈ I,
          EqOn (fun t ↦ Gout t μ) (fun t ↦ Fout t μ) (Icc (0 : ℝ) H) ∧
          EqOn (fun t ↦ Gin t μ) (fun t ↦ Fincoming t μ)
            (Icc (e + e - H) (e + e))) ∧
        (∀ t ∈ Icc (0 : ℝ) H, Gout t =ᶠ[𝓝 (0 : ℝ)] Fout t) ∧
        (∀ t ∈ Icc (e + e - H) (e + e), Gin t =ᶠ[𝓝 (0 : ℝ)] Fincoming t) ∧
        (∀ μ ∈ I,
          (τout μ ∈ Ioo lo hi ∧ Gout (τout μ) μ = Fout (τout μ) μ) ∧
          (τin μ ∈ Ioo lo hi ∧ Gin (τin μ) μ = Fincoming (τin μ) μ)) ∧
        M =ᶠ[𝓝 (0 : ℝ)] Mold ∧ M 0 = Mold 0 ∧
        deriv M 0 = deriv Mold 0 ∧ deriv (deriv M) 0 = deriv (deriv Mold) 0 := by
  intro lo hi Mold
  have hH : 0 < H := he.1.trans he.2
  have hAnchorOut : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  have hAnchorIn : e + e ∈ Icc (e + e - H) (e + e) := ⟨sub_le_self _ hH.le, le_rfl⟩
  have hloOut : lo ≤ 0 := min_le_left _ _
  have hloIn : lo ≤ e + e - H := min_le_right _ _
  have hhiOut : H ≤ hi := le_max_left _ _
  have hhiIn : e + e ≤ hi := le_max_right _ _
  have heBig : e ∈ Ioo lo hi := ⟨hloOut.trans_lt he.1, he.2.trans_le hhiOut⟩
  have htStarBig : tStar ∈ Ioo lo hi :=
    ⟨hloOut.trans_lt htStar.1, (htStar.2.trans he.2).trans_le hhiOut⟩
  -- Each constructor keeps its original anchor and section. Their new event
  -- choices are already discarded by the single-branch extension owner.
  obtain ⟨Gout, Iout, hGout, hIout, h0Iout, hIoutOld, hinitOut, hbaseOut,
      hodeOut, hagreeOut, hgermOut⟩ :=
    exists_retained_flux_flow_extension f hf q hq (Icc_subset_Icc hloOut hhiOut) hAnchorOut heBig
      Fout hFout I₀ hI₀ h0I₀ (hFoutBase hAnchorOut) hFoutOde ell htransverse
  obtain ⟨Gin, Iin, hGin, hIin, h0Iin, _, hinitIn, hbaseIn,
      hodeIn, hagreeIn, hgermIn⟩ :=
    exists_retained_flux_flow_extension f hf q hq (Icc_subset_Icc hloIn hhiIn) hAnchorIn heBig
      Fincoming hFin I₀ hI₀ h0I₀ (hFinBase hAnchorIn) hFinOde ell htransverse
  have hI : IsOpen (Iout ∩ Iin) := hIout.inter hIin
  have h0I : (0 : ℝ) ∈ Iout ∩ Iin := ⟨h0Iout, h0Iin⟩
  have hIold : Iout ∩ Iin ⊆ I₀ := fun _ hμ ↦ hIoutOld hμ.1
  have hmoving : (fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ) =ᶠ[𝓝 (0 : ℝ)] Mold :=
    moving_event_mismatch_eventuallyEq_of_eqOn (F := Fout) (G := Fincoming) (hI.mem_nhds h0I)
      (fun μ hμ ↦ hagreeOut μ hμ.1) (fun μ hμ ↦ hagreeIn μ hμ.2)
      (fun μ hμ ↦ Ioo_subset_Icc_self (hτoutNative μ (hIold hμ)))
      (fun μ hμ ↦ Ioo_subset_Icc_self (hτinNative μ (hIold hμ)))
  refine ⟨heBig, htStarBig, Gout, Gin, Iout ∩ Iin, hGout, hGin, hI, h0I, hIold,
    fun μ ↦ ⟨hinitOut μ, hinitIn μ⟩, hbaseOut, hbaseIn,
    fun μ hμ ↦ ⟨hodeOut μ hμ.1, hodeIn μ hμ.2⟩, fun μ hμ ↦ ⟨hagreeOut μ hμ.1, hagreeIn μ hμ.2⟩,
    hgermOut, hgermIn, fun μ hμ ↦ ?_, hmoving, hmoving.self_of_nhds, hmoving.deriv_eq,
    hmoving.deriv.deriv_eq⟩
  have hout := hτoutNative μ (hIold hμ)
  have hin := hτinNative μ (hIold hμ)
  exact ⟨⟨⟨hloOut.trans_lt hout.1, hout.2.trans_le hhiOut⟩,
    hagreeOut μ hμ.1 (Ioo_subset_Icc_self hout)⟩, ⟨⟨hloIn.trans_lt hin.1, hin.2.trans_le hhiIn⟩,
    hagreeIn μ hμ.2 (Ioo_subset_Icc_self hin)⟩⟩

end PDE.Analysis.ODE
