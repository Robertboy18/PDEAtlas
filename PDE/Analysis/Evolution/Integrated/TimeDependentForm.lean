/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Analysis.MeasureTheory.StronglyMeasurable.Evaluation
import Mathlib.Tactic.Positivity.Finset

/-!
# Time-dependent forms on Bochner spaces

Let `B : ℝ → (V →L[ℝ] V*)` be a family of bounded bilinear forms on a Hilbert space `V`,
strongly measurable on each fixed vector and essentially bounded in operator norm by `M_B`.
Then `u ↦ (t ↦ B(t) u(t))` maps `L²(a, b; V)` into `L²(a, b; V*)` with norm at most `M_B`.
We define that multiplication, first for a single trajectory (`timeDependentFormLp`) and
then as a continuous linear map (`timeDependentFormLpCLM`), and use it to define the
residual `ℓ - B(·) u ∈ L²(a, b; V*)` of a candidate solution. In the regularity file the
residual is shown to be the weak time derivative of an integrated weak solution, so the
bound proved here, `‖ℓ - B(·) u‖_{L²(V*)} ≤ ‖ℓ‖ + M_B ‖u‖`, is the a priori bound on `u'`.

The measurability assumption concerns each function `t ↦ B(t)v` separately. It does not
require measurability into the operator-norm topology. The measure space is arbitrary;
parabolic evolution uses Lebesgue measure restricted to the time interval.

## Main results

* `memLp_timeDependentFormApply`: `t ↦ B(t) u(t)` is in `L²` when `u` is.
* `timeDependentFormLp`, `timeDependentFormLp_apply_ae`, `norm_timeDependentFormLp_le`:
  the `L²(V*)` class of `B(·) u`, its a.e. representative, and the bound `M_B ‖u‖`.
* `timeDependentFormLpCLM`: the same map as an element of `L²(V) →L[ℝ] L²(V*)`. The
  continuous-linear form is what lets weak convergence of Galerkin states pass to
  the form term, since bounded linear maps are weak-to-weak continuous.
* `gelfandResidualLp`, `gelfandResidualLp_apply_ae`, `norm_gelfandResidualLp_le`: the
  residual `ℓ - B(·) u` and its norm bound.

## Implementation notes

The measurability hypothesis `hBmeas` and the bound `hBbound` are explicit arguments of
the definitions rather than fields of a structure. Since `MemLp` is a proposition, the
resulting `L²` class does not depend on which bound `M_B` or which proof is supplied:
terms built from different bounds are definitionally equal.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, (8) (the time-dependent bilinear form).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- A family of continuous linear maps, strongly measurable on each fixed vector and
essentially bounded in operator norm, sends a Bochner `L²` trajectory to a Bochner `L²`
trajectory. This is
the operator-valued multiplication lemma needed for the time-dependent
forms `B[u, v; t]` of Evans §7.1.1, equation (8). -/
theorem memLp_timeDependentFormApply
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    MemLp (fun t ↦ B t (u t)) 2 μ := by
  let μab := μ
  have hmeas : AEStronglyMeasurable (fun t ↦ B t (u t)) μab :=
    (Lp.aestronglyMeasurable u).eval_of_continuous hBmeas (fun t ↦ (B t).continuous)
  have hbound : ∀ᵐ t ∂μab, ‖B t (u t)‖ ≤ MB * ‖u t‖ := by
    filter_upwards [hBbound] with t hBt
    exact (ContinuousLinearMap.le_opNorm (B t) (u t)).trans
      (mul_le_mul_of_nonneg_right hBt (norm_nonneg _))
  exact MemLp.of_le_mul (Lp.memLp u) hmeas hbound

/-- The `L²(V*)` trajectory represented pointwise by `t ↦ B(t)(u(t))`. -/
noncomputable def timeDependentFormLp
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    Lp (StrongDual ℝ V) 2 μ :=
  (memLp_timeDependentFormApply B u hBmeas MB hBbound).toLp

omit [CompleteSpace V] in
/-- The Bochner representative of `timeDependentFormLp` agrees almost
everywhere with pointwise operator application. -/
theorem timeDependentFormLp_apply_ae
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    (timeDependentFormLp B u hBmeas MB hBbound : α → StrongDual ℝ V) =ᵐ[
      μ] fun t ↦ B t (u t) :=
  (memLp_timeDependentFormApply B u hBmeas MB hBbound).coeFn_toLp

omit [CompleteSpace V] in
/-- The operator multiplication map obeys the expected Bochner `L²` norm
bound.  This is the nonautonomous form estimate
`‖B(·)u‖_{L²(V*)} ≤ M_B ‖u‖_{L²(V)}` used in Evans §7.1.2. -/
theorem norm_timeDependentFormLp_le
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    ‖timeDependentFormLp B u hBmeas MB hBbound‖ ≤ MB * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeDependentFormLp_apply_ae B u hBmeas MB hBbound,
    hBbound] with t ht hBt
  rw [ht]
  exact (ContinuousLinearMap.le_opNorm (B t) (u t)).trans
    (mul_le_mul_of_nonneg_right hBt (norm_nonneg _))

/--
Operator-valued multiplication `u ↦ (t ↦ B(t)u(t))` as a continuous linear
map from `L²(a,b;V)` to `L²(a,b;V*)`.

The value-level construction `timeDependentFormLp` is convenient for
writing residuals.  The continuous linear map is what the Galerkin
limit argument needs: its induced map on weak spaces is continuous, so weak
convergence of the states automatically passes to the nonautonomous form
term.  The proof uses equality of Bochner representatives almost everywhere;
it does not select pointwise representatives as mathematical data.
-/
noncomputable def timeDependentFormLpCLM
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    Lp V 2 μ →L[ℝ]
      Lp (StrongDual ℝ V) 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ timeDependentFormLp B u hBmeas MB hBbound
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards
          [timeDependentFormLp_apply_ae B (u + v) hBmeas MB hBbound,
            timeDependentFormLp_apply_ae B u hBmeas MB hBbound,
            timeDependentFormLp_apply_ae B v hBmeas MB hBbound,
            Lp.coeFn_add u v,
            Lp.coeFn_add
              (timeDependentFormLp B u hBmeas MB hBbound)
              (timeDependentFormLp B v hBmeas MB hBbound)] with
            t huv hu hv huvPoint hsum
        rw [huv, huvPoint, hsum]
        change
          B t (u t + v t) =
            timeDependentFormLp B u hBmeas MB hBbound t +
              timeDependentFormLp B v hBmeas MB hBbound t
        rw [map_add, hu, hv]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards
          [timeDependentFormLp_apply_ae B (c • u) hBmeas MB hBbound,
            timeDependentFormLp_apply_ae B u hBmeas MB hBbound,
            Lp.coeFn_smul c u,
            Lp.coeFn_smul c
              (timeDependentFormLp B u hBmeas MB hBbound)] with
            t hcu hu hcuPoint hsmul
        have hsmul' :
            ((RingHom.id ℝ) c •
                timeDependentFormLp B u hBmeas MB hBbound :
              Lp (StrongDual ℝ V) 2
                μ) t =
              c • timeDependentFormLp B u hBmeas MB hBbound t := by
          simpa using hsmul
        rw [hcu, hcuPoint, hsmul']
        change B t (c • u t) =
          c • timeDependentFormLp B u hBmeas MB hBbound t
        rw [map_smul, hu] }
    MB
    (fun u ↦ norm_timeDependentFormLp_le B u hBmeas MB hBbound)

omit [CompleteSpace V] in
/-- The bundled operator multiplication agrees with `timeDependentFormLp` on each
trajectory. -/
@[simp]
theorem timeDependentFormLpCLM_apply
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB)
    (u : Lp V 2 μ) :
    timeDependentFormLpCLM B hBmeas MB hBbound u =
      timeDependentFormLp B u hBmeas MB hBbound :=
  rfl

/-- The `V*`-valued residual `ell - B(t)u` associated with an `L²` weak
evolution trajectory. -/
noncomputable def gelfandResidualLp
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (ell : Lp (StrongDual ℝ V) 2 μ)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    Lp (StrongDual ℝ V) 2 μ :=
  ell - timeDependentFormLp B u hBmeas MB hBbound

omit [CompleteSpace V] in
/-- The canonical `L²(V*)` residual has the expected pointwise formula
`ell(t) - B(t)u(t)` almost everywhere. -/
theorem gelfandResidualLp_apply_ae
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (ell : Lp (StrongDual ℝ V) 2 μ)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    (gelfandResidualLp B ell u hBmeas MB hBbound :
      α → StrongDual ℝ V) =ᵐ[μ]
        fun t ↦ ell t - B t (u t) := by
  filter_upwards [Lp.coeFn_sub ell
      (timeDependentFormLp B u hBmeas MB hBbound),
    timeDependentFormLp_apply_ae B u hBmeas MB hBbound] with t hsub hB
  change (ell - timeDependentFormLp B u hBmeas MB hBbound) t =
    ell t - B t (u t)
  rw [hsub]
  change ell t - timeDependentFormLp B u hBmeas MB hBbound t =
    ell t - B t (u t)
  rw [hB]

omit [CompleteSpace V] in
/-- Quantitative `L²(V*)` bound for the evolution residual
`ell - B(·)u`, hence for the weak time derivative of an integrated solution. -/
theorem norm_gelfandResidualLp_le
    (B : α → V →L[ℝ] StrongDual ℝ V)
    (ell : Lp (StrongDual ℝ V) 2 μ)
    (u : Lp V 2 μ)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ)
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) :
    ‖gelfandResidualLp B ell u hBmeas MB hBbound‖ ≤
      ‖ell‖ + MB * ‖u‖ := by
  exact (norm_sub_le ell (timeDependentFormLp B u hBmeas MB hBbound)).trans
    (add_le_add le_rfl
      (norm_timeDependentFormLp_le B u hBmeas MB hBbound))

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
