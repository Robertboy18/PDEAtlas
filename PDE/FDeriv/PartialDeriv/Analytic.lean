/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Coordinate derivatives of analytic functions

## Motivation

Is a coordinate derivative of a real-analytic function on `ℝ^n` real-analytic again?

## The idea

Yes. The Fréchet derivative of an analytic function is analytic, and `∂ᵢ f` is that derivative
followed by evaluation at the `i`-th coordinate vector, which is a continuous linear map.

## Main results

* `AnalyticAt.partialDeriv`: for all functions `f : ℝ^n → E` into a real Banach space that are
  analytic at `x`, and all `i`, the coordinate derivative `∂ᵢ f` is analytic at `x`.
* `AnalyticOnNhd.partialDeriv`: the same at every point of a set.

## Relations

`AnalyticAt.partialDeriv` is `AnalyticAt.fderiv` composed with a continuous linear map.
`ContDiffAt.partialDeriv` is the counterpart for finite regularity, which loses one order.
`AnalyticOnNhd.partialDeriv` is `AnalyticAt.partialDeriv` at every point.

## What stays open

Derivatives along directions other than the coordinate vectors are the same statement with
another vector and are not written out.
-/

@[expose] public section

open PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ^n → E}

/-- **Coordinate derivatives of analytic functions.** If `f : ℝ^n → E` is real-analytic at `x`,
then so is `∂ᵢ f`, for every `i`. The Fréchet derivative is analytic and evaluation at a
coordinate vector is linear. -/
theorem AnalyticAt.partialDeriv {x : ℝ^n} (hf : AnalyticAt ℝ f x) (i : Fin n) :
    AnalyticAt ℝ (∂[i] f) x :=
  ((ContinuousLinearMap.apply ℝ E (EuclideanSpace.single i (1 : ℝ))).analyticAt _).comp hf.fderiv

/-- If `f : ℝ^n → E` is real-analytic at every point of `s`, then so is `∂ᵢ f`, for every
`i`. This is `AnalyticAt.partialDeriv` at each point. -/
theorem AnalyticOnNhd.partialDeriv {s : Set (ℝ^n)} (hf : AnalyticOnNhd ℝ f s) (i : Fin n) :
    AnalyticOnNhd ℝ (∂[i] f) s :=
  fun x hx ↦ (hf x hx).partialDeriv i
