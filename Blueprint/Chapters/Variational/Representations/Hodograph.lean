/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import PDE.Fluid.Compressible.Hodograph
import PDE.Elliptic.MinimalSurface.Legendre
import PDE.Examples.Elliptic.MinimalSurface.Legendre

/-!
# Hodograph and local Legendre transformations

Velocity and gradient coordinates turn two nonlinear planar equations into
linear equations for an inverse map or its potential. The inverse charts,
regularity, and minimal-surface divergence identity are part of the construction.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Hodograph and Local Legendre Transformations" =>

# Using the unknown as a coordinate

In a planar flow, the velocity $`w(x)` is a function of position. If its
Jacobian is nonsingular at $`x_*`, nearby velocities distinguish nearby
positions: we can use $`q=w(x)` as the independent variable and write
$`x=X(q)`. A coefficient that originally depended on the unknown velocity,
such as $`\sigma(w(x))^2-w^0(x)^2`, becomes the known function
$`\sigma(q)^2-q_0^2`. The derivatives change too, and their inverse-matrix
formula is what makes the transformed equations linear.

For a scalar graph, the useful new coordinate is its slope
$`p=\nabla u(x)`. The inverse slope map is itself a gradient, obtained from
$`v(p)=p\cdot X(p)-u(X(p))`. This cancellation carries through to the
minimal-surface equation, and it applies to a graph whose Hessian has one
positive and one negative eigenvalue.

Coordinates are numbered $`0,1`, as in the Lean statements.

## The signed inverse Jacobian

Write $`J_{ij}(x)=\partial_{x_j}w^i(x)`, with the velocity component
selecting the row and the spatial derivative selecting the column. On an
inverse chart, differentiating $`w(X(q))=q` gives

$$`
J(X(q))\,DX(q)=I.
`

For $`J=\begin{pmatrix}A&B\\C&D\end{pmatrix}` and
$`\Delta=AD-BC`, this says

$$`
DX=\frac1\Delta
\begin{pmatrix}D&-B\\-C&A\end{pmatrix}.
`

Here $`J` and $`\Delta` are evaluated at $`X(q)`. The determinant keeps
its sign. For example, the off-diagonal difference in the inverse matrix
is $`(-B+C)/\Delta`, so

$$`
J_{01}-J_{10}
=-\Delta\bigl(\partial_{q_1}X^0-\partial_{q_0}X^1\bigr).
`

Both orientations therefore preserve the zero-curl equation. Taking an
absolute value of the determinant would lose this identity.

:::theorem "analysis.inverse_function.local_chart" (parent := "methods.representations") (lean := "PDE.Analysis.exists_regular_contDiffOn_inverse_chart")
Let $`\Omega\subseteq\mathbb R^n` be open, $`x_*\in\Omega`, and
$`w:\mathbb R^n\to\mathbb R^n` be $`C^1` on $`\Omega`. If
$`\det Dw(x_*)\ne0`, there are open sets $`U\subseteq\Omega` and $`V`,
with $`x_*\in U` and $`w(x_*)\in V`, such that $`w:U\to V` is a
homeomorphism with a $`C^1` inverse $`X:V\to U`. Moreover,

$$`
\det Dw(x)\ne0\qquad(x\in U).
`

Nonsingularity is assumed at one point; the chart and its regularity on the
whole target are conclusions.
:::

:::proof "analysis.inverse_function.local_chart"
Apply the inverse-function theorem at $`x_*`. Restrict the source to
$`\Omega` and the target to an open neighborhood on which the inverse is
$`C^1`. Differentiating the inverse identities there makes the two
Jacobians inverse matrices, so their determinants multiply to one. This
also proves nonsingularity throughout the restricted source.
:::

## A potential for the inverse velocity

Let $`\sigma:\mathbb R^2\to\mathbb R` be a prescribed function of velocity.
The compressible-flow system used here is

$$`
\begin{aligned}
&(\sigma(w)^2-(w^0)^2)J_{00}
-w^0w^1(J_{01}+J_{10})
+(\sigma(w)^2-(w^1)^2)J_{11}=0,\\
&J_{01}-J_{10}=0.
\end{aligned}
`

Substituting the inverse matrix into the first equation and dividing by
the nonzero signed determinant gives

$$`
(\sigma(q)^2-q_0^2)\partial_{q_1}X^1
+q_0q_1(\partial_{q_1}X^0+\partial_{q_0}X^1)
+(\sigma(q)^2-q_1^2)\partial_{q_0}X^0=0.
`

This equation is linear in $`DX`. The transformed curl equation says that
$`DX` is symmetric. On a ball inside the target, that symmetry supplies a
potential $`z` with $`\nabla z=X`. The ball matters: local inversion
alone does not give a global potential on an arbitrary target domain.

:::theorem "fluid.hodograph.potential" (parent := "methods.representations") (lean := "PDE.Fluid.Hodograph.exists_hodograph_potential") (uses := "analysis.inverse_function.local_chart")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.4.3(a) (Hodograph transformation)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`\Omega\subseteq\mathbb R^2` is open, $`x_*\in\Omega`,
$`w\in C^1(\Omega;\mathbb R^2)`, and $`\det Dw(x_*)\ne0`.
Let $`\sigma:\mathbb R^2\to\mathbb R` be arbitrary, and suppose $`w`
satisfies both displayed compressible-flow equations throughout $`\Omega`.
There are a local inverse chart $`X:V\to U`, with
$`x_*\in U\subseteq\Omega`, and $`r>0` such that
$`B(w(x_*),r)\subseteq V`. On this ball there is a $`C^2` function $`z`
with $`\nabla z=X` and

$$`
(\sigma(q)^2-q_0^2)z_{11}
+2q_0q_1z_{01}
+(\sigma(q)^2-q_1^2)z_{00}=0.
`

Here $`z_{ij}=\partial_{q_i}\partial_{q_j}z`.
:::

:::proof "fluid.hodograph.potential"
Construct the regular inverse chart. The cofactor identities give the
linear mass equation and preserve zero curl, with the signed determinant.
Choose a positive-radius ball around $`w(x_*)` inside the open target.
The $`C^1` inverse field has symmetric derivative on this convex ball,
so the potential theorem constructs $`z\in C^2` with $`\nabla z=X`.
Substitution and symmetry of the second derivatives give the scalar equation.
:::

## Inverting the slope of a graph

Now let $`u:\mathbb R^n\to\mathbb R` be $`C^2` and suppose its Hessian
is nonsingular at $`x_*`. Its gradient is $`C^1`, so the same inverse
construction applies to $`p=\nabla u(x)`. For its local inverse $`X`,
define

$$`
v(p)=p\cdot X(p)-u(X(p)).
`

The derivative of $`X` appears twice when we differentiate this expression.
Since $`\nabla u(X(p))=p`, the two terms cancel:

$$`
\begin{aligned}
Dv(p)[h]
&=h\cdot X(p)+p\cdot DX(p)[h]
  -\nabla u(X(p))\cdot DX(p)[h]\\
&=X(p)\cdot h.
\end{aligned}
`

Thus $`\nabla v=X`. We have only differentiated $`X` once, and its
$`C^1` regularity now makes the gradient of $`v` $`C^1`. This is why
$`C^2` regularity of $`u` suffices for a $`C^2` dual.

:::theorem "analysis.legendre.local_dual" (parent := "methods.representations") (lean := "PDE.Analysis.exists_localLegendre_inverse_hessian") (uses := "analysis.inverse_function.local_chart")
Let $`\Omega\subseteq\mathbb R^n` be open, $`x_*\in\Omega`, and
$`u\in C^2(\Omega)`. Assume $`\det D^2u(x_*)\ne0`.
There is an open inverse chart
$`\nabla u:U\to V`, with $`x_*\in U\subseteq\Omega` and inverse
$`X\in C^1(V)`, for which the explicit function
$`v(p)=p\cdot X(p)-u(X(p))` is $`C^2` on $`V` and

$$`
\nabla v(p)=X(p),\qquad
D^2v(p)=\bigl(D^2u(X(p))\bigr)^{-1}
\quad(p\in V).
`

These are the actual derivatives of $`u` and $`v`.
:::

:::proof "analysis.legendre.local_dual"
Apply the local inverse theorem to the $`C^1` gradient of $`u`. Since
$`\nabla u(X(p))=p`, the two $`DX` terms cancel and the gradient of the
explicit dual is $`X`,
which gives $`C^2` regularity. Differentiating this gradient identity and
the local inverse identity gives $`D^2v=DX=(D^2u)^{-1}`.
:::

This construction uses one inverse branch of the gradient. It does not
take a supremum over all $`x`, as a global convex conjugate would.
An indefinite Hessian is therefore allowed.

In the plane, the inverse-Hessian formula reads

$$`
\Delta\,D^2v(p)=
\begin{pmatrix}u_{11}&-u_{01}\\-u_{01}&u_{00}\end{pmatrix}(X(p)),
\qquad \Delta=\det D^2u(X(p)).
`

The diagonal entries exchange places and the mixed entry changes sign.
This determines the transformed equation.

:::theorem "analysis.legendre.linearization" (parent := "methods.representations") (lean := "PDE.Analysis.exists_localLegendre_linearized") (uses := "analysis.legendre.local_dual")
Let $`\Omega\subseteq\mathbb R^2` be open, $`x_*\in\Omega`,
$`u\in C^2(\Omega)`, and $`\det D^2u(x_*)\ne0`. Let
$`a,b,c:\mathbb R^2\to\mathbb R` be arbitrary functions. If

$$`
a(\nabla u)u_{00}+2b(\nabla u)u_{01}+c(\nabla u)u_{11}=0
\qquad\text{on }\Omega,
`

the construction gives a local inverse chart and its explicit $`C^2`
dual $`v`, satisfying

$$`
c(p)v_{00}-2b(p)v_{01}+a(p)v_{11}=0
\qquad(p\in V).
`

The coefficients depend only on the new independent variable $`p`.
:::

:::proof "analysis.legendre.linearization"
Multiply the transformed expression by the signed determinant $`\Delta`.
The inverse-Hessian entries turn it into the original expression at $`X(p)`,
and $`\nabla u(X(p))=p` identifies the coefficients. The original
equation makes this product zero. Nonsingularity on the chart lets us
cancel $`\Delta`.
:::

## From the minimal-graph divergence to a linear equation

For a planar graph $`u`, set $`s=\sqrt{1+|\nabla u|^2}`. Its classical
minimal-surface equation is

$$`
\operatorname{div}\left(\frac{\nabla u}{s}\right)=0.
`

The factor $`1` keeps $`s` positive, including at a critical point of $`u`.
For $`u\in C^2`, differentiation gives

$$`
\partial_i s=\frac{u_0u_{i0}+u_1u_{i1}}{s},\qquad
\operatorname{div}\left(\frac{\nabla u}{s}\right)
=\frac{u_{00}+u_{11}}s
-\frac{u_0^2u_{00}+2u_0u_1u_{01}+u_1^2u_{11}}{s^3}.
`

Putting the first term over $`s^3` leaves the two diagonal coefficients
from the other coordinate.

:::theorem "elliptic.minimal_surface.divergence" (parent := "methods.representations") (lean := "PDE.Elliptic.MinimalSurface.contDiffAt_normalizedGradient, PDE.Elliptic.MinimalSurface.divergence_normalizedGradient_eq, PDE.Elliptic.MinimalSurface.divergence_normalizedGradient_eq_zero_iff")
If $`u:\mathbb R^2\to\mathbb R` is $`C^2` at $`x`, its normalized
gradient is $`C^1` there and

$$`
\operatorname{div}\left(\frac{\nabla u}{\sqrt{1+|\nabla u|^2}}\right)(x)
=\frac{(1+u_1^2)u_{00}-2u_0u_1u_{01}+(1+u_0^2)u_{11}}
       {\bigl(\sqrt{1+|\nabla u|^2}\bigr)^3}(x).
`

The divergence vanishes exactly when the numerator vanishes. The $`C^1`
regularity assertion also holds in every finite dimension.
:::

:::proof "elliptic.minimal_surface.divergence"
The gradient is $`C^1`, and the squared norm, positive square root, and
reciprocal preserve the required regularity. Apply the quotient rule to
each component. Symmetry of the actual second derivatives combines the
two mixed terms; $`s^2=1+u_0^2+u_1^2` gives the displayed numerator.
Since $`s^3>0`, division preserves the zero equation.
:::

We can now read off
$`a(p)=1+p_1^2`, $`b(p)=-p_0p_1`, and $`c(p)=1+p_0^2`.
The sign change in the mixed coefficient makes the dual mixed term positive.

:::theorem "elliptic.minimal_surface.legendre" (parent := "methods.representations") (lean := "PDE.Elliptic.MinimalSurface.exists_localLegendre_solution_of_divergence_eq_zero") (uses := "analysis.legendre.linearization, elliptic.minimal_surface.divergence, elliptic.minimal_surface.dual_principal_form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.4.3(b), equations (24)–(30), Legendre transform and the minimal-surface equation"
    page := "210"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^2` be open, $`x_*\in\Omega`, and
$`u\in C^2(\Omega)`. Suppose

$$`
\operatorname{div}\left(\frac{\nabla u}{\sqrt{1+|\nabla u|^2}}\right)=0
\quad\text{on }\Omega,\qquad
\det D^2u(x_*)\ne0.
`

There is a local inverse chart $`\nabla u:U\to V` through $`x_*`, with
$`U\subseteq\Omega` and a $`C^1` inverse $`X`. Its explicit local dual
$`v(p)=p\cdot X(p)-u(X(p))` is $`C^2` on $`V`, has gradient $`X`, and
satisfies the linear equation

$$`
(1+p_0^2)v_{00}+2p_0p_1v_{01}+(1+p_1^2)v_{11}=0
\qquad(p\in V).
`

Its principal quadratic form is at least $`|\xi|^2` in every direction
$`\xi\in\mathbb R^2`.
:::

:::proof "elliptic.minimal_surface.legendre"
The divergence identity gives the nondivergence equation throughout
$`\Omega`. Apply local Legendre linearization with the coefficients
$`a=1+p_1^2`, $`b=-p_0p_1`, $`c=1+p_0^2`. It constructs the chart and the
dual; exchanging the diagonal coefficients and negating the mixed one gives
the displayed equation. The lower bound for the dual principal form gives
the last assertion.
:::

The principal matrix is $`I+pp^{\mathsf T}`. Its quadratic form exposes
the ellipticity directly.

:::theorem "elliptic.minimal_surface.dual_principal_form" (parent := "methods.representations") (lean := "PDE.Elliptic.MinimalSurface.dual_principalForm_lower_bound")
For every $`p,\xi\in\mathbb R^2`,

$$`
|\xi|^2\le
(1+p_0^2)\xi_0^2+2p_0p_1\xi_0\xi_1+(1+p_1^2)\xi_1^2.
`

The lower bound is global in $`p`; the coefficients themselves need not
have a global upper bound.
:::

:::proof "elliptic.minimal_surface.dual_principal_form"
The right side is $`|\xi|^2+(p\cdot\xi)^2`. Subtract $`|\xi|^2` and
use nonnegativity of the remaining square.
:::

## A Scherk graph with an indefinite Hessian

Consider

$$`
u(x_0,x_1)=\log(\cos x_1)-\log(\cos x_0)
\qquad\left(|x_0|,|x_1|<\frac\pi2\right).
`

Both cosines are positive on this square. The derivatives are

$$`
u_0=\tan x_0,\qquad u_1=-\tan x_1,\qquad
D^2u=
\begin{pmatrix}
\sec^2x_0&0\\0&-\sec^2x_1
\end{pmatrix}.
`

Substitution into the nonlinear numerator gives

$$`
(1+\tan^2x_1)\sec^2x_0
-(1+\tan^2x_0)\sec^2x_1=0,
`

using $`1+\tan^2t=\sec^2t`. The divergence identity therefore proves
the minimal-surface equation. At the origin,

$$`
\nabla u(0)=0,\qquad
D^2u(0)=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad\det D^2u(0)=-1.
`

The gradient vanishes there, but its derivative is invertible. The local
dual theorem applies at exactly this point and produces a $`C^2` solution
of the linear equation near $`p=0`.

The checked example in
`PDE/Examples/Elliptic/MinimalSurface/Legendre.lean` uses the larger open
set where both cosines are nonzero. On that set Mathlib's real logarithm
expresses $`\log|\cos x_1|-\log|\cos x_0|`. The example proves its
regularity, first and second derivatives, zero nonlinear residual, zero
divergence, and the nonsingular Hessian before invoking the dual construction.
