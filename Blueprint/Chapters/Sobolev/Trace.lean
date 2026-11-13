/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Extension
import Blueprint.Commands.Figures
import PDE.Analysis.Operator.KernelQuotient
import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasIndependence
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage.Smooth
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage.Trace
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.AtlasIndependence
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Naturality
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Operator
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Scalar
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.HeightAverage
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Naturality
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Scalar
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.AtlasIndependence
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Range
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Identification
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Lifting
import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentTraceSpace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.ZeroTrace
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.ZeroTrace
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1Converse
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.HalfSpaceConverse
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentTraceSpace
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.TraceSpace
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.HigherOrder

/-!
# Sobolev traces

Trace operators and their analytic properties on regular domains.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Trace" =>

Boundary values of a Sobolev function cannot be defined by evaluating an
arbitrary `Lp` representative. A trace theorem instead constructs a bounded
operator by proving an estimate where classical evaluation makes sense and
then extending that map to the completed Sobolev space.

For example, take the constant function $`u=1` on $`(0,1)`. Assigning
the value zero or seven at the endpoints changes neither its interior
$`L^2` class nor its weak derivative. Its trace is nevertheless $`1` at
both endpoints, as agreement with the smooth constant function requires.
The trace recovers boundary values from controlled interior approximation;
arbitrary values assigned on the boundary cannot change it.

The construction follows the geometry. Endpoint evaluation on the positive
half-line supplies the one-dimensional estimate. Integrating the same
estimate over tangential variables gives the flat half-space trace. Boundary
charts, a partition of unity, and the atlas's flattening operators then
assemble a trace on an operational $`C^1` domain; the global extension
operator is not used. The kernel of the trace is $`W^{1,p}_0`, the closure of
the test functions, which is why membership in $`H^1_0` is the formal
replacement for “vanishes on the boundary” in weak Dirichlet problems.

:::group "sobolev.trace"
Sobolev traces
:::

# Endpoint and Flat Traces

The estimate has a short one-dimensional derivation. For a smooth function
$`g` compactly supported on the closed positive half-line,

$$`
|g(0)|^2
 =-2\int_0^\infty g(t)g'(t)\,dt
 \leq2\|g\|_2\|g'\|_2
 \leq\|g\|_2^2+\|g'\|_2^2.
`

Apply this inequality to the difference of two smooth approximations:
convergence in $`H^1` forces their endpoint values to converge too.
The same estimate shows that the limit does not depend on the approximating
sequence. This is how an estimate becomes a well-defined boundary operator
on a space whose elements initially have no endpoint values.

:::definition "sobolev.half_line_endpoint_trace" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfLine.endpointTrace") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On the positive half-line, completion of endpoint evaluation on globally
smooth compactly supported functions gives a continuous linear map

$$`
\operatorname{Tr}_0:H^1(0,\infty)\longrightarrow\mathbb R.
`

This one-dimensional model is the normal-slice ingredient in the flat
half-space trace theorem.
:::

An operator defined by completion is pinned down by its values on the dense
core and by the estimate that permitted the extension. Both facts pass to the
completed map without loss: the unit constant on the core is the unit constant
of the operator.

:::theorem "sobolev.half_line_endpoint_trace_bound" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfLine.endpointTrace_smooth, SobolevSpace.Trace.HalfLine.norm_endpointTrace_le") (uses := "sobolev.half_line_endpoint_trace")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The completed half-line trace agrees with literal evaluation at zero on its
smooth core and satisfies the unit operator estimate

$$`|\operatorname{Tr}_0u|\leq\lVert u\rVert_{H^1(0,\infty)}.`
:::

:::proof "sobolev.half_line_endpoint_trace_bound"
Endpoint evaluation is first bounded by the $`H^1` norm on restrictions of
global smooth compactly supported functions. Those restrictions have dense
range in the half-line Sobolev space, so the bounded linear map extends
uniquely by continuity. The extension theorem gives both agreement with
literal evaluation on the dense core and the same norm-one estimate on the
completion.
:::

Continuity alone gives $`H^1_0(0,\infty)\subseteq\ker(\operatorname{Tr}_0)`,
since test functions vanish at the endpoint. Equality asks for the converse,
and on the half-line it can be proved directly because a function with zero
endpoint value can be cut off near the endpoint at controlled $`H^1` cost.

:::theorem "sobolev.half_line_zero_trace_kernel" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfLine.endpointTrace_eq_zero_iff_mem_H10") (uses := "sobolev.half_line_endpoint_trace_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "273-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the positive half-line, the completed endpoint trace has exactly the
closure-defined zero-trace Sobolev space as its kernel:

$$`
H^1_0(0,\infty)=\ker(\operatorname{Tr}_0).
`

The half-space and $`C^1` versions are proved at the end of the chapter
by a different argument.
:::

:::proof "sobolev.half_line_zero_trace_kernel"
Every compactly supported smooth function on the open half-line vanishes at
the endpoint, so continuity of $`\operatorname{Tr}_0` shows that
$`H^1_0(0,\infty)` lies in its kernel. Conversely, if an $`H^1` function has
zero endpoint trace, approximate it in $`H^1` by restrictions of globally
smooth, compactly supported functions. Subtract each approximant's endpoint
value times a fixed smooth bump with value one at zero. Trace continuity
makes these corrections tend to zero in $`H^1`. Each corrected function
vanishes at zero but need not vanish near it. Multiply it by cutoffs that
vanish on successively smaller neighborhoods of zero; its linear growth
near the endpoint controls the cutoff derivative and gives convergence in
$`H^1`. Thus each corrected function belongs to $`H^1_0`, and closedness gives
the same conclusion for the original function.
:::

Adding tangential variables changes the target from $`\mathbb R`
to $`L^2(\mathbb R^n)` but not the mechanism. For a smooth function on the
half-space, each normal slice $`t\mapsto f(y,t)` is a half-line function, and
the endpoint estimate integrated over $`y` is the estimate needed for the
completion.

:::definition "sobolev.flat_trace" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.trace") (uses := "sobolev.graph_space, sobolev.half_line_endpoint_trace_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Writing a point of $`\mathbb R^{n+1}` as tangential and normal coordinates
$`(y,t)\in\mathbb R^n\times\mathbb R`, the library first constructs the flat
trace

$$`
\operatorname{Tr}_{+}:H^1(\mathbb R^{n+1}_{+})\longrightarrow L^2(\mathbb R^n).
`

It is obtained by extending literal evaluation $`f(y,0)` from the dense class
of restrictions of globally smooth compactly supported functions. The
coordinate split is proved volume preserving, so the one-dimensional endpoint
estimate integrates to the correct upper-half-space energy estimate.
:::

The same two facts that characterized the half-line operator are recorded for
the flat trace. Agreement on the core now takes place in $`L^2(\mathbb R^n)`,
so it identifies the trace of a smooth function with the class of its literal
boundary restriction rather than with a number.

:::theorem "sobolev.flat_trace_smooth" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.trace_smooth") (uses := "sobolev.flat_trace")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every globally smooth compactly supported function, the completed flat
trace agrees exactly in $`L^2(\mathbb R^n)` with the classical boundary value
$`y\mapsto f(y,0)`. Thus the completion is tied to the intended pointwise
operator on its dense core.
:::

:::proof "sobolev.flat_trace_smooth"
On the smooth core, boundary restriction is the $`L^2` class of
$`y\mapsto f(y,0)`. The slice estimate bounds this linear map by the
half-space $`H^1` norm. Since smooth restrictions are dense, its continuous
extension agrees with the original map on that core. This gives the stated
identity for the completed trace.
:::

:::theorem "sobolev.flat_trace_bound" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.norm_trace_le") (uses := "sobolev.flat_trace, sobolev.flat_trace_smooth")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The model trace satisfies the quantitative estimate

$$`
\lVert\operatorname{Tr}_{+}u\rVert_{L^2(\mathbb R^n)}
  \leq \lVert u\rVert_{H^1(\mathbb R^{n+1}_{+})}.
`
:::

:::proof "sobolev.flat_trace_bound"
On the smooth dense core, apply
$`|g(0)|^2\leq2\|g\|_{L^2(0,\infty)}\|g'\|_{L^2(0,\infty)}` to each normal
slice $`g(t)=u(y,t)`. Integrate over $`y`, use Fubini, and then apply
$`2ab\leq a^2+b^2`. The base and normal-derivative energies are two
coordinates of the finite `L^2` graph norm, so their sum is bounded by the
full $`H^1` energy. Taking square roots and passing to the completion gives
the stated contraction estimate.
:::

Which boundary functions arise as traces is not answered by the estimate.
We first form the quotient of the domain by the trace kernel. It carries an
intrinsic norm and is realized injectively inside boundary $`L^2`. The
{bpref "sobolev.hilbert_trace_space_identification"}[Fourier section] identifies
this quotient with real $`H^{1/2}(\mathbb R^n)`, with equivalent norms.

We use one quotient construction for both flat and curved boundaries. The
first step needs only a continuous linear map; the least-norm extension will
use the Hilbert structure of its source.

:::definition "sobolev.kernel_quotient" (parent := "sobolev.trace") (lean := "Submodule.mkQL, Submodule.liftQL")
For a continuous linear map $`T:E\to F` between real normed spaces, set

$$`
Q_T:=E/\ker T.
`

Write $`[x]` for the class of $`x`. The quotient carries its quotient norm,
and $`T` induces a continuous linear map
$`\iota_T:Q_T\to F`, defined by $`\iota_T([x])=Tx`.
:::

:::theorem "sobolev.kernel_quotient_values" (parent := "sobolev.trace") (lean := "Submodule.liftQ_apply, Submodule.ker_liftQ_eq_bot") (uses := "sobolev.kernel_quotient")
The map $`\iota_T` is injective and satisfies $`\iota_T([x])=Tx`.
Thus quotient classes record exactly the distinct values of $`T`.
:::

:::proof "sobolev.kernel_quotient_values"
Two vectors have the same value under $`T` precisely when their difference
lies in $`\ker T`. They therefore define the same quotient class. The
formal proof uses Mathlib's quotient map and its kernel identity.
:::

:::definition "sobolev.kernel_quotient_representative" (parent := "sobolev.trace") (lean := "ContinuousLinearMap.KernelQuotient.representative") (uses := "sobolev.kernel_quotient")
If $`E` is a real Hilbert space, orthogonal decomposition identifies
$`Q_T` isometrically with $`(\ker T)^\perp`. Composing that identification
with the inclusion into $`E` defines a continuous linear representative map
$`R_T:Q_T\to E`.
:::

:::theorem "sobolev.kernel_quotient_minimality" (parent := "sobolev.trace") (lean := "ContinuousLinearMap.KernelQuotient.mk_representative, ContinuousLinearMap.KernelQuotient.norm_representative, ContinuousLinearMap.KernelQuotient.apply_representative, ContinuousLinearMap.KernelQuotient.representative_mem_orthogonal, ContinuousLinearMap.KernelQuotient.norm_representative_le_of_apply_eq, ContinuousLinearMap.KernelQuotient.representative_eq_of_mem_orthogonal") (uses := "sobolev.kernel_quotient_representative, sobolev.kernel_quotient_values")
For every $`q\in Q_T`,

$$`
[R_Tq]=q,\qquad TR_Tq=\iota_T(q),\qquad
\|R_Tq\|_E=\|q\|_{Q_T}.
`

Moreover, $`R_Tq` lies in $`(\ker T)^\perp` and has no larger norm than
any $`x` with $`Tx=\iota_T(q)`. It is the unique such vector orthogonal
to $`\ker T`. The norm here is the quotient norm; it need not agree with
the norm of the boundary value in $`F`.
:::

:::proof "sobolev.kernel_quotient_minimality"
The kernel is closed because $`T` is continuous. Mathlib's orthogonal
decomposition gives the quotient isometry and its inverse law, hence the
class identity and norm equality. Applying $`\iota_T` gives the value
identity. Every representative has norm at least its quotient norm, which
proves minimality. Uniqueness follows from the same orthogonal decomposition.
:::

:::definition "sobolev.hilbert_trace_space" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.traceKernel, SobolevSpace.Trace.HalfSpace.HilbertTraceSpace, SobolevSpace.Trace.HalfSpace.boundaryValue") (uses := "sobolev.flat_trace, sobolev.kernel_quotient_values")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The natural Hilbert boundary space of the flat trace is the quotient

$$`
\mathcal T^{1/2}(\mathbb R^n)
  :=H^1(\mathbb R^{n+1}_+)/\ker(\operatorname{Tr}_+).
`

Its quotient norm is the least upper-half-space $`H^1` norm among all
representatives of the same trace. The induced map

$$`
\mathcal T^{1/2}(\mathbb R^n)\longrightarrow L^2(\mathbb R^n)
`

is injective. Consequently the quotient is canonically realized as the range
of $`\operatorname{Tr}_+` equipped with its quotient norm. The Fourier
chapter identifies this range, with equivalent norms, with
$`H^{1/2}(\mathbb R^n)`, which justifies the notation.
:::

In a Hilbert space a closed subspace has an orthogonal complement, so the
quotient by the kernel has a canonical section. This is the feature that
separates $`p=2` from the finite-exponent construction below, where a right
inverse has to be built by hand.

Here the minimized quantity is the full squared $`H^1` norm,
$`\int(|u|^2+|\nabla u|^2)`. Orthogonality to every zero-trace variation
$`v` means

$$`
\int_{\mathbb R^{n+1}_+}(uv+\nabla u\cdot\nabla v)=0.
`

Testing with compactly supported smooth $`v` gives
$`-\Delta u+u=0` in the weak sense. The zeroth-order term comes from
including $`\|u\|_2^2` in the quantity being minimized; minimizing only
$`\int|\nabla u|^2` would give a different equation.
On the half-line, the least-norm extension of the endpoint value $`a` is
$`g(t)=ae^{-t}`. Indeed, $`-g''+g=0` and
$`\|g\|_{H^1}^2=a^2`, attaining the lower bound in the endpoint estimate.

:::definition "sobolev.hilbert_trace_minimal_extension" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.minimalExtension") (uses := "sobolev.hilbert_trace_space, sobolev.kernel_quotient_minimality")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Apply the representative map to $`T=\operatorname{Tr}_+`. This defines
the canonical extension $`E_{\min}`. For every class
$`q\in\mathcal T^{1/2}(\mathbb R^n)`, the shared quotient theorem gives

$$`
[E_{\min}q]=q,\qquad
\operatorname{Tr}_+(E_{\min}q)=\iota(q),\qquad
\|E_{\min}q\|_{H^1}=\|q\|_{\mathcal T^{1/2}}.
`

Here the middle equality uses the injective $`L^2` realization of the quotient
class. Moreover,

$$`
\|E_{\min}q\|_{H^1}\leq\|u\|_{H^1}
`

for every $`u` with the same boundary value. It is the unique such
representative orthogonal to $`\ker(\operatorname{Tr}_+)`.
:::


The construction is repeated for $`1\leq p<\infty`, following the same path
from the normal variable to the half-space. The one-dimensional input is an
inequality for compactly supported $`C^1` functions; only the half-space
operator is completed.

:::theorem "sobolev.half_line_finite_exponent_endpoint" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfLine.endpoint_abs_rpow_le_integral_add_integral") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`1\leq p<\infty` and $`f:\mathbb R\to\mathbb R` is compactly supported and
$`C^1`, then

$$`
|f(0)|^p\leq (p-1)\int_0^\infty |f(t)|^p\,dt+
  \int_0^\infty |f'(t)|^p\,dt.
`

This is the finite-exponent endpoint estimate used to construct the flat
$`W^{1,p}` trace.
:::

:::proof "sobolev.half_line_finite_exponent_endpoint"
Apply the fundamental theorem of calculus to $`|f|^p` on the positive
half-line, using compact support to eliminate the endpoint at infinity.
Mathlib's derivative rule for the real norm power expresses the result as an
integral of $`p|f|^{p-1}|f'|`. Young's inequality with conjugate exponents
$`p/(p-1)` and $`p` bounds that integrand by
$`(p-1)|f|^p+|f'|^p`.
:::

Integrating the endpoint inequality over the tangential variables produces the
finite-exponent analogue of the flat trace, with the same dense core of
restricted smooth functions and the same completion argument. The target is
now $`L^p(\mathbb R^n)`, and the constant in the inequality determines the
operator bound.

:::definition "sobolev.flat_trace_finite_exponent" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.traceLp") (uses := "sobolev.graph_space, sobolev.half_line_finite_exponent_endpoint")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every real $`p\geq1`, boundary restriction extends to a continuous linear map

$$`
\operatorname{Tr}_{+,p}:W^{1,p}(\mathbb R^{n+1}_+)
  \longrightarrow L^p(\mathbb R^n).
`

The domain is the completed finite-exponent Sobolev graph space. The
constructor takes a proof of `1 ≤ p`.
:::

Classical agreement and the operator bound are again the two facts carried
through the completion. The constant $`p^{1/p}` takes the place of the unit
constant of the Hilbert case.

:::theorem "sobolev.flat_trace_finite_exponent_bound" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.traceLp_smooth, SobolevSpace.Trace.HalfSpace.norm_traceLp_le") (uses := "sobolev.flat_trace_finite_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The finite-exponent trace agrees with literal restriction
$`y\mapsto f(y,0)` on globally smooth compactly supported functions and
satisfies

$$`
\|\operatorname{Tr}_{+,p}u\|_{L^p(\mathbb R^n)}
  \leq p^{1/p}\|u\|_{W^{1,p}(\mathbb R^{n+1}_+)}.
`
:::

:::proof "sobolev.flat_trace_finite_exponent_bound"
Integrate the one-dimensional endpoint estimate over tangential variables and
use the volume-preserving tangential-normal coordinate split. The base and
normal-derivative terms are bounded by coordinates of the finite `PiLp`
Sobolev graph norm, giving the constant $`p^{1/p}`. Restrictions of global
smooth compactly supported functions are dense by the half-space extension
and mollification theorem, so `LinearMap.extendOfNorm` supplies the completed
operator, its classical agreement, and the same norm bound.
:::

The completion defines $`\operatorname{Tr}_{+,p}u` through smooth
approximants of $`u`, not through $`u` itself. A second description
averages $`u` over a thin strip above the boundary:

$$`
A_\varepsilon u(y)=\frac1\varepsilon\int_0^\varepsilon u(y,t)\,dt,
\qquad \varepsilon>0 .
`

Each $`A_\varepsilon` is a bounded operator from
$`L^p(\mathbb R^{n+1}_+)` to $`L^p(\mathbb R^n)`. It reads $`u` only in the
open half-space, so it cannot see values assigned on the boundary, and yet
the averages converge to the trace.

{leanpde_figure "trace-height-average"}

In the figure the strip shrinks, and the averaged boundary function moves
onto the restriction $`u(y,0)` at the rate predicted by the estimate below.

:::theorem "sobolev.flat_trace_height_average" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.norm_heightAverageLp_sub_traceLp_rpow_le, SobolevSpace.Trace.HalfSpace.tendsto_heightAverageLp, SobolevSpace.Trace.HalfSpace.tendsto_heightAverageLp_of_tendsto, SobolevSpace.Trace.HalfSpace.heightAverage, SobolevSpace.Trace.HalfSpace.heightAverageLp, SobolevSpace.Trace.HalfSpace.norm_height_average_sub_rpow_le, SobolevSpace.VectorValued.Trace.HalfSpace.norm_heightAverageLp_sub_traceLp_rpow_le, SobolevSpace.VectorValued.Trace.HalfSpace.tendsto_heightAverageLp") (uses := "sobolev.flat_trace_finite_exponent, sobolev.flat_trace_finite_exponent_bound")
Let $`p\geq1`, $`\varepsilon>0` and $`U\in W^{1,p}(\mathbb R^{n+1}_+)` with
base coordinate $`U_0`. Then

$$`
\|A_\varepsilon U_0-\operatorname{Tr}_{+,p}U\|_{L^p(\mathbb R^n)}^p
  \leq\varepsilon^{p-1}\,\|\partial_tU\|_{L^p(\mathbb R^{n+1}_+)}^p .
`

For $`p>1` the right side tends to zero, so
$`A_\varepsilon U_0\to\operatorname{Tr}_{+,p}U` in $`L^p(\mathbb R^n)` as
$`\varepsilon\downarrow0`, along every sequence of positive heights. At
$`p=1` the theorem gives the error bound only. Both results also hold for
functions with values in a real Banach space.
:::

:::proof "sobolev.flat_trace_height_average"
For a $`C^1` function $`g` on $`[0,\varepsilon]`,

$$`
\frac1\varepsilon\int_0^\varepsilon g\,dt-g(0)
  =\frac1\varepsilon\int_0^\varepsilon\bigl(g(t)-g(0)\bigr)\,dt,
\qquad
|g(t)-g(0)|\leq\int_0^\varepsilon|g'| ,
`

and Hölder's inequality on the interval turns this into
$`|A g-g(0)|^p\leq\varepsilon^{p-1}\int_0^\varepsilon|g'|^p`. Apply this to
every normal slice of a smooth compactly supported function and integrate
over $`y`. Both sides of the resulting inequality are continuous on
$`W^{1,p}(\mathbb R^{n+1}_+)`, so density of the smooth restrictions carries
it to every $`U`. The proof is written once for Banach-valued functions,
and the scalar statement is read off through the identification of
real-valued Sobolev functions with $`\mathbb R`-valued ones.
:::

The kernel-quotient construction does not use the inner product, so it applies
verbatim at finite exponent. What it yields is a Banach quotient with an
injective boundary realization; the orthogonal-complement section of the
Hilbert case has no counterpart here.

:::definition "sobolev.flat_lp_trace_space" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.traceLpKernel, SobolevSpace.Trace.HalfSpace.LpTraceSpace, SobolevSpace.Trace.HalfSpace.traceLpClass, SobolevSpace.Trace.HalfSpace.boundaryValueLp, SobolevSpace.Trace.HalfSpace.traceLpEquivRange, SobolevSpace.Trace.HalfSpace.range_boundaryValueLp") (uses := "sobolev.flat_trace_finite_exponent, sobolev.kernel_quotient_values")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The intrinsic finite-exponent flat trace space is the Banach quotient

$$`
\mathcal T_p(\mathbb R^n)
  :=W^{1,p}(\mathbb R^{n+1}_+)/\ker(\operatorname{Tr}_{+,p}).
`

Its boundary-value map into
$`L^p(\mathbb R^n)` is continuous and injective,
and its range is exactly the range of $`\operatorname{Tr}_{+,p}`. The first
isomorphism theorem also gives a linear equivalence with that algebraic range.
For $`1<p<\infty` the Fourier chapter identifies the quotient with the
Gagliardo space of order $`1-1/p`.
:::

Without a canonical section, the existence of a bounded right inverse of the
quotient map becomes a question about extension operators. The criterion below
reformulates it in terms of the trace alone.

:::theorem "sobolev.flat_lp_trace_splitting_criterion" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.rightInverse_traceLpClass_iff") (uses := "sobolev.flat_lp_trace_space")
A bounded linear map
$`E:\mathcal T_p(\mathbb R^n)\to W^{1,p}(\mathbb R^{n+1}_+)` is a right
inverse of the quotient map exactly when

$$`
\operatorname{Tr}_{+,p}(Eq)=\iota(q)
`

for every intrinsic trace class $`q`, where $`\iota` is its injective
$`L^p` boundary realization. For $`1<p<\infty`, precomposing the mollified
lifting of the Fourier chapter with the Gagliardo identification gives such
an $`E`.
:::

:::proof "sobolev.flat_lp_trace_splitting_criterion"
Apply the injective boundary-value map to the proposed quotient identity.
Its factorization through the original trace converts that identity exactly
into the displayed trace equation; injectivity proves the converse.
:::

At $`p=2` the two constructions apply to the same functions and differ only in
how the exponent is written: the finite-exponent operator is defined
on $`W^{1,2}` with $`2` coerced from a real number, the Hilbert operator
on $`H^1`. The canonical identification induced
by $`\operatorname{ofReal}(2)=2` carries one operator to the other, and with
it kernels and quotients.

:::theorem "sobolev.flat_trace_exponent_two_compatibility" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.boundaryLpTwoEquivL2_traceLp, SobolevSpace.Trace.HalfSpace.upperW1pTwoEquivH1_mem_traceKernel_iff, SobolevSpace.Trace.HalfSpace.lpTraceSpaceTwoEquivHilbertTraceSpace_traceLpClass, SobolevSpace.Trace.HalfSpace.boundaryValue_lpTraceSpaceTwoEquivHilbertTraceSpace, SobolevSpace.Trace.HalfSpace.upperW1pTwoEquivH1, SobolevSpace.Trace.HalfSpace.boundaryLpTwoEquivL2, SobolevSpace.Trace.HalfSpace.lpTraceSpaceTwoEquivHilbertTraceSpace") (uses := "sobolev.flat_trace, sobolev.hilbert_trace_space, sobolev.flat_trace_finite_exponent, sobolev.flat_lp_trace_space")
At $`p=2`, the finite-exponent and Hilbert constructions are the same after
the canonical exponent identifications. If

$$`
J_\Omega:W^{1,2}(\mathbb R^{n+1}_+)\simeq H^1(\mathbb R^{n+1}_+),
\qquad
J_\partial:L^2(\mathbb R^n)\simeq L^2(\mathbb R^n),
`

then

$$`
J_\partial\operatorname{Tr}_{+,2}
  =\operatorname{Tr}_+J_\Omega.
`

The map $`J_\Omega` also identifies the two zero-trace kernels and descends to
a continuous linear equivalence

$$`
\mathcal T_2(\mathbb R^n)\simeq
\mathcal T^{1/2}(\mathbb R^n)
`

that commutes with quotient classes and boundary-value realizations.
:::

:::proof "sobolev.flat_trace_exponent_two_compatibility"
Transport both source and target along the equality
$`\operatorname{ofReal}(2)=2`. The two bounded operators agree on the dense
smooth core, hence agree everywhere. Their commuting identity carries one
kernel onto the other. The generic kernel-quotient congruence theorem then
descends $`J_\Omega` to the quotient spaces; quotient surjectivity proves the
boundary-value square.
:::

# Assembly on an Operational C¹ Domain

Boundary charts reduce each localized piece of a regular domain to the flat
model. Surface-measure comparison transports the half-space estimate back to
the physical boundary, and the finite partition of unity assembles one global
operator. The hypotheses expose every chart, cutoff, and quantitative bound
used in that argument.

:::definition "sobolev.surface_measure" (parent := "sobolev.trace") (lean := "SobolevSpace.Boundary.Geometry.SurfaceMeasure.surfaceMeasure")
For any set $`\Omega\subseteq\mathbb R^n`, the intrinsic surface measure is
the normalized codimension-one Euclidean Hausdorff measure restricted to the
topological frontier:

$$`
\sigma_\Omega:=\mathcal H^{n-1}\restriction\partial\Omega .
`

The normalization is Mathlib's, for which $`\mathcal H^n` on $`\mathbb R^n`
is Lebesgue measure, so on a flat hyperplane $`\sigma_\Omega` is Lebesgue
measure in tangential coordinates. The definition needs no regularity of
$`\Omega`; in dimension $`n=0` the codimension $`n-1` is truncated to $`0` by
natural subtraction, a case nothing uses. Every trace operator on an
operational $`C^1` domain below takes values in $`L^2(\partial\Omega,d\sigma)`
or $`L^p(\partial\Omega,d\sigma)` for this measure. The boundary-calculus
chapter proves that it has finite total mass on bounded operational $`C^1`
domains and compares it with the chart-assembled atlas measure.
:::

For the intrinsic measure to serve as the boundary measure on a general
domain, it must agree with tangential Lebesgue measure on the flat model,
where the trace theorems above were proved.

:::theorem "sobolev.surface_measure_half_space" (parent := "sobolev.trace") (lean := "SobolevSpace.Boundary.Geometry.SurfaceMeasure.surfaceMeasure_upperHalfSpace, SobolevSpace.Boundary.Geometry.SurfaceMeasure.map_flatEmbedding_volume, SobolevSpace.Boundary.Geometry.SurfaceMeasure.integral_flatSurfaceMeasure, SobolevSpace.Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure_lt_top_of_bounded, SobolevSpace.Boundary.Geometry.SurfaceMeasure.frontier_upperHalfSpace, SobolevSpace.Boundary.Geometry.SurfaceMeasure.isometry_flatEmbedding, SobolevSpace.Boundary.Geometry.SurfaceMeasure.range_flatEmbedding, SobolevSpace.Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure, SobolevSpace.Boundary.Geometry.SurfaceMeasure.flatEmbedding") (uses := "sobolev.surface_measure")
Let $`\mathbb R^{n+1}_+=\{x:x_{n+1}>0\}` and let
$`\iota:\mathbb R^n\to\mathbb R^{n+1}`, $`\iota(y)=(y,0)`, be the
inclusion of the boundary hyperplane. Then
$`\partial\mathbb R^{n+1}_+=\{x_{n+1}=0\}`, $`\iota` is an isometry onto
this hyperplane, and

$$`
\sigma_{\mathbb R^{n+1}_+}
  =\mathcal H^{n}\restriction\{x_{n+1}=0\}
  =\iota_*\mathcal L^n,
`

the pushforward of Lebesgue measure $`\mathcal L^n` on $`\mathbb R^n`.
Consequently, for every $`f:\mathbb R^{n+1}\to\mathbb R`,

$$`
\int f\,d\sigma_{\mathbb R^{n+1}_+}
  =\int_{\mathbb R^n}f(y,0)\,dy ,
`

as Bochner integrals, with no integrability hypothesis on $`f`, and every
bounded measurable subset of the hyperplane has finite surface measure.
:::

:::proof "sobolev.surface_measure_half_space"
The frontier of the open half-space is computed directly from the last
coordinate. The inclusion $`\iota` preserves distances, and an isometry
pushes normalized Hausdorff measure of any dimension forward to the same
Hausdorff measure restricted to its range; since $`\mathcal H^n` on
$`\mathbb R^n` is Lebesgue measure and the range of $`\iota` is the
hyperplane, this is the pushforward identity. The integral formula is the
change of variables along the closed measurable embedding $`\iota`. A
bounded set has bounded preimage under the isometry, hence finite Lebesgue
measure.
:::

With the two measures identified, the flat trace can be rewritten so that its
values are functions on the boundary hyperplane rather than of the tangential
coordinate. Composition with the measure-preserving projection is an isometry
of $`L^p` spaces, so the norm estimate is unchanged.

:::definition "sobolev.flat_trace_intrinsic" (parent := "sobolev.trace") (lean := "SobolevSpace.Boundary.Geometry.SurfaceMeasure.flatTrace, SobolevSpace.Boundary.Geometry.SurfaceMeasure.norm_flatTrace_le, SobolevSpace.Boundary.Geometry.SurfaceMeasure.liftLp, SobolevSpace.Boundary.Geometry.SurfaceMeasure.liftLp_apply_ae, SobolevSpace.Boundary.Geometry.SurfaceMeasure.measurePreserving_flatProjection, SobolevSpace.Boundary.Geometry.SurfaceMeasure.flatProjection") (uses := "sobolev.flat_trace, sobolev.flat_trace_bound, sobolev.surface_measure_half_space")
Let $`\pi:\mathbb R^{n+1}\to\mathbb R^n` drop the last coordinate. It is
measure preserving from the flat surface measure
$`\sigma=\mathcal H^n\restriction\{x_{n+1}=0\}` to Lebesgue measure on
$`\mathbb R^n`, so for every $`1\leq p\leq\infty` composition with $`\pi`
is a linear isometry

$$`
\Lambda_p:L^p(\mathbb R^n)\longrightarrow L^p(\sigma),
\qquad
\Lambda_pg=g\circ\pi\quad\sigma\text{-a.e.}
`

Composing the flat trace of {uses "sobolev.flat_trace"}[] with
$`\Lambda_2` gives the intrinsic flat trace

$$`
\operatorname{Tr}_{+}^{\sigma}
  :=\Lambda_2\circ\operatorname{Tr}_{+}
  :H^1(\mathbb R^{n+1}_+)\longrightarrow L^2(\sigma),
\qquad
\|\operatorname{Tr}_{+}^{\sigma}u\|_{L^2(\sigma)}
  \leq\|u\|_{H^1(\mathbb R^{n+1}_+)} .
`
:::

The intrinsic flat trace is the local model. On a domain with an operational
atlas, each boundary cutoff piece of a function is flattened by its chart,
traced on the half-space, and transported back to the physical boundary; the
finite partition of unity sums the pieces.

:::definition "sobolev.trace_operator" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.trace") (uses := "sobolev.graph_space, sobolev.extension.atlas, sobolev.flat_trace_bound, sobolev.surface_measure")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an operational bounded $`C^1` domain
$`\Omega\subseteq\mathbb R^{m+1}`, the library constructs a continuous linear
map

$$`
\operatorname{Tr}:H^1(\Omega)\longrightarrow L^2(\partial\Omega,
  d\sigma).
`

Here $`d\sigma` is the intrinsic codimension-one Hausdorff measure restricted
to the frontier; the charts enter the operator, not the measure. This is the
exponent-two case of Evans's theorem. The `C1ExtensionAtlas` hypothesis
supplies global chart extensions, cutoffs and a finite partition of unity. For a
bounded open set with $`C^1` graph boundary,
such an atlas exists. It also builds
the global extension operator of the preceding chapter, but the trace is
assembled directly from localized flattening maps and flat traces.
:::

The assembled operator is a finite sum of completed pieces, so it is
characterized by the same two facts as the flat model: agreement with literal
restriction on ambient smooth functions and a norm estimate. Agreement is now
in $`L^2(\partial\Omega,d\sigma)` with respect to the intrinsic surface
measure.

:::theorem "sobolev.trace_classical" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.trace_classical, SobolevSpace.Trace.C1.traceLp_eq_ae_of_continuousOn, SobolevSpace.Trace.C1.trace_eq_ae_of_continuousOn, SobolevSpace.Trace.C1.traceLp_eq_ae_of_continuousOn_of_local_graph") (uses := "sobolev.trace_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every globally smooth compactly supported ambient function, the assembled
trace agrees in boundary $`L^2` with literal restriction to
$`\partial\Omega`.

Agreement also holds beyond the smooth core. Let $`1\leq p<\infty` and let
$`U\in W^{1,p}(\Omega)` have a representative continuous on
$`\overline\Omega`. Then the finite-exponent trace $`\operatorname{Tr}_pU`
constructed below equals the boundary restriction of that representative
$`\sigma`-almost everywhere, and so does $`\operatorname{Tr}U` when $`p=2`.
These statements assume an inward partition of unity, a finite family of
cutoffs with a fixed inward direction on each patch. Such a partition exists
on bounded open $`C^1` domains, and one version of the statement assumes only
a bounded open set with $`C^1` graph boundary.
:::

:::proof "sobolev.trace_classical"
Localize the ambient smooth function by the finite boundary partition of
unity. Flattening with a $`C^1` chart and a target cutoff gives a compactly
supported $`C^1` function, so the compact-$`C^1` flat-trace agreement theorem
identifies its boundary value. The chart's surface-measure pushforward bound
transports this almost-everywhere identity back to the physical patch.
Summing the partition pieces yields literal boundary restriction in
$`L^2(\partial\Omega,d\sigma)`.

For a continuous representative, inward mollification gives smooth
approximants converging both in $`W^{1,p}` and pointwise on
$`\overline\Omega`. Their traces converge in boundary $`L^p`, so a
subsequence converges almost everywhere there. Smooth agreement identifies
this limit with the representative's boundary restriction.
:::

The estimate inherits the unit constant of the flat trace, so each chart
contributes only its flattening norm and its surface-measure distortion.

:::theorem "sobolev.trace_bound" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.norm_trace_le") (uses := "sobolev.trace_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The trace norm is bounded by a finite sum of atlas-dependent chart constants:

$$`
\|\operatorname{Tr}u\|_{L^2(\partial\Omega)}
\leq
\left(\sum_i C_i^{1/2}\|F_i\|\right)\|u\|_{H^1(\Omega)}.
`

Here $`F_i` is the continuous linear flattening operator for the $`i`th
localized chart and $`C_i` is its surface-measure distortion bound. Thus the
map in {uses "sobolev.trace_operator"}[] is quantitatively continuous.
:::

:::proof "sobolev.trace_bound"
Each flattened boundary piece satisfies the half-space trace estimate.  The
surface-measure pushforward bound transports that estimate to the physical
boundary, and the triangle inequality sums over the finite chart cover.
:::

The kernel-quotient construction of the flat case depends only on having a
bounded operator out of a Hilbert space, so it applies verbatim to the
assembled trace.

:::definition "sobolev.c1_hilbert_trace_space" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceKernel, SobolevSpace.Trace.C1.HilbertTraceSpace, SobolevSpace.Trace.C1.boundaryValue") (uses := "sobolev.trace_operator, sobolev.kernel_quotient_values")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The intrinsic Hilbert boundary space of an operational $`C^1` domain is

$$`
\mathcal T^{1/2}(\partial\Omega)
  :=H^1(\Omega)/\ker(\operatorname{Tr}).
`

It carries the quotient norm inherited from $`H^1(\Omega)`, and the induced
boundary-value map

$$`
\mathcal T^{1/2}(\partial\Omega)
  \longrightarrow L^2(\partial\Omega,d\sigma)
`

is injective. Hence this quotient realizes precisely the range of the
assembled trace inside boundary $`L^2`. The Fourier chapter identifies it,
with two-sided norm bounds, with a space of compatible chartwise $`H^{1/2}`
data, and shows that two atlases give equivalent chartwise spaces.
:::

Orthogonal decomposition in $`H^1(\Omega)` again produces the canonical
least-energy representative of each trace class. Minimality and uniqueness
come from Hilbert-space geometry alone, not from the charts.

:::definition "sobolev.c1_hilbert_trace_minimal_extension" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.minimalExtension") (uses := "sobolev.c1_hilbert_trace_space, sobolev.kernel_quotient_minimality")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Define $`E_{\min}` by applying the same representative map to the assembled
trace $`T=\operatorname{Tr}`. The quotient theorem gives, for every class $`q`,

$$`
[E_{\min}q]=q,\qquad
\operatorname{Tr}(E_{\min}q)=\iota(q),\qquad
\|E_{\min}q\|_{H^1(\Omega)}=\|q\|_{\mathcal T^{1/2}(\partial\Omega)}.
`

This extension has least $`H^1(\Omega)` norm among all functions with the
same boundary value and is the unique such representative orthogonal to the
zero-trace kernel.
:::


For $`1\leq p<\infty` the same chart assembly is run with the finite-exponent flat
trace as the local model. The parallel with the Hilbert case is exact except
for the constants and for the absence of an inner product on the quotient.

:::definition "sobolev.trace_operator_finite_exponent" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceLp") (uses := "sobolev.extension.atlas, sobolev.flat_trace_finite_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every real $`p\geq1` and every operational bounded $`C^1` domain
$`\Omega\subseteq\mathbb R^{m+1}`, the chart construction gives a continuous
linear map

$$`
\operatorname{Tr}_p:W^{1,p}(\Omega)\longrightarrow
  L^p(\partial\Omega,d\sigma).
`

The source is the general completed Sobolev graph space, and the target uses
intrinsic codimension-one Hausdorff measure on the frontier.
:::

Classical agreement and the norm estimate are inherited from the flat
finite-exponent trace exactly as in the Hilbert case, with the flat
constant $`p^{1/p}` now appearing in each chart term alongside $`C_i^{1/p}`.

:::theorem "sobolev.trace_finite_exponent_classical_bound" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceLp_classical, SobolevSpace.Trace.C1.norm_traceLp_le") (uses := "sobolev.trace_operator_finite_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The completed operator agrees with literal boundary restriction on every
ambient smooth compactly supported function. It also satisfies

$$`
\|\operatorname{Tr}_p u\|_{L^p(\partial\Omega)}
\leq
\left(\sum_i C_i^{1/p}p^{1/p}\|F_i\|\right)
\|u\|_{W^{1,p}(\Omega)},
`

where $`F_i` is the chart-flattening operator and $`C_i` is the corresponding
surface-measure distortion bound.
:::

:::proof "sobolev.trace_finite_exponent_classical_bound"
Localize by the finite boundary partition, flatten each piece, and apply the
finite-exponent half-space trace estimate. The chart pushforward inequality
transports the local trace back with factor $`C_i^{1/p}`. On smooth input,
the compact-$`C^1` agreement theorem identifies each contribution with
$`\psi_i u` on the physical boundary. Summing the partition gives literal
restriction; summing the local norm estimates gives the stated bound.
:::

The intrinsic trace space is again the quotient by the kernel, as in the flat
case.

:::definition "sobolev.c1_lp_trace_space" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceLpKernel, SobolevSpace.Trace.C1.LpTraceSpace, SobolevSpace.Trace.C1.traceLpClass, SobolevSpace.Trace.C1.boundaryValueLp, SobolevSpace.Trace.C1.traceLpEquivRange, SobolevSpace.Trace.C1.range_boundaryValueLp, SobolevSpace.Trace.C1.Fractional.FiniteExponent.mem_range_traceLp_iff, SobolevSpace.Trace.C1.Fractional.FiniteExponent.lifting, SobolevSpace.Trace.C1.Fractional.FiniteExponent.traceLp_lifting, SobolevSpace.Trace.C1.Fractional.FiniteExponent.norm_lifting_le") (uses := "sobolev.trace_operator_finite_exponent, sobolev.kernel_quotient_values")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an operational $`C^1` domain and $`1\leq p<\infty`, the intrinsic trace
space is

$$`
\mathcal T_p(\partial\Omega)
  :=W^{1,p}(\Omega)/\ker(\operatorname{Tr}_p).
`

This Banach quotient maps continuously and injectively into
$`L^p(\partial\Omega,d\sigma)`, with image exactly
$`\operatorname{range}(\operatorname{Tr}_p)`. It is linearly equivalent to
that algebraic range. For $`1<p<\infty` the range is characterized
chartwise: $`g` is a trace if and only if every localized chart coordinate of
$`g` lies in the Gagliardo space of order $`1-1/p`, and compatible chart data
lift boundedly to $`W^{1,p}(\Omega)`. The range is thus identified as a set,
together with a bounded lifting, rather than through a norm equivalence
between $`\mathcal T_p(\partial\Omega)` and a chartwise Gagliardo space.
:::

As on the half-space, the orthogonal-complement construction needs an inner
product. The condition a bounded right inverse must satisfy is the same.

:::theorem "sobolev.c1_lp_trace_splitting_criterion" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.rightInverse_traceLpClass_iff") (uses := "sobolev.c1_lp_trace_space")
A bounded linear map
$`E:\mathcal T_p(\partial\Omega)\to W^{1,p}(\Omega)` splits the quotient map
if and only if

$$`
\operatorname{Tr}_p(Eq)=\iota(q)
`

for every intrinsic trace class $`q`, where $`\iota` is the injective
boundary realization.
:::

:::proof "sobolev.c1_lp_trace_splitting_criterion"
Factor the trace through the quotient map and the injective boundary-value
realization. A right inverse immediately gives the trace identity. Conversely,
the trace identity becomes equality after applying the boundary realization,
whose injectivity recovers the quotient identity.
:::

For $`1<p<\infty`, the local fractional traces and the lifting give such a
right inverse. Write $`Au=(\operatorname{localTrace}_i u)_i` and
$`L=\operatorname{lifting}`. Each $`L^p` coordinate of $`Au` is the
localized chart coordinate of $`\operatorname{Tr}_p u` almost everywhere.
Since a Gagliardo element is determined by its $`L^p` coordinate, $`A` vanishes on
$`\ker(\operatorname{Tr}_p)`. Thus the bounded linear map $`LA` descends
through the quotient to

$$`
E[u]=L(Au).
`

Compatibility of the chart data $`Au` with the physical trace gives
$`\operatorname{Tr}_p(E[u])=\operatorname{Tr}_p u=\iota([u])`.
The criterion above shows that $`E` splits the quotient. This splitting is
derived here from the maps above by quotient descent, and it requires
$`p>1`.

The two assembled operators overlap at $`p=2`, and their compatibility follows
the flat pattern: the canonical exponent identification of the domain carries
one operator to the other, hence one kernel and one quotient to the other.

:::theorem "sobolev.c1_trace_exponent_two_compatibility" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.boundaryLpTwoEquivL2_traceLp, SobolevSpace.Trace.C1.domainW1pTwoEquivH1_mem_traceKernel_iff, SobolevSpace.Trace.C1.lpTraceSpaceTwoEquivHilbertTraceSpace_traceLpClass, SobolevSpace.Trace.C1.boundaryValue_lpTraceSpaceTwoEquivHilbertTraceSpace, SobolevSpace.Trace.C1.domainW1pTwoEquivH1, SobolevSpace.Trace.C1.boundaryLpTwoEquivL2, SobolevSpace.Trace.C1.lpTraceSpaceTwoEquivHilbertTraceSpace") (uses := "sobolev.trace_operator, sobolev.c1_hilbert_trace_space, sobolev.trace_operator_finite_exponent, sobolev.c1_lp_trace_space")
For every operational $`C^1` domain, the finite-exponent trace at $`p=2`
commutes with the canonical identifications

$$`
J_\Omega:W^{1,2}(\Omega)\simeq H^1(\Omega),
\qquad
J_\partial:L^2(\partial\Omega)\simeq L^2(\partial\Omega):
`

$$`
J_\partial\operatorname{Tr}_2
  =\operatorname{Tr}J_\Omega.
`

Consequently $`J_\Omega` identifies the zero-trace kernels and induces a
continuous linear equivalence

$$`
\mathcal T_2(\partial\Omega)\simeq
\mathcal T^{1/2}(\partial\Omega)
`

compatible with quotient classes and their intrinsic boundary values.
:::

:::proof "sobolev.c1_trace_exponent_two_compatibility"
The finite and Hilbert operators agree on ambient smooth compactly supported
functions after exponent transport. Density of that core in $`H^1(\Omega)`
upgrades the agreement to equality of continuous linear maps. Kernel
compatibility follows from injectivity of the boundary exponent equivalence,
and the generic kernel-quotient construction supplies the trace-space
equivalence and its commuting boundary-value identity.
:::

Everything above was built from one atlas: its charts, flattening operators
and partition of unity all enter the constant in the trace bound. The
operator itself does not depend on those choices. Since the operator is
assembled chart by chart, this has to be proved. Two continuous
linear maps that agree on a dense set are equal, and every atlas produces a
map that is literal restriction on smooth functions.

:::theorem "sobolev.trace_atlas_independence" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceLp_eq_of_atlases, SobolevSpace.Trace.C1.eq_traceLp_of_classical, SobolevSpace.VectorValued.Trace.C1.traceLp_eq_of_atlases, SobolevSpace.VectorValued.Trace.C1.eq_traceLp_of_classical") (uses := "sobolev.trace_operator_finite_exponent, sobolev.trace_finite_exponent_classical_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "272-273"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1\leq p<\infty`. A continuous linear map
$`T:W^{1,p}(\Omega)\to L^p(\partial\Omega,d\sigma)` that sends every
restriction of an ambient smooth compactly supported function to its
boundary values is the trace $`\operatorname{Tr}_p`. In particular, two
operational $`C^1` atlases on the same domain construct the same continuous
linear trace. Both statements also hold for functions with values in a real
Banach space.
:::

:::proof "sobolev.trace_atlas_independence"
For finite $`p`, restrictions of ambient smooth compactly supported functions
are dense in $`W^{1,p}(\Omega)`: extend with any one atlas, mollify in the
whole space, and restrict. On that set $`T` and $`\operatorname{Tr}_p` both
give literal restriction, by hypothesis and by classical agreement. The
target is built from intrinsic surface measure, which involves no chart, so
the two maps have the same codomain and agree everywhere by continuity.
For two atlases, apply the first statement to the trace built from the
first atlas, with the second atlas defining $`\operatorname{Tr}_p`.
:::

The same chart assembly works for functions with values in a real Banach
space $`F`. The half-space trace of an $`F`-valued function is built from the
endpoint inequality for norms, and the charts transport it exactly as in the
scalar case. For $`F=\mathbb R` it reproduces the scalar trace, and it
commutes with every bounded linear map $`L:F\to G`, so a trace can be taken
before or after applying $`L` pointwise.

:::theorem "sobolev.vector_c1_trace" (parent := "sobolev.trace") (lean := "SobolevSpace.VectorValued.Trace.C1.traceLp_coeFn_ae, SobolevSpace.VectorValued.Trace.C1.traceLp, SobolevSpace.VectorValued.Trace.C1.norm_traceLp_le, SobolevSpace.VectorValued.Trace.C1.traceLp_mapCLM, SobolevSpace.VectorValued.Trace.C1.traceLp_comp_mapCLM, SobolevSpace.VectorValued.Trace.C1.traceLp_eq_scalar_traceLp, SobolevSpace.VectorValued.Trace.C1.dense_compact_smooth, SobolevSpace.VectorValued.Trace.HalfSpace.traceLp, SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_c1, SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_mapCLM, SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_eq_scalar_traceLp") (uses := "sobolev.trace_operator_finite_exponent, sobolev.trace_finite_exponent_classical_bound")
Let $`F` be a real Banach space, $`1\leq p<\infty`, and $`\Omega` an open
set carrying an operational $`C^1` atlas. There is a continuous linear map

$$`
\operatorname{Tr}_p:W^{1,p}(\Omega;F)\longrightarrow
  L^p(\partial\Omega,d\sigma;F)
`

with the same chart-sum bound as the scalar trace. If the base coordinate of
$`U` agrees almost everywhere on $`\Omega` with an ambient $`C^1` function
$`f`, then $`\operatorname{Tr}_pU=f|_{\partial\Omega}`; $`f` need not have
compact support. For every bounded linear $`L:F\to G` into a real Banach
space,

$$`
\operatorname{Tr}_p(L\circ U)=L\circ\operatorname{Tr}_pU ,
`

and for $`F=\mathbb R` the trace agrees with the scalar
$`\operatorname{Tr}_p` under the identification of the two graph spaces.
The flat half-space trace has the same properties, with a compactly
supported $`C^1` representative in the classical formula.
:::

:::proof "sobolev.vector_c1_trace"
The operator is the finite sum over charts of localize, flatten, take the
half-space trace, and transport back to surface measure. Each summand is
bounded, which gives the bound. On a $`C^1` representative each summand is
the restriction of $`\psi_if`, and the cutoffs sum to one on the boundary;
the cutoffs also supply the compact support the flat theorem needs. For
naturality, both sides are continuous in $`U` and agree on ambient smooth
compactly supported functions by the classical formula, which are dense.
Scalar compatibility is the same density argument, since the scalar
identification preserves every Sobolev coordinate and the graph norm.
:::

# Zero Traces and Higher-Order Closures

The zero-boundary spaces are defined by closure of compactly supported smooth
functions. Continuity of the trace immediately gives one inclusion into its
kernel; the converse inclusion needs an approximation argument. At higher
order, the closure argument is applied to every lower-order derivative slice.

:::theorem "sobolev.zero_trace" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.trace_coe_H10_eq_zero") (uses := "sobolev.trace_operator, sobolev.h10_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "273-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every element of the closure-defined subspace $`H^1_0(\Omega)` has zero
trace: $`H^1_0(\Omega)\subseteq\ker(\operatorname{Tr})`. The reverse
inclusion is the kernel characterization below.
:::

:::proof "sobolev.zero_trace"
Smooth compactly supported test functions have vanishing classical boundary
values.  Continuity of the trace passes this identity to their $`H^1` closure,
which is the definition of $`H^1_0`.
:::

The same continuity argument applies to the finite-exponent trace, with the
closure $`W^{1,p}_0(\Omega)` of compactly supported smooth functions in place
of $`H^1_0(\Omega)`.

:::theorem "sobolev.zero_trace_finite_exponent" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.C1.traceLp_coe_W1p0_eq_zero") (uses := "sobolev.trace_operator_finite_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "273-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every real $`p\geq1`,

$$`
W^{1,p}_0(\Omega)\subseteq\ker(\operatorname{Tr}_p).
`

Here $`W^{1,p}_0` is the closure of compactly supported smooth functions in
the same finite-exponent graph space used by the trace.
:::

:::proof "sobolev.zero_trace_finite_exponent"
Literal boundary restriction vanishes for every compactly supported smooth
function on the open domain. The trace is continuous, and those functions
have dense image in the closure defining $`W^{1,p}_0`, so the identity
extends to the whole supported-core completion.
:::

For the converse, extend a trace-zero function on the half-space by zero.
The normal Green identity, with the boundary term equal to the vanishing
trace, shows that the extension stays in $`W^{1,p}` of the whole space.
Translating it upward creates a strip above the boundary on which it
vanishes, and mollification with cutoffs then gives test functions inside
the half-space. On a $`C^1` domain the charts reduce the question to this
case.

:::theorem "sobolev.trace_kernel_characterization" (parent := "sobolev.trace") (lean := "SobolevSpace.Trace.HalfSpace.traceLp_eq_zero_iff_mem_Wkp0, SobolevSpace.Trace.HalfSpace.ker_traceLp_eq_wkp0SubmoduleOn, SobolevSpace.Trace.C1.traceLp_eq_zero_iff_mem_Wkp0, SobolevSpace.Trace.C1.trace_eq_zero_iff_mem_H10, SobolevSpace.Trace.C1.ker_traceLp_eq_wkp0SubmoduleOn, SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_eq_zero_iff_mem_Wkp0, SobolevSpace.VectorValued.Trace.HalfSpace.ker_traceLp_eq_wkp0SubmoduleOn, SobolevSpace.VectorValued.Trace.C1.traceLp_eq_zero_iff_mem_Wkp0, SobolevSpace.VectorValued.Trace.C1.ker_traceLp_eq_wkp0SubmoduleOn") (uses := "sobolev.zero_trace, sobolev.zero_trace_finite_exponent, sobolev.flat_trace_finite_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "273-275"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1\leq p<\infty`, and let $`\Omega` be the upper half-space or an
operational $`C^1` domain. Then

$$`
\ker(\operatorname{Tr}_p)=W^{1,p}_0(\Omega),
`

and in particular $`\ker(\operatorname{Tr})=H^1_0(\Omega)`. The same holds
for functions with values in a real Banach space.
:::

:::proof "sobolev.trace_kernel_characterization"
One inclusion is the previous theorem. For the other, a half-space function
with zero trace is approximated by the zero extension, upward translation and
mollification described above. On a $`C^1` domain, the partition of unity
splits the function into an interior piece with compact support and boundary
pieces; each boundary piece is flattened, approximated on the half-space, and
returned through its chart.
:::

Vanishing trace is one formal expression of zero boundary values, and it needs
a trace operator, hence on a general domain an operational atlas. A second
expression needs no boundary regularity at all: a function in $`H^1_0(\Omega)`
can be extended by zero without leaving $`H^1`, because no jump is created
across $`\partial\Omega`.

:::definition "sobolev.zero_extension_h10" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ₗᵢ, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendAmbient, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendWkp0") (uses := "sobolev.h10_space, sobolev.h1_space")
Let $`\Omega\subseteq\mathbb R^n` be measurable. Extending each coordinate
of an $`H^1(\Omega)` bundle by zero outside $`\Omega` is a continuous linear
map of coordinate bundles, $`(u_a)_a\mapsto(\mathbf 1_\Omega u_a)_a`. On the
zero-trace subspace it lands in whole-space $`H^1`, giving a continuous
linear map and a linear isometry

$$`
E_0:H^1_0(\Omega)\longrightarrow H^1(\mathbb R^n),
\qquad
\|E_0u\|_{H^1(\mathbb R^n)}=\|u\|_{H^1(\Omega)} .
`

Measurability of $`\Omega` is the only hypothesis; no openness or boundary
regularity is required. The zero extension of an arbitrary $`H^1(\Omega)`
function is not in $`H^1(\mathbb R^n)` in general, because a jump across
$`\partial\Omega` creates a boundary measure; the theorem below shows that
the closure definition of $`H^1_0` rules this out.
:::

Everything in the definition rests on the whole-space weak-derivative
identities for the zero-extended bundle.

:::theorem "sobolev.zero_extension_h10_isometry" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.ZeroTrace.zeroExtendAmbient_mem_globalWkp, SobolevSpace.GraphSpace.ZeroTrace.norm_zeroExtendWkp0, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendWkp0_coordinate, SobolevSpace.GraphSpace.ZeroTrace.norm_zeroExtendH10, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10_coordinate_apply_ae, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10_testFunction_eq, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10_injective, SobolevSpace.GraphSpace.ZeroTrace.restrict_zeroExtendH10, SobolevSpace.GraphSpace.ZeroTrace.restrictCLM_comp_zeroExtendH10") (uses := "sobolev.zero_extension_h10, sobolev.graph_space_restriction")
Let $`\Omega` be measurable, let $`u\in H^1_0(\Omega)`, and write
$`\widetilde u=E_0u`. The coordinatewise zero extension of $`u` satisfies
every whole-space weak-derivative identity, so
$`\widetilde u\in H^1(\mathbb R^n)`, and its coordinates are

$$`
\widetilde u_0=\mathbf 1_\Omega u_0,
\qquad
\widetilde u_i=\mathbf 1_\Omega u_i
\quad\text{almost everywhere on }\mathbb R^n ,
`

so the weak derivatives of the extension are the zero extensions of the
weak derivatives. Moreover:

- $`\|\widetilde u\|_{H^1(\mathbb R^n)}=\|u\|_{H^1(\Omega)}`, and $`E_0`
  is injective;
- for a test function $`\varphi` supported in $`\Omega`, $`E_0\varphi` is
  $`\varphi` itself regarded as an element of $`H^1(\mathbb R^n)`;
- if $`\Omega` is open, restriction back to $`\Omega` is a left inverse:
  $`\rho_{\mathbb R^n,\Omega}\circ E_0` is the inclusion
  $`H^1_0(\Omega)\to H^1(\Omega)`.
:::

:::proof "sobolev.zero_extension_h10_isometry"
For a test function supported in $`\Omega`, the zero extension of the bundle
is the bundle of the same smooth function on $`\mathbb R^n`, so the
whole-space identities hold literally. The set of $`u\in H^1(\Omega)` whose
extended bundle lies in the closed whole-space graph submodule is the
preimage of a closed set under a continuous linear map, hence closed, and it
contains the test functions; the closure principle for $`H^1_0` gives the
first claim. Indicator extension preserves each coordinate's $`L^2` norm,
and the graph norm is the $`\ell^2` sum of coordinate norms, which gives the
isometry and injectivity. The coordinate formula is the almost-everywhere
description of $`L^2` zero extension. For open $`\Omega`, restricting
$`\mathbf 1_\Omega u_a` to $`\Omega` recovers $`u_a` almost everywhere, and
an $`H^1(\Omega)` element on an open set is determined by its base
coordinate through uniqueness of weak derivatives.
:::

The closure argument works for every derivative order $`k` and every
$`1\le p\le\infty`. Extend each derivative coordinate by zero, use the
closedness of the global weak-derivative graph, and take the closure of the
supported smooth functions. This gives

$$`
E_0:W^{k,p}_0(\Omega)\longrightarrow W^{k,p}(\mathbb R^n),
\qquad \|E_0u\|_{W^{k,p}(\mathbb R^n)}=\|u\|_{W^{k,p}(\Omega)}.
`

Here $`W^{k,p}_0` means that supported smooth-core closure, including at
$`p=\infty`. The domain need only be measurable. PDEAtlas uses this common
construction for the $`H^1_0` results above; the derivative identities and
norm preservation are proved once.

Restricting the whole-space extension to an open set gives a relative
version. As on the whole space, the left-inverse property comes from
uniqueness of weak derivatives on the smaller open set.

:::definition "sobolev.zero_extension_h10_superset" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSupersetₗᵢ, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSuperset, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSupersetH1, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSupersetH1_mem_H10, SobolevSpace.GraphSpace.ZeroTrace.norm_zeroExtendH10ToSuperset, SobolevSpace.GraphSpace.ZeroTrace.restrict_zeroExtendH10ToSuperset, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSuperset_injective, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSuperset_self, SobolevSpace.GraphSpace.ZeroTrace.zeroExtendH10ToSuperset_comp") (uses := "sobolev.zero_extension_h10, sobolev.zero_extension_h10_isometry, sobolev.graph_space_restriction")
Let $`V` and $`\Omega` be open subsets of $`\mathbb R^n`. Restricting the
whole-space zero extension of {uses "sobolev.zero_extension_h10"}[] to
$`\Omega` gives a continuous linear map $`H^1_0(V)\to H^1(\Omega)`. When
$`V\subseteq\Omega`, its values lie in the zero-trace subspace, and the
resulting map

$$`
E_{V,\Omega}:H^1_0(V)\longrightarrow H^1_0(\Omega),
\qquad
\|E_{V,\Omega}u\|_{H^1(\Omega)}=\|u\|_{H^1(V)},
`

is a linear isometry, hence injective, with restriction as a left inverse:
$`\rho_{\Omega,V}\circ E_{V,\Omega}` is the inclusion
$`H^1_0(V)\to H^1(V)`. The construction is functorial: $`E_{\Omega,\Omega}`
is the identity, and $`E_{V,\Omega}\circ E_{U,V}=E_{U,\Omega}` for open
$`U\subseteq V\subseteq\Omega`. This is the operator behind localization
arguments that regard a function supported in a subdomain as a zero-trace
function on the whole domain.
:::

The space $`H^1_0(\Omega)` is the first-order, exponent-two instance of a
closure that makes sense at every order. At higher order the natural question
is which derivatives of an element of the closure themselves have zero
boundary values.

The distinction already appears for $`u(x)=x(1-x)` on $`(0,1)`.
It is smooth, belongs to $`H^2(0,1)`, and vanishes at both endpoints,
so it lies in $`H^1_0(0,1)`. But $`u'(x)=1-2x` has endpoint values
$`1` and $`-1`. It cannot be an $`H^2` limit of smooth functions
compactly supported in the interval: their derivatives would converge to
$`u'` in $`H^1`, forcing both derivative traces to be zero. Thus
$`H^2_0(0,1)` imposes more than membership in
$`H^2(0,1)\cap H^1_0(0,1)`. Taking a closure at higher order also controls
boundary values of lower-order derivatives.

:::definition "sobolev.higher_order_zero_trace_space" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.wk0SubmoduleOn, SobolevSpace.GraphSpace.Wk0SpaceOn") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-260"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every finite order $`k`, the supported-core space

$$`
W^{k,2}_0(\Omega)
  = \overline{C_c^\infty(\Omega)}^{\,W^{k,2}(\Omega)}
`

is defined as a closed submodule of the completed Sobolev graph space. This
is Evans's closure definition on open domains. The Lean definition makes
sense for arbitrary sets; trace characterizations need an open domain with
regular boundary.
:::

To ask whether $`D^\alpha u` has zero trace, one must first regard it as an
element of $`H^1(\Omega)`, which requires its own first derivatives.
For $`|\alpha|<m` these are among the stored coordinates of a $`W^{m,2}`
element, and the slice operator collects them.

:::definition "sobolev.first_order_derivative_slice" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.derivativeSliceIndex, SobolevSpace.GraphSpace.derivativeSliceAmbient, SobolevSpace.GraphSpace.derivativeSlice") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U\in W^{m,2}(\Omega)` and let $`\alpha` be a derivative word with
$`|\alpha|<m`. The canonical first-order derivative slice is a continuous
linear map

$$`
S_\alpha:W^{m,2}(\Omega)\longrightarrow H^1(\Omega).
`

Its base coordinate is the symmetric Sobolev coordinate representing
$`D^\alpha U`, while its first coordinate in direction $`i` is the coordinate
representing $`D^{\alpha+[i]}U`. Thus the slice holds exactly the
derivative and the one-more-order data needed to regard $`D^\alpha U` as an
$`H^1` element. It is different from the later arbitrary-order
derivative-word operator: only this first-order slice is needed for traces.
:::

:::theorem "sobolev.higher_order_zero_trace_slices" (parent := "sobolev.trace") (lean := "SobolevSpace.GraphSpace.Wk0SpaceOn.derivativeSlice_mem_H10") (uses := "sobolev.higher_order_zero_trace_space, sobolev.first_order_derivative_slice")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "259"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "273-275"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be any set, not necessarily open. If
$`u\in W^{m,2}_0(\Omega)` and $`|\alpha|<m`, then the canonical first-order
slice representing $`D^\alpha u` belongs to $`H^1_0(\Omega)`. This is the
closure form of the statement that all derivatives below top order have zero
boundary values, and it is one direction of the characterization of
$`W^{m,2}_0` by vanishing traces of derivatives.
:::

:::proof "sobolev.higher_order_zero_trace_slices"
The property that an order-$`\alpha` derivative slice lies in the closed
$`H^1_0` subspace is closed in $`W^{m,2}`. Classical differentiation preserves
compact support for every smooth core function, so density passes the
property to the supported-core closure.
:::
