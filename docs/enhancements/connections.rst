# (Linear) Connections on tensor bundles

## Motivation

Consider a differentiable curve `γ` in `ℝ^n`: `γ : ℝ → ℝ^n` and its derivative `γ'`. When you do calculus on vector spaces, `γ'` is also a curve `γ' : ℝ → ℝ^n` in `ℝ^n`, for example interpreted as the velocity. You would easily talk about the higher order derivatives as well, for example the acceleration `γ'' : ℝ → ℝ^n`, and all derivatives have the same type `ℝ → ℝ^n`.

If you do calculus on manifolds, this fails completely: a curve on a manifold is a differentiable map `γ : ℝ → M`, but the derivative of `γ` is a map `γ' : Tℝ → Tℝ^n`, where `Tℝ` and `Tℝ^n` are the tangent bundles of `ℝ` and `ℝ^n` resp. On vector spaces we don't see this because the tangent bundle `TV`od a vector space `V` is the trivial bundle and we simply project to the fibre - but this is not possible in general manifolds.
A naive approach to higher order derivatives would involve tangent bundles of tangent bundles of... which is simply not useful at all.

Another view on this problem is the original motivation of derivatives: the derivative encodes how a "thing" (a vector, a point on a curve) changes over time or another parameter. This involves comparing objects in the tangent space at two different points on the manifold. For vector spaces this, works because we identify the tangent space at any point with the vector space itself and the derivatives lie in the same vector space.
In manifolds, this won't work because we can simply compare two tangent spaces at different points.

To resolve this, we introduce (linear) connections to allow us to differentiate "things" which vary of the manifold such that the derivative of such a "thing" has the same type as the "thing" itself. A "thing" of course being vectors in many cases, but also arbitrary tensor fields on `M`. If such derivative is `0`, we call the "thing" parallel, which correponds to being constant in calculus on vector spaces.
Also, we can repeat the process, creating a notion of higher order derivatives.


## Definition of (linear) connections

In differential geometry, the (linear) connection is often defined as follows:

Let `E` be a vector bundle over a manifold `M`, `𝓧(M)` the vector fields on `M` and `Γ(E)` the sections in `E`. A linear connection on `E` is a map `𝓓 : 𝓧(M) × Γ(E) → Γ(E)` such that:
* `𝓓` is `C^n`-linear in the first component,
* `𝓓` is `𝕜`-linear in the second component, and
* `𝓓` follows the Leibniz rule (or product rule) in the second component.

More precisely, for any sections `s, s₁, s₂`, vector fields `X, X₁, X₂`, functions `f₁ f₂` on `M` and `a₁ a₂ ∈ 𝕜` we have:
* `𝓓(f₁ X₁ + f₂ X₂, s) = f₁ 𝓓(X₁, s) + f₂ 𝓓(X₂, s)`
* `𝓓(X, a₁ s₁ + a₂ s₂) = a₁ 𝓓(X, s₁) + a₂ 𝓓(X, s₂)`
* `𝓓(X, f s) = Df s + f 𝓓(X, s)` where `Df` is the differential of `f` which operates linearly on the vector fiels.

Here, the first component is the direction in which we want to differentiate, the second component is the section we want to to differentiate and the image is the derivate: `𝓓 (X, s) = 𝓓_X s` is the derivative of `s` in the direction of the vector field `X`.

**In Mathlib, we define a connection in a different order**: the first component is the section and the second component is the direction, i.e. `𝓓` is of type `(Π (x : M), E x) → (Π (x : M), TangentSpace I  x) → (Π (x : M), E x)`.

This allows us to write something like `𝓓 s` for the derivative of `s`, which is applied to a vector field `X` giving the derivative `𝓓 s X` of `s` in the direction of `X`.

Here is the full definition of a linear connection on vector bundles:

```

```





Topics to cover:
* Motivation: second order derivative fails
* connections on vector bundles in general
* affine connection on vector fields
* How to define a parallel tensor? Like a type class IsParallel for a class of tensors? Or just as a proposition isParallel iff Ds = 0?
* normal derivative as connection on functions (which are sections in the trivial bundle M \times k over M)
* torsion tensor, curvature tensor

* Sectional, Ricci and scalar curvature require metric?

Requires:
* manifolds.md
* tensorFields.md
