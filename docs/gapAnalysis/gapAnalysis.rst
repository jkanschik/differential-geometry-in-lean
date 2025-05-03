A Gap Analyis for Riemannian Geometry
====================================

To make any statements about (Pseudo-)Riemannian Geometry, many structures and propositions need to be established in Mathlib. On this page we give an opinionated overview about topics which often occur in Riemannian Geometry.

A few things to note:
* The analysis focuses on real manifolds, though most statements can be made over a general `NontriviallyNormedField`.
* Some parts may not work for Pseudo-Riemannian geometries.
* The description is not mathematically precise, it should just give an idea of the topic.
* Many interesting topics are missing - but we have to start somewhere.

## Curves and submanifolds

Typical constructions for curves and submanifolds are:
1. Differential curves vs. piece-wise differential curves
1. Length of curves (requires metric)
1. Differentiation along curves ("velocity")
1. Immersions of submanifolds, i.e. smooth maps `N -> M` where the derivative has maximal rank / is injective
1. Construction of vector fields along curves and immersions, for example:
    1. normal vector fields (requires metric)
    1. projection onto the tangent space of `N` (requires metric)
    1. parallel vector fields along `N` (requires connection)
1. Variations of curves, especially geodesics; variations per se are simply immersions of `[0, 1] x [0, 1]` or similar. For geodesic variations, metric and connection is required

## Vector bundles and tensor bundles

Here, we refer only to vector bundles, not to principal fibre bundles etc. For example, we wouldn't be able to define Chern classes, Yang-Mills, Ehresmann connections etc.

Most vector bundles in Riemannian are actually tensor bundles of the tangent bundle and many objects are usually viewed as sections in tensor bundles of the tangent bundle (aka tensors).

A tensor (field) of type (k,l) is a smooth section in a tensor bundle with type (k,l) of the tangent bundle.

Examples for such objects are:
1. The metric is a (0, 2) tensor
1. The curvature tensor is a (1, 3) tensor
1. The Ricci tensor is also a (0, 2) tensor - this is why we can combine Ric and g in General Relativity
1. The curvature tensor for the Levi-Civita connection is sometimes also seen as a (2, 2) or (0, 4) tensor. For example `R(X ∧ Y) = Z ∧ W`, which is a symmetric, bilinear form on the exterior product `TM ∧ TM`.
1. A function can be seen as a (0, 0) tensor
1. A vector field is a (1, 0) tensor
1. The torsion of a connection is a (1, 2) tensor
1. Differential forms are alternating (0, k) tensors, or sections in the exterior product of the tangent bundle.

We also have vector bundles in the theory of submanifolds:
1. Vector fields along immersions `i: N -> M` can be seen as sections in the bundle over `N` with fibre `T_i(p) M`
1. If we have a metric, we can project `TM` to `TN` and define the normal bundle with base `N` and the fibres are the vector space orthogonal to `TN` in `TM`.

Topics to cover:
1. Construction of the (k, l) tensor bundle from another vector bundle (probably only used for tensor bundles from `TM`, but can be generalized)
1. Define exterior product of vector bundles - either repeating the process for tensor bundles, or by defining it as a sub bundle of the tensor bundle.
1. Define sub bundle, for example to define the immersed tangent bundle of a submanifold or the normal bundle. Maybe a statement that the kernel of a pointwise linear map of the fibre to "something" creates a subbundle. This could be used to define exterior products and symmetric products.
1. Contractions / traces and similar constructions on tensors.
1. Define a metric on tensor products

## Linear Connections

The most important connection on (Pseudo-)Riemannian manifolds is the Levi-Civita connection, but for example in the theory of homogeneous spaces there are other linear connections, such that all left invariant vector fields along curves are parallel.

Connections are also used for submanifolds, like the normal connection which is used in the formulation of the Gauss-Codazzi equations.

Any connection on `TM` induces a connection on the tensor bundles. This is used for the derivative of the curvature tensor, Ricci tensor or the second fundamental form (parallel submanifolds).

So, topics to look at are:
1. Definition of linear connections on arbitrary vector bundles, including bundles over immersions.
1. Definition of curvature of linear connections and torsion of affine connections.
1. Define parallel sections / parallel transport on vector bundles, prove existence and uniqueness (Picard-Lindeloff in coordinates).
1. Special case: the affine connections on `TM`
1. A connection on a vector bundle induces a unique connection on the tensor bundles.
1. Levi-Civita connection: this is the unique affine connection which has no torsion and where the metric (0, 2) tensor is parallel.
1. Definition of curvature: curvature tensor, Ricci, scalar curvature, sectional curvature on planes

## Geodesics and exponential map

This part requires metrics and connections.

* Define a geodesic as having zero second derivative
* Existence, uniqueness of geodesics (Picard-Lindeloff)
* Define exponential map
* Describe length of a curve, geodesic variations, action / Energy of the curve
* Prove that geodesics are minimizing
* Geodesic distance is a metric

## Curvature and Geodesics

* Define variation vector fields (=> Jacobi fields)
* Prove Jacobi formula `J''(t) = R(J(t), c'(t)) c'(t)`
* Estimations for Jacobi fields in presence of upper / lower bounds for curvature?
* Statements about the injectivity radius

## Differential forms & de Rham cohomology

If we have the exterior product of vector bundles defined, we can introduce differential forms and the derivative:

* Define the space of differential forms and proof structural results (module over differentiable functions)
* Define exterior derivative of differential forms (axiomatic approach)
* Proof `d d = 0`
* Define de Rham cohomology
* State the theorem of de Rham (probably no proof...)

## Isometries and Lie groups

Though a generic manifold has no isometries, many interesting examples have many isometries or are even homogeneous.

A few topics:
* Define an isometry and the isotropy at a point
* Proof that Isom(M) is a group (not a Lie group, yet)
* Proof that Isom(M) is a Lie group.
* Construct differentiable structure on quotients (such that the projection becomes a submersion)
* Construct metric on the quotient (assuming the total space has a metric)
* Proof that G/H becomes a Riemannian manifold if H compact and G carries an appropriate left invariant metric.
* Define S^n, CP^n, HP^n with Fubini-Studi metric as first example of symmtric spaces.


## Dependency diagram

The red topics should be the first; as a first milestone, we could introduce the Levi-Civita Connection and proof it's existence and uniqueness.

```mermaid
graph TD;

    subgraph "Vector and Tensor Bundles"
        T1["Construction of tensor bundles"]
        style T1 color:red
    end

    subgraph "Metrics"
        T2["Definition of metric"]
        style T2 color:red
        T12["Musical isomorphisms on tensors"]
        style T12 color:red
        T3["Define length of curves"]
        T4["Definition of Isom(M,g;M',g'), Isom(M,g) and Isom₀(M,g)"]
        T5["Isom(M,g) is a group and Isom₀(M,g) a normal subgroup"]

        T2-->T3
        T2-->T12
        T2-->T4-->T5
    end

    T1-->T2

    subgraph "Connections"
        T17["Definition of connections on vector bundles"]
        style T17 color:red
        T18["Define affine connection as a connection on TM"]
        style T18 color:red
        T11.1["Definition of torsion and torsion free"]
        style T11.1 color:red

        T10["Connections on vector bundles induce connection on tensor bundles"]
        style T10 color:red
        T13.1["Connection is compatible with metric if g is parallel"]
        style T13.1 color:red

        T11["Definition of curvature tensor"]


        T13["Levi-Civita connection"]
        style T13 color:red
        T14["Ricci, scalar and sectional curvature"]
        T15["Connection along immersions (incl. curves)"]
        T16["Existence and uniqueness of parallel transport"]

        T2-->T13.1
        T10-->T13.1
        T18-->T13.1
        T17-->T18-->T11.1-->T13
        T13.1-->T13
        T17-->T10
        T17-->T11-->T14
        T13-->T14
        T10-->T15-->T16
    end

    T1-->T10
    T12-->T13

    subgraph "Geodesics"
        T30["Define a geodesic (c'' = 0)"]
        T31["Existence and uniqueness of geodesics"]
        T32["Define exponential map"]
        T33["Define Energy functional"]
        T40["Variations and variation vector fields"]
        T34["Geodesics minimize the energy functional and length"]
        T35["Geodesic distance is metric"]

        T15-->T30
        T3-->T33

        T30-->T31-->T32
        T13-->T34
        T30-->T34
        T40-->T34
        T33-->T34-->T35
    end

    subgraph "Jacobi"
        T41["Jacobi formula"]
        T42["Estimations of Jacobi fields when curvature is bounded"]
        T43["Estimations for conjugate radius"]

        T30-->T41
        T40-->T41-->T42-->T43
    end

    subgraph "Differential forms"
        T50["Exterior products of vector bundles"]
        T51["Differential forms"]
        T52["Exterior derivative"]
        T53["de Rham cohomology"]

        T1-->T50
        T50-->T51-->T52-->T53
    end



```