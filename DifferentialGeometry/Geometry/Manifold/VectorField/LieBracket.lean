import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorField.Pullback

import Mathlib.Geometry.Manifold.VectorField.LieBracket
import DifferentialGeometry.Analysis.Calculus.VectorField
import DifferentialGeometry.Geometry.Manifold.VectorField.Pullback


open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

namespace VectorField

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}
variable [IsManifold I 2 M] [CompleteSpace E]



/-
  -----------------------------------------------------------------------
  Propose changes start here
  -----------------------------------------------------------------------
-/



theorem mlieBracketWithinAt_fmul_right
  {f : M → 𝕜}
  (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
  (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
  (hf : ContMDiffWithinAt I 𝓘(𝕜, 𝕜) (minSmoothness 𝕜 2) f s x)
  (hs : UniqueMDiffWithinAt I s x) :

  mlieBracketWithin I V (fun y => f y • W y) s x =
    (mfderivWithin I 𝓘(𝕜, 𝕜) f s x) (V x) • (W x)  + (f • mlieBracketWithin I V W s) x := by

  simp only [mlieBracketWithin_apply]
  rw [mpullbackWithin_fmul]

  -- The function f in the preferred chart is differentiable:
  have hfc : DifferentiableWithinAt 𝕜
      (f ∘ ↑(extChartAt I x).symm)
      (↑(extChartAt I x).symm ⁻¹' s ∩ range ↑I)
      ((extChartAt I x) x) := by
    have hf' : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) (minSmoothness 𝕜 2) (f ∘ ↑(extChartAt I x).symm)  (↑(extChartAt I x).symm ⁻¹' s ∩ range ↑I) ((extChartAt I x) x) := by
      sorry
    apply hf'.contDiffWithinAt.differentiableWithinAt
    sorry
  -- The vector field W in the preferred chart is differentiable:
  have hWc : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (↑(extChartAt I x).symm) W (range ↑I))
      (↑(extChartAt I x).symm ⁻¹' s ∩ range ↑I)
      ((extChartAt I x) x) := by
    exact hW.differentiableWithinAt_mpullbackWithin_vectorField
  -- On the set in E, the differentials are unique
  have hsc : UniqueDiffWithinAt 𝕜 (↑(extChartAt I x).symm ⁻¹' s ∩ range ↑I)
      ((extChartAt I x) x) := by
      exact uniqueMDiffWithinAt_iff_inter_range.1 hs


  rw [lieBracketWithin_fmul_right hfc hWc hsc]
  rw [ContinuousLinearMap.map_add]

  sorry

end VectorField

end
