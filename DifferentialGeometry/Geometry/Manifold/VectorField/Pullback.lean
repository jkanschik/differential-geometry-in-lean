import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

import Mathlib.Geometry.Manifold.VectorField.Pullback


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


open ContinuousLinearMap

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}
variable {c : 𝕜} {m n : WithTop ℕ∞} {t : Set M'} {y₀ : M'}
variable {g : M' → 𝕜}



/-
  -----------------------------------------------------------------------
  Propose changes start here
  -----------------------------------------------------------------------
-/


lemma mpullbackWithin_fmul :
    mpullbackWithin I I' f (fun y => g y • V y) s =
      (fun y => (g ∘ f) y • (mpullbackWithin I I' f V s) y) := by
  ext x
  simp [mpullbackWithin_apply]






end VectorField

end
