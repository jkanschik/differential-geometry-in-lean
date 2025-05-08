import Mathlib.Analysis.Calculus.VectorField


noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}


namespace VectorField

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracketWithin_fmul_right {f : E → 𝕜}
    (hf : DifferentiableWithinAt 𝕜 f s x)
    (hW : DifferentiableWithinAt 𝕜 W s x)
    (hs: UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (fun y => f y • W y) s x =
      (fderivWithin 𝕜 f s x) (V x) • (W x)  + (f • lieBracketWithin 𝕜 V W s) x := by
  simp [lieBracketWithin, fderivWithin_smul hs hf hW, smul_sub, add_comm, add_sub_assoc]

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracket_fmul_right {f : E → 𝕜}
    (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y => f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x)  + (f • lieBracket 𝕜 V W) x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hf ⊢
  rw [fderiv]
  exact lieBracketWithin_fmul_right hf hW uniqueDiffWithinAt_univ

end VectorField


end

