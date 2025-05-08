import Mathlib.Topology.VectorBundle.Basic

variable
  (R : Type*) [NontriviallyNormedField R]
  (F : Type*) [AddCommMonoid F] [Module R F]

noncomputable section



structure Tensor (i_cov i_contra : Nat)
  extends MultilinearMap R (fun _ : Fin i_cov => F) R


#check Tensor R F 2 3
variable
  (v v₁ v₂ : F)
  (T : Tensor R F 2 0)
  (f : MultilinearMap R (fun _ : Fin 3 => F) R)


#check f
#check f (fun _ : Fin 3 => v)
#check f ![v, v₁, v₂]

#check T.toFun (fun _ : Fin 2 => v)
#check T.toFun ![v, v₁]
-- #check T ![v, v₁]


end




open Bundle

variable
  {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace R F]
  (E : B → Type*)
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)]
  [∀ x, Module R (E x)]
  (ι : Type*)

#check VectorBundleCore


structure TensorBundleCore (i j : Nat) extends VectorBundleCore R B (Tensor R F i j) ι

-- Ersetze F durch Multilinear (f)
def tensorBundleCore : VectorBundleCore R B F (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.uniqueDiffWithinAt_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hx]
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simp; infer_instance
    refine (contDiffOn_fderiv_coord_change (n := 0) i j).continuousOn.comp
      (i.1.continuousOn_extend.mono ?_) ?_
    · rw [i.1.extend_source]; exact inter_subset_left
    simp_rw [← i.1.extend_image_source_inter, mapsTo_image]
  coordChange_comp := by
    have : IsManifold I (0 + 1) M := by simp; infer_instance
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds (I := I) hxi (j.1.extend_source_mem_nhds (I := I) hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hxi, j.1.extend_left_inv hxj]
    · exact (contDiffWithinAt_extend_coord_change' (subset_maximalAtlas k.2)
        (subset_maximalAtlas j.2) hxk hxj).differentiableWithinAt le_rfl
    · exact (contDiffWithinAt_extend_coord_change' (subset_maximalAtlas j.2)
        (subset_maximalAtlas i.2) hxj hxi).differentiableWithinAt le_rfl
    · intro x _; exact mem_range_self _
    · exact I.uniqueDiffWithinAt_image
    · rw [Function.comp_apply, i.1.extend_left_inv hxi]


instance : TopologicalSpace TM :=
  (tangentTensorBundleCore).toTopologicalSpace

instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).fiberBundle

instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).vectorBundle
