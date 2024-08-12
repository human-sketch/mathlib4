/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Convex functions are continuous

This file proves that convex functions from a finite dimensional real normed space are locally
lipschitz, in particular continuous.
-/

open AffineBasis FiniteDimensional Metric Set
open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ}
  {s : Set E} {x : E}

protected lemma ConvexOn.locallyLipschitzOn (hf : ConvexOn ℝ s f) :
    LocallyLipschitzOn (intrinsicInterior ℝ s) f := by
  classical
  simp only [LocallyLipschitzOn, mem_intrinsicInterior, coe_affineSpan, Subtype.exists,
    exists_and_right, exists_eq_right, forall_exists_index]
  rintro x hx hx'
  -- obtain ⟨t, ht⟩ := exists_mem_interior_convexHull_affineBasis $ mem_interior_iff_mem_nhds.1 hx'

  -- simp only [mem_intrinsicInterior, coe_affineSpan, Subtype.exists, exists_and_right,
  --   exists_eq_right] at hx
  -- refine isOpen_interior.continuousOn_iff.2 (fun x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := isOpen_interior.exists_mem_interior_convexHull_finset hx,
  -- set M := t.sup' (convexHull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (fun ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convexHull
  --   (hf.subset (hts.trans interior_subset) $ convex_convexHull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, fun y hy, _⟩,
  sorry

protected lemma ConcaveOn.locallyLipschitzOn (hf : ConcaveOn ℝ s f) :
    LocallyLipschitzOn (intrinsicInterior ℝ s) f := by simpa using hf.neg.locallyLipschitzOn

protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn

protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn

protected lemma ConvexOn.continuousOn (hf : ConvexOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := hf.locallyLipschitzOn.continuousOn

protected lemma ConcaveOn.continuousOn (hf : ConcaveOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := hf.locallyLipschitzOn.continuousOn

protected lemma ConvexOn.continuous (hf : ConvexOn ℝ univ f) : Continuous f :=
  hf.locallyLipschitz.continuous

protected lemma ConcaveOn.continuous (hf : ConcaveOn ℝ univ f) : Continuous f :=
  hf.locallyLipschitz.continuous
