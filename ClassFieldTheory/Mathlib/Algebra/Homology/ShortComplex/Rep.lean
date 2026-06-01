/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Rep.Iso

public section

universe w w' u u' v v'

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G] {A : Rep.{w} k G}

open CategoryTheory ShortComplex ShortExact Limits

-- instance : HasForget₂ (Rep.{w} k G) Ab where
--   forget₂ := forget₂ (Rep k G) (ModuleCat k) ⋙ (forget₂ _ _)

-- instance : (forget₂ (Rep.{w} k G) Ab).Additive := ⟨rfl⟩

-- `compNatIso'` (a workaround for mathlib's `compNatIso` needing `Functor.IsEquivalence`)
-- was removed during the v4.31 bump: it is unused elsewhere in CFT, and its
-- `NatIso.ofComponents` naturality no longer elaborates cleanly under v4.31.

attribute [local instance] Functor.PreservesHomology.preservesKernel
  Functor.PreservesHomology.preservesCokernel in
instance CategoryTheory.Functor.PreservesHomology.comp {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [hF : F.PreservesHomology] (G : D ⥤ E) [G.PreservesZeroMorphisms]
    [hG : G.PreservesHomology] :
    PreservesHomology (F ⋙ G) where
  preservesKernels _ _ _ :=
    ⟨fun hc ↦ ⟨(KernelFork.isLimitMapConeEquiv _ _).2
      (KernelFork.mapIsLimit _ (KernelFork.mapIsLimit _ hc F) G)⟩⟩
  preservesCokernels _ _ _ :=
    ⟨fun hc ↦ ⟨(CokernelCofork.isColimitMapCoconeEquiv _ _).2
      (CokernelCofork.mapIsColimit _ (CokernelCofork.mapIsColimit _ hc F) G)⟩⟩

lemma CategoryTheory.ShortComplex.rep_exact_iff {S : ShortComplex (Rep.{w} k G)} :
    S.Exact ↔ S.g.hom.ker ≤ S.f.hom.range := by
  rw [← exact_map_iff_of_faithful (F := forget₂ (Rep k G) (ModuleCat k)),
    CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
  rfl

lemma CategoryTheory.ShortComplex.ShortExact.rep_exact_iff_function_exact
    {S : ShortComplex (Rep.{w} k G)} : S.Exact ↔ Function.Exact S.f S.g := by
  rw [← exact_map_iff_of_faithful (F := forget₂ _ (ModuleCat k)),
    moduleCat_exact_iff_function_exact]
  rfl
