module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

@[expose] public noncomputable section

namespace CategoryTheory.ShortComplex
open Abelian
open Limits hiding im

variable {C D : Type*} [Category C] [Category D]

section Abelian
variable [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
to the coimage of the second map.

Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
def kerIsoIm (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ gFunctor ⋙ ker C ≅ F ⋙ fFunctor ⋙ im :=
  NatIso.ofComponents
    (fun X ↦
      have := (hF X).mono_cokernelDesc
      kernel.congr _ _ (by
        show (F.obj X).g = cokernel.π (F.obj X).f ≫ cokernel.desc (F.obj X).f (F.obj X).g (F.obj X).zero
        simp) ≪≫
        kernelCompMono _ (cokernel.desc (F.obj X).f (F.obj X).g (F.obj X).zero))
    (by intro X Y f; apply equalizer.hom_ext; simp)

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
to the coimage of the second map.

Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
def cokerIsoCoim (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ fFunctor ⋙ coker C ≅ F ⋙ gFunctor ⋙ coim :=
  NatIso.ofComponents
    (fun X ↦
      have := (hF X).epi_kernelLift
      cokernel.congr _ _ (by
        show (F.obj X).f = kernel.lift (F.obj X).g (F.obj X).f (F.obj X).zero ≫ kernel.ι (F.obj X).g
        simp [kernel.lift_ι]) ≪≫
        cokernelEpiComp (kernel.lift (F.obj X).g (F.obj X).f (F.obj X).zero) _)
    (by intro X Y f; apply coequalizer.hom_ext; simp)

end Abelian
end CategoryTheory.ShortComplex
