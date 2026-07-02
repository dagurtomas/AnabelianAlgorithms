/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Examples.MochizukiThm.PadicLocalField
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Structure-sheaf cohomology used by the curve package

This file contains the small amount of extracted structure-sheaf cohomology API needed to define
the arithmetic genus of a curve over a `p`-adic local field object.  The construction keeps the
`R`-module structure on cohomology explicit by transporting scalar multiplication through the
underlying abelian sheaf.
-/

@[expose] public section

universe u uG

namespace Anabelian
namespace Examples
namespace MochizukiLocalProP
namespace ProperHyperbolicCurveHomStandalone

open CategoryTheory
open AlgebraicGeometry
open Opposite

/-! ## Structure-sheaf cohomology and arithmetic genus -/

namespace ExtractedStructureSheafCohomology

universe w' w v

namespace LinearSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Type w) [CommRing R]
variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Forget a sheaf of `R`-modules to its underlying abelian sheaf. -/
abbrev underlyingAdditiveSheaf (F : Sheaf J (ModuleCat.{w} R)) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F

namespace HModule

variable {R}

/-- The endomorphism of the underlying abelian sheaf given by scalar multiplication by `r`. -/
noncomputable def scalarEnd (F : Sheaf J (ModuleCat.{w} R)) (r : R) :
    underlyingAdditiveSheaf R F ⟶ underlyingAdditiveSheaf R F where
  hom :=
    { app U := AddCommGrpCat.ofHom ((LinearMap.lsmul R (F.obj.obj U) r).toAddMonoidHom)
      naturality := by
        intro U V i
        ext x
        let x' : F.obj.obj U := x
        let y' : F.obj.obj V := (F.obj.map i).hom x'
        change r • y' = (F.obj.map i).hom (r • x')
        exact ((F.obj.map i).hom.map_smul r x').symm }

@[simp]
lemma scalarEnd_zero (F : Sheaf J (ModuleCat.{w} R)) :
    scalarEnd (R := R) F 0 = 0 := by
  ext U x
  let x' : F.obj.obj U := x
  change (0 : R) • x' = 0
  simp

@[simp]
lemma scalarEnd_one (F : Sheaf J (ModuleCat.{w} R)) :
    scalarEnd (R := R) F 1 = 𝟙 _ := by
  ext U x
  let x' : F.obj.obj U := x
  change (1 : R) • x' = x'
  simp

@[simp]
lemma scalarEnd_add (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalarEnd (R := R) F (r + s) = scalarEnd (R := R) F r + scalarEnd (R := R) F s := by
  ext U x
  let x' : F.obj.obj U := x
  change (r + s) • x' = r • x' + s • x'
  simp [add_smul]

@[simp]
lemma scalarEnd_mul (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalarEnd (R := R) F (r * s) = scalarEnd (R := R) F s ≫ scalarEnd (R := R) F r := by
  ext U x
  let x' : F.obj.obj U := x
  change (r * s) • x' = r • s • x'
  rw [mul_smul]

end HModule

section Cohomology

variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The type underlying `R`-linear sheaf cohomology.

This is the cohomology of the underlying abelian sheaf, equipped below with the `R`-module
structure induced by scalar multiplication on the coefficient sheaf. -/
abbrev HModuleType (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) : Type w' :=
  (underlyingAdditiveSheaf R F).H n

namespace HModule

variable {R}

noncomputable instance instModuleHModuleType (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    Module R (HModuleType R F n) where
  smul r x := CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n x
  one_smul x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F 1) n x = x
    rw [scalarEnd_one]
    simp
  mul_smul r s x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F (r * s)) n x =
      CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n
        (CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F s) n x)
    rw [scalarEnd_mul]
    simp [CategoryTheory.Sheaf.H.map_comp_apply]
  smul_zero r := map_zero _
  zero_smul x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F 0) n x = 0
    rw [scalarEnd_zero]
    simp [CategoryTheory.Sheaf.H.map_apply]
  add_smul r s x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F (r + s)) n x =
      CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n x +
        CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F s) n x
    rw [scalarEnd_add]
    simp [CategoryTheory.Sheaf.H.map_add_apply]
  smul_add r x y := map_add _ x y

end HModule

/-- `R`-linear sheaf cohomology as an object of `ModuleCat R`. -/
noncomputable def HModule (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) : ModuleCat.{w'} R :=
  ModuleCat.of R (HModuleType R F n)

end Cohomology

end LinearSheaf

/-- The map from the base ring to sections of the structure sheaf over an open set of `X`, induced
by a morphism `X ⟶ Spec R`. -/
noncomputable def structureSheafToOpen (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (U : X.Opens) : CommRingCat.of R ⟶ X.presheaf.obj (.op U) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)

/-- The corresponding algebra map on sections of the structure sheaf over an open set. -/
noncomputable def structureSheafAlgebraMap (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (U : X.Opens) : R →+* X.presheaf.obj (.op U) :=
  (structureSheafToOpen R X f U).hom

@[reassoc (attr := simp)]
lemma structureSheafToOpen_naturality (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    structureSheafToOpen R X f U.unop ≫ X.presheaf.map i =
      structureSheafToOpen R X f V.unop := by
  dsimp [structureSheafToOpen]
  rw [Category.assoc, f.appLE_map]

/-- The structure presheaf of a scheme over `Spec R`, valued in `ModuleCat R`. -/
noncomputable def structureSheafModulePresheaf (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U :=
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    ModuleCat.of R (X.presheaf.obj U)
  map {U V} i := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj V) := (structureSheafAlgebraMap R X f V.unop).toAlgebra
    exact ModuleCat.ofHom
      { toFun := (X.presheaf.map i).hom
        map_add' := map_add _
        map_smul' := by
          intro r x
          change (X.presheaf.map i).hom ((structureSheafAlgebraMap R X f U.unop) r * x) =
            (structureSheafAlgebraMap R X f V.unop) r * (X.presheaf.map i).hom x
          rw [map_mul]
          congr 1
          have h := congr_arg (fun e : CommRingCat.of R ⟶ X.presheaf.obj V => e.hom r)
            (structureSheafToOpen_naturality R X f i)
          simpa only [structureSheafAlgebraMap, CommRingCat.hom_comp, RingHom.coe_comp,
            Function.comp_apply] using h }
  map_id U := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.presheaf.map (𝟙 U)).hom x = x
    simp
  map_comp {U V W} i j := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj V) := (structureSheafAlgebraMap R X f V.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj W) := (structureSheafAlgebraMap R X f W.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.presheaf.map (i ≫ j)).hom x =
      (X.presheaf.map j).hom ((X.presheaf.map i).hom x)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using
      congr_arg (fun e : X.presheaf.obj U ⟶ X.presheaf.obj W => e.hom x)
        (X.presheaf.map_comp i j)

/-- Forgetting the `R`-module structure on `structureSheafModulePresheaf` recovers the underlying
presheaf of types of the usual structure sheaf. -/
noncomputable def structureSheafModulePresheafForgetIso (R : Type u) [CommRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) :
    structureSheafModulePresheaf R X f ⋙ CategoryTheory.forget (ModuleCat.{u} R) ≅
      X.presheaf ⋙ CategoryTheory.forget CommRingCat.{u} :=
  Iso.refl _

/-- The structure sheaf of a scheme over `Spec R`, regarded as a sheaf of `R`-modules. -/
noncomputable def structureSheafModule (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) where
  obj := structureSheafModulePresheaf R X f
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X)
      (structureSheafModulePresheaf R X f) (CategoryTheory.forget (ModuleCat.{u} R))]
    exact (Presheaf.isSheaf_of_iso_iff (J := Opens.grothendieckTopology X)
      (structureSheafModulePresheafForgetIso R X f)).mpr
      ((Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X) X.presheaf
        (CategoryTheory.forget CommRingCat.{u})).mp X.sheaf.property)

/-- Cohomology of the structure sheaf of a scheme over `Spec R`, with its natural `R`-module
structure. -/
noncomputable def structureSheafCohomologyModule (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R))
    [(Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (n : ℕ) : ModuleCat.{w'} R :=
  LinearSheaf.HModule R (structureSheafModule R X f) n

end ExtractedStructureSheafCohomology

/-- The structure-sheaf cohomology group `H^i(X, 𝒪_X)` of a scheme over a `p`-adic local field. -/
noncomputable abbrev structureSheafCohomology {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) (i : ℕ) : Type u :=
  ExtractedStructureSheafCohomology.structureSheafCohomologyModule K X.left X.hom i

namespace StructureSheafCohomology

/-- Coherent cohomology finiteness for the structure sheaf of a proper scheme over a field. -/
@[instance] axiom finiteDimensional_of_proper {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom] (i : ℕ) :
    FiniteDimensional K (structureSheafCohomology K X i)

end StructureSheafCohomology

/-- The dimension `dim_K H^i(X, 𝒪_X)`, available for proper schemes over `K`. -/
noncomputable def structureSheafCohomologyRank {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom]
    (i : ℕ) : ℕ :=
  Module.finrank K (structureSheafCohomology K X i)

/-- For curves, the arithmetic genus is `dim_K H¹(X, 𝒪_X)`. -/
noncomputable def curveArithmeticGenus {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom] : ℕ :=
  structureSheafCohomologyRank K X 1

end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
