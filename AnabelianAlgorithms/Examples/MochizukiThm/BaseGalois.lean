/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianAlgorithms.Examples.MochizukiThm.FromPi1.FundamentalGroup.Galois
import Mathlib

/-!
# Base Galois action on finite étale fibers

This file constructs the scheme-level action of `Gal(Ω/K)` on the finite-étale fiber functor over
`Spec K`.  The convention is the one needed for `CategoryTheory.Aut` multiplication: because
`Spec` is contravariant, the fiber map attached to `σ` uses the scheme automorphism induced by
`σ⁻¹`, and `fiberSchemeMap (σ * τ) = fiberSchemeMap τ ≫ fiberSchemeMap σ`.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits TensorProduct
open scoped CategoryTheory.PreGaloisCategory IntermediateField

universe u

namespace AlgebraicGeometry
namespace FiniteEtale

variable (K : Type u) [Field K]
variable (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The automorphism of `Spec Ω` induced contravariantly by a `K`-algebra automorphism of `Ω`. -/
noncomputable def specAutIso (σ : Gal(Ω/K)) : Spec (.of Ω) ≅ Spec (.of Ω) :=
  Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op

@[simp]
lemma specAutIso_one : (specAutIso K Ω 1).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (1 : Gal(Ω/K)).toRingEquiv.toRingHom) = 𝟙 _
  rw [← Spec.map_id]
  congr 1

@[simp]
lemma specAutIso_mul (σ τ : Gal(Ω/K)) :
    (specAutIso K Ω (σ * τ)).hom =
      (specAutIso K Ω σ).hom ≫ (specAutIso K Ω τ).hom := by
  change Spec.map (CommRingCat.ofHom (σ * τ).toRingEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom τ.toRingEquiv.toRingHom)
  rw [← Spec.map_comp]
  congr 1

@[simp]
lemma specAutIso_hom_inv (σ : Gal(Ω/K)) :
    (specAutIso K Ω σ).hom ≫ (specAutIso K Ω σ⁻¹).hom = 𝟙 _ := by
  rw [← specAutIso_mul, mul_inv_cancel, specAutIso_one]

@[simp]
lemma specAutIso_inv_hom (σ : Gal(Ω/K)) :
    (specAutIso K Ω σ⁻¹).hom ≫ (specAutIso K Ω σ).hom = 𝟙 _ := by
  rw [← specAutIso_mul, inv_mul_cancel, specAutIso_one]

lemma specAut_hom_comp_base (σ : Gal(Ω/K)) :
    (specAutIso K Ω σ).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  change Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = _
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The geometric point `Spec Ω ⟶ Spec K` induced by the `K`-algebra structure on `Ω`. -/
abbrev baseGeom : Spec (.of Ω) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- The action map on the scheme underlying the pulled-back finite étale cover.

The map for `σ` uses `(specAutIso K Ω σ⁻¹).hom`, because `Spec` is contravariant. -/
noncomputable def fiberSchemeMap (σ : Gal(Ω/K)) (A : FiniteEtale (Spec (.of K))) :
    ((FiniteEtale.pullback (baseGeom K Ω)).obj A).left ⟶
      ((FiniteEtale.pullback (baseGeom K Ω)).obj A).left :=
  pullback.lift
    (pullback.fst A.hom (baseGeom K Ω))
    (pullback.snd A.hom (baseGeom K Ω) ≫ (specAutIso K Ω σ⁻¹).hom)
    (by
      rw [Category.assoc]
      change pullback.fst A.hom (baseGeom K Ω) ≫ A.hom =
        pullback.snd A.hom (baseGeom K Ω) ≫
          ((specAutIso K Ω σ⁻¹).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      rw [specAut_hom_comp_base]
      exact pullback.condition)

lemma fiberSchemeMap_comp_inv (σ : Gal(Ω/K)) (A : FiniteEtale (Spec (.of K))) :
    fiberSchemeMap K Ω σ A ≫ fiberSchemeMap K Ω σ⁻¹ A = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [fiberSchemeMap]
  · simp [fiberSchemeMap, Category.assoc]

lemma fiberSchemeMap_inv_comp (σ : Gal(Ω/K)) (A : FiniteEtale (Spec (.of K))) :
    fiberSchemeMap K Ω σ⁻¹ A ≫ fiberSchemeMap K Ω σ A = 𝟙 _ := by
  simpa using fiberSchemeMap_comp_inv K Ω σ⁻¹ A

/-- The permutation of a finite étale fiber induced by `σ : Gal(Ω/K)`. -/
noncomputable def fiberSchemeEquiv (σ : Gal(Ω/K)) (A : FiniteEtale (Spec (.of K))) :
    ((FiniteEtale.fiber (baseGeom K Ω)).obj A) ≃
      ((FiniteEtale.fiber (baseGeom K Ω)).obj A) where
  toFun x := fiberSchemeMap K Ω σ A x
  invFun x := fiberSchemeMap K Ω σ⁻¹ A x
  left_inv := by
    intro x
    change (fiberSchemeMap K Ω σ A ≫ fiberSchemeMap K Ω σ⁻¹ A).base x = x
    rw [fiberSchemeMap_comp_inv]
    rfl
  right_inv := by
    intro x
    change (fiberSchemeMap K Ω σ⁻¹ A ≫ fiberSchemeMap K Ω σ A).base x = x
    rw [fiberSchemeMap_inv_comp]
    rfl

lemma pullbackMap_fiberSchemeMap (σ : Gal(Ω/K)) {A B : FiniteEtale (Spec (.of K))}
    (f : A ⟶ B) :
    ((FiniteEtale.pullback (baseGeom K Ω)).map f).left ≫ fiberSchemeMap K Ω σ B =
      fiberSchemeMap K Ω σ A ≫ ((FiniteEtale.pullback (baseGeom K Ω)).map f).left := by
  apply pullback.hom_ext
  · simp [fiberSchemeMap, FiniteEtale.pullback]
  · simp [fiberSchemeMap, FiniteEtale.pullback, Category.assoc]

/-- The natural automorphism of the finite-étale fiber functor induced by a Galois element. -/
noncomputable def galToSchemeFiberAut (σ : Gal(Ω/K)) :
    Aut (FiniteEtale.fiber (baseGeom K Ω)) :=
  NatIso.ofComponents
    (fun A ↦ FintypeCat.equivEquivIso (fiberSchemeEquiv K Ω σ A))
    (fun {A B} f ↦ by
      ext x
      change (((FiniteEtale.pullback (baseGeom K Ω)).map f).left ≫
          fiberSchemeMap K Ω σ B).base x =
        (fiberSchemeMap K Ω σ A ≫ ((FiniteEtale.pullback (baseGeom K Ω)).map f).left).base x
      exact congrArg (fun g : ((FiniteEtale.pullback (baseGeom K Ω)).obj A).left ⟶
          ((FiniteEtale.pullback (baseGeom K Ω)).obj B).left ↦ g.base x)
        (pullbackMap_fiberSchemeMap K Ω σ f))

lemma fiberSchemeMap_one (A : FiniteEtale (Spec (.of K))) :
    fiberSchemeMap K Ω 1 A = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [fiberSchemeMap]
  · simp [fiberSchemeMap]

lemma fiberSchemeMap_mul (σ τ : Gal(Ω/K)) (A : FiniteEtale (Spec (.of K))) :
    fiberSchemeMap K Ω (σ * τ) A = fiberSchemeMap K Ω τ A ≫ fiberSchemeMap K Ω σ A := by
  apply pullback.hom_ext
  · simp [fiberSchemeMap]
  · simp [fiberSchemeMap, Category.assoc]

/-- The scheme-level Galois action on the finite-étale fiber functor, as a monoid homomorphism. -/
noncomputable def galToSchemeFiberAutHom :
    Gal(Ω/K) →* Aut (FiniteEtale.fiber (baseGeom K Ω)) where
  toFun := galToSchemeFiberAut K Ω
  map_one' := by
    ext A x
    change fiberSchemeMap K Ω 1 A x = x
    rw [fiberSchemeMap_one]
    rfl
  map_mul' σ τ := by
    ext A x
    simp [galToSchemeFiberAut, fiberSchemeEquiv, fiberSchemeMap_mul, Aut.Aut_mul_def]

/-- The action of `Gal(Ω/K)` on each scheme-level finite-étale fiber over `Spec K`. -/
noncomputable instance galFiberMulAction (A : FiniteEtale (Spec (.of K))) :
    MulAction Gal(Ω/K) ((FiniteEtale.fiber (baseGeom K Ω)).obj A) :=
  MulAction.compHom _ (galToSchemeFiberAutHom K Ω)

@[simp]
lemma galToSchemeFiberAutHom_hom_app_apply (σ : Gal(Ω/K))
    (A : FiniteEtale (Spec (.of K)))
    (x : (FiniteEtale.fiber (baseGeom K Ω)).obj A) :
    (galToSchemeFiberAutHom K Ω σ).hom.app A x = σ • x :=
  rfl

/-- The Galois action on finite-étale fibers is natural in scheme-level finite-étale covers. -/
instance galFiberIsNaturalSMul :
    CategoryTheory.PreGaloisCategory.IsNaturalSMul
      (FiniteEtale.fiber (baseGeom K Ω)) Gal(Ω/K) where
  naturality σ _ _ f x := by
    change (FiniteEtale.fiber (baseGeom K Ω)).map f
        ((galToSchemeFiberAutHom K Ω σ).hom.app _ x) =
      (galToSchemeFiberAutHom K Ω σ).hom.app _
        ((FiniteEtale.fiber (baseGeom K Ω)).map f x)
    exact (NatTrans.naturality_apply (galToSchemeFiberAutHom K Ω σ).hom f x).symm

/-- The finite-étale `K`-scheme associated to a finite étale `K`-algebra. -/
noncomputable def specObj (S : CommAlgCat.FiniteEtale K) :
    FiniteEtale (Spec (.of K)) := by
  letI : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K S.obj))) := by
    rw [AlgebraicGeometry.IsFiniteEtale.SpecMap_iff]
    change RingHom.FiniteEtale (algebraMap K S.obj)
    rw [RingHom.FiniteEtale.iff_finite_and_etale]
    exact ⟨RingHom.etale_algebraMap.mpr inferInstance,
      RingHom.finite_algebraMap.mpr inferInstance⟩
  exact FiniteEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap K S.obj)))

/-- The pullback of `Spec S` to `Ω`, identified with `Spec (Ω ⊗[K] S)`. -/
noncomputable def specPullbackIso (S : CommAlgCat.FiniteEtale K) :
    ((FiniteEtale.pullback (baseGeom K Ω)).obj (specObj K S)).left ≅
      Spec (.of (TensorProduct K Ω S.obj)) :=
  pullbackSymmetry _ _ ≪≫ AlgebraicGeometry.pullbackSpecIso K Ω S.obj

/-- The tensor-product automorphism induced by acting on the `Ω` factor. -/
noncomputable def tensorGalAlgEquiv (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K)) :
    TensorProduct K Ω S.obj ≃ₐ[K] TensorProduct K Ω S.obj :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : S.obj ≃ₐ[K] S.obj)

@[simp]
lemma tensorGalAlgEquiv_tmul (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K))
    (a : Ω) (s : S.obj) :
    tensorGalAlgEquiv K Ω S σ (a ⊗ₜ[K] s) = σ a ⊗ₜ[K] s := by
  simp [tensorGalAlgEquiv, Algebra.TensorProduct.congr_apply]

lemma tensorGalAlgEquiv_includeLeft (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K)) :
    (tensorGalAlgEquiv K Ω S σ).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      Algebra.TensorProduct.includeLeftRingHom.comp σ.toRingEquiv.toRingHom := by
  ext a
  change tensorGalAlgEquiv K Ω S σ (a ⊗ₜ[K] (1 : S.obj)) = σ a ⊗ₜ[K] (1 : S.obj)
  simp

lemma tensorGalAlgEquiv_includeRight (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K)) :
    (tensorGalAlgEquiv K Ω S σ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj).toRingHom =
      (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj).toRingHom := by
  ext s
  change tensorGalAlgEquiv K Ω S σ ((1 : Ω) ⊗ₜ[K] s) = (1 : Ω) ⊗ₜ[K] s
  simp

lemma specPullbackIso_hom_includeLeft (S : CommAlgCat.FiniteEtale K) :
    (specPullbackIso K Ω S).hom ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      pullback.snd (specObj K S).hom (baseGeom K Ω) := by
  calc
    (specPullbackIso K Ω S).hom ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
        = (pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).hom ≫
          ((AlgebraicGeometry.pullbackSpecIso K Ω S.obj).hom ≫
            Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) := by
          rw [specPullbackIso, Iso.trans_hom, Category.assoc]
    _ = (pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).hom ≫
          pullback.fst (baseGeom K Ω) (specObj K S).hom := by
          rw [AlgebraicGeometry.pullbackSpecIso_hom_fst]
          rfl
    _ = pullback.snd (specObj K S).hom (baseGeom K Ω) := by
          rw [pullbackSymmetry_hom_comp_fst]

lemma specPullbackIso_hom_includeRight (S : CommAlgCat.FiniteEtale K) :
    (specPullbackIso K Ω S).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj)) =
      pullback.fst (specObj K S).hom (baseGeom K Ω) := by
  calc
    (specPullbackIso K Ω S).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj))
        = (pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).hom ≫
          ((AlgebraicGeometry.pullbackSpecIso K Ω S.obj).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj))) := by
          rw [specPullbackIso, Iso.trans_hom, Category.assoc]
    _ = (pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).hom ≫
          pullback.snd (baseGeom K Ω) (specObj K S).hom := by
          rw [AlgebraicGeometry.pullbackSpecIso_hom_snd]
          rfl
    _ = pullback.fst (specObj K S).hom (baseGeom K Ω) := by
          rw [pullbackSymmetry_hom_comp_snd]

lemma specPullbackIso_inv_fst (S : CommAlgCat.FiniteEtale K) :
    (specPullbackIso K Ω S).inv ≫ pullback.fst (specObj K S).hom (baseGeom K Ω) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj)) := by
  calc
    (specPullbackIso K Ω S).inv ≫ pullback.fst (specObj K S).hom (baseGeom K Ω)
        = (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
          ((pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).inv ≫
            pullback.fst (specObj K S).hom (baseGeom K Ω)) := by
          rw [specPullbackIso, Iso.trans_inv, Category.assoc]
    _ = (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
          pullback.snd (baseGeom K Ω) (specObj K S).hom := by
          rw [pullbackSymmetry_inv_comp_fst]
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj)) := by
          change (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
              pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
                (Spec.map (CommRingCat.ofHom (algebraMap K S.obj))) = _
          rw [AlgebraicGeometry.pullbackSpecIso_inv_snd]

lemma specPullbackIso_inv_snd (S : CommAlgCat.FiniteEtale K) :
    (specPullbackIso K Ω S).inv ≫ pullback.snd (specObj K S).hom (baseGeom K Ω) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
  calc
    (specPullbackIso K Ω S).inv ≫ pullback.snd (specObj K S).hom (baseGeom K Ω)
        = (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
          ((pullbackSymmetry (specObj K S).hom (baseGeom K Ω)).inv ≫
            pullback.snd (specObj K S).hom (baseGeom K Ω)) := by
          rw [specPullbackIso, Iso.trans_inv, Category.assoc]
    _ = (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
          pullback.fst (baseGeom K Ω) (specObj K S).hom := by
          rw [pullbackSymmetry_inv_comp_snd]
    _ = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
          change (AlgebraicGeometry.pullbackSpecIso K Ω S.obj).inv ≫
              pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
                (Spec.map (CommRingCat.ofHom (algebraMap K S.obj))) = _
          rw [AlgebraicGeometry.pullbackSpecIso_inv_fst]

/-- Under `Spec (Ω ⊗[K] S)`, the BG1 scheme action is the prime-spectrum map induced by
`σ⁻¹` on the `Ω` tensor factor. -/
lemma specPullbackIso_fiberSchemeMap (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K)) :
    fiberSchemeMap K Ω σ (specObj K S) ≫ (specPullbackIso K Ω S).hom =
      (specPullbackIso K Ω S).hom ≫
        Spec.map (CommRingCat.ofHom (tensorGalAlgEquiv K Ω S σ⁻¹).toRingHom) := by
  rw [← cancel_mono (specPullbackIso K Ω S).inv]
  apply pullback.hom_ext
  · calc
      ((fiberSchemeMap K Ω σ (specObj K S) ≫ (specPullbackIso K Ω S).hom) ≫
          (specPullbackIso K Ω S).inv) ≫ pullback.fst (specObj K S).hom (baseGeom K Ω)
          = fiberSchemeMap K Ω σ (specObj K S) ≫
              pullback.fst (specObj K S).hom (baseGeom K Ω) := by
            simp [Category.assoc]
      _ = pullback.fst (specObj K S).hom (baseGeom K Ω) := by
            simp [fiberSchemeMap]
      _ = (((specPullbackIso K Ω S).hom ≫
              Spec.map (CommRingCat.ofHom (tensorGalAlgEquiv K Ω S σ⁻¹).toRingHom)) ≫
              (specPullbackIso K Ω S).inv) ≫
            pullback.fst (specObj K S).hom (baseGeom K Ω) := by
            rw [Category.assoc]
            rw [specPullbackIso_inv_fst]
            rw [Category.assoc]
            rw [← Spec.map_comp]
            rw [← CommRingCat.ofHom_comp]
            rw [← AlgHom.toRingHom_eq_coe
              (Algebra.TensorProduct.includeRight : S.obj →ₐ[K] TensorProduct K Ω S.obj)]
            rw [tensorGalAlgEquiv_includeRight]
            simpa [AlgHom.toRingHom_eq_coe] using
              (specPullbackIso_hom_includeRight K Ω S).symm
  · calc
      ((fiberSchemeMap K Ω σ (specObj K S) ≫ (specPullbackIso K Ω S).hom) ≫
          (specPullbackIso K Ω S).inv) ≫ pullback.snd (specObj K S).hom (baseGeom K Ω)
          = fiberSchemeMap K Ω σ (specObj K S) ≫
              pullback.snd (specObj K S).hom (baseGeom K Ω) := by
            simp [Category.assoc]
      _ = pullback.snd (specObj K S).hom (baseGeom K Ω) ≫ (specAutIso K Ω σ⁻¹).hom := by
            simp [fiberSchemeMap]
      _ = (((specPullbackIso K Ω S).hom ≫
              Spec.map (CommRingCat.ofHom (tensorGalAlgEquiv K Ω S σ⁻¹).toRingHom)) ≫
              (specPullbackIso K Ω S).inv) ≫
            pullback.snd (specObj K S).hom (baseGeom K Ω) := by
            rw [Category.assoc]
            rw [specPullbackIso_inv_snd]
            rw [Category.assoc]
            rw [← Spec.map_comp]
            rw [← CommRingCat.ofHom_comp]
            rw [tensorGalAlgEquiv_includeLeft]
            rw [CommRingCat.ofHom_comp]
            rw [Spec.map_comp]
            simpa [specAutIso, Category.assoc] using
              congrArg (fun f ↦ f ≫ (specAutIso K Ω σ⁻¹).hom)
                (specPullbackIso_hom_includeLeft K Ω S).symm

/-- The natural Galois action on a ring-theoretic geometric fiber. -/
noncomputable instance ringFiberGalMulAction (S : CommAlgCat.FiniteEtale K) :
    MulAction Gal(Ω/K) ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) where
  smul σ φ := (σ : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω)
  one_smul φ := by
    change ((1 : Gal(Ω/K)) : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω) =
      (φ : S.obj →ₐ[K] Ω)
    ext x
    simp
  mul_smul σ τ φ := by
    change ((σ * τ : Gal(Ω/K)) : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω) =
      (σ : Ω →ₐ[K] Ω).comp
        (((τ : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω)) : S.obj →ₐ[K] Ω)
    ext x
    rfl

/-- The explicit ring-fiber/prime-spectrum comparison underlying
`CommAlgCat.FiniteEtale.fiberIsoComp`. -/
noncomputable def ringFiberToTensorPrimeEquiv [IsSepClosed Ω] (S : CommAlgCat.FiniteEtale K) :
    ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) ≃
      PrimeSpectrum (TensorProduct K Ω S.obj) :=
  (Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω).trans
    (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω (TensorProduct K Ω S.obj))

lemma liftEquivRight_smul_apply (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K))
    (φ : ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)))
    (r : TensorProduct K Ω S.obj) :
    (Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω
      ((σ : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω))) r =
      σ ((Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω (φ : S.obj →ₐ[K] Ω))
        ((tensorGalAlgEquiv K Ω S σ⁻¹) r)) := by
  refine TensorProduct.induction_on r ?_ ?_ ?_
  · simp
  · intro a s
    simp [Algebra.TensorProduct.liftEquivRight_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
    rw [map_add]
    exact (map_add σ
      (((Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω) (φ : S.obj →ₐ[K] Ω))
        ((tensorGalAlgEquiv K Ω S σ⁻¹) x))
      (((Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω) (φ : S.obj →ₐ[K] Ω))
        ((tensorGalAlgEquiv K Ω S σ⁻¹) y))).symm

lemma ringFiberToTensorPrimeEquiv_smul [IsSepClosed Ω]
    (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K))
    (φ : ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S))) :
    ringFiberToTensorPrimeEquiv K Ω S (σ • φ) =
      PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
        (ringFiberToTensorPrimeEquiv K Ω S φ) := by
  apply PrimeSpectrum.ext
  simp only [ringFiberToTensorPrimeEquiv, Equiv.trans_apply,
    Algebra.IsFiniteSplit.coe_algHomEquivPrimeSpectrum, PrimeSpectrum.comap_asIdeal]
  ext r
  simp only [RingHom.mem_ker, Ideal.mem_comap]
  change ((Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω)
        ((σ : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω))) r = 0 ↔
      ((Algebra.TensorProduct.liftEquivRight K Ω S.obj Ω) (φ : S.obj →ₐ[K] Ω))
        ((tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom r) = 0
  constructor
  · intro hr
    have h := liftEquivRight_smul_apply K Ω S σ φ r
    rw [h] at hr
    exact σ.toRingEquiv.injective (by simpa using hr)
  · intro hr
    rw [liftEquivRight_smul_apply]
    simpa [hr]

/-- The scheme fiber of `Spec S` over `Spec Ω` is the ring-theoretic geometric fiber. -/
noncomputable def specFiberToRingFiberEquiv [IsSepClosed Ω] (S : CommAlgCat.FiniteEtale K) :
    ((FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S)) ≃
      ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) :=
  (specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv.trans
    (ringFiberToTensorPrimeEquiv K Ω S).symm

lemma specPullbackIso_apply_smul [IsSepClosed Ω]
    (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K))
    (x : (FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S)) :
    (specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv (σ • x) =
      PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
        ((specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv x) := by
  change ((specPullbackIso K Ω S).hom.base (fiberSchemeMap K Ω σ (specObj K S) x)) =
      PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
        ((specPullbackIso K Ω S).hom.base x)
  have h := congrArg
    (fun g : ((FiniteEtale.pullback (baseGeom K Ω)).obj (specObj K S)).left ⟶
        Spec (.of (TensorProduct K Ω S.obj)) ↦ g.base x)
    (specPullbackIso_fiberSchemeMap K Ω S σ)
  simpa [Scheme.Hom.comp_apply, AlgebraicGeometry.Spec.map_apply] using h

/-- Equivariance of the scheme/ring fiber comparison for the BG1 action. -/
lemma specFiberToRingFiberEquiv_equivariant [IsSepClosed Ω]
    (S : CommAlgCat.FiniteEtale K) (σ : Gal(Ω/K))
    (x : (FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S)) :
    specFiberToRingFiberEquiv K Ω S (σ • x) =
      σ • specFiberToRingFiberEquiv K Ω S x := by
  apply (ringFiberToTensorPrimeEquiv K Ω S).injective
  calc
    ringFiberToTensorPrimeEquiv K Ω S (specFiberToRingFiberEquiv K Ω S (σ • x))
        = (specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv (σ • x) := by
          exact Equiv.apply_symm_apply (ringFiberToTensorPrimeEquiv K Ω S) _
    _ = PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
        ((specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv x) :=
          specPullbackIso_apply_smul K Ω S σ x
    _ = ringFiberToTensorPrimeEquiv K Ω S (σ • specFiberToRingFiberEquiv K Ω S x) := by
          rw [ringFiberToTensorPrimeEquiv_smul]
          change PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
              ((specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv x) =
            PrimeSpectrum.comap (tensorGalAlgEquiv K Ω S σ⁻¹).toRingEquiv.toRingHom
              ((ringFiberToTensorPrimeEquiv K Ω S)
                ((ringFiberToTensorPrimeEquiv K Ω S).symm
                  ((specPullbackIso K Ω S).schemeIsoToHomeo.toEquiv x)))
          rw [Equiv.apply_symm_apply]

lemma ringFiber_stabilizer_isOpen [Algebra.IsIntegral K Ω]
    (S : CommAlgCat.FiniteEtale K)
    (φ : (CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) φ : Set Gal(Ω/K)) := by
  let b := Module.finBasis K S.obj
  let φS : S.obj →ₐ[K] Ω := φ
  let H : Subgroup Gal(Ω/K) := ⨅ i : Fin (Module.finrank K S.obj),
    MulAction.stabilizer Gal(Ω/K) (φS (b i))
  have hHopen : IsOpen (H : Set Gal(Ω/K)) := by
    dsimp [H]
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ stabilizer_isOpen_of_isIntegral (φS (b i))
  have hsub : H ≤ MulAction.stabilizer Gal(Ω/K) φ := by
    intro σ hσ
    exact (MulAction.mem_stabilizer_iff (G := Gal(Ω/K)) (a := φ)).mpr <| by
      change ((σ : Ω →ₐ[K] Ω).comp φS : S.obj →ₐ[K] Ω) = φS
      ext x
      change σ (φS x) = φS x
      let L1 : S.obj →ₗ[K] Ω := σ.toLinearMap.comp φS.toLinearMap
      let L2 : S.obj →ₗ[K] Ω := φS.toLinearMap
      have hL : L1 = L2 := by
        apply b.ext
        intro i
        dsimp [L1, L2]
        have hi : σ ∈ MulAction.stabilizer Gal(Ω/K) (φS (b i)) := by
          exact Subgroup.mem_iInf.mp hσ i
        simpa using (MulAction.mem_stabilizer_iff.mp hi)
      exact DFunLike.congr_fun hL x
  exact Subgroup.isOpen_mono hsub hHopen

/-- Ring-level continuity of the natural Galois action on finite-étale algebra fibers. -/
theorem ringFiber_continuousSMul [Algebra.IsIntegral K Ω] (S : CommAlgCat.FiniteEtale K) :
    ContinuousSMul Gal(Ω/K) ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  exact ringFiber_stabilizer_isOpen K Ω S

/-- Continuity for the scheme fiber of an affine finite-étale cover `Spec S`. -/
theorem specObjFiber_continuousSMul [Algebra.IsIntegral K Ω] [IsSepClosed Ω]
    (S : CommAlgCat.FiniteEtale K) :
    ContinuousSMul Gal(Ω/K) ((FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S)) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  have hopen := (continuousSMul_iff_stabilizer_isOpen.mp
    (ringFiber_continuousSMul K Ω S)) (specFiberToRingFiberEquiv K Ω S x)
  refine Subgroup.isOpen_mono ?_ hopen
  intro σ hσ
  exact (MulAction.mem_stabilizer_iff (G := Gal(Ω/K)) (a := x)).mpr <| by
    apply (specFiberToRingFiberEquiv K Ω S).injective
    rw [specFiberToRingFiberEquiv_equivariant]
    exact MulAction.mem_stabilizer_iff.mp hσ

/-- Global sections of a finite-étale scheme over `Spec K`, as a finite étale `K`-algebra. -/
noncomputable def globalSectionsFiniteEtale (A : FiniteEtale (Spec (.of K))) :
    CommAlgCat.FiniteEtale K :=
  CommAlgCat.FiniteEtale.of K Γ(A.left, ⊤)

lemma baseMap_isoSpec_hom (A : FiniteEtale (Spec (.of K))) :
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(A.left, ⊤))) ≫
        (Spec (.of K)).isoSpec.hom =
      Spec.map A.hom.appTop := by
  rw [Scheme.isoSpec_Spec_hom]
  rw [← Spec.map_comp]
  congr 1
  ext x
  change (algebraMap K Γ(A.left, ⊤)) ((Scheme.ΓSpecIso (.of K)).hom.hom x) =
    A.hom.appTop.hom x
  dsimp [instAlgebraSectionOfType]
  change (A.hom.appLE ⊤ ⊤ (by simp)).hom
      ((Scheme.ΓSpecIso (.of K)).inv.hom ((Scheme.ΓSpecIso (.of K)).hom.hom x)) =
    A.hom.appTop.hom x
  have happ : A.hom.appLE ⊤ ⊤ (by simp) = A.hom.app ⊤ := by
    simpa using (Scheme.Hom.appLE_eq_app (f := A.hom) (U := ⊤))
  rw [happ]
  simp

lemma isoSpec_hom_comp_algebraMap (A : FiniteEtale (Spec (.of K))) :
    A.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(A.left, ⊤))) =
      A.hom := by
  haveI : IsAffineHom A.hom := A.prop.toIsFinite.toIsAffineHom
  haveI : IsAffine ((Functor.fromPUnit (Spec (.of K))).obj A.right) := by
    change IsAffine (Spec (.of K))
    infer_instance
  haveI : IsAffine A.left := isAffine_of_isAffineHom A.hom
  haveI : IsAffine ((𝟭 Scheme).obj A.left) := by
    change IsAffine A.left
    infer_instance
  rw [← cancel_mono (Spec (.of K)).isoSpec.hom]
  calc
    A.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(A.left, ⊤))) ≫
        (Spec (.of K)).isoSpec.hom
        = A.left.isoSpec.hom ≫ Spec.map A.hom.appTop := by
          rw [baseMap_isoSpec_hom]
    _ = A.hom ≫ (Spec (.of K)).isoSpec.hom := by
          exact Scheme.isoSpec_hom_naturality A.hom

/-- Every finite-étale scheme over `Spec K` is isomorphic to the one associated to its global
sections. -/
noncomputable def isoSpecObj (A : FiniteEtale (Spec (.of K))) :
    A ≅ specObj K (globalSectionsFiniteEtale K A) :=
  MorphismProperty.Over.isoMk A.left.isoSpec (by
    exact isoSpec_hom_comp_algebraMap K A)

/-- Continuity of the BG1 Galois action on every finite-étale fiber over `Spec K`. -/
theorem galFiber_continuousSMul [Algebra.IsIntegral K Ω] [IsSepClosed Ω]
    (A : FiniteEtale (Spec (.of K))) :
    ContinuousSMul Gal(Ω/K) ((FiniteEtale.fiber (baseGeom K Ω)).obj A) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  let e := isoSpecObj K A
  let F := FiniteEtale.fiber (baseGeom K Ω)
  have hcont : ContinuousSMul Gal(Ω/K) (F.obj (specObj K (globalSectionsFiniteEtale K A))) :=
    specObjFiber_continuousSMul K Ω (globalSectionsFiniteEtale K A)
  have hopen := (continuousSMul_iff_stabilizer_isOpen.mp hcont) (F.map e.hom x)
  refine Subgroup.isOpen_mono ?_ hopen
  intro σ hσ
  exact (MulAction.mem_stabilizer_iff (G := Gal(Ω/K)) (a := x)).mpr <| by
    let m : F.obj A → F.obj (specObj K (globalSectionsFiniteEtale K A)) := F.map e.hom
    have hinj : Function.Injective m := by
      intro x₁ x₂ h
      have h' := congrArg (fun y ↦ F.map e.inv y) h
      change ((F.map e.hom ≫ F.map e.inv) : F.obj A ⟶ F.obj A) x₁ =
        ((F.map e.hom ≫ F.map e.inv) : F.obj A ⟶ F.obj A) x₂ at h'
      rw [← F.map_comp, e.hom_inv_id, F.map_id] at h'
      simpa using h'
    apply hinj
    have hnat := CategoryTheory.PreGaloisCategory.IsNaturalSMul.naturality
      (F := F) (G := Gal(Ω/K)) σ e.hom x
    calc
      m (σ • x) = σ • m x := by
        simpa [m] using hnat
      _ = m x := MulAction.mem_stabilizer_iff.mp hσ

/-- Field-level transitivity of the natural Galois action on finite-étale algebra fibers. -/
theorem ringFiber_pretransitive_of_isField [Normal K Ω]
    (S : CommAlgCat.FiniteEtale K) (hS : IsField S.obj) :
    MulAction.IsPretransitive Gal(Ω/K)
      ((CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S)) := by
  letI : Field S.obj := hS.toField
  constructor
  intro φ ψ
  let χ : (φ : S.obj →ₐ[K] Ω).fieldRange ≃ₐ[K] (ψ : S.obj →ₐ[K] Ω).fieldRange :=
    (AlgHom.equivFieldRange (φ : S.obj →ₐ[K] Ω)).symm.trans
      (AlgHom.equivFieldRange (ψ : S.obj →ₐ[K] Ω))
  refine ⟨χ.liftNormal Ω, ?_⟩
  change ((χ.liftNormal Ω : Ω →ₐ[K] Ω).comp (φ : S.obj →ₐ[K] Ω) :
      S.obj →ₐ[K] Ω) = (ψ : S.obj →ₐ[K] Ω)
  ext s
  have h := AlgEquiv.liftNormal_commutes (χ := χ) Ω
    ((AlgHom.equivFieldRange (φ : S.obj →ₐ[K] Ω)) s)
  simpa [χ] using h

/-- Scheme-fiber transitivity for an affine finite-étale cover whose coordinate algebra is a
field. -/
theorem specObjFiber_pretransitive_of_isField [Normal K Ω] [IsSepClosed Ω]
    (S : CommAlgCat.FiniteEtale K) (hS : IsField S.obj) :
    MulAction.IsPretransitive Gal(Ω/K)
      ((FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S)) := by
  constructor
  intro x y
  have hpre := ringFiber_pretransitive_of_isField K Ω S hS
  obtain ⟨σ, hσ⟩ := hpre.exists_smul_eq
    (specFiberToRingFiberEquiv K Ω S x) (specFiberToRingFiberEquiv K Ω S y)
  refine ⟨σ, ?_⟩
  apply (specFiberToRingFiberEquiv K Ω S).injective
  rw [specFiberToRingFiberEquiv_equivariant]
  exact hσ

variable {X : Scheme.{u}}

/-- A finite-étale object whose underlying scheme is empty is initial. -/
noncomputable def isInitial_of_isEmpty_left (A : FiniteEtale X) [IsEmpty A.left] :
    IsInitial A := by
  let hA : IsInitial A.left := AlgebraicGeometry.isInitialOfIsEmpty (X := A.left)
  refine IsInitial.ofUniqueHom (fun Y ↦ MorphismProperty.Over.homMk (hA.to Y.left) ?_) ?_
  · exact hA.hom_ext _ _
  · intro Y f
    apply MorphismProperty.Over.Hom.ext
    exact hA.hom_ext _ _

lemma notInitial_of_nonempty_left (A : FiniteEtale X) [Nonempty A.left] :
    IsInitial A → False := by
  intro hA
  let e : A ≅ empty X := hA.uniqueUpToIso (IsInitial.ofUnique (empty X))
  haveI : IsIso e.hom.left := by
    change IsIso ((MorphismProperty.Over.forget (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X ⋙
      Over.forget X).map e.hom)
    infer_instance
  have hEmpty : IsEmpty A.left := by
    haveI : IsEmpty (empty X).left := by
      dsimp [empty]
      infer_instance
    exact Function.isEmpty e.hom.left.base
  exact (not_isEmpty_iff.mpr ‹Nonempty A.left›) hEmpty

/-- A categorically connected finite-étale cover over a connected base has connected total space. -/
theorem connectedSpace_left_of_isConnected [ConnectedSpace X]
    (A : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsConnected A] :
    ConnectedSpace A.left := by
  rw [connectedSpace_iff_connectedComponent]
  have hnonemptyA : Nonempty A.left := by
    by_contra h
    haveI : IsEmpty A.left := not_nonempty_iff.mp h
    exact CategoryTheory.PreGaloisCategory.IsConnected.notInitial
      (isInitial_of_isEmpty_left A)
  obtain ⟨a⟩ := hnonemptyA
  refine ⟨a, ?_⟩
  apply Set.eq_univ_of_forall
  intro b
  let i : _root_.ConnectedComponents A.left := _root_.ConnectedComponents.mk a
  let B : FiniteEtale X := ⟨Over.mk ((A.left.connCompOpen i).ι ≫ A.hom), by
    change IsFiniteEtale ((A.left.connCompOpen i).ι ≫ A.hom)
    exact connCompOpen_comp_isFiniteEtale A i⟩
  let j : B ⟶ A := MorphismProperty.Over.homMk (A.left.connCompOpen i).ι (by rfl)
  haveI : Mono j := by
    rw [AlgebraicGeometry.FiniteEtale.mono_iff X B A j]
    constructor
    · change IsOpenImmersion (A.left.connCompOpen i).ι
      infer_instance
    · change IsClosedImmersion (A.left.connCompOpen i).ι
      infer_instance
  have hninit : IsInitial B → False := by
    haveI : Nonempty B.left := by
      dsimp [B]
      infer_instance
    exact notInitial_of_nonempty_left B
  haveI : IsIso j := CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent B j hninit
  obtain ⟨y, hy⟩ := (asIso j.left).hom.homeomorph.toEquiv.surjective b
  have hycomp : j.left.base y ∈ connectedComponent a := by
    have hy2 : _root_.ConnectedComponents.mk (j.left.base y) = i := by
      dsimp [j, B]
      exact y.2
    rw [_root_.ConnectedComponents.coe_eq_coe'] at hy2
    simpa [i] using hy2
  simpa [← hy] using hycomp

/-- A connected finite-étale scheme over a field has a field of global sections. -/
theorem globalSections_isField_of_connectedSpace
    (A : FiniteEtale (Spec (.of K))) [ConnectedSpace A.left] :
    IsField Γ(A.left, ⊤) := by
  let R : Type u := Γ(A.left, ⊤)
  haveI : IsArtinianRing R := inferInstance
  haveI : _root_.IsReduced R := inferInstance
  haveI : ConnectedSpace (PrimeSpectrum R) := by
    change ConnectedSpace (Spec (.of R))
    exact (Homeomorph.connectedSpace_iff A.left.isoSpec.schemeIsoToHomeo).mp inferInstance
  haveI : Subsingleton (PrimeSpectrum R) := by
    exact PreconnectedSpace.trivial_of_discrete
  haveI : Subsingleton (MaximalSpectrum R) := by
    constructor
    intro x y
    exact (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := R)).symm.injective
      (Subsingleton.elim _ _)
  haveI : Nonempty (MaximalSpectrum R) := by
    obtain ⟨a⟩ := (inferInstance : Nonempty A.left)
    let p : PrimeSpectrum R := A.left.isoSpec.hom.base a
    exact ⟨⟨p.asIdeal, IsArtinianRing.isMaximal_of_isPrime p.asIdeal⟩⟩
  haveI : IsLocalRing R := IsLocalRing.of_singleton_maximalSpectrum (R := R)
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing R

/-- The coordinate algebra of a categorically connected finite-étale cover of `Spec K` is a
field. -/
theorem globalSectionsFiniteEtale_isField_of_isConnected
    (A : FiniteEtale (Spec (.of K))) [CategoryTheory.PreGaloisCategory.IsConnected A] :
    IsField (globalSectionsFiniteEtale K A).obj := by
  change IsField Γ(A.left, ⊤)
  haveI : ConnectedSpace A.left := connectedSpace_left_of_isConnected A
  exact globalSections_isField_of_connectedSpace K A

/-- Transitivity of the Galois action on the fiber of a connected finite-étale cover. -/
theorem galFiber_pretransitive_of_isConnected [Normal K Ω] [IsSepClosed Ω]
    (A : FiniteEtale (Spec (.of K))) [CategoryTheory.PreGaloisCategory.IsConnected A] :
    MulAction.IsPretransitive Gal(Ω/K) ((FiniteEtale.fiber (baseGeom K Ω)).obj A) := by
  constructor
  intro x y
  let e := isoSpecObj K A
  let F := FiniteEtale.fiber (baseGeom K Ω)
  have hpre : MulAction.IsPretransitive Gal(Ω/K)
      (F.obj (specObj K (globalSectionsFiniteEtale K A))) :=
    specObjFiber_pretransitive_of_isField K Ω (globalSectionsFiniteEtale K A)
      (globalSectionsFiniteEtale_isField_of_isConnected K A)
  haveI := hpre
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq Gal(Ω/K) (F.map e.hom x) (F.map e.hom y)
  refine ⟨σ, ?_⟩
  let m : F.obj A → F.obj (specObj K (globalSectionsFiniteEtale K A)) := F.map e.hom
  have hinj : Function.Injective m := by
    intro x₁ x₂ h
    have h' := congrArg (fun y ↦ F.map e.inv y) h
    change ((F.map e.hom ≫ F.map e.inv) : F.obj A ⟶ F.obj A) x₁ =
      ((F.map e.hom ≫ F.map e.inv) : F.obj A ⟶ F.obj A) x₂ at h'
    rw [← F.map_comp, e.hom_inv_id, F.map_id] at h'
    simpa using h'
  apply hinj
  have hnat := CategoryTheory.PreGaloisCategory.IsNaturalSMul.naturality
    (F := F) (G := Gal(Ω/K)) σ e.hom x
  calc
    m (σ • x) = σ • m x := by
      simpa [m] using hnat
    _ = m y := hσ

/-- The finite-étale algebra `K⟮x⟯` cut out by a single algebraic element of the geometric
closure. -/
noncomputable def adjoinFiniteEtale [Algebra.IsAlgebraic K Ω] [Algebra.IsSeparable K Ω]
    (x : Ω) : CommAlgCat.FiniteEtale.{u} K := by
  letI : Module.Finite K K⟮x⟯ := by
    have hfd : FiniteDimensional K K⟮x⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    exact Module.finite_of_finrank_pos Module.finrank_pos
  letI : Algebra.Etale K K⟮x⟯ := by
    rw [Algebra.Etale.iff_exists_algEquiv_prod]
    refine ⟨PUnit, inferInstance, fun _ ↦ K⟮x⟯, fun _ ↦ inferInstance,
      fun _ ↦ inferInstance, ?_, ?_⟩
    · exact (AlgEquiv.funUnique K PUnit K⟮x⟯).symm
    · intro _
      constructor
      · exact Module.finite_of_finrank_pos Module.finrank_pos
      · infer_instance
  exact CommAlgCat.FiniteEtale.of K K⟮x⟯

/-- The finite-étale `K`-scheme associated to `K⟮x⟯`. -/
noncomputable def adjoinFiniteEtaleScheme [Algebra.IsAlgebraic K Ω] [Algebra.IsSeparable K Ω]
    (x : Ω) : FiniteEtale (Spec (.of K)) :=
  specObj K (adjoinFiniteEtale K Ω x)

/-- If a Galois element acts trivially on every finite-étale fiber over `Spec K`, it is the
identity. -/
theorem galFiber_nontrivial [Algebra.IsAlgebraic K Ω] [Algebra.IsSeparable K Ω] [IsSepClosed Ω]
    (σ : Gal(Ω/K)) :
    (∀ A : FiniteEtale (Spec (.of K)),
      ∀ x : (FiniteEtale.fiber (baseGeom K Ω)).obj A, σ • x = x) → σ = 1 := by
  intro h
  ext x
  let S := adjoinFiniteEtale K Ω x
  let φ : (CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S) :=
    (K⟮x⟯).val
  let y : (FiniteEtale.fiber (baseGeom K Ω)).obj (specObj K S) :=
    (specFiberToRingFiberEquiv K Ω S).symm φ
  have hy : σ • y = y := h (specObj K S) y
  have hring : σ • φ = φ := by
    calc
      σ • φ = σ • (specFiberToRingFiberEquiv K Ω S y) := by
            exact congrArg (fun z ↦ σ • z)
              (Equiv.apply_symm_apply (specFiberToRingFiberEquiv K Ω S) φ).symm
      _ = specFiberToRingFiberEquiv K Ω S (σ • y) := by
            rw [specFiberToRingFiberEquiv_equivariant]
      _ = specFiberToRingFiberEquiv K Ω S y := by rw [hy]
      _ = φ := by
            exact Equiv.apply_symm_apply (specFiberToRingFiberEquiv K Ω S) φ
  let gen : S.obj := IntermediateField.AdjoinSimple.gen K x
  have hgen := congrArg
    (fun ψ : (CommAlgCat.FiniteEtale.fiber K Ω).obj (Opposite.op S) ↦
      (show S.obj →ₐ[K] Ω from ψ) gen) hring
  change σ (((K⟮x⟯).val) (IntermediateField.AdjoinSimple.gen K x)) =
    ((K⟮x⟯).val) (IntermediateField.AdjoinSimple.gen K x) at hgen
  simpa [IntermediateField.AdjoinSimple.algebraMap_gen] using hgen

/-- The Krull-topologized Galois group attached to a Galois extension. -/
noncomputable abbrev galProfiniteGrp [IsGalois K Ω] : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp K Ω

/-- The BG1 homomorphism from a Galois group to automorphisms of the scheme-level finite-étale
fiber functor. -/
noncomputable abbrev galToFiberAut [IsGalois K Ω] :
    galProfiniteGrp K Ω →* Aut (FiniteEtale.fiber (baseGeom K Ω)) :=
  galToSchemeFiberAutHom K Ω

/-- The action of the Krull-topologized Galois group on each scheme-level finite-étale fiber. -/
noncomputable instance galProfiniteGrpFiberMulAction [IsGalois K Ω]
    (A : FiniteEtale (Spec (.of K))) :
    MulAction (galProfiniteGrp K Ω) ((FiniteEtale.fiber (baseGeom K Ω)).obj A) :=
  galFiberMulAction K Ω A

/-- The Galois action is natural for morphisms in the scheme-level finite-étale category. -/
instance galProfiniteGrpFiberIsNaturalSMul [IsGalois K Ω] :
    CategoryTheory.PreGaloisCategory.IsNaturalSMul
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) :=
  galFiberIsNaturalSMul K Ω

@[simp]
lemma galToFiberAut_hom_app_apply [IsGalois K Ω]
    (σ : galProfiniteGrp K Ω) (A : FiniteEtale (Spec (.of K)))
    (x : (FiniteEtale.fiber (baseGeom K Ω)).obj A) :
    (galToFiberAut K Ω σ).hom.app A x = σ • x :=
  rfl

/-- The Galois group of a separably closed Galois extension is a fundamental group for the
finite-étale fiber functor over `Spec K`. -/
instance gal_isFundamentalGroup [IsGalois K Ω] [IsSepClosed Ω] :
    CategoryTheory.PreGaloisCategory.IsFundamentalGroup
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) where
  transitive_of_isGalois A := galFiber_pretransitive_of_isConnected K Ω A
  continuous_smul A := galFiber_continuousSMul K Ω A
  non_trivial' σ := galFiber_nontrivial K Ω σ

/-- The `IsFundamentalGroup.toAut` map agrees pointwise with the explicit Galois action. -/
@[simp]
theorem gal_toAut_hom_app_apply [IsGalois K Ω] [IsSepClosed Ω]
    (σ : galProfiniteGrp K Ω) (A : FiniteEtale (Spec (.of K)))
    (x : (FiniteEtale.fiber (baseGeom K Ω)).obj A) :
    (CategoryTheory.PreGaloisCategory.toAut
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) σ).hom.app A x =
      (galToFiberAut K Ω σ).hom.app A x :=
  rfl

/-- Objectwise form of the comparison between the assembled `toAut` map and the explicit action. -/
theorem gal_toAut_hom_app [IsGalois K Ω] [IsSepClosed Ω]
    (σ : galProfiniteGrp K Ω) (A : FiniteEtale (Spec (.of K))) :
    (CategoryTheory.PreGaloisCategory.toAut
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) σ).hom.app A =
      (galToFiberAut K Ω σ).hom.app A := by
  ext x
  exact gal_toAut_hom_app_apply K Ω σ A x

/-- Homomorphism-level comparison between the assembled `toAut` map and the explicit action. -/
theorem gal_toAut_eq [IsGalois K Ω] [IsSepClosed Ω] :
    CategoryTheory.PreGaloisCategory.toAut
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) =
      galToFiberAut K Ω := by
  ext σ A x
  exact gal_toAut_hom_app_apply K Ω σ A x

/-- The canonical homeomorphism from the Galois group to automorphisms of the finite-étale fiber
functor. -/
noncomputable def galAutFiberHomeo [IsGalois K Ω] [IsSepClosed Ω] :
    galProfiniteGrp K Ω ≃ₜ Aut (FiniteEtale.fiber (baseGeom K Ω)) :=
  CategoryTheory.PreGaloisCategory.toAutHomeo
    (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω)

/-- The Galois comparison as a continuous multiplicative equivalence. -/
noncomputable def galAutFiberContinuousMulEquiv [IsGalois K Ω] [IsSepClosed Ω] :
    galProfiniteGrp K Ω ≃ₜ* Aut (FiniteEtale.fiber (baseGeom K Ω)) where
  __ := galAutFiberHomeo K Ω
  map_mul' σ τ := by
    change CategoryTheory.PreGaloisCategory.toAut
        (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) (σ * τ) =
      CategoryTheory.PreGaloisCategory.toAut
        (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) σ *
      CategoryTheory.PreGaloisCategory.toAut
        (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω) τ
    exact map_mul (CategoryTheory.PreGaloisCategory.toAut
      (FiniteEtale.fiber (baseGeom K Ω)) (galProfiniteGrp K Ω)) σ τ

/-- A large-universe copy of a profinite group. -/
noncomputable def uliftProfiniteGrp (G : ProfiniteGrp.{u}) : ProfiniteGrp.{u + 1} :=
  letI : TotallyDisconnectedSpace (ULift.{u + 1, u} G) :=
    Homeomorph.totallyDisconnectedSpace (Homeomorph.ulift.symm : G ≃ₜ ULift.{u + 1, u} G)
  ProfiniteGrp.of (ULift.{u + 1, u} G)

/-- The continuous multiplicative equivalence from a large-universe copy back to the original
profinite group. -/
noncomputable def uliftContinuousMulEquiv (G : ProfiniteGrp.{u}) :
    ULift.{u + 1, u} G ≃ₜ* G where
  __ := (Homeomorph.ulift : ULift.{u + 1, u} G ≃ₜ G)
  map_mul' _ _ := rfl

/-- The Galois comparison after applying the `ULift` bridge on the source. -/
noncomputable def galUliftAutFiberContinuousMulEquiv [IsGalois K Ω] [IsSepClosed Ω] :
    ULift.{u + 1, u} (galProfiniteGrp K Ω) ≃ₜ*
      Aut (FiniteEtale.fiber (baseGeom K Ω)) :=
  (uliftContinuousMulEquiv (galProfiniteGrp K Ω)).trans (galAutFiberContinuousMulEquiv K Ω)

/-- The profinite-group isomorphism between the large-universe Galois group and the pointed
finite-étale fundamental group of `Spec K`. -/
noncomputable def galUliftAutFiberIso [IsGalois K Ω] [IsSepClosed Ω] :
    uliftProfiniteGrp (galProfiniteGrp K Ω) ≅
      ProfiniteGrp.of (Aut (FiniteEtale.fiber (baseGeom K Ω))) :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso
    (galUliftAutFiberContinuousMulEquiv K Ω)

end FiniteEtale
end AlgebraicGeometry
