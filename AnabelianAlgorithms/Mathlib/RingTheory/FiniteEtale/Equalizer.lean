module

public import Mathlib.Logic.Function.Coequalizer
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.Bijective
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import AnabelianAlgorithms.Mathlib.RingTheory.TensorProduct.Basic
public import AnabelianAlgorithms.Mathlib.RingTheory.FiniteEtale.Descent

/-
This file amalgamates material copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
Corresponding source files in that project:
- `Pi1/RingTheory/FiniteEtale/Equalizer.lean`
- `Pi1/RingTheory/KerTensor.lean`
- `Pi1/Mathlib/RingTheory/Flat/Equalizer.lean`
-/
@[expose] public section

attribute [local instance] Module.FinitePresentation.of_finite_of_finitePresentation

open TensorProduct

universe u v

namespace RingHom

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable {P} in
lemma OfLocalizationSpan.pi (hP : OfLocalizationSpan P)
    (hPi : RespectsIso P)
    {ι : Type u} [_root_.Finite ι]
    (R : ι → Type u) (S : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i)
    (hf : ∀ i, P (f i)) :
    P (RingHom.pi <| fun i ↦ (f i).comp <| Pi.evalRingHom R i) := by
  classical
  have := Ideal.span_single_eq_top R
  apply hP.ofIsLocalization hPi _ _ this
  rintro ⟨r, i, rfl⟩
  let i₁ : Algebra (∀ i, R i) (R i) := (Pi.evalRingHom R i).toAlgebra
  let i₂ : Algebra (∀ i, S i) (S i) := (Pi.evalRingHom S i).toAlgebra
  refine ⟨R i, S i, inferInstance, inferInstance, i₁, i₂, ?_, ?_, f i, ?_, hf i⟩
  · refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom R i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · have : (RingHom.pi fun i ↦ (f i).comp <| Pi.evalRingHom R i)
        (Pi.single i 1) = Pi.single i 1 := by
      ext j
      simp only [Pi.single, RingHom.pi_apply, coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
        Function.update, Pi.zero_apply]
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    simp only [this]
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · ext j x
    simp [RingHom.algebraMap_toAlgebra]

lemma _root_.Pi.algebraMap_instAlgebraForall_apply {ι : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] (S : ι → Type*) [∀ i, CommSemiring (S i)]
    [∀ i, Algebra (S i) (A i)] (x : ∀ i, S i) :
    algebraMap (∀ i, S i) (∀ i, A i) x = fun i ↦ algebraMap (S i) (A i) (x i) :=
  rfl

instance (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  refine ⟨fun P _ _ _ Q _ ↦ ?_⟩
  have heq :
      LinearMap.rTensor (M × N) Q.subtype =
        (TensorProduct.prodRight _ _ _ _ _).symm.toLinearMap ∘ₗ
          LinearMap.prodMap (Q.subtype.rTensor M) (Q.subtype.rTensor N) ∘ₗ
          (TensorProduct.prodRight _ _ _ _ _).toLinearMap := by
    ext <;>
    · apply (TensorProduct.prodRight R R P M N).injective
      simp
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, heq]
  apply Function.Injective.prodMap <;>
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

set_option synthInstance.maxHeartbeats 0 in
-- Finite products of flat modules are flat; the finite-product induction synthesizes many
-- intermediate module instances.
instance {ι : Type*} (R : Type*) [CommRing R] [_root_.Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) := by
  refine Module.pi_induction' (ι := ι) R (motive := fun N _ _ ↦ Module.Flat R N)
    (motive' := fun N _ _ ↦ Module.Flat R N)
      ?_ ?_ ?_ ?_ M inferInstance
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · infer_instance
  · intros
    infer_instance

lemma CodescendsAlong.of_forall_flat {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    {ι : Type u} (T : ι → Type u) [∀ i, CommRing (T i)]
    [∀ i, Algebra R (T i)] [∀ i, Module.Flat R (T i)]
    (ho : ∀ i, IsOpen <| Set.range <| PrimeSpectrum.comap (algebraMap R (T i)))
    (hunion : ⋃ i, Set.range (PrimeSpectrum.comap (algebraMap R (T i))) = Set.univ)
    (H : ∀ i, P (algebraMap (T i) (T i ⊗[R] S))) :
    P (algebraMap R S) := by
  classical
  let U (i : ι) : Set (PrimeSpectrum R) :=
    Set.range <| PrimeSpectrum.comap (algebraMap R (T i))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun p ↦ ho _) (hunion ▸ le_rfl)
  let A : Type u := ∀ (p : t), T p.1
  have : Module.FaithfullyFlat R A := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    obtain ⟨i, hi, q, rfl⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    use (PrimeSpectrum.comap <| Pi.evalRingHom (fun p : t ↦ T p.1) ⟨i, hi⟩) q
    rfl
  apply hP.algebraMap_tensorProduct (R := R) (S := A) (T := S)
  · rwa [faithfullyFlat_algebraMap_iff]
  let e : A ⊗[R] S ≃ₐ[R] ∀ i : t, T i.val ⊗[R] S :=
    (Algebra.TensorProduct.comm ..).trans <|
      (Algebra.TensorProduct.piRight R R S (fun i : t ↦ T i)).trans <|
        .piCongrRight fun i ↦ Algebra.TensorProduct.comm ..
  have : algebraMap A (A ⊗[R] S) = e.symm.toRingHom.comp
      (algebraMap A <| ∀ p : t, T p.1 ⊗[R] S) := by
    ext i x
    simp [e, A, Pi.algebraMap_instAlgebraForall_apply, -AlgEquiv.symm_toRingEquiv,
      AlgEquiv.piCongrRight, Algebra.TensorProduct.piRight]
  rw [this]
  apply hPi.1
  exact hPl.pi hPi _ _ _ (fun i ↦ H i.1)

lemma CodescendsAlong.of_forall_exists_flat {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧ Module.Flat R T ∧
      IsOpen (Set.range <| PrimeSpectrum.comap (algebraMap R T)) ∧
      P (algebraMap T (T ⊗[R] S))) :
    P (algebraMap R S) := by
  choose T h1 h2 hmem _ ho hT using H
  exact hP.of_forall_flat _ hPi hPl T ho (Set.iUnion_eq_univ_iff.mpr fun p ↦ ⟨p, hmem p⟩) hT

open AlgebraicGeometry CategoryTheory Limits in
lemma PrimeSpectrum.range_comap_tensorProduct (R S T : Type u) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    Set.range (PrimeSpectrum.comap <| algebraMap S (S ⊗[R] T)) =
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    use PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom p
    have : (algebraMap S (S ⊗[R] T)).comp (algebraMap R S) =
        Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R T) := by ext; simp
    exact congr(PrimeSpectrum.comap $(this) p).symm
  · rintro ⟨q, hp⟩
    obtain ⟨z, hz⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (X := Spec <| .of S) (Y := Spec <| .of T) (S := Spec <| .of R)
        (f := Spec.map <| CommRingCat.ofHom (algebraMap R S))
        (g := Spec.map <| CommRingCat.ofHom (algebraMap R T)) p q hp.symm
    let e : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T) :=
      pullbackSpecIso R S T
    use e.hom.base z
    rw [← hz.1, ← pullbackSpecIso_hom_fst]
    rfl

set_option maxHeartbeats 0 in
-- This is the algebra-map form of faithfully flat codescent, transported across the standard
-- tensor-product description of affine pullbacks.
lemma CodescendsAlong.algHom_of_forall_exists_flat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (f : A →ₐ[R] B)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧ Module.Flat R T ∧
      IsOpen (Set.range <| PrimeSpectrum.comap (algebraMap R T)) ∧
      P (Algebra.TensorProduct.map (.id T T) f).toRingHom) :
    P f.toRingHom := by
  algebraize [f.toRingHom]
  apply hP.of_forall_exists_flat _ hPi hPl
  intro p
  obtain ⟨T, _, _, ⟨q, hq⟩, hflat, ho, hp⟩ :=
    H (PrimeSpectrum.comap (algebraMap R A) p)
  have heq : Set.range (PrimeSpectrum.comap (algebraMap A (A ⊗[R] T))) =
      (PrimeSpectrum.comap (algebraMap R A)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) :=
    PrimeSpectrum.range_comap_tensorProduct R A T
  let e : T ⊗[R] B ≃ₐ[R] (A ⊗[R] T) ⊗[A] B :=
    .trans ((Algebra.TensorProduct.comm _ _ _).restrictScalars R)
      (.trans
        ((Algebra.TensorProduct.cancelBaseChange R A A B T).symm.restrictScalars R)
        ((Algebra.TensorProduct.comm _ _ _).restrictScalars R))
  have hdiag' :
    IsScalarTower.toAlgHom R (A ⊗[R] T) ((A ⊗[R] T) ⊗[A] B) =
      (AlgHom.comp e.toAlgHom
        ((Algebra.TensorProduct.map (AlgHom.id T T) f).restrictScalars R)).comp
        (Algebra.TensorProduct.comm _ _ _).toAlgHom := by
    ext a
    · suffices h : (a ⊗ₜ[R] (1 : T)) ⊗ₜ[A] (1 : B) = (1 ⊗ₜ[R] 1) ⊗ₜ[A] f a by
        simp [e, h]
      rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, smul_eq_mul, mul_one,
        AlgHom.toRingHom_eq_coe, coe_coe]
    · simp [e]
  replace hdiag' := congr($(hdiag').toRingHom)
  simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, AlgHom.comp_toRingHom] at hdiag'
  refine ⟨A ⊗[R] T, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · rw [heq]
    use q
  · rw [heq]
    exact ho.preimage (PrimeSpectrum.continuous_comap _)
  · rw [hdiag']
    exact hPi.2 _ (Algebra.TensorProduct.comm R A T).toRingEquiv (hPi.1 _ _ hp)

end RingHom

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Localization in
lemma AlgHom.exists_cover_eq_of_eq {R A B : Type*} [CommRing R] (S : Submonoid R)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A]
    (Rₚ : Type*) (Aₚ Bₚ : Type u) [CommRing Rₚ] [CommRing Aₚ] [CommRing Bₚ]
    [Algebra R Rₚ] [Algebra R Aₚ] [Algebra R Bₚ] [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ]
    [Algebra A Aₚ] [Algebra B Bₚ]
    [IsScalarTower R A Aₚ] [IsScalarTower R B Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]
    [IsLocalization S Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₚ]
    (f g : A →ₐ[R] B) (hf : IsLocalization.mapₐ S Rₚ Aₚ Bₚ f = IsLocalization.mapₐ S Rₚ Aₚ Bₚ g) :
    ∃ (r : S),
      Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) f =
        Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) g := by
  let u : B →ₗ[R] Bₚ := (IsScalarTower.toAlgHom R B Bₚ).toLinearMap
  have : IsLocalizedModule S u := by
    simp only [u]
    rw [isLocalizedModule_iff_isLocalization]
    infer_instance
  obtain ⟨s, hs⟩ := by
    refine Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
      (N := B) (N' := Bₚ) (M := A) u f g ?_
    ext x
    simpa using! DFunLike.congr_fun hf (algebraMap A Aₚ x)
  use s
  ext a
  simp only [Algebra.TensorProduct.map_restrictScalars_comp_includeRight, coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
  have hun : IsUnit ((algebraMap R (Away s.val ⊗[R] B) s)) := by
    rw [IsScalarTower.algebraMap_apply R (Away s.val) _]
    apply (IsLocalization.Away.algebraMap_isUnit s.val).map
  suffices s.val • ((1 : Away s.val) ⊗ₜ[R] f a) = s.val • (1 ⊗ₜ[R] g a) by
    apply hun.mul_left_cancel
    rwa [← Algebra.smul_def, ← Algebra.smul_def]
  have := DFunLike.congr_fun hs a
  simp only [LinearMap.smul_apply, LinearMap.coe_coe] at this
  rw [← TensorProduct.tmul_smul]
  erw [← TensorProduct.tmul_smul, this]
  rfl

end

section Equalizer

def AlgHom.equalizerCongr {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA) :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgEquiv.ofAlgHom
    (AlgHom.codRestrict (eA.toAlgHom.comp (equalizer f g).val) _ <| by
      intro x
      simp only [coe_comp, AlgEquiv.coe_toAlgHom, Subalgebra.coe_val, Function.comp_apply,
        mem_equalizer]
      rw [← hf', x.2, hg'])
    (AlgHom.codRestrict (eA.symm.toAlgHom.comp (equalizer f' g').val) _ <| by
      intro x
      simp only [coe_comp, AlgEquiv.coe_toAlgHom, Subalgebra.coe_val, Function.comp_apply,
        mem_equalizer]
      apply eB.injective
      rw [hf', hg', AlgEquiv.apply_symm_apply, x.2])
    (by ext; simp)
    (by ext; simp)
   where
    hf' (x) : eB (f x) = f' (eA x) := DFunLike.congr_fun hf x
    hg' (x) : eB (g x) = g' (eA x) := DFunLike.congr_fun hg x

def AlgHom.equalizerCongrOfEq {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {f g f' g' : A →ₐ[R] B}
    (hf : f = f') (hg : g = g') :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgHom.equalizerCongr AlgEquiv.refl AlgEquiv.refl
    (by subst hf; simp) (by subst hg; simp)

lemma AlgHom.equalizerCongr_symm_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f' g') :
    (AlgHom.equalizerCongr eA eB hf hg).symm x =
      ⟨eA.symm x, ((AlgHom.equalizerCongr eA eB hf hg).symm x).2⟩ :=
  rfl

lemma AlgHom.equalizerCongr_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f g) :
    AlgHom.equalizerCongr eA eB hf hg x =
      ⟨eA x, (AlgHom.equalizerCongr eA eB hf hg x).2⟩ :=
  rfl

end Equalizer

--lemma Algebra.FiniteEtale.mk (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
--    (h₁ : Algebra.Etale R S) (h₂ : Module.Finite R S) :
--    Algebra.FiniteEtale R S :=
--  inferInstance

section rankAtStalk

lemma Algebra.exists_cover_rankAtStalk_eq {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p,
      Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] S) =
        Module.rankAtStalk S ⟨p, inferInstance⟩ := by
  obtain ⟨U, hU, hp, heq⟩ := (Module.isLocallyConstant_rankAtStalk (M := S)).exists_open ⟨p, ‹_›⟩
  obtain ⟨V, ⟨r, rfl⟩, (hr : r ∉ p), hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
  refine ⟨r, hr, ?_⟩
  ext q
  rw [Module.rankAtStalk_baseChange]
  apply heq
  apply hrU
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    SetLike.mem_coe]
  obtain ⟨-, b⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (.powers r) _ q.asIdeal).mp q.2
  rw [Set.disjoint_left] at b
  simp only [SetLike.mem_coe, Ideal.coe_comap, Set.mem_preimage] at b
  apply b
  use 1
  simp

end rankAtStalk

namespace RingHom

/-- A ring hom is split of (constant) rank `n` if `S` is `R`-split of rank `n`. -/
def IsFiniteSplit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.IsFiniteSplit R S

end RingHom

section

variable {E F : Type*}

@[simps!]
def AlgHom.compRight (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (σ : E → F) :
    (F → S) →ₐ[R] E → S :=
  AlgHom.pi (R := R) (fun f ↦ Pi.evalAlgHom R _ (σ f))

instance [Finite F] (σ τ : E → F) : Finite (Function.Coequalizer σ τ) :=
  Finite.of_surjective _ (Function.Coequalizer.mk_surjective σ τ)

def RingHom.compRight (R : Type*) [CommRing R] {E F : Type*} (σ : E → F) :
    (F → R) →+* (E → R) :=
  RingHom.pi (fun f ↦ Pi.evalRingHom _ (σ f))

@[simp]
lemma RingHom.compRight_apply (R : Type*) [CommRing R] {E F : Type*} (σ : E → F)
    (x : F → R) (i : E) :
    compRight R σ x i = x (σ i) :=
  rfl

def AlgHom.equalizerCompRightEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ τ : E → F) :
    AlgHom.equalizer (AlgHom.compRight R S σ) (AlgHom.compRight R S τ) ≃ₐ[R]
      Function.Coequalizer σ τ → S :=
  AlgEquiv.ofAlgHom
    (AlgHom.pi (R := R) (Function.Coequalizer.desc σ τ
      (fun f ↦ (Pi.evalAlgHom R (fun _ ↦ S) f).comp
        (equalizer (AlgHom.compRight R S σ) (AlgHom.compRight R S τ)).val)
        (by ext f ⟨x, hx⟩; exact congrFun hx f)))
    (codRestrict (.compRight _ _ (Function.Coequalizer.mk _ _))
      (equalizer _ _)
      (fun x ↦ by ext e; simp only [AlgHom.compRight_apply]; rw [Function.Coequalizer.condition]))
    (by
      ext f x
      obtain ⟨x, rfl⟩ := Function.Coequalizer.mk_surjective _ _ x
      simp)
    (by ext f x; simp)

@[simp]
lemma AlgHom.equalizerCompRightEquiv_symm_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F) (x : Function.Coequalizer σ τ → S)
    (i : F) :
    ((equalizerCompRightEquiv R S σ τ).symm x).val i = x (.mk _ _ i) :=
  rfl

@[simp]
lemma AlgHom.equalizerCompRightEquiv_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F)
    (x : equalizer (compRight R S σ) (compRight R S τ)) (i : F) :
    (AlgHom.equalizerCompRightEquiv R S σ τ) x (Function.Coequalizer.mk σ τ i) =
      x.val i :=
  rfl

instance (R : Type*) [CommRing R] [Finite E] [Finite F] (σ τ : E → F) :
    Algebra.IsFiniteSplit R
      (AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ)) :=
  Algebra.IsFiniteSplit.of_algEquiv (AlgHom.equalizerCompRightEquiv R R σ τ).symm

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem {R E F : Type*} [_root_.Finite E]
    [Nonempty E] [CommRing R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R R σ := by
  nontriviality R
  cases nonempty_fintype E
  classical
  have hor (i) (j) : f (Pi.single j 1) i = 0 ∨ f (Pi.single j 1) i = 1 := by
    apply H
    unfold IsIdempotentElem
    rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul_left]
    simp
  have (x : F) : ∃ (y : E), f (Pi.single y 1) x = 1 := by
    by_contra! hc
    replace hc (y : E) : f (Pi.single y 1) x = 0 := by
      obtain (h|h) := hor x y
      · assumption
      · simp [hc] at h
    have : 1 = ∑ y : E, f (Pi.single y 1) x := by
      rw [← Fintype.sum_apply]
      rw [← map_sum, Finset.univ_sum_single, ← Pi.one_def, map_one, Pi.one_apply]
    simp_rw [hc] at this
    simp at this
  have (x : F) : ∃! (y : E), f (Pi.single y 1) x = 1 := by
    apply existsUnique_of_exists_of_unique
    · exact this x
    · intro a b ha hb
      by_contra! h
      have : (Pi.single a 1) * (Pi.single b 1 : E → R) = 0 := by
        simp [← Pi.single_mul_left, h]
      apply_fun ((f ·) · x) at this
      simp [ha, hb] at this
  choose σ hσ hun using this
  use σ
  dsimp at hσ
  ext x i
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single j r =>
      have : Pi.single j r = r • (Pi.single j 1 : E → R) := by simp [← Pi.single_smul]
      rw [this]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, AlgHom.compRight_apply]
      congr
      obtain (h|h) := hor i j
      · have : j ≠ σ i := by
          intro hj
          subst hj
          simp [hσ] at h
        simp [this, h]
      · have := hun i j h
        subst this
        simp [hσ]

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem' {R E F : Type*} [_root_.Finite E]
    [CommRing R] [Nontrivial R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R R σ := by
  cases isEmpty_or_nonempty E
  · have : Subsingleton (F → R) := f.codomain_trivial
    cases isEmpty_or_nonempty F
    · use default
      apply Subsingleton.elim
    · simpa using false_of_nontrivial_of_subsingleton (F → R)
  · apply eq_compRight_of_no_nontrivial_isIdempotentElem H

lemma IsIdempotentElem.eq_one_of_isUnit {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (heu : IsUnit e) : e = 1 := by
  rw [eq_comm, ← sub_eq_zero]
  apply heu.mul_left_cancel
  simp [he]

lemma IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {e : R} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · obtain (h|h) := IsLocalRing.isUnit_or_isUnit_one_sub_self e
    · exact Or.inr (he.eq_one_of_isUnit h)
    · exact Or.inl (by simpa using he.one_sub.eq_one_of_isUnit h)
  · rintro (h|h) <;> subst h
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

lemma RingHom.eq_compRight_of_isLocalHom {R E F : Type*} [_root_.Finite E] [CommRing R]
    (f : (E → R) →ₐ[R] F → R) [IsLocalRing R] :
    ∃ (σ : F → E), f = .compRight R R σ := by
  apply AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem'
  intro e he
  rwa [IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one] at he

-- TODO: fix `IsLocalization.mapₐ` to have the correct universe generality
open Localization in
lemma AlgHom.exists_cover_eq_compRight'' {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F]
    [CommRing R]
    (f : (E → R) →ₐ[R] F → R) (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
      (E → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    all_goals try rfl
    infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid (F → R) p.primeCompl)
      (F → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    all_goals try rfl
    infer_instance
  let fₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) f
  obtain ⟨σ, hσ⟩ := RingHom.eq_compRight_of_isLocalHom fₚ
  let gₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) (.compRight R R σ)
  have : fₚ = gₚ := by
    rw [hσ]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
    ext x i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      AlgHom.compRight_apply, IsLocalization.mapₐ_coe, IsLocalization.map_eq, gₚ]
    rfl
  obtain ⟨⟨r, hr⟩, heq⟩ := AlgHom.exists_cover_eq_of_eq _ _ _ _ f (.compRight R R σ) this
  exact ⟨r, hr, σ, heq⟩

open Localization in
lemma AlgHom.exists_cover_eq_compRight''₂ {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F] [CommRing R] (f g : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ τ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) ∧
      Algebra.TensorProduct.map (.id (Away r) (Away r)) g =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ τ) := by
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f p
  obtain ⟨r', hr', τ, hτ⟩ := AlgHom.exists_cover_eq_compRight'' g p
  letI : Algebra (Localization.Away r) (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_left (y := algebraMap _ _ r')
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  letI : Algebra (Localization.Away r') (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r' (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_right (x := algebraMap _ _ r)
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  have : IsScalarTower R (Away r) (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R (Away r') (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  let eE : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eE' : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF' : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have heq (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE.toAlgHom) := by
    ext
    simp [eF, eE]
  have heq' (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF'.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE'.toAlgHom) := by
    ext
    simp [eF', eE']
  refine ⟨r * r', ?_, σ, τ, ?_, ?_⟩
  · intro hr
    cases Ideal.IsPrime.mem_or_mem inferInstance hr <;> contradiction
  · rw [heq, hσ, ← heq]
  · rw [heq', hτ, ← heq']

def AlgHom.IsSplit {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : Prop :=
  ∃ (n m : ℕ) (eA : A ≃ₐ[R] (Fin n → R)) (eB : B ≃ₐ[R] (Fin m → R))
    (σ : Fin m → Fin n),
    f = eB.symm.toAlgHom.comp ((AlgHom.compRight R R σ).comp eA)

lemma AlgHom.IsSplit.mk {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) {E F : Type*}
    [_root_.Finite E] [_root_.Finite F]
    (eA : A ≃ₐ[R] (E → R)) (eB : B ≃ₐ[R] (F → R)) (σ : F → E)
    (h : eB.toAlgHom.comp f = (AlgHom.compRight R R σ).comp eA.toAlgHom) :
    f.IsSplit := by
  cases nonempty_fintype E
  cases nonempty_fintype F
  let eE := Fintype.equivFin E
  let eF := Fintype.equivFin F
  refine ⟨Fintype.card E, Fintype.card F, eA.trans ?_, eB.trans ?_,
    eE ∘ σ ∘ eF.symm, ?_⟩
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eE
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eF
  · ext x
    apply eB.injective
    have := DFunLike.congr_fun h x
    simp only [coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply] at this
    ext i
    simp [this, AlgHom.compRight]

lemma AlgHom.compRight_apply' {E F : Type*} (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (σ : E → F) (x : F → S) :
    AlgHom.compRight R S σ x = fun i ↦ x (σ i) :=
  rfl

variable (S) in
lemma AlgHom.IsSplit.tensorProductMap {R S A B : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R S] [Algebra R B]
    {f : A →ₐ[R] B} (hf : f.IsSplit) :
    (Algebra.TensorProduct.map (.id S S) f).IsSplit := by
  obtain ⟨n, m, eA, eB, σ, hf⟩ := hf
  refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
    ((Algebra.TensorProduct.congr .refl eA).trans (Algebra.TensorProduct.piScalarRight ..))
    ((Algebra.TensorProduct.congr .refl eB).trans (Algebra.TensorProduct.piScalarRight ..)) σ ?_
  ext a
  simp [hf]

variable (S) in
lemma AlgHom.IsSplit.iff_of_isScalarTower {R S A B : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R S] [Algebra R B]
    (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (f : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (.id T T) f).IsSplit ↔
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f)).IsSplit := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ a)
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, coe_comp, Function.comp_apply] at this
    simp [this]
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ (1 ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, coe_comp, Function.comp_apply] at this
    simp [this]

namespace Algebra

lemma exists_isFiniteSplit {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      Algebra.IsFiniteSplit S (S ⊗[R] A) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) A = n
  · obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq A p.asIdeal
    obtain ⟨p', rfl⟩ : p ∈ Set.range
        (PrimeSpectrum.comap <| algebraMap R (Localization.Away r)) := by
      rwa [PrimeSpectrum.localization_away_comap_range _ r]
    obtain ⟨S, _, _, _, ho, ⟨q, rfl⟩, h⟩ := this p' ⟨_, hn⟩
    let _ : Algebra R S := Algebra.compHom S (algebraMap R (Localization.Away r))
    have : IsScalarTower R (Localization.Away r) S := IsScalarTower.of_algebraMap_eq' rfl
    let e : S ⊗[Localization.Away r] (Localization.Away r ⊗[R] A) ≃ₐ[S] S ⊗[R] A :=
      TensorProduct.cancelBaseChange ..
    refine ⟨S, inferInstance, inferInstance, ?_, ?_, ⟨q, rfl⟩, ?_⟩
    · exact Module.Flat.trans R (Localization.Away r) S
    · rw [IsScalarTower.algebraMap_eq R (Localization.Away r) S, PrimeSpectrum.comap_comp]
      exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap.comp ho
    · exact IsFiniteSplit.of_algEquiv (S := S ⊗[Localization.Away r]
        (Localization.Away r ⊗[R] A)) e
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, _, _, _, _, _, hS⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨p, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S) p
  have homap : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  refine ⟨S, inferInstance, inferInstance, ?_, homap, ⟨p, rfl⟩, hS⟩
  exact Module.Flat.trans _ S _

lemma exists_isSplit {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (f : A →ₐ[R] B) (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      (TensorProduct.map (AlgHom.id S S) f).IsSplit := by
  classical
  wlog hA : IsFiniteSplit R A
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isFiniteSplit p (A := A)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this (TensorProduct.map (.id S S) f) p hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · exact (AlgHom.IsSplit.iff_of_isScalarTower (S := S) (T := S') f).2 hS'
  wlog hB : IsFiniteSplit R B
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isFiniteSplit p (A := B)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this
      (A := S ⊗[R] A) (B := S ⊗[R] B) (R := S)
      (TensorProduct.map (.id S S) f) p inferInstance hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · exact (AlgHom.IsSplit.iff_of_isScalarTower (S := S) (T := S') f).2 hS'
  obtain ⟨n, ⟨eA⟩⟩ := hA
  obtain ⟨m, ⟨eB⟩⟩ := hB
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap
  · rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · let e := TensorProduct.piScalarRight R (Localization.Away r) (Localization.Away r) (Fin m)
    apply AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
      (TensorProduct.congr .refl eA |>.trans (TensorProduct.piScalarRight ..))
      (TensorProduct.congr .refl eB |>.trans (TensorProduct.piScalarRight ..)) σ
    ext a : 2
    simpa [TensorProduct.piScalarRight_tmul, f', e] using! congr(e ($(hσ) (1 ⊗ₜ eA a)))

end Algebra

end

lemma Algebra.FiniteEtale.equalizer_fun {R : Type u} {E F : Type} [CommRing R] [Finite E] [Finite F]
    (f g : (E → R) →ₐ[R] (F → R)) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  apply Algebra.FiniteEtale.of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, σ, τ, hσ, hτ⟩ := AlgHom.exists_cover_eq_compRight''₂ f g p
  use r, hr
  set A := Localization.Away r
  let f' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) f
  let g' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) g
  let cong₁ : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
    AlgHom.tensorEqualizerEquiv A A f g
  let T := AlgHom.equalizer
    (TensorProduct.map (.id A A) (.compRight R R σ))
    (TensorProduct.map (.id A A) (.compRight R R τ))
  let cong₂ : AlgHom.equalizer f' g' ≃ₐ[A] T := AlgHom.equalizerCongrOfEq hσ hτ
  let cong₃ : T ≃ₐ[A] A ⊗[R] AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ) :=
    (AlgHom.tensorEqualizerEquiv A A _ _).symm
  let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] A ⊗[R]
      AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ) :=
    cong₁.trans (cong₂.trans cong₃)
  have : FiniteEtale
      A (A ⊗[R] ↥(AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ))) := by
    constructor
  apply Algebra.FiniteEtale.of_equiv cong.symm

lemma Algebra.FiniteEtale.equalizer_of_isFiniteSplit {R S T : Type u} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra.IsFiniteSplit R S] [Algebra.IsFiniteSplit R T] (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  obtain ⟨n, ⟨eS⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  obtain ⟨m, ⟨eT⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R T
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (f.comp eS.symm)
  let g' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (g.comp eS.symm)
  have : Algebra.FiniteEtale R (AlgHom.equalizer f' g') :=
    Algebra.FiniteEtale.equalizer_fun f' g'
  let cong : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
    AlgHom.equalizerCongr eS eT (by ext; simp [f']) (by ext; simp [g'])
  exact Algebra.FiniteEtale.of_equiv cong.symm

lemma Algebra.FiniteEtale.equalizer_of_rankAtStalk_eq {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    {n m : ℕ} (hn : Module.rankAtStalk (R := R) S = n) (hm : Module.rankAtStalk (R := R) T = m)
    (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  wlog hS : Algebra.IsFiniteSplit R S
  · obtain ⟨A, _, _, _, _, _, hA⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (n := n) (m := m)
      · ext p
        rw [Module.rankAtStalk_baseChange, hn]
        rfl
      · ext p
        rw [Module.rankAtStalk_baseChange, hm]
        rfl
      exact hA
    have : Algebra.FiniteEtale A (A ⊗[R] AlgHom.equalizer f g) :=
      Algebra.FiniteEtale.of_equiv cong.symm
    exact Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat A
  clear n hn
  wlog hT : Algebra.IsFiniteSplit R T
  · obtain ⟨A, _, _, _, _, _, hA⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hm
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (m := m)
      · ext p
        rw [Module.rankAtStalk_baseChange, hm]
        rfl
      · infer_instance
      · exact hA
    have : Algebra.FiniteEtale A (A ⊗[R] AlgHom.equalizer f g) :=
      Algebra.FiniteEtale.of_equiv cong.symm
    exact Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat A
  apply Algebra.FiniteEtale.equalizer_of_isFiniteSplit

set_option maxHeartbeats 0 in
-- The rank-localization argument below follows the copied `pi1` proof and expands many tensor
-- and finite-split algebra identifications.
theorem Algebra.Etale.equalizer {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · apply Algebra.FiniteEtale.of_exists_of_isPrime
    intro p hp
    obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq S p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this
      use Module.rankAtStalk S ⟨p, hp⟩
    exact Algebra.FiniteEtale.of_equiv (S := AlgHom.equalizer f' g') cong.symm
  obtain ⟨n, hn⟩ := h
  wlog h : ∃ (m : ℕ), Module.rankAtStalk (R := R) T = m
  · apply Algebra.FiniteEtale.of_exists_of_isPrime
    intro p hp
    obtain ⟨r, hr, hm⟩ := Algebra.exists_cover_rankAtStalk_eq T p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (n := n)
      · ext p
        rw [Module.rankAtStalk_baseChange, hn]
        rfl
      · use (Module.rankAtStalk T ⟨p, hp⟩)
    exact Algebra.FiniteEtale.of_equiv (S := AlgHom.equalizer f' g') cong.symm
  obtain ⟨m, hm⟩ := h
  apply Algebra.FiniteEtale.equalizer_of_rankAtStalk_eq hn hm

section FinalTensorEqualizerHelpers

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g
local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

variable (R) in
/-- The equalizer of two algebra maps is unchanged by restricting scalars. -/
def _root_.AlgHom.equalizerRestrictScalars [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) :
    AlgHom.equalizer (f.restrictScalars R) (g.restrictScalars R) ≃ₐ[R]
      AlgHom.equalizer f g :=
  AlgEquiv.refl

@[simp]
lemma _root_.AlgHom.equalizerRestrictScalars_symm_apply [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) (x) :
    (AlgHom.equalizerRestrictScalars R f g).symm x = x :=
  rfl

set_option maxHeartbeats 0 in
-- The base-change cancellation equivalence expands several nested tensor-product algebra
-- structures; elaborating the scalar-tower instances needs an unbounded heartbeat budget.
variable (S) in
noncomputable def _root_.AlgHom.equalizerCancelBaseChange (f g : A →ₐ[R] B)
    (T : Type u) [CommRing T] [Algebra R T] :
    (((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g))) ≃ₐ[T]
      (((T ⊗[R] S) ⊗ₘ f) ≟ₐ ((T ⊗[R] S) ⊗ₘ g)) :=
  AlgHom.equalizerCongr
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) A)
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) B)
    (by ext; simp) (by ext; simp) |>.restrictScalars T

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_algebraMap (f g : A →ₐ[R] B)
    (T : Type u) [CommRing T] [Algebra R T] (x : T ⊗[R] S) :
    AlgHom.equalizerCancelBaseChange S f g T (algebraMap _ _ x) = algebraMap _ _ x := by
  simp [AlgHom.equalizerCancelBaseChange]

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_tmul (f g : A →ₐ[R] B)
    (T : Type u) [CommRing T] [Algebra R T] (x : A)
    (hx : x ∈ AlgHom.equalizer f g) :
    ((AlgHom.equalizerCancelBaseChange S f g T)
      ⟨1 ⊗ₜ[T] (1 ⊗ₜ[R] x), by simp [show f x = g x from hx]⟩) =
        ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ := by
  ext : 1
  simp [AlgHom.equalizerCancelBaseChange, AlgHom.equalizerCongr_apply]

/-- A generator computation for the flat equalizer comparison. -/
lemma _root_.AlgHom.tensorEqualizerEquiv_symm_apply
    {R : Type*} (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) [Module.Flat R T]
    (x : A) (hx : x ∈ AlgHom.equalizer f g) :
    (f.tensorEqualizerEquiv S T g).symm ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ =
      1 ⊗ₜ ⟨x, hx⟩ := by
  apply (f.tensorEqualizerEquiv S T g).injective
  ext
  simp

set_option maxHeartbeats 0 in
-- The middle step in the nested flat base-change equivalence expands associativity and
-- restricts scalars; keeping it named makes the generator computations tractable.
noncomputable def auxEquivRHSCore (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] :
      ↥(TensorProduct.map (.id T T) (TensorProduct.map (.id R S) f) ≟ₐ
        TensorProduct.map (.id T T) (TensorProduct.map (.id R S) g)) ≃ₐ[T]
      ↥(TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) f ≟ₐ
        TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) g) :=
    .trans
      (AlgHom.equalizerCongr
        (TensorProduct.assoc' R T T S A).symm
        (TensorProduct.assoc' R T T S B).symm
        (by ext <;> simp) (by ext <;> simp))
      (AlgHom.equalizerRestrictScalars T _ _)

set_option maxHeartbeats 0 in
-- This is the nested flat base-change equivalence from upstream `KerTensor`.
noncomputable def auxEquivRHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] [Module.Flat R T] :
    T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g)) :=
  (TensorProduct.map (.id R S) f).tensorEqualizerEquiv T T
      (TensorProduct.map (.id R S) g) |>.trans (auxEquivRHSCore f g T) |>.trans
    (f.equalizerCancelBaseChange S g T).symm

set_option maxHeartbeats 0 in
-- This generator computation unfolds a three-step `AlgEquiv.trans`; the explicit proof avoids
-- repeated `whnf` timeouts in the simplifier.
lemma auxEquivRHS_symm_tmul (f g : A →ₐ[R] B) (T : Type u)
    [CommRing T] [Algebra R T] [Module.Flat R T] (x : S) :
    (auxEquivRHS (S := S) f g T).symm (algebraMap (T ⊗[R] S) _ (1 ⊗ₜ x)) =
      1 ⊗ₜ algebraMap _ _ x := by
  let eTE := (TensorProduct.map (.id R S) f).tensorEqualizerEquiv T T
      (TensorProduct.map (.id R S) g)
  let eCore := auxEquivRHSCore (S := S) f g T
  let eCancel := AlgHom.equalizerCancelBaseChange S f g T
  let y := algebraMap (T ⊗[R] S)
      (((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g))) (1 ⊗ₜ[R] x)
  change (eTE.trans eCore |>.trans eCancel.symm).symm y =
      1 ⊗ₜ[R] (algebraMap S ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) x)
  have hchange : (eTE.trans eCore |>.trans eCancel.symm).symm y =
      eTE.symm (eCore.symm (eCancel y)) := rfl
  rw [hchange]
  subst eTE
  subst eCore
  subst eCancel
  subst y
  rw [AlgHom.equalizerCancelBaseChange_algebraMap]
  have hcore : (auxEquivRHSCore (S := S) f g T).symm
      (algebraMap (T ⊗[R] S) _ (1 ⊗ₜ[R] x)) =
      ⟨1 ⊗ₜ[R] (x ⊗ₜ[R] (1 : A)), by simp⟩ := by
    ext : 1
    simp [auxEquivRHSCore, AlgHom.equalizerCongr_symm_apply]
  rw [hcore]
  let fS : S ⊗[R] A →ₐ[R] S ⊗[R] B := TensorProduct.map (.id R S) f
  let gS : S ⊗[R] A →ₐ[R] S ⊗[R] B := TensorProduct.map (.id R S) g
  have h := AlgHom.tensorEqualizerEquiv_symm_apply (S := T) (T := T) fS gS
    (algebraMap S (S ⊗[R] A) x) (by simp [fS, gS])
  simpa [fS, gS] using! h

set_option maxHeartbeats 0 in
-- As above, but for the equalizer generator coming from `A` rather than from the scalar algebra.
lemma auxEquivRHS_symm_tmul' (f g : A →ₐ[R] B) (T : Type u)
    [CommRing T] [Algebra R T] [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivRHS (S := S) f g T).symm
      ⟨1 ⊗ₜ (1 ⊗ₜ x), by simp [show f x = g x from x.2]⟩ =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x = g x from x.2]⟩ := by
  let eTE := (TensorProduct.map (.id R S) f).tensorEqualizerEquiv T T
      (TensorProduct.map (.id R S) g)
  let eCore := auxEquivRHSCore (S := S) f g T
  let eCancel := AlgHom.equalizerCancelBaseChange S f g T
  let y : ↥(AlgHom.equalizer
      (TensorProduct.map (AlgHom.id (T ⊗[R] S) (T ⊗[R] S))
        (TensorProduct.map (AlgHom.id T T) f))
      (TensorProduct.map (AlgHom.id (T ⊗[R] S) (T ⊗[R] S))
        (TensorProduct.map (AlgHom.id T T) g))) :=
    ⟨1 ⊗ₜ[T] (1 ⊗ₜ[R] (x : A)), by simp [show f x.1 = g x.1 from x.2]⟩
  change (eTE.trans eCore |>.trans eCancel.symm).symm y =
      1 ⊗ₜ[R] (⟨1 ⊗ₜ[R] (x : A), by simp [show f x.1 = g x.1 from x.2]⟩ :
        ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)))
  have hchange : (eTE.trans eCore |>.trans eCancel.symm).symm y =
      eTE.symm (eCore.symm (eCancel y)) := rfl
  rw [hchange]
  subst eTE
  subst eCore
  subst eCancel
  subst y
  rw [AlgHom.equalizerCancelBaseChange_tmul (S := S) (f := f) (g := g) (T := T)
    (x := (x : A)) (hx := x.2)]
  have hcore : (auxEquivRHSCore (S := S) f g T).symm
      ⟨(1 : T ⊗[R] S) ⊗ₜ[R] (x : A),
        by simp [show f x = g x from x.2]⟩ =
      ⟨1 ⊗ₜ[R] (1 ⊗ₜ[R] (x : A)), by simp [show f x = g x from x.2]⟩ := by
    ext : 1
    change (TensorProduct.assoc' R T T S A)
        (((1 : T) ⊗ₜ[R] (1 : S)) ⊗ₜ[R] (x : A)) =
      (1 : T) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (x : A))
    rw [TensorProduct.assoc'_tmul]
  rw [hcore]
  let fS : S ⊗[R] A →ₐ[R] S ⊗[R] B := TensorProduct.map (.id R S) f
  let gS : S ⊗[R] A →ₐ[R] S ⊗[R] B := TensorProduct.map (.id R S) g
  have hx : (1 ⊗ₜ[R] (x : A)) ∈ AlgHom.equalizer fS gS := by
    simp [fS, gS, show f x.1 = g x.1 from x.2]
  have h := AlgHom.tensorEqualizerEquiv_symm_apply (S := T) (T := T) fS gS
    (1 ⊗ₜ[R] (x : A)) hx
  simpa [fS, gS] using! h

noncomputable def auxEquivLHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] [Module.Flat R T] :
    T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T]
      (T ⊗[R] S) ⊗[T] ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
  .trans
    (.trans
      (TensorProduct.assoc' R T T S (f ≟ₐ g)).symm
      (TensorProduct.cancelBaseChange R T T (T ⊗[R] S) (f ≟ₐ g)).symm)
    (TensorProduct.congr .refl (f.tensorEqualizerEquiv T T g))

@[simp]
lemma auxEquivLHS_one_tmul_one (f g : A →ₐ[R] B) (T : Type u)
    [CommRing T] [Algebra R T] [Module.Flat R T] (x : S) :
    auxEquivLHS f g T (1 ⊗ₜ[R] (x ⊗ₜ[R] 1)) = (1 ⊗ₜ x) ⊗ₜ 1 :=
  rfl

lemma auxEquivLHS_one_one_tmul (f g : A →ₐ[R] B) (T : Type u)
    [CommRing T] [Algebra R T] [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivLHS (S := S) f g T) (1 ⊗ₜ[R] (1 ⊗ₜ[R] x)) =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma tensorEqualizer_compRight_bijective {E F : Type*} [Finite E] [Finite F]
    (σ τ : E → F) :
    Function.Bijective ((AlgHom.compRight R R σ).tensorEqualizer S S (.compRight R R τ)) := by
  classical
  cases nonempty_fintype E
  cases nonempty_fintype F
  cases nonempty_fintype (Function.Coequalizer σ τ)
  set f : (F → R) →ₐ[R] E → R := AlgHom.compRight R R σ
  set g : (F → R) →ₐ[R] E → R := AlgHom.compRight R R τ
  let eL : S ⊗[R] (F → R) ≃ₐ[S] F → S :=
    Algebra.TensorProduct.piScalarRight R S S F
  let eR : S ⊗[R] (E → R) ≃ₐ[S] E → S :=
    Algebra.TensorProduct.piScalarRight R S S E
  let eq₂ : S ⊗[R] (Function.Coequalizer σ τ → R) ≃ₐ[S]
      Function.Coequalizer σ τ → S :=
    Algebra.TensorProduct.piScalarRight R S S (Function.Coequalizer σ τ)
  let e₁ := AlgHom.equalizerCompRightEquiv R R σ τ
  let e₂ := AlgHom.equalizerCompRightEquiv S S σ τ
  let _ : AddCommMonoid ↥(f ≟ₐ g) := AddCommGroup.toAddCommMonoid
  let eq₁ : S ⊗[R] (f ≟ₐ g) ≃ₐ[S]
      S ⊗[R] (Function.Coequalizer σ τ → R) :=
    TensorProduct.congr AlgEquiv.refl e₁
  let eq₃ : ↥(TensorProduct.map (AlgHom.id S S) f ≟ₐ
        TensorProduct.map (AlgHom.id S S) g) ≃ₐ[S]
      (AlgHom.compRight S S σ) ≟ₐ (AlgHom.compRight S S τ) :=
    AlgHom.equalizerCongr eL eR (by ext; simp [eL, eR, f]) (by ext; simp [eL, eR, g])
  have : AlgHom.tensorEqualizer S S f g =
      AlgHom.comp (.comp (.comp eq₃.symm.toAlgHom e₂.symm.toAlgHom)
        eq₂.toAlgHom) eq₁.toAlgHom := by
    ext x
    apply (TensorProduct.piScalarRight R S S F).injective
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      TensorProduct.includeRight_apply, AlgHom.coe_tensorEqualizer, TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, Subalgebra.coe_val, TensorProduct.piScalarRight_tmul, smul_def,
      mul_one, AlgEquiv.coe_toAlgHom, TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      AlgHom.equalizerCongr_symm_apply, AlgEquiv.apply_symm_apply, eq₃, eL, e₂, eq₂, eq₁, e₁]
    ext i
    rw [AlgHom.equalizerCompRightEquiv_symm_apply, AlgHom.equalizerCompRightEquiv_apply]
  rw [this]
  dsimp
  exact eq₃.symm.bijective.comp (e₂.symm.bijective.comp <| eq₂.bijective.comp eq₁.bijective)

end Algebra

set_option maxHeartbeats 0 in
-- Elaborating the tensor-product congruence here requires a large typeclass search through
-- scalar-tower algebra structures.
lemma TensorProduct.map_bijective_of_bijective {R S A B C D : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    [Algebra S C] [IsScalarTower R S C] [Semiring D] [Algebra R D]
    {f : A →ₐ[S] C} {g : B →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (Algebra.TensorProduct.map f g) :=
  (Algebra.TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

namespace AlgHom

lemma tensorEqualizer_tmul_one (f g : A →ₐ[R] B) (x : S) :
    f.tensorEqualizer S S g (x ⊗ₜ 1) = algebraMap S _ x :=
  rfl

lemma tensorEqualizer_one_tmul {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : AlgHom.equalizer f g) :
    f.tensorEqualizer S T g (1 ⊗ₜ x) = ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma tensorEqualizer_tmul_one' {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : T) :
    f.tensorEqualizer S T g (x ⊗ₜ 1) = ⟨x ⊗ₜ 1, by simp⟩ :=
  rfl

end AlgHom

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g
local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

set_option maxHeartbeats 0 in
-- The key naturality comparison: after a flat base change by `T`, bijectivity of the
-- tensor-equalizer map is equivalent to bijectivity of the tensor-equalizer map after base change.
variable (S) in
lemma TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective
    (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    Function.Bijective ⇑(TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g)) ↔
    Function.Bijective
            ((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
                  (TensorProduct.map (.id T T) g)) := by
  let eLHS : T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T] (T ⊗[R] S) ⊗[T]
      ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
    auxEquivLHS f g T
  let eRHS : T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g)) :=
    auxEquivRHS f g T
  have : IsScalarTower R T
      (T ⊗[R] ↥(TensorProduct.map (AlgHom.id R S) f ≟ₐ
        TensorProduct.map (AlgHom.id R S) g)) :=
    TensorProduct.isScalarTower_left
  let u := (TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
    (TensorProduct.map (.id T T) g)
  have heq : TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g) =
      eRHS.symm.toAlgHom.comp
        (((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
            (TensorProduct.map (.id T T) g)).comp
          eLHS.toAlgHom) := by
    ext x
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        Function.comp_apply, TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply,
        AlgHom.coe_restrictScalars']
      erw [AlgHom.comp_apply]
      erw [AlgHom.comp_apply]
      simp only [AlgEquiv.coe_toAlgHom, auxEquivLHS_one_tmul_one, eLHS]
      change 1 ⊗ₜ[R] (AlgHom.tensorEqualizer S S f g) (x ⊗ₜ 1) = eRHS.symm
        ((AlgHom.tensorEqualizer (T ⊗[R] S) (T ⊗[R] S)
          (TensorProduct.map (AlgHom.id T T) f) (TensorProduct.map (AlgHom.id T T) g))
          ((1 ⊗ₜ[R] x) ⊗ₜ[T] 1))
      rw [AlgHom.tensorEqualizer_tmul_one, AlgHom.tensorEqualizer_tmul_one,
        auxEquivRHS_symm_tmul]
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, TensorProduct.includeRight_apply,
        eLHS]
      erw [AlgHom.comp_apply]
      erw [AlgHom.comp_apply]
      simp only [AlgEquiv.coe_toAlgHom]
      rw [auxEquivLHS_one_one_tmul]
      rw [AlgHom.tensorEqualizer_one_tmul]
      rw [AlgHom.tensorEqualizer_one_tmul]
      change 1 ⊗ₜ[R] (⟨1 ⊗ₜ[R] (x : A), by simp [show f x.1 = g x.1 from x.2]⟩ :
        ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g))) =
          eRHS.symm ⟨1 ⊗ₜ[T] (1 ⊗ₜ[R] (x : A)),
            by simp [show f x.1 = g x.1 from x.2]⟩
      rw [show eRHS = auxEquivRHS f g T by rfl]
      rw [auxEquivRHS_symm_tmul']
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [heq] at H
    change Function.Bijective (⇑eRHS.symm ∘
      (⇑(AlgHom.tensorEqualizer T (T ⊗[R] S) (TensorProduct.map (AlgHom.id T T) f)
          (TensorProduct.map (AlgHom.id T T) g)) ∘ ⇑eLHS)) at H
    have H' : Function.Bijective
        (⇑(AlgHom.tensorEqualizer T (T ⊗[R] S) (TensorProduct.map (AlgHom.id T T) f)
          (TensorProduct.map (AlgHom.id T T) g)) ∘ ⇑eLHS) :=
      (Function.Bijective.of_comp_iff' eRHS.symm.bijective _).1 H
    exact (Function.Bijective.of_comp_iff
      (⇑(AlgHom.tensorEqualizer T (T ⊗[R] S) (TensorProduct.map (AlgHom.id T T) f)
          (TensorProduct.map (AlgHom.id T T) g)) : _ → _) eLHS.bijective).1 H'
  · rw [heq]
    apply eRHS.symm.bijective.comp
    exact H.comp eLHS.bijective

lemma tensorEqualizer_comp_comp {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] {A A' : Type*} {B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra R A] [Algebra R A']
    [Algebra R B] [Algebra R B'] (f g : A' →ₐ[R] B')
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') :
    AlgHom.tensorEqualizer S T
      (eB.symm.toAlgHom.comp (f.comp eA.toAlgHom))
      (eB.symm.toAlgHom.comp (g.comp eA.toAlgHom)) =
        AlgHom.comp
          (AlgHom.equalizerCongr
            (TensorProduct.congr .refl eA.symm)
            (TensorProduct.congr .refl eB.symm)
            (by ext <;> simp) (by ext <;> simp)).toAlgHom
          (AlgHom.comp (AlgHom.tensorEqualizer S T f g)
          (TensorProduct.congr .refl
            (AlgHom.equalizerCongr eA eB (by ext; simp) (by ext; simp))).toAlgHom) := by
  ext t
  · simp [AlgHom.tensorEqualizer_tmul_one', AlgHom.equalizerCongr_apply]
  · simp [AlgHom.tensorEqualizer_one_tmul, AlgHom.equalizerCongr_apply]

end Algebra

end FinalTensorEqualizerHelpers

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g

-- The finite-split/codescent proof repeatedly elaborates nested tensor-product scalar towers.
/-- The natural map `S ⊗[R] eq(f, g) →ₐ[S] eq(S ⊗ f, S ⊗ g)` is an isomorphism
for arbitrary `S` if `A` and `B` are finite étale over `R`.

This is adapted from upstream `pi1`, `Pi1/RingTheory/KerTensor.lean`. -/
nonrec theorem tensorEqualizer_bijective_of_finite_of_etale {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A →ₐ[R] B) [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] :
    Function.Bijective (f.tensorEqualizer R S g) := by
  wlog hf : f.IsSplit
  · apply RingHom.FaithfullyFlat.codescendsAlong_bijective.algHom_of_forall_exists_flat
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨T, _, _, _, ho, hmem, hf⟩ := exists_isSplit f p
      refine ⟨T, inferInstance, inferInstance, hmem, inferInstance, ho.isOpen_range, ?_⟩
      apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
      apply this
      exact hf
  obtain ⟨n, m, eA, eB, σ, rfl⟩ := hf
  let g' : (Fin n → R) →ₐ[R] (Fin m → R) :=
    eB.toAlgHom.comp (g.comp eA.symm.toAlgHom)
  have : g = eB.symm.toAlgHom.comp (g'.comp eA.toAlgHom) := by ext; simp [g']
  rw [this]
  have : Function.Bijective (AlgHom.tensorEqualizer R S (.compRight R R σ) g') := by
    let _ : AddCommMonoid ↥(AlgHom.compRight R R σ ≟ₐ g') := AddCommGroup.toAddCommMonoid
    let _ : CommRing (S ⊗[R] ↥(AlgHom.compRight R R σ ≟ₐ g')) := inferInstance
    apply RingHom.FaithfullyFlat.codescendsAlong_bijective.algHom_of_forall_exists_flat
      (B := TensorProduct.map (AlgHom.id R S) (.compRight R R σ) ≟ₐ
        TensorProduct.map (.id R S) g')
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨r, hr, τ, h⟩ := AlgHom.exists_cover_eq_compRight'' g' p.asIdeal
      refine ⟨Localization.Away r, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
      · change p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact hr
      · change IsOpen <| Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact PrimeSpectrum.isOpen_basicOpen
      · apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
        rw [h]
        apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mp
        apply TensorProduct.map_bijective_of_bijective
        · exact Function.bijective_id
        apply tensorEqualizer_compRight_bijective
  erw [tensorEqualizer_comp_comp]
  dsimp
  apply Function.Bijective.comp
  · apply AlgEquiv.bijective
  apply Function.Bijective.comp
  · exact this
  apply AlgEquiv.bijective

end Algebra
