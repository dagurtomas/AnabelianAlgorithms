/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.Basic
public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.SplitPrime
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed


/-!
# Finite quotients and centers of absolute Galois groups

This file contains the profinite/group-theoretic reduction used in the proof that number-field
absolute Galois groups have trivial center, together with the first finite Kummer-theoretic setup
used by the arithmetic part of the proof.
-/

@[expose] public section

universe u

namespace NumberField

open IntermediateField Polynomial

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']

/--
The finite Galois intermediate field which is the image of a finite Galois extension under a
`K`-algebra embedding into `K'`.
-/
noncomputable def finiteGaloisIntermediateOfAlgHom {M : Type u} [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (f : M →ₐ[K] K') :
    FiniteGaloisIntermediateField K K' := by
  refine { toIntermediateField := f.fieldRange, finiteDimensional := ?_, isGalois := ?_ }
  · exact f.equivFieldRange.toLinearEquiv.finiteDimensional
  · haveI : Algebra.IsSeparable K f.fieldRange := AlgEquiv.Algebra.isSeparable f.equivFieldRange
    haveI : Normal K f.fieldRange := Normal.of_algEquiv f.equivFieldRange
    exact (isGalois_iff (F := K) (E := f.fieldRange)).mpr ⟨inferInstance, inferInstance⟩

@[simp]
theorem finiteGaloisIntermediateOfAlgHom_toIntermediateField {M : Type u}
    [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M] (f : M →ₐ[K] K') :
    (finiteGaloisIntermediateOfAlgHom (K := K) (K' := K') f).toIntermediateField =
      f.fieldRange :=
  rfl

/--
Realize an abstract finite Galois extension `M / K` as a finite Galois intermediate field of the
chosen separable closure `K' / K`.
-/
noncomputable def finiteGaloisIntermediateOfExtension
    {K K' M : Type u} [Field K] [Field K'] [Field M]
    [Algebra K K'] [IsSepClosure K K'] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] :
    FiniteGaloisIntermediateField K K' := by
  letI : IsSepClosed K' := IsSepClosure.sep_closed K
  exact finiteGaloisIntermediateOfAlgHom (K := K) (K' := K')
    (IsSepClosed.lift : M →ₐ[K] K')

@[simp]
theorem finiteGaloisIntermediateOfExtension_toIntermediateField
    {K K' M : Type u} [Field K] [Field K'] [Field M]
    [Algebra K K'] [IsSepClosure K K'] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] :
    (finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M)).toIntermediateField =
      (letI : IsSepClosed K' := IsSepClosure.sep_closed K
       (IsSepClosed.lift : M →ₐ[K] K')).fieldRange := by
  rw [finiteGaloisIntermediateOfExtension]
  rfl

/-- For a normal abstract extension, all `K`-embeddings into the same ambient field have the same
image. -/
theorem algHom_fieldRange_eq_of_isGalois {M : Type u} [Field M] [Algebra K M]
    [IsGalois K M] (f g : M →ₐ[K] K') :
    f.fieldRange = g.fieldRange := by
  let e : M ≃ₐ[K] f.fieldRange := f.equivFieldRange
  haveI : Normal K f.fieldRange := Normal.of_algEquiv e
  let h : f.fieldRange →ₐ[K] K' := g.comp e.symm.toAlgHom
  have hh : h.fieldRange = f.fieldRange := AlgHom.fieldRange_of_normal h
  have hgf : h.fieldRange = g.fieldRange := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [h, e]⟩
  exact hh.symm.trans hgf

/-- The finite intermediate field obtained from an abstract finite Galois extension is independent
of the chosen embedding into `K'`. -/
theorem finiteGaloisIntermediateOfAlgHom_eq {M : Type u} [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (f g : M →ₐ[K] K') :
    finiteGaloisIntermediateOfAlgHom (K := K) (K' := K') f =
      finiteGaloisIntermediateOfAlgHom (K := K) (K' := K') g := by
  apply FiniteGaloisIntermediateField.val_injective
  exact algHom_fieldRange_eq_of_isGalois f g

/-- Compare the canonical realization with the image of any specified embedding. -/
theorem finiteGaloisIntermediateOfExtension_eq_of_algHom
    {K K' M : Type u} [Field K] [Field K'] [Field M]
    [Algebra K K'] [IsSepClosure K K'] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (f : M →ₐ[K] K') :
    finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M) =
      finiteGaloisIntermediateOfAlgHom (K := K) (K' := K') f := by
  letI : IsSepClosed K' := IsSepClosure.sep_closed K
  exact finiteGaloisIntermediateOfAlgHom_eq (K := K) (K' := K')
    (IsSepClosed.lift : M →ₐ[K] K') f

/--
A finite Galois extension `M / K` containing an already embedded finite Galois intermediate field
`L` admits an embedding into the chosen separable closure extending the inclusion of `L`.
-/
theorem exists_algHom_to_sepClosure_extending
    {M : Type u} [Field M] [Algebra K M] [IsSepClosure K K'] [IsGalois K M]
    (L : FiniteGaloisIntermediateField K K') (i : L →ₐ[K] M) :
    ∃ φ : M →ₐ[K] K', φ.comp i = L.val := by
  letI : Algebra L M := RingHom.toAlgebra i.toRingHom
  have h_tower : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      exact (i.commutes x).symm
  letI : IsScalarTower K L M := h_tower
  haveI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  letI : IsSepClosed K' := IsSepClosure.sep_closed K
  obtain ⟨φ, hφ⟩ :=
    IsSepClosed.surjective_restrictDomain_of_isSeparable (K := K) (L := L) (M := K') (E := M)
      L.val
  exact ⟨φ, by
    ext x
    exact congrFun (congrArg DFunLike.coe hφ) x⟩

/--
The realization of `M` in `K'` can be chosen compatibly with an already chosen finite Galois
intermediate field `L`: if `L` embeds in `M` over `K`, then the canonical realized intermediate
field attached to `M` contains `L`.
-/
theorem le_finiteGaloisIntermediateOfExtension_of_algHom
    {M : Type u} [Field M] [Algebra K M] [IsSepClosure K K']
    [FiniteDimensional K M] [IsGalois K M]
    (L : FiniteGaloisIntermediateField K K') (i : L →ₐ[K] M) :
    L ≤ finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M) := by
  obtain ⟨φ, hφ⟩ := exists_algHom_to_sepClosure_extending (K := K) (K' := K') (M := M) L i
  rw [finiteGaloisIntermediateOfExtension_eq_of_algHom (K := K) (K' := K') (M := M) φ,
    FiniteGaloisIntermediateField.le_iff]
  intro x hx
  change x ∈ φ.fieldRange
  exact ⟨i ⟨x, hx⟩, by
    have h := congrFun (congrArg DFunLike.coe hφ) ⟨x, hx⟩
    simpa using h⟩

/--
A compatible algebra equivalence from the abstract extension to its realized intermediate field.
-/
theorem exists_algEquiv_finiteGaloisIntermediateOfExtension_extends
    {M : Type u} [Field M] [Algebra K M] [IsSepClosure K K']
    [FiniteDimensional K M] [IsGalois K M]
    (L : FiniteGaloisIntermediateField K K') (i : L →ₐ[K] M) :
    ∃ e : M ≃ₐ[K] finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M),
      ∀ x : L, (e (i x) : K') = x := by
  obtain ⟨φ, hφ⟩ := exists_algHom_to_sepClosure_extending (K := K) (K' := K') (M := M) L i
  let hEq : φ.fieldRange =
      (finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M)).toIntermediateField := by
    rw [finiteGaloisIntermediateOfExtension_eq_of_algHom (K := K) (K' := K') (M := M) φ]
    rfl
  refine ⟨φ.equivFieldRange.trans (IntermediateField.equivOfEq hEq), ?_⟩
  intro x
  have h := congrFun (congrArg DFunLike.coe hφ) x
  simpa [hEq] using h

/--
Data for the odd-root Kummer setup over a finite Galois number-field extension.

The field `Lζ` is a finite Galois extension of `K` containing `L` and a primitive `ell`-th root of
unity, and `τζ` is an actual lift of the prescribed automorphism `τ`.
-/
structure OddKummerSetup (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) where
  ell : ℕ
  ell_prime : ell.Prime
  ell_ne_two : ell ≠ 2
  Lζ : Type u
  [field_Lζ : Field Lζ]
  [numberField_Lζ : NumberField Lζ]
  [algebra_K_Lζ : Algebra K Lζ]
  [algebra_L_Lζ : Algebra L Lζ]
  [tower : IsScalarTower K L Lζ]
  [isGalois_K_Lζ : IsGalois K Lζ]
  primitiveRoot : (primitiveRoots ell Lζ).Nonempty
  τζ : Gal(Lζ/K)
  restrict_τζ : τζ.restrictNormalHom L = τ

attribute [instance] OddKummerSetup.field_Lζ OddKummerSetup.numberField_Lζ
  OddKummerSetup.algebra_K_Lζ OddKummerSetup.algebra_L_Lζ OddKummerSetup.tower
  OddKummerSetup.isGalois_K_Lζ

section OddKummerSetup

variable {L : Type u} [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- A chosen primitive third root of unity in an algebraic closure of `L`. -/
noncomputable def oddKummerZeta : AlgebraicClosure L :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure L) 3).choose

theorem oddKummerZeta_isPrimitiveRoot :
    IsPrimitiveRoot (oddKummerZeta (L := L)) 3 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure L) 3).choose_spec

/-- The embedded copy of `L` in `AlgebraicClosure L`, viewed as an intermediate field over `K`. -/
noncomputable def oddKummerEmbeddedL : IntermediateField K (AlgebraicClosure L) :=
  (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).fieldRange

/-- The field generated over `K` by the chosen primitive third root of unity. -/
noncomputable def oddKummerZetaField : IntermediateField K (AlgebraicClosure L) :=
  IntermediateField.adjoin K ({oddKummerZeta (L := L)} : Set (AlgebraicClosure L))

/-- The finite extension of `K` generated by the embedded `L` and the chosen root of unity. -/
noncomputable def oddKummerBaseField : IntermediateField K (AlgebraicClosure L) :=
  oddKummerEmbeddedL (K := K) (L := L) ⊔ oddKummerZetaField (K := K) (L := L)

/-- The normal closure over `K` of `L` with a primitive third root of unity adjoined. -/
noncomputable abbrev oddKummerField : Type u :=
  normalClosure K (oddKummerBaseField (K := K) (L := L)) (AlgebraicClosure L)

omit [IsGalois K L]
theorem finiteDimensional_oddKummerEmbeddedL :
    FiniteDimensional K (oddKummerEmbeddedL (K := K) (L := L)) := by
  unfold oddKummerEmbeddedL
  exact (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).equivFieldRange.toLinearEquiv
    |>.finiteDimensional

omit [IsGalois K L]
theorem finiteDimensional_oddKummerZetaField :
    FiniteDimensional K (oddKummerZetaField (K := K) (L := L)) := by
  unfold oddKummerZetaField
  exact IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) (oddKummerZeta (L := L)))

theorem finiteDimensional_oddKummerBaseField :
    FiniteDimensional K (oddKummerBaseField (K := K) (L := L)) := by
  unfold oddKummerBaseField
  haveI := finiteDimensional_oddKummerEmbeddedL (K := K) (L := L)
  haveI := finiteDimensional_oddKummerZetaField (K := K) (L := L)
  infer_instance

theorem finiteDimensional_oddKummerField :
    FiniteDimensional K (oddKummerField (K := K) (L := L)) := by
  dsimp [oddKummerField]
  haveI := finiteDimensional_oddKummerBaseField (K := K) (L := L)
  exact normalClosure.is_finiteDimensional K (oddKummerBaseField (K := K) (L := L))
    (AlgebraicClosure L)

/-- The inclusion of `L` into the normal closure used for the odd Kummer setup. -/
@[reducible]
noncomputable def oddKummerAlgebraL :
    Algebra L (oddKummerField (K := K) (L := L)) := by
  dsimp [oddKummerField]
  let hL : oddKummerEmbeddedL (K := K) (L := L) ≤
      normalClosure K (oddKummerBaseField (K := K) (L := L)) (AlgebraicClosure L) :=
    le_trans (by
      unfold oddKummerBaseField
      exact le_sup_left) (IntermediateField.le_normalClosure _)
  exact RingHom.toAlgebra
    (((IsScalarTower.toAlgHom K L (AlgebraicClosure L)).codRestrict _ fun x ↦ hL ⟨x, rfl⟩)
      |>.toRingHom)

omit [NumberField K] in
theorem oddKummerTower :
    letI : Algebra L (oddKummerField (K := K) (L := L)) :=
      oddKummerAlgebraL (K := K) (L := L)
    IsScalarTower K L (oddKummerField (K := K) (L := L)) := by
  letI : Algebra L (oddKummerField (K := K) (L := L)) :=
    oddKummerAlgebraL (K := K) (L := L)
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change algebraMap K (AlgebraicClosure L) x =
    algebraMap L (AlgebraicClosure L) (algebraMap K L x)
  simp [IsScalarTower.algebraMap_apply K L (AlgebraicClosure L)]

omit [NumberField K] in
theorem oddKummerZeta_mem_field :
    oddKummerZeta (L := L) ∈
      (normalClosure K (oddKummerBaseField (K := K) (L := L)) (AlgebraicClosure L) :
        IntermediateField K (AlgebraicClosure L)) := by
  apply IntermediateField.le_normalClosure (oddKummerBaseField (K := K) (L := L))
  unfold oddKummerBaseField oddKummerZetaField
  exact (le_sup_right : oddKummerZetaField (K := K) (L := L) ≤
      oddKummerEmbeddedL (K := K) (L := L) ⊔ oddKummerZetaField (K := K) (L := L))
    (IntermediateField.subset_adjoin K ({oddKummerZeta (L := L)} : Set (AlgebraicClosure L))
      (by simp))

omit [NumberField K] in
theorem oddKummerPrimitiveRoot :
    (primitiveRoots 3 (oddKummerField (K := K) (L := L))).Nonempty := by
  refine ⟨⟨oddKummerZeta (L := L), oddKummerZeta_mem_field (K := K) (L := L)⟩, ?_⟩
  rw [mem_primitiveRoots (by decide : 0 < 3)]
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
  exact oddKummerZeta_isPrimitiveRoot (L := L)

/--
Construct the NCT3 odd-root Kummer setup, using the fixed odd prime `3`.

The extension is the normal closure over `K` inside `AlgebraicClosure L` of the compositum of the
embedded copy of `L` and a primitive third root of unity.  The lift of `τ` is the normal-extension
lift, so its restriction to `L` is definitionally the standard `restrict_liftNormal` theorem.
-/
noncomputable def oddKummerSetup (τ : Gal(L/K)) : OddKummerSetup K L τ where
  ell := 3
  ell_prime := by decide
  ell_ne_two := by decide
  Lζ := oddKummerField (K := K) (L := L)
  field_Lζ := inferInstance
  numberField_Lζ := by
    haveI := finiteDimensional_oddKummerField (K := K) (L := L)
    exact NumberField.of_module_finite K (oddKummerField (K := K) (L := L))
  algebra_K_Lζ := inferInstance
  algebra_L_Lζ := oddKummerAlgebraL (K := K) (L := L)
  tower := oddKummerTower (K := K) (L := L)
  isGalois_K_Lζ := by
    dsimp [oddKummerField]
    exact IsGalois.normalClosure K (oddKummerBaseField (K := K) (L := L)) (AlgebraicClosure L)
  primitiveRoot := oddKummerPrimitiveRoot (K := K) (L := L)
  τζ := by
    letI : Algebra L (oddKummerField (K := K) (L := L)) :=
      oddKummerAlgebraL (K := K) (L := L)
    letI : IsScalarTower K L (oddKummerField (K := K) (L := L)) :=
      oddKummerTower (K := K) (L := L)
    exact τ.liftNormal (oddKummerField (K := K) (L := L))
  restrict_τζ := by
    letI : Algebra L (oddKummerField (K := K) (L := L)) :=
      oddKummerAlgebraL (K := K) (L := L)
    letI : IsScalarTower K L (oddKummerField (K := K) (L := L)) :=
      oddKummerTower (K := K) (L := L)
    exact τ.restrict_liftNormal (oddKummerField (K := K) (L := L))

/--
Replace the chosen lift in an odd Kummer setup by another lift over the same cyclotomic field.
-/
noncomputable def retargetOddKummerSetup
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (σ : Gal(S.Lζ/K))
    (hσ : σ.restrictNormalHom L = τ) : OddKummerSetup K L τ :=
  { S with τζ := σ, restrict_τζ := hσ }

end OddKummerSetup

section CyclotomicExponent

variable {L : Type u} [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] {τ : Gal(L/K)}

/-- The cyclotomic exponent by which `S.τζ` acts on a chosen primitive root of unity. -/
noncomputable def cyclotomicExponent
    (S : OddKummerSetup K L τ) {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell) : ℕ := by
  haveI : NeZero S.ell := ⟨S.ell_prime.ne_zero⟩
  exact (((IsPrimitiveRoot.autToPow K hζ) S.τζ : (ZMod S.ell)ˣ) : ZMod S.ell).val

/-- The chosen primitive root is sent to its `cyclotomicExponent`-th power. -/
theorem zeta_pow_cyclotomicExponent
    (S : OddKummerSetup K L τ) {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell) :
    ζ ^ cyclotomicExponent S hζ = S.τζ ζ := by
  haveI : NeZero S.ell := ⟨S.ell_prime.ne_zero⟩
  simp [cyclotomicExponent, IsPrimitiveRoot.autToPow_spec (R := K) hζ S.τζ]

/-- The same cyclotomic exponent describes the action on every `S.ell`-th root of unity. -/
theorem aut_rootsOfUnity_eq_pow_cyclotomicExponent
    (S : OddKummerSetup K L τ) {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell)
    (η : rootsOfUnity S.ell S.Lζ) :
    S.τζ ((η : S.Lζˣ) : S.Lζ) =
      ((η : S.Lζˣ) : S.Lζ) ^ cyclotomicExponent S hζ := by
  haveI : NeZero S.ell := ⟨S.ell_prime.ne_zero⟩
  obtain ⟨i, -, hη⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((η : S.Lζˣ) : S.Lζ)) (by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val η.2)
  rw [← hη, map_pow, ← zeta_pow_cyclotomicExponent S hζ]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end CyclotomicExponent

section MovedKummerClass

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped Pointwise

variable {F : Type u} [Field F] [NumberField F]

/--
A CRT element with valuation exactly one at `P` and valuation zero at a distinct prime `Q`.
-/
theorem exists_integer_mem_prime_not_square_not_conjugate
    (P Q : HeightOneSpectrum (𝓞 F)) (hPQ : P ≠ Q) :
    ∃ a : 𝓞 F, a ∈ P.asIdeal ∧ a ∉ P.asIdeal ^ 2 ∧ a ∉ Q.asIdeal := by
  classical
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ_mem : π ∈ P.asIdeal := by
    rw [← P.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]
    omega
  have hπ_not_mem_sq : π ∉ P.asIdeal ^ 2 := by
    rw [← P.intValuation_le_pow_iff_mem, hπ, exp_le_exp]
    omega
  have hcop : IsCoprime (P.asIdeal ^ 2) (Q.asIdeal ^ 1) :=
    HeightOneSpectrum.isCoprime_pow_of_ne P Q hPQ 2 1
  have hpair : Pairwise (Function.onFun IsCoprime
      (fun i : Fin 2 => if i = 0 then P.asIdeal ^ 2 else Q.asIdeal)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Function.onFun] at hij ⊢
    · simpa using hcop
    · simpa using hcop.symm
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal (ι := Fin 2)
    (I := fun i => if i = 0 then P.asIdeal ^ 2 else Q.asIdeal) hpair
    (fun i => if i = 0 then π else 1)
  refine ⟨a, ?_, ?_, ?_⟩
  · have h0 : a - π ∈ P.asIdeal ^ 2 := by simpa using ha 0
    have : a = π + (a - π) := by abel
    rw [this]
    exact P.asIdeal.add_mem hπ_mem (Ideal.pow_le_self (by decide : 2 ≠ 0) h0)
  · have h0 : a - π ∈ P.asIdeal ^ 2 := by simpa using ha 0
    intro hmem
    exact hπ_not_mem_sq (by simpa [sub_eq_add_neg] using (P.asIdeal ^ 2).sub_mem hmem h0)
  · have h1 : a - 1 ∈ Q.asIdeal := by simpa using ha 1
    intro hmem
    have htop : (1 : 𝓞 F) ∈ Q.asIdeal := by
      simpa [sub_eq_add_neg] using Q.asIdeal.sub_mem hmem h1
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one Q.asIdeal).2 htop)

/-- Membership in the image prime is equivalent to membership in the inverse-translated prime. -/
theorem smul_mem_heightOneSpectrum_iff_inv_smul
    {K F : Type u} [Field K] [Field F] [NumberField K] [NumberField F]
    [Algebra K F] [IsGalois K F]
    (σ : Gal(F/K)) (P : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    σ • x ∈ P.asIdeal ↔ x ∈ (σ⁻¹ • P).asIdeal := by
  constructor
  · intro hx
    have hx' : σ⁻¹ • (σ • x) ∈ σ⁻¹ • P.asIdeal :=
      (Ideal.smul_mem_pointwise_smul_iff (a := σ⁻¹) (S := P.asIdeal) (x := σ • x)).2 hx
    simpa [heightOneSpectrum_smul_asIdeal] using hx'
  · intro hx
    have hx' : σ • x ∈ σ • (σ⁻¹ • P).asIdeal :=
      (Ideal.smul_mem_pointwise_smul_iff (a := σ) (S := (σ⁻¹ • P).asIdeal) (x := x)).2 hx
    simpa [heightOneSpectrum_smul_asIdeal] using hx'

/-- An integral element in `P \ P²` has normalized `P`-adic value `exp (-1)`. -/
theorem intValuation_eq_exp_neg_one_of_mem_not_mem_sq
    (P : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F}
    (haP : a ∈ P.asIdeal) (haP2 : a ∉ P.asIdeal ^ 2) :
    P.intValuation a = exp (-1 : ℤ) := by
  have ha_ne_zero : a ≠ 0 := by
    intro h
    exact haP2 (by simp [h])
  have hspan_ne : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hcount : Multiset.count P.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a} : Ideal (𝓞 F))) = 1 := by
    apply Ideal.count_normalizedFactors_eq (p := P.asIdeal) (x := Ideal.span {a}) (n := 1)
    · rwa [Ideal.span_singleton_le_iff_mem, pow_one]
    · rwa [Ideal.span_singleton_le_iff_mem]
  rw [P.intValuation_if_neg ha_ne_zero,
    Ideal.count_associates_factors_eq hspan_ne P.isPrime P.ne_bot, hcount]
  norm_num

/-- The valuation of `σ a / a` at `P` is `exp 1` for the CRT witness orientation used here. -/
theorem valuation_aut_div_eq_exp_one
    {K F : Type u} [Field K] [Field F] [NumberField K] [NumberField F]
    [Algebra K F] [IsGalois K F]
    (σ : Gal(F/K)) (P : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F}
    (hva : P.valuation F (algebraMap (𝓞 F) F a) = exp (-1 : ℤ))
    (hvσa : P.valuation F (algebraMap (𝓞 F) F (σ • a)) = 1) :
    P.valuation F (σ (algebraMap (𝓞 F) F a) / algebraMap (𝓞 F) F a) = exp (1 : ℤ) := by
  change P.valuation F ((σ • algebraMap (𝓞 F) F a) / algebraMap (𝓞 F) F a) = exp (1 : ℤ)
  rw [← algebraMap.smul' σ a F, map_div₀, hvσa, hva]
  rw [← exp_zero, ← exp_sub]
  norm_num

/-- The valuation of `σ a / a ^ q` at `P` for the CRT witness orientation used here. -/
theorem valuation_aut_div_pow_eq_exp_nat
    {K F : Type u} [Field K] [Field F] [NumberField K] [NumberField F]
    [Algebra K F] [IsGalois K F]
    (σ : Gal(F/K)) (P : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F} (q : ℕ)
    (hva : P.valuation F (algebraMap (𝓞 F) F a) = exp (-1 : ℤ))
    (hvσa : P.valuation F (algebraMap (𝓞 F) F (σ • a)) = 1) :
    P.valuation F (σ (algebraMap (𝓞 F) F a) / algebraMap (𝓞 F) F a ^ q) =
      exp (q : ℤ) := by
  change P.valuation F ((σ • algebraMap (𝓞 F) F a) / algebraMap (𝓞 F) F a ^ q) =
    exp (q : ℤ)
  rw [← algebraMap.smul' σ a F, map_div₀, map_pow, hvσa, hva]
  rw [← exp_zero, ← WithZero.exp_nsmul, ← exp_sub]
  simp

/-- The valuation modulo `n` of an element with specified valuation exponent. -/
theorem valuationOfNeZeroMod_mk0_eq_of_valuation_exp
    (P : HeightOneSpectrum (𝓞 F)) (n : ℕ) (m : ℤ) {c : F} (hc : c ≠ 0)
    (hv : P.valuation F c = exp m) :
    P.valuationOfNeZeroMod (K := F) n (QuotientGroup.mk (Units.mk0 c hc)) =
      Multiplicative.ofAdd ((m : ZMod n)) := by
  have hunit : P.valuationOfNeZero (K := F) (Units.mk0 c hc) = Multiplicative.ofAdd m := by
    apply WithZero.coe_inj.mp
    rw [P.valuationOfNeZero_eq, Units.val_mk0, hv]
    rfl
  erw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply,
    QuotientGroup.map_mk', hunit]
  rfl

/-- The valuation modulo `n` of an element with valuation exponent `1`. -/
theorem valuationOfNeZeroMod_mk0_eq_of_valuation_exp_one
    (P : HeightOneSpectrum (𝓞 F)) (n : ℕ) {c : F} (hc : c ≠ 0)
    (hv : P.valuation F c = exp (1 : ℤ)) :
    P.valuationOfNeZeroMod (K := F) n (QuotientGroup.mk (Units.mk0 c hc)) =
      Multiplicative.ofAdd ((1 : ℤ) : ZMod n) := by
  exact valuationOfNeZeroMod_mk0_eq_of_valuation_exp P n 1 hc hv

/-- In `ZMod n`, the class of `1` is nonzero when `1 < n`. -/
theorem multiplicative_one_zmod_ne_one (n : ℕ) (hn : 1 < n) :
    Multiplicative.ofAdd ((1 : ℤ) : ZMod n) ≠ (1 : Multiplicative (ZMod n)) := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  have hzero : ((1 : ℤ) : ZMod n) = 0 := by simpa using h'
  have hne : (1 : ZMod n) ≠ 0 := by
    intro hz
    haveI : Fact (1 < n) := ⟨hn⟩
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_one, ZMod.val_zero] at hv
    omega
  exact hne (by simpa using hzero)

/--
If a field element has valuation exponent nonzero modulo `n` at a height-one prime, it is not an
`n`-th power.
-/
theorem not_exists_pow_eq_of_valuation_exp_ne_zero
    (P : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : n ≠ 0) {m : ℤ} {c : F} (hc : c ≠ 0)
    (hv : P.valuation F c = exp m) (hm : (m : ZMod n) ≠ 0) :
    ¬ ∃ b : F, b ^ n = c := by
  rintro ⟨b, hbpow⟩
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hbpow
    exact hc hbpow.symm
  have hquot : QuotientGroup.mk (Units.mk0 c hc) =
      (1 : Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range) := by
    rw [QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 b hb, ?_⟩
    ext
    simp [powMonoidHom_apply, hbpow]
  have hval1 := congrArg (P.valuationOfNeZeroMod (K := F) n) hquot
  rw [map_one] at hval1
  have hval := valuationOfNeZeroMod_mk0_eq_of_valuation_exp P n m hc hv
  have hne : Multiplicative.ofAdd (m : ZMod n) ≠ (1 : Multiplicative (ZMod n)) := by
    intro h
    exact hm (by simpa using congrArg Multiplicative.toAdd h)
  exact hne (hval.symm.trans hval1)

/--
If a field element has valuation exponent `1` at a height-one prime, it is not an `n`-th power.
-/
theorem not_exists_pow_eq_of_valuation_exp_one
    (P : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : 1 < n) {c : F} (hc : c ≠ 0)
    (hv : P.valuation F c = exp (1 : ℤ)) :
    ¬ ∃ b : F, b ^ n = c := by
  exact not_exists_pow_eq_of_valuation_exp_ne_zero P (by omega) hc hv
    (by
      intro h
      exact multiplicative_one_zmod_ne_one n hn (by
        ext
        exact h))

/--
NCT4: a nontrivial finite Galois automorphism moves a Kummer class in the odd Kummer setup.
-/
theorem exists_kummerClass_moved_by_aut
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ (S : OddKummerSetup K L τ) (a : S.Lζ),
      ¬ ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a := by
  classical
  let S : OddKummerSetup K L τ := oddKummerSetup (K := K) (L := L) τ
  have hτζ : S.τζ ≠ 1 := by
    intro h
    apply hτ
    simpa [h] using S.restrict_τζ.symm
  obtain ⟨P, hP⟩ := exists_split_prime_not_fixed (K := K) (L := S.Lζ) S.τζ hτζ
  let Q : HeightOneSpectrum (𝓞 S.Lζ) := S.τζ⁻¹ • P
  have hPQ : P ≠ Q := by
    intro h
    apply hP
    calc
      S.τζ • P = S.τζ • Q := by rw [h]
      _ = P := by simp [Q]
  obtain ⟨a₀, haP, haP2, haQ⟩ :=
    exists_integer_mem_prime_not_square_not_conjugate (F := S.Lζ) P Q hPQ
  let a : S.Lζ := algebraMap (𝓞 S.Lζ) S.Lζ a₀
  refine ⟨S, a, ?_⟩
  have ha₀_ne_zero : a₀ ≠ 0 := by
    intro h
    exact haQ (by simp [Q, h])
  have ha_ne_zero : a ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective (𝓞 S.Lζ) S.Lζ).ne ha₀_ne_zero
  have hσa_not_mem : S.τζ • a₀ ∉ P.asIdeal := by
    rwa [smul_mem_heightOneSpectrum_iff_inv_smul (K := K) (F := S.Lζ) S.τζ P a₀]
  have hva : P.valuation S.Lζ a = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_eq_exp_neg_one_of_mem_not_mem_sq P haP haP2
  have hvσa : P.valuation S.Lζ (algebraMap (𝓞 S.Lζ) S.Lζ (S.τζ • a₀)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hσa_not_mem
  have hval : P.valuation S.Lζ (S.τζ a / a) = exp (1 : ℤ) := by
    exact valuation_aut_div_eq_exp_one (K := K) (F := S.Lζ) S.τζ P hva hvσa
  have hc_ne_zero : S.τζ a / a ≠ 0 := by
    exact div_ne_zero ((map_ne_zero S.τζ).2 ha_ne_zero) ha_ne_zero
  exact not_exists_pow_eq_of_valuation_exp_one (F := S.Lζ) P S.ell_prime.one_lt hc_ne_zero hval

/--
Setup-level strengthened NCT4: any nontrivial chosen lift in an odd Kummer setup has a Kummer
class which is not an `S.ell`-th power and whose cyclotomic-twisted translate is not an
`S.ell`-th power.
-/
theorem exists_kummerClass_twisted_moved_by_setup_aut
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (hSτ : S.τζ ≠ 1) :
    ∃ a : S.Lζ,
      (¬ ∃ b : S.Lζ, b ^ S.ell = a) ∧
      ∀ {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell),
        ¬ ∃ b : S.Lζ,
          b ^ S.ell = S.τζ a / a ^ cyclotomicExponent S hζ := by
  classical
  obtain ⟨P, hP⟩ := exists_split_prime_not_fixed (K := K) (L := S.Lζ) S.τζ hSτ
  let Q : HeightOneSpectrum (𝓞 S.Lζ) := S.τζ⁻¹ • P
  have hPQ : P ≠ Q := by
    intro h
    apply hP
    calc
      S.τζ • P = S.τζ • Q := by rw [h]
      _ = P := by simp [Q]
  obtain ⟨a₀, haP, haP2, haQ⟩ :=
    exists_integer_mem_prime_not_square_not_conjugate (F := S.Lζ) P Q hPQ
  let a : S.Lζ := algebraMap (𝓞 S.Lζ) S.Lζ a₀
  have ha₀_ne_zero : a₀ ≠ 0 := by
    intro h
    exact haQ (by simp [Q, h])
  have ha_ne_zero : a ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective (𝓞 S.Lζ) S.Lζ).ne ha₀_ne_zero
  have hσa_not_mem : S.τζ • a₀ ∉ P.asIdeal := by
    rwa [smul_mem_heightOneSpectrum_iff_inv_smul (K := K) (F := S.Lζ) S.τζ P a₀]
  have hva : P.valuation S.Lζ a = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_eq_exp_neg_one_of_mem_not_mem_sq P haP haP2
  have hvσa : P.valuation S.Lζ (algebraMap (𝓞 S.Lζ) S.Lζ (S.τζ • a₀)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hσa_not_mem
  refine ⟨a, ?_, ?_⟩
  · have hm : ((-1 : ℤ) : ZMod S.ell) ≠ 0 := by
      intro h
      have h1 : (1 : ZMod S.ell) = 0 := by
        simpa using congrArg Neg.neg h
      have h1ne : (1 : ZMod S.ell) ≠ 0 := by
        intro hzero
        have hzero' : ((1 : ℕ) : ZMod S.ell) = 0 := by simpa using hzero
        exact S.ell_prime.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 S.ell).mp hzero')
      exact h1ne h1
    exact not_exists_pow_eq_of_valuation_exp_ne_zero (F := S.Lζ) P S.ell_prime.ne_zero
      ha_ne_zero hva hm
  · intro ζ hζ
    haveI : NeZero S.ell := ⟨S.ell_prime.ne_zero⟩
    haveI : Fact (1 < S.ell) := ⟨S.ell_prime.one_lt⟩
    let q := cyclotomicExponent S hζ
    have hqNat : (q : ZMod S.ell) ≠ 0 := by
      change (((((IsPrimitiveRoot.autToPow K hζ) S.τζ : (ZMod S.ell)ˣ) : ZMod S.ell).val : ℕ) :
          ZMod S.ell) ≠ 0
      rw [ZMod.natCast_zmod_val]
      exact Units.ne_zero _
    have hq : (((q : ℕ) : ℤ) : ZMod S.ell) ≠ 0 := by
      simpa only [Int.cast_natCast] using hqNat
    have hval : P.valuation S.Lζ (S.τζ a / a ^ q) = exp ((q : ℕ) : ℤ) := by
      exact valuation_aut_div_pow_eq_exp_nat (K := K) (F := S.Lζ) S.τζ P q hva hvσa
    have hc_ne_zero : S.τζ a / a ^ q ≠ 0 := by
      exact div_ne_zero ((map_ne_zero S.τζ).2 ha_ne_zero) (pow_ne_zero q ha_ne_zero)
    exact not_exists_pow_eq_of_valuation_exp_ne_zero (F := S.Lζ) P S.ell_prime.ne_zero
      hc_ne_zero hval hq

/--
Strengthened NCT4: the valuation witness gives a Kummer class which is not an `S.ell`-th power
and whose cyclotomic-twisted translate is not an `S.ell`-th power.
-/
theorem exists_kummerClass_twisted_moved_by_aut
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ (S : OddKummerSetup K L τ) (a : S.Lζ),
      (¬ ∃ b : S.Lζ, b ^ S.ell = a) ∧
      ∀ {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell),
        ¬ ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a ^ cyclotomicExponent S hζ := by
  let S : OddKummerSetup K L τ := oddKummerSetup (K := K) (L := L) τ
  have hSτ : S.τζ ≠ 1 := by
    intro h
    apply hτ
    simpa [h] using S.restrict_τζ.symm
  exact ⟨S, exists_kummerClass_twisted_moved_by_setup_aut S hSτ⟩

/--
The moved Kummer class supplied by NCT4 gives an irreducible cyclic Kummer polynomial over `S.Lζ`.
This is the first local Kummer-extension input for NCT5: adjoining a root of
`X ^ S.ell - C (S.τζ a / a)` gives a genuine degree-`S.ell` Kummer extension over `S.Lζ`.
-/
theorem movedKummerClass_polynomial_irreducible
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha : ¬ ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a) :
    Irreducible (X ^ S.ell - C (S.τζ a / a)) := by
  have hpow : Irreducible (X ^ (S.ell ^ 1) - C (S.τζ a / a)) := by
    apply X_pow_sub_C_irreducible_of_prime_pow S.ell_prime S.ell_ne_two 1
    intro b hb
    exact ha ⟨b, hb⟩
  simpa using hpow

/--
The cyclic Kummer extension attached to the moved class is Galois over `S.Lζ`.
-/
theorem movedKummerClass_adjoinRoot_isGalois
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha : ¬ ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a) :
    letI : Fact (Irreducible (X ^ S.ell - C (S.τζ a / a))) :=
      ⟨movedKummerClass_polynomial_irreducible S ha⟩
    IsGalois S.Lζ (AdjoinRoot (X ^ S.ell - C (S.τζ a / a))) := by
  letI : Fact (Irreducible (X ^ S.ell - C (S.τζ a / a))) :=
    ⟨movedKummerClass_polynomial_irreducible S ha⟩
  letI : IsSplittingField S.Lζ (AdjoinRoot (X ^ S.ell - C (S.τζ a / a)))
      (X ^ S.ell - C (S.τζ a / a)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C S.primitiveRoot
      (movedKummerClass_polynomial_irreducible S ha)
  exact isGalois_of_isSplittingField_X_pow_sub_C S.primitiveRoot
    (movedKummerClass_polynomial_irreducible S ha)
    (AdjoinRoot (X ^ S.ell - C (S.τζ a / a)))

/--
The cyclic Kummer extension attached to the moved class is finite-dimensional over `S.Lζ`.
-/
theorem movedKummerClass_adjoinRoot_finiteDimensional
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha : ¬ ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a) :
    letI : Fact (Irreducible (X ^ S.ell - C (S.τζ a / a))) :=
      ⟨movedKummerClass_polynomial_irreducible S ha⟩
    FiniteDimensional S.Lζ (AdjoinRoot (X ^ S.ell - C (S.τζ a / a))) := by
  letI : Fact (Irreducible (X ^ S.ell - C (S.τζ a / a))) :=
    ⟨movedKummerClass_polynomial_irreducible S ha⟩
  letI : IsSplittingField S.Lζ (AdjoinRoot (X ^ S.ell - C (S.τζ a / a)))
      (X ^ S.ell - C (S.τζ a / a)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C S.primitiveRoot
      (movedKummerClass_polynomial_irreducible S ha)
  exact Polynomial.IsSplittingField.finiteDimensional
    (AdjoinRoot (X ^ S.ell - C (S.τζ a / a))) (X ^ S.ell - C (S.τζ a / a))

/-- The Kummer polynomial for a non-`S.ell`-th-power radicand `a` is irreducible over `S.Lζ`. -/
theorem kummerClass_polynomial_irreducible_of_not_pow
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    Irreducible (X ^ S.ell - C a) := by
  have hpow : Irreducible (X ^ (S.ell ^ 1) - C a) := by
    apply X_pow_sub_C_irreducible_of_prime_pow S.ell_prime S.ell_ne_two 1
    intro b hb
    exact ha0 ⟨b, hb⟩
  simpa using hpow

/-- The cyclic Kummer extension attached to a non-power radicand `a` is Galois over `S.Lζ`. -/
theorem kummerClass_adjoinRoot_isGalois_of_not_pow
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    letI : Fact (Irreducible (X ^ S.ell - C a)) :=
      ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
    IsGalois S.Lζ (AdjoinRoot (X ^ S.ell - C a)) := by
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  letI : IsSplittingField S.Lζ (AdjoinRoot (X ^ S.ell - C a)) (X ^ S.ell - C a) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C S.primitiveRoot
      (kummerClass_polynomial_irreducible_of_not_pow S ha0)
  exact isGalois_of_isSplittingField_X_pow_sub_C S.primitiveRoot
    (kummerClass_polynomial_irreducible_of_not_pow S ha0) (AdjoinRoot (X ^ S.ell - C a))

/-- The cyclic Kummer extension attached to a non-power radicand `a` is finite over `S.Lζ`. -/
theorem kummerClass_adjoinRoot_finiteDimensional_of_not_pow
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    letI : Fact (Irreducible (X ^ S.ell - C a)) :=
      ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
    FiniteDimensional S.Lζ (AdjoinRoot (X ^ S.ell - C a)) := by
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  letI : IsSplittingField S.Lζ (AdjoinRoot (X ^ S.ell - C a)) (X ^ S.ell - C a) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C S.primitiveRoot
      (kummerClass_polynomial_irreducible_of_not_pow S ha0)
  exact Polynomial.IsSplittingField.finiteDimensional
    (AdjoinRoot (X ^ S.ell - C a)) (X ^ S.ell - C a)

/-- The one-radical Kummer extension `S.Lζ(α)` with `α ^ S.ell = a`. -/
noncomputable abbrev kummerAdjoinRoot
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ) : Type u :=
  AdjoinRoot (X ^ S.ell - C a)

/-- The normal closure over `K` of the one-radical Kummer extension for `a`. -/
noncomputable abbrev kummerNormalClosure
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ)
    [Fact (Irreducible (X ^ S.ell - C a))] : Type u :=
  normalClosure K (kummerAdjoinRoot S a) (AlgebraicClosure (kummerAdjoinRoot S a))

noncomputable instance kummerNormalClosure.field
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ)
    [Fact (Irreducible (X ^ S.ell - C a))] : Field (kummerNormalClosure S a) :=
  inferInstance

noncomputable instance kummerNormalClosure.algebra_K
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ)
    [Fact (Irreducible (X ^ S.ell - C a))] : Algebra K (kummerNormalClosure S a) :=
  inferInstance

/-- The `S.Lζ`-algebra structure on the normal closure, composed through the Kummer extension. -/
@[reducible]
noncomputable instance kummerNormalClosure.algebra_Lζ
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ)
    [Fact (Irreducible (X ^ S.ell - C a))] : Algebra S.Lζ (kummerNormalClosure S a) := by
  dsimp [kummerNormalClosure, kummerAdjoinRoot]
  letI : Algebra (AdjoinRoot (X ^ S.ell - C a))
      (normalClosure K (AdjoinRoot (X ^ S.ell - C a))
        (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))) :=
    normalClosure.algebra K (AdjoinRoot (X ^ S.ell - C a))
      (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))
  exact Algebra.compHom _ (algebraMap S.Lζ (AdjoinRoot (X ^ S.ell - C a)))

noncomputable instance kummerNormalClosure.tower
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (a : S.Lζ)
    [Fact (Irreducible (X ^ S.ell - C a))] :
    IsScalarTower K S.Lζ (kummerNormalClosure S a) := by
  dsimp [kummerNormalClosure, kummerAdjoinRoot]
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change algebraMap K (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a))) x =
    algebraMap (AdjoinRoot (X ^ S.ell - C a))
      (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))
      (algebraMap S.Lζ (AdjoinRoot (X ^ S.ell - C a)) (algebraMap K S.Lζ x))
  simp [IsScalarTower.algebraMap_apply K S.Lζ (AdjoinRoot (X ^ S.ell - C a)),
    IsScalarTower.algebraMap_apply K (AdjoinRoot (X ^ S.ell - C a))
      (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))]

/-- The Kummer normal closure is finite-dimensional over `K`. -/
theorem finiteDimensional_kummerNormalClosure
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    letI : Fact (Irreducible (X ^ S.ell - C a)) :=
      ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
    FiniteDimensional K (kummerNormalClosure S a) := by
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  dsimp [kummerNormalClosure, kummerAdjoinRoot]
  haveI : FiniteDimensional S.Lζ (AdjoinRoot (X ^ S.ell - C a)) :=
    kummerClass_adjoinRoot_finiteDimensional_of_not_pow S ha0
  haveI : FiniteDimensional K (AdjoinRoot (X ^ S.ell - C a)) :=
    FiniteDimensional.trans K S.Lζ (AdjoinRoot (X ^ S.ell - C a))
  exact normalClosure.is_finiteDimensional K (AdjoinRoot (X ^ S.ell - C a))
    (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))

/-- The Kummer normal closure is Galois over `K`. -/
theorem isGalois_K_kummerNormalClosure
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    letI : Fact (Irreducible (X ^ S.ell - C a)) :=
      ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
    IsGalois K (kummerNormalClosure S a) := by
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  dsimp [kummerNormalClosure, kummerAdjoinRoot]
  haveI : FiniteDimensional S.Lζ (AdjoinRoot (X ^ S.ell - C a)) :=
    kummerClass_adjoinRoot_finiteDimensional_of_not_pow S ha0
  haveI : FiniteDimensional K (AdjoinRoot (X ^ S.ell - C a)) :=
    FiniteDimensional.trans K S.Lζ (AdjoinRoot (X ^ S.ell - C a))
  exact IsGalois.normalClosure K (AdjoinRoot (X ^ S.ell - C a))
    (AlgebraicClosure (AdjoinRoot (X ^ S.ell - C a)))

/-- The Kummer normal closure is also Galois over the root-of-unity field `S.Lζ`. -/
theorem isGalois_Lζ_kummerNormalClosure
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a) :
    letI : Fact (Irreducible (X ^ S.ell - C a)) :=
      ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
    IsGalois S.Lζ (kummerNormalClosure S a) := by
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  haveI : IsGalois K (kummerNormalClosure S a) :=
    isGalois_K_kummerNormalClosure S ha0
  exact IsGalois.tower_top_of_isGalois K S.Lζ (kummerNormalClosure S a)

/--
A central lift of `S.τζ` to the one-radical Kummer normal closure forces the cyclotomic-twisted
Kummer class to be an `S.ell`-th power.

The extra local `Fact` argument is the irreducibility instance required by the current KC3
`kummerNormalClosure` definition; callers obtain it from `ha0` using
`kummerClass_polynomial_irreducible_of_not_pow`.
-/
theorem central_lift_forces_twisted_kummer_power
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a)
    [Fact (Irreducible (X ^ S.ell - C a))]
    {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell)
    (τM : Gal(kummerNormalClosure S a/K))
    (hτM : τM.restrictNormalHom S.Lζ = S.τζ)
    (hc : τM ∈ Subgroup.center Gal(kummerNormalClosure S a/K)) :
    ∃ b : S.Lζ, b ^ S.ell = S.τζ a / a ^ cyclotomicExponent S hζ := by
  classical
  let E := kummerAdjoinRoot S a
  let M := kummerNormalClosure S a
  let χ := cyclotomicExponent S hζ
  letI : Algebra E M := normalClosure.algebra K E (AlgebraicClosure E)
  haveI : IsScalarTower K E M := inferInstance
  have h_tower_FE_M : IsScalarTower S.Lζ E M := by
    dsimp [E, M, kummerAdjoinRoot, kummerNormalClosure]
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rfl
  letI : IsScalarTower S.Lζ E M := h_tower_FE_M
  have H : Irreducible (X ^ S.ell - C a) :=
    kummerClass_polynomial_irreducible_of_not_pow S ha0
  haveI : IsSplittingField S.Lζ E (X ^ S.ell - C a) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C S.primitiveRoot H
  haveI : Normal S.Lζ E :=
    (isGalois_iff (F := S.Lζ) (E := E)).mp
      (kummerClass_adjoinRoot_isGalois_of_not_pow S ha0) |>.2
  haveI : IsGalois S.Lζ M := isGalois_Lζ_kummerNormalClosure S ha0
  haveI : FiniteDimensional K M := finiteDimensional_kummerNormalClosure S ha0
  haveI : FiniteDimensional S.Lζ M := FiniteDimensional.right K S.Lζ M
  haveI : NeZero S.ell := ⟨S.ell_prime.ne_zero⟩
  let α : M := algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a))
  have hαE : (AdjoinRoot.root (X ^ S.ell - C a) : E) ^ S.ell =
      algebraMap S.Lζ E a := by
    exact root_X_pow_sub_C_pow S.ell a
  have hα : α ^ S.ell = algebraMap S.Lζ M a := by
    dsimp [α]
    rw [← map_pow, hαE]
    rw [IsScalarTower.algebraMap_apply S.Lζ E M]
  have ha_ne_zero : a ≠ 0 := by
    intro ha
    apply ha0
    refine ⟨0, ?_⟩
    rw [ha, zero_pow S.ell_prime.ne_zero]
  have hτ_on_F (x : S.Lζ) : τM (algebraMap S.Lζ M x) =
      algebraMap S.Lζ M (S.τζ x) := by
    have h := AlgEquiv.restrictNormal_commutes τM S.Lζ x
    change algebraMap S.Lζ M (((AlgEquiv.restrictNormalHom S.Lζ) τM) x) =
      τM (algebraMap S.Lζ M x) at h
    rw [hτM] at h
    exact h.symm
  let β : M := τM α / α ^ χ
  have hfixed : ∀ ρ : Gal(M / S.Lζ), ρ β = β := by
    intro ρ
    let ρK : Gal(M / K) := ρ.restrictScalars K
    have hcomm_apply : ρ (τM α) = τM (ρ α) := by
      have hcomm := Subgroup.mem_center_iff.mp hc ρK
      have happ := congrArg (fun e : Gal(M / K) => e α) hcomm
      change ρK (τM α) = τM (ρK α) at happ
      exact happ
    let ρE : Gal(E / S.Lζ) := ρ.restrictNormalHom E
    let η : rootsOfUnity S.ell S.Lζ := autEquivRootsOfUnity S.primitiveRoot H E ρE
    have hηα_E : η • (AdjoinRoot.root (X ^ S.ell - C a) : E) =
        ρE (AdjoinRoot.root (X ^ S.ell - C a)) := by
      exact autEquivRootsOfUnity_smul S.primitiveRoot H E hαE ρE
    have hρ_alpha : ρ α = η • α := by
      dsimp [α]
      rw [← AlgEquiv.restrictNormal_commutes ρ E (AdjoinRoot.root (X ^ S.ell - C a))]
      change algebraMap E M (ρE (AdjoinRoot.root (X ^ S.ell - C a))) =
        η • (algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a)))
      rw [← hηα_E]
      rw [show η • (AdjoinRoot.root (X ^ S.ell - C a) : E) =
          algebraMap S.Lζ E (((η : S.Lζˣ) : S.Lζ)) *
            (AdjoinRoot.root (X ^ S.ell - C a) : E) by
        change ((η : S.Lζˣ) • (AdjoinRoot.root (X ^ S.ell - C a) : E)) =
          algebraMap S.Lζ E (((η : S.Lζˣ) : S.Lζ)) *
            (AdjoinRoot.root (X ^ S.ell - C a) : E)
        rw [Units.smul_def, Algebra.smul_def]]
      rw [map_mul]
      rw [show η • (algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a))) =
          algebraMap S.Lζ M (((η : S.Lζˣ) : S.Lζ)) *
            algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a)) by
        change ((η : S.Lζˣ) • (algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a)))) =
          algebraMap S.Lζ M (((η : S.Lζˣ) : S.Lζ)) *
            algebraMap E M (AdjoinRoot.root (X ^ S.ell - C a))
        rw [Units.smul_def, Algebra.smul_def]]
      rw [IsScalarTower.algebraMap_apply S.Lζ E M]
    let η0 : S.Lζ := ((η : S.Lζˣ) : S.Lζ)
    let ηM : M := algebraMap S.Lζ M η0
    let ηχM : M := algebraMap S.Lζ M (η0 ^ χ)
    have hη_smul : η • α = ηM * α := by
      simp [ηM, η0, Subgroup.smul_def, Units.smul_def, Algebra.smul_def]
    have hτ_eta : τM ηM = ηχM := by
      dsimp [ηM, ηχM, η0]
      rw [hτ_on_F]
      rw [aut_rootsOfUnity_eq_pow_cyclotomicExponent S hζ η]
    have hη_ne_zero : ηχM ≠ 0 := by
      dsimp [ηχM, η0]
      exact (map_ne_zero (algebraMap S.Lζ M)).2
        (pow_ne_zero χ (Units.ne_zero (η : S.Lζˣ)))
    have hτ_smul : τM (η • α) = ηχM * τM α := by
      rw [hη_smul, map_mul, hτ_eta]
    have hpow_smul : (η • α) ^ χ = ηχM * α ^ χ := by
      rw [hη_smul, mul_pow]
      dsimp [ηχM, ηM, η0]
      rw [map_pow]
    calc
      ρ β = ρ (τM α) / ρ (α ^ χ) := by simp [β, map_div₀]
      _ = τM (ρ α) / (ρ α) ^ χ := by rw [hcomm_apply, map_pow]
      _ = τM (η • α) / (η • α) ^ χ := by rw [hρ_alpha]
      _ = (ηχM * τM α) / (ηχM * α ^ χ) := by rw [hτ_smul, hpow_smul]
      _ = τM α / α ^ χ := by exact mul_div_mul_left (τM α) (α ^ χ) hη_ne_zero
      _ = β := rfl
  have hβ_range : β ∈ Set.range (algebraMap S.Lζ M) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := S.Lζ) (E := M) β).2 hfixed
  obtain ⟨b, hb⟩ := hβ_range
  refine ⟨b, ?_⟩
  apply (algebraMap S.Lζ M).injective
  calc
    algebraMap S.Lζ M (b ^ S.ell) = (algebraMap S.Lζ M b) ^ S.ell := by rw [map_pow]
    _ = β ^ S.ell := by rw [hb]
    _ = (τM α) ^ S.ell / (α ^ χ) ^ S.ell := by simp [β, div_pow]
    _ = τM (α ^ S.ell) / (α ^ S.ell) ^ χ := by
        rw [← map_pow]
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        exact Nat.mul_comm χ S.ell
    _ = algebraMap S.Lζ M (S.τζ a) / (algebraMap S.Lζ M a) ^ χ := by
        rw [hα, hτ_on_F]
    _ = algebraMap S.Lζ M (S.τζ a / a ^ χ) := by simp [map_div₀, map_pow]

/--
The Kummer normal closure of a cyclotomic-twisted moved class has no central lift restricting to
`S.τζ`.
-/
theorem kummer_conjugation_nontrivial_of_twisted_moved_class
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) {a : S.Lζ}
    (ha0 : ¬ ∃ b : S.Lζ, b ^ S.ell = a)
    {ζ : S.Lζ} (hζ : IsPrimitiveRoot ζ S.ell)
    (haχ : ¬ ∃ b : S.Lζ,
      b ^ S.ell = S.τζ a / a ^ cyclotomicExponent S hζ) :
    ∃ (M : Type u) (_ : Field M) (_ : NumberField M)
      (_ : Algebra K M) (_ : Algebra S.Lζ M) (_ : IsScalarTower K S.Lζ M)
      (_ : FiniteDimensional K M) (_ : IsGalois K M),
      ∀ τM : Gal(M/K), τM.restrictNormalHom S.Lζ = S.τζ →
        τM ∉ Subgroup.center Gal(M/K) := by
  classical
  letI : Fact (Irreducible (X ^ S.ell - C a)) :=
    ⟨kummerClass_polynomial_irreducible_of_not_pow S ha0⟩
  let M := kummerNormalClosure S a
  haveI : FiniteDimensional K M := finiteDimensional_kummerNormalClosure S ha0
  haveI : IsGalois K M := isGalois_K_kummerNormalClosure S ha0
  haveI : NumberField M := NumberField.of_module_finite K M
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  intro τM hτM hc
  exact haχ (central_lift_forces_twisted_kummer_power S ha0 hζ τM hτM hc)

/--
Setup-level abstract no-central-lift theorem obtained by feeding the setup-level Kummer class
witness into the existing Kummer conjugation computation.
-/
theorem exists_abstract_no_central_lift_of_setup_aut
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] {τ : Gal(L/K)}
    (S : OddKummerSetup K L τ) (hSτ : S.τζ ≠ 1) :
    ∃ (M : Type u) (_ : Field M) (_ : NumberField M)
      (_ : Algebra K M) (_ : Algebra S.Lζ M) (_ : IsScalarTower K S.Lζ M)
      (_ : FiniteDimensional K M) (_ : IsGalois K M),
      ∀ τM : Gal(M/K), τM.restrictNormalHom S.Lζ = S.τζ →
        τM ∉ Subgroup.center Gal(M/K) := by
  obtain ⟨ζ, hζ⟩ := S.primitiveRoot
  have hζ' : IsPrimitiveRoot ζ S.ell := by
    rwa [mem_primitiveRoots S.ell_prime.pos] at hζ
  obtain ⟨a, ha0, haχ⟩ := exists_kummerClass_twisted_moved_by_setup_aut S hSτ
  exact kummer_conjugation_nontrivial_of_twisted_moved_class S ha0 hζ' (haχ hζ')

end MovedKummerClass

/--
Restriction between finite Galois intermediate quotients, using an explicit inclusion `L ≤ M`.

The explicit inclusion is needed because `AlgEquiv.restrictNormalHom` requires an `Algebra L M`
instance, which is supplied by the inclusion of intermediate fields.
-/
noncomputable def finiteGaloisRestrictHomOfLe
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) : Gal(M/K) →* Gal(L/K) := by
  letI : Algebra L M := RingHom.toAlgebra (Subsemiring.inclusion hLM)
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower L M K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom L

/-- Restricting from `K'` to `M` and then to `L` is the same as restricting directly to `L`. -/
theorem finiteGaloisRestrictHomOfLe_apply_restrict [IsGalois K K']
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) (σ : Gal(K'/K)) :
    finiteGaloisRestrictHomOfLe hLM (σ.restrictNormalHom M) = σ.restrictNormalHom L := by
  unfold finiteGaloisRestrictHomOfLe
  letI : Algebra L M := RingHom.toAlgebra (Subsemiring.inclusion hLM)
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower L M K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ).symm

/-- The coset of automorphisms of `F` whose restriction to `L` is `τ`. -/
def liftCoset
    {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {L F : FiniteGaloisIntermediateField K K'} (hLF : L ≤ F)
    (τ : Gal(L/K)) : Set Gal(F/K) :=
  {σ | finiteGaloisRestrictHomOfLe hLF σ = τ}

/-- Restriction maps for finite Galois intermediate fields compose in towers. -/
theorem finiteGaloisRestrictHomOfLe_comp
    {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {L F M : FiniteGaloisIntermediateField K K'}
    (hLF : L ≤ F) (hFM : F ≤ M) (η : Gal(M/K)) :
    finiteGaloisRestrictHomOfLe hLF (finiteGaloisRestrictHomOfLe hFM η) =
      finiteGaloisRestrictHomOfLe (le_trans hLF hFM) η := by
  unfold finiteGaloisRestrictHomOfLe
  letI : Algebra L F := RingHom.toAlgebra (Subsemiring.inclusion hLF)
  letI : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower L F K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : Algebra F M := RingHom.toAlgebra (Subsemiring.inclusion hFM)
  letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower F M K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : Algebra L M := RingHom.toAlgebra (Subsemiring.inclusion (le_trans hLF hFM))
  letI : IsScalarTower L F M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower L M K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L F η).symm

/-- Restriction to a normal subextension sends central automorphisms to central automorphisms. -/
theorem restrictNormalHom_mem_center [IsGalois K K']
    (L : IntermediateField K K') [Normal K L]
    {z : Gal(K'/K)} (hz : z ∈ Subgroup.center Gal(K'/K)) :
    AlgEquiv.restrictNormalHom L z ∈ Subgroup.center Gal(L/K) := by
  rw [Subgroup.mem_center_iff]
  intro τ
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := K') τ
  rw [← hσ]
  simpa only [map_mul] using
    congrArg (AlgEquiv.restrictNormalHom L) (Subgroup.mem_center_iff.mp hz σ)

/-- Restricting a central finite-quotient automorphism remains central in a smaller quotient. -/
theorem finiteGaloisRestrictHomOfLe_mem_center
    {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {A B : FiniteGaloisIntermediateField K K'} (hAB : A ≤ B)
    {z : Gal(B/K)} (hz : z ∈ Subgroup.center Gal(B/K)) :
    finiteGaloisRestrictHomOfLe hAB z ∈ Subgroup.center Gal(A/K) := by
  letI : Algebra A B := RingHom.toAlgebra (Subsemiring.inclusion hAB)
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsScalarTower A B K' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let i : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  let E : IntermediateField K B := i.fieldRange
  haveI : Normal K E := Normal.of_algEquiv i.equivFieldRange
  have hEcenter : AlgEquiv.restrictNormalHom E z ∈ Subgroup.center Gal(E/K) :=
    restrictNormalHom_mem_center (K := K) (K' := B) E hz
  have hcompat : (AlgEquiv.autCongr i.equivFieldRange)
      (finiteGaloisRestrictHomOfLe hAB z) = AlgEquiv.restrictNormalHom E z := by
    ext x
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [AlgEquiv.restrictNormalHom_apply E z x]
    have h := AlgEquiv.restrictNormal_commutes z A (i.equivFieldRange.symm x)
    calc
      (↑↑(i.equivFieldRange (((finiteGaloisRestrictHomOfLe hAB z)
            (i.equivFieldRange.symm x)))) : K') =
          ↑((algebraMap A B) (((AlgEquiv.restrictNormalHom A) z)
            (i.equivFieldRange.symm x)) : B) := by
        simp [i, finiteGaloisRestrictHomOfLe]
      _ = ↑(z ((algebraMap A B) (i.equivFieldRange.symm x)) : B) := by
        exact congrArg Subtype.val h
      _ = ↑(z ↑x : B) := by
        congr 1
        apply congrArg z
        exact congrArg Subtype.val (i.equivFieldRange.apply_symm_apply x)
  rw [Subgroup.mem_center_iff] at hEcenter ⊢
  intro γ
  apply (AlgEquiv.autCongr i.equivFieldRange).injective
  simpa [map_mul, hcompat] using hEcenter ((AlgEquiv.autCongr i.equivFieldRange) γ)

/-- A finite Galois intermediate field over a number field is again a number field. -/
noncomputable instance finiteGaloisIntermediateField.numberField [NumberField K]
    (L : FiniteGaloisIntermediateField K K') : NumberField L :=
  NumberField.of_module_finite K L

/--
The abstract odd Kummer setup, realized inside the fixed separable closure `K'`.

The field `F` is the realized copy of `S.Lζ`; the equivalence `eF` extends the identity on the
original intermediate field `L`.
-/
structure RealizedOddKummerSetup
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    (L : FiniteGaloisIntermediateField K K') (τ : Gal(L/K)) where
  S : OddKummerSetup K L τ
  F : FiniteGaloisIntermediateField K K'
  hLF : L ≤ F
  eF : S.Lζ ≃ₐ[K] F
  eF_extends : ∀ x : L, (eF (algebraMap L S.Lζ x) : K') = x

/--
Realize the cyclotomic field of the canonical odd Kummer setup in the fixed separable closure.
-/
noncomputable def realizedOddKummerSetup
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    (L : FiniteGaloisIntermediateField K K') (τ : Gal(L/K)) :
    RealizedOddKummerSetup L τ := by
  let S : OddKummerSetup K L τ := oddKummerSetup (K := K) (L := L) τ
  let i : L →ₐ[K] S.Lζ := IsScalarTower.toAlgHom K L S.Lζ
  let F : FiniteGaloisIntermediateField K K' :=
    finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := S.Lζ)
  have hLF : L ≤ F :=
    le_finiteGaloisIntermediateOfExtension_of_algHom (K := K) (K' := K') (M := S.Lζ) L i
  let hExists :=
    exists_algEquiv_finiteGaloisIntermediateOfExtension_extends
      (K := K) (K' := K') (M := S.Lζ) L i
  exact
    { S := S
      F := F
      hLF := hLF
      eF := Classical.choose hExists
      eF_extends := Classical.choose_spec hExists }

/--
Retarget a realized odd Kummer setup to a chosen automorphism of the realized cyclotomic field.
-/
noncomputable def RealizedOddKummerSetup.forLift
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    {L : FiniteGaloisIntermediateField K K'} {τ : Gal(L/K)}
    (R : RealizedOddKummerSetup L τ)
    (σ : Gal(R.F/K)) (hσ : finiteGaloisRestrictHomOfLe R.hLF σ = τ) :
    OddKummerSetup K L τ := by
  letI : Algebra L R.F := RingHom.toAlgebra (Subsemiring.inclusion R.hLF)
  letI : IsScalarTower K L R.F := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  refine
    { ell := R.S.ell
      ell_prime := R.S.ell_prime
      ell_ne_two := R.S.ell_ne_two
      Lζ := R.F
      field_Lζ := inferInstance
      numberField_Lζ := inferInstance
      algebra_K_Lζ := inferInstance
      algebra_L_Lζ := inferInstance
      tower := inferInstance
      isGalois_K_Lζ := inferInstance
      primitiveRoot := ?_
      τζ := σ
      restrict_τζ := ?_ }
  · obtain ⟨ζ, hζ⟩ := R.S.primitiveRoot
    refine ⟨R.eF ζ, ?_⟩
    rw [mem_primitiveRoots R.S.ell_prime.pos] at hζ ⊢
    exact hζ.map_of_injective R.eF.injective
  · change AlgEquiv.restrictNormalHom L σ = τ
    simpa [finiteGaloisRestrictHomOfLe] using hσ

/--
Transport a no-central-lift statement across a `K`-algebra equivalence which is the identity on the
base field `F`.
-/
theorem no_central_lift_transport_algEquiv
    {K M N F : Type u} [Field K] [Field M] [Field N] [Field F]
    [Algebra K F] [Algebra K M] [Algebra K N]
    [Algebra F M] [Algebra F N]
    [IsScalarTower K F M] [IsScalarTower K F N] [Normal K F]
    (e : M ≃ₐ[K] N)
    (heF : ∀ x : F, e (algebraMap F M x) = algebraMap F N x)
    (σ : Gal(F/K))
    (hkill : ∀ η : Gal(M/K), η.restrictNormalHom F = σ →
      η ∉ Subgroup.center Gal(M/K)) :
    ∀ η : Gal(N/K), η.restrictNormalHom F = σ →
      η ∉ Subgroup.center Gal(N/K) := by
  intro η hη hηc
  let ηM : Gal(M/K) := e.trans (η.trans e.symm)
  have hηM_restrict : ηM.restrictNormalHom F = σ := by
    ext x
    apply (algebraMap F M).injective
    calc
      algebraMap F M ((ηM.restrictNormalHom F) x) = ηM (algebraMap F M x) := by
        exact AlgEquiv.restrictNormal_commutes ηM F x
      _ = e.symm (η (algebraMap F N x)) := by simp [ηM, heF]
      _ = e.symm (algebraMap F N (σ x)) := by
        have h := AlgEquiv.restrictNormal_commutes η F x
        change algebraMap F N (((AlgEquiv.restrictNormalHom F) η) x) =
          η (algebraMap F N x) at h
        rw [hη] at h
        exact congrArg e.symm h.symm
      _ = algebraMap F M (σ x) := by
        apply e.injective
        rw [heF]
        simp
  have hηM_center : ηM ∈ Subgroup.center Gal(M/K) := by
    rw [Subgroup.mem_center_iff] at hηc ⊢
    intro γ
    let δ : Gal(N/K) := e.symm.trans (γ.trans e)
    have hcomm := hηc δ
    ext x
    apply e.injective
    have happ := congrArg (fun a : Gal(N/K) => a (e x)) hcomm
    simpa [ηM, δ, AlgEquiv.mul_apply] using happ
  exact hkill ηM hηM_restrict hηM_center

/--
Realized per-lift Kummer theorem: every automorphism of the realized Kummer field restricting to the
chosen lift `σ` is noncentral.
-/
theorem exists_realized_no_central_lift_of_lift_on_Lζ
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    {L : FiniteGaloisIntermediateField K K'} {τ : Gal(L/K)} (hτ : τ ≠ 1)
    (R : RealizedOddKummerSetup L τ)
    (σ : Gal(R.F/K)) (hσ : finiteGaloisRestrictHomOfLe R.hLF σ = τ) :
    ∃ (Mσ : FiniteGaloisIntermediateField K K'), ∃ hFMσ : R.F ≤ Mσ,
      ∀ η : Gal(Mσ/K), finiteGaloisRestrictHomOfLe hFMσ η = σ →
        η ∉ Subgroup.center Gal(Mσ/K) := by
  classical
  let Sσ := R.forLift σ hσ
  have hσ_ne : σ ≠ 1 := by
    intro hσ1
    apply hτ
    rw [← hσ, hσ1]
    exact map_one (finiteGaloisRestrictHomOfLe R.hLF)
  have hSσ : Sσ.τζ ≠ 1 := by
    change σ ≠ 1
    exact hσ_ne
  obtain ⟨M, fieldM, numberFieldM, algKM, algFM, towerKFM, finiteKM, galoisKM, hkill⟩ :=
    exists_abstract_no_central_lift_of_setup_aut Sσ hSσ
  letI : Field M := fieldM
  letI : NumberField M := numberFieldM
  letI : Algebra K M := algKM
  letI : Algebra R.F M := algFM
  letI : IsScalarTower K R.F M := towerKFM
  letI : FiniteDimensional K M := finiteKM
  letI : IsGalois K M := galoisKM
  let i : R.F →ₐ[K] M := IsScalarTower.toAlgHom K R.F M
  let Mσ : FiniteGaloisIntermediateField K K' :=
    finiteGaloisIntermediateOfExtension (K := K) (K' := K') (M := M)
  have hFMσ : R.F ≤ Mσ :=
    le_finiteGaloisIntermediateOfExtension_of_algHom (K := K) (K' := K') (M := M) R.F i
  letI : Algebra R.F Mσ := RingHom.toAlgebra (Subsemiring.inclusion hFMσ)
  letI : IsScalarTower K R.F Mσ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  obtain ⟨eM, heM⟩ :=
    exists_algEquiv_finiteGaloisIntermediateOfExtension_extends
      (K := K) (K' := K') (M := M) R.F i
  have heM_F : ∀ x : R.F, eM (algebraMap R.F M x) = algebraMap R.F Mσ x := by
    intro x
    apply Subtype.ext
    change (eM (i x) : K') = (x : K')
    exact heM x
  have hkill' : ∀ η : Gal(Mσ/K), η.restrictNormalHom R.F = σ →
      η ∉ Subgroup.center Gal(Mσ/K) :=
    no_central_lift_transport_algEquiv (K := K) (M := M) (N := Mσ) (F := R.F)
      eM heM_F σ hkill
  refine ⟨Mσ, hFMσ, ?_⟩
  intro η hη
  apply hkill' η
  simpa [finiteGaloisRestrictHomOfLe] using hη

/--
Take the compositum of one no-central-lift field for each member of a finite lift coset.
-/
theorem exists_compositum_no_central_lift
    {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {L F : FiniteGaloisIntermediateField K K'} (hLF : L ≤ F)
    (τ : Gal(L/K))
    (Mσ : {σ : Gal(F/K) // finiteGaloisRestrictHomOfLe hLF σ = τ} →
      FiniteGaloisIntermediateField K K')
    (hFMσ : ∀ σ, F ≤ Mσ σ)
    (hkillσ : ∀ σ, ∀ η : Gal(Mσ σ/K),
      finiteGaloisRestrictHomOfLe (hFMσ σ) η = σ.1 →
        η ∉ Subgroup.center Gal(Mσ σ/K)) :
    ∃ (M : FiniteGaloisIntermediateField K K'), ∃ hLM : L ≤ M,
      ∀ η : Gal(M/K), finiteGaloisRestrictHomOfLe hLM η = τ →
        η ∉ Subgroup.center Gal(M/K) := by
  classical
  letI : Fintype Gal(F/K) := Fintype.ofFinite _
  let C := {σ : Gal(F/K) // finiteGaloisRestrictHomOfLe hLF σ = τ}
  letI : Fintype C := inferInstance
  let N : Option C → FiniteGaloisIntermediateField K K'
    | none => F
    | some σ => Mσ σ
  let M : FiniteGaloisIntermediateField K K' := Finset.univ.sup N
  have hFM : F ≤ M := by
    change N none ≤ M
    exact Finset.le_sup (s := Finset.univ) (f := N) (b := none) (by simp)
  have hMσM : ∀ σ : C, Mσ σ ≤ M := by
    intro σ
    change N (some σ) ≤ M
    exact Finset.le_sup (s := Finset.univ) (f := N) (b := some σ) (by simp)
  refine ⟨M, le_trans hLF hFM, ?_⟩
  intro η hη hηc
  let σ0 : Gal(F/K) := finiteGaloisRestrictHomOfLe hFM η
  have hσ0 : finiteGaloisRestrictHomOfLe hLF σ0 = τ := by
    rw [finiteGaloisRestrictHomOfLe_comp hLF hFM η]
    exact hη
  let c0 : C := ⟨σ0, hσ0⟩
  let η0 : Gal(Mσ c0/K) := finiteGaloisRestrictHomOfLe (hMσM c0) η
  have hη0center : η0 ∈ Subgroup.center Gal(Mσ c0/K) := by
    exact finiteGaloisRestrictHomOfLe_mem_center (hMσM c0) hηc
  have hη0restrict : finiteGaloisRestrictHomOfLe (hFMσ c0) η0 = c0.1 := by
    have hcomp := finiteGaloisRestrictHomOfLe_comp (hFMσ c0) (hMσM c0) η
    rw [hcomp]
  exact hkillσ c0 η0 hη0restrict hη0center

/--
For every nontrivial automorphism on a finite Galois intermediate field, there is a larger finite
Galois intermediate field whose lifts of that automorphism are all noncentral.
-/
theorem exists_no_central_lift_of_ne_one
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    (L : FiniteGaloisIntermediateField K K')
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ (M : FiniteGaloisIntermediateField K K'), ∃ hLM : L ≤ M,
      ∀ τM : Gal(M/K), finiteGaloisRestrictHomOfLe hLM τM = τ →
        τM ∉ Subgroup.center Gal(M/K) := by
  classical
  let R := realizedOddKummerSetup L τ
  let C := {σ : Gal(R.F/K) // finiteGaloisRestrictHomOfLe R.hLF σ = τ}
  have hExists : ∀ σ : C,
      ∃ (Mσ : FiniteGaloisIntermediateField K K'), ∃ hFMσ : R.F ≤ Mσ,
        ∀ η : Gal(Mσ/K), finiteGaloisRestrictHomOfLe hFMσ η = σ.1 →
          η ∉ Subgroup.center Gal(Mσ/K) := by
    intro σ
    exact exists_realized_no_central_lift_of_lift_on_Lζ hτ R σ.1 σ.2
  let Mσ : C → FiniteGaloisIntermediateField K K' := fun σ ↦ Classical.choose (hExists σ)
  have hFMσ : ∀ σ : C, R.F ≤ Mσ σ := fun σ ↦
    Classical.choose (Classical.choose_spec (hExists σ))
  have hkillσ : ∀ σ : C, ∀ η : Gal(Mσ σ/K),
      finiteGaloisRestrictHomOfLe (hFMσ σ) η = σ.1 →
        η ∉ Subgroup.center Gal(Mσ σ/K) := fun σ ↦
    Classical.choose_spec (Classical.choose_spec (hExists σ))
  exact exists_compositum_no_central_lift R.hLF τ Mσ hFMσ hkillσ

/--
A central element of the absolute Galois group restricts trivially to every finite Galois
intermediate field.
-/
theorem central_absGal_restrict_finGalois_eq_one
    {K K' : Type u} [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K']
    {z : Gal(K'/K)} (hz : z ∈ Subgroup.center Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    z.restrictNormalHom L = 1 := by
  by_contra hne
  obtain ⟨M, hLM, hM⟩ :=
    exists_no_central_lift_of_ne_one L (z.restrictNormalHom L) hne
  have hzM : z.restrictNormalHom M ∈ Subgroup.center Gal(M/K) := by
    exact restrictNormalHom_mem_center (K := K) (K' := K') M.toIntermediateField hz
  exact hM (z.restrictNormalHom M) (finiteGaloisRestrictHomOfLe_apply_restrict hLM z) hzM

/--
An element of an infinite Galois group is determined by its restrictions to all finite Galois
intermediate fields.
-/
theorem gal_eq_one_of_forall_finGalois_restrict_eq_one [IsGalois K K']
    (z : Gal(K'/K))
    (hz : ∀ L : FiniteGaloisIntermediateField K K', z.restrictNormalHom L = 1) :
    z = 1 := by
  ext x
  let L := FiniteGaloisIntermediateField.adjoin K ({x} : Set K')
  have hx : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set K') (by simp)
  have h := congrArg (fun σ : Gal(L/K) => (σ ⟨x, hx⟩ : L)) (hz L)
  simpa [AlgEquiv.restrictNormalHom_apply] using congrArg Subtype.val h

/--
Abstract finite-quotient criterion for triviality of the center: if every nontrivial finite
restriction has a larger finite Galois quotient with no central lift, then the center is trivial.
-/
theorem center_eq_bot_of_no_central_lifts [IsSepClosure K K']
    (hkill : ∀ (L : FiniteGaloisIntermediateField K K')
      (τ : Gal(L/K)), τ ≠ 1 →
        ∃ (M : FiniteGaloisIntermediateField K K'), ∃ hLM : L ≤ M,
          ∀ τM : Gal(M/K), finiteGaloisRestrictHomOfLe hLM τM = τ →
            τM ∉ Subgroup.center Gal(M/K)) :
    Subgroup.center Gal(K'/K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have htriv : ∀ L : FiniteGaloisIntermediateField K K', z.restrictNormalHom L = 1 := by
    intro L
    by_contra hne
    obtain ⟨M, hLM, hM⟩ := hkill L (z.restrictNormalHom L) hne
    have hzM : z.restrictNormalHom M ∈ Subgroup.center Gal(M/K) := by
      exact restrictNormalHom_mem_center (K := K) (K' := K') M.toIntermediateField hz
    exact hM (z.restrictNormalHom M) (finiteGaloisRestrictHomOfLe_apply_restrict hLM z) hzM
  exact gal_eq_one_of_forall_finGalois_restrict_eq_one z htriv

end NumberField

/--
The absolute Galois group of a number field has trivial center, for any chosen separable closure.
-/
theorem numberField_absGal_center_trivial {K K' : Type u} [Field K] [Field K']
    [NumberField K] [Algebra K K'] [IsSepClosure K K'] :
    Subgroup.center Gal(K'/K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  exact NumberField.gal_eq_one_of_forall_finGalois_restrict_eq_one z
    (fun L ↦ NumberField.central_absGal_restrict_finGalois_eq_one hz L)
