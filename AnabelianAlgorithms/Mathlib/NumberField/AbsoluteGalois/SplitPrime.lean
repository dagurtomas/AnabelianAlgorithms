/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Int


/-!
# Split-prime infrastructure for finite Galois extensions of number fields

This file starts the elementary infrastructure for separating primes moved by a nontrivial finite
Galois automorphism.  The first step is the action of the Galois group on height-one primes of the
upstairs ring of integers, compatible by definition with the existing pointwise action on ideals.

It also contains the elementary Schur prime-divisor theorem for integer-polynomial values, used as
an arithmetic prime-producing engine in later phases.
-/

open scoped Pointwise

universe u

namespace NumberField

/--
The action of a finite Galois automorphism on height-one primes of the upstairs ring of integers.
The underlying ideal is the existing pointwise action on ideals.
-/
noncomputable instance heightOneSpectrum.instMulActionGal
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    MulAction Gal(L/K) (IsDedekindDomain.HeightOneSpectrum (𝓞 L)) where
  smul τ P :=
    { asIdeal := τ • P.asIdeal
      isPrime := by infer_instance
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [← inv_smul_smul τ P.asIdeal, h, Ideal.smul_bot] }
  one_smul P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (one_smul Gal(L/K) P.asIdeal : (1 : Gal(L/K)) • P.asIdeal = P.asIdeal)
  mul_smul τ σ P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (mul_smul τ σ P.asIdeal : (τ * σ) • P.asIdeal = τ • σ • P.asIdeal)

@[simp]
theorem heightOneSpectrum_smul_asIdeal
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    (τ • P).asIdeal = τ • P.asIdeal :=
  rfl

/-- A nontrivial finite Galois automorphism moves some algebraic integer. -/
theorem exists_ringOfIntegers_moved
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ x : 𝓞 L, τ • x ≠ x := by
  by_contra h
  apply hτ
  ext y
  obtain ⟨a, b, _, hy⟩ := IsFractionRing.div_surjective (𝓞 L) y
  rw [← hy]
  have hfix : ∀ x : 𝓞 L, τ • x = x := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have ha : τ (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a := by
    change τ • algebraMap (𝓞 L) L a = algebraMap (𝓞 L) L a
    rw [← algebraMap.smul', hfix a]
  have hb : τ (algebraMap (𝓞 L) L b) = algebraMap (𝓞 L) L b := by
    change τ • algebraMap (𝓞 L) L b = algebraMap (𝓞 L) L b
    rw [← algebraMap.smul', hfix b]
  simp [map_div₀, ha, hb]

/--
If a rational prime divides an integer-specialized minimal polynomial of an algebraic integer,
there is a maximal ideal above that prime containing the corresponding difference.
-/
theorem exists_isMaximal_under_int_of_prime_dvd_minpoly_eval
    {L : Type u} [Field L] [NumberField L]
    (x : 𝓞 L) (n : ℤ) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (minpoly ℤ x).eval n) :
    ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
      x - algebraMap ℤ (𝓞 L) n ∈ P := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : Polynomial ℤ := minpoly ℤ x
  have hxint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hroot : Polynomial.aeval (n : ZMod p) f = 0 := by
    have hcast : ((f.eval n : ℤ) : ZMod p) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval n) p).2 (by simpa [f] using hdvd)
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ (algebraMap ℤ (ZMod p)) (algebraMap ℤ (ZMod p) n) f = 0
    rw [Polynomial.eval₂_at_apply]
    exact hcast
  let ψ : AdjoinRoot f →ₐ[ℤ] ZMod p :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId ℤ (ZMod p)) (n : ZMod p) hroot
  let A : Subalgebra ℤ (𝓞 L) := Algebra.adjoin ℤ ({x} : Set (𝓞 L))
  let e := (minpoly.equivAdjoin hxint : AdjoinRoot f ≃ₐ[ℤ] Algebra.adjoin ℤ ({x} : Set (𝓞 L)))
  let φ : A →+* ZMod p := (ψ.comp e.symm.toAlgHom).toRingHom
  have hφ_surj : Function.Surjective φ := by
    intro z
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
    refine ⟨algebraMap ℤ A m, ?_⟩
    change (ψ.comp e.symm.toAlgHom) (algebraMap ℤ A m) = z
    rw [← hm]
    simp [ψ]
  let q : Ideal A := RingHom.ker φ
  have hqmax : q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ_surj
  have hAint : Algebra.IsIntegral A (𝓞 L) := by
    constructor
    intro y
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) y).tower_top (A := A)
  have hker_le : RingHom.ker (algebraMap A (𝓞 L)) ≤ q := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have : a = 0 := Subtype.ext ha
    rw [this]
    exact q.zero_mem
  haveI : Algebra.IsIntegral A (𝓞 L) := hAint
  haveI : q.IsMaximal := hqmax
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) q hker_le
  have hq_under : q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    ext m
    change algebraMap ℤ A m ∈ RingHom.ker φ ↔ m ∈ Ideal.span ({(p : ℤ)} : Set ℤ)
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    simp only [eq_intCast, map_intCast]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd m p
  have hP_under : P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    calc
      P.under ℤ = (P.under A).under ℤ := (Ideal.under_under P).symm
      _ = q.under ℤ := by rw [show P.under A = q by simpa [Ideal.under_def] using hPover]
      _ = Ideal.span ({(p : ℤ)} : Set ℤ) := hq_under
  have hφ_x :
      (ψ.comp e.symm.toAlgHom) (⟨x, Algebra.self_mem_adjoin_singleton ℤ x⟩ : A) =
        (n : ZMod p) := by
    change ψ (e.symm (⟨x, Algebra.self_mem_adjoin_singleton ℤ x⟩ : A)) = (n : ZMod p)
    have heq : e.symm (⟨x, Algebra.self_mem_adjoin_singleton ℤ x⟩ : A) =
        AdjoinRoot.root f := by
      rw [AlgEquiv.symm_apply_eq]
      ext
      simp [e, f]
    rw [heq]
    exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId ℤ (ZMod p)) (n : ZMod p) hroot
  have hsub_q : (⟨x - algebraMap ℤ (𝓞 L) n,
      (Algebra.adjoin ℤ ({x} : Set (𝓞 L))).sub_mem (Algebra.self_mem_adjoin_singleton ℤ x)
        ((Algebra.adjoin ℤ ({x} : Set (𝓞 L))).algebraMap_mem n)⟩ : A) ∈ q := by
    rw [RingHom.mem_ker]
    change (ψ.comp e.symm.toAlgHom) _ = 0
    have hn : (ψ.comp e.symm.toAlgHom) (algebraMap ℤ A n) = (n : ZMod p) := by simp [ψ]
    let a : A := ⟨x - algebraMap ℤ (𝓞 L) n,
      (Algebra.adjoin ℤ ({x} : Set (𝓞 L))).sub_mem (Algebra.self_mem_adjoin_singleton ℤ x)
        ((Algebra.adjoin ℤ ({x} : Set (𝓞 L))).algebraMap_mem n)⟩
    have ha : a = (⟨x, Algebra.self_mem_adjoin_singleton ℤ x⟩ : A) - algebraMap ℤ A n := by
      ext
      simp [a]
    change (ψ.comp e.symm.toAlgHom) a = 0
    rw [ha, map_sub, hφ_x, hn, sub_self]
  refine ⟨P, hPmax, hP_under, ?_⟩
  have hmemP : algebraMap A (𝓞 L) (⟨x - algebraMap ℤ (𝓞 L) n,
      (Algebra.adjoin ℤ ({x} : Set (𝓞 L))).sub_mem (Algebra.self_mem_adjoin_singleton ℤ x)
        ((Algebra.adjoin ℤ ({x} : Set (𝓞 L))).algebraMap_mem n)⟩ : A) ∈ P := by
    rw [← Ideal.mem_comap, hPover]
    exact hsub_q
  simpa using hmemP

end NumberField

namespace IntPolynomial

open Polynomial

/--
A finite-exclusion form of Schur's prime-divisor theorem for integer polynomials.

The nonconstant hypothesis is expressed as `0 < f.natDegree`: over the domain `ℤ`, this says
that `f` is not a constant polynomial, and is the polynomial-degree form used by the growth and
roots API.
-/
theorem exists_prime_not_mem_finset_dvd_eval
    (f : ℤ[X]) (hf : 0 < f.natDegree) (S : Finset ℕ) :
    ∃ n : ℤ, ∃ p : ℕ,
      p.Prime ∧ p ∉ S ∧ (p : ℤ) ∣ f.eval n := by
  classical
  have hf_ne_zero : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hf
  obtain ⟨a, ha⟩ := f.roots.toFinset.exists_notMem
  have hc : f.eval a ≠ 0 := by
    intro hroot
    apply ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne_zero]
    simpa [Polynomial.IsRoot] using hroot
  let c : ℤ := f.eval a
  have hc_ne_zero : c ≠ 0 := hc
  let m : ℕ := (S.filter Nat.Prime).prod id
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Finset.prod_pos fun q hq ↦ (Finset.mem_filter.mp hq).2.pos
  let B : ℤ := c * (m : ℤ)
  have hB_ne_zero : B ≠ 0 := by
    dsimp [B]
    exact mul_ne_zero hc_ne_zero (by exact_mod_cast hm_pos.ne')
  let q : ℤ[X] := Polynomial.C B * Polynomial.X + Polynomial.C a
  let P : ℤ[X] := f.comp q
  have hq_natDegree : q.natDegree = 1 := by
    dsimp [q]
    exact Polynomial.natDegree_linear hB_ne_zero
  have hP_natDegree : P.natDegree = f.natDegree := by
    dsimp [P]
    rw [Polynomial.natDegree_comp, hq_natDegree, Nat.mul_one]
  have hP_degree_pos : 0 < P.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hP_natDegree]
    exact hf
  have hdeg : (Polynomial.C c).degree < P.degree :=
    lt_of_le_of_lt Polynomial.degree_C_le hP_degree_pos
  have hfinite := Polynomial.finite_abs_eval_le_of_degree_lt hdeg
  obtain ⟨t, ht⟩ := hfinite.exists_notMem
  let n : ℤ := a + B * t
  have hq_eval : q.eval t = n := by
    dsimp [q, n]
    simp
    ring
  have hP_eval : P.eval t = f.eval n := by
    dsimp [P]
    rw [Polynomial.eval_comp, hq_eval]
  have hlarge_int : |(Polynomial.C c).eval t| < |P.eval t| := by
    have hnot : ¬ |P.eval t| ≤ |(Polynomial.C c).eval t| := by
      simpa using ht
    exact lt_of_not_ge hnot
  have hlarge_nat : c.natAbs < (f.eval n).natAbs := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hlarge_int
    exact Int.ofNat_lt.mp (by simpa [hP_eval] using hlarge_int)
  have hsub : n - a = B * t := by
    dsimp [n]
    ring
  have hB_dvd_sub : B ∣ n - a := by
    rw [hsub]
    exact dvd_mul_right B t
  have hdiff_dvd : n - a ∣ f.eval n - f.eval a :=
    Polynomial.sub_dvd_eval_sub n a f
  have hB_dvd_diff : B ∣ f.eval n - c := by
    dsimp [c]
    exact dvd_trans hB_dvd_sub hdiff_dvd
  obtain ⟨k, hk⟩ := hB_dvd_diff
  let z : ℤ := 1 + (m : ℤ) * k
  have hval : f.eval n = c * z := by
    calc
      f.eval n = c + (f.eval n - c) := by ring
      _ = c + B * k := by rw [hk]
      _ = c * z := by
        dsimp [B, z]
        ring
  have hz_natAbs_gt_one : 1 < z.natAbs := by
    have hmul : c.natAbs < c.natAbs * z.natAbs := by
      simpa [hval, Int.natAbs_mul] using hlarge_nat
    have hmul' : c.natAbs * 1 < c.natAbs * z.natAbs := by
      simpa using hmul
    exact Nat.lt_of_mul_lt_mul_left hmul'
  obtain ⟨p, hp_prime, hp_dvd_z_natAbs⟩ :=
    Nat.exists_prime_and_dvd (n := z.natAbs) (by omega)
  have hp_dvd_z : (p : ℤ) ∣ z := Int.natCast_dvd.mpr hp_dvd_z_natAbs
  have hp_not_mem : p ∉ S := by
    intro hp_mem
    have hp_dvd_m : p ∣ m := by
      dsimp [m]
      exact Finset.dvd_prod_of_mem id (by simp [hp_mem, hp_prime])
    have hp_dvd_m_int : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hp_dvd_m
    have hp_dvd_one_int : (p : ℤ) ∣ (1 : ℤ) := by
      have hzm : z - (m : ℤ) * k = 1 := by
        dsimp [z]
        ring
      rw [← hzm]
      exact dvd_sub hp_dvd_z (dvd_mul_of_dvd_left hp_dvd_m_int k)
    have hp_dvd_one_natAbs : p ∣ (1 : ℤ).natAbs := Int.natCast_dvd.mp hp_dvd_one_int
    exact hp_prime.not_dvd_one (by simpa using hp_dvd_one_natAbs)
  refine ⟨n, p, hp_prime, hp_not_mem, ?_⟩
  rw [hval]
  exact dvd_mul_of_dvd_right hp_dvd_z c

end IntPolynomial

namespace NumberField

/--
Integer-specialized prime separation: for any nonzero `δ`, some principal translate of `x` by an
integer from the smaller ring is contained in a height-one prime not containing `δ`.
-/
theorem exists_prime_dividing_sub_not_dividing
    {E L : Type u} [Field E] [Field L] [NumberField E] [NumberField L]
    [Algebra E L] [FiniteDimensional E L]
    (x δ : 𝓞 L) (hδ : δ ≠ 0)
    (_hx : x ∉ Set.range (algebraMap (𝓞 E) (𝓞 L))) :
    ∃ a : 𝓞 E, ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      x - algebraMap (𝓞 E) (𝓞 L) a ∈ P.asIdeal ∧ δ ∉ P.asIdeal := by
  classical
  let Iδ : Ideal (𝓞 L) := Ideal.span ({δ} : Set (𝓞 L))
  have hIδ_ne : Iδ ≠ ⊥ := by
    simpa [Iδ, Ideal.span_singleton_eq_bot] using hδ
  have hnormδ_ne : Ideal.absNorm Iδ ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr hIδ_ne
  let S : Finset ℕ := (Ideal.absNorm Iδ).divisors
  let f : Polynomial ℤ := minpoly ℤ x
  have hxint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hf : 0 < f.natDegree := by
    simpa [f] using minpoly.natDegree_pos hxint
  obtain ⟨n, p, hp, hp_not_mem, hp_dvd⟩ :=
    IntPolynomial.exists_prime_not_mem_finset_dvd_eval f hf S
  obtain ⟨P, hPmax, hP_under, hxP⟩ :=
    exists_isMaximal_under_int_of_prime_dvd_minpoly_eval (L := L) x n hp (by simpa [f] using hp_dvd)
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have hp_mem : (p : ℤ) ∈ (P.under ℤ) := by
      rw [hP_under]
      exact Ideal.mem_span_singleton.mpr dvd_rfl
    have : (p : ℤ) = 0 := by
      simpa [hbot, Ideal.under_bot] using hp_mem
    exact hp.ne_zero (Int.ofNat_eq_zero.mp this)
  let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    { asIdeal := P
      isPrime := hPmax.isPrime
      ne_bot := hP_ne_bot }
  refine ⟨algebraMap ℤ (𝓞 E) n, Q, ?_, ?_⟩
  · convert hxP using 1
    rw [IsScalarTower.algebraMap_apply ℤ (𝓞 E) (𝓞 L)]
  · intro hδP
    have hP_dvd : P ∣ Iδ := by
      simpa [Iδ] using (Ideal.dvd_span_singleton (I := P) (x := δ)).mpr hδP
    have hnorm_dvd : Ideal.absNorm P ∣ Ideal.absNorm Iδ :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hP_dvd)
    have hp_absP : p ∣ Ideal.absNorm P := by
      have hunder_dvd := Int.absNorm_under_dvd_absNorm P
      have h_under_norm : Ideal.absNorm (P.under ℤ) = p := by
        rw [hP_under]
        simp [Ideal.absNorm_span_singleton]
      rw [h_under_norm] at hunder_dvd
      exact hunder_dvd
    have hp_dvd_normδ : p ∣ Ideal.absNorm Iδ := dvd_trans hp_absP hnorm_dvd
    exact hp_not_mem (Nat.mem_divisors.mpr ⟨hp_dvd_normδ, hnormδ_ne⟩)

/--
Algebraic integers coming from the fixed field of a subgroup are fixed by every element of that
subgroup after mapping to the upstairs ring of integers.
-/
theorem smul_algebraMap_ringOfIntegers_fixedField
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (H : Subgroup Gal(L/K)) (hτH : τ ∈ H)
    (a : 𝓞 (IntermediateField.fixedField H)) :
    τ • algebraMap (𝓞 (IntermediateField.fixedField H)) (𝓞 L) a =
      algebraMap (𝓞 (IntermediateField.fixedField H)) (𝓞 L) a := by
  let E : Type u := IntermediateField.fixedField H
  let y : E := algebraMap (𝓞 E) E a
  have hy_fixed : τ (y : L) = (y : L) :=
    (IntermediateField.mem_fixedField_iff H (y : L)).1 y.2 τ hτH
  have hcoe : (algebraMap (𝓞 E) (𝓞 L) a : L) = (y : L) := by
    change (RingOfIntegers.mapRingHom (algebraMap E L) a : L) = (y : L)
    rw [RingOfIntegers.mapRingHom_apply]
    rfl
  apply RingOfIntegers.ext
  change τ ((algebraMap (𝓞 E) (𝓞 L) a : 𝓞 L) : L) =
    ((algebraMap (𝓞 E) (𝓞 L) a : 𝓞 L) : L)
  rw [hcoe, hy_fixed]

/--
If a prime contains `x - a` but not `τ • x - x`, then it cannot be fixed by `τ`, provided `a`
is fixed by `τ` after mapping upstairs.
-/
theorem moved_of_sub_mem_and_delta_not_mem
    {K L E : Type u} [Field K] [Field L] [Field E]
    [NumberField K] [NumberField L] [NumberField E]
    [Algebra K L] [IsGalois K L] [Algebra E L]
    (τ : Gal(L/K)) (x : 𝓞 L) (a : 𝓞 E)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hτa : τ • algebraMap (𝓞 E) (𝓞 L) a = algebraMap (𝓞 E) (𝓞 L) a)
    (hxP : x - algebraMap (𝓞 E) (𝓞 L) a ∈ P.asIdeal)
    (hδP : τ • x - x ∉ P.asIdeal) :
    τ • P ≠ P := by
  intro hP
  let A : 𝓞 L := algebraMap (𝓞 E) (𝓞 L) a
  have hτ_mem_smulIdeal : τ • (x - A) ∈ τ • P.asIdeal := by
    simpa [A] using (Set.smul_mem_smul_set (a := τ) hxP)
  have hτ_mem : τ • (x - A) ∈ P.asIdeal := by
    rw [← heightOneSpectrum_smul_asIdeal, hP] at hτ_mem_smulIdeal
    exact hτ_mem_smulIdeal
  have hτ_sub_mem : τ • x - A ∈ P.asIdeal := by
    simpa [A, smul_sub, hτa] using hτ_mem
  have hdelta : τ • x - x ∈ P.asIdeal := by
    have hsub := sub_mem hτ_sub_mem hxP
    simpa [A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
  exact hδP hdelta

/--
A nontrivial automorphism of a finite Galois extension of number fields moves some height-one prime
of the upstairs ring of integers.
-/
theorem exists_split_prime_not_fixed
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 L), τ • P ≠ P := by
  classical
  -- 1. Work over the fixed field of the cyclic subgroup generated by `τ`.
  let H : Subgroup Gal(L/K) := Subgroup.zpowers τ
  let E : IntermediateField K L := IntermediateField.fixedField H
  have hτH : τ ∈ H := Subgroup.mem_zpowers τ
  -- 2. Algebraic integers from `E` are fixed by `τ` after mapping to `𝓞 L`.
  have hτ_fixed_on_E_int : ∀ a : 𝓞 E,
      τ • algebraMap (𝓞 E) (𝓞 L) a = algebraMap (𝓞 E) (𝓞 L) a := by
    intro a
    exact smul_algebraMap_ringOfIntegers_fixedField τ H hτH a
  -- 3. Choose an algebraic integer moved by `τ` and set `δ = τ • x - x`.
  obtain ⟨x, hx_moved⟩ := exists_ringOfIntegers_moved τ hτ
  let δ : 𝓞 L := τ • x - x
  have hδ_ne : δ ≠ 0 := by
    dsimp [δ]
    exact sub_ne_zero.mpr hx_moved
  -- 4. The moved integer cannot come from the fixed field.
  have hx_not_range : x ∉ Set.range (algebraMap (𝓞 E) (𝓞 L)) := by
    rintro ⟨a, rfl⟩
    exact hx_moved (hτ_fixed_on_E_int a)
  -- 5. Separate `x` and `δ` by a height-one prime after an integral translate from `E`.
  obtain ⟨a, P, hx_sub_mem, hδ_not_mem⟩ :=
    exists_prime_dividing_sub_not_dividing (E := E) (L := L) x δ hδ_ne hx_not_range
  -- 6. If `P` were fixed by `τ`, the two congruent translates would force `δ ∈ P`.
  refine ⟨P, ?_⟩
  exact moved_of_sub_mem_and_delta_not_mem (E := E) τ x a P (hτ_fixed_on_E_int a)
    hx_sub_mem (by simpa [δ] using hδ_not_mem)

end NumberField
