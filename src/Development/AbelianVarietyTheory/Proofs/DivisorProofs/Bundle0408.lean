module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0387
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NullHtpyStair

variable {R : Type} [CommRing R]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m' hm] at h0
  obtain ⟨β, hβ⟩ := h0
  refine ⟨sglι A ≫ β.v 0 m' (by omega), ?_⟩
  have := congrArg (fun c => c.v 0 m (zero_add m)) hβ
  beta_reduce at this
  rw [δ_v m' m hm β 0 m (zero_add m) m' 1 (by omega) (by omega), Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v] at this
  have hd : (sgl A).d 0 1 = 0 := (HomologicalComplex.isZero_single_obj_X _ _ _ 1 (by omega)).eq_of_tgt _ _
  rw [hd, zero_comp, smul_zero, add_zero] at this
  rw [Category.assoc, this]
  exact Iso.inv_hom_id_assoc _ _

theorem comp_d_eq_zero {K M : Cx R} {n : ℤ} (c : Cochain K M n) (hc : δ n (n + 1) c = 0) (p : ℤ)
    (h1 : ∀ q hq, c.v (p + 1) q hq = 0) : c.v p (p + n) rfl ≫ M.d (p + n) (p + n + 1) = 0 := by
  have := congrArg (fun c' => c'.v p (p + n + 1) (by omega)) hc
  simp only [Cochain.zero_v] at this
  rw [δ_v n (n + 1) rfl c p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl, h1, comp_zero, smul_zero,
    add_zero] at this
  exact this

def Good {K M : Cx R} {n : ℤ} (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) : Prop :=
  ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n y).v p q hpq = (z : Cochain K M n).v p q hpq

theorem step {K M : Cx R} {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) (hy : Good z k y) :
    ∃ g : K.X (-(k : ℤ)) ⟶ M.X (-(k : ℤ) + (n - 1)), Good z (k + 1) (y + Cochain.single g (n - 1)) := by
  let c : Cochain K M n := (z : Cochain K M n) - δ (n - 1) n y
  have hc : δ n (n + 1) c = 0 := by
    simp only [c, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  have h1 : ∀ q hq, c.v (-(k : ℤ) + 1) q hq = 0 := fun q hq => by
    simp only [c, Cochain.sub_v, hy (-(k : ℤ) + 1) q hq (by omega), sub_self]
  obtain ⟨g, hg⟩ := hK (-(k : ℤ)) (-(k : ℤ) + (n - 1)) (-(k : ℤ) + n) (by omega) (by omega)
    (c.v (-(k : ℤ)) (-(k : ℤ) + n) rfl) (comp_d_eq_zero c hc _ h1)
  refine ⟨g, fun p q hpq hp => ?_⟩
  rw [δ_add, Cochain.add_v]
  by_cases hpp : p = -(k : ℤ)
  · subst hpp
    obtain rfl : q = -(k : ℤ) + n := by omega
    rw [δ_v (n - 1) n (by omega) (Cochain.single g (n - 1)) _ _ hpq (-(k : ℤ) + (n - 1)) (-(k : ℤ) + 1) (by omega) rfl,
      Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero, smul_zero, add_zero, hg]
    simp only [c, Cochain.sub_v]
    abel
  · rw [hy p q hpq (by omega), δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp

def seq {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) : {y : Cochain K M (n - 1) // Good z k y} :=
  Nat.rec (motive := fun k => {y : Cochain K M (n - 1) // Good z k y})
    (⟨0, fun p q hpq hp => (K.isZero_of_isStrictlyLE 0 p (by omega)).eq_of_src _ _⟩ : {y : Cochain K M (n - 1) // Good z 0 y})
    (fun k ih => ⟨ih.1 + Cochain.single (step hK z k _ ih.2).choose (n - 1), (step hK z k _ ih.2).choose_spec⟩) k

theorem seq_agree {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k j : ℕ) (hkj : k ≤ j) (p q : ℤ) (hpq : p + (n - 1) = q) (hp : -(k : ℤ) < p) :
    (seq hK z j).1.v p q hpq = (seq hK z k).1.v p q hpq := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((seq hK z j).1 + Cochain.single _ (n - 1)).v p q hpq = _
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), add_zero]

end GlobalTheory.NullHtpyStair


open GlobalTheory.NullHtpyStair in
theorem GlobalTheory.nullHtpy_stair : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0],
    (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ,
    Subsingleton (CohomologyClass K M n) := by
  intro R _ K M _ hA n
  have hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f :=
    fun p m' m hp hm f hf => GlobalTheory.NullHtpyStair.lift_of_subsingleton hm (hA p m hp) f hf
  suffices h : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨Cochain.mk (fun p q hpq => (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).1.v p q hpq), ?_⟩
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl, Cochain.mk_v, Cochain.mk_v,
    ← GlobalTheory.NullHtpyStair.seq_agree hK z ((-(p + 1)).toNat + 1) ((-p).toNat + 1)
      (by omega) (p + 1) q _ (by omega),
    ← δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl]
  exact (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).2 p q hpq (by omega)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityOfPrincipalCongruence
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem inv_small {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by
  obtain ⟨Q, hQm, hQ⟩ := hg
  rw [← aeval_def] at hQ
  set D := algebraMap O A α + algebraMap O A β * g with hD
  set n := Q.natDegree
  let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (X - C α) ^ i * C β ^ (n - i)
  have hR : aeval D R = 0 := by
    have : aeval D R = algebraMap O A β ^ n * aeval g Q := by
      conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Algebra.smul_def, hD]
      have : algebraMap O A β ^ n = algebraMap O A β ^ i * algebraMap O A β ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hin]
      rw [this]; ring
    rw [this, hQ, mul_zero]
  have hR0 : IsUnit (R.eval 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hb : IsLocalRing.residue O β = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hβ
    have ha : IsLocalRing.residue O α ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hα
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_sum, map_mul, map_pow,
      map_sub, map_zero, hb]
    rw [Finset.sum_eq_single n]
    · simp [n, hQm.coeff_natDegree, ha]
    · intro i hi hin
      have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  obtain ⟨w, hw, hDw⟩ := sub_inv_mem D 0 R hR hR0
  rw [map_zero, sub_zero] at hDw
  refine ⟨w, ?_, hDw⟩
  have hDmem : D ∈ Algebra.adjoin O ({g} : Set A) :=
    add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hDmem) hw

theorem adjoin_both {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g Y : A) (α β γ : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) (hγ : IsUnit γ)
    (hY : Y * (algebraMap O A α + algebraMap O A β * g) = algebraMap O A γ * g) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  obtain ⟨w, hw, hDw⟩ := inv_small g α β hg hα hβ
  have h1 : Y ∈ Algebra.adjoin O ({g} : Set A) := by
    have e : Y = algebraMap O A γ * g * w := by linear_combination (-Y) * hDw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hw
  refine ⟨h1, ?_⟩
  have hYi : IsIntegral O Y := IsIntegral.of_mem_of_fg _ hg.fg_adjoin_singleton Y h1
  have hβ' : -β ∈ IsLocalRing.maximalIdeal O := neg_mem hβ
  obtain ⟨v, hv, hEv⟩ := inv_small Y γ (-β) hYi hγ hβ'
  have e : g = algebraMap O A α * Y * v := by
    rw [map_neg] at hEv
    linear_combination (-g) * hEv - v * hY
  rw [e]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hv

variable {K : UQ}

theorem congruence_selfadj (B : InvAlg K) (a x y : K.O) (ha0 : a ≠ 0)
    (hac : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hu : (1 + algebraMap K.O B.A a * B.g) * B.σ (1 + algebraMap K.O B.A a * B.g) = 1)
    (Y w : B.A)
    (hw : (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) * w = 1)
    (hY : Y * (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) =
      algebraMap K.O B.A (x * y) * B.g) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have sa : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [σ_algebraMap, hac, ← IsScalarTower.algebraMap_apply]
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_sub, map_add (f := _), sx, sy, sa] at h1 hY hw
  rw [map_add (f := _), map_one, map_mul, sa] at hu
  set G := B.g
  set S := B.σ B.g
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  set aA := algebraMap K.O B.A a
  have key : (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA = 0 := by
    linear_combination (-aA * (1 + aA * G)) * h1 - (xA * yA - aA * B.σ Y * yA) * hu - aA * hY
  have key2 : (B.σ Y - Y) * aA = 0 := by
    calc (B.σ Y - Y) * aA = (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA * w := by
          linear_combination (-(B.σ Y - Y) * aA) * hw
      _ = 0 := by rw [key, zero_mul]
  have hae : algebraMap K.O K.E a ≠ 0 := by
    intro h; exact ha0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  have : (algebraMap K.O K.E a) • (B.σ Y - Y) = 0 := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]; exact key2
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left hae)

end GlobalTheory.UnitLemma.CongruenceCayley

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a →
    ∀ B₁ B₂ : InvAlg K,
    (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 →
    (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K a ha B₁ B₂ hu₁ hu₂ hsep
  by_cases hint : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  swap
  · obtain ⟨h1, h2⟩ := kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hint
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]
  obtain ⟨i₁, i₂⟩ := hint
  obtain ⟨ha0, ham, hac⟩ := ha
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (CayleyAny.isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := CayleyAny.isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hβ : x * a ∈ IsLocalRing.maximalIdeal K.O := Ideal.mul_mem_left _ _ ham
  have hγ : IsUnit (x * y) := hxu.mul hyu
  obtain ⟨w₁, -, hw₁⟩ := inv_small B₁.g (x - y) (x * a) i₁ hxyu hβ
  obtain ⟨w₂, -, hw₂⟩ := inv_small B₂.g (x - y) (x * a) i₂ hxyu hβ
  set Y₁ := algebraMap K.O B₁.A (x * y) * B₁.g * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A (x * y) * B₂.g * w₂ with hY₂d
  have hY₁ : Y₁ * (algebraMap K.O B₁.A (x - y) + algebraMap K.O B₁.A (x * a) * B₁.g) =
      algebraMap K.O B₁.A (x * y) * B₁.g := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A (x * y) * B₁.g) * hw₁
  have hY₂ : Y₂ * (algebraMap K.O B₂.A (x - y) + algebraMap K.O B₂.A (x * a) * B₂.g) =
      algebraMap K.O B₂.A (x * y) * B₂.g := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A (x * y) * B₂.g) * hw₂
  have adj₁ := adjoin_both B₁.g Y₁ (x - y) (x * a) (x * y) i₁ hxyu hβ hγ hY₁
  have adj₂ := adjoin_both B₂.g Y₂ (x - y) (x * a) (x * y) i₂ hxyu hβ hγ hY₂
  have iP : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := IsIntegral.pair i₁ i₂
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * (algebraMap K.O (B₁.A × B₂.A) (x - y) +
      algebraMap K.O (B₁.A × B₂.A) (x * a) * (B₁.g, B₂.g)) =
      algebraMap K.O (B₁.A × B₂.A) (x * y) * (B₁.g, B₂.g) :=
    Prod.ext hY₁ hY₂
  have adjP := adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (x - y) (x * a) (x * y) iP hxyu hβ hγ hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := congruence_selfadj B₁ a x y ha0 hac hxy hu₁ Y₁ w₁ hw₁ hY₁
  have sa₂ := congruence_selfadj B₂ a x y ha0 hac hxy hu₂ Y₂ w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g i₁
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g i₂
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CongruenceCayley
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibreStatement
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_full_rank_fibre :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
      GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
      MeasureTheory.Integrable (fun g : GL (Fin a) k =>
        Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
          (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
        (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hLocal, hCompact⟩, hRank⟩ := hΦ
  let σ := finSumFinEquiv (m := a) (n := b)
  let X₀ := GlobalTheory.SplitFlip.X0 (k := k) σ
  have hLocalΦ : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X₀) :=
    hLocal.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hLocalν := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hLocalPow : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hContinuous := ((hLocalΦ.mul hLocalν).mul hLocalPow).continuous

  let D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X₀) ≠ 0}
  have hClosed : IsClosed D :=
    (hLocal.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X₀ from
        continuous_id.matrix_mul continuous_const)
  have hSubset : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X₀, subset_tsupport _ hA, ?_⟩
    have hTranspose : X₀ * X₀ᵀ = 1 := by
      ext i j
      change (GlobalTheory.SplitFlip.X0 (k := k) σ * X₀ᵀ) i j = _
      rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
      simp [X₀, GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]
    show A * X₀ * X₀ᵀ = A
    rw [Matrix.mul_assoc, hTranspose, Matrix.mul_one]
  have hCompactD : IsCompact D :=
    (hCompact.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hClosed hSubset
  have hRange : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hFullRank : (A * X₀).rank = a := by
      by_contra hne
      exact hA (hRank _ hne)
    have hRankA : A.rank = Fintype.card (Fin a) := by
      refine le_antisymm (by simpa using A.rank_le_width) ?_
      simpa [hFullRank] using Matrix.rank_mul_le_left A X₀
    have hIndependent : LinearIndependent k A.row := by
      rw [rank_eq_finrank_span_row] at hRankA
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact hRankA.symm
    exact ⟨(Matrix.linearIndependent_row_iff_isUnit.1 hIndependent).unit, rfl⟩
  have hPreimage : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hCompactD hRange
  have hSupport : HasCompactSupport fun g : GL (Fin a) k =>
      Φ (g.val * X₀) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hPreimage fun g hg => ?_
    have hZero : Φ (g.val * X₀) = 0 := not_not.1 hg
    simp [hZero]
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  exact hContinuous.integrable_of_hasCompactSupport (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) hSupport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → IsIntegral R (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsIntegral R (f i τ₀ / Ω ^ w) := by
  first | exact @GlobalTheory.QFam.isIntegral_value_div | exact GlobalTheory.QFam.isIntegral_value_div | (intros; apply GlobalTheory.QFam.isIntegral_value_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR.FormExtJ

open GlobalTheory.CatCoh

section Inst

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (j : ℕ)

@[reducible] def opModJ : Module Bᵐᵒᵖ (Om R B j) :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModJ

theorem isCentralScalarJ : IsCentralScalar B (Om R B j) := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTowerJ : IsScalarTower R Bᵐᵒᵖ (Om R B j) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

end Inst

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

def extMapJ {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (Om R (F.obj T) j) →ₐ[R] TrivSqZeroExt (F.obj T') (Om R (F.obj T') j) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (pOm F j φ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [pOm_smul]
  commutes' r := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).fst = mp F φ c.fst := by
  simp [extMapJ]

theorem snd_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).snd = pOm F j φ c.snd := by
  simp [extMapJ]

def omjExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
  map φ := CommAlgCat.ofHom (extMapJ F j φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans (mp_id F T _)) ((snd_extMapJ F j _ c).trans (pOm_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).fst
      rw [fst_extMapJ, fst_extMapJ])))
    ((snd_extMapJ F j _ c).trans ((pOm_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).snd
      rw [snd_extMapJ, snd_extMapJ]))))

theorem mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))

theorem snd_mp_omjExt {T T' : C} (φ : T ⟶ T') (c : (omjExt F j).obj T) :
    (mp (omjExt F j) φ c).snd = pOm F j φ c.snd := snd_extMapJ F j φ c

theorem isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))

theorem span_inlJ_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omjExt F j).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (Om R (F.obj S) j))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.CechDR.FormExtJ
end
end

