module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.JSW.Bialt

lemma coeff_prod_one_sub_eq_zero {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι) :
    ∀ r, s.card < r →
      PowerSeries.coeff r (∏ k ∈ s, (1 - PowerSeries.C (a k) * PowerSeries.X : PowerSeries R)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    rw [prod_empty, PowerSeries.coeff_one, if_neg (by simp at hr; omega)]
  | insert k s hk ih =>
    intro r hr
    rw [card_insert_of_notMem hk] at hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [prod_insert hk, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, ih _ (by omega), ih _ (by omega), mul_zero, sub_zero]

def ec (n : ℕ) (i : Fin n) (r : ℕ) : MvPolynomial (Fin n) ℤ :=
  PowerSeries.coeff r (∏ k ∈ univ.erase i,
    (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X))

lemma ec_eq_zero {n : ℕ} (i : Fin n) {r : ℕ} (hr : n ≤ r) : ec n i r = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have := i.2
  omega

lemma sum_ec_hsymm {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range (a + 1), ec n i r * MvPolynomial.hsymm (Fin n) ℤ (a - r) = MvPolynomial.X i ^ a := by
  have hAB : (∏ k ∈ univ.erase i,
      (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X)) *
      (∏ j : Fin n, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial (Fin n) ℤ) ^ m)) =
      PowerSeries.mk (fun m => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m) := by
    rw [← prod_erase_mul _ _ (mem_univ i), ← mul_assoc, ← prod_mul_distrib,
      prod_eq_one fun j _ => Formalism.FT.SymmetricSeries.geom_mul _, one_mul]
  have h := congrArg (PowerSeries.coeff a) hAB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Formalism.FT.SymmetricSeries.coeff_prod_geom, ec] using h

lemma sum_ec_hsymm' {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      MvPolynomial.X i ^ a := by
  rw [← sum_ec_hsymm i a]
  have h1 : ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [ec_eq_zero i (by simpa using hr), zero_mul]
  have h2 : ∑ r ∈ range (a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [if_pos (by simp at hr; omega), mul_zero]
  rw [h1, ← h2]
  refine sum_congr rfl fun r hr => ?_
  rw [if_neg (by simp at hr; omega)]

lemma pow_matrix_eq (n : ℕ) (α : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (α j)) =
      (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) *
        (Matrix.of fun m j : Fin n => if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.of_apply, ← sum_ec_hsymm' i (α j), ← sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun m => ec n i (n - 1 - m) * (if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))))]
  rfl

lemma det_pow_matrix (n : ℕ) (l : Fin n → ℕ) :
    Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) * schur n l := by
  rw [pow_matrix_eq n (fun j => l j + n - 1 - (j : ℕ)), Matrix.det_mul, schur, ← Matrix.det_transpose (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))]
  congr 2
  refine Matrix.ext fun m j => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hm := m.2
  have hj := j.2
  by_cases h : ((l j : ℤ) - j + m) < 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    congr 1
    omega

lemma schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · refine prod_eq_one fun i _ => ?_
    simp [MvPolynomial.hsymm_zero]
  · intro i j hij
    have : (j : ℕ) < i := hij
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

end GlobalTheory.JSW.Bialt

namespace GlobalTheory.JSW

theorem schur_mul_det_eq_det (n : ℕ) (l : Fin n → ℕ) (_hl : Antitone l) :
    schur n l * Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  have h0 := Bialt.det_pow_matrix n (fun _ => 0)
  simp only [zero_add, Bialt.schur_zero, mul_one] at h0
  rw [h0, Bialt.det_pow_matrix n l, mul_comm]

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursion
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.WhittakerRecursion

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
open scoped ValuativeRel

theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

theorem mem_minusculeSet_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem finsum_minuscule {f : GL (Fin n) F → ℂ} (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g) {l : Fin n → ℤ} (hl : Antitone l) (r : ℕ) :
    ∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
        (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) x.out • f (torusPow F n l * x.out) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  letI : MeasurableSpace (GL (Fin n) F) := borel _
  haveI : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard r).biUnion
    fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)
  rw [finsum_eq_sum_of_support_subset (s := Cs)]
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rw [Finset.sum_image fun c _ c' _ h => gMat_injective S h]
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (sum_gMat_torusPow hN hl S)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)
      have hm := mul_mem_minusculeSet (hSr ▸ gMat_mem_minusculeSet (F := F) S c) (one_mem _) k.2
      rw [one_mul] at hm
      rw [hk, Set.indicator_of_mem hm, one_smul, ← mul_assoc, hf _ k k.2]
    · intro S _ S' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_gMat] at this
      exact hne (lamS_injective this).symm
  · intro x hx
    have hm : x.out ∈ minusculeSet F n r := by
      by_contra hm
      apply hx
      simp only [Set.indicator_of_notMem hm, zero_smul]
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩,
      Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

theorem sqrtQ_zpow (m : ℤ) : sqrtQ F ^ m = (qF F : ℂ) ^ ((m : ℂ) / 2) := by
  rw [div_eq_inv_mul, Complex.cpow_mul_int]
  congr 1
  rw [sqrtQ, Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

theorem cpow_eq_sqrtQ (m : Fin n → ℕ) :
    (qF F : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * ((m k : ℕ) : ℂ))) / 2) =
      sqrtQ F ^ rhoPair (fun i => (m i : ℤ)) := by
  rw [sqrtQ_zpow, rhoPair]
  push_cast
  rfl

end Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}


variable (w n) in
theorem integralGL_eq : integralGL (w.adicCompletion E) n = GLint (Fin n) (Ov E w) := by
  have hO : Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
    Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
  rw [hO]
  rfl


variable (w) in
theorem isUnifV_uniformizer : IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) :=
  GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)


variable (w) in
theorem Tj_eq_indicator {r : ℕ} (hr : r ≤ n) :
    Tj ℂ n (Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ) := by
  unfold Tj
  rw [← integralGL_eq]
  congr 1
  ext g
  exact (mem_minusculeSet_iff hr g).symm

theorem apply_diag_eq {W : GL (Fin n) (w.adicCompletion E) → ℂ}
    (hK : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g)
    {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (m : Fin n → ℕ) :
    W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
      (MulEquiv.piUnits.symm fun i => ϖ ^ m i)) = W (torusPow (w.adicCompletion E) n fun i => (m i : ℤ)) := by
  have hπ := isUnifV_uniformizer w
  set d : Fin n → (w.adicCompletion E)ˣ := fun i => ((uniformizerUnit (w.adicCompletion E))⁻¹ * ϖ) ^ m i
  have hv : ∀ i, Valued.v (d i : w.adicCompletion E) = 1 := fun i => by
    simp only [d, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, coe_uniformizerUnit, map_pow,
      map_mul, map_inv₀]
    rw [hπ, hϖ, inv_mul_cancel₀ WithZero.coe_ne_zero, one_pow]
  have hd : diagGL (w.adicCompletion E) n d ∈ integralGL (w.adicCompletion E) n := by
    rw [mem_integralGL_iff, ← map_inv]
    constructor <;> intro i j <;> rw [coe_diagGL, Matrix.diagonal_apply] <;> split_ifs
    · exact (GroundTheory.Global.mem_valuationInteger_iff w _).2 (hv i).le
    · exact zero_mem _
    · refine (GroundTheory.Global.mem_valuationInteger_iff w _).2 ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    · exact zero_mem _
  rw [← hK (torusPow _ _ _) _ hd, torusPow, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [coe_diagGL]
  change Matrix.diagonal _ = _
  congr 1
  funext i
  simp [d, mul_pow]

theorem recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  intro E _ _ w n ψ hψ W α hN hK hT ϖ hϖ l hl j hj
  have hKK : integralGL (w.adicCompletion E) n = KGL w (n := n) := integralGL_eq w n
  have hπ := isUnifV_uniformizer w
  have hq : qF (w.adicCompletion E) = qV E w := by
    unfold qF qV
    rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : sqrtQ (w.adicCompletion E) ^ (j * (n - j)) = (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    rw [← zpow_natCast, sqrtQ_zpow, hq]
    push_cast [Nat.cast_sub hj]
    rfl
  have hK' : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g := hKK ▸ hK
  have hN' : ∀ u ∈ unipotent (w.adicCompletion E) n ⊓ integralGL (w.adicCompletion E) n, ∀ g, W (u * g) = W g := by
    intro u hu g
    obtain ⟨hu, hi⟩ := (mem_unipotent_inf_integralGL_iff _ n).1 hu
    rw [hN u ((GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => hu.1 hij, hu.2⟩)]
    have h1 : GlobalTheory.Whittaker.superDiag u ∈ Ov E w := by
      unfold GlobalTheory.Whittaker.superDiag
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      exact (GroundTheory.Global.mem_valuationInteger_iff w _).1 (hi i j)
    have h2 := (hψ 1).2 (one_mem _) _ h1
    rw [one_mul] at h2
    rw [h2, one_mul]
  have hl' : Antitone fun i => (l i : ℤ) := fun a b h => Int.ofNat_le.2 (hl h)
  have h := congrFun (hT _ hπ j hj) (torusPow (w.adicCompletion E) n fun i => (l i : ℤ))
  rw [heckeVec_rightReg (Final.GLintComm E w n) (Tj_mem_hecke hπ j),
    Tj_eq_indicator w hj, hAct, ← integralGL_eq w n, finsum_minuscule hK' hN' hl', satEig, ← hsq,
    Multiset.map_map, Pi.smul_apply, smul_eq_mul] at h
  have h0 : sqrtQ (w.adicCompletion E) ≠ 0 := sqrtQ_ne_zero
  refine mul_left_cancel₀ (pow_ne_zero (j * (n - j)) h0) ?_
  rw [apply_diag_eq hK' hϖ, ← hq, cpow_eq_sqrtQ, Finset.mul_sum]
  have e : (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j) = Finset.univ.powersetCard j := by
    ext J; simp [Finset.mem_powersetCard]
  rw [e]
  refine Eq.trans ?_ ((congrArg (sqrtQ (w.adicCompletion E) ^ rhoPair (fun i => (l i : ℤ)) * ·) h).trans (by
    simp only [Function.comp_def]; ring))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc : (fun i => (((l + (fun i => if i ∈ S then 1 else 0) : Fin n → ℕ) i : ℕ) : ℤ)) =
      (fun i => (l i : ℤ)) + lamS S := by
    funext i
    simp [lamS]
  have hr : rhoPair ((fun i => (l i : ℤ)) + lamS S) = rhoPair (fun i => (l i : ℤ)) + rhoPair (lamS S) := by
    simp [rhoPair, mul_add, Finset.sum_add_distrib]
  rw [apply_diag_eq hK' hϖ, cpow_eq_sqrtQ, hc, ← kappa_mul_halfModulus hj (Finset.mem_powersetCard.1 hS).2,
    halfModulus_eq, hr, zpow_add₀ h0, zpow_neg]
  have := zpow_ne_zero (rhoPair (lamS S)) h0
  field_simp

end GlobalTheory.WhittakerRecursion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableKerRepsAddSub
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) + w) := by
  intro ω hω
  rw [add_mul]
  refine add_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem mulStable_intCast_sub {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) - w) := by
  intro ω hω
  rw [sub_mul]
  refine sub_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem ringEquiv_sqrtNegNat (σ : ℂ ≃+* ℂ) (p : ℕ) :
    σ (sqrtNegNat p) = sqrtNegNat p ∨ σ (sqrtNegNat p) = -sqrtNegNat p := by
  have h : σ (sqrtNegNat p) ^ 2 = sqrtNegNat p ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem stable_kerReps_add_sub : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (a : ℤ) (S S' : Finset ℂ), L.g₂ ∈ F → L.g₃ ∈ F → MulStable L (sqrtNegNat p) → IsKerReps L (a + sqrtNegNat p) S → IsKerReps L (a - sqrtNegNat p) S' → Stable L F (Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ))) := by
  intro p F L a S S' h2 h3 hm hS hS' σ hσ
  have e2 : L.g₂ = σ L.g₂ := (hσ _ h2).symm
  have e3 : L.g₃ = σ L.g₃ := (hσ _ h3).symm
  have mp := mulStable_intCast_add a hm
  have mm := mulStable_intCast_sub a hm
  have hσa : σ (a : ℂ) = a := map_intCast σ a
  rcases ringEquiv_sqrtNegNat σ p with hs | hs
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by rw [map_add (f := _), hσa, hs]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by rw [map_sub, hσa, hs]
    obtain ⟨e, he⟩ := _root_.GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj L σ _ S S e2 e3 mp hS (by rw [hp]; exact hS)
    obtain ⟨e', he'⟩ := _root_.GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj L σ _ S' S' e2 e3 mm hS' (by rw [hm']; exact hS')
    refine ⟨Equiv.sumCongr e e', ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by
      rw [map_add (f := _), hσa, hs, sub_eq_add_neg]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by
      rw [map_sub, hσa, hs, sub_neg_eq_add]
    obtain ⟨e, he⟩ := _root_.GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj L σ _ S S' e2 e3 mp hS (by rw [hp]; exact hS')
    obtain ⟨e', he'⟩ := _root_.GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj L σ _ S' S e2 e3 mm hS' (by rw [hm']; exact hS)
    refine ⟨(Equiv.sumCongr e e').trans (Equiv.sumComm _ _), ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictAntiOfStep
section
open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem strictAnti_of_step {N : ℕ} {α : Type} [Preorder α] (f : Fin N → α)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

theorem divided_strictAnti : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ,
    StrictAnti (W.u1 τ) ∧ StrictAnti (W.u' τ) ∧ StrictAnti (fun i => (W.u1 τ i : ℝ)) := by
  intro ι _ N W H hD τ
  have hT : (4 : ℤ) ≤ W.T := by have := H.h1; omega
  have hh : (0 : ℤ) < W.h0 := by
    obtain ⟨k1, _⟩ := H.h2
    have := H.weightConst_nonneg
    omega
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a := by
    intro a b hab
    obtain ⟨g1, g2, _⟩ := divided_gaps ι N W H hD τ a b hab
    by_cases hb : (b : ℕ) = W.p
    · obtain ⟨e1, e2⟩ := g2 hb
      have ha : ¬ ((b : ℕ) < W.p) := by omega
      have ha' : (a : ℕ) < W.p := by omega
      have p1 : 0 < W.u1 τ a - W.u1 τ b := by
        by_contra hc
        push_neg at hc
        nlinarith
      have p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N := by
        by_contra hc
        push_neg at hc
        nlinarith
      refine ⟨by omega, ?_⟩
      simp only [Wts.u', if_pos ha', if_neg ha]
      omega
    · have e := g1 hb
      have hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N := by positivity
      refine ⟨by omega, ?_⟩
      simp only [Wts.u']
      by_cases ha : (a : ℕ) < W.p
      · have hb' : (b : ℕ) < W.p := by omega
        rw [if_pos ha, if_pos hb']; omega
      · have hb' : ¬ (b : ℕ) < W.p := by omega
        rw [if_neg ha, if_neg hb']; omega
  have s1 : StrictAnti (W.u1 τ) := strictAnti_of_step _ fun a b h => (step a b h).1
  exact ⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2,
    (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩

end GlobalTheory.MeanTop
end

