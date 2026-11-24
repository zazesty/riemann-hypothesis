module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModMat

theorem addEquivAddHaarChar_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  intro F E _ _ _ _ _ σ _ j m _ _ _ _ g a
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E j m g a
  rw [hchar, GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele]
  have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det g ^ m * Matrix.GeneralLinearGroup.det a ^ j) := by
    ext
    simp [hdet]
  rw [hu]
  apply NNReal.eq
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.NormScaleHaar.ideleModule_norm, map_mul, map_pow, map_pow]

end GlobalTheory.ResidueEisenstein.ModMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_skewA_iff {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ ∀ i k, c i k + sigR (AF F) σ (c k i) = 0 := by
  rw [mem_skewA]
  constructor
  · intro h i k
    have := congrFun (congrFun h i) k
    simpa [cT] using this
  · intro h
    ext i k
    simpa [cT] using h i k

theorem cT_apply (σ : E →ₐ[F] E) {j : ℕ} (M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (i k : Fin j) :
    cT (sigR (AF F) σ) M i k = sigR (AF F) σ (M k i) := by
  simp [cT]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR, ← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact cA_cA σ hσ z

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact GlobalTheory.ImaginaryModulus.cA_inclR σ e

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = cA σ :=
    funext fun z => (GlobalTheory.ImaginaryModulus.cA_eq_sigR σ z).symm
  rw [this]
  exact continuous_cA σ

theorem continuous_cT (σ : E →ₐ[F] E) (j : ℕ) :
    Continuous (fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M) := by
  have hs := continuous_sigR σ
  exact continuous_pi fun i => continuous_pi fun k =>
    hs.comp ((continuous_apply i).comp (continuous_apply k))

def split (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) :
    (skewA σ j × skewA σ j) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) where
  toFun p := (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
  invFun M := (⟨inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.sub_apply, cT_apply, smul_eq_mul, map_mul, map_sub, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2]
      ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.add_apply, cT_apply, smul_eq_mul, map_mul, map_add (f := _), sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2, map_inv₀ σ δ, hδ, inv_neg, map_neg]
      ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    rw [mem_skewA_iff] at hx hy
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hx' : ∀ i k, sigR (AF F) σ (x k i) = -x i k := fun i k => eq_neg_of_add_eq_zero_right (hx i k)
    have hy' : ∀ i k, sigR (AF F) σ (y k i) = -y i k := fun i k => eq_neg_of_add_eq_zero_right (hy i k)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * ((x i k + inclR (F := F) (AF F) δ * y i k) -
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i)) = x i k
      rw [map_add (f := _), map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination x i k * hh
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * ((x i k + inclR (F := F) (AF F) δ * y i k) +
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i))) = y i k
      rw [map_add (f := _), map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination (y i k * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y i k * hc
  right_inv M := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    ext i k
    show inclR (F := F) (AF F) (2⁻¹ : E) * (M i k - sigR (AF F) σ (M k i)) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * (M i k + sigR (AF F) σ (M k i)))) = M i k
    linear_combination M i k * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (M i k + sigR (AF F) σ (M k i)) * hc
  map_add' p q := by
    show ((p.1 + q.1 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + _ • ((p.2 + q.2 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = _
    push_cast
    rw [smul_add]
    abel
  continuous_toFun := by
    show Continuous fun p : skewA σ j × skewA σ j => (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul (inclR (F := F) (AF F) δ))
  continuous_invFun := by
    have hc := continuous_cT σ j
    have h1 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M) :=
      (continuous_id.sub hc).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    have h2 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M) :=
      ((continuous_id.add hc).const_smul (inclR (F := F) (AF F) δ⁻¹)).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)

theorem split_apply (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ)
    (p : skewA σ j × skewA σ j) :
    split σ hσ j δ hδ0 hδ p = (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := rfl

end GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

namespace GlobalTheory.ResidueEisenstein.ModConj


open GlobalTheory.ResidueEisenstein.ModConj.SkewSplit in
theorem addEquivAddHaarChar_skewA_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  intro F E _ _ _ _ _ σ hcm j _ _ _ _ l L hL
  haveI : IsTotallyReal F := hcm.1
  have hσ := GlobalTheory.ImaginaryModulus.sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.ImaginaryModulus.exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := hlc
  haveI : SecondCountableTopology (AF F ⊗[F] E) := hsc
  haveI : T2Space (AF F ⊗[F] E) := ht2
  haveI : LocallyCompactSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin j → Fin j → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : T2Space (skewA σ j) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (skewA σ j × skewA σ j) := Prod.borelSpace
  set Φ := split σ hσ j δ hδ0 hδ
  set M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AF F ⊗[F] E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AF F ⊗[F] E) = l * sigR (AF F) σ l := rfl
  have hM : ∀ z, M z = (a : AF F ⊗[F] E) • z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = (a : AF F ⊗[F] E) • Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, split_apply, split_apply, hL, hL, ha,
      smul_add, smul_comm (inclR (F := F) (AF F) δ)]
  set g : GL (Fin j) (AF F ⊗[F] E) := Units.map (Matrix.scalar (Fin j) : (AF F ⊗[F] E) →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a ^ j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
    show (Matrix.scalar (Fin j) (a : AF F ⊗[F] E)).det = _
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT : M = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i k
    rw [hM, GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.mul_one]
    show ((a : AF F ⊗[F] E) • u) i k = (Matrix.scalar (Fin j) (a : AF F ⊗[F] E) * u) i k
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h1 : addEquivAddHaarChar M = absE F E a ^ (j * j) := by
    rw [hT, GlobalTheory.ModuLR.chi_lr F E j j g 1, hg, map_one, map_one, one_pow, mul_one, map_pow, ← pow_mul]
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  have h4 : addEquivAddHaarChar L * addEquivAddHaarChar L = absE F E l ^ (j * j) * absE F E l ^ (j * j) := by
    rw [← h2, h1, h3, mul_pow]
  exact (mul_self_inj (by positivity) (by positivity)).1 h4

end GlobalTheory.ResidueEisenstein.ModConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem adelic_schwartz_slice_l2_word_bound : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  intro F _ _ _ κ _ ψ hψ i j
  obtain ⟨ℓ, hnd, hℓ⟩ := hψ
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) ℝ (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, ⟨Module.finBasis ℝ _⟩⟩
  obtain ⟨K4, hK4, hb4⟩ := _root_.GlobalTheory.continuousMultilinear_norm_le_basis_sum (κ → mixedEmbedding.mixedSpace F) _ b j
  obtain ⟨K5, hK5, hb5⟩ := _root_.GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow (κ → mixedEmbedding.mixedSpace F) _ b i
  choose u hu using fun c => _root_.GlobalTheory.dualform F κ ℓ hnd (b.coord c)
  let ia : Option (Fin n) → ℕ := fun a => a.elim 0 (fun _ => i)
  let ua : Option (Fin n) → (κ → mixedEmbedding.mixedSpace F) := fun a => a.elim 0 u
  let wd : Option (Fin n) × (Fin j → Fin n) →
      List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    fun p => List.replicate (ia p.1) (0, ua p.1) ++ (List.ofFn fun r => b (p.2 r)).map fun v => (v, 0)
  refine ⟨Finset.univ.toList.map wd, (K5 * K4) ^ 2 * (Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ),
    fun Φ hΦ y => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hΦ y
  have hsf : (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = s := funext fun x => (hs x).symm
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := hsf ▸ s.smooth ⊤
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have key : ∀ p x, GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * ua p.1 k) : ℂ)) ^ (ia p.1) *
        iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r)) := by
    intro p x
    rw [_root_.GlobalTheory.WeilL2Words.slice_word_mul_fderivs F κ ψ ℓ hℓ Φ y hsm, _root_.GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv _ _ hsm]
  have hcont : ∀ p, Continuous fun x => GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
    intro p
    simp_rw [key]
    have h1 : Continuous fun x : κ → mixedEmbedding.mixedSpace F => ∑ k, x k * ua p.1 k := by fun_prop
    have h2 : Continuous fun x => iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hℓc.comp h1))).pow _).mul
      ((ContinuousMultilinearMap.apply ℝ _ ℂ (fun r => b (p.2 r))).continuous.comp h2)
  rw [List.map_map, Finset.sum_map_toList]
  refine GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise _ MeasureTheory.volume _ _ _ _ hcont fun x => ?_
  have hterm : ∀ p : Option (Fin n) × (Fin j → Fin n),
      p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ ≤
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    intro p
    rw [key, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases p with ⟨_ | c, cs⟩
    · simp [ia]
    · simp only [Option.elim, ia, ua, hu, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [mul_pow]
      refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
  have h1 : ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤
      K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    calc _ ≤ (K5 * (1 + ∑ c, |b.coord c x| ^ i)) *
          (K4 * ∑ cs : Fin j → Fin n, ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x
            (fun r => b (cs r))‖) :=
          mul_le_mul (hb5 x) (hb4 _) (norm_nonneg _) (by positivity)
      _ = K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n), p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ := by
          rw [Fintype.sum_prod_type, Fintype.sum_option]
          simp only [Option.elim, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          gcongr with p
          exact hterm p
  have h0 : 0 ≤ ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ := by positivity
  calc _ ≤ (K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (K5 * K4) ^ 2 * (∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := by ring
    _ ≤ (K5 * K4) ^ 2 * ((Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ) * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
    _ = _ := by ring

end GlobalTheory.WeilL2Words
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
namespace GlobalTheory.WeilL2Words
open NumberField IsDedekindDomain

theorem adeleOfMixedSpaceComponent_add (F : Type) [Field F] [NumberField F] (z w : mixedEmbedding.mixedSpace F) :
    arch1 F (z + w) = arch1 F z + arch1 F w :=
  Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z w) (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem mul_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    a * arch1 F z = arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * z) := by
  refine Prod.ext ?_ ?_
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

theorem adeleOfMixedSpaceComponent_zero (F : Type) [Field F] [NumberField F] : arch1 F 0 = 0 :=
  Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl

theorem add_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (a + arch1 F z).1 = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 + z ∧
    (a + arch1 F z).2 = a.2 := by
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = _
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  · exact add_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

def arch1Hom (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F where
  toFun := arch1 F
  map_zero' := adeleOfMixedSpaceComponent_zero F
  map_add' := adeleOfMixedSpaceComponent_add F

theorem adeleOfMixedSpaceComponent_finsetSum (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (z : ι → mixedEmbedding.mixedSpace F) :
    arch1 F (∑ i ∈ s, z i) = ∑ i ∈ s, arch1 F (z i) :=
  map_sum (arch1Hom F) z s

theorem dotProduct_arch (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : κ → AdeleRing (𝓞 F) F)
    (y : κ → mixedEmbedding.mixedSpace F) :
    a ⬝ᵥ arch F y = arch1 F (∑ k, InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 * y k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  exact Finset.sum_congr rfl fun k _ => mul_arch1' F (a k) (y k)

theorem fst_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (arch1 F z).1 = z :=
  RingEquiv.apply_symm_apply _ z

theorem dS_sum_pureA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro F _ _ _ κ _ ψ hψ m g f h
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Complex.ofRealCLM.toLinearMap.comp (ℓ.comp M))
  have hL : ∀ X, L X = ((ℓ (∑ k, X k * h.2 k) : ℝ) : ℂ) := by
    intro X
    simp [L, M]
  have hg : (fun X => (2 * Real.pi * Complex.I) * L X).HasTemperateGrowth :=
    ((2 * Real.pi * Complex.I) • L).hasTemperateGrowth
  refine ⟨fun i => SchwartzMap.smulLeftCLM ℂ (fun X => (2 * Real.pi * Complex.I) * L X) (f i) +
    LineDeriv.lineDerivOp h.1 (f i), ?_⟩
  funext a
  set X : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 with hX
  set Y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2 with hY
  set c : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 with hc
  set A : ℝ := ℓ (∑ k, X k * h.2 k) with hA
  set B : ℝ := ℓ (c * ∑ k, h.1 k * h.2 k) with hB
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) *
        ∑ i, f i (X + t • h.1) * g i Y := by
    funext t
    unfold GlobalTheory.WeilM.schr
    congr 1
    · have e0 : (archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2 =
          arch1 F (∑ k, (t • h.1) k * (t • h.2) k) := by
        rw [archPair, dotProduct_arch]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· * (t • h).2 k) (fst_arch1 F ((t • h).1 k))
      have e1 : a ⬝ᵥ (archPair F (t • h)).2 + ⅟(2 : AdeleRing (𝓞 F) F) * ((archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2)
          = arch1 F (t • (∑ k, X k * h.2 k) + t ^ 2 • (c * ∑ k, h.1 k * h.2 k)) := by
        rw [e0, mul_arch1', archPair, dotProduct_arch, ← adeleOfMixedSpaceComponent_add]
        congr 1
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum,
          Finset.mul_sum, smul_smul, pow_two]
        rfl
      rw [e1, hℓ, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + (archPair F (t • h)).1) k).1) = X + t • h.1 :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).1
      have hy : (fun k => ((a + (archPair F (t • h)).1) k).2) = Y :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).2
      unfold GlobalTheory.WeilM.pureA
      rw [hx, hy]

  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((f i).hasFDerivAt (X + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add X)).mul_const (g i Y))
  have hT := hφ.cexp.fun_mul hS
  unfold dS
  rw [key]
  refine (HasDerivAt.deriv hT).trans ?_
  simp only [Finset.sum_apply, GlobalTheory.WeilM.pureA, SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [hL, ← hA]
  simp only [← hX, ← hY, ← hA, id, zero_smul, add_zero, one_smul, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [show ((0:ℝ) ^ (2 - 1)) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring
end GlobalTheory.WeilL2Words
end
end

