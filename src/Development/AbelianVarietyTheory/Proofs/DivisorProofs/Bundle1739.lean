module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallFStdB
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.StdPairZetaB
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem cball_mul_left {m n : ℕ} {s : kˣ} {M : Matrix (Fin m) (Fin m) k} (hM : ∀ i j, M i j ∈ 𝒪[k])
    {N : Matrix (Fin m) (Fin n) k} (hN : ∀ i j, N i j ∈ cball s) : ∀ i j, (M * N) i j ∈ cball s := fun i j => by
  have hN' : ∀ i j, valuation k (N i j) ≤ valuation k (s : k) := hN
  change valuation k _ ≤ valuation k (s : k)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hM i l) (hN' l j)).trans (by rw [one_mul])

theorem mem_KO_of_isGLO {n : ℕ} (g : GL (Fin n) k) (h : IsGLO g.val) : g ∈ KO k (Fin n) := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h.1 i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e]; exact h.2
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem isGLO_of_mem_KO {n : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) : IsGLO g.val :=
  ⟨((mem_KO_iff g).1 h).1, valuation_gdet_of_mem_KO h⟩

end GlobalTheory.StdPairZetaB


open GlobalTheory.StdPairZetaB in
theorem GlobalTheory.StdPairZetaB.smallF_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ),
    (∀ Y : Matrix (Fin a') (Fin (a + a')) k, (blk₂ Y).det = 0 →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0) ∧
    ∀ (Y : Matrix (Fin a') (Fin (a + a')) k) (g₂ : GL (Fin a') k), g₂.val = blk₂ Y →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
        (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) := by
  intro k _ _ _ _ _ _ ν ϖ c a a'
  refine ⟨fun Y hY => ?_, fun Y g₂ hg₂ => ?_⟩
  · have h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0 := fun g => by
      unfold stdB
      rw [dite_eq_right]
      rintro ⟨h0, -⟩
      apply h0
      rw [blk₂_mul_left, Matrix.det_mul, hY, mul_zero]
    simp [smallF, h0]
  · set d : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hd
    set C : ℂ := (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d) *
      Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) with hC
    set S : Set (GL (Fin a') k) := (fun g => g * g₂) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
    have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
      letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
      haveI : BorelSpace (GL (Fin a') k) := borel_GL
      exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
    have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
      simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
    have hint : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) d =
        S.indicator (fun _ => C) g := by
      intro g
      have hb₂ : blk₂ (g.val * Y) = g.val * blk₂ Y := blk₂_mul_left _ _
      have hb₁ : blk₁ (g.val * Y) = g.val * blk₁ Y := blk₁_mul_left _ _
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hκ : g * g₂ ∈ KO k (Fin a') := hg
        have hG := isGLO_of_mem_KO hκ
        have e₂ : blk₂ (g.val * Y) = (g * g₂).val := by rw [hb₂, ← hg₂, Units.val_mul]
        have e₁ : blk₁ (g.val * Y) = (g * g₂).val * ((g₂⁻¹).val * blk₁ Y) := by
          rw [hb₁, ← Matrix.mul_assoc, Units.val_mul, Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
        have hgd : gdet g = gdet (g * g₂) * (gdet g₂)⁻¹ := by rw [gdet_mul]; group
        have hap : apow (gdet g) d = apow (gdet g₂) (-d) := by
          rw [hgd, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hκ), one_mul, apow_inv]
        unfold stdB
        by_cases hP : ∀ i j, ((g₂⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
        · have hcond : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
            rw [e₂, e₁]
            exact ⟨(g * g₂).det_ne_zero, hG, cball_mul_left hG.1 hP⟩
          rw [dite_eq_left hcond, hC, Set.indicator_of_mem (show ((g₂⁻¹).val * blk₁ Y) ∈
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP), Pi.one_apply, mul_one, hap]
          have hu : Units.mk0 _ hcond.1 = gdet g * gdet g₂ := Units.ext (by
            rw [Units.val_mk0, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
              Matrix.GeneralLinearGroup.val_det_apply, hb₂, ← hg₂, Matrix.det_mul])
          rw [hu, map_mul, mul_inv_rev, Units.val_mul]
          have h1 : ((ν (gdet g))⁻¹ : ℂˣ) * (ν (gdet g) : ℂ) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          linear_combination ((((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d)) * h1
        · have hcond : ¬ ((blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
            rintro ⟨-, -, h3⟩
            apply hP
            have hinv := (mem_KO_iff (g * g₂)).1 hκ
            have := cball_mul_left hinv.2 h3
            rwa [e₁, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
          rw [dite_eq_right hcond, hC, Set.indicator_of_notMem (show ((g₂⁻¹).val * blk₁ Y) ∉
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP)]
          simp
      · rw [Set.indicator_of_notMem hg]
        unfold stdB
        rw [dite_eq_right, zero_mul, zero_mul]
        rintro ⟨-, h2, -⟩
        apply hg
        show g * g₂ ∈ KO k (Fin a')
        apply mem_KO_of_isGLO
        rwa [Units.val_mul, hg₂, ← hb₂]
    rw [smallF, ← hd]
    simp_rw [hint]
    rw [integral_indicator_const (μ := haarVol (KO k (Fin a'))) C hSm, hS1, one_smul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

theorem smul_mem_scLat_of_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} {a : E} (ha : a ∈ 𝔞) {y : Fin n → E} (hy : y ∈ Λ) :
    a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
  intro c hc
  have h : a * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    FractionalIdeal.mul_one_div_le_one (FractionalIdeal.mul_mem_mul ha hc)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
  rw [smul_smul, mul_comm, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hy

theorem divG_gen {D : D7} (S : HSp D) {n : ℕ} (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin n → D.host.E) (p : Fin n) (q : Fin S.rank) :
    divG S (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) p q =
      β ⊗ₜ[D.host.F] (a * t p * star (s q)) := by
  have h : (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : Matrix _ _ (AE D)) =
      mulG S (Matrix.of fun i k => β ⊗ₜ[D.host.F] (a * t i * star (s k))) := by
    ext i j
    rw [mulG_eq, Matrix.mul_apply]
    simp only [of_apply, map_apply, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = (β ⊗ₜ[D.host.F] (a * t i * star (s k))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc (a * t i)]
  rw [h, divG_mulG, of_apply]

theorem divG_zero {D : D7} (S : HSp D) {n : ℕ} : divG S (0 : Matrix (Fin n) (Fin S.rank) (AE D)) = 0 :=
  Matrix.zero_mul _

theorem divG_neg {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (-x) = -divG S x :=
  Matrix.neg_mul _ _

theorem smul_incM_apply {D : D7} {m n : Type} (β : AF D.host.F) (M : Matrix m n D.host.E) (p : m) (q : n) :
    (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F M) p q = β ⊗ₜ[D.host.F] M p q := by
  change β • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M p q) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem one_smul_gen_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {α : Af F} (hα : α ∈ intAf F) {x : Fin n → E} (hx : x ∈ X.L)
    {y : Fin d → E} (hy : y ∈ Y.L) :
    GlobalTheory.LatVac.liftV v 1 • pairA F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (vecMulVec x y) ∈ latAtV X Y v := by
  rw [smul_smul]
  refine AddSubgroup.subset_closure ⟨_, ?_, ?_, x, hx, y, hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_mul]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
    exact hα v

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inl (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV G i j).rank) :
    ofMaps e x p (e (.inl k)) = divG (negSp (spW G i j)) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inr (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV₁ G i j).rank) :
    ofMaps e x p (e (.inr k)) = cA D (divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genV (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW G i j).rank → D.host.E)
    (t : Fin (spV G i j).rank → D.host.E) :
    ofMaps e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (negSp (spW G i j)).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • t) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((divG_gen (negSp (spW G i j)) β a s t k p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero, divG_zero,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genW (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (t : Fin (spW G i j).rank → D.host.E) :
    ofMaps e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (spV₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star (-t)) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((congrFun (congrFun (divG_zero (negSp (spW G i j))) k) p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, divG_neg, Matrix.neg_apply,
      divG_gen, ← TensorProduct.tmul_neg]
    change β ⊗ₜ[D.host.F] star (-(a * t p * star (s k))) = β ⊗ₜ[D.host.F] (star (-t p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem map_mem_of_closure {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {s : Set A} {H : AddSubgroup B}
    (h : ∀ x ∈ s, f x ∈ H) {x : A} (hx : x ∈ AddSubgroup.closure s) : f x ∈ H :=
  (AddSubgroup.closure_le (H.comap f)).2 h hx

theorem pair_mem {E : Type} [Field E] [NumberField E] {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)}
    {ΛB : Submodule (𝓞 E) (Fin b → E)} (e : Fin a ⊕ Fin b ≃ Fin d) {x : Fin a → E} {y : Fin b → E} (hx : x ∈ ΛA) (hy : y ∈ ΛB) :
    Sum.elim x y ∘ e.symm ∈ GlobalTheory.SkewLat.pairLat ΛA ΛB e := by
  rw [GlobalTheory.SkewLat.mem_pairLat]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  exact ⟨hx, hy⟩

theorem star_mem_conjSub {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {y : Fin n → E} (hy : y ∈ Λ) : star y ∈ GlobalTheory.TripleSpaceW.conjSub Λ := by
  rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hy

theorem smul_ofMaps_inl_mem {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomV G i j} (hx : x ∈ latV G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (x, 0) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribSMul.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genV e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub hs))
      (h.2.1.ge (pair_mem e (smul_mem_scLat_of_mem ha ht) (zero_mem _))))

theorem smul_ofMaps_inr_mem {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomW G i j} (hx : x ∈ latW G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (0, x) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribSMul.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genW e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub (neg_mem ht)))
      (h.2.1.ge (pair_mem e (zero_mem _) (star_mem_conjSub (smul_mem_scLat_of_mem ha (star_mem_conjSub hs))))))

theorem latPt_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTied t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps e (mapV e u, 0) + ofMaps e (0, mapW e u) :=
    ((ofMaps_maps e u).symm.trans (congrArg (ofMaps e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps e).symm (mapV e u, 0) (0, mapW e u))
  have e3 := add_mem (smul_ofMaps_inl_mem h v h1) (smul_ofMaps_inr_mem h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.BigDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairs
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SUGenPairs

open GlobalTheory.UnRep Matrix

section Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem refl_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E) :
    k * refl c G x u = refl c G (k *ᵥ x) u * k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ReflLaws.refl_mulVec, ReflLaws.refl_mulVec, hk, hk, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem refl_conj' {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E)
    (X : Matrix (Fin n) (Fin n) E) : k * (refl c G x u * X) = refl c G (k *ᵥ x) u * (k * X) := by
  rw [← mul_assoc, refl_conj hk, mul_assoc]

theorem det_refl (x : Fin n → E) (u : E) (hx : hermE c G x x ≠ 0) : (refl c G x u).det = u := by
  rw [GlobalTheory.UnRep.refl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, ← ReflLaws.hermE_eq_dot, div_mul_cancel₀ _ hx]
  ring

theorem det_prod (l : List ((Fin n → E) × E)) (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0) :
    (l.map fun p => refl c G p.1 p.2).prod.det = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.det_mul]
    rw [det_refl _ _ (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

theorem prod_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (P : List ((Fin n → E) × (Fin n → E) × E)) :
    k * (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod =
      ((P.map fun p => (k *ᵥ p.1, k *ᵥ p.2.1, p.2.2)).map
        fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * k := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc, refl_conj' hk, ih]

theorem tele (hG : IsHermForm c G) (x₀ : Fin n → E) (h₀ : hermE c G x₀ x₀ ≠ 0) :
    ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
    ∃ P : List ((Fin n → E) × (Fin n → E) × E),
      (∀ p ∈ P, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * c p.2.2 = 1) ∧
      (l.map fun p => refl c G p.1 p.2).prod =
        (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * refl c G x₀ (l.map Prod.snd).prod := by
  have L := ReflLaws.refl_laws F E c n G hG x₀ h₀
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp, by simp [L.2.1]⟩
  | cons q l ih =>
    intro hl
    obtain ⟨P, hP, e⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    have hk : IsUnE c G (refl c G x₀ q.2) := L.2.2.2 q.2 hq2
    refine ⟨(q.1, x₀, q.2) :: P.map (fun p => (refl c G x₀ q.2 *ᵥ p.1, refl c G x₀ q.2 *ᵥ p.2.1, p.2.2)), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hq1, h₀, hq2⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨a1, a2, a3⟩ := hP p' hp'
        exact ⟨by rw [hk]; exact a1, by rw [hk]; exact a2, a3⟩
    · have hcu : refl c G x₀ (c q.2) * refl c G x₀ q.2 = 1 := by
        rw [L.2.2.1, mul_comm, hq2, L.2.1]
      have hc := prod_conj hk P
      simp only [List.map_cons, List.prod_cons]
      rw [e, ← L.2.2.1 q.2]
      calc refl c G q.1 q.2 * ((P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod *
              refl c G x₀ (l.map Prod.snd).prod)
          = refl c G q.1 q.2 * ((refl c G x₀ (c q.2) * refl c G x₀ q.2) *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by rw [hcu, one_mul, mul_assoc]
        _ = refl c G q.1 q.2 * refl c G x₀ (c q.2) * (refl c G x₀ q.2 *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]

end Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjE_apply (hcm : IsCMExt F E σ) (x : E) : GlobalTheory.WeilTwistF.conjE hcm x = σ x := rfl

theorem hermE_transpose (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = (fun b => σ (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [hermE, conjE_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermE_eq_hE (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = hE σ J y x := by
  rw [hermE_transpose]
  simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem isUnE_of (hcm : IsCMExt F E σ) {n : ℕ} (J m : Matrix (Fin n) (Fin n) E) (h : (m.map σ)ᵀ * J * m = J) :
    IsUnE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ m := by
  have e1 : ∀ y : Fin n → E, (fun b => σ ((m *ᵥ y) b)) = m.map σ *ᵥ (fun b => σ (y b)) := fun y => by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  intro x y
  have e : (fun b => σ ((m *ᵥ y) b)) ⬝ᵥ J *ᵥ (m *ᵥ x) = (fun b => σ (y b)) ⬝ᵥ ((m.map σ)ᵀ * J * m) *ᵥ x := by
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [hermE_transpose, hermE_transpose, e, h]

theorem qr_eq_refl (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = GlobalTheory.UnRep.refl (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x u := by
  rw [GlobalTheory.SUAssemble.qr, GlobalTheory.UnRep.refl, hermE_eq_hE, Matrix.mulVec_transpose]
  rfl

end GlobalTheory.SUGenPairs


open GlobalTheory.UnRep GlobalTheory.SUGenPairs in
theorem GlobalTheory.SUGenPairs.eq_prod_pairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  intro F E _ _ _ _ _ σ hcm M J hJ g hg hdet
  have hG : IsHermForm (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ :=
    ⟨fun x => (GlobalTheory.WeilTwistF.conjE hcm).apply_symm_apply x, GlobalTheory.WeilTwistF.conjE_ne hcm, fun a b => hJ.1 a b,
      by rw [Matrix.det_transpose]; exact hJ.2⟩
  have hu : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  obtain ⟨l, hl, hgl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl F E _ M Jᵀ hG _ (isUnE_of hcm J _ hu)
  have hne : ∀ x : Fin M → E, hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x x ≠ 0 → hE σ J x x ≠ 0 := fun x hx => by
    rwa [← hermE_eq_hE hcm]
  cases l with
  | nil => exact ⟨[], by simp, by simpa using hgl⟩
  | cons q l' =>
    obtain ⟨P, hP, e⟩ := tele hG q.1 (hl q List.mem_cons_self).1 (q :: l') hl
    have ha : ((q :: l').map Prod.snd).prod = 1 := by
      rw [← det_prod _ (fun p hp => (hl p hp).1), ← hgl, hdet]
    rw [ha, (ReflLaws.refl_laws F E _ M Jᵀ hG q.1 (hl q List.mem_cons_self).1).2.1, mul_one] at e
    refine ⟨P, fun p hp => ⟨hne _ (hP p hp).1, hne _ (hP p hp).2.1, (hP p hp).2.2⟩, ?_⟩
    rw [hgl, e]
    congr 2
    funext p
    rw [qr_eq_refl hcm, qr_eq_refl hcm]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquiv
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealConjFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mem_UAt {n : ℕ} {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) :
    g⁻¹ ∈ UAt σ X (evI F) := by
  intro u hu
  have h1 : u • (mat g - 1) = 0 := hg u hu
  have hm : mat g⁻¹ * mat g = 1 := by simp [mat]
  have : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, hm, Matrix.mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, h1, Matrix.mul_zero, neg_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

end GlobalTheory.RealConjFac
end
end

