module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinpolyDefinitePairsTermNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFu
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_eventually_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite

theorem factor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU (E := E) (n := n), (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w (n := n)) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero

theorem cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UA E n), cLoc w y ∈ UL n w := by
  intro E _ _ _ hU n w y
  by_cases hs : IsSplitAt w
  · unfold UL
    rw [if_pos hs]
    exact Subgroup.mem_top _
  · obtain ⟨-, -, hloc, -⟩ := (GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs
    have hu := GlobalTheory.DefU.ClassFin.cT_pFin y
    unfold UL
    rw [if_neg hs]
    change cT (cj w) (cLoc w y).val * 1 * (cLoc w y).val = 1
    rw [mul_one]
    have key : cT (cj w) ((GeneralLinearGroup.map (pFin E) (y : GA E n)).val.map (pLoc E w)) =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
      refine Matrix.ext fun i j => ?_
      simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
      exact (hloc _).symm
    calc cT (cj w) (cLoc w y).val * (cLoc w y).val =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val *
          (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
          rw [Matrix.map_mul, ← key]
          rfl
      _ = 1 := by rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem compact_val_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := _root_.GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact

theorem valuation_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : E), w.valuation E (IsCMField.complexConj E a) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E a := by
  intro E _ _ _ w a
  obtain ⟨-, h1, h2⟩ := conjLoc_spec (GlobalTheory.SplitPts.conjE E) w
  have hv : ∀ (v : Pl E) (b : E), Valued.v (algebraMap E (v.adicCompletion E) b) = v.valuation E b :=
    fun v b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v b
  have e := h2 (algebraMap E _ a)
  rw [h1] at e
  rw [← hv, ← hv]
  exact e

theorem section_conjSrc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → (∀ w, w ∉ S → conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S) ∧ Function.Injective (conjSrc (GlobalTheory.SplitPts.conjE E)) := by
  intro E _ _ _ S hS
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
    by_cases hs : IsSplitAt w
    · rcases (GlobalTheory.SplitPts.over_split hs).2.2 u hu with rfl | h
      · exact absurd huS hw
      · rwa [← h]
    · exfalso
      exact hs ⟨u, fun h => hw (h ▸ huS), hu⟩
  · intro a b hab
    have ha := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) a
    have hb := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) b
    rw [hab] at ha
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at ha hb
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have hy : IsIntegral ℤ ((GlobalTheory.SplitPts.conjE E) (x : E)) :=
      x.isIntegral_coe.map (RingHom.toIntAlgHom (GlobalTheory.SplitPts.conjE E).toRingHom)
    exact (ha x ⟨_, hy⟩ rfl).trans (hb x ⟨_, hy⟩ rfl).symm

theorem unitary_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := _root_.GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one

theorem finite_of_local_bounds : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := _root_.GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one

theorem cLoc_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (γ : UE E n), cLoc w (finPt γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  intro E _ _ _ n w γ
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  have hc : cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (ratF E n γ.1).val * (ratF E n γ.1).val = 1 := by
    have e : (ratF E n γ.1).val = γ.1.val.map (algebraMap E (Af E)) := rfl
    rw [e]
    calc cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (γ.1.val.map (algebraMap E (Af E))) * γ.1.val.map (algebraMap E (Af E))
        = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * γ.1.val).map (algebraMap E (Af E)) := by
          rw [Matrix.map_mul]
          congr 1
          refine Matrix.ext fun i j => ?_
          simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
          exact conjFin_algebraMap (E := E) _ _
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero (algebraMap E (Af E))) (map_one (algebraMap E (Af E)))
  have hUA := GlobalTheory.DefU.ClassFin.finGL_mem_UA _ hc
  have hfin : (⟨_, hUA⟩ : UA E n) ∈ finU (E := E) (n := n) := (MonoidHom.mem_ker).2 (Units.ext (by
    have := pInf_finGL (E := E) (ratF E n γ.1)
    exact congrArg Units.val this))
  have e0 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, hUA⟩ := dif_pos hUA
  have e1 : (finPt γ).1 = ⟨finGL E n (ratF E n γ.1), hUA⟩ := by
    unfold finPt
    rw [e0]
    exact congrArg Subtype.val (dif_pos hfin)
  rw [e1]
  have h2 := GlobalTheory.CuspRep.pFin_finGL (E := E) (a := n) (ratF E n γ.1)
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  exact congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) h2

end GlobalTheory.BCT.SuppFin

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem val_le_one_of_KGL {w : Pl E} {h : GL (Fin n) (w.adicCompletion E)} (hh : h ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    Valued.v (h.val i j) ≤ 1 := by
  obtain ⟨k, rfl⟩ := hh
  exact (k.val i j).2

theorem conj_entry (γ : UE E n) (i j : Fin n) : IsCMField.complexConj E (γ.1.val i j) = (γ.1⁻¹).val j i := by
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  rw [Units.inv_eq_of_mul_eq_one_left h]
  rfl

theorem finite_of_bounds (S : Set (Pl E)) (hS : IsSection S) (Γs : Set (UE E n))
    (hb : ∀ w ∈ S, ∃ N : ℤ, ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ WithZero.exp N ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ WithZero.exp N)
    (hc : ∀ᶠ w in cofinite, w ∈ S → ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ 1 ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ 1) : Γs.Finite := by
  classical
  set X : Set E := {a | ∃ γ ∈ Γs, ∃ i j, a = γ.1.val i j ∨ a = (γ.1⁻¹).val i j} with hXdef
  have hcc : ∀ a : E, IsCMField.complexConj E (IsCMField.complexConj E a) = a := IsCMField.complexConj_apply_apply E
  have hXc : ∀ a ∈ X, IsCMField.complexConj E a ∈ X := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
    · exact ⟨γ, hγ, j, i, Or.inr (conj_entry γ i j)⟩
    · refine ⟨γ, hγ, j, i, Or.inl ?_⟩
      rw [← conj_entry γ j i, hcc]
  obtain ⟨hsec, hinj⟩ := section_conjSrc E S hS
  have hval : ∀ (w : Pl E) (a : E), w.valuation E a =
      (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E (IsCMField.complexConj E a) := by
    intro w a
    rw [← valuation_conj, hcc]
  have hall : ∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨N, hN⟩ := hb w hw
      refine ⟨N, ?_⟩
      rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
    · obtain ⟨N, hN⟩ := hb _ (hsec w hw)
      refine ⟨N, fun a ha => ?_⟩
      rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
  have hcof : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1 := by
    have h2 := hinj.tendsto_cofinite.eventually hc
    filter_upwards [hc, h2] with w h1 h2 a ha
    by_cases hw : w ∈ S
    · obtain ⟨γ, hγ, i, j, rfl | rfl⟩ := ha
      exacts [(h1 hw γ hγ i j).1, (h1 hw γ hγ i j).2]
    · rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(h2 (hsec w hw) γ hγ i j).1, (h2 (hsec w hw) γ hγ i j).2]
  have hinf : ∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1 := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩ τ
    · exact unitary_norm_le_one E n γ τ i j
    · exact unitary_norm_le_one E n γ⁻¹ τ i j
  have hX := finite_of_local_bounds E X hall hcof hinf
  have hM : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => X).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hX
  refine (hM.preimage (f := fun γ : UE E n => (γ.1.val : Fin n → Fin n → E)) ?_).subset ?_
  · intro a _ b _ h
    exact Subtype.ext (Units.ext h)
  · intro γ hγ i _ j _
    exact ⟨γ, hγ, i, j, Or.inl rfl⟩

end GlobalTheory.BCT.SuppFin


open GlobalTheory.BCT.SuppFin in
theorem GlobalTheory.BCT.SuppFin.suppFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU (E := E) (n := n), {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf x
  classical
  set Γs : Set (UE E n) := {γ | globFn S f (x⁻¹ * finPt γ * x) ≠ 0} with hΓs
  have hUL : ∀ (w : Pl E) (z : UA E n), cLoc w z ∈ UL n w := fun w z => cLoc_mem_UL E hU n w z
  have hnz : ∀ γ ∈ Γs, ∀ w ∈ S, f w (toSub _ (cLoc w (x⁻¹ * finPt γ * x).1)) ≠ 0 :=
    fun γ hγ w hw => factor_ne_zero E n S K' f hf (x⁻¹ * finPt γ * x) (cLoc_eventually_KGL E n _) hγ w hw
  have hpt : ∀ (w : Pl E) (γ : UE E n), GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 =
      cLoc w x.1 * cLoc w (x⁻¹ * finPt γ * x).1 * (cLoc w x.1)⁻¹ := by
    intro w γ
    rw [← cLoc_finPt E n w γ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    group
  have hv : ∀ (w : Pl E) (a : E), Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
    fun w a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
  have hent : ∀ (w : Pl E) (γ : UE E n) (i j : Fin n),
      (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val i j = algebraMap E _ (γ.1.val i j) ∧
      ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)⁻¹).val i j =
        algebraMap E _ ((γ.1⁻¹).val i j) := by
    intro w γ i j
    rw [← map_inv]
    exact ⟨rfl, rfl⟩
  refine finite_of_bounds S hS Γs ?_ ?_
  · intro w hw
    set c := cLoc w x.1 with hcdef
    set D : Set (GL (Fin n) (w.adicCompletion E)) :=
      (fun h => c * h * c⁻¹) '' ((UL n w).subtype '' tsupport (f w)) with hDdef
    have hD : IsCompact D :=
      (((hf.1 w).1.image continuous_subtype_val).image ((continuous_const.mul continuous_id).mul continuous_const))
    obtain ⟨N, hN⟩ := compact_val_bounded E w n D hD
    refine ⟨N, fun γ hγ i j => ?_⟩
    have hmem : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ D := by
      rw [hpt]
      refine ⟨_, ⟨⟨_, hUL w _⟩, subset_tsupport _ ?_, rfl⟩, rfl⟩
      have h0 := hnz γ hγ w hw
      rwa [toSub, dif_pos (hUL w _)] at h0
    obtain ⟨h1, h2⟩ := hN _ hmem i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
  · filter_upwards [hf.2, cLoc_eventually_KGL E n x.1] with w hfw hxw hw γ hγ i j
    have h0 := hnz γ hγ w hw
    rw [hfw, toSub, dif_pos (hUL w _)] at h0
    have hy : cLoc w (x⁻¹ * finPt γ * x).1 ∈ GlobalTheory.LFun.KGL w (n := n) :=
      Subgroup.mem_subgroupOf.1 (Set.indicator_apply_ne_zero.1 h0).1
    have hg : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
      rw [hpt]
      exact mul_mem (mul_mem hxw hy) (inv_mem hxw)
    have h1 := val_le_one_of_KGL hg i j
    have h2 := val_le_one_of_KGL (inv_mem hg) i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernel
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

theorem mem_augRk_of_fibre_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ hΨ hT
  have hT' : ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n →
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = 0 := fun Y hY => by
    obtain ⟨h, rfl⟩ := GlobalTheory.T.full_rank_normal_form_orbit k n d hnd Y hY
    exact hT h
  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d _ (GlobalTheory.T.isClopen_unit_minor_set k n d).isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ hΨ
  obtain ⟨Φ, hΦ, hS, hdiff, hF⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν _ (GlobalTheory.T.isClopen_unit_minor_set k n d)
    (fun Φ hΦ Y => _root_.GlobalTheory.FullRankCoinv.integrable_fibre_target k n d ν hν Φ hΦ Y) s Ψ hΨ hs
  have hA := GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν _ (GlobalTheory.T.integral_group_of_unit_minor_stable k n d) (fun E hE Y hY => GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY) Φ hΦ hS
    (fun Y hY => by rw [hF]; exact hT' Y (GlobalTheory.T.rank_eq_of_unit_minor k n d Y hY))
  have e : Ψ = (Ψ - Φ) + Φ := by abel
  rw [e]; exact add_mem hdiff hA

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
section
noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace GlobalTheory.GaussNonvanish

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd, ← map_pow]
  rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  exact pow_lt_one' h (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  have h1 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c) - 1) ≤
      valuation k (ϖ : k) ^ c := by
    have := (mk_eq_mk_iff hϖ c (Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) 1).1
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one])
    simpa [rep] using this
  have h2 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) = 1 := by
    have := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt_one hϖ hc))
    simpa using this
  rw [map_mul] at h2
  refine le_antisymm (rep_le_one _) ?_
  calc (1 : ValueGroupWithZero k) = _ := h2.symm
    _ ≤ _ := mul_le_of_le_one_right' (rep_le_one _)

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have := val_rep_unit hϖ hc y
  rw [h, map_zero] at this
  exact zero_ne_one this

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  rw [show a = b + (a - b) by ring, hadd, hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  have hlt : valuation k ((a : k) - b) < valuation k (b : k) := by
    rw [hb]; exact h.trans_lt (val_pow_lt_one hϖ hc1)
  have ha : valuation k (a : k) = 1 := ((valuation k).map_eq_of_sub_lt hlt).trans hb
  have hw : a * b⁻¹ ∈ unitCong (ϖ ^ c) := by
    refine ⟨by simp [ha, hb], ?_⟩
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ b.ne_zero]
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one, Units.val_pow_eq_pow_val, map_pow]
    exact h
  have := hc _ hw
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

end Generic
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

end Sums
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  have hopen : IsOpen {x : kˣ | ‖(ν x : ℂ) - 1‖ < 1 / 2} := isOpen_lt (by fun_prop) continuous_const
  obtain ⟨V, hV, hV'⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.1 hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ Units.val ⁻¹' V := by rw [hV']; simp
    simpa using this
  have h2 : (fun z : k => z + 1) ⁻¹' V ∈ 𝓝 (0 : k) :=
    (hV.preimage (by fun_prop)).mem_nhds (by simpa using h1)
  obtain ⟨s, hs⟩ := exists_cball_subset h2
  obtain ⟨p, hp, hp'⟩ := GlobalTheory.LocLanglands.exists_unit_pow k (ord k s).toNat
  have hsmall : ∀ x ∈ unitCong (ϖ ^ (ord k s).toNat), ‖(ν x : ℂ) - 1‖ < 1 / 2 := fun x hx => by
    have h3 : (x : k) - 1 ∈ GlobalTheory.SplitWeil.cball s := by
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      refine hx.2.trans ?_
      rw [Units.val_pow_eq_pow_val, map_pow, hϖ, ← hp, GlobalTheory.LocLanglands.valuation_le_iff_ord, hp']
      exact Int.self_le_toNat _
    have h4 : x ∈ Units.val ⁻¹' V := by simpa using hs h3
    rw [hV'] at h4
    exact h4
  refine ⟨(ord k s).toNat, fun x hx => Units.ext ?_⟩
  refine GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m => ?_
  have := hsmall (x ^ m) (pow_mem hx m)
  rw [map_pow, Units.val_pow_eq_pow_val] at this
  exact this.le

end Main
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end Place
end GlobalTheory.GaussNonvanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarConjugateSubgroupIndexRatio
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.FinPairs

theorem finite_classes_irr_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G ha L f hf hfb K' f' hf' hfb'
  refine ((_root_.GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero p G ha L f hf hfb K' f' hf' hfb').biUnion
    (fun P0 _ => GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one p G ha L f hf hfb K' f' hf' hfb' P0)).subset ?_
  intro q hq
  exact Set.mem_biUnion (x := (Quot.out q).pol) ⟨Quot.out q, rfl, hq.1, hq.2⟩ ⟨rfl, hq.1, hq.2⟩

end GlobalTheory.LKDef.FinPairs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImgSet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DecOn (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl (F := F)))
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ j, f j ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ j v ∈ SB _) ∧ ∀ v ∉ T, φ j v = M.vac v) ∧ Ψ = ∑ j, pure (f j) (φ j)

end GlobalTheory.ThK.CycGen
end
end

