module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShapeBd

variable {D : D7} {a a' : ℕ}

theorem symp_add_left' (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
    (x x' y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB (x + x') y =
      GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x y +
        GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x' y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)]

theorem det_ne_zero_skew (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) {d : ℕ} (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    {r s : ℕ} (hY : Y.IsSkew D.sp.cm.sig B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hY.sig w)
  intro h0
  apply h
  have hm : (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]

theorem exists_local (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : Fv D.host.F v) :
    ∃ e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) e ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ e = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp D.sp.cm.sig) e = c := by
  refine ⟨GlobalTheory.SrcHalfOne.plcC τ c, ?_, GlobalTheory.SrcHalfOne.piW_plcC τ c, ?_⟩
  · intro u hu
    have h0 : u * GlobalTheory.LatVac.liftV v c = 0 := GlobalTheory.LatVac.at_liftV v c u hu
    change u • (Formalism.L2.Theta.cA D (GlobalTheory.EmbChart.idem τ) *
      algebraMap (AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) (GlobalTheory.LatVac.liftV v c)) = 0
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, h0, map_zero, mul_zero]
  · have h := GlobalTheory.SrcHalfOne.piW_cA_plcC τ c
    rw [GlobalTheory.SrcHalfOne.piW_cA] at h
    exact h

theorem coBar_onto (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (hV' : Γ.V'.J.det ≠ 0) (hW : Γ.W.J.det ≠ 0) (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := (Γ.W.J.map Bs.τ₁)ᵀ with hBdef
  have hA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero, hAdef]
    have hm : (Γ.V'.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hV'
  have hB : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, hBdef, Matrix.det_transpose]
    have hm : (Γ.W.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hW
  choose e he using fun c => exists_local (D := D) Bs.v₁ Bs.τ₁ c
  set z : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(A⁻¹ * Y * B⁻¹) with hz
  refine ⟨z.map e, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (he (z i j)).1 u hu
  · funext i j
    exact (he (z i j)).2.1
  · have hx : (z.map e).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = z := by
      funext i j
      exact (he (z i j)).2.2
    unfold GlobalTheory.VacShape.coBar
    rw [hx, ← hAdef, ← hBdef, hz]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]

theorem bd_sub : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ Y h hY hYh
  have hV' := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D Bs Γ.V' hTr.geo.hV'
  have hW := det_ne_zero_skew Bs Γ.W hTr.geo.hW
  intro x hx hx0 hxh u hu hu0
  obtain ⟨x', hx', hx'0, hx'Y⟩ := coBar_onto Bs Γ hV' hW Y
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (x' + x) := by
    intro w hw
    rw [smul_add, hx' w hw, hx w hw, add_zero]
  have h1 := hYh (x' + x) hat (by rw [Matrix.map_add _ (map_add _), hx'0, hx0, add_zero])
    (by rw [GlobalTheory.VacShape.coBar_add, hx'Y, hxh]) u hu hu0
  have h2 := hY x' hx' hx'0 hx'Y u hu hu0
  rw [symp_add_left', AddChar.map_add_eq_mul, h2, one_mul] at h1
  exact h1

end GlobalTheory.VacShapeBd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicHaarSplitArchimedeanFinite
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.WeilAdm.HaarSplit

theorem lintegral_split_mul : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  intro F _ _ κ _ mA _ mI _ mf _ μ _ μi _ μf _
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) := Prod.borelSpace
  haveI : (μi.prod μf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μi μf
  have hH : ((μ.map (splitE F κ).symm)).IsAddHaarMeasure :=
    (splitE F κ).symm.isAddHaarMeasure_map μ (continuous_splitE_symm F κ) (continuous_splitE F κ)
  let em : (κ → AF F) ≃ᵐ ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    (Homeomorph.mk (splitE F κ).symm.toEquiv (continuous_splitE_symm F κ) (continuous_splitE F κ)).toMeasurableEquiv
  set c : NNReal := Measure.addHaarScalarFactor (μ.map (splitE F κ).symm) (μi.prod μf) with hc
  have heq : μ.map (splitE F κ).symm = c • (μi.prod μf) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(c : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  intro fi g hfi hg
  have h1 : ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ
      = ∫⁻ p, fi p.1 * g p.2 ∂(μ.map (splitE F κ).symm) := by
    rw [show μ.map (splitE F κ).symm = μ.map em from rfl, lintegral_map_equiv]
    rfl
  rw [h1, heq, lintegral_smul_measure, lintegral_prod_mul hfi.aemeasurable hg.aemeasurable]
  rfl

end GlobalTheory.WeilAdm.HaarSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFiniteAdelicFactorOffPlace
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_factor {A V : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableNeg A] [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    (μ : Measure A) (ν : Measure V) [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant]
    [ν.IsAddRightInvariant] (c : A → V) (e : V → A) (hcm : Measurable c)
    (hce : ∀ y t, c (y + e t) = c y + t) (O : Set V) (hOm : MeasurableSet O)
    (hOneg : ∀ x, x ∈ O ↔ -x ∈ O) (hO : ν O = 1) (K : A → ℝ≥0∞) (hK : Measurable K)
    (hKe : ∀ y t, K (y + e t) = K y) (g : V → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (c y) * K y ∂μ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := by
  have hχm : Measurable (O.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hOm
  have hcs : ∀ y t, c (y - e t) = c y - t := fun y t => by
    have h := hce (y - e t) t
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  have hKs : ∀ y t, K (y - e t) = K y := fun y t => by
    have h := hKe (y - e t) t
    rw [sub_add_cancel] at h
    exact h.symm
  have hχneg : ∀ x, O.indicator (1 : V → ℝ≥0∞) (-x) = O.indicator 1 x := fun x => by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hOneg x).1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hOneg x).2 h))]
  have hχint : ∫⁻ t, O.indicator 1 t ∂ν = 1 := by
    rw [lintegral_indicator_one hOm]; exact hO
  have hA : ∀ t, ∫⁻ y, g (c y) * K y ∂μ = ∫⁻ y, g (c y + t) * K y ∂μ := fun t => by
    rw [← lintegral_add_right_eq_self (fun y => g (c y) * K y) (e t)]
    simp only [hce, hKe]
  have hL : ∫⁻ y, g (c y) * K y ∂μ =
      ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
    calc ∫⁻ y, g (c y) * K y ∂μ
        = (∫⁻ t, O.indicator 1 t ∂ν) * ∫⁻ y, g (c y) * K y ∂μ := by rw [hχint, one_mul]
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y) * K y ∂μ ∂ν := (lintegral_mul_const _ hχm).symm
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y + t) * K y ∂μ ∂ν :=
          lintegral_congr fun t => by rw [← hA t]
      _ = ∫⁻ t, ∫⁻ y, O.indicator 1 t * (g (c y + t) * K y) ∂μ ∂ν :=
          lintegral_congr fun t =>
            (lintegral_const_mul _ ((hg.comp (hcm.add_const t)).mul hK)).symm
      _ = ∫⁻ y, ∫⁻ t, O.indicator 1 t * (g (c y + t) * K y) ∂ν ∂μ := by
          apply lintegral_lintegral_swap
          exact ((hχm.comp measurable_fst).mul
            ((hg.comp ((hcm.comp measurable_snd).add measurable_fst)).mul
              (hK.comp measurable_snd))).aemeasurable
      _ = ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [← lintegral_sub_right_eq_self (fun t => O.indicator 1 t * (g (c y + t) * K y)) (c y)]
          refine lintegral_congr fun s => ?_
          simp only [add_sub_cancel]
  have hM : ∀ s, ∫⁻ y, O.indicator 1 (c y) * K y ∂μ =
      ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ := fun s => by
    rw [← lintegral_sub_right_eq_self (fun y => O.indicator 1 (c y) * K y) (e s)]
    refine lintegral_congr fun y => ?_
    simp only [hcs, hKs]
    rw [← neg_sub, hχneg]
  rw [hL]
  calc ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ
      = ∫⁻ s, ∫⁻ y, O.indicator 1 (s - c y) * (g s * K y) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact ((hχm.comp (measurable_snd.sub (hcm.comp measurable_fst))).mul
          ((hg.comp measurable_snd).mul (hK.comp measurable_fst))).aemeasurable
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ ∂ν := by
        refine lintegral_congr fun s => ?_
        have hm : Measurable fun y => O.indicator (1 : V → ℝ≥0∞) (s - c y) * K y :=
          (hχm.comp (measurable_const.sub hcm)).mul hK
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ ∂ν :=
        lintegral_congr fun s => by rw [← hM s]
    _ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := lintegral_mul_const _ hg

end GlobalTheory.HaarFactorOffPlace

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_evalV_mul_shiftInvariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (w : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (κ → Fv F w)] [BorelSpace (κ → Fv F w)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure] (μw : Measure (κ → Fv F w)) [μw.IsAddHaarMeasure],
    μw {t | ∀ i, t i ∈ w.adicCompletionIntegers F} = 1 →
    ∀ (K : (κ → Af F) → ℝ≥0∞), Measurable K → (∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y) →
    ∀ (g : (κ → Fv F w) → ℝ≥0∞), Measurable g →
      ∫⁻ y, g (fun i => evalV F w (y i)) * K y ∂μf =
        (∫⁻ t, g t ∂μw) * ∫⁻ y, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1 (fun i => evalV F w (y i)) * K y ∂μf := by
  intro F _ _ κ _ _ _ w _ _ μf _ μw _ hO K hK hKinv g hg
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F w
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (κ → Af F) := inferInstance
  haveI : SecondCountableTopology (κ → Fv F w) := inferInstance
  haveI : LocallyCompactSpace (κ → Af F) := inferInstance
  haveI : LocallyCompactSpace (κ → Fv F w) := inferInstance
  have hcont : Continuous fun (y : κ → Af F) (i : κ) => evalV F w (y i) :=
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV w).comp (continuous_apply i)
  have hOc : IsClosed {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      (Valued.isClosed_integer (Fv F w)).preimage (continuous_apply i)
  refine lintegral_factor μf μw (fun y i => evalV F w (y i)) (fun t i => singleFin w (t i))
    hcont.measurable ?_ _ hOc.measurableSet ?_ hO K hK (fun y t => hKinv y t) g hg
  · intro y t
    funext i
    simp only [Pi.add_apply, map_add (f := _), evalV_singleFin_self]
  · intro x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_mem_iff]

end GlobalTheory.HaarFactorOffPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigen
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen

theorem local_identity_of_tens_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f R c hγ hR x₀ hx₀ hA ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : R x = R x₀ := hR x₀ z hzat
  have hrx1 : R (x + (co.e γ).1) = R x := hR x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : R x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  apply mul_right_cancel₀ hr0
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
  linear_combination this

end GlobalTheory.DblVacEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubledStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weyl_element_doubled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  first | exact @GlobalTheory.DblDiag.swap_at_place | exact GlobalTheory.DblDiag.swap_at_place | (intros; apply GlobalTheory.DblDiag.swap_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRoute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRoute

theorem modGrowth_integral_norm_kerBig {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) :
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  obtain ⟨ε, ω, χ, χ', Φ, C₀, hω, hΦ, hb⟩ := _root_.GlobalTheory.BigRouteIdent.kerBig_norm_le_thetaKO (G := G) hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  obtain ⟨p, hsig, hrk⟩ := _root_.GlobalTheory.FunObj.squareTriple_sig_rank W t i j hT M hM
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨N, Cw, hMI⟩ := hWC D W.ψ W.θ W.θ_is ε _ _ χ χ' ω hω p hsig hrk _ _ hHF Φ hΦ
  obtain ⟨Cc, hCc, hcmp⟩ := GlobalTheory.Grow.height_comparison (G.V (.grid i (j + 1))) W.θ_is
  set h₁ : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g₁ : ℝ)
  refine ⟨max C₀ 0 * (max Cw 0 * (Cc * h₁) ^ N), N, fun g => ?_⟩
  have hI := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).1
  have hle := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).2
  have hpos : 0 ≤ ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hpos]
  have h1 : ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) ≤
      ∫ u in M.fd (.grid (i + 1) (j + 1)), max C₀ 0 * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hI.norm.const_mul _)
      (Filter.Eventually.of_forall fun u => (hb g u).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  rw [integral_const_mul] at h1
  have hX := _root_.GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul D W.θ _ _ g g₁
  have hXg : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ≤
      Cc * GlobalTheory.Grow.height _ g * h₁ := by
    have := (hcmp g).1
    calc _ ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g : ℝ) * h₁ := by exact_mod_cast hX
      _ ≤ _ := mul_le_mul_of_nonneg_right this (NNReal.coe_nonneg _)
  have h0 : (0 : ℝ) ≤ ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have h2 : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      (Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 (hXg.trans_eq (by ring)) N
  have h3 : Cw * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 _)).trans
      (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
  calc _ ≤ _ := h1
    _ ≤ max C₀ 0 * (max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N)) :=
      mul_le_mul_of_nonneg_left (hle.trans h3) (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.BigRoute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagChar

theorem haarChar_det_mul_integral_comp_mulVec_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (m : MeasurableSpace (Fin N → k)) (hm : m = borel _)
    (ν : @Measure (Fin N → k) m) (hν : @Measure.IsAddHaarMeasure _ _ _ m ν)
    (T : GL (Fin N) k) (f : (Fin N → k) → ℂ) :
    ((distribHaarChar k (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have h2 : m = MeasurableSpace.pi := hm.trans (@BorelSpace.measurable_eq (Fin N → k) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst h2
  have hc := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin N => (Measure.addHaar : Measure k))
  rw [hc, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    ← GlobalTheory.WeilM.integral_comp_mulVec (Measure.addHaar : Measure k) T f, mul_smul_comm]

theorem nabs_det_mul_integral_comp_mulVec :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  intro F _ _ v N ν hν T f
  exact haarChar_det_mul_integral_comp_mulVec_localField (Fv F v) N _ rfl ν hν T f

end GlobalTheory.InertLagChar
end

