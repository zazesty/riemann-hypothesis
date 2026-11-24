module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstract
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi


set_option maxHeartbeats 1000000 in
theorem kirillov_semiLocal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  intro E _ _ _ m S b hb hC hU hsm 𝒲 h1 h2 h3 h4 h5 hne
  obtain ⟨W₀, hW₀, p₀, hp₀, hne₀⟩ := hne
  refine GlobalTheory.T.exists_eq_on_mirabolic_of_slices_finitePlaces E m S b 𝒲 hb hC hU h1 h2 h5 fun q hq hq1 => ?_
  have hh : q⁻¹ * p₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    intro w hw
    rw [map_mul, map_inv, hq.1 w hw, hp₀.1 w hw, inv_one, one_mul]
  have hW' := h2 W₀ hW₀ _ hh
  have hq0 : (fun g => W₀ (g * (q⁻¹ * p₀))) q ≠ 0 := by
    simpa [← mul_assoc] using hne₀
  obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ :=
    GlobalTheory.T.semiLocal_kirillov_archimedean_kernel_complexPlaces E m S b _ q hb hC (hsm q) (h1 _ hW') (h4 _ hW' q).1 (h4 _ hW' q).2 hq1 hq0
  exact ⟨_, h3 _ hW' X ν k γ hk, hK⟩

end GlobalTheory.JSW.MirSemi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBoundedStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  first | exact @GlobalTheory.LatVacBdd.locCo_bounded | exact GlobalTheory.LatVacBdd.locCo_bounded | (intros; apply GlobalTheory.LatVacBdd.locCo_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord
section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BigOn.leafDepth_all_record : ∃ C0 : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ N : IndefNum A.fam.base, LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent N (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) → C0 ≤ c.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  obtain ⟨C0, h⟩ := GlobalTheory.RunDepth.leafDepth_all_run GlobalTheory.ChF.colength_bound_split_place_chart
    GlobalTheory.ChF.hodgeTate_inclusion_chart GlobalTheory.ChF.unramified_companion_chart_characters
  refine ⟨C0, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hrec N hPg hSz hx hb tF hC hn he
  obtain ⟨st, hd⟩ := hrec.depth
  obtain ⟨hc, -⟩ := hrec.tied
  letI := st
  letI := hostAlg D
  exact h D L Pm Tp hK J.toCore EX D.what₂.LL _ _ _ _ c O _ N hc.toLawsM hd hPg hSz hx hb tF hC hn he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbedding
section
noncomputable section

open NumberField IsDedekindDomain Module MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Mult
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopCore

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) :
    ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2


open Classical in
theorem isConjChars_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu


open Classical in
theorem isLevelVec_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1


open Classical in
theorem chr_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  GlobalTheory.BaseScalar.exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_of_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := GlobalTheory.BaseScalar.integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem scalar_of_lift_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (b : ℝ)
    (hb : Sizes D i b) (t : T0) (ht : PrimeToHost R t)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th)
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i (sg0 D A) t R.triv ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i (sg0 D A) t R.triv ev, th (adjLev R.triv th x) = (l : ℂ) • x) ∧
      mainTerm D i (sg0 D A) - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  have key := hA h i b hb t ht _ _ hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_base_ofCore R h i t) (R.ωP i t) (h.thP.ωP i t)
    (onb (R.MW i (sg0 D A))) (fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ)) _ _ (isLevelVec_base_ofCore R h i t)
    (h.thP.pt_theta i t) (R.cV i) (h.models.cV i) (R.ioP i) (by rw [delta_base R]; exact h.thP.ioP i t)
    (R.νV i t) (R.fdV i t) (h.models.νV i t) _ (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t)
    (by rw [chr_base_ofCore R h]; exact h.models.HV i t)
  exact key.2 th hth ev hev

theorem scalar_on_part_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F)
    (hp : PrimeToHost R A.μ0) (i : Fin D.R.m) (b : ℝ) (hb : Sizes D i b)
    (th : (R.HV i A.μ0).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i A.μ0 x)
    (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    ∃ l : ℝ, Real.exp (lowB D i b) ≤ l ∧
      ∀ y ∈ GlobalTheory.LiftLower.partH R i (sg0 D A) c, th (LinearMap.adjoint th y) = (l : ℂ) • y := by
  have e := GlobalTheory.LiftLower.typePart_base h.lev i (sg0 D A) c
  have h1 := scalar_of_lift_ofCore R hA h i b hb A.μ0 hp th (isLift_of_ofCore R h i A.μ0 th hth) c
  have h2 := GlobalTheory.BaseScalar.adjLev_triv R th
  have h3 : lowB D i b ≤ mainTerm D i (sg0 D A) -
      8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b := sub_le_sub_right (GlobalTheory.LowTopBound.hookPlus_le_mainTerm R i) _
  exact GlobalTheory.LowTopBound.scalar_of_ne_bot th _ _ h2 _ _ e _ _ h3 h1

theorem lowTop_ofCore : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ),
    GlobalTheory.LowRow.AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s b hA h _ hp hb i l x hx hl hxl
  obtain ⟨th, hth⟩ := exists_lift_ofCore R h i A.μ0
  have hinj : Function.Injective (R.HW i (sg0 D A)).e := (h.models.HW i (sg0 D A)).1
  have hS : ∀ y, R.thG i A.μ0 y = GlobalTheory.LiftLower.projH R i (sg0 D A) (th y) := fun y => by
    have a1 := h.thP.thG i A.μ0 y
    have a2 := GlobalTheory.LiftLower.e_projH h.models.gW i (sg0 D A) (th y)
    have a3 := congrArg (Formalism.IndefR.Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))) (hth y)
    exact hinj (a1.trans (a3.symm.trans a2.symm))
  have hid := GlobalTheory.LiftScalarCompare.eC_idem (R := R) h.grp.record
  have hu := GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i (sg0 D A)
  have htop := _root_.GlobalTheory.FiveClauseParts.parts_conj_five.1 R F (GlobalTheory.Core5.of_core h) i (sg0 D A)
    (GlobalTheory.LiftLower.schurMult_of_models R h.models.HW i (sg0 D A))
  have htop' : (⨆ c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D, GlobalTheory.LiftLower.partH R i (sg0 D A) c) = ⊤ :=
    top_le_iff.1 (htop.ge.trans (iSup_mono fun c => iSup_le fun _ => le_rfl))
  have hm := GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts th _ (Real.exp (lowB D i b)) htop'
    (scalar_on_part_ofCore R hA h hp i b (hb i) th hth)
  have key := GlobalTheory.LowTopBound.le_eigenvalue th (R.thG i A.μ0) (GlobalTheory.LiftLower.projH R i (sg0 D A)) _ l hS
    (GlobalTheory.LowTopBound.idem_apply (R.gW i (sg0 D A)) hid)
    (fun x hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i (sg0 D A)) hu hid hx y) hm x hx hl hxl
  exact (Real.le_log_iff_exp_le hl).2 key

end GlobalTheory.LowTopCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sum_transpose_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix m m K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (gᵀ * Y) k j * L k j = ∑ k, ∑ j, Y k j * (g * L) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ j, g i x * Y i j * L x j := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, g i x * Y i j * L x j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, g i x * Y i j * L x j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.LinBarOps

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem heis_ops : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hT K hK S hSB h4
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)
    have e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := Γ.W.J.map Bs.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bᵀ.det := by
    have e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hBm : IsUnit B.det := by rw [← Matrix.det_transpose]; exact hB
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) :=
    fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 →
      u.map (piW (Bs.τ₁.comp σ)) = 0 →
      Bs.ψ (symp (R := AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) =
        GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  refine ⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)),
    fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hK' : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      actAB (cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) u = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u := by
    intro g u
    simp [actAB, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  have hKat : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u →
      At (evFin F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u) := by
    intro g u hu r hr
    rw [← Matrix.mul_smul, hu r hr, Matrix.mul_zero]
  have hKmap : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u).map (piW t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (piW t) * u.map (piW t) :=
    fun g u t => Matrix.map_mul
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  · intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  · intro g C φ hφ
    funext Y
    rw [h4 g _ (hUat 0 (Pm C)) φ hφ, hK']
    have hat := hKat g _ (hUat 0 (Pm C))
    rw [htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) Y]
    congr 2
    rw [hKmap, (hK g).2.2, hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  · intro g l φ hφ
    funext Y
    rw [h4 g _ (hUat (-Lm l) 0) φ hφ, hK']
    have hat := hKat g _ (hUat (-Lm l) 0)
    have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0 := by
      rw [hKmap, hU1, Matrix.mul_zero]
    have hm := hmu _ hat h1 _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, (hK g).2.1, hU0, linForm_eq l]
    congr 2
    rw [show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]
    simp [Matrix.mul_neg, Finset.sum_neg_distrib]

end GlobalTheory.LinBarOps
end
end

