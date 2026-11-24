module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerne
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.WhitAlg

open GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_psiNeg :
    Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem whit_eq (F : GA E a → ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit F g = ∫ X in vecDomain E (Pos a),
      F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := rfl

theorem integrableOn_whit {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) :
    IntegrableOn (fun X => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hF.comp (continuous_uGL.mul continuous_const)).mul continuous_psiNeg
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add_mul {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (c : ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g := by
  rw [whit_eq, whit_eq, whit_eq, ← integral_const_mul,
    ← integral_add (integrableOn_whit hF g) ((integrableOn_whit hG g).const_mul c)]
  congr 1
  funext X
  ring

theorem whit_kerInf {F : GA E a → ℂ} (hF : Continuous F)
    (hgr : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N)
    {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : GlobalTheory.JSW.IsRapidInf ν k γ) (g : GA E a) :
    GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  let ψ : (Pos a → Ad E) → ℂ := fun Y => (GroundTheory.Global.adelicChar E (-supSum 0 Y) : ℂ)
  let f : (Pos a → Ad E) → X → ℂ := fun Y x => k x * F (uGL Y * g * infGL E a (γ x)) * ψ Y
  have hmeas : Measurable (Function.uncurry f) := by
    haveI : BorelSpace ((Pos a → Ad E) × Lie E a) := Prod.borelSpace
    have hc : ContinuousOn (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) :=
      (GlobalTheory.ConstTermSmooth.continuousOn_chart hF).comp
        (((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hφ : Measurable fun p : (Pos a → Ad E) × X => ((p.1, toL (γ p.2).val) : (Pos a → Ad E) × Lie E a) :=
      measurable_fst.prodMk (hk.2.1.comp measurable_snd)
    have h1 : Measurable fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val) := by
      have e : (fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val)) =
          (Set.univ ×ˢ invSet E a).restrict (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2) ∘
            fun p => (⟨(p.1, toL (γ p.2).val), Set.mem_univ _, val_mem_invSet _⟩ :
              (Set.univ ×ˢ invSet E a : Set ((Pos a → Ad E) × Lie E a))) := rfl
      rw [e]
      exact hc.restrict.measurable.comp hφ.subtype_mk
    have e2 : Function.uncurry f = fun p => k p.2 * chart F (uGL p.1 * g) (toL (γ p.2).val) * ψ p.1 := by
      funext p
      exact congrArg (fun z => k p.2 * z * ψ p.1) (chart_val F _ _).symm
    rw [e2]
    exact ((hk.1.comp measurable_snd).mul h1).mul (continuous_psiNeg.measurable.comp measurable_fst)
  obtain ⟨C, N, hC⟩ := hgr ((fun Y => uGL Y * g) '' closure (vecDomain E (Pos a)))
    (isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const))
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hb : Integrable (fun p : (Pos a → Ad E) × X => (1 : ℝ) * (C * (‖k p.2‖ * height (γ p.2) ^ N))) (μ.prod ν) :=
      (integrable_const (1 : ℝ)).mul_prod ((hk.2.2 N).const_mul C)
    have hae : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ vecDomain E (Pos a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_vecDomain)
    refine hb.mono' hmeas.aestronglyMeasurable (hae.mono fun p hp => ?_)
    have hb1 := hC (uGL p.1 * g) ⟨p.1, subset_closure hp, rfl⟩ (γ p.2)
    change ‖k p.2 * F (uGL p.1 * g * infGL E a (γ p.2)) * (GroundTheory.Global.adelicChar E (-supSum 0 p.1) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    calc ‖k p.2‖ * ‖F (uGL p.1 * g * infGL E a (γ p.2))‖ ≤ ‖k p.2‖ * (C * height (γ p.2) ^ N) :=
          mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
      _ = 1 * (C * (‖k p.2‖ * height (γ p.2) ^ N)) := by ring
  have hin : ∀ Y, GlobalTheory.JSW.kerInf ν k γ F (uGL Y * g) * ψ Y = ∫ x, f Y x ∂ν := fun Y => by
    simp only [f, GlobalTheory.JSW.kerInf]
    rw [integral_mul_const]
  calc GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ Y, ∫ x, f Y x ∂ν ∂μ := by
        rw [whit_eq]
        congr 1
        funext Y
        exact hin Y
    _ = ∫ x, ∫ Y, f Y x ∂μ ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext x
        rw [whit_eq, ← integral_const_mul]
        congr 1
        funext Y
        simp only [f, ψ, mul_assoc]

theorem whit_linear_kerInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ),
    Continuous F → Continuous G →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧
      ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
        GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g =
          ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  intro E _ _ _ a F G hF hG hFg _
  exact ⟨fun c g => whit_add_mul hF hG c g, fun X _ ν _ k γ hk g => whit_kerInf hF hFg ν hk g⟩

end GlobalTheory.JSW.WhitAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

end GlobalTheory.GoodFiniteDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
section
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult in
open scoped ComplexOrder in
theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))
end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem automorphicFormsFiniteGL_of_core (h : CoreFiniteGL) : GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  intro E _ _ _ a L hL W _ _ _ ρ _ c
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := _root_.GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := _root_.GlobalTheory.CuspRep.Zalg_acts_by_scalar E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h E a L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.FramePower

theorem exists_nabValN_eq_of_map {R K O : Type} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K] [Algebra R K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (h : PS R 2 d) (hc : MvPowerSeries.constantCoeff h = 0)
    (w0 : O) (k k' : ℕ) {n : ℕ} (g : PS R n d) :
    ∃ g' : PS R n d, ∀ {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K),
      nabValN B K (FB.toK K h) w0 k (FB.toK K g) cp u P = nabValN B K (FB.toK K h) w0 k' (FB.toK K g') cp u P := by
  have gC : GP (comp1 (B.actK R w0) (pt R (n := 1) d 0)) :=
    gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)
  have cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0 := by
    unfold FB.hL
    rw [GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _),
      GlobalTheory.QuadDeriv.baseChange_pt]
    have := GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0
    exact congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this
  set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS
  have gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j) := by
    intro b j; fin_cases j; exact gp_pt b
  have cS : MvPowerSeries.constantCoeff S = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL
  have eS : MvPowerSeries.map (algebraMap R K) S =
      ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]
    congr 1
    funext j; fin_cases j
    exact GlobalTheory.QuadDeriv.baseChange_pt _ _
  have cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0 := fun m => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]
  have em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0)) =
      FB.toK K (FB.expS R ((m : R) • S)) := fun m => by
    rw [FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul,
      map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]
  refine ⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩
  unfold nabValN
  rw [em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc,
    ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]

end GlobalTheory.FramePower


open GlobalTheory.FramePower in
theorem GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  intro T io y C hchar
  letI := io.toAlgebra
  intro a n k k' P hP f hf
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨hF, hA, -⟩ := C.gen.1
  obtain ⟨e1, e2, -⟩ := hBT
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF, e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA, e2]
  letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by
    rintro ⟨z, hz⟩
    have h0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    rw [← residue_ne_zero_iff_isUnit]
    simpa using h0)).toAlgebra
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B
  have hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0
  choose g hg' using hf
  have ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch)) := by
    ext m
    exact (hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm
  obtain ⟨g', hgg⟩ := exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0)
    H.w0 k k' (g : PS T.V n (chD C.ch))
  have key := GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1
    (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0
  refine ⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩
  rw [← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (key k f).trans (Eq.trans ?_ (key k' _).symm)
  rw [ef]
  exact hgg _ _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem quot_mul_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ)
    (t t' : Aˣ) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t' * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht : algebraMap A S ((t⁻¹ : Aˣ) : A) * algebraMap A S (t : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t⁻¹ : Aˣ) : A) * b := by
    calc ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop
        = algebraMap A S ((t⁻¹ : Aˣ) : A) * (((x⁻¹ : Sˣ) : S) * algebraMap A S (t : A) *
            (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [← Algebra.commutes (t : A), ← mul_assoc, ← mul_assoc, ht, one_mul]
      _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((((x⁻¹ : Sˣ) : S) * x) * b *
            ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)) := by
          rw [← hx]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]
  calc ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop
      = x' * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((x' : S) * b * (σ x').unop) := by
        rw [h2]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [hx', ← map_mul, mul_comm, Units.val_mul]

theorem triv_quot : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' →
    ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  intro p _ G R _ _ β x x' t t' hx hx'
  exact ⟨⟨(x' * x⁻¹, t' * t⁻¹), quot_mul_star (starT G.star R) (inC G R β) x x' t t' hx hx'⟩, rfl⟩

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

abbrev Qv (v : AwayP p) : Type := v.1.adicCompletion ℚ

abbrev Gv (G : HTGroup p) (v : AwayP p) : Type := UPts G.star (Qv v)

def piV (G : HTGroup p) (v : AwayP p) : G.GAf →* Gv G v := ubcMap (AfP.eval v)

def basV (G : HTGroup p) (v : AwayP p) : Module.Basis (Fin (Module.finrank ℚ G.C)) (Qv v) (Qv v ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (Qv v) (Module.finBasis ℚ G.C)

def IsIntV (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) : Prop :=
  ∀ i, (basV G v).repr y i ∈ v.1.adicCompletionIntegers ℚ

def IntV (G : HTGroup p) (v : AwayP p) : Set (Gv G v) :=
  {g | IsIntV G v (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    IsIntV G v ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ) ∧
    (((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ)}

theorem inv_mem_IntV (G : HTGroup p) (v : AwayP p) {g : Gv G v} (h : g ∈ IntV G v) : g⁻¹ ∈ IntV G v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h2
  · simpa using h1
  · exact h4
  · simpa using h3

end GlobalTheory.OrbFinAf
end
end

