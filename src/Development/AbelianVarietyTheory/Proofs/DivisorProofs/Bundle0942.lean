module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapMemMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.ConjFull

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_mem_mult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    {J : Set (GA D V)} {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = star (χ k)) {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    conjMap M M' c h T ∈ Mult θ M' J χ' := by
  obtain ⟨T', hT', e1⟩ := (_root_.GlobalTheory.ConjMult.conj_mult θ M M' c hc).2 J χ T hT
  have : conjMap M M' c h T = T' := by
    refine MultilinearMap.ext fun v' => funext fun g => ?_
    rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
    rfl
  rw [this]
  exact mult_congr θ M' hχ hT'

theorem heckeLin_star (R : Finset (GA D V)) (φ : GA D V → ℂ) : heckeLin V R (star φ) = star (heckeLin V R φ) := by
  funext g
  show ∑ γ ∈ R, star (φ (g * γ)) = star (∑ γ ∈ R, φ (g * γ))
  rw [star_sum]

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a a' : Pl D.host.E → List ℤ → ℂ)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (hχ0 : ∀ k ∈ J0, χ0 k = star (χ0 k))
    (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) (ha : ∀ P d, a' P d = star (a P d)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
  have h := (_root_.GlobalTheory.ConjMult.conj_mult θ M M' c hc).1
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨conjMap_mem_mult θ M M' c hc h hχ h1, ?_⟩, ?_⟩
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · obtain ⟨h4, h5⟩ := (mem_partFull θ M J0 χ0 SF a T).1 h3
      refine (mem_partFull θ M' J0 χ0 SF a' _).2 ⟨conjMap_mem_mult θ M M' c hc h hχ0 h4, fun P d R hR v' => ?_⟩
      rw [conjMap_apply, heckeLin_star, h5 P d R hR, star_smul, ha]
  let j : (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank_full : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), (∀ k ∈ J, χ' k = star (χ k)) → (∀ k ∈ J0, χ0 k = star (χ0 k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF (fun P d => star (a P d)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J J0 χ χ' χ0 e e' SF a hχ hχ0 he
  refine le_antisymm (rank_le θ M M' c hc J J0 χ χ' χ0 e e' SF a _ hχ hχ0 he fun _ _ => rfl) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J J0 χ' χ χ0 e' e SF _ a ?_ hχ0 ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P d
    simp

end GlobalTheory.ConjFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.continuous_piV) | (exact GlobalTheory.OrbFinAf.continuous_piV) | (intros; apply GlobalTheory.OrbFinAf.continuous_piV  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ContMapReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evInf (w : InfinitePlace F) : Continuous (evInf F w) := by
  show Continuous (fun a : AF F => a.1 w)
  exact (continuous_apply w).comp continuous_fst

def phiW (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

theorem continuous_phiW (w : InfinitePlace F) : Continuous (phiW (F := F) w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_evInf w)

theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : AE F E) :
    piInf τ (a • x) = phiW w a * piInf τ x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp [piInf, compInf, infEmb, phiW, Algebra.TensorProduct.algebraMap_apply]

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf (E := E) τ) := by
  letI : Module (AF F) ℂ := Module.compHom ℂ (phiW (F := F) w)
  haveI : ContinuousSMul (AF F) ℂ := ⟨by
    show Continuous (fun p : AF F × ℂ => phiW w p.1 * p.2)
    exact ((continuous_phiW w).comp continuous_fst).mul continuous_snd⟩
  let L : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := fun a x => by rw [piInf_smul]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem contmap {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)}
    (γ : Multiplicative ℝ →* UG (cA σ) J) (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  have h1 : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))
  exact h1.matrix_map (continuous_piInf τ)

end GlobalTheory.ContMapReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferentialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  first | (exact @GlobalTheory.FormsLocus.polys_ker) | (exact GlobalTheory.FormsLocus.polys_ker) | (intros; apply GlobalTheory.FormsLocus.polys_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CoreOfWeak

theorem core_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h e
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak h e
  refine ⟨⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩, ?_, fun c => rfl, fun i c => rfl⟩
  intro v
  rw [h.inert.SF v, h.allPl]

end GlobalTheory.CoreOfWeak
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaRefinementProof
section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem coset_refinement : CosetRefinement := by
  intro X A a b S Md _ _ hOdd hLa
  exact indAdd_of A a b S Md hOdd.pos (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S Md hOdd.pos hLa)

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroupStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_theorem_picardGroup : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B), GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) = GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  exact @GlobalTheory.CubeThm.cube_pic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompact
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Matrix

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def IsLocModerate (F : GA E a → ℂ) : Prop :=
  ∀ g₀ : GA E a, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ᶠ g in 𝓝 g₀, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

theorem continuous_mapGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] {p : R →+* S} (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) :=
  Continuous.units_map _ (continuous_id.matrix_map hp)

theorem continuous_pInf_ad : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_pFin_ad : Continuous (pFin E) := continuous_snd

theorem continuous_height_inf : Continuous (height : GL (Fin a) (Cinf E) → ℝ) := by
  have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
  show Continuous fun y : GL (Fin a) (Cinf E) => 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  exact (continuous_const.add (ht.comp Units.continuous_val).norm).add (ht.comp Units.continuous_coe_inv).norm

theorem isAutForm_continuous_locModerate {φ : Sm E a} (hA : IsAutForm φ) : Continuous φ.1 ∧ IsLocModerate φ.1 := by
  have cI : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g := continuous_mapGL continuous_pInf_ad
  have cF : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g := continuous_mapGL continuous_pFin_ad
  have dec : ∀ g₀ g : GA E a, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ → ∀ y,
      φ.1 (g * infGL E a y) = φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)) := by
    intro g₀ g hk y
    have hu : g = g₀ * (infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) := by
      rw [infGL_mul_finGL, mul_inv_cancel_left]
    have e : g * infGL E a y = g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) := by
      conv_lhs => rw [hu]
      rw [map_mul (infGL E a) (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) y]
      simp only [mul_assoc]
      rw [← infGL_comm]
    rw [e]
    exact congrArg (fun ψ : Sm E a => ψ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))) hk
  have nb : ∀ g₀ : GA E a, ∀ᶠ g in 𝓝 g₀, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := by
    intro g₀
    have hc : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
      cF.comp (continuous_const.mul continuous_id)
    refine hc.continuousAt.preimage_mem_nhds (hA.level.mem_nhds ?_)
    simp
  refine ⟨continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · have e : (fun g => φ.1 g) =ᶠ[𝓝 g₀]
        fun g => chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
      filter_upwards [nb g₀] with g hg
      rw [chart_val]
      have := dec g₀ g hg 1
      simp only [map_one, mul_one] at this
      exact this
    refine ContinuousAt.congr ?_ e.symm
    refine ContinuousAt.comp_of_eq (contDiffAt_chart (x := oneL E a) φ.2 g₀ isUnit_one).continuousAt ?_
      (by simp [oneL])
    have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
    exact ((ht.comp Units.continuous_val).comp (cI.comp (continuous_const.mul continuous_id))).continuousAt
  · obtain ⟨C, N, hC⟩ := hA.growth g₀
    have ha : (0 : ℝ) ≤ 1 + 2 * a := by positivity
    have h1' := one_le_height (1 : GL (Fin a) (Cinf E))
    refine ⟨|C| * ((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) ^ N, N,
      mul_nonneg (abs_nonneg C) (pow_nonneg (mul_nonneg ha (by linarith)) N), ?_⟩
    have hh : ∀ᶠ g in 𝓝 g₀, height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) <
        height (1 : GL (Fin a) (Cinf E)) + 1 := by
      have hc : Continuous fun g : GA E a => height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) :=
        continuous_height_inf.comp (cI.comp (continuous_const.mul continuous_id))
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [nb g₀, hh] with g hg hg' y
    rw [dec g₀ g hg y]
    have h1 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g))
    have h2 := one_le_height y
    have h3 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)
    calc ‖φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))‖
        ≤ C * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N := hC _
      _ ≤ |C| * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)
      _ ≤ |C| * ((1 + 2 * a) * (height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) * height y)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (RapidModel.height_mul_le _ y) N) (abs_nonneg C)
      _ ≤ |C| * (((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) * height y) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (mul_nonneg ha (mul_nonneg (by linarith) (by linarith))) ?_ N) (abs_nonneg C)
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg'.le ha) (by linarith)
      _ = _ := by rw [mul_pow]; ring


variable (π : CuspSub E a) in
def regSpan : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F}
  add_mem' := fun {F G} hF hG => by
    refine ⟨add_mem hF.1 hG.1, hF.2.1.add hG.2.1, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e1⟩ := hF.2.2 g₀
    obtain ⟨C', N', h0', e2⟩ := hG.2.2 g₀
    refine ⟨C + C', N + N', add_nonneg h0 h0', ?_⟩
    filter_upwards [e1, e2] with g h1 h2 y
    have hy := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    refine (norm_add_le _ _).trans ?_
    nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' := ⟨zero_mem _, continuous_zero, fun _ => ⟨0, 0, le_rfl, Eventually.of_forall fun _ _ => by simp⟩⟩
  smul_mem' c F hF := by
    refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨‖c‖ * C, N, mul_nonneg (norm_nonneg _) h0, ?_⟩
    filter_upwards [e] with g h y
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} :
    F ∈ regSpan π ↔ F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F := Iff.rfl

theorem rt_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ regSpan π := by
  refine ⟨rt_mem_rspan hF.1 h, hF.2.1.comp (continuous_mul_const h), fun g₀ => ?_⟩
  obtain ⟨y₀, k, rfl⟩ : ∃ y₀ k, h = infGL E a y₀ * finGL E a k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  obtain ⟨C, N, h0, e⟩ := hF.2.2 (g₀ * finGL E a k)
  have hy₀ := one_le_height y₀
  refine ⟨C * ((1 + 2 * a) * height y₀) ^ N, N, mul_nonneg h0 (pow_nonneg (mul_nonneg (by positivity)
    (by linarith)) N), ?_⟩
  have ht : Tendsto (fun g => g * finGL E a k) (𝓝 g₀) (𝓝 (g₀ * finGL E a k)) := (continuous_mul_const _).tendsto g₀
  filter_upwards [ht.eventually e] with g hg z
  have ex : g * infGL E a z * (infGL E a y₀ * finGL E a k) = g * finGL E a k * infGL E a (z * y₀) := by
    rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
  change ‖F (g * infGL E a z * (infGL E a y₀ * finGL E a k))‖ ≤ _
  rw [ex]
  refine (hg _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y₀)]) ?_ N) h0
  exact (RapidModel.height_mul_le z y₀).trans_eq (by ring)

theorem kerInf_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ regSpan π := by
  have hM := RapidModel.rspan_le_modGr π hF.1
  refine ⟨kerInf_mem_rspan hF.1 ν hk, continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    show ContinuousAt (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) g₀
    set_option synthInstance.maxHeartbeats 200000 in
    refine continuousAt_of_dominated (bound := fun x => C * (‖k x‖ * height (γ x) ^ N))
      (Eventually.of_forall fun g => (RapidModel.integrable_of_modGr hM hk g).aestronglyMeasurable) ?_
      ((hk.2.2 N).const_mul C)
      (Eventually.of_forall fun x => (continuous_const.mul (hF.2.1.comp (continuous_mul_const _))).continuousAt)
    filter_upwards [e] with g hg
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, ?_⟩
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · filter_upwards [e] with g hC z
      rw [kerInf]
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (RapidModel.height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem IsLocModerate.bound_of_isCompact {F : GA E a → ℂ} (hF : IsLocModerate F) {K : Set (GA E a)}
    (hK : IsCompact K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g ∈ K, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first
  | exact @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | (apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound ..)

theorem locSpan_le_regSpan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    locSpan S φ.1 ≤ regSpan π :=
  locSpan_le (mem_regSpan.2 ⟨mem_rspan hφ, isAutForm_continuous_locModerate (π.cusp φ hφ).1⟩)
    (fun _ hF h _ => rt_mem_regSpan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_regSpan hF ν hk

end GlobalTheory.JSW.MirSemi


open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory in
theorem GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧
        ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
          ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a S π φ hφ F hF
  have hG := GlobalTheory.JSW.MirSemi.locSpan_le_regSpan hφ S hF
  refine ⟨hG.2.1, fun K hK => ?_⟩
  obtain ⟨C, N, -, h⟩ := hG.2.2.bound_of_isCompact hK
  exact ⟨C, N, h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentEqualizerDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositiveStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  first | (exact @GlobalTheory.diag_sign_of_pos_eigenvector) | (exact GlobalTheory.diag_sign_of_pos_eigenvector) | (intros; apply GlobalTheory.diag_sign_of_pos_eigenvector  <;> assumption)
end

