module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorMove

theorem isLocalHom_of_finExt {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hi : Algebra.IsIntegral R R' := ⟨fun x => h.2.2.to_isIntegral x⟩
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) h.2.2.to_isIntegral (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_tfae ρ).out 1 5).2 hm

theorem exists_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁] [GrpObj G₂]
    {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {β₁ : G₁.left ⟶ G.left} {β₂ : G₂.left ⟶ G.left}
    {β₁₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {β₂₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (h₁ : IsGrpPullback G₁ G f β₁) (h₂ : IsGrpPullback G₂ G (g ≫ f) β₂)
    (s₁ : Geo.Tor.IsSquare β₁ β₁₂) (s₂ : Geo.Tor.IsSquare β₂ β₂₂) :
    ∃ (β : G₂.left ⟶ G₁.left) (β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left),
      IsGrpPullback G₂ G₁ g β ∧ Geo.Tor.IsSquare β β' ∧ β₂₂ = β' ≫ β₁₂ := by
  have w₀ : β₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h₂.1.w, Category.assoc]
  have e : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ β₁ = β₂ := h₁.1.lift_fst _ _ _
  have w : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ G₁.hom = G₂.hom ≫ g := h₁.1.lift_snd _ _ _
  generalize h₁.1.lift β₂ (G₂.hom ≫ g) w₀ = β at e w
  have s : Geo.Tor.IsSquare β (lift (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))).left :=
    ⟨congrArg (fun q => q.left) (lift_fst (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))),
      congrArg (fun q => q.left) (lift_snd (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂)))⟩
  obtain ⟨β', s⟩ : ∃ β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left, Geo.Tor.IsSquare β β' := ⟨_, s⟩
  refine ⟨β, β', IsGrpPullback.cancel h₁ (h₂.congr rfl e.symm) w, s, ?_⟩
  have a : β₂₂ ≫ (fst G G).left = (β' ≫ β₁₂) ≫ (fst G G).left := by
    rw [s₂.1, Category.assoc, s₁.1, ← Category.assoc, s.1, Category.assoc, e]
  have b : β₂₂ ≫ (snd G G).left = (β' ≫ β₁₂) ≫ (snd G G).left := by
    rw [s₂.2, Category.assoc, s₁.2, ← Category.assoc, s.2, Category.assoc, e]
  exact pullback.hom_ext a b

theorem extLam_congr {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {L : LB ((Over.pullback (jK R)).obj G).left} (hL : L.IsLB) {P Q : LB (G2 G).left} (h : ExtLam G L P) (hQ : Q.IsLB)
    (e : LBIso P Q) : ExtLam G L Q :=
  ⟨hQ, fun κ hκ => LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_pull h.1 _) (LB.isLB_pull hQ _) (h.2 κ hκ)
    (GlobalTheory.GenSpread.lbIso_pullback e κ)⟩

theorem exists_finExt_factor_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁
    hρ₁ hβ₁ hsq₁ hgen₁ hext
  haveI := hR.2
  have hR₁ : Base R₁ := ⟨hρ₁.1, charZero_of_injective_ringHom hρ₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (Geo.Tor.IsSemiAbelian.pullback (f := spMap ρ₁) (G := G) hG)
  obtain ⟨R₂, _, _, _, ρ, hρ, H⟩ := _root_.GlobalTheory.Mum.exists_finExt_trait_unif_lam R₁ hR₁ G₁ hG₁ A₁ gen₁ hgen₁ _ hext
  have hρ₂ : FinExt (ρ.comp ρ₁) := ⟨hρ.1, hρ.2.1.comp hρ₁.2.1, hρ.2.2.comp hρ₁.2.2⟩
  have hR₂ : Base R₂ := ⟨hρ.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  obtain ⟨D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, β₂, β₂₂, inc₂, pr₂, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    GlobalTheory.FactorPull.factor_baseChange R hR.1 D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr hip hpi R₂ (ρ.comp ρ₁) hρ.1
      hρ₂.2.1 (isLocalHom_of_finExt hρ₂)
  have es : spMap (ρ.comp ρ₁) = spMap ρ ≫ spMap ρ₁ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨β, β', hβ, hsq, hc⟩ := exists_factor hβ₁ (h8.congr es rfl) hsq₁ h9
  obtain ⟨A₂, gen₂, W, _, _, _, φ, GW, _, _, βW, DW, AW, UW, κ, k1, k2, k3, k4, k5, k6, k7, k8⟩ := H G₂ β β' hβ hsq
  have hP := LB.isLB_pull (L := abelian₂ G' U'.LG.L) (LB.isLB_linComb U'.LG.isLB _ _)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have hP₂ := LB.isLB_pull (L := abelian₂ G₂' U₂'.LG.L) (LB.isLB_linComb U₂'.LG.isLB _ _)
    (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ.comp ρ₁, D₂, D₂', F₂, A₂', G₂', inferInstance, inferInstance,
    U₂', oA₂, oG₂, G₂, inferInstance, inferInstance, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, inferInstance, inferInstance,
    inferInstance, φ, GW, inferInstance, inferInstance, βW, DW, AW, UW, κ, hρ₂, hR₂, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    k1, ?_, h10, k3, k4, k5, k6, k7, k8⟩
  exact extLam_congr (LB.isLB_pull A₂.isLB _) k2 hP₂
    (LBIso.trans hP₂ (LB.isLB_pull hP _) k2.1 h10 (GlobalTheory.GenSpread.lbIso_pull_pull hP β' hc)).symm

end GlobalTheory.Mum.FactorMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GCTrait

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem map_cycAway_mem {n : ℕ} {L : Type} [Field L] (φ : cycAway n →+* L) (K : Subring L)
    (hz : φ (zetaAway n) ∈ K) (hi : φ ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ ∈ K) (c : cycAway n) : φ c ∈ K := by
  obtain ⟨c, hc⟩ := c
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz
    · exact hi
  | zero => rw [show (⟨0, _⟩ : cycAway n) = 0 from rfl, map_zero]; exact K.zero_mem
  | one => rw [show (⟨1, _⟩ : cycAway n) = 1 from rfl, map_one]; exact K.one_mem
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, _⟩ : cycAway n) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add (f := _)]; exact K.add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, _⟩ : cycAway n) = -⟨x, hx⟩ from rfl, map_neg]; exact K.neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, _⟩ : cycAway n) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]; exact K.mul_mem ihx ihy

theorem exists_finite_point (n : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s]
    (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := cycAway n) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U)) ∪
    {φ.hom (a.hom (zetaAway n)), φ.hom (a.hom ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩)}
  have hSfin : S.Finite := (T.finite_toSet.image _).union (Set.toFinite _)
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : cycAway n, φ.hom (a.hom c) ∈ K.toSubfield.toSubring :=
    map_cycAway_mem (φ.hom.comp a.hom) K.toSubfield.toSubring
      (hS (Or.inr (Or.inl rfl))) (hS (Or.inr (Or.inr rfl)))
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin (cycAway n) (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_ext_emb (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W)
    (hinj : Function.Injective f) (hloc : IsLocalHom f) (hfin : f.Finite)
    (hc : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) (κ : FractionRing V →+* PadicAlgCl p)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ ι : FractionRing W →+* PadicAlgCl p, ι.comp fK = κ ∧
      ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  letI : Algebra V W := f.toAlgebra
  letI : Algebra (FractionRing V) (FractionRing W) := fK.toAlgebra
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  haveI : IsLocalHom (algebraMap V W) := hloc
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := fun w =>
    IsIntegral.map_of_comp_eq (algebraMap V (FractionRing V)) (algebraMap W (FractionRing W))
      (RingHom.ext fun v => hc v) (Algebra.IsIntegral.isIntegral w)
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    rw [div_eq_mul_inv]
    exact ((hint a).mul (hint b).inv).isAlgebraic
  let ι : FractionRing W →ₐ[FractionRing V] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ι.toRingHom.comp fK = κ := RingHom.ext fun x => ι.commutes x
  refine ⟨ι.toRingHom, hι, GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ ι.toRingHom (fun v => ?_) hV⟩
  show ι (algebraMap W (FractionRing W) (f v)) = _
  rw [← hc]
  exact ι.commutes _

theorem exists_cTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X₁.M.Z), Set.range (gPt p ≫ y ≫ X₁.π) ⊆ Set.range i → ∃ c : CTrait X₁ p (y (cPt p)), c.y = y := by
  intro g n F W Z i X₁ hg hn hodd hi p _ y hr
  let y₁ : Sp (PadicAlgCl p) ⟶ F.X := IsOpenImmersion.lift i (gPt p ≫ y ≫ X₁.π) hr
  have hy₁ : y₁ ≫ i = gPt p ≫ y ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  obtain ⟨K, hK, x, hx⟩ := exists_finite_point n F.s p y₁
  obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
  haveI := hdvr
  haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
  let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
  let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
  have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ := _root_.GlobalTheory.Poinc.traitExtSt g n (cycAway n) (zetaAway n) F _ hbase hdvr (spMap es ≫ x)
  obtain ⟨ι, hι, hint⟩ := exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
  have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
      (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
    show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
    rw [AlgEquiv.commutes]
    rfl
  have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es = algebraMap K (PadicAlgCl p) := by
    ext k
    rw [h2]
    show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
    rw [AlgEquiv.apply_symm_apply]
  have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
    rw [spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
  refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
  calc gPt p ≫ y ≫ X₁.π = y₁ ≫ i := hy₁.symm
    _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ i := by rw [hx]
    _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ i := by rw [key]
    _ = spMap ι ≫ T.y ≫ i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.Poinc.GCTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.RowTest.BottomMeas

theorem exists_haar_fd_volQ_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  intro D T L sc G W i j A A' WW X _
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas WW
  have : BorelSpace (GA D WW) := ⟨rfl⟩
  refine ⟨ν, 𝓕, hν, h𝓕, ?_⟩
  haveI := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure (V := WW) ν
  rw [(GlobalTheory.QuotFundDom.volQ_and_integrable_iff D WW ν 𝓕 hν h𝓕).1]
  refine ENNReal.toReal_ne_zero.2 ⟨h𝓕.measure_ne_zero (NeZero.ne ν), ?_⟩
  exact (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol WW ν _ hν h𝓕).ne

end GlobalTheory.RowTest.BottomMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

theorem kerPow_one {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) :
    KerPow f 1 k (1 : ptOver k k ⟶ A.X) := by
  refine ⟨⟨MonObj.one_comp _, one_pow _⟩, ?_⟩
  intro R _ _ x _ hx
  rw [pow_one] at hx
  subst hx
  refine ⟨Algebra.ofId k R, ?_, fun ψ _ => Subsingleton.elim _ _⟩
  change (spOver (Algebra.ofId k R) ≫ (1 : ptOver k k ⟶ A.X)).left = (1 : ptOver k R ⟶ A.X).left
  rw [MonObj.comp_one]

theorem exists_kerPow_primePow {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) (q e : ℕ) (hq : q.Prime) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f (q ^ e) H i ∧ ∃ j : ℕ, Module.finrank k H = q ^ j := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨G, -, ⟨tA⟩⟩ := GlobalTheory.AVTower.exists_tower q k A
  obtain ⟨G', -, ⟨tB⟩⟩ := GlobalTheory.AVTower.exists_tower q k B
  refine ⟨_, inferInstance, inferInstance, kerPt tA tB f e, kerPow_kerPt tA tB f e, ?_⟩
  exact (Nat.dvd_prime_pow hq).1 (finrank_quot_kerIdeal_dvd (tA.map tB f.hom) e) |>.imp fun _ h => h.2

theorem exists_kerPow_not_dvd : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B)
    (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  intro p hp k _ A B f m
  have hpp : p.Prime := hp.out
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ hdvd
    have hqp : q ≠ p := by
      rintro rfl
      exact hdvd (dvd_pow_self q hn.ne')
    obtain ⟨H, _, _, i, hi, j, hj⟩ := exists_kerPow_primePow f q n hq
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hj]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h)).symm
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    refine ⟨k, inferInstance, inferInstance, 1, kerPow_one f, ?_⟩
    rw [Module.finrank_self]
    exact hpp.not_dvd_one
  | coprime a b ha hb hab iha ihb =>
    intro _ hdvd
    have hpa : ¬ p ∣ a := fun h => hdvd (h.mul_right b)
    have hpb : ¬ p ∣ b := fun h => hdvd (h.mul_left a)
    obtain ⟨H₁, _, _, i₁, hi₁, h₁⟩ := iha (by omega) hpa
    obtain ⟨H₂, _, _, i₂, hi₂, h₂⟩ := ihb (by omega) hpb
    obtain ⟨H, _, _, i, hi, hH⟩ := _root_.GlobalTheory.AV.KerPart.kerPow_mul_of_coprime k A B f a b hab H₁ i₁ H₂ i₂ hi₁ hi₂
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hH]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
    · exact h₁ h
    · exact h₂ h

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_desc_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hl D' G' _ _ A' hP hG hU hS
  obtain ⟨A₀, e₀, hc, hS₀, hI⟩ := GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS
  obtain ⟨R₁, _, _, _, ρ, D₁, A, hF, hP₁, hS₁, hT⟩ :=
    GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS A₀ e₀ hc hS₀ hI
  have hR₁ : Base R₁ := ⟨hF.1, by haveI := hR.2; exact charZero_of_injective_ringHom hF.2.1⟩
  obtain ⟨lab, hO⟩ := _root_.GlobalTheory.Mum.exists_oneTrait R₁ hR₁ D₁ A hT
  exact GlobalTheory.T.exists_finite_extension_galois_equivariant_labels R hR D n hn ho hu R₁ ρ D₁ A lab hF hP₁ hS₁ hO

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | (exact @GlobalTheory.HomFixMat.exists_locClosed_homFix) | (exact GlobalTheory.HomFixMat.exists_locClosed_homFix) | (intros; apply GlobalTheory.HomFixMat.exists_locClosed_homFix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFormalSectionCoefficientFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumford_formal_section_coefficient_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ g : ∀ β, SecT D.toPre a N (-1) β, Small (maximalIdeal R) (w := id) g ∧ TFE h h' g ∧ (∀ β, β ≠ 0 → Van (maximalIdeal R) (g β) 0) ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval (g 0) (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J = sval σ₀ (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J := by
  first | exact @GlobalTheory.MumCoef.coef | exact GlobalTheory.MumCoef.coef | (intros; apply GlobalTheory.MumCoef.coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ratios_generate_mod_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_mod | exact GlobalTheory.Mum.exists_ratio_gen_mod | (intros; apply GlobalTheory.Mum.exists_ratio_gen_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.InertSph.vac_fixed_pair | exact GlobalTheory.InertSph.vac_fixed_pair | (intros; apply GlobalTheory.InertSph.vac_fixed_pair <;> assumption)
end

