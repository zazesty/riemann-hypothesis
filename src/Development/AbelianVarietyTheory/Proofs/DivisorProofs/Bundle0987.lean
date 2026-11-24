module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroups
section
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.FinAdeleNbhd

theorem exists_prod_openCompact_subset :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (V : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    V ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (N v : Set (v.adicCompletion F))) ∧ (∀ v, IsCompact (N v : Set (v.adicCompletion F))) ∧
      (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ⊆ V := by
  intro F _ _ κ _ V hV
  classical

  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨J, s, hs, hJs⟩ := hV
  set W : Set (FiniteAdeleRing (𝓞 F) F) := ⋂ i, s i with hWdef
  have hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 hs
  have hWV : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, y i ∈ W) → y ∈ V := fun y hy =>
    hJs fun i _ => Set.mem_iInter.1 (hy i) i

  let R : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Type := fun v => v.adicCompletion F
  let A : ∀ v, Set (R v) := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let e := RestrictedProduct.structureMap R A Filter.cofinite
  have he : Continuous e := (RestrictedProduct.isEmbedding_structureMap).continuous
  let p : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hep : (e p : FiniteAdeleRing (𝓞 F) F) = 0 := rfl
  have hpre : e ⁻¹' W ∈ 𝓝 p := he.continuousAt.preimage_mem_nhds (by rw [hep]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨I, t, ht, hIt⟩ := hpre
  have hu : ∀ v, ∃ u ∈ 𝓝 (0 : R v), Subtype.val ⁻¹' u ⊆ t v := fun v =>
    (mem_nhds_subtype (A v) (p v) (t v)).1 (ht v)
  choose u hu0 hut using hu

  have hG : ∀ v, ∃ G : OpenAddSubgroup (R v), (G : Set (R v)) ⊆ u v := fun v =>
    NonarchimedeanAddGroup.is_nonarchimedean _ (hu0 v)
  choose G hGu using hG
  let O : ∀ v, AddSubgroup (R v) := fun v => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hOset : ∀ v, ((O v : AddSubgroup (R v)) : Set (R v)) = A v := fun v => rfl
  have hOopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hOcpt : ∀ v, IsCompact (A v) := fun v =>
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let N : ∀ v, AddSubgroup (R v) := fun v => if v ∈ I then (G v).toAddSubgroup ⊓ O v else O v
  have hNO : ∀ v, ∀ x ∈ N v, x ∈ A v := by
    intro v x hx
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true] at hx; exact hx.2
    · simp only [N, hv, if_false] at hx; exact hx
  have hNG : ∀ v ∈ I, ∀ x ∈ N v, x ∈ (G v : Set (R v)) := by
    intro v hv x hx
    simp only [N, hv, if_true] at hx; exact hx.1
  have hNopen : ∀ v, IsOpen (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (G v).isOpen.inter (hOopen v)
    · simp only [N, hv, if_false]; exact hOopen v
  have hNcpt : ∀ v, IsCompact (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (hOcpt v).inter_left (G v).isClosed
    · simp only [N, hv, if_false]; exact hOcpt v
  refine ⟨N, hNopen, hNcpt, ?_, ?_, ?_⟩
  · filter_upwards [I.eventually_cofinite_notMem] with v hv
    simp only [N, hv, if_false]; rfl
  ·
    let P : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ N v}
    have hPeq : P = {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ I → a v ∈ A v} ∩ ⋂ v ∈ I, (fun a : FiniteAdeleRing (𝓞 F) F => a v) ⁻¹' (N v : Set (R v)) := by
      ext a
      simp only [P, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h; exact ⟨fun v _ => hNO v _ (h v), fun v _ => h v⟩
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ I
        · exact h2 v hv
        · have := h1 v hv
          simp only [N, hv, if_false]; exact this
    have hPopen : IsOpen P := by
      rw [hPeq]
      refine IsOpen.inter (RestrictedProduct.isOpen_forall_imp_mem hOopen) ?_
      exact isOpen_biInter_finset fun v _ => (hNopen v).preimage (RestrictedProduct.continuous_eval v)
    have hP0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ P := fun v => (N v).zero_mem
    have : (Set.univ : Set κ).pi (fun _ => P) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      set_pi_mem_nhds Set.finite_univ fun i _ => hPopen.mem_nhds hP0
    refine Filter.mem_of_superset this ?_
    intro y hy i v
    exact hy i (Set.mem_univ i) v
  ·
    intro y hy
    apply hWV
    intro i
    have hyi : ∀ v, (y i) v ∈ N v := fun v => hy i v
    let x : ∀ v, A v := fun v => ⟨(y i) v, hNO v _ (hyi v)⟩
    have hex : (e x : FiniteAdeleRing (𝓞 F) F) = y i := rfl
    have hxI : x ∈ (I : Set _).pi t := by
      intro v hv
      apply hut v
      show (y i) v ∈ u v
      exact hGu v (hNG v hv _ (hyi v))
    have h := hIt hxI
    have h' : (e x : FiniteAdeleRing (𝓞 F) F) ∈ W := h
    rw [hex] at h'
    exact h'

end GlobalTheory.FinAdeleNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunction
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem support_subset_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨S, hS⟩ := hf.2.2.2
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => q.1 * s * q.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => ?_
    exact (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory.FinClsLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjWeil
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ConjWeil

theorem hecke_mul_inv {D : D7} {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem exists_of_datum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (ho : IsWeilDatumO ψ S T χS χT om)
    (hS : IsHeckeChar D χS') (hT : IsHeckeChar D χT') (rS : ResEta D χS' S.rank) (rT : ResEta D χT' T.rank) :
    ∃ om', IsWeilDatumO ψ S T χS' χT' om' := by
  obtain ⟨o, h1, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (hecke_mul_inv hS ho.hecS) (hecke_mul_inv hT ho.hecT)
    (resEta_parity (resEta_mul rS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul rT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  exact ⟨o, h1⟩

theorem even_im_hermitian_sub (R : Ranks) : 0 % 2 = R.nV % 2 ∧ (0 + 1) % 2 = R.r % 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have h2 := R.two_le_m
  unfold Ranks.nV Ranks.r
  constructor <;> omega

end GlobalTheory.GalLift.ConjWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqGeneratorFactorialBase
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GlobalVerticalUnit
open GlobalTheory.VerticalUnit

theorem exists_const_mul_eq_gen : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  intro R K _ _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have hg : ∀ i j (x : X.left) (hi : x ∈ M.U i) (hj : x ∈ M.U j),
      haveI : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      r i = X.left.germToFunctionField (M.U i ⊓ M.U j) (M.g i j).val * r j := by
    intro i j x hi hj
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    refine hb.1 ?_
    have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
    rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
    rw [map_mul, hr, hr]
    exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _)))
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → _root_.GlobalTheory.VerticalUnit.UnitAt x (t * r j) → _root_.GlobalTheory.VerticalUnit.UnitAt x (t * r i) := by
    intro i j x t hi hj h
    rw [hg i j x hi hj, mul_left_comm]
    exact UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  have hκR : ∀ b : R, κ (algebraMap R K b) = X.left.presheaf.germ ⊤ (genericPoint X.left) trivial (constFn X.hom ⊤ b) := fun b => hb.1 (by
    rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
    exact (ffMap_germ φ hφ ⊤ ⊤ le_top _).symm)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.VerticalUnit.exists_const_mul_unitAt_coheight_one R K X.left X.hom κ hκR M.ι M.U r (LB.mem_of_cover hM) (fun i x hx => hr0 i x hx) htr (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i)⟩)
  have hu : ∀ i, ∃ v : Γ(X.left, M.U i)ˣ, ∀ [Nonempty (M.U i)],
      X.left.germToFunctionField (M.U i) v.val = κ a * r i := fun i => by
    by_cases h : Nonempty (M.U i)
    · obtain ⟨v, hv⟩ := exists_unit_eq (M.U i) (κ a * r i)
        (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ h.some.2)) (ha i)
      exact ⟨v, @fun _ => hv⟩
    · exact ⟨1, @fun h' => (h h').elim⟩
  choose u hu using hu
  refine ⟨a, ⟨u⟩, fun i j => ?_, fun i Z rr z hz => ?_⟩
  · by_cases h : Nonempty (M.U i ⊓ M.U j : X.left.Opens)
    · obtain ⟨⟨x, hi, hj⟩⟩ := h
      have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
      have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
      have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      refine Units.ext (X.left.germToFunctionField_injective (M.U i ⊓ M.U j) ?_)
      show X.left.germToFunctionField _ (X.left.presheaf.map (homOfLE _).op (u i).val) =
        X.left.germToFunctionField _ ((M.g i j).val * X.left.presheaf.map (homOfLE _).op (u j).val)
      rw [map_mul, germToFunctionField_res, germToFunctionField_res, hu, hu, hg i j x hi hj]
      ring
    · exact unit_ext fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  · have hm : rr z ∈ (M.pull φ).U fun _ => i := mem_pull.2 hz
    have h₂ : ((M.pull φ).U fun _ => i) ≤ φ ⁻¹ᵁ M.U i := fun y hy => mem_pull.1 hy
    have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, hm⟩⟩
    have : Nonempty (M.U i) := ⟨⟨_, hz⟩⟩
    have hW : (φ.appLE (M.U i) _ h₂).hom (u i).val = constFn p _ (a : K) * (c.s fun _ => i).val := by
      refine Y.germToFunctionField_injective _ ((ffMap_germ φ hφ _ _ h₂ _).symm.trans ?_)
      rw [hu, map_mul, map_mul, hκ, hr]
      refine congrArg₂ (· * ·) ?_ rfl
      exact (germToFunctionField_res (le_top : ((M.pull φ).U fun _ => i) ≤ ⊤) _).symm.trans
        (congrArg _ (res_appLE_apply p _ _ _))
    show (gm (rr ≫ φ) z (M.U i) (u i)).val = _
    rw [← gs_unit (rr ≫ φ) z _ hz, ← gs_unit rr z _ hm, ← GlobalTheory.OpenPartUnit.gs_appLE rr φ z _ _ h₂ hm, hW,
      gs_mul rr z _ hm]
    refine congrArg (· * _) ?_
    exact GlobalTheory.OpenPartUnit.gs_appLE rr p z ⊤ _ _ hm _

end GlobalTheory.GlobalVerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpace
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory Topology

namespace GlobalTheory.JSW.MirSemi

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem whit_smul_fun (c : ℂ) (F : GA E a → ℂ) (g : GA E a) : whit (c • F) g = c * whit F g := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem whit_mul_right_fun (F : GA E a → ℂ) (g h : GA E a) : whit F (g * h) = whit (fun z => F (z * h)) g := by
  simp only [whit, whittaker, mul_assoc]

theorem continuous_heightInf : Continuous (fun y : GL (Fin a) (Cinf E) => height y) := by
  unfold height
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j
  exact (continuous_const.add h1.norm).add h2.norm

theorem height_pos_inf (y : GL (Fin a) (Cinf E)) : 0 < height y := by
  unfold height; positivity

theorem whit_infGL_growth {F : GA E a → ℂ} (hc : Continuous F)
    (hg : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) (g : GA E a) :
    Continuous (fun y : GL (Fin a) (Cinf E) => whit F (g * infGL E a y)) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef
  have hK : IsCompact K := isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)
  obtain ⟨C, N, hC⟩ := hg K hK
  set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X =>
    F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef
  have hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a) :=
    fun y => rfl
  have hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N := by
    intro y X hX
    simp only [hfdef]
    rw [norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]
    exact hC _ ⟨X, subset_closure hX, rfl⟩ y
  have hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a))
      (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf] at h
  refine ⟨?_, C, N, hbound⟩
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (hc.comp (continuous_uGL.mul continuous_const)).mul hchar
  haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1 :=
    continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  simp only [hwf]
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_
    calc ‖f y X‖ ≤ C * height y ^ N := hb y X hX
      _ ≤ max C 0 * height y ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_pos_inf y).le _)
      _ ≤ max C 0 * (height y₀ + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos_inf y).le hy.le _) (le_max_right _ _)
  · refine Filter.Eventually.of_forall fun X => ?_
    have : Continuous fun y : GL (Fin a) (Cinf E) => f y X :=
      (hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul
        continuous_const
    exact this.continuousAt

end GlobalTheory.JSW.MirSemi


open GlobalTheory.JSW.MirSemi in
theorem GlobalTheory.JSW.MirSemi.whitSpace_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  intro E _ _ _ m S π φ hφ
  have hreg := _root_.GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate E (m + 1) S π φ hφ
  let 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ) :=
    { carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W}
      add_mem' := by
        rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
        refine ⟨F + G, add_mem hF hG, funext fun g => ?_⟩
        have h := ((_root_.GlobalTheory.JSW.WhitAlg.whit_linear_kerInf E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)
        simp only [one_mul] at h
        exact h
      zero_mem' := ⟨0, zero_mem _, funext fun g => by
        simpa using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩
      smul_mem' := by
        rintro c _ ⟨F, hF, rfl⟩
        exact ⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }
  refine ⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩ u hu g
    exact GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1
      (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g
  · rintro _ ⟨F, hF, rfl⟩ h hh
    exact ⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩
  · rintro _ ⟨F, hF, rfl⟩ X _ ν _ k γ hk
    refine ⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩
    rw [(_root_.GlobalTheory.JSW.WhitAlg.whit_linear_kerInf E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]
    rfl
  · rintro _ ⟨F, hF, rfl⟩ g
    exact whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨U, hU, hinv⟩ := _root_.GlobalTheory.JSW.MirSemi.locSpan_openInv E (m + 1) S π φ hφ F hF
    refine ⟨U, hU, fun u hu g => ?_⟩
    rw [whit_mul_right_fun]
    congr 1
    funext z
    exact hinv u hu z
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun g => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMul
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_cofinite : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) :=
  isIntB_one_mul_eventually

end GlobalTheory.AdicSpan
end
end

