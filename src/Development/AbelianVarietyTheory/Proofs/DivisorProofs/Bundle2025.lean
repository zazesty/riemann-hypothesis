module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEvenBC

theorem keyOn_pullback : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  intro A B K _ _ _ f h G _ _ L σ x y hG hy hσ hK _
  obtain ⟨φ, he, ψ, F, hφ, hψ, hrig, hsec, hF1, hF2, hFv⟩ := hK
  have hP := isGrpPullback_pullback G (spMap f)
  have sqφ : φ ≫ G.hom = (x.P.A.hom ≫ spMap h) ≫ spMap f := by
    rw [Category.assoc, ← spMap_comp]
    exact hφ.1.w
  obtain ⟨φ', hφ', hfst, hsnd⟩ : ∃ φ' : x.P.A.left ⟶ ((Over.pullback (spMap f)).obj G).left,
      IsGrpPullback x.P.A ((Over.pullback (spMap f)).obj G) (spMap h) φ' ∧ φ' ≫ pullback.fst G.hom (spMap f) = φ ∧
        φ' ≫ ((Over.pullback (spMap f)).obj G).hom = x.P.A.hom ≫ spMap h := by
    refine ⟨pullback.lift φ (x.P.A.hom ≫ spMap h) sqφ, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, ← spMap_comp]
    exact hφ
  subst hfst
  have hL := L.isLB
  have hL' : (L.L.pull (pullback.fst G.hom (spMap f))).IsLB := LB.isLB_pull hL _
  have heF : eSec ((Over.pullback (spMap f)).obj G) ≫ pullback.fst G.hom (spMap f) = spMap f ≫ eSec G :=
    PolBaseChange.eSec_comm hP
  let L' : RigLB ((Over.pullback (spMap f)).obj G) :=
    ⟨L.L.pull (pullback.fst G.hom (spMap f)), rigPullOf (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L L.rig, hL',
      Out.LBxP.isGen_pullAlong L.L (pullback.fst G.hom (spMap f)) (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1)
        (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => heF) L.rig L.rigGen⟩
  have he' : eSec x.P.A ≫ φ' = spMap h ≫ eSec ((Over.pullback (spMap f)).obj G) := PolBaseChange.eSec_comm hφ'
  have pw := (isGen_iff (L := L.L) (F := pullback.fst G.hom (spMap f)) (idIso _)).1 (idIso_isGen hL')
  obtain ⟨σ', hσ'⟩ := sec_pull_down pw hL hL' σ
  have pψ := (isGen_iff ψ).1 hψ
  obtain ⟨w', T⟩ := exists_cancel hL (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) ψ pw pψ hL' x.P.isLB
  have H : PMaps (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) (K := PUnit)
      (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (spMap f) :=
    (maps_iff _ _ _ _ L'.rig L.rig (spMap f) L'.rig (rigPull_le (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L) (fun _ => rfl)).1 (idIso_maps L')
  have H'' : PMaps ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec G) (fun _ => 1) x.rig L.rig
      (spMap h ≫ spMap f) := by
    rw [← spMap_comp]
    exact (maps_iff ψ _ _ _ x.rig L.rig (spMap (h.comp f)) _ (rigPull_le (G' := x.P.A) (φ' ≫ pullback.fst G.hom (spMap f)) (spMap (h.comp f)) he L.L)
      (fun _ => rfl)).1 hrig
  have H' := T.pmaps_cancel hL (fun _ => he') H H''
  have hrig' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ' (spMap h) he' L'.L L'.rig) :=
    (maps_iff w' _ _ _ x.rig L'.rig (spMap h) _ (rigPull_le φ' (spMap h) he' L'.L) (fun _ => rfl)).2 H'

  have hsec' : ∀ (j : (L'.L.pull φ').ι) (i : x.P.L.ι) (hh : (L'.L.pull φ').U j ⊓ x.P.L.U i ≤ φ' ⁻¹ᵁ L'.L.U (j PUnit.unit)),
      (φ'.appLE _ _ hh).hom (σ'.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L'.L.pull φ').U j ⊓ x.P.L.U i) from (w'.s (j, i)).val) * resG _ inf_le_right (x.th.f i) := by
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk w' σ' x.th ?_
    intro z J k hJ hk
    have ha : (pullback.fst G.hom (spMap f)) (φ' z) ∈ L.L.U (J PUnit.unit) := mem_pull.1 hJ
    have hW : (𝟙 x.P.A.left) z ∈ (L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k :=
      ⟨mem_pull.2 ha, hk⟩
    have s2 : gs (𝟙 _ ≫ φ' ≫ pullback.fst G.hom (spMap f)) z _ (σ.f (J PUnit.unit)) =
        (gw ψ (𝟙 _) z (J PUnit.unit) k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e := congrArg (gs (𝟙 _) z ((L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k))
        (hsec (fun _ => J PUnit.unit) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE (φ' ≫ pullback.fst G.hom (spMap f)) _ _ _ (𝟙 _) z hW _).symm.trans (e.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := hσ' _ (𝟙 _ ≫ φ') z (J PUnit.unit) J ha hJ
    have e3 := T _ (𝟙 _) z (J PUnit.unit) J k ha hJ hk
    rw [Category.assoc] at e1
    rw [e1, e3, Units.val_mul, _root_.mul_assoc] at s2
    exact (Units.mul_right_inj _).1 s2
  have hnz : NzFib (L := L'.L) σ' := by
    intro s
    obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y0, rfl, hy0⟩ := Scheme.exists_preimage_of_isPullback hP.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y0, hy0, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs (pullback.fst G.hom (spMap f)) y0 _ (σ.f k)) := by
      rw [gs_stalkMap _ y0 _ hk]; exact u.map _
    have e := hσ' _ (𝟙 _) y0 k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)

  have := hG.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y i).left) ≫ G.hom = (epsR B).hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let y' : Fin x.P.g → (epsR B ⟶ ((Over.pullback (spMap f)).obj G)) := fun i =>
    Over.homMk (hP.1.lift _ _ (sq i)) (hP.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap f) = spMap (Chart.dualMapR f) ≫ (y i).left :=
    fun i => hP.1.lift_fst _ _ _
  have hadd : ∀ (a b : B) (w : Chart.sp (DualNumber B) ⟶ ((Over.pullback (spMap f)).obj G)), Chart.IsTan w →
      Chart.spMap (Chart.scaleD (a + b)) ≫ w = (Chart.spMap (Chart.scaleD a) ≫ w) * (Chart.spMap (Chart.scaleD b) ≫ w) :=
    fun a b w hw => GlobalTheory.LieMultiple.scale_add ((Chart.isTan_iff w).1 hw) a b
  have hT : ∀ i, IsTangent (y' i) := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hy', show η[((Over.pullback (spMap f)).obj G)].left = eSec ((Over.pullback (spMap f)).obj G) from rfl, heF, ← Category.assoc]
      have e0 := hy.1 i
      rw [IsTangent] at e0
      rw [show eSec G = η[G].left from rfl, ← e0, ← Category.assoc]
      congr 1
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      simp [Chart.dualMapR]
    · rw [Category.assoc, Over.w (y' i), Over.w η[((Over.pullback (spMap f)).obj G)]]
      show Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      convert Spec.map_id (CommRingCat.of B)
      ext a; simp
  have hLie : IsLieBasis y' := Chart.frameLieBCR G hy f hP hadd hT hy'

  have hF' : F = (Chart.dualMapR h).comp (Chart.dualMapR f) := by
    refine GlobalTheory.KeyExtLie.dnRingHom_ext (fun a => ?_) ?_
    · have e1 := hF1 a
      simp only [TrivSqZeroExt.algebraMap_eq_inl] at e1
      rw [e1]
      simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [hF2]
      ext <;> simp [Chart.dualMapR]
  have hv' : ∀ i, (x.v i).left ≫ φ' = spMap (Chart.dualMapR h) ≫ (y' i).left := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hFv i, Category.assoc, hy', ← Category.assoc, hF', spMap_comp]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x.v i), Category.assoc, Over.w (y' i)]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨L', σ', y', ⟨idIso _, idIso_isGen hL'⟩, hLie, hnz, φ', he', w', Chart.dualMapR h, hφ',
    (isGen_iff w').2 (T.pgen_cancel hL pw pψ), hrig', hsec', fun a => ?_, ?_, hv'⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyEvenBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacV

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S := GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V F E σ B a a' G X om om' hT v w hw hv H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (_root_.GlobalTheory.star_mem_schA_main _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.DblVacV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingTermUniqueSupportedBalancedCone
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem leadingTerm_unique : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a →
    ∀ (β : LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), 0 < k → (∀ j, 0 < c j) → k • β = ∑ j, c j • γ j →
    (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[O] X) (N : ℕ), 3 ≤ N → (∀ x, CongMod N (e x) x) →
    d * φ.evalZ β = (∑ i, β (e (a i)) (e (a i)) : ℤ) → ∀ x, e x = x := by
  intro O _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS β k c hk hc hβ hpos e N hN he hd
  have hkβ : ∀ y z, (k : ℤ) * β y z = ∑ j, (c j : ℤ) * γ j y z := fun y z => by
    have := LinearMap.congr_fun₂ hβ y z
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hbal : β ∈ balForms bar X := by
    refine ⟨fun y z => mul_left_cancel₀ hk0 ?_, fun o y z => mul_left_cancel₀ hk0 ?_⟩
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).1]
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).2]
  have hbal' : pull e.toLinearMap β ∈ balForms bar X := pull_mem _ hbal
  have hnn' : ∀ y, 0 ≤ pull e.toLinearMap β y y := fun y => by
    rw [pull_apply]
    by_cases h0 : e.toLinearMap y = 0
    · rw [h0]; simp
    · exact (hpos _ h0).le
  obtain ⟨k', c', hk', hβ'⟩ := hS.only _ hbal' hnn' (by rw [evalZ_pull φ e.surjective]; exact hd)
  have hsum : ∑ j, (k' * c j) • pull e.toLinearMap (γ j) = ∑ j, (k * c' j) • γ j := by
    refine LinearMap.ext₂ fun y z => ?_
    have h1 := hkβ (e y) (e z)
    have h2 := LinearMap.congr_fun₂ hβ' y z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul, LinearEquiv.coe_coe] at h1 h2 ⊢
    have e1 : ∑ j, ((k' * c j : ℕ) : ℤ) * γ j (e y) (e z) = k' * ∑ j, (c j : ℤ) * γ j (e y) (e z) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have e2 : ∑ j, ((k * c' j : ℕ) : ℤ) * γ j y z = k * ∑ j, (c' j : ℤ) * γ j y z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1, e2, ← h1, ← h2]; ring
  have hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j) := hγ.pull_equiv e
  choose σ hσ using _root_.GlobalTheory.Poinc.intCone_face O bar φ X hF r r _ γ hγe hγ (fun j => k' * c j) (fun j => k * c' j)
    (fun j => Nat.mul_pos hk' (hc j)) hsum
  have hσinj : Function.Injective σ := fun i j hij => hγe.injective (by simp only [hσ, hij])
  let σe := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hG : ∀ y z, (∑ j, γ j) (e y) (e z) = (∑ j, γ j) y z := by
    intro y z
    simp only [LinearMap.sum_apply]
    calc ∑ j, γ j (e y) (e z) = ∑ j, γ (σe j) y z :=
          Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hσ j) y z
      _ = ∑ j, γ j y z := σe.sum_comp (fun j => γ j y z)
  have hGpos : ∀ x, x ≠ 0 → 0 < (∑ j, γ j) x x := by
    intro x hx
    have h2 : 0 < (k : ℤ) * β x x := mul_pos (by exact_mod_cast hk) (hpos x hx)
    rw [hkβ] at h2
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (show ∑ j : Fin r, (0 : ℤ) < _ by simpa using h2)
    have hj' : 0 < γ j x x := pos_of_mul_pos_right hj (by positivity)
    simp only [LinearMap.sum_apply]
    exact hj'.trans_le (Finset.single_le_sum (fun i _ => hγ.nonneg i x) (Finset.mem_univ j))
  have key := _root_.GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ j, γ j) hGpos e.toAddEquiv.toIntLinearEquiv (fun y z => hG y z) N hN he
  intro x
  simpa using LinearEquiv.congr_fun key x

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOneStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ γ : LevelAut Dw l, UnipAt I γ → ∀ y : FrPt Xo c ℂ, ptF (move Xo c γ y) = ptF y → γ = 1 := by
  first | exact @GlobalTheory.UnipFree.free | exact GlobalTheory.UnipFree.free | (intros; apply GlobalTheory.UnipFree.free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolPush

theorem meas_translate_eq : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  intro D V θ A m rp K μ hV hθ hA hm hc hrp hK hμ g hg B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← GlobalTheory.CovTop.VolBox.meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB,
    ← measure_preimage_mul μ g⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
  congr 1
  ext h
  show finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B ↔ finE V (g⁻¹ * h) ∈ K ∧ rp (g⁻¹ * h) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

end GlobalTheory.CovTop.VolPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonpos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem linesLE_zero_of_sub_lie : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → LinesLE g 0 := by
  intro k K _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s g hV₀ hs hg hloc
  intro E _ _ _ _ _ ρ hρ w hw
  simp only [zero_mul]
  by_contra hpos
  push_neg at hpos
  have hpos' : 0 < degLine (pullAd ρ g) w := by exact_mod_cast hpos
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  letI : Algebra ℚ E := DivisionRing.toRatAlgebra

  have hne : Nonempty (Place k E) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [degLine, finsum_of_isEmpty] at hpos'
  obtain ⟨p₀⟩ := hne
  obtain ⟨b₀, V, t, V', h₀, h₁, hxV, M, -, -, -, -, -⟩ := hloc (ρ p₀)
  set b : Sp E ⟶ C := spMap (algebraMap K E) ≫ x with hb
  have hbV : ⊤ ≤ b ⁻¹ᵁ V₀ := by
    intro z _
    have hz := h₀ (hxV (show (spMap (algebraMap K E)).base z ∈ (⊤ : (Sp K).Opens) from trivial))
    show b.base z ∈ V₀
    simpa [hb] using hz
  haveI : QuasiSeparated G.hom := inferInstance
  obtain ⟨ξ, hξ, htan⟩ := _root_.GlobalTheory.Nef.exists_path_tan C G E hG.smooth inferInstance b r V₀ (fun j => i.app V₀ (s j)) w hbV

  have hvec : ∀ p : Place k E, (pullAd ρ g p).mulVec w ≠ 0 := by
    intro p h
    have hdet : (pullAd ρ g p).det ≠ 0 := by
      simp only [pullAd]
      have e := RingHom.map_det (algebraMap K E) (g (ρ p))
      rw [RingHom.mapMatrix_apply] at e
      rw [← e]
      exact (map_ne_zero _).mpr (hg.1 (ρ p))
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
  have hu : ∀ p : Place k E, ∃ u : E, u ≠ 0 ∧ p.1 u = nrm p ((pullAd ρ g p).mulVec w) ∧
      ordVec p ((pullAd ρ g p).mulVec w) = ord p u := by
    intro p
    obtain ⟨j, hj0, hj1, hj2, -⟩ := ((_root_.GlobalTheory.Nef.ord_calculus k E p).2.2.2.2.2.2.1) r _ (hvec p)
    exact ⟨_, hj0, hj1.symm, hj2⟩
  choose u hu0 hu1 hu2 using hu
  have hsum : ∑ᶠ p, ord p (u p) = degLine (pullAd ρ g) w := by
    unfold degLine; exact finsum_congr fun p => (hu2 p).symm
  have hfin : {p | ord p (u p) ≠ 0}.Finite := by
    by_contra hinf
    have : ∑ᶠ p, ord p (u p) = 0 := finsum_of_infinite_support (by simpa [Function.support] using hinf)
    omega
  have hint := fun p => _root_.GlobalTheory.Nef.genPath_scaling k K E C x hx G hG W r i V₀ s ρ hρ p (g (ρ p)) (hloc (ρ p)) w (u p) (hu0 p) (hu1 p) ξ hξ htan
  have hrat := _root_.GlobalTheory.Nef.isRatPath_of_integral_at_places k K E C x hx G ξ u hu0 hfin (by omega) hint
  have htriv : ξ = triv G b := _root_.GlobalTheory.Nef.ratRigid_of_isSemiAbelian C G hG E b ξ hξ hrat
  rw [htriv] at htan
  exact hw (_root_.GlobalTheory.Nef.tan_triv_eq_zero k K E C x hx G hG W r i hi V₀ s hV₀ hs w htan)

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInduction
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem eq_of_sup_baseIdeal_pow_eq {C : Type} [CommRing C] [IsNoetherianRing C] {J : Ideal C}
    (hJ : J ≤ Ideal.jacobson ⊥) {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of C)) [IsProper p]
    (a a' : V.IdealSheafData)
    (h : ∀ e : ℕ, a ⊔ baseIdeal p (J ^ (e + 1)) = a' ⊔ baseIdeal p (J ^ (e + 1))) : a = a' := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  refine le_antisymm ?_ ?_
  · exact _root_.GlobalTheory.FormalAlg.le_of_le_reductions C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left
  · exact _root_.GlobalTheory.FormalAlg.le_of_le_reductions C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left

theorem map_inf_eq_of_reductions : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  intro C _ _ J hJ W' π U hπ hU K τ hK
  obtain ⟨k₀, hk₀⟩ := _root_.GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK
  refine ⟨k₀, fun k hk T' T'' h' h'' => ?_⟩
  have e' : T' = τ.comap π := by
    refine eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_
    rw [h' e, Scheme.IdealSheafData.comap_sup, _root_.GlobalTheory.FormalAlg.baseIdeal_calculus.1, Category.comp_id]
  have e'' : T'' = τ ⊔ K ^ k := by
    refine eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_
    rw [h'' e, sup_right_comm]
  rw [e', e'']
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheafStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf : ∀ (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0}) (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z), z ∈ V → I ≤ (p z).asIdeal → r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩ → z ∈ Z.basicOpen r := by
  first | exact @GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | exact GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | (intros; apply GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal <;> assumption)
end

