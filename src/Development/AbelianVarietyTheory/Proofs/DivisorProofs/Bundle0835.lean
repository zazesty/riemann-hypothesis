module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ValuativeFlat

theorem isProper_of_lift_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  intro R _ _ _ _ X s hq hflat h
  have hq' : IsQProjOver (s ≫ 𝟙 (Sp R)) := by rwa [Category.comp_id]
  have hP := GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R X (Sp R) s (𝟙 _) inferInstance hq' ?_
  · exact hP
  intro V K _ _ _ _ _ _ _ x y hx hxy
  let β : R →+* V := (Spec.preimage y).hom
  have hy : y = spMap β := by simp [β, spMap]
  have hxs : x ≫ s = spMap ((algebraMap V K).comp β) := by
    rw [hxy, hy, spMap, spMap, ← Spec.map_comp]; rfl
  have hinj : Function.Injective ((algebraMap V K).comp β) :=
    _root_.GlobalTheory.injective_of_flat_of_range_subset_genericPoints R K X s x _ hflat hx hxs
  have : CharZero K := charZero_of_injective_ringHom hinj
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hloc, f, hf⟩ := h V K β x hxs
  exact _root_.GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain V K W L hc hloc X x f hf

end GlobalTheory.ValuativeFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafOfOpenImmersionLocalGlue
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isSheaf_of_local_glue : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → Presieve.IsSheaf Scheme.zariskiTopology F := by
  intro F hext hglue
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  choose jj q hq using 𝒰.exists_eq
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨y₀, hy₀⟩ := hglue Y Y (fun p => 𝒰.X (jj p)) (fun p => 𝒰.f (jj p)) (fun p => x (jj p))
      (fun p => inferInstance) (fun p => ⟨p, q p, hq p⟩)
      (fun i k Z a b h => hx (jj i) (jj k) Z a b h)
    refine ⟨y₀, fun i => hext _ _ _ fun r => ?_⟩
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i)
      (g := 𝒰.f (jj (𝒰.f i r))) r (q (𝒰.f i r)) (hq _).symm
    refine ⟨_, pullback.fst (𝒰.f i) (𝒰.f (jj (𝒰.f i r))), inferInstance, ⟨w, hw⟩, ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, pullback.condition, op_comp,
      Functor.map_comp_apply, hy₀]
    exact (hx _ _ _ _ _ pullback.condition).symm
  · intro y y' h h'
    refine hext Y y y' fun p => ?_
    exact ⟨𝒰.X (jj p), 𝒰.f (jj p), inferInstance, ⟨q p, hq p⟩, (h _).trans (h' _).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMapCoeffSpaceOfJetStepPartitionTriples
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem jetInVV_of_stepWeights : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  intro K _ _ ι _ a b hlt lam ν lam' hw J P hP
  choose s' hs' using fun τ => (hw τ).2.1
  choose s hs using fun τ => (hw τ).2.2
  refine GlobalTheory.JetPoint.jetMap_mem hlt.le _ _ _ (fun ap => ?_) J
  refine GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hlt lam lam' s (fun τ => if 0 < a then s' τ else 0) _
    ⟨fun τ i => ?_, fun τ j hj => ?_, fun τ => ?_⟩ ap _ hP
  · have h := hs τ (Fin.castLE hlt.le i)
    have h0 := hs' τ i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, Fin.val_castLE, i.2, dif_pos, Fin.eta] at h
    simp only [Fin.pos i, if_true]
    omega
  · have h := hs τ j
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, dif_neg (not_lt.2 hj)] at h
    omega
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry DomWeight.detShift
    split_ifs with h
    · have h0 := hs' τ ⟨a - 1, by omega⟩
      have h1 := (hw τ).1 ⟨a - 1, by omega⟩
      simp only
      omega
    · simp

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.JetBase

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

variable {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]

theorem map_pairP_basis {n : ℕ} (lam : ι → DomWeight n) (i j : VVIdx lam) :
    σ (pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVVfun K lam i) (bVVfun K lam j)) =
      pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (map σ (bVVfun K lam i)) (map σ (bVVfun K lam j)) := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  have e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q := by
    rw [hQ, MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  have e2 : σ (extNorm K lam) = extNorm ℂ lam := by
    rw [pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  rw [pairP_apply, pairP_apply, pb_gramTw_one, pb_gramTw_one, pb_blockAct_one_tr, pb_blockAct_one_tr, fockL_apply, fockL_apply,
    map_mul, map_div₀, map_one, e2]
  congr 1
  rw [e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]

theorem sqAt_eq {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) (y : Formalism.L2.DIV.VV ℂ lam)
    (h : (y : Pol ℂ ι n) = map σ (x : Pol K ι n)) : sqAt σ lam x = invNormSq lam y := by
  have hx : (x : Pol K ι n) = ∑ i, (bVV K lam).repr x i • bVVfun K lam i := by
    conv_lhs => rw [← (bVV K lam).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  have hy : (y : Pol ℂ ι n) = ∑ i, σ ((bVV K lam).repr x i) • map σ (bVVfun K lam i) := by
    rw [h]
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, smul_eq_C_mul, map_mul, map_C]
  unfold sqAt invNormSq
  congr 1
  rw [pairK_apply, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairK_apply, bVV_coe, map_pairP_basis, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {a b : ℕ}


omit [StarRing K] in
theorem degAt_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ)
    (hμ : μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ lastEntry (nu τ))).support) (τ : ι) :
    ((degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ : ℕ) : ℤ) = ∑ i, (nu τ).w i := by
  classical
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ
    (GlobalTheory.JetDeg.sharp_hom (fun τ => lastEntry (nu τ)) τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  have hd : degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ = Finsupp.weight (GlobalTheory.JetDeg.derW a b τ) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, degAt, Finset.sum_filter,
      Finset.sum_subset (Finset.subset_univ _)]
    · simp [GlobalTheory.JetDeg.derW]
    · intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk]
      simp
  rw [hd, h]
  push_cast
  obtain ⟨h0, ⟨s', hs'⟩, -⟩ := hw τ
  have e : ∀ i, (nu τ).w i = ((lam τ).natW i : ℤ) + lastEntry (nu τ) := fun i => by
    have hi := i.2
    have ha : 0 < a := by omega
    rw [GlobalTheory.JetDeg.natW_cast, lastEntry, DomWeight.detShift, DomWeight.detShift, dite_eq_left ha, dite_eq_left ha,
      Int.toNat_of_nonneg (h0 _), hs', hs']
    ring
  simp [e, Finset.sum_add_distrib, mul_comm]


omit [StarRing K] in
theorem map_jetMap_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ)
    (hJ : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    map σ (jetMap J (fun τ => lastEntry (nu τ)) P) = jetMap J' (fun τ => lastEntry (nu τ)) (map σ P) := by
  have hdet : ∀ τ : ι, map σ (frDet K a τ) = frDet ℂ a τ := fun τ => by
    rw [GlobalTheory.JetPoint.map_frDet, frDet]
    simp only [map_X]
  rw [GlobalTheory.GO.map_jetMap σ J J' 1 _ P fun μ hμ => by
    rw [one_mul]; exact hJ _ (degAt_eq lam nu lam' hw P hP μ hμ), one_smul]
  simp [jetMap, hdet]

end GlobalTheory.JetBase

theorem GlobalTheory.coefOpLe_jetOp_of_opNormSqLe : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  intro K _ _ _ σ ι _ a b lam nu lam' hw hK hC J J' hJ t ht x
  have h := ht ⟨MvPolynomial.map σ (x : Pol K ι a), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ lam' _ _ ?_) h
  rw [GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hC _ _ (Subtype.prop _)), GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hK _ _ x.2)]
  exact (GlobalTheory.JetBase.map_jetMap_eq σ lam nu lam' hw J J' hJ _ x.2).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def locSpan (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) : Submodule ℂ (GA E a → ℂ) :=
  sInf {V | F₀ ∈ V ∧ (∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V) ∧
    ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V}

variable {S : Finset (HeightOneSpectrum (𝓞 E))} {F₀ : GA E a → ℂ}

theorem self_mem_locSpan : F₀ ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun _ hV => hV.1

theorem rt_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {h : GA E a} (hh : h ∈ supS (E := E) (a := a) S) :
    (fun g => F (g * h)) ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.1 F (Submodule.mem_sInf.1 hF V hV) h hh

theorem kerInf_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.2 F (Submodule.mem_sInf.1 hF V hV) X ν k γ hk

theorem locSpan_le {V : Submodule ℂ (GA E a → ℂ)} (h₁ : F₀ ∈ V)
    (h₂ : ∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V)
    (h₃ : ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V) : locSpan S F₀ ≤ V :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem locSpan_le_rspan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ rspan π :=
  locSpan_le (mem_rspan hφ) (fun _ hF h _ => rt_mem_rspan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_rspan hF ν hk

theorem locSpan_le_mspanR {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ mspanR π := by
  rw [← rspan_eq_mspanR]; exact locSpan_le_rspan hφ

end GlobalTheory.JSW.MirSemi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapHalfRecNumsOfLogLevelPrimeLe
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

theorem lastSide_of_logT_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)),
    WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L →
    1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  intro CY CT N X Pr W pl u δ J _ eJ R hWT hS hSR hlogT hT hR
  obtain ⟨C, hC⟩ := GlobalTheory.BranchLogBound.orthNormLogBound
  have hW : W.Ok := hWT.1
  have hk := N.R.m_add_three_le_k
  have hm := N.R.two_le_m
  obtain ⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩ := hR.nums
  obtain ⟨-, -, -, -, -, hnodes, hcloud, -, hbT, hoff⟩ := id hSR
  have hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
    unfold NumDatum.Nm Ranks.N; push_cast; ring

  let lam1 : RPl N.R → ℝ := fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)
  let D0 : RPl N.R → ℝ := fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let D1 : RPl N.R → ℝ := fun z =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let logc : RPl N.R → ℝ := fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)
  let logxi : RPl N.R → ℝ := fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
  let bT : RPl N.R → ℝ := fun z => ((N.bT z.2 : ℚ) : ℝ)

  have hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e := fun z =>
    ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩
  have hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_first N δ z _)
  have hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_last N δ z _)
  have hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 -
      (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2) := by
    intro z
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))
    rw [hu0 z] at h
    push_cast at h
    show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _
    rw [h]; ring
  have hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B -
      ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta := by
    intro z
    push_cast
    have : ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) -
        ((N.R.t : ℝ) + 1) / 2 ≤ N.eta := by
      intro B hB
      rw [Finset.mem_range] at hB
      rw [RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]
      have h1 := hnodes z ⟨B, hB⟩ ⟨B, hB⟩
      have h2 := neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))
      push_cast at h1 h2
      have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0) := by
    intro z
    have h := castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))
    push_cast at h
    have hB := hsumB z
    push_cast at hB
    have hv0 := hcloud z ⟨0, by omega⟩
    rw [← (hrow z).1] at hv0
    have hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc := hv0.2
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _
    split_ifs with htop
    · obtain ⟨h1, h2⟩ := (hR.tops z).1 htop
      have hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 := by
        show ((N.bT z.2 : ℚ) : ℝ) = _
        obtain ⟨b, t⟩ := z
        simp only at h1
        subst h1
        unfold NumDatum.bT
        push_cast
        rfl
      rw [hbz, ← hul z]
      linarith
    · have hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩ := (hcloud z ⟨N.R.k - 2, by omega⟩).1
      obtain ⟨hlast, -, -⟩ := hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)
      have hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
        rw [hul z, hlast]; push_cast; ring
      have hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hzero
      rw [hl] at h
      linarith
  have hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta := by
    intro z
    have h := castQ (dOne_le_place W hW u (pl z))
    push_cast at h
    have hv0 := (hcloud z ⟨0, by omega⟩).2
    have hvk := (hcloud z ⟨N.R.k - 2, by omega⟩).1
    rw [← (hrow z).1] at hv0 hvk
    have hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hvk
    have hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast (W.hc u (pl z)).v_gt_u ⟨0, by omega⟩
    rw [RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)] at h
    have hg := (W.hc u (pl z)).gap_be ⟨0, by omega⟩
    have hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ) := by
      have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
      exact_mod_cast (by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)
    have hn := hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩
    rw [← (hrow z).2.1, ← (hrow z).2.2] at hn
    have hn' := neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))
    push_cast at hn hn'
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    have hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by omega : 1 ≤ N.R.m)
      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _

      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      nlinarith
    show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤
      3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta
    linarith
  refine ⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hI : (∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ)) ∧ ∀ τ, Br.SameShift (W.lamTrue u N.R.m τ) (W.sgTrue τ) :=
      ⟨fun τ => GlobalTheory.BranchMembers.interlace W hW u τ, fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hW u τ⟩
    have hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a := fun τ => hS.spread_le u N.R.m le_rfl τ
    obtain ⟨-, hlog, -⟩ := hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue
      hI.1 N.sc.a hsp
    have hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
        Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue) := rfl
    have h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩ := fun z =>
      ext_of _ ⟨0, _⟩
    have hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z) := by
      rw [Int.cast_sum, ← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [nBr_eq_sub (N_m_succ N.R)]
      show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) -
        ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
      rw [h0]
      push_cast
      rfl
    have hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) *
          ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) +
          ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) =
        ∑ z, (2 * logc z + logxi z) := by
      rw [← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) *
        Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
      rw [hNn, ha]
      unfold NumDatum.Nm
      ring
    show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)
    rw [hA, hn, hR.logT, ← Finset.sum_mul, ← hre]
    linarith
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hlam1, hR.aT t h2, hNn, hkR, hNq]
    unfold NumDatum.aT
    push_cast
    ring
  · intro z hz
    obtain ⟨-, hS1, -⟩ := hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)
    have hv := (hcloud z ⟨0, by omega⟩).1
    have hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hv
    rw [hlam1, hSc, hNn, hNq]
    push_cast at hS1
    linarith
  · intro z
    rw [hSc, hmR, hη]
    exact hD0 z
  · intro z
    rw [hSc, hη]
    exact hD1 z
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hb']
    exact (hbT t h2).2
  · rw [hR.logT]
    exact Real.log_nonneg (by exact_mod_cast hT)
  · rw [hR.logT, hmR, hL]
    exact hlogT

end GlobalTheory.ColRows.LastSideProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConjStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ ε : AF F, ε * ε = ε → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → ∀ c c' : DA F a b, c * c' = 1 → c' * c = 1 → c * g * c' ∈ closure (H0 (a := a) (b := b) ε) → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | exact GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | (intros; apply GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent <;> assumption)
end

