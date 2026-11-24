module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.Bundle0001
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMatrixMetricMeans
section
open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

section Mat
open scoped Matrix.Norms.L2Operator

end Mat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem meanInf_eq [_root_.NumberField.IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_const [_root_.NumberField.IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp


end GlobalTheory.Proof.DualMatrixMetricMeans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteQuotient

theorem exists_bound_unitary {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨B, rfl⟩ := hB
  refine ⟨∑ i, ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖, fun g hg i j => ?_⟩
  have hu : B.1 * g * (B⁻¹).1 ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have : star (B.1 * g * (B⁻¹).1) * (B.1 * g * (B⁻¹).1) =
        star (B⁻¹).1 * (gᴴ * (star B.1 * B.1) * g) * (B⁻¹).1 := by
      simp only [star_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [this, hg, ← Matrix.mul_assoc, ← star_mul, Units.mul_inv, star_one, Matrix.one_mul, Units.mul_inv]
  have e : g = (B⁻¹).1 * (B.1 * g * (B⁻¹).1) * B.1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have h1 : ‖g i j‖ ≤ ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖ := by
    generalize B.1 * g * (B⁻¹).1 = u at hu e
    rw [e, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
      (entry_norm_bound_of_unitary hu k l)) (norm_nonneg _)
  refine h1.trans ?_
  refine (Finset.single_le_sum (f := fun j => ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem posDef_of_signature {n p : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq p 0 = 1 := by
    ext (i | i) (j | j)
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have h2 : (star P.1 * G.reindex e e * P.1).PosDef := by
    have : star P.1 * G.reindex e e * P.1 = 1 := hP.trans h1
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

variable {D : D7}

theorem gram_hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), GlobalTheory.StabCompact.det_gram_ne_zero V⟩

theorem cmExt (D : D7) : IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

theorem isTotDef_of_posDef (V : HSp D) (h : ∀ τ, (gramAt D V τ).PosDef) : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := by
  refine ⟨D.sp.cm.totReal, fun ι => Or.inl fun x hx => ?_⟩
  have hτ := (cmExt D).2.2.2
  obtain ⟨τ, hι⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 (InfinitePlace.mk (Complex.ofRealHom.comp ι))
  have hι' : (tauE D τ).comp (algebraMap D.host.F D.host.E) = Complex.ofRealHom.comp ι := by
    rcases InfinitePlace.mk_eq_iff.1 hι with h1 | h1
    · exact h1
    · ext a
      have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 a)
      simpa using this
  have hpos : 0 < tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x) := by
    have hx' : (fun i => tauE D τ (x i)) ≠ 0 := fun e => hx (funext fun i => (tauE D τ).injective (by
      simpa using congrFun e i))
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 (h τ)).2 hx'
    convert this using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, gramAt, Pi.star_apply,
      Matrix.map_apply, mul_assoc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hτ]; rfl
  obtain ⟨a, ha⟩ := (D.sp.cm.fixed (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)).1 (by
    apply (tauE D τ).injective
    refine (hτ (tauE D τ) _).trans ?_
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 hpos).2.symm)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at hpos
  have e : tauE D τ (algebraMap D.host.F D.host.E a) = (ι a : ℂ) := RingHom.congr_fun hι' a
  rw [e] at hpos
  exact_mod_cast hpos

theorem exists_compact : ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  intro D V hV
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (cmExt D) (gram_hermND V) (isTotDef_of_posDef V hV)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_unitary (hV τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group


open MeasureTheory in
theorem integrableOn_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))),
    IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)),
    (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) →
    ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ →
    ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ := by
  intro D ψ _ S T χS χT om hom hS X _ _ _ L hL F hF hinv μ 𝓕 hμ h𝓕 h
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  obtain ⟨C, hC, hcov⟩ := exists_compact S hS
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D S) (GQ S) C hC (fun g => ?_) μ hμ 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · let b := Module.finBasis ℂ X
    have e : (fun g => thetaKO om g h (L (F g))) =
        fun g => ∑ k, b.coord k (F g) * om (g, h) (L (b k)) 0 := by
      funext g
      conv_lhs => rw [← b.sum_repr (F g)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp hF
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_id.prodMk continuous_const)
  · intro γ hγ g
    have e : (γ * g, h) = ((γ, 1) : GA D S × GA D T) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))

end GlobalTheory.DefiniteQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem image_inf_le (a b : L.ι) : f ''ᵁ L.U a ⊓ f ''ᵁ L.U b ≤ f ''ᵁ (L.U a ⊓ L.U b) := fun x hx ↦ by
  obtain ⟨w, hw, rfl⟩ := hx.1
  exact f.apply_mem_image_iff.2 ⟨hw, f.apply_mem_image_iff.1 hx.2⟩

def extLB : LB X :=
  ⟨L.ι, fun a ↦ f ''ᵁ L.U a, fun a b ↦ res (image_inf_le f L a b) (GlobalTheory.GlueLineBundle.imU f _ (L.g a b))⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (a b : L.ι) (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gm (r ≫ f) z ((extLB f L).U a ⊓ (extLB f L).U b) ((extLB f L).g a b) = gm r z (L.U a ⊓ L.U b) (L.g a b) := by
  have hm : (r ≫ f) z ∈ f ''ᵁ L.U a ⊓ f ''ᵁ L.U b := ⟨f.apply_mem_image_iff.2 ha, f.apply_mem_image_iff.2 hb⟩
  exact (gm_res (r ≫ f) z (image_inf_le f L a b) hm _).trans
    (GlobalTheory.GlueLineBundle.gm_imU f r z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)


variable {f} in
theorem gm_eq_map {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (U : X.Opens) (h : g y ∈ U) (a : Γ(X, U)ˣ) :
    gm g y U a = Units.map (g.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (g y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val g y U h, GlobalTheory.GlueLineBundle.gm_id_val h]
  exact (Scheme.Hom.germ_stalkMap_apply g U y h a.val).symm

end GlobalTheory.PicGlue.OpenExt

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem isOn_extLB (hL : L.IsLB) : IsOn f.opensRange (extLB f L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨w, -, rfl⟩ := hx
    exact ⟨w, rfl⟩
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_chart hL w
    exact ⟨a, f.apply_mem_image_iff.2 ha⟩
  · intro x a b c hxa hxb hxc
    obtain ⟨w, ha, rfl⟩ := hxa
    have hb : w ∈ L.U b := f.apply_mem_image_iff.1 hxb
    have hc : w ∈ L.U c := f.apply_mem_image_iff.1 hxc
    have e : ∀ (d d' : L.ι) (hd : w ∈ L.U d) (hd' : w ∈ L.U d'),
        Units.map (f.stalkMap w).hom.toMonoidHom (gm (𝟙 X) (f w) _ ((extLB f L).g d d')) =
          gm (𝟙 X') w (L.U d ⊓ L.U d') (L.g d d') := by
      intro d d' hd hd'
      rw [← gm_eq_map f w ((extLB f L).U d ⊓ (extLB f L).U d') ⟨f.apply_mem_image_iff.2 hd, f.apply_mem_image_iff.2 hd'⟩]
      have k := gm_ext_g f L (𝟙 X') w d d' hd hd'
      rwa [Category.id_comp] at k
    apply Units.map_injective (f := (f.stalkMap w).hom.toMonoidHom)
      (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (f.stalkMap w)).1 h)
    refine (MonoidHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (e a b ha hb) (e b c hb hc)).trans
      ((gm_cocycle hL (𝟙 X') w ha hb hc).trans (e a c ha hc).symm)

end GlobalTheory.PicGlue.OpenExt


open GlobalTheory.PicGlue.OpenExt in
theorem GlobalTheory.PicGlue.exists_isOn_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'),
    L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  intro X X' f _ L hL
  refine ⟨extLB f L, isOn_extLB f L hL, iso_of_chart hL ⟨fun J ↦ J PUnit.unit, ?_, ?_⟩⟩
  · intro J y hy
    exact f.apply_mem_image_iff.1 (mem_pull.1 hy)
  · intro y J J' hj hj'
    exact (gm_pull_g (extLB f L) f (𝟙 X') y J J' hj hj').trans
      (gm_ext_g f L (𝟙 X') y _ _ (f.apply_mem_image_iff.1 (mem_pull.1 hj)) (f.apply_mem_image_iff.1 (mem_pull.1 hj')))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexAbelianVarietySectionRatioAffineCov
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioCover

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r := by
  intro A _ g L u hA
  haveI := hA.comm
  obtain ⟨H, _, m, s, hv⟩ := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA
  refine ⟨m + 1, fun k => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k),
    fun k j => GlobalTheory.ProjSpace.secRatio (s k) (s j), fun k => (hv.2 k).1, hv.1,
    fun k j => GlobalTheory.ProjSpace.basicOpen_secRatio _ _, fun k => GlobalTheory.ProjSpace.secRatio_self _, ?_⟩
  intro k j l z hk hj
  have hkj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s j)) :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hk, hj⟩
  have e := congrArg (valAt' (u.ex z).left _)
    (GlobalTheory.ProjSpace.secRatio_mul_secRatio (s k) (s j) (s l) (inf_le_left) (inf_le_right))
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj] at e
  exact e.symm

end GlobalTheory.RatioCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexBaseChangePolarizedAbelianFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_isBC : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g),
    ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  intro O _ g R _ σ Λ F
  let f : pullback F.s (spMap σ) ⟶ F.X := pullback.fst _ _
  let A' : Over (pullback F.s (spMap σ)) := (Over.pullback f).obj F.A
  letI : GrpObj A' := Functor.grpObjObj
  have hP : IsGrpPullback A' F.A f (pullback.fst F.A.hom f) := isGrpPullback_pullback F.A f
  haveI : IsCommMonObj A' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hP
  obtain ⟨act', ⟨hh, h1, hm, ha⟩, hc⟩ := GlobalTheory.ActPull.exists_act_pull _ _ f F.A A' _ hP Oᵐᵒᵖ
    (fun a => F.act a.unop) (fun a => F.hom _) F.act_one (fun a b => F.act_mul b.unop a.unop)
    (fun a b => F.act_add _ _)
  have hLB := LB.isLB_pull F.isLB (pullback.fst F.A.hom f)
  have hpol := GlobalTheory.pol_pull _ _ F.A A' f _ F.L (F.L.pull _) F.isLB hLB F.ab hP (GlobalTheory.PolBaseChange.lbIso_refl hLB)
  have hdim : SmoothOfRelativeDimension g A'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hP.1 F.dim
  let eta' : Λ → (𝟙_ (Over (pullback F.s (spMap σ))) ⟶ A') := fun a =>
    Over.homMk (hP.1.lift (f ≫ (F.eta a).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; simp)) (hP.1.lift_snd _ _ _)
  refine ⟨Fam.mk (pullback F.s (spMap σ)) (pullback.snd _ _) A' hpol.1 hdim (fun a => act' (MulOpposite.op a))
    (fun a => hh _) h1 (fun a b => by rw [MulOpposite.op_mul]; exact hm _ _)
    (fun a b => by rw [MulOpposite.op_add]; exact ha _ _)
    (F.L.pull (pullback.fst F.A.hom f)) hLB (hpol.2.1 F.ample) eta',
    f, pullback.fst F.A.hom f, IsPullback.of_hasPullback _ _, hP, fun a => hc _,
    GlobalTheory.PolBaseChange.lbIso_refl hLB, fun a => hP.1.lift_fst _ _ _⟩

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminantStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cube_valuation_eq_discriminant : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  first | exact @GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | exact GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | (intros; apply GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPointThrough
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_geomPoint_through : ∀ (T : Scheme.{0}) (p : T), ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Sp K ⟶ T), p ∈ Set.range s := by
  intro T p
  refine ⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p))) := inferInstance
  refine ⟨x, ?_⟩
  show (T.fromSpecResidueField p).base _ = p
  exact Scheme.fromSpecResidueField_apply p _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

namespace GlobalTheory

theorem exists_holUnif_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  intro A _ g e Λ he hd hf hk
  refine ⟨⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩,
    { ex := e
      ex_add := he.1
      ex_onto := he.2.1
      Λ := Λ
      ker := hk
      discrete := hd
      full := hf
      hol := fun U f => by
        have h := he.2.2.1 U f
        simpa using h
      fr := fun _ _ => 1
      fr_hol := fun _ => differentiableOn_const _
      fr_ne := fun _ _ _ => one_ne_zero
      fr_compat := fun i j z h => by
        show (1 : ℂ) = _
        exact ((_root_.mul_one _).trans (valAt'_one _ h)).symm }, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasisStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ, ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  first | exact @GlobalTheory.LBTrans.transition_units | exact GlobalTheory.LBTrans.transition_units | (intros; apply GlobalTheory.LBTrans.transition_units <;> assumption)
end

