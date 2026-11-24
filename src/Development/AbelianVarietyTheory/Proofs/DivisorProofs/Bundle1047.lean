module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicType
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.ZDecay

theorem eq_zero_of_le_div {x K T : ℝ} (hx : 0 ≤ x) (h : ∀ t : ℝ, T ≤ t → 0 ≤ t → x * (1 + t) ≤ K) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have h1 := h (max (max T 0) (K / x)) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have h2 : K / x ≤ max (max T 0) (K / x) := le_max_right _ _
  have h3 : x * (K / x) = K := mul_div_cancel₀ _ hne
  nlinarith

theorem holFn_eq_zero {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    {w : ι → Fin n → ℤ} (hx : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {e : ι → Fin n → ℂ}
    (he : ∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f)
    (hinv : ∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, m * u ∈ UG Hm ∧ f (m * u) = f u)
    (hdec : ∀ k : ℕ, ∃ K : ℝ, ∀ u ∈ UG Hm, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((u τ)⁻¹.mulVec (e τ)) i‖ ≤ δ) →
      ‖f u‖ ≤ K * δ ^ k) :
    ∀ u ∈ UG Hm, f u = 0 := by
  intro u hu
  obtain ⟨P, hP, hfP⟩ := hf
  have hflow := GlobalTheory.HolDict.flowInv n ι Hm q x₀ w hx P e he hP (fun m hm v hv => by
    obtain ⟨h1, h2⟩ := hinv m hm v hv
    rw [hfP _ h1, hfP _ hv] at h2
    exact h2) u hu
  choose C A hCA using fun τ => GlobalTheory.HolDict.FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hx τ) (w τ) (e τ) (he τ) (u τ) (hu τ)
  have hC0 : ∀ τ, 0 ≤ C τ := fun τ => by
    obtain ⟨u', -, b, -, -, h, -⟩ := hCA τ 0 le_rfl
    have := (norm_nonneg _).trans h
    simpa using this
  obtain ⟨K, hK⟩ := hdec (2 * (∑ τ, A τ + 1))
  obtain ⟨-, -, hst, hbase⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ hx
  set C' : ℝ := ∑ τ, C τ + 1 with hC'
  have hCs : 0 ≤ ∑ τ, C τ := Finset.sum_nonneg fun τ _ => hC0 τ
  have hC'pos : 0 < C' := by linarith
  have hCle : ∀ τ, C τ ≤ C' := fun τ => by
    have := Finset.single_le_sum (f := C) (fun τ _ => hC0 τ) (Finset.mem_univ τ)
    linarith
  rw [← norm_eq_zero]
  refine eq_zero_of_le_div (K := (∏ τ, C τ) * K * C' ^ (∑ τ, A τ + 1)) (T := C') (norm_nonneg _) fun t hT ht => ?_
  choose u' hu' b hb hdecomp hchi hshort using fun τ => hCA τ t ht
  have ht1 : 0 < 1 + t := by linarith
  have hone : ∀ _ : ι, UpT (1 : Mt n) := fun _ => ⟨by simp, fun a c hc => Matrix.one_apply_ne hc.ne'⟩
  have hmem : (fun τ => (u' τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
    have := hst u' hu' (fun _ => 1) hone _ hbase
    simp only [Matrix.mul_one] at this
    exact this
  have h1 : f u = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u' := by
    rw [hfP u hu, ← hflow t ht, hfP u' hu', ← hP.2 _ hmem b hb]
    congr 1
    funext τ
    exact hdecomp τ
  have hq : 0 < C' / (1 + t) := div_pos hC'pos ht1
  have h2 := hK u' hu' (Real.sqrt (C' / (1 + t))) (Real.sqrt_pos.2 hq)
    (Real.sqrt_le_one.2 ((div_le_one ht1).2 (by linarith))) fun τ i =>
      Real.le_sqrt_of_sq_le ((le_div_iff₀ ht1).2 ((hshort τ i).trans (hCle τ)))
  rw [pow_mul, Real.sq_sqrt hq.le] at h2
  have h3 : ‖∏ τ, ∏ a, b τ a a ^ w τ a‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => hchi τ
  have h4 : ‖f u‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) * (K * (C' / (1 + t)) ^ (∑ τ, A τ + 1)) := by
    rw [h1, norm_mul]
    exact mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  refine (mul_le_mul_of_nonneg_right h4 ht1.le).trans_eq ?_
  rw [div_pow, pow_succ (1 + t)]
  field_simp

theorem setIntegral_translate {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (hc : ∀ a b : G, a * b = b * a) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ z, F (γ * z) = F z) (z₀ : G) :
    ∫ z in 𝓕, F (z₀ * z) ∂μ = ∫ z in 𝓕, F z ∂μ := by
  have : SMulCommClass G Γ G := ⟨fun a γ z => by
    change a * ((γ : G) * z) = γ * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  have h2 := h𝓕.smul_of_comm z₀
  rw [h𝓕.setIntegral_eq h2 fun γ z => hF γ γ.2 z]
  exact ((measurePreserving_mul_left μ z₀).setIntegral_image_emb (measurableEmbedding_mulLeft z₀) F 𝓕).symm

theorem iso_tau {D : D7} {V : HSp D} {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (ξ i)) ⬝ᵥ (gramAt D V τ).mulVec (fun i => tauE D τ (ξ i)) = 0 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h := congrArg (tauE D τ) hξ.2
  rw [map_zero] at h
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, gramAt, Matrix.map_apply, Pi.star_apply]

theorem zCusp_of_rapidDecay : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  intro D θ V S M w hθ hM φ haut hhol hdec ξ hξ μ 𝓕 hμ h𝓕 g
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace (fun x => x ∈ (ZI V ξ : Set (GA D V)))
  have : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ V).subgroupOf (ZI V ξ) => (⟨γ.1.1, γ.2⟩ : GQ V))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  obtain ⟨L, hL, hLmul, -, hUG, hLa, -, hsplit, hcomm, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨⟨ε, -⟩, -, -, hlift, -⟩ := _root_.GlobalTheory.HolDict.TransvGroup.transvection_group D θ V hθ ξ hξ
  have hfin := ((_root_.GlobalTheory.TransvMeasure.transvection_measure D θ V hθ ξ hξ).2.1 μ 𝓕 hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have hc : ∀ a b : ZI V ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨a, ha, u, hu, rfl⟩ := hsplit g
  have hx : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hM).1
  obtain ⟨B, hB⟩ := hdec.bounded
  have hf : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w
      fun v => ∫ z in 𝓕, φ ((z : GA D V) * a * L v) ∂μ := by
    refine _root_.GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hx (ZI V ξ) (μ.restrict 𝓕) (fun z v => φ ((z : GA D V) * a * L v)) B
      (fun z => ?_) (fun z v _ => hB _) fun v _ => ?_
    · obtain ⟨f, ⟨P, hP, hfP⟩, hφf⟩ := hhol ((z : GA D V) * a)
      refine ⟨P, hP, fun v hv => ?_⟩
      beta_reduce
      rw [hφf _ (hL v hv).1, ← hfP v hv]
      congr 1
      funext τ
      exact (hL v hv).2 τ
    · exact (haut.cont.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)).measurable.aestronglyMeasurable
  have key := holFn_eq_zero hx (iso_tau hξ) hf (fun m hm v hv => ?_) (fun k => ?_) _ (hUG u)
  · simp only [hLa u hu, mul_assoc] at key
    exact key
  · obtain ⟨z₀, hz₀, hz₁, hz₂⟩ := hlift m hm
    have hm' : m = fun τ => archM V (θ τ) z₀ := funext fun τ => (hz₂ τ).symm
    have hmU : m ∈ UG (gramAt D V) := hm' ▸ hUG z₀
    have hLm : L m = z₀ := by rw [hm']; exact hLa z₀ hz₁
    refine ⟨fun τ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hmU τ) (hv τ), ?_⟩
    rw [← setIntegral_translate hc _ μ h𝓕 (fun z => φ ((z : GA D V) * a * L v)) (fun γ hγ z => ?_) ⟨z₀, hz₀⟩]
    · refine integral_congr_ae (.of_forall fun z => ?_)
      have h1 := congrArg Subtype.val (hc ⟨z₀, hz₀⟩ z)
      simp only [Subgroup.coe_mul] at h1 ⊢
      rw [hLmul m hmU v hv, hLm, h1, mul_assoc (z : GA D V) z₀, ← hcomm a ha z₀ hz₁]
      simp only [mul_assoc]
    · simp only [Subgroup.coe_mul, mul_assoc]
      exact haut.left _ hγ _
  · obtain ⟨c, N, hc0, hh⟩ := _root_.GlobalTheory.HolDict.quotHeight_lower_bound D θ V hθ ξ hξ a ha
    obtain ⟨C, hC⟩ := hdec (N * k)
    refine ⟨C / c ^ k * (μ.restrict 𝓕).real Set.univ, fun v hv δ h0 h1 hs => ?_⟩
    rw [mul_right_comm]
    refine norm_integral_le_of_norm_le_const (.of_forall fun z => ?_)
    have h2 := hh z z.2 (L v) (hL v hv).1 δ h0 h1 fun τ i => by rw [(hL v hv).2 τ]; exact hs τ i
    have h3 := pow_le_pow_left₀ hc0.le h2 k
    rw [mul_pow, ← pow_mul] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 k)]
    calc _ ≤ ‖φ ((z : GA D V) * a * L v)‖ * (δ ^ k * _) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (‖φ ((z : GA D V) * a * L v)‖ * _) * δ ^ k := by rw [mul_comm (δ ^ k), ← mul_assoc]
      _ ≤ C * δ ^ k := mul_le_mul_of_nonneg_right (hC _) (pow_nonneg h0.le _)

end GlobalTheory.HolDict.ZDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwTrConjEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem twTr_conj_equiv : ∀ (G : Type) [Group G] (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : ρ.Equiv ρ') (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V), twTr ρ' K K' f (e.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ e.toLinearEquiv.symm.toLinearMap) = twTr ρ K K' f A := by
  intro G _ V V' _ _ _ _ ρ ρ' e K K' f A
  set φ := e.toLinearEquiv with hφ
  have hint : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa [hφ] using h
  have hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v')) := fun g v' => by
    rw [hint, φ.apply_symm_apply]
  have hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K' := by
    intro v'
    show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔
      (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    refine forall_congr' fun h => ?_
    rw [hint']
    constructor
    · intro H
      exact (φ.symm_apply_eq.2 H.symm).symm
    · intro H
      rw [H, φ.apply_symm_apply]
  have hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A) := by
    have hs := (φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))
    unfold levOp
    rw [map_smul]
    congr 1
    refine Eq.trans ?_ hs.symm
    congr 1
    funext q
    ext v'
    simp [LinearEquiv.conj_apply, hint']
  have hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hA]
  have hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K' := by
    ext v'
    rw [Submodule.mem_map_equiv, hmem]
  set L := levOp ρ K K' f A with hL
  have hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K') := by
    constructor
    · intro H v hv
      have h1 : φ v ∈ fixed ρ' K' := (hmem _).2 (by simpa using hv)
      have h2 := (hmem _).1 (H _ h1)
      simpa [LinearEquiv.conj_apply] using h2
    · intro H v' hv'
      rw [hmem]
      simpa [LinearEquiv.conj_apply] using H _ ((hmem _).1 hv')
  unfold twTr
  simp only [hlev]
  by_cases h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'
  · rw [dite_eq_left (hc.2 h), dite_eq_left h]
    let ψ := φ.ofSubmodules _ _ hmap
    have hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h) := by
      ext ⟨v', hv'⟩
      simp [ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]
    rw [hr, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hc.1 h), dite_eq_right h]

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormConjHermitianTripleRegul
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.NrmUnique

theorem phi_surj_commutant : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r), Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := GlobalTheory.T.exists_matrixAdjoinTensorUnramified_of_commute_separable

theorem phi_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) := GlobalTheory.T.matrixAdjoinTensorUnramifiedToMatrix_injective

theorem hilbert_ninety_gl1 : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified

theorem map_nrmG {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (a : H) : f (nrmG θ r a) = nrmG θ' r (f a) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact Function.Semiconj.iterate_right (f := f) hf i a

theorem nrmG_mul {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact iterate_map_mul θ i a b

theorem nrmG_inv {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a : H) :
    nrmG θ r a⁻¹ = (nrmG θ r a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← nrmG_mul, inv_mul_cancel]
  simp [nrmG, iterate_map_one]

theorem gl_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem twConj_place (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (n : ℕ) (γ : GL (Fin n) K) (hγ : γ.val.charpoly.Separable)
    (δ δ' : GL (Fin n) (KQ p K r))
    (hc : Commute δ.val (γ.val.map (inclK p K r))) (hc' : Commute δ'.val (γ.val.map (inclK p K r)))
    (hN : nrmG (sigRes p K n r) r δ = nrmG (sigRes p K n r) r δ') :
    ∃ h : GL (Fin n) (KQ p K r), δ' = h⁻¹ * δ * sigRes p K n r h ∧
      ∀ y : GL (Fin n) K, Commute y.val γ.val → Commute h.val (y.val.map (inclK p K r)) := by
  have hinj := phi_injective p K n r γ.val hr
  have lift : ∀ d : GL (Fin n) (KQ p K r), Commute d.val (γ.val.map (inclK p K r)) →
      ∃ u : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ,
        GlobalTheory.PolyTensor.phi p K n γ.val r u = d.val := by
    intro d hd
    obtain ⟨x, hx⟩ := phi_surj_commutant p K n r γ.val hr hγ d.val hd
    obtain ⟨x', hx'⟩ := phi_surj_commutant p K n r γ.val hr hγ (d⁻¹).val (Commute.units_inv_left hd)
    have h1 : x * x' = 1 := hinj (by rw [map_mul, map_one, hx, hx']; exact d.mul_inv)
    exact ⟨⟨x, x', h1, by rw [mul_comm]; exact h1⟩, hx⟩
  obtain ⟨u, hu⟩ := lift δ hc
  obtain ⟨u', hu'⟩ := lift δ' hc'
  let Φ : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ →* GL (Fin n) (KQ p K r) :=
    Units.map (GlobalTheory.PolyTensor.phi p K n γ.val r).toMonoidHom
  let τ : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ →* (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ :=
    Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] (GlobalTheory.PolyTensor.PolyAlg p K n γ.val)) (frobQ p r)).toRingHom.toMonoidHom
  have hΦ : ∀ a, Φ (τ a) = sigRes p K n r (Φ a) := fun a =>
    Units.ext (GlobalTheory.PolyTensor.phi_tw p K n γ.val r a)
  have hΦinj : Function.Injective Φ := fun a b h => Units.ext (hinj (congrArg Units.val h))
  have hδ : Φ u = δ := Units.ext hu
  have hδ' : Φ u' = δ' := Units.ext hu'
  have hNu : nrmG τ r u = nrmG τ r u' :=
    hΦinj (by rw [map_nrmG τ _ Φ hΦ, map_nrmG τ _ Φ hΦ, hδ, hδ', hN])
  have hn1 : nrmG τ r (u' * u⁻¹) = 1 := by rw [nrmG_mul, nrmG_inv, hNu, mul_inv_cancel]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr p r hr (GlobalTheory.PolyTensor.PolyAlg p K n γ.val) (u' * u⁻¹) hn1
  have hu'g : u' = g⁻¹ * u * τ g := by
    calc u' = (u' * u⁻¹) * u := by group
      _ = g⁻¹ * τ g * u := by rw [hg]
      _ = g⁻¹ * u * τ g := by rw [mul_assoc, mul_comm (τ g) u, ← mul_assoc]
  refine ⟨Φ g, ?_, fun y hy => ?_⟩
  · rw [← hδ', ← hδ, hu'g, map_mul, map_mul, map_inv, hΦ]
  · exact (GlobalTheory.PolyTensor.phi_commute p K n γ.val r y.val hy (g : _)).symm

theorem nrm_unique : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z δ' z' : Gr G r), 0 < r →
    regular₂ G γ → IsNrm G r γ δ z → IsNrm G r γ δ' z' → ∃ g : Gr G r, δ' = g⁻¹ * δ * sigG G r g ∧
      ∀ y ∈ Subgroup.centralizer {γ}, carry G r z' y = g⁻¹ * carry G r z y * g := by
  intro p _ G r γ δ z δ' z' hr hreg h h'
  obtain ⟨hex, -⟩ := GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G
  obtain ⟨hit, hfix, -, -⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  set d := z * δ * (sigG G r z)⁻¹ with hd
  set d' := z' * δ' * (sigG G r z')⁻¹ with hd'
  have hN : nrmG (sigG G r) r d = inclG G r γ := by
    have := hex r γ δ z hr h
    simpa [IsNrm] using this
  have hN' : nrmG (sigG G r) r d' = inclG G r γ := by
    have := hex r γ δ' z' hr h'
    simpa [IsNrm] using this
  have comm : ∀ e, nrmG (sigG G r) r e = inclG G r γ → e * inclG G r γ = inclG G r γ * e := by
    intro e he
    have := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r e 1).2
    rw [he, hfix, hit] at this
    exact this
  have hc := comm d hN
  have hc' := comm d' hN'
  have key : ∀ (w : Fin G.m) (e : Gr G r),
      (nrmG (sigG G r) r e).2 w = nrmG (sigRes p (G.Fw w) G.n r) r (e.2 w) := fun w e =>
    map_nrmG (sigG G r) (sigRes p (G.Fw w) G.n r) ((Pi.evalMonoidHom _ w).comp (MonoidHom.snd _ _))
      (fun _ => rfl) r e
  have key1 : ∀ e : Gr G r, (nrmG (sigG G r) r e).1 = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r e.1 := fun e =>
    map_nrmG (sigG G r) (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (MonoidHom.fst _ _) (fun _ => rfl) r e
  have hNw : ∀ w, nrmG (sigRes p (G.Fw w) G.n r) r (d.2 w) = nrmG (sigRes p (G.Fw w) G.n r) r (d'.2 w) :=
    fun w => by rw [← key, ← key, hN, hN']
  have hN1 : nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r d.1 = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r d'.1 := by
    rw [← key1, ← key1, hN, hN']
  have hcw : ∀ (e : Gr G r), e * inclG G r γ = inclG G r γ * e →
      ∀ w, Commute (e.2 w).val ((γ.2 w).val.map (inclK p (G.Fw w) r)) := by
    intro e he w
    have := congrArg (fun x : Gr G r => (x.2 w).val) he
    exact this
  choose H hH hHc using fun w => twConj_place p r hr (G.Fw w) G.n (γ.2 w) (hreg w) (d.2 w) (d'.2 w)
    (hcw d hc w) (hcw d' hc' w) (hNw w)
  obtain ⟨h0, hh0⟩ := hilbert_ninety_gl1 p r hr d.1 d'.1 hN1
  let hh : Gr G r := (h0, H)
  have hdd : d' = hh⁻¹ * d * sigG G r hh := Prod.ext hh0 (funext hH)
  have hcomm : ∀ y ∈ Subgroup.centralizer {γ}, hh * inclG G r y = inclG G r y * hh := by
    intro y hy
    have hy' : γ * y = y * γ := Subgroup.mem_centralizer_iff.1 hy γ rfl
    refine Prod.ext (gl_one_mul_comm _ _) (funext fun w => ?_)
    have hyw : Commute (y.2 w).val (γ.2 w).val := by
      have := congrArg (fun x : Gp G => (x.2 w).val) hy'
      exact this.symm
    exact Units.ext (hHc w (y.2 w) hyw)
  refine ⟨z⁻¹ * hh * z', ?_, fun y hy => ?_⟩
  · have e1 : δ' = z'⁻¹ * d' * sigG G r z' := by rw [hd']; group
    rw [e1, hdd, hd]
    simp only [map_mul, map_inv]
    group
  · have h2 : hh⁻¹ * inclG G r y * hh = inclG G r y := by
      rw [mul_assoc, ← hcomm y hy, inv_mul_cancel_left]
    simp only [carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (z⁻¹ * hh * z')⁻¹ * (z⁻¹ * inclG G r y * z) * (z⁻¹ * hh * z') =
      z'⁻¹ * (hh⁻¹ * inclG G r y * hh) * z' by group, h2]

end GlobalTheory.NrmUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrders
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPartsF

theorem exists_real_finite_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J) :
    ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y : AEF F E, infPartF F E x = infPartF F E y → finPartF F E x = finPartF F E y → x = y :=
    fun x y h1 h2 => GlobalTheory.AdelicOrbit.parts_inj x y h1 h2
  have hs : ∀ a b, ∃ x : AEF F E, infPartF F E x = a ∧ finPartF F E x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  set g : GL (Fin n) (AEF F E) := matHomF σ J p with hg
  have hgm : g ∈ HR (AF F) σ J := p.2
  have hparts := (GlobalTheory.AdelicOrbit.mem_parts σ J g).1 hgm
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs (Formalism.UG.bc (infPartF F E) g) 1
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs 1 (Formalism.UG.bc (finPartF F E) g)
  have ha : a ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J a).2 ⟨a1 ▸ hparts.1, a2 ▸ one_mem _⟩
  have hk : k ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J k).2 ⟨k1 ▸ one_mem _, k2 ▸ hparts.2⟩
  refine ⟨⟨a, ha⟩, ?_, ⟨k, hk⟩, ?_, ?_, ?_⟩
  · exact MonoidHom.mem_ker.2 a2
  · exact MonoidHom.mem_ker.2 k1
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (a * k)
      rw [map_mul, a1, k1, mul_one]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (a * k)
      rw [map_mul, a2, k2, one_mul]
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (k * a)
      rw [map_mul, a1, k1, one_mul]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (k * a)
      rw [map_mul, a2, k2, mul_one]

end GlobalTheory.WeilPartsF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpanStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
end

