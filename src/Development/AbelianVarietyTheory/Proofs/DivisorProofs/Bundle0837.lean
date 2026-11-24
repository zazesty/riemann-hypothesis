module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesgu
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem sectionsOn_res_pi_bijective_of_separating {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens)
    (hcov : support F ⊆ ⋃ i, (W i : Set X))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) :
    Function.Bijective
      (LinearMap.pi fun i => sectionsOn.res R F (le_top : W i ≤ ⊤) :
        sectionsOn F ⊤ →ₗ[R] ∀ i, sectionsOn F (W i)) := by
  classical
  refine ⟨?_, fun t => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    apply (sectionsOn.toΓ F ⊤).injective
    rw [map_zero]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    by_cases hxs : x ∈ support F
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hxs)
      have h0 : sectionsOn.res R F (le_top : W i ≤ ⊤) s = 0 := congrFun hs i
      have := congrArg (fun u => F.presheaf.germ (W i) x hi (sectionsOn.toΓ F (W i) u)) h0
      simp only [sectionsOn.toΓ_res, map_zero] at this
      rwa [F.presheaf.germ_res_apply] at this
    · exact (notMem_support_iff.1 hxs).elim _ _
  have key (i : ι) : ∃ s : sectionsOn F ⊤, sectionsOn.res R F (le_top : W i ≤ ⊤) s = t i ∧
      ∀ j, j ≠ i → sectionsOn.res R F (le_top : W j ≤ ⊤) s = 0 := by
    let C : X.Opens := ⟨(support F)ᶜ, (isClosed_support F).isOpen_compl⟩
    let V : X.Opens := (⨆ (j : ι) (_ : j ≠ i), W j) ⊔ C
    have hWV (j : ι) (hj : j ≠ i) : W j ≤ V :=
      le_sup_of_le_left (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => W j) j hj)
    have hcovV : (⊤ : X.Opens) ≤ W i ⊔ V := fun x _ => by
      by_cases hxs : x ∈ support F
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hxs)
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr (hWV j hji hj)
      · exact Or.inr (Or.inr hxs)
    have : Subsingleton Γ(F, W i ⊓ V) := subsingleton_sections_of_notMem_support fun y hy hys => by
      rcases hy.2 with hy' | hy'
      · obtain ⟨j, hj, hyj⟩ : ∃ j, j ≠ i ∧ y ∈ W j := by
          simpa [Opens.mem_iSup] using hy'
        exact hdisj i j (Ne.symm hj) y hys hy.1 hyj
      · exact hy' hys
    obtain ⟨s, h₁, h₂⟩ := Qcqs.exists_section_glue₂ F (V₁ := W i) (V₂ := V) (W := ⊤) le_top le_top
      hcovV (sectionsOn.toΓ F (W i) (t i)) 0 (Subsingleton.elim _ _)
    refine ⟨(sectionsOn.toΓ F ⊤).symm s, (sectionsOn.toΓ F (W i)).injective ?_, fun j hj =>
      (sectionsOn.toΓ F (W j)).injective ?_⟩
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply]
      exact h₁
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply, map_zero]
      have e := congrArg (F.presheaf.map (homOfLE (hWV j hj)).op) h₂
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
      exact e
  choose s h₁ h₂ using key
  refine ⟨∑ i, s i, funext fun j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.pi_apply, map_sum, Finset.sum_eq_single j (fun i _ hi => h₂ i j hi.symm) (by simp),
    h₁]

theorem length_sectionsOn_top_eq_sum_of_separating :
    ∀ {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F] (R : Type) [CommRing R]
      [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens),
      support F ⊆ ⋃ i, (W i : Set X) → (∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) →
      Module.length R (sectionsOn F ⊤) = ∑ i, Module.length R (sectionsOn F (W i)) := by
  intro X F _ R _ _ ι _ W hcov hdisj
  rw [(LinearEquiv.ofBijective _
    (sectionsOn_res_pi_bijective_of_separating F R W hcov hdisj)).length_eq,
    Module.length_pi_of_fintype]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAndIsPreconnected
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SpecialisationPts

open GlobalTheory.AffinePoints GlobalTheory.CxPts

theorem nonempty_point (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem specializes_iff_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x z : X}
    (hz : z ∈ U) : x ⤳ z ↔ ∀ f : Γ(X, U), z ∈ X.basicOpen f → x ∈ X.basicOpen f := by
  refine ⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩
  rw [specializes_iff_forall_open]
  intro s hs hzs
  obtain ⟨g, hg, hzg⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz
  exact hg (h g hzg)

theorem mem_basicOpen_iff_notMem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

theorem specializes_iff_ev {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {y : GlobalTheory.CxPts p (RingHom.id ℂ)} (hy : y ∈ ptsIn p (RingHom.id ℂ) U) :
    x ⤳ y.1 (IsLocalRing.closedPoint ℂ) ↔
      ∀ f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal, ev p (RingHom.id ℂ) U f y = 0 := by
  rw [specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]
  refine forall_congr' fun f => ?_
  rw [mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]
  exact not_imp_not

theorem nonempty_and_isPreconnected : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), LocallyOfFiniteType p →
    ∀ (U : X.Opens), IsAffineOpen U → ∀ x ∈ U,
    (∃ y : GlobalTheory.CxPts p (RingHom.id ℂ), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧
      x ⤳ y.1 (IsLocalRing.closedPoint ℂ)) ∧
    _root_.IsPreconnected {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
  intro X p hp U hU x hx
  let : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType ℂ Γ(X, U) := hft
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : P.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ) :=
    ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom
      fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a
  have hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f) :=
    ev_ofHom _ _ _ f
  have hc : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem)
        fun f => ?_)
    have h := (continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ
    simp only [← hev] at h
    exact h
  have hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩
      rw [hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · rintro ⟨hy, hxy⟩
      have hy' := mem_ptsIn.2 hy
      let ψ : Γ(X, U) →ₐ[ℂ] ℂ :=
        { evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }
      refine ⟨Ideal.Quotient.liftₐ P ψ fun f hf =>
        (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩
      refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)
      exact (hev _ f).trans (ev_eq hy' f).symm
  constructor
  · obtain ⟨φ⟩ := nonempty_point (Γ(X, U) ⧸ P)
    have h := Set.mem_range_self (f := Φ) φ
    rw [hr] at h
    exact ⟨_, h⟩
  · have := GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)
    rw [← hr]
    exact isPreconnected_range hc

end GlobalTheory.SpecialisationPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CMVal.NormConj

theorem norm_sigma_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] (σ : ℂ ≃+* ℂ) (φ : E →+* ℂ) (α : Eˣ) :
    ‖σ (φ (α : E) / starRingEnd ℂ (φ (α : E)))‖ = 1 := by
  rw [← IsCMField.complexEmbedding_complexConj, map_div₀]
  have e2 : σ (φ (IsCMField.complexConj E (α : E))) = starRingEnd ℂ (((σ : ℂ →+* ℂ).comp φ) (α : E)) := by
    rw [← IsCMField.complexEmbedding_complexConj]; rfl
  have e1 : σ (φ (α : E)) = ((σ : ℂ →+* ℂ).comp φ) (α : E) := rfl
  have h0 : ((σ : ℂ →+* ℂ).comp φ) (α : E) ≠ 0 := by simp
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

end GlobalTheory.CMVal.NormConj


open GlobalTheory.CMVal.NormConj in
theorem GlobalTheory.CMVal.norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E)
    (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ),
    ‖σ (finPart χ y : ℂ)‖ = 1 := by
  intro E _ _ _ I _ φ _ s κ c hc χ hinf hχ σ y
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)
  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hn : ‖σ (finPart χ y : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, hf, (hasInfRatio_iff χ φ _).1 hinf α, map_inv₀, norm_inv, map_prod, norm_prod]
    simp only [map_zpow₀, norm_zpow, norm_sigma_ratio, one_zpow, Finset.prod_const_one, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedLineBundleIsoCocycleIdentity
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem cocycle_defect_eq {G : Type} [CommGroup G] {A B C A' B' C' G₁ G₂ G₃ : G} (h₁ : A * G₂ = G₁ * A')
    (h₂ : B * G₃ = G₂ * B') (h₃ : C * G₃ = G₁ * C') : A * B * C⁻¹ = A' * B' * C'⁻¹ := by
  have e₁ : A' = G₁⁻¹ * (A * G₂) := by rw [h₁, inv_mul_cancel_left]
  have e₂ : B' = G₂⁻¹ * (B * G₃) := by rw [h₂, inv_mul_cancel_left]
  have e₃ : C' = G₁⁻¹ * (C * G₃) := by rw [h₃, inv_mul_cancel_left]
  subst e₁ e₂ e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cocycle_defect_one {G : Type} [CommGroup G] {A B C R₁ R₂ R₃ : G} (h₁ : A * R₂ = R₁) (h₂ : B * R₃ = R₂)
    (h₃ : C * R₃ = R₁) : A * B * C⁻¹ = 1 := by
  rw [mul_inv_eq_one]
  apply mul_right_cancel (b := R₃)
  rw [_root_.mul_assoc, h₂, h₁, h₃]

theorem norm_cocycle : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  intro X Y p e hep hp V W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ L₁ L₂ L₃ w₁₂ w₂₃ w₁₃ r₁ r₂ r₃ h₁ h₂ h₃ hVW hVW' i₁₂ i₂₃ i₁₃
    n₁₂ n₂₃ n₁₃ x a b c hx ha hb hc
  let O : L₁.ι × L₂.ι × L₃.ι → X.Opens := fun j ↦ p ⁻¹ᵁ V ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1 ⊓ L₃.U j.2.2)
  have mO : ∀ (j : L₁.ι × L₂.ι × L₃.ι) (z : X),
      z ∈ O j ↔ p z ∈ V ∧ z ∈ L₁.U j.1 ∧ z ∈ L₂.U j.2.1 ∧ z ∈ L₃.U j.2.2 := by
    intro j z
    simp only [O, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have mW : ∀ z : X, p z ∈ V → (z ∈ W₁ ∧ z ∈ W₂ ∧ z ∈ W₃) ∧ z ∈ W₁₂ ∧ z ∈ W₂₃ ∧ z ∈ W₁₃ := by
    intro z hz
    have e₁ := hVW (show z ∈ p ⁻¹ᵁ V from hz)
    have e₂ := hVW' (show z ∈ p ⁻¹ᵁ V from hz)
    simp only [TopologicalSpace.Opens.mem_inf] at e₁ e₂
    exact ⟨⟨e₁.1.1, e₁.1.2, e₁.2⟩, e₂.1.1, e₂.1.2, e₂.2⟩
  have l₁₂ : ∀ j, O j ≤ W₁₂ ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.1, hz.2.1, hz.2.2.1⟩
  have l₂₃ : ∀ j, O j ≤ W₂₃ ⊓ (L₂.U j.2.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.1, hz.2.2.1, hz.2.2.2⟩
  have l₁₃ : ∀ j, O j ≤ W₁₃ ⊓ (L₁.U j.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.2, hz.2.1, hz.2.2.2⟩
  let u : ∀ j, Γ(X, O j)ˣ := fun j ↦
    res (l₁₂ j) (w₁₂ j.1 j.2.1) * res (l₂₃ j) (w₂₃ j.2.1 j.2.2) * (res (l₁₃ j) (w₁₃ j.1 j.2.2))⁻¹
  have hu : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j : L₁.ι × L₂.ι × L₃.ι), f z ∈ O j →
      gm f z (O j) (u j) = gm f z _ (w₁₂ j.1 j.2.1) * gm f z _ (w₂₃ j.2.1 j.2.2) * (gm f z _ (w₁₃ j.1 j.2.2))⁻¹ := by
    intro Z f z j hz
    simp only [u, map_mul, map_inv]
    rw [gm_res f z (l₁₂ j) hz, gm_res f z (l₂₃ j) hz, gm_res f z (l₁₃ j) hz]
  have compat : ∀ i j, ∀ z ∈ O i ⊓ O j, gm (𝟙 X) z (O i) (u i) = gm (𝟙 X) z (O j) (u j) := by
    intro i j z hz
    rw [TopologicalSpace.Opens.mem_inf] at hz
    have hzi := hz.1
    have hzj := hz.2
    rw [hu (𝟙 X) z i hzi, hu (𝟙 X) z j hzj]
    rw [mO] at hzi hzj
    have hW := mW z hzi.1
    exact cocycle_defect_eq (i₁₂ z hW.2.1 i.1 j.1 i.2.1 j.2.1 hzi.2.1 hzj.2.1 hzi.2.2.1 hzj.2.2.1)
      (i₂₃ z hW.2.2.1 i.2.1 j.2.1 i.2.2 j.2.2 hzi.2.2.1 hzj.2.2.1 hzi.2.2.2 hzj.2.2.2)
      (i₁₃ z hW.2.2.2 i.1 j.1 i.2.2 j.2.2 hzi.2.1 hzj.2.1 hzi.2.2.2 hzj.2.2.2)
  have chart : ∀ z : X, p z ∈ V → ∃ j, z ∈ O j := by
    intro z hz
    have hW := mW z hz
    obtain ⟨a', ha'⟩ := h₁.cov z hW.1.1
    obtain ⟨b', hb'⟩ := h₂.cov z hW.1.2.1
    obtain ⟨c', hc'⟩ := h₃.cov z hW.1.2.2
    exact ⟨(a', b', c'), (mO _ z).2 ⟨hz, ha', hb', hc'⟩⟩
  have hcov : p ⁻¹ᵁ V ≤ iSup O := fun z hz ↦ by
    obtain ⟨j, hj⟩ := chart z hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨ρ, hρ⟩ := glue_unit (p ⁻¹ᵁ V) O (fun j ↦ inf_le_left) hcov u compat

  let φ := RingEquiv.ofBijective (p.app V).hom (hp V)
  let v : Γ(Y, V)ˣ := Units.map φ.symm.toMonoidHom ρ
  have hv : pullU p V v = ρ := by
    apply Units.ext
    exact φ.apply_symm_apply ρ.val

  have hepy : ∀ y : Y, p (e y) = y := fun y ↦ by
    change (e ≫ p) y = y
    rw [hep]
    rfl
  have hρe : ∀ y : Y, y ∈ V → gm e y (p ⁻¹ᵁ V) ρ = 1 := by
    intro y hy
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    obtain ⟨j, hj⟩ := chart (e y) hy'
    rw [← gm_res e y (inf_le_left : O j ≤ p ⁻¹ᵁ V) hj, hρ j, hu e y j hj]
    rw [mO] at hj
    have hW := mW (e y) hj.1
    exact cocycle_defect_one (n₁₂ y j.1 j.2.1 hW.2.1 hj.2.1 hj.2.2.1) (n₂₃ y j.2.1 j.2.2 hW.2.2.1 hj.2.2.1 hj.2.2.2)
      (n₁₃ y j.1 j.2.2 hW.2.2.2 hj.2.1 hj.2.2.2)
  have hv1 : v = 1 := by
    apply unit_ext
    intro y hy
    rw [map_one]
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    have h := gm_pull e p y V hy' v
    rw [hep, hv] at h
    rw [← h]
    exact hρe y hy
  have hρ1 : ρ = 1 := by rw [← hv, hv1, map_one]

  have hxO : x ∈ O (a, b, c) := (mO _ x).2 ⟨hx, ha, hb, hc⟩
  have h := hu (𝟙 X) x (a, b, c) hxO
  rw [← hρ, hρ1, map_one, map_one] at h
  exact (mul_inv_eq_one.1 h.symm)

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev compGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)

theorem compGL_apply (w : InfinitePlace E) (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = (g : Matrix (Fin n) (Fin n) (Cinf E)) i j w := rfl

abbrev matInf (g : GL (Fin n) (Cinf E)) : Fin n → Fin n → Cinf E :=
  fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j

def IsWhitInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), ∀ g,
    W (u * g) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * W g

def IsModGrowthInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  Continuous W ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * htInf g ^ N

def IsRapidFInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : X → Z →L[ℝ] ℝ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
    (∀ z, Measurable fun x => η x z) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * (htInf (γ x) * (1 + ‖η x‖)) ^ N) ν

def IsKerOpInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin n) (Cinf E))
    (η : X → Z →L[ℝ] ℝ), IsRapidFInf ν k γ η ∧
      ∀ W, IsModGrowthInf W → ∀ z g, T W z g = ∫ x, k x * (𝐞 (η x z) : ℂ) * W (g * γ x) ∂ν


variable (E) in
def levSetInf (n r : ℕ) : Set (GL (Fin n) (Cinf E)) := {g | ∀ w, compGL w g ∈ levSet n r}

def rowCutInf (ρ : Fin n) (x : Matrix (Fin n) (Fin n) (Cinf E)) : Fin n → Cinf E := fun j => if j ≤ ρ then x ρ j else 0

def secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) : Fin n → Fin n → Cinf E :=
  fun i l w => secMat ρ (j w) (fun l => v l w) i l


open Classical in
def onMatInf (W : GL (Fin n) (Cinf E) → ℂ) (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℂ :=
  if h : IsUnit x then W h.unit else 0

def smoothMatInf (α : (Fin n → Fin n → Cinf E) → ℂ) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) : ℂ :=
  ∫ a : Fin n → Fin n → Cinf E, α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)


open Classical in
def toGLInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : GL (Fin n) (Cinf E) := if h : IsUnit x then h.unit else 1

theorem val_toGLInf {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    (toGLInf x : Matrix (Fin n) (Fin n) (Cinf E)) = x := by
  simp [toGLInf, h]

theorem onMatInf_val (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) :
    onMatInf W (g : Matrix (Fin n) (Fin n) (Cinf E)) = W g := by
  simp [onMatInf]

theorem onMatInf_of_isUnit (W : GL (Fin n) (Cinf E) → ℂ) {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    onMatInf W x = W (toGLInf x) := by
  simp [onMatInf, toGLInf, h]

theorem mem_levSetInf {r : ℕ} {g : GL (Fin n) (Cinf E)} : g ∈ levSetInf E n r ↔
    ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
      (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1 := by
  constructor
  · intro h i hi
    refine ⟨fun j hj => funext fun w => ?_, funext fun w => ?_⟩
    · exact (h w i hi).1 j hj
    · exact (h w i hi).2
  · intro h w i hi
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [compGL_apply, (h i hi).1 j hj]; rfl
    · rw [compGL_apply, (h i hi).2]; rfl

theorem isKerOpInf_dirac (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (h : GL (Fin n) (Cinf E)) :
    IsKerOpInf (fun W (_ : Z) g => W (g * h)) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => h, fun _ => 0,
    ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_const _⟩,
    fun W _ z g => ?_⟩
  simp

def LevRepInf (E : Type) [Field E] [NumberField E] (n r : ℕ) (lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ) : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (B : Y × (Fin n → Fin n → Cinf E) → ℂ),
    ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)} → (∀ y, IsWhitInf fun g => B (y, matInf g)) →
    (∃ (D : Set Y) (C : Set (GL (Fin n) (Cinf E))), IsCompact D ∧ IsCompact C ∧ ∀ y, ∀ g ∈ levSetInf E n r,
      B (y, matInf g) ≠ 0 → y ∈ D ∧ ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C) →
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n r, T W y g = B (y, matInf g) * lam W

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesguStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), 1 ≤ r → IsOrth X x → ∀ D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ), (∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧ ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ)) → Function.Injective D ∧ riemLie X.Ψ X.Gm x = ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) • (volume : Measure (ChartSp X)).map D := by
  first | exact @GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | exact GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | (intros; apply GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map <;> assumption)
end

