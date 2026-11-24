module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C, hC⟩ := hT μ₂ inferInstance

  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : (κ ⊕ κ' → AF F) ≃ₜ+ (κ → AF F) × (κ' → AF F) :=
    { e.toEquiv with
      map_add' := fun _ _ => rfl
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  haveI : (μ.map eA).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ eA
  set c := (μ.map eA).addHaarScalarFactor (μ₁.prod μ₂)
  have hprod : μ.map eA = c • μ₁.prod μ₂ := Measure.isAddLeftInvariant_eq_smul _ _

  have key : ∀ g : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable g →
      ∫⁻ z, g z ∂μ = c * ∫⁻ a, ∫⁻ b, g (Sum.elim a b) ∂μ₂ ∂μ₁ := by
    intro g hg
    have h1 : ∫⁻ z, g z ∂μ = ∫⁻ p, g (e.symm p) ∂(μ.map eA) := by
      rw [show μ.map eA = μ.map e.toMeasurableEquiv from rfl, lintegral_map_equiv]
      refine lintegral_congr fun z => ?_
      exact congrArg g (e.symm_apply_apply z).symm
    rw [h1, hprod, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
      lintegral_prod (fun p => g (e.symm p)) (hg.comp e.symm.continuous.measurable).aemeasurable]
    rfl
  have hmeas : ∀ Φ ∈ schA F (κ ⊕ κ'), Measurable fun z => ‖Φ z‖ₑ ^ 2 := fun Φ hΦ =>
    ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ).measurable.enorm).pow_const 2
  refine ⟨C, fun Φ hΦ => ?_⟩
  have hslice : ∀ a : κ → AF F, (fun x => Φ (Sum.elim a x)) ∈ schA F κ' := fun a =>
    GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ
  have hin : ∀ a : κ → AF F, ∫⁻ b, ‖partR T Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ =
      C * ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ := fun a => hC _ (hslice a)
  have hm2 : Measurable fun a : κ → AF F => ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ :=
    ((hmeas Φ hΦ).comp e.symm.continuous.measurable).lintegral_prod_right'
  rw [key _ (hmeas _ (hmem Φ hΦ)), key _ (hmeas Φ hΦ)]
  simp_rw [hin]
  rw [lintegral_const_mul _ hm2, mul_left_comm]

end GlobalTheory.DblEval.L2RightPartial

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.OneSquareZeta
open ValuativeRel GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isPrimFrame_mul_iff {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] {Λ : Submodule 𝒪[k] (C → k)}
    {X : Matrix (Fin a) C k} {g₀ : GL (Fin a) k} (h₀ : IsPrimFrame Λ (g₀.val * X)) (g : GL (Fin a) k) :
    IsPrimFrame Λ (g.val * X) ↔ g * g₀⁻¹ ∈ KO k (Fin a) := by
  rw [isPrimFrame_iff] at h₀ ⊢
  have hrow : ∀ (M : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) C k) i, (M * Y).row i = M.row i ᵥ* Y :=
    fun M Y i => by funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  have hgX : g.val * X = (g * g₀⁻¹).val * (g₀.val * X) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc g.val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hg0X : g₀.val * X = ((g * g₀⁻¹)⁻¹).val * (g.val * X) := by
    rw [hgX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [mem_KO_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h₀.2 ((g * g₀⁻¹).val.row i) (by rw [← hrow, ← hgX]; exact h1 i) j
    · exact h2 (((g * g₀⁻¹)⁻¹).val.row i) (by rw [← hrow, ← hg0X]; exact h₀.1 i) j
  · rintro ⟨hu1, hu2⟩
    refine ⟨fun i => ?_, fun c hc i => ?_⟩
    · show (g.val * X).row i ∈ Λ
      rw [hgX, hrow]; exact vecMul_mem_of_int h₀.1 (fun j => hu1 i j)
    · have h3 := h₀.2 (c ᵥ* (g * g₀⁻¹).val) (by rw [vecMul_vecMul, ← hgX]; exact hc)
      have hc' : c = (c ᵥ* (g * g₀⁻¹).val) ᵥ* ((g * g₀⁻¹)⁻¹).val := by
        rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [hc']
      change (∑ l, (c ᵥ* (g * g₀⁻¹).val) l * ((g * g₀⁻¹)⁻¹).val l i) ∈ 𝒪[k]
      exact Subring.sum_mem _ fun l _ => mul_mem (h3 l) (hu2 l i)

theorem fFun_mul_left {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C)
    (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k) :
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  exact _root_.GlobalTheory.fFun_mul_left k a A' C μ σ ν Ψ g h

theorem exists_primFrame {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] (d : C → kˣ)
    (X : Matrix (Fin a) C k) (hX : X.rank = a) : ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  exact _root_.GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame k a C d X hX

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_phiA {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ)
    (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (hϖ : IsUnif ϖ) (h : GL C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (phiA μ σ ν ϖ n (diagLat c) Ψ) (X0 k σ * (invT h).val) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  set X := X0 k σ * (invT h).val with hXdef
  have hΛ : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : X.rank = a := by
    have := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 ⟨h, rfl⟩; simpa using this
  obtain ⟨g₀, hg₀⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) X hrank
  rw [← hΛ] at hg₀
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₀
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, phiA μ σ ν ϖ n (diagLat c) Ψ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card C : ℂ) / 2) = S.indicator (fun _ => fFun μ σ ν Ψ X) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, phiA, if_pos ((isPrimFrame_mul_iff hg₀ g).2 hg)]
      exact fFun_mul_left μ σ ν Ψ g h
    · rw [Set.indicator_of_notMem hg, phiA, if_neg (fun h' => hg ((isPrimFrame_mul_iff hg₀ g).1 h')),
        zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card C : ℂ) / 2) (fun M => phiA μ σ ν ϖ n (diagLat c) Ψ (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • fFun μ σ ν Ψ X := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => fFun μ σ ν Ψ X) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹ * g₀ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀ = (g * g₀⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.OneSquareZeta


open GlobalTheory.OneSquareZeta in
theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ), IsUnif ϖ →
    bigP (haarVol (KO k (Fin a))) ϖ σ ν β (phiA μ σ ν ϖ n (diagLat c) Ψ) = smallP μ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ hϖ
  funext h
  rw [bigZetaIntegral_eq, bigF_phiA μ σ ν ϖ n c Ψ hϖ h, splitTheta_fFun_frameFirstBlock_mul, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination (β (gdet h) * ν (gdet h) * smallF μ ν Ψ (Y0 k σ * h.val) : ℂ) * e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemSB
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.FinPull

theorem pullback_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ w)) ∈
        SB (ι → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ ι κ _ _ D hD g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  set A := algebraMap F (FiniteAdeleRing (𝓞 F) F)
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact hD z (by simpa using hz)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D) (LinearMap.ker_eq_bot.mpr hinj)
  set L := LinearMap.toMatrix' G
  have hLD : L * D = 1 := by
    have : LinearMap.toMatrix' (G ∘ₗ Matrix.toLin' D) = LinearMap.toMatrix' LinearMap.id := by rw [hG]
    simpa [L, LinearMap.toMatrix'_comp] using this
  have hM : Continuous fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hN : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Function.LeftInverse (fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w)
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w) := fun w => by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hLD, Matrix.map_one A (map_zero A) (map_one A), Matrix.one_mulVec]
  exact ⟨hg.1.comp_continuous hM, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding hN hM)⟩

end GlobalTheory.FinPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.RatTop

theorem exists_linearMap_of_repr_mem_range {K : Type} [Field K] (φ : K →+* ℂ) {VS VT WS WT : Type}
    [AddCommGroup VS] [Module K VS] [AddCommGroup VT] [Module K VT]
    [AddCommGroup WS] [Module ℂ WS] [AddCommGroup WT] [Module ℂ WT]
    (mS : VS →ₛₗ[φ] WS) (mT : VT →ₛₗ[φ] WT) {ι κ : Type} [Fintype ι] [Fintype κ]
    (b0 : Module.Basis ι K VS) (bS : Module.Basis ι ℂ WS) (bT : Module.Basis κ ℂ WT)
    (uS : ι → VS) (uT : κ → VT) (hS : ∀ i, mS (uS i) = bS i) (hT : ∀ k, mT (uT k) = bT k)
    (L : WS →ₗ[ℂ] WT) (hL : ∀ k i, bT.repr (L (bS i)) k ∈ Set.range φ) :
    ∃ f : VS →ₗ[K] VT, ∀ u, L (mS u) = mT (f u) := by
  classical
  haveI : FiniteDimensional K VS := Module.Finite.of_basis b0
  have hli : LinearIndependent K uS := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, φ (g i) • bS i = 0 := by
      have := congrArg mS hg
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, LinearMap.map_smulₛₗ, hS] using this
    have h2 := Fintype.linearIndependent_iff.mp bS.linearIndependent _ h1 i
    exact φ.injective (by rw [h2, map_zero])
  have hsp : Submodule.span K (Set.range uS) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b0).symm
  let bS' : Module.Basis ι K VS := Module.Basis.mk hli hsp.ge
  choose m hm using hL
  let f : VS →ₗ[K] VT := bS'.constr K fun i => ∑ k, m k i • uT k
  refine ⟨f, fun u => ?_⟩
  have e : (L.comp mS : VS →ₛₗ[φ] WT) = (mT.comp f : VS →ₛₗ[φ] WT) := by
    refine bS'.ext fun i => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.mk_apply, hS, map_sum]
    conv_lhs => rw [← bT.sum_repr (L (bS i))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, hT, hm]
  exact LinearMap.congr_fun e u

end GlobalTheory.RatTop

namespace GlobalTheory.KerConjMean

theorem ratTopAt_big : BigC fun _ ch _ _ => RatTopAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c j
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).1 j
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun i => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro i
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k i
    have h := hr k i
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominator
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.BoundedDen

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc


set_option maxHeartbeats 1000000 in
theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFixatorOfColumnsIsSemidirectLattice
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem semiLat_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ →
    ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C))
      (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))),
      SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ H
  have key : ∀ {P : Subgroup (GAd σ J)}, P ≤ fixG σ J C →
      (ratPts σ J ⊓ fixG σ J C).subgroupOf P = (ratPts σ J).subgroupOf P := fun h => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩
  obtain ⟨hC, -, cM, cN, hN, hP, hd, hn, -⟩ := _root_.GlobalTheory.SphEis.frame_facts F E σ n J j m C D Z J₀ H
  haveI := locallyCompact_unipRad H.cm H.herm hC
  obtain ⟨ν, DN, hν, hDN, h1⟩ := exists_mass_one (cocompact_unipRad H.cm H.herm hC)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := cM.locallyCompactSpace
  have hDM := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom
    ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) Measure.haar
  refine ⟨ν, Measure.haar, DN, _,
    { closedN := cN
      closedM := cM
      norm := fun x hx u hu => (hn x (hP hx.1) u).1 hu
      disj := hd
      dec := ?_
      haarN := hν
      haarM := inferInstance
      domN := by rw [key hN]; exact hDN
      domM := by rw [key inf_le_left]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := _root_.GlobalTheory.SphEis.finCovol_fixG F E σ n J j m C D Z J₀ H _ _ inferInstance hDM }⟩
  rintro γ ⟨hγ, hf⟩
  obtain ⟨u, hu, x, hx, e, hr⟩ := _root_.GlobalTheory.SphEis.fixG_eq_unipRad_mul F E σ n J j m C D Z J₀ H γ hf
  refine ⟨u, hu, x, hx, ⟨?_, hN hu⟩, ⟨hr hγ, hx.1⟩, e⟩
  have : u = γ * x⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVectorStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_invariant_vector : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | exact GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | (intros; apply GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any <;> assumption)
end

