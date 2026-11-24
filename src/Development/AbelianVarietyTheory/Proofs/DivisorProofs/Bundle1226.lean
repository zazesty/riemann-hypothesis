module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import GroundTheory.LocalFields.LocalFourierHaar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslate
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped NNReal ENNReal

namespace GlobalTheory.SplitFlip

theorem lintegral_mul_invT_sq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  intro k _ _ _ _ a d Φ h ν hν
  letI mk : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  letI mM : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI := hν
  set M : Matrix (Fin d) (Fin d) k := (invT h).1 with hM
  set M' : Matrix (Fin d) (Fin d) k := ((invT h)⁻¹).1
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let L : Matrix (Fin a) (Fin d) k ≃ᵐ Matrix (Fin a) (Fin d) k :=
    { toFun := fun Y => Y * M
      invFun := fun Y => Y * M'
      left_inv := fun Y => by simp [Matrix.mul_assoc, hMM']
      right_inv := fun Y => by simp [Matrix.mul_assoc, hM'M]
      measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
      measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable }
  let f0 : Matrix (Fin a) (Fin d) k → (Fin a × Fin d → k) := fun Y p => Y p.1 p.2
  have hEc : Continuous f0 := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  let g0 : (Fin a × Fin d → k) → Matrix (Fin a) (Fin d) k := fun f => Matrix.of fun i j => f (i, j)
  have hEsc : Continuous g0 :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  let E : Matrix (Fin a) (Fin d) k ≃+ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }
  let EM : Matrix (Fin a) (Fin d) k ≃ᵐ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      measurable_toFun := hEc.measurable, measurable_invFun := hEsc.measurable }
  haveI hμ : (ν.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map ν hEc hEsc
  let K : Matrix (Fin a × Fin d) (Fin a × Fin d) k := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin a) (Fin a) k) Mᵀ
  have hK : ∀ Y, K *ᵥ f0 Y = f0 (Y * M) := by
    intro Y; funext p
    simp [K, f0, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply, mul_comm]
  have hdetK : K.det = (((gdet h)⁻¹ ^ a : kˣ) : k) := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose, Fintype.card_fin, ← gdet_invT]
    simp [M, gdet]
  have hu : K.det ≠ 0 := by rw [hdetK]; exact Units.ne_zero _
  have hlam : (Measure.addHaar : Measure k).map (fun x => algebraMap k k K.det * x) =
      (distribHaarChar k (gdet h) ^ a) • (Measure.addHaar : Measure k) := by
    have h2 := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map (Measure.addHaar : Measure k) ((gdet h)⁻¹ ^ a)
    rw [Algebra.algebraMap_self, RingHom.id_apply, hdetK]
    have hcd : distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a) = 1 := by
      rw [map_pow, map_inv, ← mul_pow, mul_inv_cancel₀ distribHaarChar_pos.ne', one_pow]
    calc (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x)
        = (distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a)) •
            (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x) := by rw [hcd, one_smul]
      _ = _ := by rw [mul_smul, h2]
  have h1 := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul k k (Fin a × Fin d) K hu Measure.addHaar inferInstance _ hlam
    (ν.map E) hμ
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have key : ν.map L = (distribHaarChar k (gdet h) ^ a) • ν := by
    apply EM.map_measurableEquiv_injective
    rw [Measure.map_map EM.measurable L.measurable, Measure.map_smul]
    have e1 : (EM ∘ L) = (fun x => K *ᵥ x) ∘ EM := by funext Y; exact (hK Y).symm
    rw [e1, ← Measure.map_map (GlobalTheory.CompanionTheory.SW.DetScale.measurable_mulVec K) EM.measurable]
    exact h1
    exact EM.measurable.aemeasurable
  have hl := lintegral_map_equiv (fun Y => ‖Φ Y‖ₑ ^ 2) L (μ := ν)
  rw [key] at hl
  refine hl.symm.trans ?_
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  simp only [apow, GlobalTheory.SplitWeil.nabs, Complex.cpow_natCast, enorm_pow]
  rw [ENNReal.coe_pow]; congr 1; rw [← ofReal_norm_eq_enorm]; simp

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
section
noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem chrW_nu_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ t
  have hν : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  exact ⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (continuous_chrW hν t), isUnitaryChar_chrW _ t⟩

end GlobalTheory.ChrWSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_conj {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) :
    Integrable (fun x => f x * conj (h x)) μ := by
  have cf : Continuous f := hf.1.continuous
  have ch : Continuous h := hh.1.continuous
  exact (cf.mul (Complex.continuous_conj.comp ch)).integrable_of_hasCompactSupport
    (hf.2.mul_right)

theorem conj_mem {h : X → ℂ} (hh : h ∈ SB X) : (fun y => conj (h y)) ∈ SB X :=
  ⟨hh.1.comp _, hh.2.comp_left (map_zero _)⟩

theorem self_eq {g : X → ℂ} (hg : g ∈ SB X) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∧
    (∫ x, g x * conj (g x) ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi : Integrable (fun x => g x * conj (g x)) μ := integrable_mul_conj μ hg hg
  have hn : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    have := hi.norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · rw [ofReal_integral_eq_lintegral_ofReal hn (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  · rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem expand {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) (c : ℂ) :
    ∫ x, (c • h + f) x * conj ((c • h + f) x) ∂μ =
      c * conj c * ∫ x, h x * conj (h x) ∂μ + c * ∫ x, h x * conj (f x) ∂μ +
      conj c * ∫ x, f x * conj (h x) ∂μ + ∫ x, f x * conj (f x) ∂μ := by
  have e : (fun x => (c • h + f) x * conj ((c • h + f) x)) =
      fun x => (c * conj c) * (h x * conj (h x)) + c * (h x * conj (f x)) +
        conj c * (f x * conj (h x)) + f x * conj (f x) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact integrable_mul_conj μ hf hf
    | exact (integrable_mul_conj μ hh hh).const_mul _
    | exact (integrable_mul_conj μ hh hf).const_mul _
    | exact (integrable_mul_conj μ hf hh).const_mul _
    | exact ((integrable_mul_conj μ hh hh).const_mul _).add ((integrable_mul_conj μ hh hf).const_mul _)
    | exact (((integrable_mul_conj μ hh hh).const_mul _).add
        ((integrable_mul_conj μ hh hf).const_mul _)).add ((integrable_mul_conj μ hf hh).const_mul _)

end GlobalTheory.PolarSB


open MeasureTheory ComplexConjugate in
theorem GlobalTheory.PolarSB.pairing_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  open MeasureTheory ComplexConjugate in
  intro F _ _ κ _ v T hSB hlin μ hμ hnorm φ₁ h₁ φ₂ h₂
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  set w : (κ → Fv F v) → ℂ := fun y => starRingEnd ℂ (φ₂ y) with hw
  have hwSB : w ∈ SB (κ → Fv F v) := GlobalTheory.PolarSB.conj_mem h₂
  have hN : ∀ g ∈ SB (κ → Fv F v),
      ∫ x, T g x * conj (T g x) ∂μ = ∫ x, g x * conj (g x) ∂μ := by
    intro g hg
    obtain ⟨a1, a2⟩ := GlobalTheory.PolarSB.self_eq μ hg
    obtain ⟨b1, b2⟩ := GlobalTheory.PolarSB.self_eq μ (hSB g hg)
    rw [a2, b2]
    congr 1
    have := hnorm g hg
    rw [← a1, ← b1] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)).1 this
  have key : ∀ c : ℂ,
      c * ∫ x, T w x * conj (T φ₁ x) ∂μ + conj c * ∫ x, T φ₁ x * conj (T w x) ∂μ =
      c * ∫ x, w x * conj (φ₁ x) ∂μ + conj c * ∫ x, φ₁ x * conj (w x) ∂μ := by
    intro c
    have hm : c • w + φ₁ ∈ SB (κ → Fv F v) := add_mem (Submodule.smul_mem _ c hwSB) h₁
    have e1 := hN _ hm
    rw [hlin w hwSB φ₁ h₁ c, GlobalTheory.PolarSB.expand μ h₁ hwSB c,
      GlobalTheory.PolarSB.expand μ (hSB _ h₁) (hSB _ hwSB) c, hN _ h₁, hN _ hwSB] at e1
    linear_combination e1
  have k1 := key 1
  have kI := key Complex.I
  simp only [map_one, one_mul, Complex.conj_I] at k1 kI
  have hfin : ∫ x, T φ₁ x * conj (T w x) ∂μ = ∫ x, φ₁ x * conj (w x) ∂μ := by
    linear_combination (k1 + Complex.I * kI) / 2 +
      (-(∫ x, T w x * conj (T φ₁ x) ∂μ) + ∫ x, T φ₁ x * conj (T w x) ∂μ
        + ∫ x, w x * conj (φ₁ x) ∂μ - ∫ x, φ₁ x * conj (w x) ∂μ) / 2 * Complex.I_sq
  rw [hfin]
  simp [hw]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
section
open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

end GlobalTheory.UnitaryVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJReg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def chiS (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) s

theorem chiS_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g h : GL (Fin n) k) : chiS ν s (g * h) = chiS ν s g * chiS ν s h := by
  simp only [chiS, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

@[simp] theorem chiS_one (ν : kˣ →* ℂˣ) (s : ℂ) : chiS ν s (1 : GL (Fin n) k) = 1 := by
  simp [chiS, gdet]

theorem chiS_inv_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : chiS ν s g⁻¹ * chiS ν s g = 1 := by
  rw [← chiS_mul, inv_mul_cancel, chiS_one]

theorem chiS_of_mem_KO {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (s : ℂ) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    chiS ν s g = 1 := by
  have hv := valuation_gdet_of_mem_KO hg
  simp [chiS, hν _ hv, apow_of_valuation_eq_one hv]

def latInd (g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k → ℂ := fun X =>
  (intM k (Fin n) (Fin n)).indicator 1 (X * (g⁻¹ : GL (Fin n) k).val)

theorem latInd_mem_SB (g : GL (Fin n) k) : latInd g ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := g.val) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    indicator_intM_mem_SB

theorem mul_left_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (g.val * X)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun X : Matrix (Fin n) (Fin n) k => g.val * X := continuous_const.matrix_mul continuous_id
  have c2 : Continuous fun X : Matrix (Fin n) (Fin n) k => (g⁻¹).val * X := continuous_const.matrix_mul continuous_id
  have e : Topology.IsClosedEmbedding fun X : Matrix (Fin n) (Fin n) k => g.val * X :=
    Function.LeftInverse.isClosedEmbedding (f := fun X => (g⁻¹).val * X)
      (fun X => by simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])
      c2 c1
  exact ⟨hφ.1.comp_continuous c1, hφ.2.comp_isClosedEmbedding e⟩

theorem mul_right_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (X * g.val)) ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := (g⁻¹).val) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hφ


variable (k n) in
def kInd : Matrix (Fin n) (Fin n) k → ℂ := {X | ∃ g ∈ KO k (Fin n), g.val = X}.indicator 1

def gjZ [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (s : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) : ℂ :=
  ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) s ∂(haarVol (KO k (Fin n)))

end GlobalTheory.GJReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenforms
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_expCurve (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun x => ψ.1 (g * expCurve E a x)) ((scalD E a ψ).1 (g * expCurve E a t)) t := by
  have h1 := Central.hasDerivAt_scalar (1 : Cinf E) ψ (g * expCurve E a t)
  have h3 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ h1)
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  have e : expCurve E a x = expCurve E a t * expCurve E a (x - t) := by
    rw [← expCurve_add, add_sub_cancel]
  simp only [Function.comp_apply]
  rw [e, ← mul_assoc]
  rfl

theorem commute_scalD_sub (c c' : ℂ) :
    Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c') :=
  Commute.sub_left ((Commute.refl _).sub_right (Algebra.commute_algebraMap_right c' _))
    (Algebra.commute_algebraMap_left c _)

theorem mem_expSol_of_prod (l : List ℂ) : ∀ (ψ : Sm E a),
    (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod ψ = 0 →
    ∀ g : GA E a, (fun x => ψ.1 (g * expCurve E a x)) ∈ expSol l := by
  induction l with
  | nil =>
    intro ψ h g
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h
    subst h
    exact mem_expSol_nil.2 rfl
  | cons c l ih =>
    intro ψ h g
    refine mem_expSol_cons.2 ⟨fun x => (hasDerivAt_expCurve ψ g x).differentiableAt, ?_⟩
    have hc : Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c)
        (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod :=
      Commute.list_prod_right _ _ fun b hb => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.1 hb
        exact commute_scalD_sub c c'
    have h2 : (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod
        ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ) = 0 := by
      rw [List.map_cons, List.prod_cons] at h
      rw [← Module.End.mul_apply, ← hc.eq]; exact h
    have h3 := ih _ h2 g
    have e : deriv (fun x => ψ.1 (g * expCurve E a x)) - c • (fun x => ψ.1 (g * expCurve E a x)) =
        fun x => ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ).1 (g * expCurve E a x) := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [(hasDerivAt_expCurve ψ g x).deriv]
      simp [Module.algebraMap_end_apply]
    rw [e]; exact h3

theorem norm_le_of_band_wide : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ (N : ℕ) (c : ℝ), 1 ≤ c → ∃ C : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g : GA E a, c⁻¹ ≤ absDetA g → absDetA g ≤ 2 * c → ‖φ.1 g‖ ≤ C * M := by
  intro E _ _ _ a L _ W _ X hX N c hc
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨1, fun φ _ M hM g _ _ => ?_⟩
    have e : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [one_mul]; exact hM g (e ▸ one_mem_band)
  obtain ⟨Λ, hΛ⟩ := _root_.GlobalTheory.HCF.span_formsGL_killed_scalD E a L W X hX N
  set κ : ℝ := a * Module.finrank ℚ E with hκ
  have hκ0 : 0 < κ := mul_pos (by exact_mod_cast ha) (by exact_mod_cast Module.finrank_pos)
  set ℓ : ℝ := Real.log 2 / κ
  have hℓ : 0 < ℓ := div_pos (Real.log_pos (by norm_num)) hκ0
  have hvan : ∀ f ∈ expSol Λ, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0 := fun f hf h0 =>
    _root_.GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo Λ f hf 0 ℓ hℓ fun x hx => h0 x (Set.Ioo_subset_Icc_self hx)
  have hcont : ∀ f ∈ expSol Λ, Continuous f := by
    intro f hf
    cases Λ with
    | nil => rw [mem_expSol_nil.1 hf]; exact continuous_const
    | cons c l => exact (mem_expSol_cons.1 hf).1.continuous
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.finiteDim_norm_le_on_Icc_of_determined (expSol Λ) (GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional Λ) hcont ℓ hℓ hvan (Real.log (2 * c) / κ)
  refine ⟨C, fun φ hφ M hM g hg1 hg2 => ?_⟩
  have hgpos := absDetA_pos g
  set τ : ℝ := Real.log (absDetA g) / κ
  set g1 := g * expCurve E a (-τ)
  have hdet1 : absDetA g1 = 1 := by
    rw [_root_.GlobalTheory.HCF.absDetA_mul_expCurve, ← hκ, show -τ * κ = -Real.log (absDetA g) by simp only [τ]; field_simp, Real.exp_neg,
      Real.exp_log hgpos, mul_inv_cancel₀ hgpos.ne']
  have hf := mem_expSol_of_prod Λ φ (hΛ φ hφ) g1
  have hband : ∀ x ∈ Set.Icc 0 ℓ, ‖φ.1 (g1 * expCurve E a x)‖ ≤ M := by
    intro x hx
    refine hM _ ⟨?_, ?_⟩
    · rw [_root_.GlobalTheory.HCF.absDetA_mul_expCurve, hdet1, one_mul, ← hκ]
      exact Real.one_le_exp (mul_nonneg hx.1 hκ0.le)
    · rw [_root_.GlobalTheory.HCF.absDetA_mul_expCurve, hdet1, one_mul, ← hκ]
      have : x * κ ≤ Real.log 2 := by
        have := hx.2; simp only [ℓ] at this; rwa [le_div_iff₀ hκ0] at this
      calc Real.exp (x * κ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 this
        _ = 2 := Real.exp_log (by norm_num)
  have hτ : τ ∈ Set.Icc (-(Real.log (2 * c) / κ)) (Real.log (2 * c) / κ) := by
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
    have l1 : Real.log (absDetA g) ≤ Real.log (2 * c) := Real.log_le_log hgpos hg2
    have l2 : -Real.log c ≤ Real.log (absDetA g) := by
      rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.2 hc0) hg1
    have l3 : Real.log c ≤ Real.log (2 * c) := Real.log_le_log hc0 (by linarith)
    constructor
    · rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hκ0.le
    · exact div_le_div_of_nonneg_right l1 hκ0.le
  have := hC _ hf M hband τ hτ
  have e : g1 * expCurve E a τ = g := by
    simp only [g1]; rw [mul_assoc, ← expCurve_add, neg_add_cancel, expCurve_zero, mul_one]
  simpa only [e] using this

end GlobalTheory.HCF

end
end

