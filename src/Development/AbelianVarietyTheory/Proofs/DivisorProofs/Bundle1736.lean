module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCompInfGLProd
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ComplexConjugate

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem measurable_chart_prod {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Measurable fun p : GA E a × Lie E a => chart φ p.1 p.2 := by
  classical
  have e : (fun p : GA E a × Lie E a => chart φ p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart φ p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.univ ×ˢ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have hp' : ¬ IsUnit (Matrix.of p.2) := fun h => hp ⟨trivial, h⟩
      exact dif_neg hp'
  rw [e]
  exact (GlobalTheory.ConstTermSmooth.continuousOn_chart hφ).measurable_piecewise continuousOn_const
    (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun p : GA E a × Lie E a => chart F p.1 p.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem IsRapidInf.integrable_norm {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable (fun x => ‖k x‖) ν := by
  simpa using hk.2.2 0

theorem kerInf_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
    refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (hm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_mul_const _)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [kerInf, mul_assoc, h.2.1]
  · rw [kerInf, kerInf, ← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left {ω : HChar E} (hω : ω.IsUnitary) {F ψ : GA E a → ℂ} (h : F ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    pet (latticeGL E a) μ (kerInf ν k γ F) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki).mono'
      (((hk.1.comp measurable_snd).mul hm).mul
        ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms h hk) h' hD).2]
  simp only [kerInf, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem rspan_central {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {F : GA E a → ℂ} (hF : F ∈ rspan π)
    (z : Ideles E) (g : GA E a) :
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g := by
  have hc := CuspSub.hasCentral_iff.2 hπ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (z : Ideles E) g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
      add_mem' := fun {F F'} hF hF' z g => by simp only [Pi.add_apply, hF z g, hF' z g, mul_add]
      zero_mem' := fun z g => by simp
      smul_mem' := fun c F hF z g => by simp only [Pi.smul_apply, smul_eq_mul, hF z g]; ring }
  refine rspan_le (S := S) (fun φ hφ z g => hc.apply hφ z g) (fun F hF h z g => ?_)
    (fun F hF X _ ν _ k γ _ z g => ?_) hF z g
  · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
    rw [mul_assoc]; exact hF z _
  · change ∫ x, k x * F (GeneralLinearGroup.scalar (Fin a) z * g * infGL E a (γ x)) ∂ν =
      _ * ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, hF z]; ring

theorem pet_rt_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ π.V)
    (h : GA E a) : pet (latticeGL E a) μ (fun g => φ.1 (g * h)) ψ = 0 := by
  have hb : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ hφ =>
    mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
  rw [← infGL_mul_finGL h]
  have e : (fun g => φ.1 (g * (infGL E a (GeneralLinearGroup.map (pInf E) h) *
      finGL E a (GeneralLinearGroup.map (pFin E) h)))) =
      fun g => (finRep E a (GeneralLinearGroup.map (pFin E) h) φ).1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h)) := by
    funext g
    change _ = φ.1 (g * infGL E a _ * finGL E a _)
    rw [mul_assoc]
  rw [e]
  exact GlobalTheory.KeepOrth.pet_translate_eq_zero μ hω hψ hb (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1) h0
    (π.stable (.fin _) φ hφ) _

theorem rspan_bdd_pet_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω)
    {ψ : GA E a → ℂ} (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0)
    {F : GA E a → ℂ} (hF : F ∈ rspan π) :
    F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0 := by
  have hψh : ∀ h : GA E a, (fun g => ψ (g * h)) ∈ bddForms E a ω := mul_right_mem_bddForms hψ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun h => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hψh h), hF.2 h, hF'.2 h, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun h => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun h => by
        rw [pet_smul_left, hF.2 h, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h' : GA E a, (fun g => F (g * h')) ∈ S := fun F hF h' =>
    ⟨mul_right_mem_bddForms hF.1 h', fun h => by
      rw [pet_mul_right_left μ hω hF.1 (hψh h) h']
      have := hF.2 (h'⁻¹ * h)
      simp only [mul_assoc] at this ⊢
      exact this⟩
  refine rspan_le (S := S) (fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun h => ?_⟩) htr (fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hF.1 hk, fun h => ?_⟩) hF
  · have hb := mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
    have e := pet_mul_right_left μ hω hb hψ h⁻¹
    rw [inv_inv] at e
    rw [← e]
    exact pet_rt_eq_zero μ hω hπ hψ h0 hφ h⁻¹
  · rw [pet_kerInf_left μ hω hF.1 (hψh h) ν hk]
    exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 h))

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKOOfIsGLO
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.StdPairZeta
open GlobalTheory.OneSquareZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem val_gdet {a : ℕ} (g : GL (Fin a) k) : ((gdet g : kˣ) : k) = g.val.det := by
  first | rfl | exact Matrix.GeneralLinearGroup.val_det_apply g

theorem isGLO_of_mem_KO {a : ℕ} {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) : g.val.det ≠ 0 ∧ IsGLO g.val := by
  have hv : valuation k g.val.det = 1 := by rw [← val_gdet]; exact GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hg
  exact ⟨fun h => by simp [h] at hv, ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1, hv⟩

theorem mem_KO_of_isGLO {a : ℕ} (g : GL (Fin a) k) (h : IsGLO g.val) : g ∈ KO k (Fin a) := by
  obtain ⟨hM, hd⟩ := h
  let A : Matrix (Fin a) (Fin a) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem mul_mem_cball {n m p : ℕ} {s : kˣ} {M : Matrix (Fin n) (Fin m) k} {Y : Matrix (Fin m) (Fin p) k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ GlobalTheory.SplitWeil.cball s) :
    ∀ i j, (M * Y) i j ∈ GlobalTheory.SplitWeil.cball s := by
  intro i j
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Matrix.mul_apply] at hY ⊢
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hM i l)) (hY l j)).trans_eq (one_mul _)

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_stdA_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := by
    intro g
    unfold stdA
    rw [dite_eq_right]
    rintro ⟨h, -⟩
    exact h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]

theorem bigF_stdA_eq (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (g₁ : GL (Fin a) k) (hg₁ : g₁.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
        Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  set N : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hN
  set Y := (g₁⁻¹).val * blk₂ X with hY
  set C : ℂ := (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-N) *
      Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 Y with hC
  set S : Set (GL (Fin a) k) := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) N =
      S.indicator (fun _ => C) g := by
    intro g
    have h1 : blk₁ (g.val * X) = (g * g₁).val := by rw [blk₁_mul, Units.val_mul, hg₁]
    have h2 : blk₂ (g.val * X) = (g * g₁).val * Y := by
      rw [blk₂_mul, hY, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hκ : g * g₁ ∈ KO k (Fin a) := hg
      obtain ⟨hdet, hglo⟩ := isGLO_of_mem_KO hκ
      have hv : valuation k ((gdet (g * g₁) : kˣ) : k) = 1 := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hκ
      have hinv : (g * g₁)⁻¹ ∈ KO k (Fin a) := inv_mem hκ
      have hYiff : (∀ i j, ((g * g₁).val * Y) i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, Y i j ∈ cball (ϖ ^ c) := by
        constructor
        · intro h
          have e : Y = ((g * g₁)⁻¹).val * ((g * g₁).val * Y) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
          rw [e]; exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hinv).1 h
        · exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hκ).1
      have hap : apow (gdet g) N = apow (gdet g₁) (-N) := by
        have : gdet g = gdet (g * g₁) * (gdet g₁)⁻¹ := by rw [gdet_mul]; group
        rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv]
      unfold stdA
      by_cases hc : ∀ i j, Y i j ∈ cball (ϖ ^ c)
      · have hcond : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
          rw [h1, h2]; exact ⟨hdet, hglo, hYiff.2 hc⟩
        have hmk : Units.mk0 _ hcond.1 = gdet g * gdet g₁ := by
          rw [← gdet_mul]; exact Units.ext (by rw [Units.val_mk0, val_gdet, h1])
        rw [dite_eq_left hcond, hC, Set.indicator_of_mem (show Y ∈ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc), Pi.one_apply, mul_one, hmk, hap, map_mul, mul_inv]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        have h3 := (ν (gdet g)).ne_zero
        linear_combination ((ν (gdet g₁) : ℂ))⁻¹ * apow (gdet g₁) (-N) * inv_mul_cancel₀ h3
      · have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
          rintro ⟨-, -, h⟩
          rw [h2] at h
          exact hc (hYiff.1 h)
        rw [dite_eq_right hneg, hC, Set.indicator_of_notMem (show Y ∉ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc)]
        simp
    · rw [Set.indicator_of_notMem hg]
      have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
          ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
        rintro ⟨-, hglo, -⟩
        rw [h1] at hglo
        exact hg (mem_KO_of_isGLO _ hglo)
      unfold stdA
      rw [dite_eq_right hneg, zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν N
      (fun M => stdA ν ϖ c a a' (M * X)) m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => C) hSm
    rw [e1, setIntegral_const]
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₁⁻¹
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₁ * g₁⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₁⁻¹ = (g * g₁)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.StdPairZeta


open GlobalTheory.StdPairZeta in
theorem GlobalTheory.StdPairZeta.bigF_stdA : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
    (∀ X : Matrix (Fin a) (Fin (a + a')) k, (blk₁ X).det = 0 →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0) ∧
    ∀ (X : Matrix (Fin a) (Fin (a + a')) k) (g₁ : GL (Fin a) k), g₁.val = blk₁ X →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  intro k _ _ _ _ _ _ ν ϖ c a a' hϖ
  exact ⟨fun X hX => bigF_stdA_zero ν ϖ c a a' X hX, fun X g₁ hg₁ => bigF_stdA_eq ν ϖ c a a' hϖ X g₁ hg₁⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdm

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := _root_.GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLattice
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem inf_subgroupOf_of_le' {G : Type} [Group G] {Γ P H : Subgroup G} (h : H ≤ P) :
    (Γ ⊓ P).subgroupOf H = Γ.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩

theorem semiLat_frameGrp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 →
      ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})),
        SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤)
          ν π DN DM := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW ν DN hν hDN h1
  obtain ⟨π, DM, hπ, hDM⟩ := GlobalTheory.StdPar.exists_haar_leviOne (X := X) (Y := Y) {Fin.last r} h hJ hW
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := _root_.GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y h hJ hW
  have hN : unipRad σ J X ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun u hu => ⟨1, trivial, f3 u hu⟩
  have hM : GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun m hm => by
    obtain ⟨β, e, -⟩ := f4 m hm
    exact ⟨β, trivial, e⟩
  refine ⟨π, DM,
    { closedN := (_root_.GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one F E σ n J r X Y h hJ hW).1
      closedM := f7
      norm := fun m hm => f1 m (f6 hm)
      disj := fun g hg hg' => f2 g hg (f6 hg')
      dec := ?_
      haarN := hν
      haarM := hπ
      domN := by rw [inf_subgroupOf_of_le' hN]; exact hDN
      domM := by rw [inf_subgroupOf_of_le' hM]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := _root_.GlobalTheory.ResidueEisenstein.finCovol_leviOne_last F E σ n J r X Y h hJ hW π DM hπ hDM }⟩
  rintro γ ⟨hγ, β, -, e⟩
  obtain ⟨u, hu, m, -, hp, -, hr, ho⟩ := _root_.GlobalTheory.LeviDecompositionFrame.levi_dec_frame F E σ n J r X Y h hJ hW γ β e
  have hm := ho (f5 γ hγ β e)
  refine ⟨u, hu, m, hm, ⟨?_, hN hu⟩, ⟨hr hγ, hM hm⟩, hp⟩
  have : u = γ * m⁻¹ := by rw [hp, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.ResidueEisenstein
end

