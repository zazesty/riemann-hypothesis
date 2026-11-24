module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirections
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem exists_finset_clm_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (B : Finset V) (C : ℝ), 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℂ) (X : V) (M : ℝ),
      (∀ Y ∈ B, ‖L Y‖ ≤ M) → 0 ≤ M → ‖L X‖ ≤ C * ‖X‖ * M := by
  classical
  obtain ⟨C, hC, h⟩ := (Module.finBasis ℝ V).exists_opNorm_le (F := ℂ)
  refine ⟨Finset.univ.image (Module.finBasis ℝ V), C, hC.le, fun L X M hB hM => ?_⟩
  have h1 : ‖L‖ ≤ C * M := h hM fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  calc ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    _ ≤ C * M * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * ‖X‖ * M := by ring

theorem lieD_le_of_basis : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  intro E _ _ _ a
  obtain ⟨B, C, hC, h⟩ := exists_finset_clm_bound (Lie E a)
  exact ⟨B, C, hC, fun ψ g X M hB hM => h (fderiv ℝ (chart ψ g) (oneL E a)) X M hB hM⟩

end GlobalTheory.CuspRapid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem integral_mul_fderiv_lmul_eq_dens (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) (X : Lie E a) {G : Lie E a → ℂ} (hG : ContDiffOn ℝ ∞ G (invSet E a)) :
    ∫ x, α x * fderiv ℝ G x (lmul X x) ∂ν = ∫ x, dens X α x * G x ∂ν := by
  set L := lmul X with hL
  let b := Module.finBasis ℝ (Lie E a)
  let c : Fin (Module.finrank ℝ (Lie E a)) → Lie E a → ℂ := fun i x => α x * (b.repr (L x) i : ℝ)
  have hc : ∀ i, IsTest (invSet E a) (c i) := fun i => hα.mul (Complex.ofRealCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))
  have hG' : ∀ v, ContinuousOn (fun x => fderiv ℝ G x v) (invSet E a) := fun v =>
    (hG.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply continuousOn_const
  have e : ∀ x, α x * fderiv ℝ G x (L x) = ∑ i, c i x * fderiv ℝ G x (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr (L x)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]
  have hdc : ∀ i x, fderiv ℝ (c i) x (b i) =
      α x * (b.repr (L (b i)) i : ℝ) + (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
    intro i x
    have h1 : HasFDerivAt (fun x => ((b.repr (L x) i : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) x :=
      (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)).hasFDerivAt
    have h2 := ((hα.1.differentiable (by simp) x).hasFDerivAt).mul h1
    rw [show c i = (α * fun x => ((b.repr (L x) i : ℝ) : ℂ)) from rfl, h2.fderiv]
    simp [Module.Basis.coord_apply, smul_eq_mul]
  have key : ∀ x, ∑ i, fderiv ℝ (c i) x (b i) = -dens X α x := by
    intro x
    have h3 : fderiv ℝ α x (L x) = ∑ i, (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
      calc fderiv ℝ α x (L x) = fderiv ℝ α x (∑ i, b.repr (L x) i • b i) := by rw [b.sum_repr]
        _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]
    have h4 : (LinearMap.trace ℝ (Lie E a) L.toLinearMap : ℂ) = ∑ i, ((b.repr (L (b i)) i : ℝ) : ℂ) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      simp [LinearMap.toMatrix_apply]
    simp only [hdc, Finset.sum_add_distrib, dens, neg_neg, ← hL, h3, h4, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hi1 : ∀ i, Integrable (fun x => c i x * fderiv ℝ G x (b i)) ν := fun i =>
    (hc i).integrable_mul ν isOpen_invSet (hG' _)
  have hi2 : ∀ i, Integrable (fun x => fderiv ℝ (c i) x (b i) * G x) ν := fun i => by
    simpa using (((hc i).fderiv (b i)).mul contDiff_const (β := fun _ => (1 : ℂ))).integrable_mul ν isOpen_invSet
      hG.continuousOn
  calc ∫ x, α x * fderiv ℝ G x (L x) ∂ν = ∫ x, ∑ i, c i x * fderiv ℝ G x (b i) ∂ν := integral_congr_ae (.of_forall e)
    _ = ∑ i, ∫ x, c i x * fderiv ℝ G x (b i) ∂ν := integral_finsetSum _ fun i _ => hi1 i
    _ = ∑ i, ∫ x, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 i) (hi1 i)
        ((hc i).integrable_mul ν isOpen_invSet hG.continuousOn)
        (fun x _ => (hc i).1.differentiable (by simp) x)
        (fun x hx => (hG.contDiffAt (isOpen_invSet.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)),
        integral_neg]
    _ = ∫ x, ∑ i, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := (integral_finsetSum _ fun i _ => (hi2 i).neg).symm
    _ = ∫ x, dens X α x * G x ∂ν := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, key, neg_mul, neg_neg]

namespace SmoothingDeriv


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_rmul_fun : Continuous (fun y : Lie E a => rmul y) := by
  let R : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := rmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (x + y) = Matrix.of z * Matrix.of x + Matrix.of z * Matrix.of y by
          rw [← Matrix.of_add_of, Matrix.mul_add]
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (c • x) = c • (Matrix.of z * Matrix.of x) by
          rw [← Matrix.smul_of, Matrix.mul_smul] }
  exact R.continuous_of_finiteDimensional

omit [_root_.NumberField.IsTotallyComplex E] in
theorem lmul_oneL (y : Lie E a) : lmul (oneL E a) y = y := one_mul (Matrix.of y)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_lmul_pair : Continuous fun p : Lie E a × Lie E a => lmul p.1 p.2 :=
  Continuous.matrix_mul (A := fun p : Lie E a × Lie E a => Matrix.of p.1) (B := fun p : Lie E a × Lie E a => Matrix.of p.2)
    continuous_fst continuous_snd

theorem chart_smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (ψ : GA E a → ℂ) (g : GA E a) :
    chart (smoothing ν α ψ) g = fun z => ∫ y, α y * chart ψ g (lmul z y) ∂ν := by
  funext z
  by_cases h : IsUnit (Matrix.of z)
  · obtain ⟨u, hu⟩ := h
    obtain rfl : z = toL u.val := hu.symm
    rw [chart_val, smoothing, chart_mul]
    rfl
  · have h' : ∀ y, chart ψ g (lmul z y) = 0 := fun y => by
      have hn : ¬ IsUnit (Matrix.of (lmul z y)) := fun hy => h (by
        have h2 := (Matrix.isUnit_iff_isUnit_det _).1 hy
        change IsUnit (Matrix.of z * Matrix.of y).det at h2
        rw [Matrix.det_mul] at h2
        exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h2))
      simp [chart, hn]
    simp only [h', mul_zero, integral_zero]
    simp [chart, h]

end SmoothingDeriv


open SmoothingDeriv in
theorem lieD_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ} (hψ : ψ ∈ Sm E a) (X : Lie E a) (g : GA E a) :
    lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  set f := chart ψ g with hf
  have hfs : ContDiffOn ℝ ∞ f (invSet E a) := hψ g
  have hfd : ContinuousOn (fderiv ℝ f) (invSet E a) :=
    hfs.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
  have hmul : ∀ z y, z ∈ invSet E a → y ∈ invSet E a → lmul z y ∈ invSet E a :=
    fun z y hz hy => IsUnit.mul hz hy
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 isOpen_invSet (oneL E a) isUnit_one
  have hr : 0 < ε / 2 := half_pos ε0
  have hball : Metric.closedBall (oneL E a) (ε / 2) ⊆ invSet E a :=
    (Metric.closedBall_subset_ball (half_lt_self ε0)).trans hε
  set K := (fun p : Lie E a × Lie E a => lmul p.1 p.2) '' (Metric.closedBall (oneL E a) (ε / 2) ×ˢ tsupport α)
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod hα.2.1.isCompact).image continuous_lmul_pair
  have hKs : K ⊆ invSet E a := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hmul _ _ (hball hp1) (hα.2.2 hp2)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hfd.mono hKs)
  let F : Lie E a → Lie E a → ℂ := fun z y => α y * f (lmul z y)
  let F' : Lie E a → Lie E a → (Lie E a →L[ℝ] ℂ) := fun z y => α y • (fderiv ℝ f (lmul z y)).comp (rmul y)
  have hcontOn : ∀ z ∈ invSet E a, ContinuousOn (fun y => f (lmul z y)) (invSet E a) := fun z hz =>
    hfs.continuousOn.comp (lmul z).continuous.continuousOn fun y hy => hmul z y hz hy
  have hF'c : Continuous (F' (oneL E a)) := by
    refine continuous_of_tsupport fun y hy => ?_
    have hy' : y ∈ invSet E a := hα.2.2 (tsupport_smul_subset_left _ _ hy)
    simp only [F', lmul_oneL]
    exact hα.1.continuous.continuousAt.smul
      ((hfd.continuousAt (isOpen_invSet.mem_nhds hy')).clm_comp continuous_rmul_fun.continuousAt)
  have hbound : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), ‖F' z y‖ ≤ ‖α y‖ * (C * ‖rmul y‖) := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp [F', h0]
    have hy : y ∈ tsupport α := subset_tsupport _ h0
    have hK : lmul z y ∈ K := ⟨(z, y), ⟨Metric.ball_subset_closedBall hz, hy⟩, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _ hK) (norm_nonneg _))) (norm_nonneg _)
  have hbi : Integrable (fun y => ‖α y‖ * (C * ‖rmul y‖)) ν :=
    (hα.1.continuous.norm.mul (continuous_const.mul continuous_rmul_fun.norm)).integrable_of_hasCompactSupport
      hα.2.1.norm.mul_right
  have hdiff : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), HasFDerivAt (fun z => F z y) (F' z y) z := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp only [F, F', h0, zero_mul, zero_smul]; exact hasFDerivAt_const 0 z
    have hy : y ∈ invSet E a := hα.2.2 (subset_tsupport _ h0)
    have hw : lmul z y ∈ invSet E a := hmul _ _ (hball (Metric.ball_subset_closedBall hz)) hy
    have h1 : HasFDerivAt f (fderiv ℝ f (lmul z y)) (rmul y z) :=
      ((hfs.contDiffAt (isOpen_invSet.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp z (rmul y).hasFDerivAt).const_mul (α y)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := F) (F' := F') (Metric.ball_mem_nhds _ hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz =>
      (hα.continuous_mul isOpen_invSet (hcontOn z (hball (Metric.ball_subset_closedBall hz)))).aestronglyMeasurable)
    (hα.integrable_mul ν isOpen_invSet (hcontOn _ isUnit_one)) hF'c.aestronglyMeasurable
    (.of_forall hbound) hbi (.of_forall hdiff)
  have hint : Integrable (F' (oneL E a)) ν :=
    hbi.mono' hF'c.aestronglyMeasurable (.of_forall fun y => hbound y _ (Metric.mem_ball_self hr))
  rw [lieD, chart_smoothing, ← hf, hmain.fderiv, ContinuousLinearMap.integral_apply hint, smoothing,
    ← integral_mul_fderiv_lmul_eq_dens ν hα X hfs]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [F', lmul_oneL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

theorem lieD_smoothing_eq_dens : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a,
    ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g :=
  fun _ _ _ _ _ ν _ _ hα _ hψ X g => lieD_smoothing ν hα hψ X g

end GlobalTheory.AutGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieFirst_of_lieSecond' : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  first | exact @GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | exact GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | (intros; apply GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftIntSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace GlobalTheory.IntDescend

theorem lift_units {Γ A B : Type} [Group Γ] [Monoid A] [Monoid B] (φ : A →* B) (hφ : Function.Injective φ)
    (f : Γ →* Bˣ) (hf : ∀ g, ((f g : Bˣ) : B) ∈ Set.range φ) : ∃ f' : Γ →* Aˣ, (Units.map φ).comp f' = f := by
  classical
  have h1 : ∀ g, φ (Function.invFun φ ((f g : Bˣ) : B)) = f g := fun g => Function.invFun_eq (hf g)
  have hu : ∀ g, Function.invFun φ ((f g : Bˣ) : B) * Function.invFun φ ((f g⁻¹ : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, mul_inv_cancel, map_one f, Units.val_one]
  have hv : ∀ g, Function.invFun φ ((f g⁻¹ : Bˣ) : B) * Function.invFun φ ((f g : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, inv_mul_cancel, map_one f, Units.val_one]
  refine ⟨MonoidHom.mk' (fun g => ⟨Function.invFun φ ((f g : Bˣ) : B), Function.invFun φ ((f g⁻¹ : Bˣ) : B), hu g, hv g⟩) ?_, ?_⟩
  · intro a b
    apply Units.ext
    apply hφ
    change φ (Function.invFun φ ((f (a * b) : Bˣ) : B)) = φ (Function.invFun φ ((f a : Bˣ) : B) * Function.invFun φ ((f b : Bˣ) : B))
    rw [h1, map_mul φ, h1, h1, map_mul f, Units.val_mul]
  · ext g
    exact h1 g

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def liftInt (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx.1⟩, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l LL ⟨x, hx.1⟩).2 hx.2⟩

theorem liftInt_spec (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) :
    ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) (liftInt LL x hx) = x := rfl

theorem incl_injective : Function.Injective ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

end GlobalTheory.IntDescend

namespace GlobalTheory.IntDescend

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Γ : Type) [Group Γ], (∀ (n : ℕ) (f : Γ →* GL (Fin n) (PadicAlgCl l)), (∀ g i j, (f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1 ∧ ‖(f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1) → ∃ f' : Γ →* GL (Fin n) ↥(OL LL), (Matrix.GeneralLinearGroup.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom))).comp f' = f) ∧ ∀ χ : Γ →* (PadicAlgCl l)ˣ, (∀ g, ((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 ∧ ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1) → ∃ ψ : Γ →* (↥(OL LL))ˣ, (Units.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).toMonoidHom).comp ψ = χ := by
  intro l _ LL Γ _
  refine ⟨?_, ?_⟩
  · intro n f hf
    have hinj : Function.Injective
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro M N h
      refine Matrix.ext fun i j => ?_
      apply incl_injective LL
      have := congrArg (fun P : Matrix (Fin n) (Fin n) (PadicAlgCl l) => P i j) h
      simpa only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hr : ∀ g, ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) ∈ Set.range
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro g
      refine ⟨Matrix.of fun i j => liftInt LL _ (hf g i j), ?_⟩
      ext i j
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact liftInt_spec LL _ (hf g i j)
    exact lift_units _ hinj f hr
  · intro χ hχ
    refine lift_units _ (incl_injective LL) χ ?_
    intro g
    exact ⟨liftInt LL _ ⟨(hχ g).1, (hχ g).2.le⟩, liftInt_spec LL _ _⟩

end GlobalTheory.IntDescend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPoint
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry TopologicalSpace CategoryTheory GlobalTheory.Points GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory.Adelic.GenericRel

theorem eval₂_mul_of_isHomogeneous {σ R A : Type} [CommSemiring R] [CommSemiring A] (φ : R →+* A)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : A) (v : σ → A) :
    eval₂ φ (fun i => c * v i) p = c ^ d * eval₂ φ v p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

variable {F : Type} [Field F] (S : LinSys F)

noncomputable def relFn (c : S.L.ι) {r e : ℕ} (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ)
    (a : Fin m → MvPolynomial (Fin r) F) : Γ(S.Y, S.L.U c) :=
  zfun th c ^ m + ∑ k, eval₂ ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤)))
    (fun i => (S.comb (u i)).f c) (a k) * zfun th c ^ (k : ℕ)

theorem valR_relFn {K : Type} [Field K] (x : Sp K ⟶ S.Y) (c : S.L.ι) (hx : ptOf x ∈ S.L.U c) {r e : ℕ}
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) :
    valR x (S.L.U c) (relFn S c u th m a) = valR x (S.L.U c) (zfun th c) ^ m + ∑ k, eval₂ (S.baseHom x)
      (fun i => valR x (S.L.U c) ((S.comb (u i)).f c)) (a k) * valR x (S.L.U c) (zfun th c) ^ (k : ℕ) := by
  have h := (le_iff_ptOf_mem x _).2 hx
  have hc : (valMap x _ h).hom.comp ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤))) = S.baseHom x := by
    ext b
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x b)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [relFn, valR_eq x _ h, map_add (f := _), map_sum, map_mul, map_pow, eval₂_comp_left, hc]
  rfl

theorem relation_of_generic (F : Type) [Field F] (S : LinSys F) (hY : AlgebraicGeometry.IsIntegral S.Y)
    (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y) (hη : IsGenericPoint η Set.univ)
    (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) (ha : ∀ k, (a k).IsHomogeneous (e * (m - k)))
    (h0 : S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
      (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0)
    (K : Type) [Field K] [Algebra F K] (x : S.Pt K) :
    S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) *
      S.powVal x.1 th ^ (k : ℕ) = 0 := by
  have hxU : ptOf x.1 ∈ S.L.U (S.chartAt (ptOf x.1)) := S.mem_chartAt _
  have hηU : ptOf (resPt η) ∈ S.L.U (S.chartAt (ptOf x.1)) := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (S.L.U _).isOpen).2 ⟨_, trivial, hxU⟩
  obtain ⟨c0, hc0, hv, hp⟩ := S.exists_frame_change (resPt η) _ hηU
  have hzero : valR (resPt η) _ (relFn S (S.chartAt (ptOf x.1)) u th m a) = 0 := by
    rw [valR_relFn S _ _ hηU, hp (e : ℤ) th]
    simp only [hv, zpow_natCast, eval₂_mul_of_isHomogeneous _ (ha _)]
    calc _ = c0 ^ (e * m) * (S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
          (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, ← pow_mul, show e * m = e * (m - k) + e * k by
            rw [← mul_add, Nat.sub_add_cancel k.2.le], pow_add]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hb : S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hm : η ∈ S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) :=
      (hη.mem_open_set_iff (S.Y.basicOpen _).isOpen).2 ⟨y, trivial, hy⟩
    rw [← ptOf_resPt η] at hm
    exact ((valR_ne_zero_iff (resPt η) hηU _).2 hm hzero).elim
  have hf : relFn S (S.chartAt (ptOf x.1)) u th m a = 0 := by
    haveI := hY
    exact (basicOpen_eq_bot_iff _).1 hb
  have key := valR_relFn S x.1 _ hxU u th m a
  rw [hf, valR_zero x.1 _ ((le_iff_ptOf_mem _ _).2 hxU)] at key
  have e2 : ∀ i, valR x.1 _ ((S.comb (u i)).f (S.chartAt (ptOf x.1))) =
      ∑ j, algebraMap F K (u i j) * S.coords x.1 j := fun i =>
    (S.val_comb x.1 (u i)).trans (by rw [LinSys.baseHom_ptOver])
  simp only [e2, LinSys.baseHom_ptOver] at key
  simp only [aeval_def]
  exact key.symm

end GlobalTheory.Adelic.GenericRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompatStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_galois_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  first | exact @GlobalTheory.GeomFrobChar.charpoly_geomFrob | exact GlobalTheory.GeomFrobChar.charpoly_geomFrob | (intros; apply GlobalTheory.GeomFrobChar.charpoly_geomFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2IsometryStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_linear_operator_l2_isometry : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.PolarSB.pairing_eq | exact GlobalTheory.PolarSB.pairing_eq | (intros; apply GlobalTheory.PolarSB.pairing_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLinesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  first | exact @GlobalTheory.RealLift.kLine_of_lineEx | exact GlobalTheory.RealLift.kLine_of_lineEx | (intros; apply GlobalTheory.RealLift.kLine_of_lineEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.place_split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @GlobalTheory.KFinLoc.split_or_inert | exact GlobalTheory.KFinLoc.split_or_inert | (intros; apply GlobalTheory.KFinLoc.split_or_inert <;> assumption)
end

