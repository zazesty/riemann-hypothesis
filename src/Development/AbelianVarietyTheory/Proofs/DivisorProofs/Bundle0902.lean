module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.SchwartzTranslate

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def transl (a : κ → AdeleRing (𝓞 F) F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun φ x := φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem SB_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] (b : X) {g : X → ℂ}
    (hg : g ∈ SB X) : (fun y => g (y + b)) ∈ SB X :=
  ⟨hg.1.comp_continuous (continuous_add_const b), hg.2.comp_homeomorph (Homeomorph.addRight b)⟩

theorem pureA_translate (a : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    transl F a (pureA F f g) = pureA F (f.compSubConstCLM ℂ (-fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1))
      (fun y => g (y + fun i => (a i).2)) := by
  funext x
  simp only [transl, LinearMap.coe_mk, AddHom.coe_mk, pureA, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  congr 2
  funext i
  exact map_add _ _ _

theorem schA_translate (a : κ → AdeleRing (𝓞 F) F) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x => φ (x + a)) ∈ schA F κ := by
  have key : schA F κ ≤ (schA F κ).comap (transl F a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show transl F a (pureA F f g) ∈ schA F κ
    rw [pureA_translate]
    exact Submodule.subset_span ⟨_, _, SB_translate _ hg, rfl⟩
  exact key hφ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ,
    (fun x => φ (x + a)) ∈ schA F κ :=
  fun F _ _ _ _ a φ hφ => schA_translate F a hφ

end GlobalTheory.SchwartzTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaBox

theorem thetaSum_boxFun : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  have s₁ := (thetaSum_summable_linear F κ).2.1 φ₁ h₁
  have s₂ := (thetaSum_summable_linear F κ').2.1 φ₂ h₂
  unfold thetaSum
  rw [tsum_mul_tsum_of_summable_norm s₁ s₂]
  rw [← (Equiv.sumArrowEquivProdArrow κ κ' F).symm.tsum_eq]
  rfl

end GlobalTheory.ThetaBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SecLift

section Lin

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]


end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dite_eq_left hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

end Act

end GlobalTheory.SecLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamilyStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BasePins

theorem orient_std_lev : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hT i hO
  exact ⟨GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hL (hO.2.tuple ()).half, hO.2.lift.std, hO.2.lift.lev⟩

end GlobalTheory.BasePins
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlacesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (exact GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (intros; apply GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserInvolution
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add (f := _), MulOpposite.unop_add]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_of_sym (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1 := by
    rw [← hβ, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e, one_mul]

end GlobalTheory.CentConj

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerSeparableCommutative
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_separable_commutative : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  first | (exact @GlobalTheory.CentSep.centraliser_comm_of_separable) | (exact GlobalTheory.CentSep.centraliser_comm_of_separable) | (intros; apply GlobalTheory.CentSep.centraliser_comm_of_separable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmulStatement
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  first | (exact @GlobalTheory.conj_one_tmul_charpoly) | (exact GlobalTheory.conj_one_tmul_charpoly) | (intros; apply GlobalTheory.conj_one_tmul_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSqStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_conj_extends_of_adjoin_absSq : ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M] (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) → ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧ σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  first | (exact @GlobalTheory.cm_conj_extends_of_adjoin) | (exact GlobalTheory.cm_conj_extends_of_adjoin) | (intros; apply GlobalTheory.cm_conj_extends_of_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoAtEqZero
section
open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coAt (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
  -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
    (1 : GL (Fin (a + a')) (Fv F v)).1)

theorem coAt_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h : u.map (piW (t.comp σ)) = 0) : coAt G t u = 0 := by
  unfold coAt; rw [h]; simp

end GlobalTheory.LinBarAt
end
end

