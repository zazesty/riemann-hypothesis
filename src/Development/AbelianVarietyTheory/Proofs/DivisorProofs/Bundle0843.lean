module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovolCong

theorem smul_mem_hat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (S T : Set (Fin n → E)) (b : E) (hb : ∀ x ∈ S, b • x ∈ T) :
    ∀ z ∈ GlobalTheory.AdLat.hat F S, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b) • z ∈ GlobalTheory.AdLat.hat F T := by
  intro z hz
  let φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E) :=
    DistribSMul.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)
  have hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩
    funext i
    simp only [φ, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hz

theorem inv_smul_mem {D : D7} (V : HSp D) (I : Ideal (𝓞 D.host.E)) (b : D.host.E)
    (hb : b ∈ (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (y : Fin V.rank → D.host.E)
    (hy : y ∈ (I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))) :
    b • y ∈ (I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  have hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V := by
    rw [hsub, Submodule.map_span_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [← inv_mul_cancel₀ hA]
      exact FractionalIdeal.mul_mem_mul hb ha
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hba
    have : f (a • x) = r • x := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ r hx
  have h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hf h1

theorem gen_mem {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E))
    (I : Ideal (𝓞 D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈
      GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)))
    (c : FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), c v ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v)
    (x : Fin V.rank → D.host.E) (hx : x ∈ GlobalTheory.Member.latC V) :
    K *ᵥ (fun i => c ⊗ₜ[D.host.F] x i) - (fun i => c ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z := by
    intro s z
    simp only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]
  have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key := Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))) h1 ?_ ?_
  · simp only [one_mul] at key
    exact key
  · intro m hm b hb
    have hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈
        GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)) := by
      refine AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩
      rw [hsub]
      exact Submodule.subset_span ⟨m, hm, x, hx, rfl⟩
    have h2 := smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)
    have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) -
        (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) := by
      have : (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ring
      rw [this, hψs]
      rfl
    rw [← e]
    exact h2
  · intro t t' ht ht'
    have : (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) =
        (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i)) := by
      funext i
      simp only [Pi.add_apply, add_mul, TensorProduct.tmul_add]
    beta_reduce at ht ht' ⊢
    rw [this, AddMonoidHom.map_add ψ]
    exact (GlobalTheory.AdLat.hat _ _).add_mem ht ht'

end GlobalTheory.CovolCong


open GlobalTheory.CovolCong in
theorem GlobalTheory.CovolCong.cong_latC_of_cong_latG : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V K I h
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤
      (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))).comap ψ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, x, hx, rfl⟩
    exact gen_mem V K I h c hc x hx
  intro z hz
  exact hle hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommute
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem supS_mul_comm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S →
    GeneralLinearGroup.map (pInf E) t = 1 →
    (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  intro E _ _ _ a S h t hh ht htS
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, ht, mul_one, one_mul]
  · ext i j w
    have key : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (h * t) =
        GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (t * h) := by
      rw [map_mul, map_mul]
      by_cases hw : w ∈ S
      · rw [htS w hw, mul_one, one_mul]
      · rw [hh w hw, mul_one, one_mul]
    have e : ((GeneralLinearGroup.map (pFin E) (h * t)).val i j) w =
        ((GeneralLinearGroup.map (pFin E) (t * h)).val i j) w :=
      congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.val i j) key
    rw [e]

end GlobalTheory.JSW.MirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpen
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi.OpenInv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def invSub (F : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, F (g * finGL E a k) = F g}
  one_mem' g := by simp
  mul_mem' {k l} hk hl g := by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' {k} hk g := by
    have := hk (g * finGL E a k⁻¹)
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    exact this.symm


variable (E a) in
def openInv : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsOpen (invSub F : Set (GL (Fin a) (Af E)))}
  zero_mem' := by
    have : invSub (0 : GA E a → ℂ) = ⊤ := by
      ext k; simp [invSub]
    show IsOpen ((invSub (0 : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E))) : Set (GL (Fin a) (Af E)))
    rw [this]; exact isOpen_univ
  add_mem' {F G} hF hG := by
    have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
    have hG' : IsOpen (invSub G : Set (GL (Fin a) (Af E))) := hG
    refine Subgroup.isOpen_mono (H₁ := invSub F ⊓ invSub G) ?_ (hF'.inter hG')
    intro k hk g
    simp only [Pi.add_apply]
    rw [hk.1 g, hk.2 g]
  smul_mem' c F hF := by
    refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ hF
    intro k hk g
    simp only [Pi.smul_apply]
    rw [hk g]

theorem rt_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) (h : GA E a) :
    (fun g => F (g * h)) ∈ openInv E a := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have hh : infGL E a y * finGL E a k = h := infGL_mul_finGL h
  have hc : Continuous fun u : GL (Fin a) (Af E) => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  let U : Subgroup (GL (Fin a) (Af E)) := (invSub F).comap (MulAut.conj k⁻¹).toMonoidHom
  have hU : (U : Set _) = (fun u : GL (Fin a) (Af E) => k⁻¹ * u * k) ⁻¹' (invSub F : Set _) := by
    ext u; simp [U, MulAut.conj_apply]
  have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
  refine Subgroup.isOpen_mono (H₁ := U) ?_ (by rw [hU]; exact hF'.preimage hc)
  intro u hu g
  have hu' : ∀ g, F (g * finGL E a (k⁻¹ * u * k)) = F g := by
    have hm : k⁻¹ * u * k ∈ invSub F := by
      have := Subgroup.mem_comap.1 hu; simpa [MulAut.conj_apply] using this
    exact hm
  change F (g * finGL E a u * h) = F (g * h)
  rw [← hu' (g * h), ← hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E a u) (infGL E a y), ← infGL_comm, mul_assoc, mul_inv_cancel_left]

theorem kerInf_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) {X : Type} [MeasurableSpace X]
    (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : kerInf ν k γ F ∈ openInv E a := by
  refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ (show IsOpen (invSub F : Set (GL (Fin a) (Af E))) from hF)
  intro u hu g
  change ∫ x, k x * F (g * finGL E a u * infGL E a (γ x)) ∂ν = ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
  congr 1; funext x
  rw [mul_assoc, ← infGL_comm, ← mul_assoc, hu]

theorem mem_openInv_of_mem {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ openInv E a := by
  have h := π.isSmooth_finPart ⟨φ, hφ⟩
  show IsOpen (invSub φ.1 : Set (GL (Fin a) (Af E)))
  have e : (invSub φ.1 : Set (GL (Fin a) (Af E))) = {k | π.finPart k ⟨φ, hφ⟩ = ⟨φ, hφ⟩} := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    exact ⟨fun hk => Subtype.ext (Subtype.ext (funext hk)), fun hk g => congrArg (fun ψ : π.V => ψ.1.1 g) hk⟩
  rw [e]; exact h

end GlobalTheory.JSW.MirSemi.OpenInv


open GlobalTheory.JSW.MirSemi.OpenInv in
theorem GlobalTheory.JSW.MirSemi.locSpan_openInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V →
    ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)),
      IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  intro E _ _ _ a S π φ hφ F hF
  have h := GlobalTheory.JSW.MirSemi.locSpan_le (V := openInv E a) (S := S) (mem_openInv_of_mem hφ)
    (fun F hF h _ => rt_mem_openInv hF h) (fun F hF X _ ν _ k γ _ => kerInf_mem_openInv hF ν k γ) hF
  exact ⟨invSub F, h, fun u hu g => hu g⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReduction
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mapMatrix_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) (w : InfinitePlace E) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (Matrix.of (secMatInf ρ j v)) =
      Matrix.of (secMat ρ (j w) (fun l => v l w)) := by
  ext i l; rfl

theorem isUnit_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : IsUnit (Matrix.of (secMatInf ρ j v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  intro w
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (Matrix.of (secMatInf ρ j v))
  rw [mapMatrix_secMatInf] at h
  have hu := isUnit_secMat ρ (j w) (hj w) (fun l => v l w) (hv w)
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  have h' : (Matrix.of (secMatInf ρ j v)).det w = (Matrix.of (secMat ρ (j w) (fun l => v l w))).det := h
  rw [h']
  exact hu

theorem secMatInf_mem_lev (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1) := by
  rw [mem_levSetInf, val_toGLInf (isUnit_secMatInf ρ j hj v hv)]
  intro i hi
  have hiρ : ρ < i := by rw [Fin.lt_def]; omega
  refine ⟨fun l hl => funext fun w => ?_, funext fun w => ?_⟩
  · change secMat ρ (j w) (fun l => v l w) i l = 0
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_neg hl.ne]
  · change secMat ρ (j w) (fun l => v l w) i i = 1
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_pos rfl]

theorem rowCutInf_apply (ρ : Fin n) (g : GL (Fin n) (Cinf E)) (w : InfinitePlace E) (l : Fin n) :
    rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) l w = rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) l := by
  unfold rowCutInf rowCut
  split_ifs <;> rfl

def secLinInf (ρ : Fin n) : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMatInf_eq_add (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) :
    secMatInf ρ j v = secMatInf ρ j 0 + secLinInf ρ v := by
  funext i l w
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMatInf, secMat, secLinInf, hl]
  · simp [secMatInf, secMat, secLinInf, hi]

theorem secMatInf_main : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  intro E _ _ n ρ j hj
  refine ⟨fun v hv => ⟨isUnit_secMatInf ρ j hj v hv, secMatInf_mem_lev ρ j hj v hv⟩, ?_, secLinInf ρ, secMatInf_eq_add ρ j⟩
  intro g hg hgj w
  set v := rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) with hvdef
  have hS := isUnit_secMatInf ρ j hj v hgj
  have hne : rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (j w) ≠ 0 := by
    rw [← rowCutInf_apply]; exact hgj w
  have hcomp : compGL w (toGLInf (Matrix.of (secMatInf ρ j v))) =
      toGL (Matrix.of (secMat ρ (j w) (rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))) := by
    have hu := isUnit_secMat ρ (j w) (hj w) _ hne
    apply Units.ext
    rw [val_toGL hu]
    ext i l
    rw [compGL_apply, val_toGLInf hS]
    change secMat ρ (j w) (fun l => v l w) i l = _
    congr 1
    funext l
    exact rowCutInf_apply ρ g w l
  rw [map_mul, map_inv, hcomp]
  exact (secMat_main n ρ (j w) (hj w)).2.1 (compGL w g) (hg w) hne

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroup
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem levSetInf_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ),
    (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧
    (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  intro E _ _ n r
  refine ⟨fun g hg h hh w => ?_, fun g hg w => ?_, fun u hu => ?_, ?_⟩
  · rw [map_mul]
    exact (levSet_closed_subgroup n r).1 _ (hg w) _ (hh w)
  · rw [map_inv]
    exact (levSet_closed_subgroup n r).2.1 _ (hg w)
  · obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    exact mem_levSetInf.2 fun i _ => ⟨fun j hj => h0 i j hj, h1 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) (Cinf E) =>
        (g : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
      fun i j => (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf E))).matrix_elem i j
    have hs : levSetInf E n r = {g : GL (Fin n) (Cinf E) | ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
          (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1} := Set.ext fun g => mem_levSetInf
    rw [hs]
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
    · exact isClosed_eq (hc i i) continuous_const

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := by
  exact @GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubF
section
open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.MBLow.Cl

def cubF {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) : ℂ :=
  (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) /
    (d.fr (x + y + z) * d.fr x * d.fr y * d.fr z)

end GlobalTheory.MBLow.Cl

end
end

