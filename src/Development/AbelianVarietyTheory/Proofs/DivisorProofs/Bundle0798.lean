module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurPolar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_of_diag (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a b s t : ℂ} (ha : IsMultIP M μ 𝓕 T T a) (hb : IsMultIP M μ 𝓕 T' T' b)
    (hs : IsMultIP M μ 𝓕 (T + T') (T + T') s)
    (ht : IsMultIP M μ 𝓕 (T + Complex.I • T') (T + Complex.I • T') t) :
    IsMultIP M μ 𝓕 T T' ((1 / 2) * ((s - a - b) - Complex.I * (t - a - b))) := by
  intro v v'
  obtain ⟨ia, ea⟩ := ha v v'
  obtain ⟨ib, eb⟩ := hb v v'
  obtain ⟨is, es⟩ := hs v v'
  obtain ⟨it, et⟩ := ht v v'
  have e : (fun g => star (T v g) * T' v' g) =
      fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
        - star (T v g) * T v' g - star (T' v g) * T' v' g)) := by
    funext g
    show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g)
        - star (T v g) * T v' g - star (T' v g) * T' v' g))
    have hI : star Complex.I = - Complex.I := by simp
    rw [star_add, star_add, star_mul, hI]
    have h2 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g
      - Complex.I * star (T' v g) * T' v' g) * h2
  have i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕) :=
    is.sub ia
  have i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
      - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i1.sub ib
  have i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g) (μ.restrict 𝓕) := it.sub ia
  have i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i3.sub ib
  have i5 := i4.const_mul Complex.I
  rw [e]
  refine ⟨(i2.sub i5).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib,
    integral_sub is ia, integral_sub it ia, ea, eb, es, et]
  ring

theorem isMultiplicityInner_inner : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  intro D V S M μ 𝓕 HM U h x y
  have hip := h.2.2
  have hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := hip z z
      unfold ipM at this
      rw [dite_eq_right hn] at this
      exact hz (inner_self_eq_zero.1 this)
  rw [hip]
  apply ipM_spec
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  exact ⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

end GlobalTheory.SchurPolar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
section
noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamily
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.BaseVacuum

theorem sum_posE {M : Type} [AddCommMonoid M] (n n' : ℕ) (f : Fin (n' * 2) → Fin (n * 2) → M) :
    ∑ i, ∑ j, f i j = ∑ p : (Fin n' × Fin n) × Fin 4, f (posE n n' p).1 (posE n n' p).2 := by
  rw [← Fintype.sum_prod_type']
  exact ((posE n n').sum_comp (fun x => f x.1 x.2)).symm

theorem putB_posE (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E)
    (p : (Fin n' × Fin n) × Fin 4) :
    putB D k x (posE n n' p).1 (posE n n' p).2 = if p.1 = k then x p.2 else 0 := by
  simp [putB]

theorem hYY_putB (D : D7) {n n' : ℕ} (k k' : Fin n' × Fin n) (x y : Fin 4 → D.host.E) :
    TaylorLogMetric.hYY D (putB D k x) (putB D k' y) =
      if k = k' then Algebra.trace D.host.K D.host.E (∑ a, x a * D.host.conj (y a)) else 0 := by
  unfold TaylorLogMetric.hYY
  rw [sum_posE]
  simp only [putB_posE]
  rw [Fintype.sum_prod_type]
  split_ifs with h
  · subst h
    rw [Fintype.sum_eq_single k]
    · simp
    · intro k'' hk
      simp [hk]
  · rw [Finset.sum_eq_zero, map_zero]
    intro k'' _
    apply Finset.sum_eq_zero
    intro a _
    by_cases h1 : k'' = k
    · subst h1
      simp [Ne.symm h, h]
    · simp [h1]

end GlobalTheory.BaseVacuum

namespace GlobalTheory.BaseVacuum

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem gamma_g_xv (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : B.γ₀.g (xv B w) = Pi.single w 1 := by
  simp [xv]

theorem trace_xv (B : Base D cc δ) (w w' : Fin 4 × D.what₂.Tau) :
    Algebra.trace D.host.K D.host.E (∑ a, xv B w a * D.host.conj (xv B w' a)) = if w = w' then 1 else 0 := by
  apply (algebraMap D.host.K D.host.E).injective
  have h := B.γ₀.isom (xv B w) (xv B w')
  rw [gamma_g_xv, gamma_g_xv] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← h]
  simp only [Pi.single_apply]
  by_cases hw : w = w'
  · subst hw
    simp
  · rw [if_neg hw, map_zero]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : u = w
    · subst hu
      simp [hw]
    · simp [hu]

theorem orthonormal_bas (B : Base D cc δ) (n n' : ℕ) : TaylorLogMetric.Orthonormal D (bas B n n') := by
  intro i j
  unfold bas
  rw [hYY_putB]
  by_cases hk : (ixE D n n' i).1 = (ixE D n n' j).1
  · rw [if_pos hk, trace_xv]
    congr 1
    apply propext
    constructor
    · intro h
      exact (ixE D n n').injective (Prod.ext hk h)
    · intro h
      rw [h]
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (by rw [h])


set_option synthInstance.maxHeartbeats 200000 in
theorem sum_g_smul_xv (B : Base D cc δ) (y : Fin 4 → D.host.E) :
    ∑ w, B.γ₀.g y w • xv B w = y := by
  have h1 : ∑ w, B.γ₀.g y w • (Pi.single w (1 : D.host.K) : Fin 4 × D.what₂.Tau → D.host.K) = B.γ₀.g y := by
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ w, B.γ₀.g y w • xv B w = B.γ₀.g.symm (∑ w, B.γ₀.g y w • Pi.single w (1 : D.host.K)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, xv]
    _ = y := by rw [h1, LinearEquiv.symm_apply_apply]

theorem matrix_eq_sum_putB (B : Base D cc δ) (n n' : ℕ) (M : Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E) :
    M = ∑ k : Fin n' × Fin n, ∑ w : Fin 4 × D.what₂.Tau,
      B.γ₀.g (fun a => M (posE n n' (k, a)).1 (posE n n' (k, a)).2) w • putB D k (xv B w) := by
  ext i j
  obtain ⟨p, hp⟩ := (posE n n').surjective (i, j)
  have hi : i = (posE n n' p).1 := by rw [hp]
  have hj : j = (posE n n' p).2 := by rw [hp]
  subst hi hj
  simp only [Matrix.sum_apply, Matrix.smul_apply, putB_posE, smul_ite, smul_zero]
  rw [Fintype.sum_eq_single p.1]
  · simp only [if_true]
    have := congrFun (sum_g_smul_xv B (fun a => M (posE n n' (p.1, a)).1 (posE n n' (p.1, a)).2)) p.2
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply] at this
    rw [this]
  · intro k hk
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (Ne.symm hk)]

theorem onB_bas : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.OnB D (bas B n n') := by
  intro D cc δ B n n'
  refine ⟨orthonormal_bas B n n', ?_⟩
  refine eq_top_iff.2 fun M _ => ?_
  rw [matrix_eq_sum_putB B n n' M]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨(ixE D n n').symm (k, w), ?_⟩
  simp [bas]

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAMulEqZeroIffSnd
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA' (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA' (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd' (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', zero_mul]
    · rw [map_mul, map_zero, sndA_pairA', h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst' (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA', zero_mul]

def incFin : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA', add_zero])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA'])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply])

def incInf : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA'])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA', add_zero])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply, smul_zero])

theorem incFin_sndA (a : AF F) : incFin F (sndA F a) = pairA F 0 1 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', zero_mul]; rfl) (by rw [map_mul, sndA_pairA', one_mul]; rfl)

theorem incInf_fstA (a : AF F) : incInf F (fstA F a) = pairA F 1 0 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', one_mul]; rfl) (by rw [map_mul, sndA_pairA', zero_mul]; rfl)

end Ad

section Coord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secFin : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incFin F) LinearMap.id

def secInf : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incInf F) LinearMap.id

variable {F E}

theorem secFin_finPartF (z : AF F ⊗[F] E) : secFin F E (finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPartF F E).map_zero, (secFin F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secFin, TensorProduct.map_tmul, LinearMap.id_apply, incFin_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(finPartF F E).map_add, (secFin F E).map_add, hx, hy, smul_add]

theorem secInf_infPartF (z : AF F ⊗[F] E) : secInf F E (infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPartF F E).map_zero, (secInf F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secInf, TensorProduct.map_tmul, LinearMap.id_apply, incInf_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(infPartF F E).map_add, (secInf F E).map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) : finPartF F E (pairA F 0 1 • z) = finPartF F E z := by
  rw [Algebra.smul_def, (finPartF F E).map_mul]
  have : finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA']
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) : infPartF F E (pairA F 1 0 • z) = infPartF F E z := by
  rw [Algebra.smul_def, (infPartF F E).map_mul]
  have : infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA']
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) : finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secFin_finPartF, h, (secFin F E).map_zero]
  · intro h; rw [← finPartF_smul, h, (finPartF F E).map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) : infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secInf_infPartF, h, (secInf F E).map_zero]
  · intro h; rw [← infPartF_smul, h, (infPartF F E).map_zero]

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_fin' {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd' F (u l)

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_inf' {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst' F (u l)

theorem coordF (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] VA F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPartF F E) = 0 ↔ fin (e x).1 = 0 ∧ fin (e x).2 = 0) ∧
      (∀ x, x.map (infPartF F E) = 0 ↔ inf (e x).1 = 0 ∧ inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin n → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_fin', ← smul_vec_fin', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff
  · have key : x.map (infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_inf', ← smul_vec_inf', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff

end Coord

end GlobalTheory.ThetaTransformF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem pureLift_step : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  intro GM p hp R R₀ _ _ π hR hπ h2 g g' A B _ _ A₀ B₀ _ _ i j hA hgA hB hgB hi hj U V U₀ V₀ _ _ _ _ eU eV
    r s r' s' hU hV hu f₀ _ ef₀
  have h2' : RingHom.ker π ^ 2 = 0 := by rw [Ideal.zero_eq_bot]; exact h2
  obtain ⟨Hc, -, Hl⟩ := GM p hp R hR _ (GlobalTheory.Cris.divided₂ h2') (GlobalTheory.Cris.isDPNilpotent_squareZero h2') R₀ π hπ rfl
  set κ := GlobalTheory.Cris.divided₂ h2'
  have inj := (Hc.crysToDR_bijective hi hA hgA).1
  have key : ∀ d ∈ GlobalTheory.DeRham.liftFil κ hi, GlobalTheory.DeRham.push κ (spMap π) f₀ d ∈ GlobalTheory.DeRham.liftFil κ hj := by
    intro d hd
    have hd' : GlobalTheory.DeRham.crysToDR κ hi d ∈ GlobalTheory.DeRham.Fil A := hd
    have h1 : GlobalTheory.DeRham.push κ (spMap π) U₀ d = r • d := by
      apply inj
      rw [GlobalTheory.DeRham.crysToDR_push κ hi hi U₀ U eU, map_smul]
      exact hU.1 _ hd'
    have h3 : GlobalTheory.DeRham.push κ (spMap π) V₀ (GlobalTheory.DeRham.push κ (spMap π) f₀ d)
        = r • GlobalTheory.DeRham.push κ (spMap π) f₀ d := by
      have := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) U₀ f₀)
      have h4 := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) f₀ V₀)
      simp only [LinearMap.comp_apply] at this h4
      rw [← h4, ← GlobalTheory.DeRham.push_congr κ (spMap π) ef₀, this, h1, map_smul]
    show GlobalTheory.DeRham.crysToDR κ hj _ ∈ GlobalTheory.DeRham.Fil B
    refine IsPure.mem_Fil hV hu ?_
    rw [← GlobalTheory.DeRham.crysToDR_push κ hj hj V₀ V eV, h3, map_smul]
  obtain ⟨f, ⟨hf, ef⟩, uf⟩ := Hl g A₀ A i hi hA hgA g' B₀ B j hj hB hgB f₀ key
  refine ⟨f, hf, ef, ?_, fun f' hf' ef' => uf f' ⟨hf', ef'⟩⟩
  have e1 : i ≫ (U ≫ f).left = (U₀ ≫ f₀).left ≫ j := by
    simp only [Over.comp_left, ← Category.assoc, eU]
    simp only [Category.assoc, ef]
  have e2 : i ≫ (f ≫ V).left = (U₀ ≫ f₀).left ≫ j := by
    rw [Over.comp_left, ← Category.assoc, ef, Category.assoc, eV, ← Category.assoc, ← Over.comp_left, ← ef₀]
  exact Hl.unique hi hA hgA hj hB hgB (U₀ ≫ f₀) e1 e2

end GlobalTheory
end
end

