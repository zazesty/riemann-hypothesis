module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamily
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem measurable_htInf_comp {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun x => htInf (γ x) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isKerOpInf_comp_rapidFamInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η →
    ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ),
    (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) →
    (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) →
    IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  intro E _ _ n Z _ _ _ T hT X _ ν _ k γ η hfam S t χ hS hSk
  obtain ⟨X₀, m₀, ν₀, hν₀, k₀, γ₀, η₀, ⟨hk₀, hγ₀, hη₀, hint₀⟩, hT⟩ := hT
  obtain ⟨hγ, hjoint, hmom⟩ := hfam
  obtain ⟨hkj, hηj⟩ := hjoint X₀ γ₀ hγ₀
  have mη₀ : Measurable η₀ := measurable_dual hη₀
  have mηj : Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 := measurable_dual hηj
  have mht : Measurable fun x => htInf (γ x) := measurable_htInf_comp hγ
  have hrap : IsRapidFInf (ν₀.prod ν) (fun p : X₀ × X => k₀ p.1 * k (γ₀ p.1) p.2) (fun p => γ p.2)
      (fun p => η₀ p.1 + η (γ₀ p.1) p.2) := by
    refine ⟨(hk₀.comp measurable_fst).mul hkj, fun i j => (hγ i j).comp measurable_snd,
      fun z => ((hη₀ z).comp measurable_fst).add (hηj z), fun N => ?_⟩
    obtain ⟨C, M, hCM⟩ := hmom N
    let F : X₀ × X → ℝ := fun p => (‖k₀ p.1‖ * (1 + ‖η₀ p.1‖) ^ N) *
      (‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N)
    have mF : Measurable F := by
      have a1 : Measurable fun p : X₀ × X => k₀ p.1 := hk₀.comp measurable_fst
      have a2 : Measurable fun p : X₀ × X => η₀ p.1 := mη₀.comp measurable_fst
      have a3 : Measurable fun p : X₀ × X => htInf (γ p.2) := mht.comp measurable_snd
      exact (a1.norm.mul ((measurable_const.add a2.norm).pow_const N)).mul
        (hkj.norm.mul ((a3.mul (measurable_const.add mηj.norm)).pow_const N))
    have F0 : ∀ p, 0 ≤ F p := fun p => by
      have := htInf_pos' (γ p.2)
      positivity
    have hF : Integrable F (ν₀.prod ν) := by
      rw [integrable_prod_iff mF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun x₀ => ((hCM (γ₀ x₀)).1.const_mul (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N)), ?_⟩
      refine ((hint₀ (max N M)).const_mul (max C 0)).mono'
        (mF.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Filter.Eventually.of_forall fun x₀ => ?_)
      have e1 : ∫ y, ‖F (x₀, y)‖ ∂ν = (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N) *
          ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (F0 _))
      have I0 : 0 ≤ ∫ y, ‖F (x₀, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg I0, e1]
      have hq := (hCM (γ₀ x₀)).2
      have A0 : 0 ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N := by positivity
      have h1 : 1 ≤ htInf (γ₀ x₀) := le_of_eq_of_le rfl (by
        unfold htInf
        calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _)
      have h2 : (1 : ℝ) ≤ 1 + ‖η₀ x₀‖ := by linarith [norm_nonneg (η₀ x₀)]
      have p1 : (1 + ‖η₀ x₀‖) ^ N ≤ (1 + ‖η₀ x₀‖) ^ max N M := pow_le_pow_right₀ h2 (le_max_left _ _)
      have p2 : htInf (γ₀ x₀) ^ M ≤ htInf (γ₀ x₀) ^ max N M := pow_le_pow_right₀ h1 (le_max_right _ _)
      have hm : C * htInf (γ₀ x₀) ^ M ≤ max C 0 * htInf (γ₀ x₀) ^ max N M :=
        mul_le_mul (le_max_left _ _) p2 (by positivity) (le_max_right _ _)
      calc ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν
          ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * (max C 0 * htInf (γ₀ x₀) ^ max N M) :=
            mul_le_mul_of_nonneg_left (hq.trans hm) A0
        _ ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ max N M * (max C 0 * htInf (γ₀ x₀) ^ max N M) := by
            gcongr
        _ = max C 0 * (‖k₀ x₀‖ * (htInf (γ₀ x₀) * (1 + ‖η₀ x₀‖)) ^ max N M) := by rw [mul_pow]; ring
    refine hF.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((hk₀.comp measurable_fst).mul hkj).norm.mul (((mht.comp measurable_snd).mul
        (measurable_const.add ((mη₀.comp measurable_fst).add mηj).norm)).pow_const N)).aestronglyMeasurable
    · have hh := htInf_pos' (γ p.2)
      have hb : htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖) ≤
          (1 + ‖η₀ p.1‖) * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) := by
        have := mul_le_mul_of_nonneg_left (show 1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖ ≤ (1 + ‖η₀ p.1‖) * (1 + ‖η (γ₀ p.1) p.2‖) by
          nlinarith [norm_add_le (η₀ p.1) (η (γ₀ p.1) p.2), norm_nonneg (η₀ p.1), norm_nonneg (η (γ₀ p.1) p.2),
            mul_nonneg (norm_nonneg (η₀ p.1)) (norm_nonneg (η (γ₀ p.1) p.2))]) hh.le
        linarith
      have hp : (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N ≤
          (1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N :=
        (pow_le_pow_left₀ (by positivity) hb N).trans_eq (mul_pow _ _ _)
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N
          ≤ ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ *
              ((1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = F p := by simp only [F]; ring
  refine ⟨X₀ × X, inferInstance, ν₀.prod ν, inferInstance, _, _, _, hrap, ?_⟩
  intro W hW z g
  have hint := hrap.integrable hW z g
  show χ z * T (S W) z (g * t z) = _
  rw [integral_prod _ hint, hT (S W) (hS W hW) z (g * t z), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
  simp only
  rw [show χ z * (k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * S W (g * t z * γ₀ x₀)) =
      k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * (χ z * S W (g * t z * γ₀ x₀)) by ring, hSk W hW (γ₀ x₀) z g,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.add_apply, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKCentAf

theorem baseChange_centralizer_comm (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
      y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  intro y
  rw [← sub_eq_zero, had, hex' y]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hmap z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hmap z).symm⟩

theorem commute_of_centralizer (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [CommRing A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) (y z : k ⊗[K] B)
    (hy : y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y)
    (hz : z * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * z) : y * z = z * y := by
  obtain ⟨y', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent y).1 hy
  obtain ⟨z', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent z).1 hz
  rw [← map_mul, ← map_mul, mul_comm]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_iff_mem (P : Pair G) (y : G.C) :
    y * (P.γ : G.C) = (P.γ : G.C) * y ↔
      y ∈ Set.range ((Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro h
    have hy : y ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      simpa using h.symm
    rw [hcsa] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [hcsa]; exact w.2
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact (hw _ rfl).symm

theorem conj_commute (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t)
    (a : G.GAf) (ha : a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self)) :
    (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
      ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) *
        (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom P.γ with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C) := rfl
  have hδ : ((P.toAf x t hx P.self : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
  simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
  rw [hδ] at h1
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
    calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
      _ = U * (x⁻¹ * A * x) := by group
  rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]

theorem twCent_comm : ∀ {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
    ∀ a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self),
    ∀ b ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self), a * b = b * a := by
  intro p _ G P x t hx a ha b hb
  have hc := commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _ (cent_iff_mem P) _ _
    (conj_commute P x t hx a ha) (conj_commute P x t hx b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

end GlobalTheory.LKCentAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGram

theorem form_mem_span {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (T : Set (Fin n → R))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S) :
    ∀ x ∈ Submodule.span S T, ∀ y ∈ Submodule.span S T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact S.add_mem ha hb
    | smul c a _ ha =>
      have : ∑ i, ∑ j, σ (x i) * J i j * (c • a) j = (c : R) * ∑ i, ∑ j, σ (x i) * J i j * a j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        show _ * ((c : R) * a j) = _
        ring
      rw [this]; exact S.mul_mem c.2 ha
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
    exact S.add_mem ha hb
  | smul c a _ ha =>
    have : ∑ i, ∑ j, σ ((c • a) i) * J i j * y j = σ (c : R) * ∑ i, ∑ j, σ (a i) * J i j * y j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      show σ ((c : R) * a i) * _ * _ = _
      rw [map_mul]; ring
    rw [this]; exact S.mul_mem (hσ _ c.2) ha

theorem exists_unit {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) R) (H : Set (Fin n → R))
    (hβ : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).1.mulVec x i ∈ S)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S)
    (s s' : Fin m → Fin n → R) (hs : ∀ i, s i ∈ H) (hs' : ∀ i, s' i ∈ H)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, σ (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) S, S.subtype.mapMatrix G.1 = (β.1.map σ)ᵀ * J * β.1 := by
  have hcol : ∀ j, (fun i => β.1 i j) ∈ H := by
    intro j
    rw [hβ]
    intro k
    have : (β⁻¹).1.mulVec (fun i => β.1 i j) k = ((β⁻¹).1 * β.1) k j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have a1 : ∀ i j, ((β.1.map σ)ᵀ * J * β.1) i j ∈ S := by
    intro i j
    have := hH _ (hcol i) _ (hcol j)
    rw [Finset.sum_comm] at this
    simpa only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply] using this
  let P : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s i a
  let P' : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s' i a
  have hP : P * ((P'.map σ)ᵀ * J) = 1 := by
    ext a j
    rw [Matrix.one_apply, ← hd]
    rfl
  have a2 : ∀ i j, (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) i j ∈ S := by
    intro i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem ((hβ _).1 (hs k) i) (hσ _ ((hβ _).1 (hs' k) j))
  have hinv : (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) * ((β.1.map σ)ᵀ * J * β.1) = 1 := by
    have e : (((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ = (P'.map σ)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    calc _ = (β⁻¹).1 * (P * (((((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ) * J)) * β.1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, hP, Matrix.mul_one, Units.inv_mul]
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a2 i j⟩
  have hM : S.subtype.mapMatrix M = (β.1.map σ)ᵀ * J * β.1 := rfl
  have hM' : S.subtype.mapMatrix M' = ((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM', hinv])
  exact ⟨⟨M, M', mul_eq_one_comm.1 p2, p2⟩, hM⟩

theorem exists_unit_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : ℕ}
    (c : E → E) (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, σ s ∈ Formalism.L2.Herm.intAf F E)
    (hσι : ∀ x, σ (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (c x))
    (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hΛ : ∀ y ∈ Λ, ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, c (x i) * J i j * y j)
    (s s' : Fin m → Fin n → E) (hs : ∀ i, s i ∈ Λ ∧ s' i ∈ Λ)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, c (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) (Formalism.L2.Herm.intAf F E), (intGL F E n G).val =
      Formalism.UG.cT σ β.1 * J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.1 := by
  let ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)
  replace hσι : ∀ x, σ (ι x) = ι (c x) := hσι
  have hmem : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := fun x hx =>
    Submodule.subset_span ⟨x, hx, rfl⟩
  refine exists_unit (Formalism.L2.Herm.intAf F E) σ hσ (J.map ι) β
    (Formalism.L2.Herm.hatL (F := F) Λ) hβ ?_ (fun i a => ι (s i a)) (fun i a => ι (s' i a))
    (fun i => hmem _ (hs i).1) (fun i => hmem _ (hs i).2) ?_
  · refine form_mem_span _ σ hσ _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hΛ y hy x hx
    have : ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) = ι b := by
      rw [hb]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, RingHom.map_mul, hσι, Matrix.map_apply]
    show ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) ∈ _
    rw [this]
    exact (oToS F E b).2
  · intro a j
    have := congrArg ι (hd a j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, RingHom.map_mul, ← hσι, apply_ite ι, RingHom.map_one, RingHom.map_zero] at this
    exact this

theorem gram_unimodular : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ G : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), (intGL D.host.F D.host.E V.rank G).val = BadPlacesGoodCoefficients.gramIn V β := by
  intro D V β Λ N hB
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N ⟨1, by rw [pow_one]; exact hB⟩
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hsd
  exact exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int)
    (fun _ => rfl) V.gram β Λ hB.1 (fun y hy => (hsd.2 y).1 hy) s s' hs hd

end GlobalTheory.FrameGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
section
noncomputable section

open Matrix NumberField
open scoped TensorProduct Classical

namespace GlobalTheory.LKTrip.HTGroup

theorem span_real_embedding_places (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | (apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  simp only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

theorem psiR_pi_bijective (G : HTGroup p) :
    Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : ∀ x, Ψ x = fun v => G.psiR v x := fun x => rfl
  set S := Ψ.range with hS
  have hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) =
      fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a) := by
    intro a; funext v; rw [hΨ]; dsimp only; rw [psiR_tmul, one_smul, G.psi_F]
  let sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    { toFun := fun c v => Matrix.scalar (Fin G.n) (c v)
      map_add' := fun c d => by funext v; simp
      map_smul' := fun r c => by
        funext v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Matrix.scalar_apply, Matrix.scalar_apply]
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }
  have hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S := by
    have htop := span_real_embedding_places G.F
    have hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤
        (Subalgebra.toSubmodule S).comap sc := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)
    intro c
    exact hle (htop ▸ Submodule.mem_top)
  have hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S := by
    intro v₁ m
    have hspan := GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)
    have hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁)) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have : (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b) := by
        funext v
        rw [hΨ]
        by_cases h : v = v₁
        · subst h; simp [sc, psiR_tmul]
        · simp [sc, h, psiR_tmul]
      rw [this]; exact S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)
    | zero => simpa using S.zero_mem
    | add x y _ _ hx hy => rw [Pi.single_add]; exact S.add_mem hx hy
    | smul z x _ hx =>
      have : (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ z) * Pi.single v₁ x := by
        funext v
        by_cases h : v = v₁
        · subst h; simp [sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
        · simp [sc, h]
      rw [this]; exact S.mul_mem (hscS _) hx
  have hsurj : Function.Surjective Ψ := by
    intro y
    have : y ∈ S := by
      rw [← Finset.univ_sum_single y]
      exact Subalgebra.sum_mem _ fun v _ => hsingle v (y v)
    exact (AlgHom.mem_range _).1 this
  have hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero G.F]
    ring
  have hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← hc]; ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩

end GlobalTheory.LKTrip.HTGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviRestrictionStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_levi_restriction : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)), ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  first | exact @GlobalTheory.SliceTwo.slice_kfin | exact GlobalTheory.SliceTwo.slice_kfin | (intros; apply GlobalTheory.SliceTwo.slice_kfin <;> assumption)
end

