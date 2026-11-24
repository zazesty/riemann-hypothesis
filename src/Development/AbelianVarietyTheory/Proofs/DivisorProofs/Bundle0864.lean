module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrder
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem rep_conj_of_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  classical
  intro p _ D g ρ ρ' htr
  obtain ⟨φ, hφ, hspan⟩ := _root_.GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix p D
  haveI := D.freeO
  haveI := D.finO
  have hdim : Module.finrank ℂ ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) = Module.finrank ℤ D.O := by
    rw [Module.finrank_pi_fintype, D.rankO]
    simp [Module.finrank_matrix, NumberField.Embeddings.card]
    ring
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq D.O _ _ φ ρ hspan hdim
  obtain ⟨σ', hσ'⟩ := _root_.GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq D.O _ _ φ ρ' hspan hdim
  have key : ∀ (s : ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (f : (D.F →+* ℂ) → ℂ),
      (s (fun τ => Matrix.scalar (Fin D.m) (f τ))).trace = ∑ τ, f τ * (s (Pi.single τ 1)).trace := by
    intro s f
    have : (fun τ => Matrix.scalar (Fin D.m) (f τ)) = ∑ τ, f τ • (Pi.single τ 1 : (D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) := by
      ext τ i j
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single τ]
      · simp [Pi.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, Matrix.trace_sum]
    simp [map_smul, Matrix.trace_smul]
  let χ : (D.F →+* ℂ) → (𝓞 D.F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro τ τ' h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
    ext x
    exact DFunLike.congr_fun h x
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hlin
  have heq : ∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace := by
    have := hlin (fun τ => (σ (Pi.single τ 1)).trace - (σ' (Pi.single τ 1)).trace) (by
      funext c
      have h1 := htr c
      have hφ' : φ (algebraMap (𝓞 D.F) D.O c) = fun τ => Matrix.scalar (Fin D.m) (τ (c : D.F)) := funext (hφ c)
      rw [← hσ, ← hσ', hφ', key, key] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      simp only [χ, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1)
    intro τ
    exact sub_eq_zero.mp (this τ)
  exact _root_.GlobalTheory.conj_of_trace_central_idem_eq (D.F →+* ℂ) D.m g D.m_pos σ σ' heq |>.imp fun h hh => ⟨hh.1, fun a => by rw [← hσ, ← hσ']; exact hh.2 _⟩

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW
open scoped FourierTransform

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IsRapidFamInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ) :
    Prop :=
  (∀ i j, Measurable fun x =>(γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E)),
    (∀ i j, Measurable fun x =>(γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) →
      Measurable (fun p : X₀ × X =>k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X =>η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x =>‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htInf q ^ M

def sandCLMInf (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    (Fin n → Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>(A * Matrix.of x * B) i j
      map_add' := fun x y =>by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x =>by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

theorem sandCLMInf_apply (A B : Matrix (Fin n) (Fin n) (Cinf E)) (x : Fin n → Fin n → Cinf E) (i j : Fin n) :
    sandCLMInf A B x i j = (A * Matrix.of x * B) i j := rfl

def jacInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ := ∏ w : InfinitePlace E, Complex.normSq (x.det w) ^ n


open Classical in
def secKInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q then
    ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEtaInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → Cinf E))
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)).comp L))

theorem jacInf_mul (x y : Matrix (Fin n) (Fin n) (Cinf E)) : jacInf (x * y) = jacInf x * jacInf y := by
  simp only [jacInf, Matrix.det_mul, Pi.mul_apply, map_mul, mul_pow, Finset.prod_mul_distrib]

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOn
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin.Holo

open Matrix
open scoped ComplexOrder

noncomputable section

theorem differentiable_det {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : Type*} [Fintype n]
    [DecidableEq n] (f : F → Matrix n n ℂ) (hf : ∀ i j, Differentiable ℂ fun x => f x i j) :
    Differentiable ℂ fun x => (f x).det := by
  simp only [Matrix.det_apply']
  fun_prop

theorem det_block_ne {r p : ℕ} (hp : p ≤ r) (m : Matrix (Fin r) (Fin r) ℂ)
    (hpos : ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp)).PosDef) :
    (m.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro hdet
  set A := m.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hdc : (A.map (starRingEnd ℂ)).det = 0 := by
    rw [show A.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix A from rfl, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdc
  have h := hpos.dotProduct_mulVec_pos hv
  set u : Fin r → ℂ := fun k => ∑ b, starRingEnd ℂ (m k (Fin.castLE hp b)) * v b with hu_def
  have hu : ∀ i : Fin p, u (Fin.castLE hp i) = 0 := fun i => by
    have := congrFun hAv i
    simpa [hA, Matrix.mulVec, dotProduct, u] using this
  have hq : star v ⬝ᵥ ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp) *ᵥ v) =
      ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, mulVec, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, hu_def, map_sum, map_mul, Complex.conj_conj,
      Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]
    ring
  have hq' : ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) =
      ((∑ k : Fin r, sgn p (k : ℕ) * Complex.normSq (u k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hq, hq', Complex.zero_lt_real] at h
  refine absurd h (not_lt.2 (Finset.sum_nonpos fun k _ => ?_))
  by_cases hk : (k : ℕ) < p
  · have h0 : u k = 0 := by
      have := hu ⟨k, hk⟩
      rwa [show Fin.castLE hp ⟨k, hk⟩ = k from Fin.ext rfl] at this
    simp [h0]
  · simp only [sgn, if_neg hk]
    nlinarith [Complex.normSq_nonneg (u k)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_Mx₂₂_ne (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) : (KU.Mx X x0 x τ).toBlocks₂₂.det ≠ 0 := by
  have h0 := ExF.det_ne_of_orth X ho τ
  set m := (mat x0 τ)⁻¹ * mat x τ with hm
  have hxm : mat x τ = mat x0 τ * m := by
    rw [hm, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 h0)]
  have hg : gram τ.1 X.Gm (mat x τ) = mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ) := by
    rw [hxm, FrameDegreeData.gram_mul, ho τ]
  have hpos := X.gramPos_posDef hx τ
  rw [Data.gramPos, hg] at hpos
  have hb : (KU.Mx X x0 x τ).toBlocks₂₂ = m.submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
    ext i j
    simp [KU.Mx, KU.tl, Matrix.toBlocks₂₂, KU.eT_inr, m]
  rw [hb]
  exact det_block_ne X.p0_le m hpos

theorem differentiable_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i j) :
    Differentiable ℂ fun x : Frame X.Ψ r => KU.Mx X x0 x τ i j := by
  simp only [KU.Mx, KU.tl, Matrix.submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

theorem qS_differentiableOn (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (k : ℕ) :
    DifferentiableOn ℂ (qS X x0 k) X.dom := by
  have hd1 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).det := fun τ =>
    differentiable_det _ (differentiable_Mx X x0 τ)
  have hd2 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det := fun τ =>
    differentiable_det (fun x => (KU.Mx X x0 x τ).toBlocks₂₂) fun i j =>
      differentiable_Mx X x0 τ (Sum.inr i) (Sum.inr j)
  have hq : qS X x0 k = ∏ τ, fun x : Frame X.Ψ r =>
      ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k := by
    funext x
    simp [qS, Finset.prod_apply]
  rw [hq]
  refine Finset.prod_induction _ (fun g : Frame X.Ψ r → ℂ => DifferentiableOn ℂ g X.dom)
    (fun a b ha hb => ha.mul hb) (differentiableOn_const 1) fun τ _ => ?_
  have hne : ∀ x ∈ X.dom, (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (det_Mx₂₂_ne X ho hx τ)
  have h1 := (hd1 τ).differentiableOn (s := X.dom)
  have h2 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
    ((hd2 τ).differentiableOn).pow 2
  have h3 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom := by
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv hne)
  exact h3.pow k

theorem qS_holomorphicOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r),
    IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom :=
  fun _ _ _ _ _ X x0 ho k => qS_differentiableOn X x0 ho k

end

end GlobalTheory.ScalarPoin.Holo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorel
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

noncomputable section

theorem det_ratio_pow_mul_borel_eq_weight_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (k : ℕ) (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    ((M * KU.tl X (mat b τ)).det / (M * KU.tl X (mat b τ)).toBlocks₂₂.det ^ 2) ^ k =
      (∏ i, b τ i i ^ laS X k τ i) * (M.det / M.toBlocks₂₂.det ^ 2) ^ k := by
  set T := KU.tl X (mat b τ) with hT
  have h22 : (M * T).toBlocks₂₂ = M.toBlocks₂₂ * T.toBlocks₂₂ := by
    rw [KU.toBlocks₂₂_mul, KU.tl_bor₁₂ X hb τ, Matrix.mul_zero, zero_add]
  set D1 : ℂ := ∏ j : Fin (r - X.p0), b τ (KU.eT X (Sum.inl j)) (KU.eT X (Sum.inl j)) with hD1
  set D2 : ℂ := ∏ i : Fin X.p0, b τ (KU.eT X (Sum.inr i)) (KU.eT X (Sum.inr i)) with hD2
  have hD2ne : D2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => FrameDegreeData.bdiag_ne X hb τ _
  have hdetT : T.det = D1 * D2 := by
    have ht : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
    rw [hT, KU.tl, Matrix.det_submatrix_equiv_self, Matrix.det_of_upperTriangular ht,
      ← Fintype.prod_equiv (KU.eT X) (fun s => mat b τ (KU.eT X s) (KU.eT X s)) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    rfl
  have hdetT22 : T.toBlocks₂₂.det = D2 := by
    have ht : T.toBlocks₂₂.BlockTriangular id := by
      intro i j hij
      simp only [hT, KU.tl, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, KU.eT_inr]
      exact (hb τ).2 _ _ (show (Fin.castLE X.p0_le j : ℕ) < Fin.castLE X.p0_le i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    rfl
  have hchar : (∏ i, b τ i i ^ laS X k τ i) = D1 ^ k * (D2 ^ k)⁻¹ := by
    rw [← Fintype.prod_equiv (KU.eT X) (fun s => b τ (KU.eT X s) (KU.eT X s) ^ laS X k τ (KU.eT X s)) _
      (fun _ => rfl), Fintype.prod_sum_type, hD1, hD2, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have : X.p0 ≤ (KU.eT X (Sum.inl j) : ℕ) := by simp [KU.eT]
      simp [laS, this]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : ¬ X.p0 ≤ (KU.eT X (Sum.inr i) : ℕ) := by simp [KU.eT]
      simp [laS, this, zpow_neg]
  rw [Matrix.det_mul, h22, Matrix.det_mul, hdetT, hdetT22, hchar, ← inv_pow, ← mul_pow, ← mul_pow]
  congr 1
  have hc : D2 * (D2 ^ 2)⁻¹ = D2⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hD2ne, one_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_inv]
  calc M.det * (D1 * D2) * ((M.toBlocks₂₂.det ^ 2)⁻¹ * (D2 ^ 2)⁻¹)
      = D1 * (D2 * (D2 ^ 2)⁻¹) * (M.det * (M.toBlocks₂₂.det ^ 2)⁻¹) := by ring
    _ = _ := by rw [hc]

theorem qS_rmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  intro E _ _ _ r X x0 k x b hb
  unfold qS bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [KU.Mx_rmul]
  exact det_ratio_pow_mul_borel_eq_weight_prod X k b hb τ _

end

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : Set (GA E a) :=
  {p | ∃ u ∈ NA (E := E) (a := a), ∃ k ∈ K, ∃ y : GL (Fin a) (Cinf E), p = u * q * finGL E a k * infGL E a y}

theorem self_mem_cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : q ∈ cell K q :=
  ⟨1, ⟨fun i j h => by simp [Matrix.one_apply_ne (Fin.ne_of_gt h)], fun i => by simp⟩, 1, K.one_mem, 1, by simp⟩

end GlobalTheory.JSW.MirPatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem sig_iterate_apply (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r k : ℕ)
    (g : GL (Fin n) (Kn p K r)) (i j : Fin n) :
    (((⇑(sig p K n r))^[k] g : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j
      = (⇑(frobR p K r))^[k] ((g : Matrix (Fin n) (Fin n) (Kn p K r)) i j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sig_iterate_r : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (Kn p K r),
    (⇑(sig p K n r))^[r] g = g := by
  intro p _ K hK n r hr g
  ext i j
  rw [sig_iterate_apply]
  rw [_root_.GlobalTheory.LKLoc.frobR_iterate_self p K hK r hr]

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigKQFixedEqInclK
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _)]

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.AffineCurve

theorem subsingleton_of_three_le : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n →
    Subsingleton (Ht q (sp B) n i) := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · exact GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B (GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB) (tw q i) n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    suffices h : ∀ x : Ht q (sp B) (m + 1) i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    obtain ⟨_, _⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    have h1 : pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 :=
      (GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK (m + 1) i (by omega)).elim _ _
    obtain ⟨f, hf0, hfu, hxf⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB (m + 1) i x h1
    obtain ⟨A', _, _, _, hA', hxA'⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf0 hfu (m + 1) i (by omega) x
    obtain ⟨δ, hex, hkill⟩ := GlobalTheory.T.mayer_vietoris_exact_etale q B A' f hA' m i
    obtain ⟨z, rfl⟩ := (hex x).mp (by simp [hxf, hxA'])
    obtain ⟨A'', _, _, _, φ, hA'', hz⟩ := GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood q k B hq f hf0 hfu A' hA' m i (by omega) z
    exact hkill A'' φ hA'' z hz

end GlobalTheory.EtC.AffineCurve
end

