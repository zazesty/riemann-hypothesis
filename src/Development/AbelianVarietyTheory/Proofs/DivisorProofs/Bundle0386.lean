module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibre
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory Matrix Topology

namespace GlobalTheory.RankFibre

theorem X0_mul_X0_transpose (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)) *
      (GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]

theorem isUnit_of_rank_mul_X0 {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by
  have h1 : A.rank = Fintype.card (Fin a) := by
    refine le_antisymm (by simpa using A.rank_le_width) ?_
    simpa [h] using Matrix.rank_mul_le_left A (GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)))
  have hli : LinearIndependent k A.row := by
    rw [rank_eq_finrank_span_row] at h1
    rw [linearIndependent_iff_card_eq_finrank_span, eq_comm]; exact h1
  exact Matrix.linearIndependent_row_iff_isUnit.1 hli

theorem integrable_fibre_integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
    GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
    MeasureTheory.Integrable (fun g : GL (Fin a) k =>
      Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
        (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hl, hK⟩, hrk⟩ := hΦ
  set X0 := GlobalTheory.SplitFlip.X0 (k := k) (finSumFinEquiv (m := a) (n := b)) with hX0
  have hc1 : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X0) :=
    hl.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hc2 := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hc3 : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hcont := ((hc1.mul hc2).mul hc3).continuous

  set D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X0) ≠ 0} with hD
  have hDc : IsClosed D := by
    exact (hl.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X0 from continuous_id.matrix_mul continuous_const)
  have hDsub : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X0, subset_tsupport _ hA, ?_⟩
    show A * X0 * X0ᵀ = A
    rw [Matrix.mul_assoc, hX0, X0_mul_X0_transpose, Matrix.mul_one]
  have hDcpt : IsCompact D :=
    (hK.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hDc hDsub
  have hDr : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hr : (A * X0).rank = a := by
      by_contra hne
      exact hA (hrk _ hne)
    exact ⟨(isUnit_of_rank_mul_X0 A hr).unit, rfl⟩
  have hS : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hDcpt hDr
  have hcs : HasCompactSupport fun g : GL (Fin a) k => Φ (g.val * X0) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hS fun g hg => ?_
    have : Φ (g.val * X0) = 0 := not_not.1 hg
    simp [this]
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  exact hcont.integrable_of_hasCompactSupport (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) hcs

end GlobalTheory.RankFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulIterPartialDerivEqNegPow
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem integrable_mul_of_tsupport_subset {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hc : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hs h)
      have h0 : (fun x => f x * g x) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).1 hx'] with y hy
        simp [hy]
      exact (continuousAt_congr h0).2 continuousAt_const
  exact hc.integrable_of_hasCompactSupport hgc.mul_left

theorem integral_mul_partial_eq_neg {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (j : Fin d)
    {u ψ : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x (ev j) = - ∫ x, fderiv ℝ u x (ev j) * ψ x := by
  have hu1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (ev j)) U :=
    contDiffOn_dw_of_isOpen hU [j] u hu
  have hψ1 : Continuous (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsub : tsupport (fun x => fderiv ℝ ψ x (ev j)) ⊆ tsupport ψ := by
    refine (closure_mono ?_).trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := ψ))
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; exact hx (by simp [h])
  have hψ1c : HasCompactSupport (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E d →L[ℝ] ℂ => L (ev j)) (by simp)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_of_tsupport_subset hU hu1.continuousOn hψ.continuous hψc hψs
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ1 hψ1c (hsub.trans hψs)
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ.continuous hψc hψs
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hψs hx))).differentiableAt (by simp)
  · intro x _
    exact hψ.differentiable (by simp) x

theorem dw_contDiff_tsupport {d : ℕ} (w : List (Fin d)) {φ : E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dw w φ) ∧ tsupport (dw w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact ⟨hφ, subset_rfl⟩
  | cons j w ih =>
    refine ⟨(ih.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, ?_⟩
    refine (closure_mono ?_).trans ((tsupport_fderiv_subset (𝕜 := ℝ) (f := dw w φ)).trans ih.2)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; apply hx; show fderiv ℝ (dw w φ) x (ev j) = 0; simp [h]

theorem dw_append {d : ℕ} (w v : List (Fin d)) (f : E d → ℂ) : dw (w ++ v) f = dw w (dw v f) := by
  induction w with
  | nil => rfl
  | cons j w ih => funext x; show fderiv ℝ (dw (w ++ v) f) x (ev j) = _; rw [ih]; rfl

theorem dw_swap {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (a b : Fin d) {g : E d → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (dw [a, b] g) (dw [b, a] g) U := by
  intro x hx
  have hx' := hU.mem_nhds hx
  have hga : ContDiffAt ℝ ∞ g x := hg.contDiffAt hx'
  have hsym := hga.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.2 le_top : (2 : WithTop ℕ∞) ≤ ∞))
  have hd1 : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ g) x := by
    have := (contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg
    exact (this.2.contDiffAt hx').differentiableAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ g y (ev b)) x (ev a) = fderiv ℝ (fun y => fderiv ℝ g y (ev a)) x (ev b)
  rw [fderiv_clm_apply hdf (differentiableAt_const _), fderiv_clm_apply hdf (differentiableAt_const _)]
  have h0 : ∀ c : E d, fderiv ℝ (fun _ : E d => c) x = 0 := fun c => fderiv_const_apply c
  simp only [h0, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hsym _ _

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem dw_perm {d : ℕ} {U : Set (E d)} (hU : IsOpen U) {w₁ w₂ : List (Fin d)} (h : w₁.Perm w₂) :
    ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → Set.EqOn (dw w₁ u) (dw w₂ u) U := by
  induction h with
  | nil => intro u _; exact fun _ _ => rfl
  | cons j _ ih =>
    intro u hu z hz
    show fderiv ℝ _ z (ev j) = fderiv ℝ _ z (ev j)
    rw [((ih u hu).eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]
  | swap x y l =>
    intro u hu
    have e1 := dw_append [y, x] l u
    have e2 := dw_append [x, y] l u
    simp only [List.cons_append, List.nil_append] at e1 e2
    rw [e1, e2]
    exact dw_swap hU y x (contDiffOn_dw_of_isOpen hU l u hu)
  | trans _ _ ih₁ ih₂ => intro u hu; exact (ih₁ u hu).trans (ih₂ u hu)

theorem integral_mul_dw_eq_reverse {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d)) :
    ∀ (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w.reverse u x * φ x := by
  induction w with
  | nil => intro u φ _ _ _ _; simp [dw]
  | cons j w ih =>
    intro u φ hu hφ hφc hφs
    obtain ⟨hψ, hψs⟩ := dw_contDiff_tsupport w hφ
    have hψc : HasCompactSupport (dw w φ) := IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) hψs
    have step := integral_mul_partial_eq_neg hU j hu hψ hψc (hψs.trans hφs)
    have hu1 : ContDiffOn ℝ ∞ (dw [j] u) U := contDiffOn_dw_of_isOpen hU [j] u hu
    have ih' := ih (dw [j] u) φ hu1 hφ hφc hφs
    have e : dw w.reverse (dw [j] u) = dw (j :: w).reverse u := by
      rw [List.reverse_cons, dw_append]
    show ∫ x, u x * fderiv ℝ (dw w φ) x (ev j) = _
    rw [step]
    change -∫ x, dw [j] u x * dw w φ x = _
    rw [ih', e, List.length_cons, pow_succ]
    ring

theorem integral_mul_dw_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d))
    (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  intro d U hU w u φ hu hφ hφc hφs
  rw [integral_mul_dw_eq_reverse hU w u φ hu hφ hφc hφs]
  congr 2
  funext x
  by_cases hx : x ∈ U
  · rw [dw_perm hU (List.reverse_perm w) u hu hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
    simp [this]

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantCochainOneConstOnDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem le_of_deg_eq {K : Charts F} {m m' : Λ} {a b : K.K} (e : K.le m a b) (hm : m = m') : K.le m' a b :=
  hm ▸ e

theorem ptHom_deg_eq (K : Charts F) {m m' : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) (hm : m = m') :
    ptHom T e = ptHom T (le_of_deg_eq e hm) := by
  subst hm; rfl

theorem ptHom_triv_comp (K : Charts F) {l m : Λ} {k k' : K.K} (e : K.le l k' k) (T : K.Obj)
    (e₂ : K.le m T.k k') : ptHom (K.triv k') e ≫ ptHom T e₂ = ptHom T (K.le_trans e e₂) :=
  hom_ext (fun c ↦ show T.ρ (K.sh e₂ (K.sh e c)) = T.ρ (K.sh (K.le_trans e e₂) c) by rw [sh_sh]) rfl

theorem ptHom_eq_comp (K : Charts F) {m : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) :
    ptHom T e = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
  hom_ext (fun c ↦ show T.ρ (K.sh e c) = T.ρ (K.sh (K.le_refl T.k) (K.sh e c)) by rw [sh_refl]) (add_zero m).symm

theorem invCochain_const : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (h : C1 K.Oc) (l : Λ),
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = l → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ)) →
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = l →
      h T T'' (φ ≫ ψ) = h T' T'' ψ) →
    ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l → h T T' φ = algebraMap (Hol F.V) T'.C p := by
  intro I _ g Λ _ F K hK h l hA hB

  let B : ∀ k' k : K.K, K.le l k' k → Hol (K.W k') := fun k' k e ↦ h _ _ (ptHom (K.triv k') e)
  have hBv : ∀ {m : Λ} {k k' : K.K} (e : K.le m k' k) (hm : m = l),
      h _ _ (ptHom (K.triv k') e) = B k' k (le_of_deg_eq e hm) := by
    intro m k k' e hm
    rw [ptHom_deg_eq K (K.triv k') e hm]

  have hR : ∀ {k k' k'' : K.K} (e : K.le l k' k) (e₂ : K.le 0 k'' k'),
      K.sh e₂ (B k' k e) = B k'' k (le_of_deg_eq (K.le_trans e e₂) (add_zero l)) := by
    intro k k' k'' e e₂
    have := hA _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e₂) rfl rfl
    rw [ptHom_triv_comp, hBv _ (add_zero l)] at this
    exact this.symm

  have hC : ∀ {k₀ k k' : K.K} (e₀ : K.le 0 k k₀) (e : K.le l k' k),
      B k' k₀ (le_of_deg_eq (K.le_trans e₀ e) (zero_add l)) = B k' k e := by
    intro k₀ k k' e₀ e
    have := hB _ _ _ (ptHom (K.triv k) e₀) (ptHom (K.triv k') e) rfl rfl
    rw [ptHom_triv_comp, hBv _ (zero_add l)] at this
    exact this

  have hD : ∀ {k k' : K.K} (e : K.le l k' k) (a : Fin g), dw a (B k' k e) = 0 := by
    intro k k' e a
    obtain ⟨χ, hχ, h0, h1, -⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
    have e0 := hB _ _ _ (jet0 k) χ rfl hχ
    have e1 := hB _ _ _ (jet1 k) χ rfl hχ
    rw [h0, hA _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl] at e0
    rw [h1, hA _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl] at e1
    have := congrArg (fun x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k')) ↦ x.snd a) (e0.trans e1.symm)
    have s0 : ∀ x : Hol (K.W k'), ((jet0 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0 :=
      fun x ↦ by
        show (TrivSqZeroExt.inl (K.sh (K.le_refl k') x) : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0
        rw [TrivSqZeroExt.snd_inl]; rfl
    have s1 : ∀ x : Hol (K.W k'), ((jet1 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = dw a x :=
      fun x ↦ snd_tszeSec _ x a
    simp only at this
    rw [s0, s1] at this
    exact this.symm

  let K' : Charts F :=
    { K := {x : K.K × K.K // K.le l x.1 x.2}
      W := fun x ↦ K.W x.1.1
      base := fun x ↦ K.base x.1.1
      le := fun m x y ↦ K.le m x.1.1 y.1.1 ∧ K.le m x.1.2 y.1.2
      le_refl := fun x ↦ ⟨K.le_refl _, K.le_refl _⟩
      le_trans := fun h h' ↦ ⟨K.le_trans h.1 h'.1, K.le_trans h.2 h'.2⟩
      maps := fun h ↦ K.maps h.1 }
  have hK' : K'.Rich := by
    refine ⟨fun q hq ↦ ?_, fun m x y q hq hq' ↦ ?_⟩
    · obtain ⟨k₀, h₀⟩ := hK.1 q hq
      obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l q) hq
      obtain ⟨k₃, h₃, -, e₃⟩ := hK.2 l k₀ k₂ q h₀ h₂
      exact ⟨⟨(k₃, k₂), e₃⟩, h₃⟩
    · obtain ⟨⟨k₁', k₁⟩, e₁⟩ := x
      obtain ⟨⟨k₂', k₂⟩, e₂⟩ := y
      change q ∈ K.W k₁' at hq
      change F.shift m q ∈ K.W k₂' at hq'
      have p1 : F.shift l q ∈ K.W k₁ := K.maps e₁ q hq
      have p2 : F.shift m (F.shift l q) ∈ K.W k₂ := by
        rw [← F.shift_add, add_comm, F.shift_add]; exact K.maps e₂ _ hq'
      obtain ⟨k, hk, f₀, fm⟩ := hK.2 m k₁ k₂ _ p1 p2
      obtain ⟨k₅, h₅, g₀, gm⟩ := hK.2 m k₁' k₂' q hq hq'
      obtain ⟨k', hk', j₀, jl⟩ := hK.2 l k₅ k q h₅ hk
      exact ⟨⟨(k', k), jl⟩, hk', ⟨le_of_deg_eq (K.le_trans g₀ j₀) (add_zero 0), f₀⟩,
        ⟨le_of_deg_eq (K.le_trans gm j₀) (add_zero m), fm⟩⟩
  obtain ⟨p, hp⟩ := GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero K' hK' (fun x ↦ B x.1.1 x.1.2 x.2)
    (fun x y e ↦ by
      show K.sh e.1 (B _ _ x.2) = B _ _ y.2
      rw [hR x.2 e.1]
      exact hC e.2 y.2)
    (fun x i ↦ hD x.2 i)
  have hp' : ∀ (k' k : K.K) (e : K.le l k' k), B k' k e = K.cst k' p := fun k' k e ↦ hp ⟨(k', k), e⟩

  have hPt : ∀ {m : Λ} {k : K.K} (T' : K.Obj) (e : K.le m T'.k k), m = l →
      h _ _ (ptHom T' e) = algebraMap (Hol F.V) T'.C p := by
    intro m k T' e hm
    have s4 := hA _ _ _ (ptHom (K.triv T'.k) e) (ptHom T' (K.le_refl T'.k)) hm rfl
    rw [← ptHom_eq_comp, hBv e hm, hp'] at s4
    rw [s4]
    show T'.ρ (K.sh (K.le_refl T'.k) (K.cst T'.k p)) = _
    rw [sh_cst, T'.ρ_cst]
  refine ⟨p, fun T T' φ hφ ↦ ?_⟩
  have hd : (ptHom T (K.le_refl T.k) ≫ φ).deg = l := by
    show 0 + φ.deg = l
    rw [zero_add, hφ]
  have s1 := hB _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  have s2 := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h l
    (fun k T χ hχ ↦ (hB _ _ _ (jet0 k) χ rfl hχ).trans (hB _ _ _ (jet1 k) χ rfl hχ).symm) _ T'
    (ptHom T (K.le_refl T.k) ≫ φ) hd
  rw [← s1, s2]
  exact hPt T' _ hd

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by
  first | exact @GlobalTheory.FinWeil.invForm_intertwiner | exact GlobalTheory.FinWeil.invForm_intertwiner | (intros; apply GlobalTheory.FinWeil.invForm_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem irreducibleSpace_of_smooth_of_geometricallyConnected_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  intro R _ _ G hs hc _
  let K := FractionRing R
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F : Scheme := pullback G.hom g
  have hsnd : Smooth (pullback.snd G.hom g) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback G.hom g) hs
  have hcon : ConnectedSpace F :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) g (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hirr : IrreducibleSpace F :=
    irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd G.hom g) hsnd hcon
  have hgf : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hG : Flat G.hom := inferInstance

  have hη : genericPoint (Spec (CommRingCat.of R)) ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      (genericPoint_specializes (g (closedPoint K))) ⟨closedPoint K, rfl⟩
  let ξ : G.left := pullback.fst G.hom g (genericPoint F)
  have hspec : ∀ z : G.left, ξ ⤳ z := by
    intro z
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap G.hom (genericPoint_specializes (G.hom z))
    have hr : z' ∈ Set.range (pullback.fst G.hom g) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact hη
    obtain ⟨w, rfl⟩ := hr
    exact ((genericPoint_specializes w).map (pullback.fst G.hom g).continuous).trans hz'
  have hcl : closure ({ξ} : Set G.left) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (hspec z)
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := ξ)).closure
  rw [hcl] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isAW_existsUnique_biadditive (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc}
    {n m k : ℤ} (hk : n + m = k) :
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  refine ⟨fun α β => ?_, fun α α' β γ γ' h h' => CupSpec.isAW_add_left μ hk h h',
    fun α β β' γ γ' h h' => CupSpec.isAW_add_right μ hk h h'⟩
  obtain ⟨γ, hγ⟩ := CupSpec.isAW_exists μ hk α β
  exact ⟨γ, hγ, fun γ' h' => CupSpec.isAW_unique μ hk h' hγ⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRooStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (exact GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_of_AIC  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwiseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  first | (exact @GlobalTheory.EtC.HCEqv.main) | (exact GlobalTheory.EtC.HCEqv.main) | (intros; apply GlobalTheory.EtC.HCEqv.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowConeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  first | exact @GlobalTheory.SepCech.isLimit_leftFunc_arrCone | exact GlobalTheory.SepCech.isLimit_leftFunc_arrCone | (intros; apply GlobalTheory.SepCech.isLimit_leftFunc_arrCone <;> assumption)
end

