module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUnique
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLatVac

theorem two_inv_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    (⅟(2 : Fv F v)) ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) := by
      rw [show (((2 : 𝓞 F) : F)) = 2 from map_ofNat (algebraMap (𝓞 F) F) 2, map_ofNat]
    have e2 : algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) =
        ((algebraMap (𝓞 F) F (2 : 𝓞 F) : F) : v.adicCompletion F) := rfl
    rw [e, e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, invOf_eq_inv, map_inv₀, hv, inv_one]

theorem hTens_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E) (e : E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (e • x) y = e * GlobalTheory.WeilM.hTens c JA JB x y := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem symp_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Module.Free R E] [Module.Finite R E]
    (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (r : R)
    (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JA JB (r • x) y = r * GlobalTheory.WeilM.symp c ξ JA JB x y := by
  have : r • x = (algebraMap R E r) • x := (algebraMap_smul E r x).symm
  rw [this]
  simp only [GlobalTheory.WeilM.symp, hTens_smul_left]
  rw [mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem latAtV_smul_int {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (v : Pl (F := F)) (e : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, (inclR (F := F) (AF F) (e : E)) • γ ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨r, hr, hr', x, hx, y, hy, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨r, hr, hr', e • x, X.L.smul_mem e hx, y, hy, ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.smul_def, map_mul, RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem phase_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ θ : 𝓞 E, (θ : E) + σ (θ : E) = 1 → ∀ γ ∈ latAtV G.V G.W v,
      B.ψ (⅟2 * symp (cA σ) ((inclR (AF F)) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin θ hθ γ hγ
  have hst := GlobalTheory.LatVac.latAtV_at_stable G.V G.W v
  have h2 := two_inv_mem v (hT.base.inert v w hin).1
  have hγ' : GlobalTheory.LatVac.liftV v (⅟2) • γ ∈ latAtV G.V G.W v := hst.2 _ h2 γ hγ
  have e1 : (⅟(2 : AF F)) • γ = GlobalTheory.LatVac.liftV v (⅟2) • γ := by
    have hev : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
      refine (invOf_eq_right_inv ?_).symm
      have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
      rwa [map_mul, map_ofNat] at h
    have h0 : ((⅟(2 : AF F)) - GlobalTheory.LatVac.liftV v (⅟2)) • γ = 0 :=
      hst.1 γ hγ _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, hev, sub_self])
    rwa [sub_smul, sub_eq_zero] at h0
  have hz : -((inclR (F := F) (AF F) (θ : E)) • GlobalTheory.LatVac.liftV v (⅟2) • γ) ∈ latAtV G.V G.W v :=
    neg_mem (latAtV_smul_int G.V G.W v θ _ hγ')
  have key := (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin _ (hst.1 _ hz)).1 hz γ hγ
  rw [← symp_smul_left, e1]
  refine Eq.trans ?_ key
  congr 1
  rw [← neg_smul, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.symp, hTens_smul_left]
  ring_nf

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e := (h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ))
  funext y
  have hx := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 _ hat
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx
  exact mul_right_cancel₀ hR0 hx

theorem fixed_eq_smul {K : Type} [Field K] {h2 : Invertible (2 : K)} {κ : Type} [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K)))
    (hdual : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hrefl : ∀ t : κ → K, (∀ y : κ → K, (∀ l ∈ Λ, ψ₀ (l.1 ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → ∃ l ∈ Λ, l.1 = t)
    {f g : (κ → K) → ℂ} (hg : g ≠ 0)
    (hf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l f = f) (hgf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l g = g) :
    ∃ c : ℂ, f = c • g := by
  have hne : ∀ x : K, ψ₀ x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul ψ₀ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this

  have key1 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ t, h t ≠ 0 → ∃ l ∈ Λ, l.1 = t := by
    intro h hh t ht
    apply hrefl
    intro y hy
    have hmem : ((0 : κ → K), y) ∈ Λ := by
      rw [hdual]
      intro l hl
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv, hy l hl, inv_one]
    have := congrFun (hh _ hmem) t
    simp only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero] at this
    have h' : ψ₀ (t ⬝ᵥ y) * h t = 1 * h t := by rw [one_mul]; exact this
    exact mul_right_cancel₀ ht h'

  have key2 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ l ∈ Λ, ψ₀ (⅟2 * l.1 ⬝ᵥ l.2) * h l.1 = h 0 := by
    intro h hh l hl
    have := congrFun (hh l hl) 0
    simpa [GlobalTheory.WeilM.schr] using this
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    funext t
    by_contra ht
    obtain ⟨l, hl, rfl⟩ := key1 g hgf t ht
    have := key2 g hgf l hl
    rw [h0] at this
    exact ht ((mul_eq_zero.1 this).resolve_left (hne _))
  refine ⟨f 0 / g 0, ?_⟩
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : ∃ l ∈ Λ, l.1 = t
  · obtain ⟨l, hl, rfl⟩ := ht
    have e1 := key2 f hf l hl
    have e2 := key2 g hgf l hl
    apply mul_left_cancel₀ (hne (⅟2 * l.1 ⬝ᵥ l.2))
    rw [e1, ← mul_assoc, mul_comm _ (f 0 / g 0), mul_assoc, e2, div_mul_cancel₀ _ hg0]
  · have hf0 : f t = 0 := by by_contra h; exact ht (key1 f hf t h)
    have hg0' : g t = 0 := by by_contra h; exact ht (key1 g hgf t h)
    rw [hf0, hg0', mul_zero]

theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux Bf κ) (v : Pl (F := F)) (c : Fv F v) (z : W) :
    GlobalTheory.LatVac.locCo co v (GlobalTheory.LatVac.liftV v c • z) =
      (c • (GlobalTheory.LatVac.locCo co v z).1, c • (GlobalTheory.LatVac.locCo co v z).2) := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV]
  rfl

theorem vac_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT Y _ Xm P hP hPs ρ hρ
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hloc : ∀ γ ∈ latAtV G.V G.W v, ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hAt γ hγ) φ
  have hph := phase_one F E σ B a a' G X om om' hT v w hin θ hθ
  have hvfix : ∀ γ ∈ latAtV G.V G.W v,
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) (G.M.vac v) = G.M.vac v := by
    intro γ hγ
    have h1 := hvac γ hγ
    rw [hph γ hγ, one_smul] at h1
    exact acts_unique v _ hvSB (hloc γ hγ _) h1
  have hρs : ∀ u, P u → ∀ s : SB (Fin a × Fin (a + a') → Fv F v),
      ((ρ u s : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) =
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (Xm u)) s :=
    fun u hu s => acts_unique v _ s.2 (hρ u s) (hloc _ (hP u hu) _)
  refine ⟨fun s hs u hu => ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    rw [hρs u hu s, hs]
    exact hvfix _ (hP u hu)
  · set Λ := (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) with hΛ
    have hdual : ∀ l, l ∈ Λ ↔ ∀ m ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ m.2 - m.1 ⬝ᵥ l.2) = 1 :=
      fun l => GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hAt
        (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin) l
    have hsfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = s := by
      rintro l ⟨z, hz, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hPs z hz
      have := hρs u hu s
      rw [hs u hu] at this
      exact this.symm
    have hgfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (G.M.vac v) = G.M.vac v := by
      rintro l ⟨z, hz, rfl⟩
      exact hvfix z hz
    have hPU := (hT.base.inert v w hin).2.2
    have hψ : ∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
        x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
      intro x
      simp only [GlobalTheory.LatVac.psiAt_apply]
      exact hPU x
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded F E σ B a a' G X om om' hT v
    have hrefl : ∀ t : Fin a × Fin (a + a') → Fv F v,
        (∀ y, (∀ l ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ y) = 1) → GlobalTheory.LatVac.psiAt B.ψ v (t ⬝ᵥ y) = 1) →
          ∃ l ∈ Λ, l.1 = t := by
      intro t ht
      have := GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal F v (Fin a × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ v) hψ (Λ.map (AddMonoidHom.fst _ _))
        (by
          rintro r hr _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩
          refine ⟨GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.LatVac.liftV v r • z),
            ⟨_, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 r hr z hz, rfl⟩, ?_⟩
          rw [locCo_smul]
          rfl)
        ⟨c, hc0, by
          rintro _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩ k
          exact (hc z hz k).1⟩ t
        (fun y hy => ht y fun l hl => hy _ ⟨l, hl, rfl⟩)
      obtain ⟨l, hl, rfl⟩ := this
      exact ⟨l, hl, rfl⟩
    exact fixed_eq_smul (GlobalTheory.LatVac.psiAt B.ψ v) Λ hdual hrefl hv0 hsfix hgfix

end GlobalTheory.InertLatVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacePointSupportedAndSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenbergStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_weil_normalises_heisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ g h x, ω (g, h) * ρ x =
      ρ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L)) * ω (g, h) := by
  first | exact @GlobalTheory.InertBridge.weil_normalises_heis | exact GlobalTheory.InertBridge.weil_normalises_heis | (intros; apply GlobalTheory.InertBridge.weil_normalises_heis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIff
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport
namespace PrimFrameTr

section Fields
variable {k k' : Type} [Field k] [Field k']

theorem rank_map_le {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (f : k →+* k') (Z : Matrix A D k) :
    (Z.map f).rank ≤ Z.rank := by
  classical
  let M := LinearMap.range Z.mulVecLin
  let b := Module.finBasis k M
  have hc : ∀ y : D, (fun x => Z x y) ∈ M := fun y => ⟨Pi.single y 1, by ext x; simp⟩
  let P : Matrix A (Fin (Module.finrank k M)) k := Matrix.of fun x l => (b l : A → k) x
  let Q : Matrix (Fin (Module.finrank k M)) D k := Matrix.of fun l y => b.repr ⟨fun x => Z x y, hc y⟩ l
  have hPQ : Z = P * Q := by
    ext x y
    have h := congrArg (fun z : M => (z : A → k) x) (b.sum_repr ⟨fun x => Z x y, hc y⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, Q, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h : Z.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp [Matrix.rank, M]

theorem rank_map_equiv {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (j : k ≃+* k') (Z : Matrix A D k) :
    (Z.map j).rank = Z.rank := by
  refine le_antisymm (rank_map_le (j : k →+* k') Z) ?_
  have := rank_map_le (j.symm : k' →+* k) (Z.map j)
  have e : (Z.map j).map (j.symm : k' →+* k) = Z := by ext; simp
  rwa [e] at this

theorem rank_trM {A D A₂ D₂ : Type} [Fintype A] [Fintype D] [DecidableEq D] [Fintype D₂]
    (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) : (trM j rA cD Z).rank = Z.rank := by
  have : trM j rA cD Z = (Z.map j).submatrix rA cD := by ext; rfl
  rw [this, Matrix.rank_submatrix, rank_map_equiv]

theorem row_trM {A D A₂ D₂ : Type} (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) (r : A₂) :
    (trM j rA cD Z).row r = fun c => j (Z.row (rA r) (cD c)) := rfl

theorem read_sum {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (c : A → k) :
    (fun d => j ((∑ a, c a • Z.row a) (cD d))) = ∑ r, j (c (rA r)) • (trM j rA cD Z).row r := by
  funext d
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, row_trM]
  exact (Fintype.sum_equiv rA _ _ fun r => rfl).symm

theorem mem_spanK_of {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span k (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  rw [read_sum j rA cD Z c]
  exact (Submodule.mem_span_range_iff_exists_fun k').2 ⟨_, rfl⟩

end Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

theorem isLocIso_symm (hj : IsLocIso j) : IsLocIso j.symm :=
  ⟨hj.2.1, by simpa using hj.1, fun x => by rw [← hj.2.2 (j.symm x)]; simp⟩

theorem mem_spanO_of (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span 𝒪[k] (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 hx
  have h := read_sum j rA cD Z (fun a => (c a : k))
  have e : (∑ a, c a • Z.row a) = ∑ a, (c a : k) • Z.row a := Finset.sum_congr rfl fun a _ => rfl
  rw [e, h]
  exact (Submodule.mem_span_range_iff_exists_fun 𝒪[k']).2
    ⟨fun r => ⟨j (c (rA r)), (hj.2.2 _).2 (c (rA r)).2⟩, rfl⟩

theorem read_symm {D D₂ : Type} (cD : D₂ ≃ D) (x : D → k) :
    (fun d => j.symm ((fun c => j (x (cD c))) (cD.symm d))) = x := by
  funext d; simp

theorem trM_symm {A D A₂ D₂ : Type} (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) :
    trM j.symm rA.symm cD.symm (trM j rA cD Z) = Z := trM_symm_trM j rA cD Z

def readEquiv (j : k ≃+* k') {D D₂ : Type} (cD : D₂ ≃ D) : (D → k) ≃ (D₂ → k') where
  toFun x d := j (x (cD d))
  invFun y d := j.symm (y (cD.symm d))
  left_inv x := by funext d; simp
  right_inv y := by funext d; simp

theorem memK_iff {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span k (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanK_of j rA cD Z⟩
  have := mem_spanK_of j.symm rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

theorem memO_iff (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span 𝒪[k] (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanO_of hj rA cD Z⟩
  have := mem_spanO_of (isLocIso_symm hj) rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

end PrimFrameTr


open PrimFrameTr in
theorem isPrimFrame_trM_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂]
    [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂] (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (hL : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  have hc : Fintype.card A₂ = Fintype.card A := Fintype.card_congr rA
  have hm : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
    rw [mem_matLat, mem_matLat]
    refine (forall_congr' fun r => ?_).trans (rA.forall_congr_right (q := fun a => Z.row a ∈ Λ))
    exact hL (Z.row (rA r))
  have hs : (Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) =
        (Submodule.span k' (Set.range (trM j rA cD Z).row)).restrictScalars 𝒪[k'] ⊓ Λ₂) ↔
      (Submodule.span 𝒪[k] (Set.range Z.row) =
        (Submodule.span k (Set.range Z.row)).restrictScalars 𝒪[k] ⊓ Λ) := by
    rw [SetLike.ext_iff, SetLike.ext_iff]
    refine ((readEquiv j cD).forall_congr_right).symm.trans (forall_congr' fun x => ?_)
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    change ((fun d => j (x (cD d))) ∈ _ ↔ (fun d => j (x (cD d))) ∈ _ ∧ (fun d => j (x (cD d))) ∈ Λ₂) ↔ _
    rw [memO_iff hj, memK_iff, hL]
  unfold IsPrimFrame
  rw [rank_trM, hc, hm, hs]
end GlobalTheory.PureMatch.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstractStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  first | (exact @GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (exact GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (intros; apply GlobalTheory.JSW.MirSemi.kirillov_semiLocal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstantStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_inversion_up_to_constant : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  first | exact @GlobalTheory.FourierLocInv.fourier_inversion | exact GlobalTheory.FourierLocInv.fourier_inversion | (intros; apply GlobalTheory.FourierLocInv.fourier_inversion <;> assumption)
end

