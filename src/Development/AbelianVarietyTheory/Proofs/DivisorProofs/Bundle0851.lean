module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProduct
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTracePowRestrictNeZero
section
noncomputable section

open ValuativeRel GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.GLDoubling

namespace GlobalTheory.IwahoriUnit

section Gen

variable {G : Type} [Group G]

def cosets (I : Subgroup G) (x : G) : Set (G ⧸ I) :=
  (QuotientGroup.mk : G → G ⧸ I) '' DoubleCoset.doubleCoset x I I

theorem cosets_eq_orbit (I : Subgroup G) (x : G) : cosets I x = MulAction.orbit I (x : G ⧸ I) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * x : G) : G ⧸ I) = ((a * x * b : G) : G ⧸ I)
    rw [QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨a, rfl⟩
    exact ⟨a * x * 1, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, 1, one_mem _, rfl⟩, by rw [mul_one]; rfl⟩

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem fixed_eq_fixd (π : Representation E G V) (I : Subgroup G) : fixed π I = UpperTheory.V.Hi.fixd π I := by
  ext v
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

theorem hk_apply (π : Representation E G V) (I : Subgroup G) (x : G) (h : (cosets I x).Finite)
    (v : UpperTheory.V.Hi.fixd π I) :
    (UpperTheory.V.AlgebraTools.hk π I x v : V) = ∑ᶠ q ∈ cosets I x, π q.out v := by
  rw [cosets_eq_orbit] at h ⊢
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := h
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply E G V π I I x h).1 v, UpperTheory.V.Hi.dc,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem finite_cosets (x : GL (Fin N) k) : (cosets (iwahori k (Fin N)) x).Finite := by
  rw [cosets_eq_orbit, ← (UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1]
  exact (UpperTheory.V.AlgebraTools.heckePairIwC k N ⊤).1 x

theorem dom_of_antitone {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {ν : Fin N → ℤ} (hν : Antitone ν) :
    UpperTheory.V.AlgebraTools.Dom (fun i => ϖ ^ ν i) := by
  intro i j hij
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hν hij)

theorem torusElt_pow (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    torusElt k (Fin N) ϖ ν ^ m = diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m) := by
  rw [map_pow]; rfl

theorem dom_pow {t : Fin N → kˣ} (ht : UpperTheory.V.AlgebraTools.Dom t) (m : ℕ) : UpperTheory.V.AlgebraTools.Dom (t ^ m) := by
  intro i j hij
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_left₀ zero_le' (ht i j hij) m

theorem exists_equiv_doubleCoset (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (ν : Fin N → ℤ) (hν : Antitone ν) (E V : Type) [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (π : Representation E (GL (Fin N) k) V) :
    (∀ m : ℕ, (cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m)).Finite) ∧
    ∃ T : fixed π (iwahori k (Fin N)) ≃ₗ[E] fixed π (iwahori k (Fin N)),
      (∀ v, (T v : V) = ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν), π q.out v) ∧
      ∀ (m : ℕ) v, ((T ^ m) v : V) =
        ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m), π q.out v := by
  refine ⟨fun m => finite_cosets _, ?_⟩
  have hd := dom_of_antitone hϖ hν
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : E) := by
    refine IsUnit.mk0 _ (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul k N ⊤ E V π
  rw [(UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1] at hmul hunit
  rw [fixed_eq_fixd]
  have hone : UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) 1) = 1 := by
    have h := hmul 1 1 UpperTheory.V.AlgebraTools.dom_one UpperTheory.V.AlgebraTools.dom_one
    rw [mul_one] at h
    exact (hunit hq 1 UpperTheory.V.AlgebraTools.dom_one).mul_left_cancel (h.trans (mul_one _).symm)
  have hpow : ∀ m : ℕ, UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) fun i => ϖ ^ ν i) ^ m =
      UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m)) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih => rw [pow_succ, pow_succ, ih, hmul _ _ (dom_pow hd m) hd]
  have hb := (Module.End.isUnit_iff _).1 (hunit hq _ hd)
  refine ⟨LinearEquiv.ofBijective _ hb, fun v => hk_apply π _ _ (finite_cosets _) v, fun m v => ?_⟩
  rw [← hk_apply π _ _ (finite_cosets _) v, torusElt_pow, ← hpow]
  congr 1
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end GlobalTheory.IwahoriUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links
  GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameFinitePart

theorem exists_chrEq_val (D : D7) (χ : HChar D.host.E) (hχ : χ.IsUnitary) :
    ∃ c, ChrEq c χ ∧ ∀ x, ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c', ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, fun x => ⟨u x, rfl⟩⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · refine (hcoe _).trans ?_
    have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
      (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
    exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
  · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
    change Θ (x : Formalism.L2.Theta.AE D) = _
    rw [hx, hloc P e he]

theorem exists_lift (D : D7) (y : (AfE D)ˣ) : ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
  obtain ⟨a, a1, a2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 (y : AfE D)
  obtain ⟨b, b1, b2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 ((y⁻¹ : (AfE D)ˣ) : AfE D)
  have h : a * b = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, a1, b1, RingHom.map_one, mul_one])
    (by rw [RingHom.map_mul, a2, b2, RingHom.map_one, Units.mul_inv])
  exact ⟨⟨a, b, h, (mul_comm b a).trans h⟩, a1, a2, b2⟩

theorem exists_unit_ne_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt P) (hr : ¬ χ.UnrAt P) : ∃ k : Lˣ, P.valuation L (k : L) = 1 ∧ χ.locK P k ≠ 1 := by
  by_contra hn
  refine hr fun x hx => ?_
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-1 : ℤ)).preimage (continuous_sub_left (x : P.adicCompletion L))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L) P).exists_mem_open h1 ⟨x, by simp⟩
  have hk' : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) ≤ WithZero.exp (-1 : ℤ) := hk
  have hx' : Valued.v (x : P.adicCompletion L) = 1 := hx
  have hv : Valued.v (algebraMap L (P.adicCompletion L) k) = 1 := by
    rw [← hx']
    refine (Valuation.map_eq_of_sub_lt _ ?_)
    rw [Valuation.map_sub_swap, hx']
    refine hk'.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hv' : P.valuation L k = 1 := (GlobalTheory.BaseIdeleTriv.val_algebraMap P k).symm.trans hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv'
  have h2 : χ.loc P (atFin P (Units.mk0 k hk0)) = 1 := by
    by_contra h
    exact hn ⟨Units.mk0 k hk0, hv', h⟩
  have e : ((x * (atFin P (Units.mk0 k hk0))⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
      x * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have h0 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  have h3 := ht (x * (atFin P (Units.mk0 k hk0))⁻¹) (by
    unfold IsUnitAt
    rw [e, map_mul, map_inv₀, hx', hv]; simp) (by
    have : (x : P.adicCompletion L) * (algebraMap L (P.adicCompletion L) k)⁻¹ - 1 =
        ((x : P.adicCompletion L) - algebraMap L _ k) * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
      field_simp
    rw [e, this, map_mul, map_inv₀, hv, inv_one, mul_one]
    simpa using hk')
  rwa [map_mul, map_inv, h2, inv_one, mul_one] at h3

theorem loc_sub_one {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) (N : ℕ)
    (hN : (N : E) ≠ 0) : f (1 + e * (i k - 1)) - 1 = N • f (e * i ((k - 1) / N)) := by
  rw [← map_nsmul, ← mul_smul_comm, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hN, map_add (f := _), map_one, map_sub, map_one,
    add_sub_cancel_left]

theorem loc_eq {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) :
    f (1 + e * (i k - 1)) = 1 + f (e * i (k - 1)) := by
  rw [map_add (f := _), map_one, map_sub, map_one]

theorem loc_mul_inv {E A : Type} [Field E] [CommRing A] (i : E →+* A) (e : A) (he : e * e = e) (k : Eˣ) :
    (1 + e * (i k - 1)) * (1 + e * (i ((k⁻¹ : Eˣ) : E) - 1)) = 1 := by
  have hkk : i (k : E) * i ((k⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (i (k : E) - 1) * (i ((k⁻¹ : Eˣ) : E) - 1) * he + e * hkk


set_option maxHeartbeats 800000 in
theorem exists_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.Eˣ)
    (hk : P.valuation D.host.E (k : D.host.E) = 1) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ (e : AE D) (x : (AE D)ˣ), IsPlIdem D e P ∧ (x : AE D) = locE D e (k : D.host.E) ∧
      IntUnit (Units.map (finPart D).toMonoidHom x) ∧ CongOne N (Units.map (finPart D).toMonoidHom x) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -, e1, e2⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hee : e * e = e := he.1
  have hint : ∀ t : D.host.E, P.valuation D.host.E t ≤ 1 → finPart D (e * incA D t) ∈ intAE D := fun t ht => by
    have h4 : finPart D (incA D t) = (1 : Af D.host.F) ⊗ₜ[D.host.F] t := rfl
    rw [h2, RingHom.map_mul, map_mul, h4, h1]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_mul_apply]
    by_cases hQ : Q = P
    · subst hQ
      rw [e1, one_mul, GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]
      exact ht
    · rw [e2 Q hQ, zero_mul, map_zero]
      exact zero_le
  have hone : (1 : AfE D) ∈ intAE D := by
    rw [h2, map_one]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_one_apply, map_one]
  have hloc : ∀ t : D.host.E, P.valuation D.host.E t = 1 → finPart D (locE D e t) ∈ intAE D := fun t ht => by
    rw [show finPart D (locE D e t) = _ from loc_eq (incA D) (finPart D) e t]
    exact add_mem hone (hint _ (Valuation.map_sub_le _ ht.le (map_one _).le))
  have hm : locE D e (k : D.host.E) * locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) = 1 := loc_mul_inv (incA D) e hee k
  have hN1 : P.valuation D.host.E (N : D.host.E) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := (N : 𝓞 D.host.E))).2 hN
    simpa using this
  have hN0 : (N : D.host.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨e, ⟨_, _, hm, (mul_comm _ _).trans hm⟩, he, rfl, ⟨hloc _ hk, hloc _ ?_⟩,
    finPart D (e * incA D (((k : D.host.E) - 1) / N)), hint _ ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hk, inv_one]
  · rw [map_div₀, hN1, div_one]
    exact Valuation.map_sub_le _ hk.le (map_one _).le
  · exact loc_sub_one (incA D) (finPart D) e k N hN0


set_option maxHeartbeats 1000000 in
theorem exists_xiRec : ∀ (D : D7) (p : ℕ) (δ : Formalism.L2.Host.HChar D.host.E), (p = D.host.pde ∨ p = D.host.pde') → Formalism.L2.Host.IsDelta (H := D.host) p δ → (∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D) → ∃ (χ : (AE D)ˣ →* Circle) (de : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ), ChrEq χ δ ∧ XiRec D p de ∧ ∀ (x : (AE D)ˣ) (y : (GlobalTheory.FinalJoin.AfE D)ˣ), Formalism.L2.Theta.finPart D (x : AE D) = (y : GlobalTheory.FinalJoin.AfE D) → ((de y : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ) := by
  intro D p χ hp hδ hval
  obtain ⟨n, hn, ho⟩ := hδ.fin
  obtain ⟨c, h, hcv⟩ := exists_chrEq_val D χ fun x => by
    have h1 : χ.1 x ^ n = 1 := by
      have := DFunLike.congr_fun (congrArg Subtype.val ho) x
      simpa [MonoidHom.pow_apply] using this
    have h2 : ((χ.1 x : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'
  have h1 : ∀ x, c x ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  have h2 : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1 := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
    rw [map_pow, h1]
  have h3 : ∀ a, c (idF D a) = 1 := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    let b' : (AF D.host.F)ˣ := Units.map ((MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))) a
    have e : a = b' * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e, map_mul, map_mul, h2 (idF D b') rfl, GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ h hδ.triv b rfl, one_mul]
  obtain ⟨d, hd⟩ := GlobalTheory.DetRootChar.circle_hom_factor (Units.map (finPart D).toMonoidHom) c
    fun x hx => h2 x (congrArg Units.val hx)
  have hd' : ∀ (x : (AE D)ˣ) (y : (AfE D)ˣ), finPart D (x : AE D) = (y : AfE D) → d y = c x := fun x y hxy => by
    rw [← hd x]
    exact congrArg d (Units.ext hxy.symm)
  have hone : ∀ y, d y = 1 → (Circle.toUnits.comp d) y = 1 := fun y hy => by
    rw [MonoidHom.comp_apply, hy, map_one]
  have hcoe : ∀ y, (((Circle.toUnits.comp d) y : ℂˣ) : ℂ) = ((d y : Circle) : ℂ) := fun y => by simp
  have hpp : p.Prime ∧ ∀ i, p ≠ D.host.g i := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, fun i => (D.host.pde_ne_g i).2⟩
  refine ⟨c, Circle.toUnits.comp d, h, ⟨fun y a hy => hone y ?_, fun y a hy => hone y ?_, fun y hy hc => hone y ?_, ?_,
    ⟨n, hn, fun y => ?_⟩, fun y => ?_⟩, fun x y hxy => by rw [hcoe, hd' x y hxy]⟩
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨b, z, hz, hxz⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x (by
      rw [hx, hy]
      change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
      rw [map_one])
    rw [hd' x y hx, hxz, map_mul, h3, h2 z hz, mul_one]
  · have ha : a ≠ 0 := by
      rintro rfl
      obtain ⟨ι, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
      obtain ⟨P, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
      have e := congrArg (fun z => ι z P) y.mul_inv
      rw [hy, TensorProduct.tmul_zero, zero_mul, map_zero, map_one] at e
      exact zero_ne_one (α := P.adicCompletion D.host.E) e
    rw [hd' (Units.map (incA D).toMonoidHom (Units.mk0 a ha)) y hy.symm, h.1.2]
  · obtain ⟨x, hx0, hx, hx'⟩ := exists_lift D y
    rw [hd' x y hx]
    exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ h hδ.tame p hδ.unr x ⟨hx0, hx ▸ hy.1, hx' ▸ hy.2⟩ (hx ▸ hc)
  · obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
    obtain ⟨k, hk, hk1⟩ := exists_unit_ne_one χ P (hδ.tame P) fun hu => by
      have := (hδ.ine P hP 1).1 fun x hx => by rw [hu x hx, one_pow]
      omega
    have hcop : Nat.Coprime p (D.host.g 0 * D.host.g 1) :=
      ((Nat.coprime_primes hpp.1 (D.host.g_prime 0)).2 (hpp.2 0)).mul_right
        ((Nat.coprime_primes hpp.1 (D.host.g_prime 1)).2 (hpp.2 1))
    obtain ⟨e, x, he, hx, i1, i2⟩ := exists_local D P k hk (D.host.g 0 * D.host.g 1) fun hm => by
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hcop)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hm)))
    refine ⟨_, i1, i2, fun hh => hk1 (Units.ext ?_)⟩
    rw [← h.2 P e he k x hx, ← hd x, ← hcoe, hh]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    rw [MonoidHom.comp_apply, ← map_pow, hd' x y hx, h1, map_one]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨z, hz⟩ := hcv x
    rw [hcoe, hd' x y hx, hz]
    exact hval z

end GlobalTheory.TameFinitePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIoo
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expSol_eq_zero_of_eqOn_Ioo :
    ∀ (l : List ℂ) (f : ℝ → ℂ), f ∈ expSol l → ∀ s t : ℝ, s < t → (∀ x ∈ Set.Ioo s t, f x = 0) → f = 0 := by
  intro l
  induction l with
  | nil => intro f hf _ _ _ _; exact mem_expSol_nil.1 hf
  | cons c l ih =>
    intro f hf s t hst h0
    rw [mem_expSol_cons] at hf
    obtain ⟨hd, hg⟩ := hf
    have hg0 : deriv f - c • f = 0 := by
      refine ih _ hg s t hst (fun x hx => ?_)
      have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => h0 y hy)
      simp [Pi.sub_apply, hev.deriv_eq, h0 x hx]
    have hder : ∀ x, HasDerivAt f (c * f x) x := by
      intro x
      have h1 := congrFun hg0 x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have e : deriv f x = c * f x := sub_eq_zero.1 h1
      rw [← e]; exact (hd x).hasDerivAt
    set k : ℝ → ℂ := fun x => Complex.exp (-c * x) * f x with hk
    have hkd : ∀ x, HasDerivAt k 0 x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have h2 := ((h1.const_mul (-c)).cexp).mul (hder x)
      have h3 := h2.congr_deriv (show _ = (0 : ℂ) by ring)
      exact h3
    have hkc : ∀ x y, k x = k y := fun x y =>
      is_const_of_deriv_eq_zero (fun z => (hkd z).differentiableAt) (fun z => (hkd z).deriv) x y
    have hm : (s + t) / 2 ∈ Set.Ioo s t := ⟨by linarith, by linarith⟩
    funext x
    have := hkc x ((s + t) / 2)
    simp only [hk, h0 _ hm, mul_zero] at this
    simpa [Complex.exp_ne_zero] using this

end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem eq_smul_exp_of_deriv_eq {c : ℂ} {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (h : deriv f = c • f) : f = f 0 • (fun t : ℝ => Complex.exp (c * t)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * s)) (-c * Complex.exp (-c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c * 1) t :=
      (hasDerivAt_id t).ofReal_comp.const_mul (-c)
    have := h1.cexp
    simpa [mul_comm] using this
  set g : ℝ → ℂ := fun t => Complex.exp (-c * t) * f t with hg
  have hgd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h2 := (hd t).mul (hf t).hasDerivAt
    have e : deriv f t = c * f t := by
      have := congrFun h t; simpa using this
    rw [e] at h2
    have h3 := h2.congr_deriv (show _ = (0:ℂ) by ring)
    exact h3
  have hgdiff : Differentiable ℝ g := fun t => (hgd t).differentiableAt
  have hc := is_const_of_deriv_eq_zero hgdiff (fun t => (hgd t).deriv)
  funext t
  have h0 := hc t 0
  simp only [hg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h0, mul_comm (Complex.exp _) (f t), mul_assoc, ← Complex.exp_add]
  have e2 : -c * (t : ℂ) + c * t = 0 := by ring
  rw [e2, Complex.exp_zero, mul_one]

theorem expSol_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l)
  | [] => by
      have : expSol [] = ⊥ := rfl
      rw [this]; infer_instance
  | c :: l => by
      haveI := expSol_finiteDimensional l
      let φ : expSol (c :: l) →ₗ[ℂ] expSol l :=
        { toFun := fun f => ⟨deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ), (mem_expSol_cons.1 f.2).2⟩
          map_add' := fun f g => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            have hg := (mem_expSol_cons.1 g.2).1
            funext x
            simp only [Submodule.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [deriv_add (hf x) (hg x)]; ring
          map_smul' := fun k f => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            funext x
            simp only [Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Submodule.coe_smul_of_tower]
            rw [deriv_const_smul k (hf x)]; simp only [smul_eq_mul]; ring }
      have hker : ((LinearMap.ker φ).map (expSol (c :: l)).subtype) ≤
          Submodule.span ℂ {fun t : ℝ => Complex.exp (c * t)} := by
        rintro _ ⟨f, hf, rfl⟩
        have hd := (mem_expSol_cons.1 f.2).1
        have h0 : deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ) = 0 := by
          have := congrArg Subtype.val (LinearMap.mem_ker.1 hf)
          simpa [φ] using this
        have h1 : deriv (f : ℝ → ℂ) = c • (f : ℝ → ℂ) := sub_eq_zero.1 h0
        rw [Submodule.mem_span_singleton]
        exact ⟨(f : ℝ → ℂ) 0, (eq_smul_exp_of_deriv_eq hd h1).symm⟩
      haveI : FiniteDimensional ℂ ((LinearMap.ker φ).map (expSol (c :: l)).subtype) :=
        Submodule.finiteDimensional_of_le hker
      have hkerFG : (LinearMap.ker φ).FG :=
        Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype _)
          (Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance)
      have hmapFG : ((⊤ : Submodule ℂ (expSol (c :: l))).map φ).FG :=
        IsNoetherian.noetherian _
      have htop : (⊤ : Submodule ℂ (expSol (c :: l))).FG :=
        Submodule.fg_of_fg_map_of_fg_inf_ker φ hmapFG (by rw [top_inf_eq]; exact hkerFG)
      exact Module.finite_def.2 htop

end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProductStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integralIdeles_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (S L : ℂ), UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → 1 < S.re → HasProd (eulerFactor χ S) L → open Classical in HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q) // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q)) = z ∧ (y : Af E) ∈ hatO (condQ 𝔣 Q)} => (finPart χ z.1.out : ℂ) * ((modF z.1.out : ℝ) : ℂ) ^ S) (L * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) + ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2)) := by
  first | exact @GlobalTheory.CMVal.Euler.hasSum_euler | exact GlobalTheory.CMVal.Euler.hasSum_euler | (intros; apply GlobalTheory.CMVal.Euler.hasSum_euler <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilParts

theorem integrableOn_theta_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ :=
  GlobalTheory.DefiniteQuotient.integrableOn_theta

end GlobalTheory.WeilParts
end

