module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIndex

open GlobalTheory.SplitScalar

variable {D : D7}

theorem finPart_cA_eq_zero {a : AE D} (h : finPart D a = 0) : finPart D (cA D a) = 0 := by
  rw [← realIdem_mul_of_real h, RingHom.map_mul, cA_realIdem, RingHom.map_mul, finPart_realIdem, zero_mul]

theorem tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (β : Af F) (x : F) (k : ℕ) (t : E) :
    (algebraMap F (Af F) x + k • β) ⊗ₜ[F] t =
      (1 : Af F) ⊗ₜ[F] (algebraMap F E x * t) + k • (β ⊗ₜ[F] t) := by
  rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one x,
    TensorProduct.smul_tmul, Algebra.smul_def x t]

theorem map_add_nsmul {A B : Type} [Ring A] [Ring B] (f : A →+* B) (k : ℕ) (a s : A) :
    f (a + k • s) = f a + k • f s := by rw [map_add (f := _), map_nsmul]

theorem zero_eq_map_add_nsmul_zero {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) :
    0 = f (g 0 + k • 0) := by simp

theorem add_nsmul_residue_add {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r r' : E)
    (s s' : A) : f (g r + k • s) + f (g r' + k • s') = f (g (r + r') + k • (s + s')) := by
  rw [← map_add (f := _), map_add g, smul_add]; congr 1; abel

theorem neg_nsmul_residue {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r : E)
    (s : A) : -f (g r + k • s) = f (g (-r) + k • (-s)) := by
  rw [← map_neg, map_neg g, smul_neg, neg_add]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    ∃ (r : 𝓞 D.host.E) (s : AE D), finPart D s ∈ intAE D ∧ finPart D (cA D s) ∈ intAE D ∧
      z = finPart D (incA D (r : D.host.E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, t, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x * t, pairA D.host.F 0 β ⊗ₜ[D.host.F] (t : D.host.E),
      AddSubgroup.subset_closure ⟨β, hβ, t, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, GlobalTheory.FinWeil.sgO D t, ?_⟩, ?_⟩
    · rw [GlobalTheory.FinWeil.coe_sgO, ← GlobalTheory.SplitIdem.star_eq_conj]
      rfl
    · rw [hx]
      refine Eq.trans ?_ (map_add_nsmul (finPart D) k _ _).symm
      exact tmul_split β (x : D.host.F) k (t : D.host.E)
  | zero => exact ⟨0, 0, by rw [RingHom.map_zero]; exact zero_mem _,
      by rw [RingHom.map_zero, RingHom.map_zero]; exact zero_mem _,
      zero_eq_map_add_nsmul_zero (incA D) (finPart D) k⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [RingHom.map_add (f := _)]; exact add_mem h1 h1',
      by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]; exact add_mem h2 h2', ?_⟩
    exact add_nsmul_residue_add (incA D) (finPart D) k _ _ s s'
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [RingHom.map_neg]; exact neg_mem h1,
      by rw [RingHom.map_neg, RingHom.map_neg]; exact neg_mem h2, ?_⟩
    exact neg_nsmul_residue (incA D) (finPart D) k _ s

theorem core_mem {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (hΛ : ∀ r : O, ∀ u ∈ Λ, ι r • u ∈ Λ) (q : ℕ) (y : M) (hq : q • y ∈ Λ) (r r' : O)
    (h1 : ι (1 - r) • y ∈ Λ) (h2 : ι r' • y ∈ Λ)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : y ∈ Λ := by
  let I : Ideal O :=
    { carrier := {a | ι a • y ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        show ι (a + b) • y ∈ Λ
        rw [map_add (f := _), add_smul]; exact add_mem ha hb
      zero_mem' := by
        show ι 0 • y ∈ Λ
        rw [map_zero, zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha => by
        show ι (c * a) • y ∈ Λ
        rw [map_mul, mul_smul]; exact hΛ c _ ha }
  by_contra hy
  have hI : I ≠ ⊤ := fun h => by
    have : (1 : O) ∈ I := by rw [h]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨P, hPm, hIP⟩ := Ideal.exists_le_maximal I hI
  have hqI : (q : O) ∈ I := by
    show ι (q : O) • y ∈ Λ
    rw [map_natCast, Nat.cast_smul_eq_nsmul]; exact hq
  have hr := hP P hPm (hIP hqI) (hIP h2)
  have := add_mem (hIP h1 : 1 - r ∈ P) hr
  rw [sub_add_cancel] at this
  exact hPm.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem wachExpansion_smul_compatible {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (q : ℕ) (e f b s : A) (x : M)
    (h : (f - (b + q • s)) * e = 0) : b • e • x = (f * e) • x - s • e • q • x := by
  have : b * e = f * e - s * e * q := by
    rw [nsmul_eq_mul] at h
    linear_combination -h
  rw [smul_smul, this, sub_smul, mul_smul (s * e), mul_smul s, Nat.cast_smul_eq_nsmul]

theorem core_split {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (p : A → Prop) (hΛ : ∀ a, p a → ∀ u ∈ Λ, a • u ∈ Λ) (hι : ∀ r, p (ι r)) (q : ℕ) (x : M)
    (hx : q • x ∈ Λ) (e f s s' : A) (he : p e) (hs : p s) (hs' : p s') (hee : e * e = e) (hef : e * f = 0)
    (r r' : O) (h1 : (e - (ι r + q • s)) * e = 0) (h2 : (f - (ι r' + q • s')) * e = 0)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : e • x ∈ Λ := by
  have hqe : e • q • x ∈ Λ := hΛ e he _ hx
  refine core_mem ι Λ (fun a => hΛ _ (hι a)) q (e • x) (by rw [smul_comm]; exact hqe) r r' ?_ ?_ hP
  · rw [map_sub, map_one, sub_smul, one_smul, wachExpansion_smul_compatible q e e _ s x h1, hee, sub_sub_cancel]
    exact hΛ s hs _ hqe
  · rw [wachExpansion_smul_compatible q e f _ s' x h2, mul_comm, hef, zero_smul, zero_sub]
    exact neg_mem (hΛ _ hs' _ hqe)

theorem mem_of_inert {q : ℕ} (hq : q.Prime) (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (r : 𝓞 D.host.E)
    (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) (hqP : (q : 𝓞 D.host.E) ∈ P) (hr : GlobalTheory.FinWeil.sgO D r ∈ P) :
    r ∈ P := by
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hc := hin P hP.isPrime hne hqP
  rw [← hc] at hr
  exact Ideal.smul_mem_pointwise_smul_iff.1 hr

theorem mul_splitIdem_eq_zero {e : AE D} (he : IsSplitIdem D e) {a : AE D} (ha : finPart D a = 0) : a * e = 0 :=
  adele_ext (by rw [RingHom.map_mul, infPart_splitIdem he, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, ha, zero_mul, RingHom.map_zero])

theorem finPart_incA_mem (a : 𝓞 D.host.E) : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, a, rfl⟩

theorem split_mem {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {Λ : AddSubgroup (WO S T)}
    (hΛ : ∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) {q : ℕ} (hq : q.Prime)
    (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) {x : WO S T} (hx : q • x ∈ Λ) : e • x ∈ Λ := by
  have heI : finPart D e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  obtain ⟨r, s, hs, hs', hz⟩ := approx hq.pos heI
  have h0 : finPart D (e - (incA D (r : D.host.E) + q • s)) = 0 := by rw [RingHom.map_sub, ← hz, sub_self]
  have h0' := finPart_cA_eq_zero h0
  rw [RingHom.map_sub, map_add_nsmul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.SplitIdem.star_eq_conj,
    ← GlobalTheory.FinWeil.coe_sgO] at h0'
  exact core_split ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) Λ (fun a => finPart D a ∈ intAE D) hΛ
    finPart_incA_mem q x hx e (cA D e) s (cA D s) heI hs hs' he.1 he.2.1 r (GlobalTheory.FinWeil.sgO D r)
    (mul_splitIdem_eq_zero he h0) (mul_splitIdem_eq_zero he h0') (mem_of_inert hq hin r)

theorem not_dvd_of_saturated {M : Type} [AddCommGroup M] (Λ Λ' : AddSubgroup M) (h0 : Λ.relIndex Λ' ≠ 0)
    {q : ℕ} (hq : q.Prime) (h : ∀ x ∈ Λ', q • x ∈ Λ → x ∈ Λ) : ¬ q ∣ Λ.relIndex Λ' := by
  intro hdvd
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (Λ' ⧸ Λ.addSubgroupOf Λ') := Nat.finite_of_card_ne_zero h0
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := Λ' ⧸ Λ.addSubgroupOf Λ') q hdvd
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hqx : q • (x : M) ∈ Λ := by
    have h := addOrderOf_nsmul_eq_zero (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ')
    rw [hg, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h
    exact h
  have h2 : (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ') = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (h x x.2 hqx)
  rw [h2, addOrderOf_zero] at hg
  exact hq.one_lt.ne hg

theorem mem_of_parts {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : AddSubgroup M) (e f : A) (x : M)
    (h1 : e • x ∈ Λ) (h2 : f • x ∈ Λ) (h3 : (1 - (e + f)) • x ∈ Λ) : x ∈ Λ := by
  have h := add_mem (add_mem h1 h2) h3
  rwa [← add_smul, ← add_smul, add_sub_cancel, one_smul] at h

theorem not_dvd_relIndex : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  intro D S T e he Λ Λ' hΛ _ _ h1 h0 q hq hin
  exact not_dvd_of_saturated Λ Λ' h0 hq fun x hx hqx => mem_of_parts Λ e (cA D e) x
    (split_mem he hΛ hq hin hqx) (split_mem (isSplitIdem_conj he) hΛ hq hin hqx) (h1 x hx)

end GlobalTheory.SplitIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_cechAug_of_comp_iso (R : Type) [CommRing R] (F : Shv R) {V W T : Scheme.{0}} (g : V ⟶ W) (t : W ⟶ T) [IsIso t]
    (h : Eqv R (_root_.GlobalTheory.EtC.cechAug (g ≫ t)) F) : Eqv R (_root_.GlobalTheory.EtC.cechAug g) F := by
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let e : Arrow.mk (yoneda.map g) ≅ Arrow.mk (yoneda.map (g ≫ t)) :=
    Arrow.isoMk (Iso.refl _) (yoneda.mapIso (asIso t)) (by simp)
  let φ := SimplicialObject.augmentedCechNerve.mapIso e
  have hw : φ.hom.left ≫ _root_.GlobalTheory.EtC.cechAug (g ≫ t) = _root_.GlobalTheory.EtC.cechAug g ≫ (SimplicialObject.const _).map φ.hom.right := φ.hom.w
  have hl : IsIso φ.hom.left := (SimplicialObject.Augmented.drop.mapIso φ).isIso_hom
  have hr : IsIso ((SimplicialObject.const _).map φ.hom.right) := by
    have : IsIso φ.hom.right := (SimplicialObject.Augmented.point.mapIso φ).isIso_hom
    infer_instance
  have h1 : Eqv R (φ.hom.left ≫ _root_.GlobalTheory.EtC.cechAug (g ≫ t)) F := ((E.2.1 _ _ _ _ _).1 (E.1 _ _ _ hl)) h
  rw [hw] at h1
  exact (E.2.1 _ _ _ _ _).2.2 (E.1 _ _ _ hr) h1

theorem b4 : B4 := by
  intro q Y X f _ _ hq i
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  refine GlobalTheory.T.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X (_root_.GlobalTheory.EtC.cech f) (sch.obj X) (_root_.GlobalTheory.EtC.cechAug f) (sch.map (𝟙 X))
    (GlobalTheory.T.tateTwist_finitary q i) ?_ ?_ ?_
  · intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom Y X f ‹_› k
    haveI := hπ
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [CategoryTheory.Functor.map_id, Category.comp_id, he]
  · intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    simp [sch]
  · intro O _ s hs
    obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
    have hqO : IsUnit ((q : ℕ) : O) := by
      have := hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom
      simpa using this
    have hg : Eqv _ (_root_.GlobalTheory.EtC.cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
      eqv_cechAug_of_comp_iso _ _ _ (pullback.snd (𝟙 X) s)
        (GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh q i O hs.1 hqO _ _ inferInstance inferInstance)
    have hm : (bcMap (_root_.GlobalTheory.EtC.cechAug f) (sch.map (𝟙 X))).app (Over.mk s) =
        e₁.inv ≫ _root_.GlobalTheory.EtC.cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) ≫ e₂.hom := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [hm]
    exact (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 hg (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult

section
variable {H H' : Type} [Group H] [Group H'] {X : Type} [AddCommGroup X] [Module ℂ X]

def subrepCompIso (ρ : Representation ℂ H' X) (φ : H ≃* H') :
    Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_mulEquiv (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subrepCompIso ρ φ).isSimpleOrder

theorem isAdmissible_comp_equiv [TopologicalSpace H] [TopologicalSpace H'] (ρ : Representation ℂ H' X) (Φ : H ≃ₜ* H')
    (h : GlobalTheory.PRep.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) := by
  refine ⟨fun v => (h.1 v).preimage Φ.continuous, fun K hKo hKc => ?_⟩
  have e : GlobalTheory.PRep.fixed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) K =
      GlobalTheory.PRep.fixed ρ (K.map Φ.toMulEquiv.toMonoidHom) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (Φ.toHomeomorph.isOpenMap _ hKo) (hKc.image Φ.continuous)

end

theorem isDecomp_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type)
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'),
    IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  intro H H' _ _ _ _ X _ _ ρ C Φ h x hx ho
  have ho' : IsOpen {g : H' | ρ g x = x} := by
    have := ho.preimage Φ.symm.continuous
    convert this using 1
    ext g
    show ρ g x = x ↔ ρ (Φ (Φ.symm g)) x = x
    rw [Φ.apply_symm_apply]
  have hm := h x hx ho'
  refine (?_ : irrSum ρ C ≤ irrSum (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C) hm
  refine iSup₂_le fun U hU => ?_
  refine le_iSup₂_of_le (f := fun (U : Subrepresentation (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X))
    (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) => U.toSubmodule)
    ((subrepCompIso ρ Φ.toMulEquiv).symm U) ⟨hU.1, ?_, ?_⟩ le_rfl
  · exact isIrreducible_comp_mulEquiv U.toRepresentation Φ.toMulEquiv hU.2.1
  · exact isAdmissible_comp_equiv U.toRepresentation Φ hU.2.2

end GlobalTheory.CuspMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace SmoothGrowth

theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

theorem continuous_compGL (w : InfinitePlace E) : Continuous (compGL (n := n) w) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) := Units.continuous_val
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) :=
      Units.continuous_coe_inv
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have e : (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j) =
        fun g => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w := by
      funext g
      rw [← map_inv]; rfl
    change Continuous (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j)
    rw [e]
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))

theorem continuous_htInf : Continuous (htInf : GL (Fin n) (Cinf E) → ℝ) := by
  unfold htInf
  exact continuous_finsetProd _ fun w _ => continuous_htGL.comp (continuous_compGL w)

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

theorem smoothMatInf_integrand_eq (α : (Fin n → Fin n → Cinf E) → ℂ)
    (hsub : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E))
    (a : Fin n → Fin n → Cinf E) :
    α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a) = α a * W (g * toGLInf (Matrix.of a)) := by
  by_cases ha : a ∈ tsupport α
  · have hu : IsUnit (Matrix.of a) := hsub ha
    have : (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a =
        ((g * toGLInf (Matrix.of a) : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) := by
      rw [Units.val_mul, val_toGLInf hu]
    rw [this, onMatInf_val]
  · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]

end SmoothGrowth

open SmoothGrowth

theorem isModGrowthInf_smoothMatInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ),
    Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} →
    ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  intro E _ _ n α hα hcs hsub W hW
  haveI : FirstCountableTopology (GL (Fin n) (Cinf E)) :=
    (isOpenEmbedding_valGLInf (E := E) (n := n)).isInducing.firstCountableTopology
  obtain ⟨hWc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  have hK : IsCompact (tsupport α) := hcs
  have hcont : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
    continuous_htInf.comp_continuousOn (continuousOn_toGLInf.mono hsub)
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hcont
  set R : ℝ := max R₀ 1
  have hRb : ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R := fun a ha => by
    have := hR₀ a ha
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hαi : Integrable (fun a => ‖α a‖) (volume : Measure (Fin n → Fin n → Cinf E)) :=
    (hα.integrable_of_hasCompactSupport hcs).norm
  set F : GL (Fin n) (Cinf E) → (Fin n → Fin n → Cinf E) → ℂ := fun g a => α a * W (g * toGLInf (Matrix.of a)) with hF
  have hsm : smoothMatInf α W = fun g => ∫ a, F g a := by
    funext g
    unfold smoothMatInf
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smoothMatInf_integrand_eq α hsub W g a)
  have hbound : ∀ g a, ‖F g a‖ ≤ ‖α a‖ * (C * R ^ N * htInf g ^ N) := by
    intro g a
    by_cases ha : a ∈ tsupport α
    · simp only [hF, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : htInf (g * toGLInf (Matrix.of a)) ≤ htInf g * R :=
        (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hRb a ha) (htInf_pos' _).le)
      have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
      calc ‖W (g * toGLInf (Matrix.of a))‖ ≤ C * htInf (g * toGLInf (Matrix.of a)) ^ N := hC _
        _ ≤ C * (htInf g * R) ^ N := mul_le_mul_of_nonneg_left h2 hC0
        _ = C * R ^ N * htInf g ^ N := by ring
    · simp [hF, image_eq_zero_of_notMem_tsupport ha]
  have hmeas : ∀ g, AEStronglyMeasurable (F g) volume := fun g =>
    (hα.measurable.mul (measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop)
      (fun i j => measurable_toGLInf_entry i j))).aestronglyMeasurable
  rw [hsm]
  refine ⟨?_, C * R ^ N * ∫ a, ‖α a‖, N, fun g => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have hev : ∀ᶠ g in nhds g₀, htInf g ≤ htInf g₀ + 1 :=
      (continuous_htInf.continuousAt).eventually (gt_mem_nhds (lt_add_one (htInf g₀))) |>.mono fun _ h => h.le
    refine continuousAt_of_dominated (bound := fun a => ‖α a‖ * (C * R ^ N * (htInf g₀ + 1) ^ N))
      (Filter.Eventually.of_forall hmeas) ?_ (hαi.mul_const _) ?_
    · filter_upwards [hev] with g hg
      refine Filter.Eventually.of_forall fun a => (hbound g a).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
      exact pow_le_pow_left₀ (htInf_pos' _).le hg N
    · refine Filter.Eventually.of_forall fun a => ?_
      exact (continuous_const.mul (hWc.comp (continuous_id.mul continuous_const))).continuousAt
  · calc ‖∫ a, F g a‖ ≤ ∫ a, ‖α a‖ * (C * R ^ N * htInf g ^ N) :=
          norm_integral_le_of_norm_le (hαi.mul_const _) (Filter.Eventually.of_forall (hbound g))
      _ = C * R ^ N * (∫ a, ‖α a‖) * htInf g ^ N := by rw [integral_mul_const]; ring

end GlobalTheory.JSW.MirCinf
end
end

