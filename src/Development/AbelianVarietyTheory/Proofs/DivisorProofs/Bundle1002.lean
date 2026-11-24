module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfLe
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClsInt

section Count
variable {H Γ : Type} [Group H] [Group Γ] (ι : Γ →* H) (J J' : Subgroup H)

def toLev (a : H) : Bridge.stab ι J a →* J where
  toFun s := ⟨a⁻¹ * ι s * a, (Bridge.mem_stab _).1 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem sum_inv_card_stab (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0) {Cl : Type} [Fintype Cl] (y : Cl → H)
    (hy : Bridge.IsReps ι J' y) (a : H) [Finite (Bridge.stab ι J a)] :
    ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ := by
  let X := J ⧸ J'.subgroupOf J
  have hX : Nat.card X = J'.relIndex J := rfl
  haveI : Finite X := Nat.finite_of_card_ne_zero (hX ▸ hN)
  letI : Fintype X := Fintype.ofFinite X
  letI : MulAction (Bridge.stab ι J a) X := MulAction.compHom X (toLev ι J a)
  have hsm : ∀ (s : Bridge.stab ι J a) (u : J), s • (u : X) = ((toLev ι J a s * u : J) : X) := fun _ _ => rfl
  choose idx hidx hu using fun h => (hy h)
  have hi : ∀ h k, idx h = k ↔ ∃ γ, ∃ w ∈ J', h = ι γ * y k * w := by
    intro h k
    constructor
    · rintro rfl
      obtain ⟨γ, w, e⟩ := hidx h
      exact ⟨γ, w, w.2, e⟩
    · rintro ⟨γ, w, hw, e⟩
      exact (hu h k ⟨γ, ⟨w, hw⟩, e⟩).symm
  let f : X → Cl := fun x => idx (a * (x.out : J))
  have hq : ∀ u v : J, (u : X) = (v : X) ↔ (u : H)⁻¹ * v ∈ J' := fun u v => QuotientGroup.eq
  have hf : ∀ (u : J) k, f (u : X) = k ↔ ∃ γ, ∃ w ∈ J', a * u = ι γ * y k * w := by
    intro u k
    have h0 : ((Quotient.out (u : X) : J) : H)⁻¹ * u ∈ J' := (hq _ _).1 (Quotient.out_eq _)
    change idx _ = k ↔ _
    rw [hi]
    constructor
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw h0, by rw [← mul_assoc, ← e]; group⟩
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw (J'.inv_mem h0), by rw [← mul_assoc, ← e]; group⟩
  have hS : ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hN' : ((J'.relIndex J : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hcount : J'.relIndex J = ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      (Finset.univ.filter fun x => f x = k).card := by
    rw [← hX, Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_eq_sum_card_fiberwise fun x _ => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨γ, w, hw, e⟩ := (hf u _).1 rfl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨γ⁻¹, u * w⁻¹, J.mul_mem u.2 (J.inv_mem (hle hw)), ?_⟩
    rw [map_inv, mul_assoc, ← mul_assoc a, e]; group
  have key : ∀ k, (∃ γ, ∃ u ∈ J, y k = ι γ * a * u) →
      (Finset.univ.filter fun x => f x = k).card * Nat.card (Bridge.stab ι J' (y k)) =
        Nat.card (Bridge.stab ι J a) := by
    rintro k ⟨γ₀, u₀, hu₀, e₀⟩
    let x₀ : X := ((⟨u₀, hu₀⟩ : J) : X)
    have h1 : MulAction.orbit (Bridge.stab ι J a) x₀ = ↑(Finset.univ.filter fun x => f x = k) := by
      ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hf, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨s, hs⟩
        rw [hsm, hq] at hs
        refine ⟨s * γ₀⁻¹, _, hs, ?_⟩
        change _ = _ * ((a⁻¹ * ι s * a * u₀)⁻¹ * u)
        rw [e₀, map_mul, map_inv]; group
      · rintro ⟨γ, w, hw, e⟩
        have e1 : a⁻¹ * ι (γ * γ₀) * a = u * w⁻¹ * u₀⁻¹ := by
          have : (u : H) = a⁻¹ * (ι γ * y k * w) := by rw [← e]; group
          rw [this, e₀, map_mul]; group
        refine ⟨⟨γ * γ₀, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
        · rw [e1]; exact J.mul_mem (J.mul_mem u.2 (J.inv_mem (hle hw))) (J.inv_mem hu₀)
        · rw [hsm, hq]
          change (a⁻¹ * ι (γ * γ₀) * a * u₀)⁻¹ * u ∈ J'
          rw [e1, show ((u : H) * w⁻¹ * u₀⁻¹ * u₀)⁻¹ * u = w by group]
          exact hw
    have h2 : ∀ s : Bridge.stab ι J a, s ∈ MulAction.stabilizer (Bridge.stab ι J a) x₀ ↔
        γ₀ * s * γ₀⁻¹ ∈ Bridge.stab ι J' (y k) := by
      intro s
      rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, hq, Bridge.mem_stab]
      change u₀⁻¹ * (a⁻¹ * ι s * a * u₀) ∈ J' ↔ _
      rw [e₀, map_mul, map_mul, map_inv, show (ι γ₀ * a * u₀)⁻¹ * (ι γ₀ * ι s * (ι γ₀)⁻¹) * (ι γ₀ * a * u₀) =
        u₀⁻¹ * (a⁻¹ * ι s * a * u₀) by group]
    have h3 : Nat.card (MulAction.stabilizer (Bridge.stab ι J a) x₀) = Nat.card (Bridge.stab ι J' (y k)) := by
      refine Nat.card_eq_of_bijective (fun s => ⟨γ₀ * s.1 * γ₀⁻¹, (h2 _).1 s.2⟩) ⟨fun s t e => ?_, fun t => ?_⟩
      · have := congrArg Subtype.val e
        simp only [mul_left_inj, mul_right_inj] at this
        exact Subtype.ext (Subtype.ext this)
      · have ht := (Bridge.mem_stab _).1 t.2
        have hm : γ₀⁻¹ * t * γ₀ ∈ Bridge.stab ι J a := by
          rw [Bridge.mem_stab, map_mul, map_mul, map_inv,
            show a⁻¹ * ((ι γ₀)⁻¹ * ι t * ι γ₀) * a = u₀ * ((ι γ₀ * a * u₀)⁻¹ * ι t * (ι γ₀ * a * u₀)) * u₀⁻¹ by group,
            ← e₀]
          exact J.mul_mem (J.mul_mem hu₀ (hle ht)) (J.inv_mem hu₀)
        have e : γ₀ * (γ₀⁻¹ * t * γ₀) * γ₀⁻¹ = t := by group
        exact ⟨⟨⟨_, hm⟩, (h2 _).2 (by rw [e]; exact t.2)⟩, Subtype.ext e⟩
    rw [← h3, ← Set.ncard_coe_finset, ← h1, ← Nat.card_coe_set_eq, ← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ x₀)
  have h4 : ∀ k ∈ Finset.univ.filter (fun k => ∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ *
        (((Finset.univ.filter fun x => f x = k).card : ℕ) : ℂ) := by
    intro k hk
    have h5 := key k (Finset.mem_filter.1 hk).2
    have h6 := hS
    rw [← h5] at h6 ⊢
    push_cast at h6 ⊢
    have h7 := left_ne_zero_of_mul h6
    have h8 := right_ne_zero_of_mul h6
    field_simp
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Nat.cast_sum, ← hcount]
  field_simp

end Count

theorem integral_eq_sum_of_le {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J J' : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0)
    (Cl : Type) [Fintype Cl] (h : Cl → G) (hy : Bridge.IsReps (π.comp Γ.subtype) J' fun k => π (h k))
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (hr : ∀ u, π u ∈ J → ∀ x, Φ (x * u) = Φ x) :
    ∫ x in 𝓖, Φ x ∂ν = ∑ k, ((J'.relIndex J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (π.comp Γ.subtype) J' (π (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  set ι := π.comp Γ.subtype with hι
  choose σ hσ using hπ
  have hΦ : ∀ x, Φ (σ (π x)) = Φ x := fun x => by
    rw [← hr ((σ (π x))⁻¹ * x) (by rw [map_mul, map_inv, hσ, inv_mul_cancel]; exact J.one_mem),
      mul_inv_cancel_left]
  have hΦ' : ∀ (γ : Γ) z (k : J), Φ (σ (ι γ * z * k)) = Φ (σ z) := fun γ z k => by
    have : ι γ * z * k = π (γ * σ z * σ k) := by rw [map_mul, map_mul, hσ, hσ]; rfl
    rw [this, hΦ, hr _ (by rw [hσ]; exact k.2), hl _ γ.2]
  have hfin : ∀ z, Finite (Bridge.stab ι J z) := fun z => by
    have := GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ (J.comap π) h𝓖 (h1 ▸ one_ne_zero)
      (h1 ▸ ENNReal.one_ne_top) (σ z)
    refine Set.Finite.subset this fun γ hγ => ?_
    rw [Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, hσ]
    exact (Bridge.mem_stab _).1 hγ
  let r : Setoid Cl :=
    { r := fun k l => ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h l) * u
      iseqv :=
        ⟨fun k => ⟨1, 1, J.one_mem, by simp⟩,
          fun ⟨γ, u, hu, e⟩ => ⟨γ⁻¹, u⁻¹, J.inv_mem hu, by rw [e, map_inv]; group⟩,
          fun ⟨γ, u, hu, e⟩ ⟨δ, v, hv, e'⟩ => ⟨γ * δ, v * u, J.mul_mem hv hu, by rw [e, e', map_mul]; group⟩⟩ }
  have hq : ∀ k (i : Quotient r), Quotient.mk r k = i ↔ ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h i.out) * u :=
    fun k i => Quotient.mk_eq_iff_out
  have hreps : Bridge.IsReps ι J fun i : Quotient r => π (h i.out) := by
    intro z
    obtain ⟨k, ⟨γ, w, e⟩, -⟩ := hy z
    refine ⟨Quotient.mk r k, ?_, ?_⟩
    · obtain ⟨δ, u, hu, e'⟩ := (hq k _).1 rfl
      exact ⟨γ * δ, ⟨u * w, J.mul_mem hu (hle w.2)⟩, by simp only [] at e ⊢; rw [e, e', map_mul]; group⟩
    · rintro i ⟨δ, u, e'⟩
      refine ((hq k i).2 ⟨γ⁻¹ * δ, u * (w : H)⁻¹, J.mul_mem u.2 (J.inv_mem (hle w.2)), ?_⟩).symm
      simp only [] at e e'
      have : π (h k) = (ι γ)⁻¹ * z * (w : H)⁻¹ := by rw [e]; group
      rw [this, e', map_mul, map_inv]; group
  have key := GlobalTheory.ClassUnfold.integral_eq_sum_of_surjective ν Γ π (fun z => ⟨σ z, hσ z⟩) J 𝓖 h𝓖 ho h1
    (Quotient r) _ hreps (fun _ => hfin _) (fun z => Φ (σ z)) hΦ'
  simp only [hΦ] at key
  rw [key, ← Finset.sum_fiberwise Finset.univ (Quotient.mk r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := hfin (π (h i.out))
  rw [← sum_inv_card_stab ι J J' hle hN _ hy, Finset.sum_mul]
  refine Finset.sum_congr (Finset.filter_congr fun k _ => (hq k i).symm) fun k hk => ?_
  obtain ⟨γ, u, hu, e⟩ := (hq k i).1 (Finset.mem_filter.1 hk).2
  rw [← hΦ (h k), e, hΦ' γ _ ⟨u, hu⟩, hΦ]

theorem integral_eq_classSum_of_le : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.IsPosDef → V.SigOK → IsMeasDef V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) ν 𝓕 → (∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)) → ∀ (J' : Subgroup (Bridge.Gf V)) (Cl : Type) [Fintype Cl] (h : Cl → GA D V), J' ≤ (levEnv V β L).J → J'.relIndex (levEnv V β L).J ≠ 0 → Bridge.IsReps (Bridge.ratF V) J' (fun k => fin V (h k)) → (∀ k, h k ∈ GfC V) → ∀ Φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ x, Φ (γ * x) = Φ x) → (∀ u : GA D V, fin V u ∈ (levEnv V β L).J → ∀ x, Φ (x * u) = Φ x) → ∫ x in 𝓕, Φ x ∂ν = ∑ k, ((J'.relIndex (levEnv V β L).J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (Bridge.ratF V) J' (fin V (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  intro D V β L ν 𝓕 _ _ hν hL J' Cl _ h hle hN hy _ Φ hl hr
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hν.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict =
      (Formalism.L2.DIV.lev D.sp.cm V.gram β L).comap (Lev.finE V) := by
    ext g
    exact (hL (Lev.finE V g)).symm
  refine integral_eq_sum_of_le ν (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J J' 𝓕 hν.2 ?_ ?_ hle hN Cl h hy Φ hl hr
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hν.1

end GlobalTheory.ClsInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicType
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem UpT.diag_ne_zero {n : ℕ} {b : Mt n} (hb : UpT b) (a : Fin n) : b a a ≠ 0 := by
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular (fun i j hij => hb.2 i j hij)
  have h := hb.1
  rw [hdet, Finset.prod_ne_zero_iff] at h
  exact h a (Finset.mem_univ a)

theorem holFn_integral : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  intro n ι _ _ Hm q x₀ w hx Ω _ ν _ f C hf hC hmeas

  have hf' : ∀ o, ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f o u = P fun τ => (u τ * x₀ τ : Mt n) := hf
  choose Pc hPc using hf'

  have hβ := fun τ => _root_.GlobalTheory.HolDict.GS.smooth_gramSchmidt n (Hm τ) (q τ) (x₀ τ) (hx τ)
  choose β hβc hβ using hβ
  obtain ⟨hopen, -, hmul, hx0⟩ := _root_.GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ hx

  let uu : (ι → Fin n → Fin n → ℂ) → ι → Mt n :=
    fun y τ => Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹
  let cc : (ι → Fin n → Fin n → ℂ) → ℂ := fun y => ∏ τ, ∏ a, (β τ (y τ)) a a ^ w τ a
  have huu : ∀ y ∈ frDoms Hm q, uu y ∈ UG Hm := fun y hy τ => (hβ τ (y τ) (hy τ)).2

  have hkey : ∀ o, ∀ y ∈ frDoms Hm q, Pc o y = cc y * f o (uu y) := by
    intro o y hy
    have hu := huu y hy
    have hone : ∀ _τ : ι, UpT (1 : Mt n) := fun _ =>
      ⟨by simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
    have hfr : (fun τ => (uu y τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
      have := hmul (uu y) hu (fun _ => 1) hone (fun τ => (x₀ τ : Mt n)) hx0
      simp only [Matrix.mul_one] at this
      exact this
    have hB : ∀ τ, UpT (Matrix.of (β τ (y τ))) := fun τ => (hβ τ (y τ) (hy τ)).1
    have heq := (hPc o).1.2 (fun τ => (uu y τ * x₀ τ : Mt n)) hfr
      (fun τ => Matrix.of (β τ (y τ))) hB
    have hrec : (fun τ => (Matrix.of ((uu y τ * x₀ τ : Mt n)) * Matrix.of (β τ (y τ)) : Mt n)) = y := by
      funext τ
      have hX : (x₀ τ)⁻¹ * x₀ τ = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx0 τ).1)
      have hBB : (Matrix.of (β τ (y τ)))⁻¹ * Matrix.of (β τ (y τ)) = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hB τ).1)
      show Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹ * x₀ τ * Matrix.of (β τ (y τ)) = y τ
      rw [Matrix.mul_assoc (Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹), hX, Matrix.mul_one,
        Matrix.mul_assoc, hBB, Matrix.mul_one]
      rfl
    rw [hrec] at heq
    rw [heq, ← (hPc o).2 (uu y) hu]
    rfl

  have hcc : ContinuousOn cc (frDoms Hm q) := by
    apply continuousOn_finsetProd _
    intro τ _
    apply continuousOn_finsetProd _
    intro a _
    have h1 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ)) (frDoms Hm q) :=
      (hβc τ).continuousOn.comp (continuous_apply τ).continuousOn (fun y hy => hy τ)
    have h2 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ) a a) (frDoms Hm q) :=
      (show Continuous fun M : Fin n → Fin n → ℂ => M a a from
        (continuous_apply a).comp (continuous_apply a)).comp_continuousOn h1
    exact h2.zpow₀ _ (fun y hy => Or.inl (UpT.diag_ne_zero (hβ τ (y τ) (hy τ)).1 a))
  have hPmeas : ∀ y ∈ frDoms Hm q, AEStronglyMeasurable (fun o => Pc o y) ν := by
    intro y hy
    have : (fun o => Pc o y) = fun o => cc y * f o (uu y) := funext fun o => hkey o y hy
    rw [this]
    exact (hmeas (uu y) (huu y hy)).const_mul (cc y)
  have hdom : ∀ x ∈ frDoms Hm q, ∃ s ∈ 𝓝 x, ∃ bound : Ω → ℝ, Integrable bound ν ∧
      ∀ᵐ o ∂ν, ∀ y ∈ s, ‖Pc o y‖ ≤ bound o := by
    intro x hxm
    have hca : ContinuousAt cc x := hcc.continuousAt (hopen.mem_nhds hxm)
    have hev : ∀ᶠ y in 𝓝 x, ‖cc y‖ < ‖cc x‖ + 1 :=
      hca.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨{y | ‖cc y‖ < ‖cc x‖ + 1} ∩ frDoms Hm q, Filter.inter_mem hev (hopen.mem_nhds hxm),
      fun _ => (‖cc x‖ + 1) * max C 0, integrable_const _, Filter.Eventually.of_forall ?_⟩
    intro o y hy
    rw [hkey o y hy.2, norm_mul]
    exact mul_le_mul hy.1.le (le_max_of_le_left (hC o (uu y) (huu y hy.2))) (norm_nonneg _)
      (by positivity)
  unfold HolFn HolSec
  refine ⟨fun y => ∫ o, Pc o y ∂ν, ⟨?_, ?_⟩, ?_⟩
  · exact (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated hopen hPmeas
      (Filter.Eventually.of_forall fun o => (hPc o).1.1) hdom).1
  · intro x hxm b hb
    calc ∫ o, Pc o (fun τ => (Matrix.of (x τ) * b τ : Mt n)) ∂ν
        = ∫ o, (∏ τ, ∏ a, b τ a a ^ w τ a) * Pc o x ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).1.2 x hxm b hb)
      _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * ∫ o, Pc o x ∂ν := integral_const_mul _ _
  · intro u hu
    exact integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).2 u hu)

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiFiniteSubspace
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

private lemma span_add_le {H : Type} [Group H] (K : Subgroup H) (f f' : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (f + f') (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} ⊔
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f' (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, _,
    Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, ?_⟩
  funext g; simp

private lemma span_smul_le {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (f : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (c • f) (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  have : (fun g => (c • f) (k * g * k')) = c • fun g => f (k * g * k') := by funext g; simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, k', hk', rfl⟩)

private lemma span_zero_le {H : Type} [Group H] (K : Subgroup H) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (0 : H → ℂ) (k * g * k')} ≤ ⊥ := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  rfl

theorem isBiFinite_subspace : ∀ (H : Type) [Group H] (K : Subgroup H), IsBiFinite K (0 : H → ℂ) ∧
    (∀ f f' : H → ℂ, IsBiFinite K f → IsBiFinite K f' → IsBiFinite K (f + f')) ∧
    ∀ (c : ℂ) (f : H → ℂ), IsBiFinite K f → IsBiFinite K (c • f) := by
  intro H _ K
  refine ⟨?_, fun f f' hf hf' => ?_, fun c f hf => ?_⟩
  · unfold IsBiFinite
    exact Submodule.finiteDimensional_of_le (span_zero_le K)
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_add_le K f f')
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_smul_le K c f)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwiner
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_map : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) →
    UnitOn s F U → UnitOn s F' (U.map f) := by
  intro ι M _ _ _ _ s F M' _ _ F' f U hF hU
  obtain ⟨hfd, hst, ip, hherm, hpos, hadj⟩ := hU
  let K : Submodule ℂ M := U ⊓ LinearMap.ker f
  have hKU : ∀ k ∈ K, k ∈ U := fun k hk => (Submodule.mem_inf.mp hk).1
  have hKf : ∀ k ∈ K, f k = 0 := fun k hk => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hk).2
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le (inf_le_left : K ≤ U)
  let n := Module.finrank ℂ K
  let b := Module.finBasis ℂ K
  let ψ : M →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => ip (b i : M))
  let U1 : Submodule ℂ M := U ⊓ LinearMap.ker ψ
  have hU1U : ∀ w ∈ U1, w ∈ U := fun w hw => (Submodule.mem_inf.mp hw).1
  have hA : ∀ w ∈ U1, ∀ k ∈ K, ip k w = 0 := by
    intro w hw k hk
    have hw' : ∀ i, ip (b i : M) w = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2) i
      simpa [ψ] using this
    have h0 : ((ip.flip w).comp K.subtype) = 0 := b.ext (fun i => by simpa using hw' i)
    have := LinearMap.congr_fun h0 ⟨k, hk⟩
    simpa using this
  have hA' : ∀ w ∈ U1, ∀ k ∈ K, ip w k = 0 := by
    intro w hw k hk
    have := hherm k (hKU k hk) w (hU1U w hw)
    rw [hA w hw k hk, star_zero] at this
    exact this.symm
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have hk1 : (k : M) ∈ U1 := Submodule.mem_inf.mpr ⟨hKU k k.2, LinearMap.mem_ker.mpr (by simpa using hk)⟩
    have h0 := hA _ hk1 _ k.2
    by_contra hne
    have hne' : (k : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hKU k k.2) hne'
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective (ψ.comp K.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [n])).mp hinj
  have hdec : ∀ u ∈ U, ∃ k ∈ K, u - k ∈ U1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hsurj (ψ u)
    refine ⟨k, k.2, Submodule.mem_inf.mpr ⟨U.sub_mem hu (hKU k k.2), LinearMap.mem_ker.mpr ?_⟩⟩
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa using hk.symm)
  have hinj1 : LinearMap.ker (f.comp U1.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwK : (w : M) ∈ K := Submodule.mem_inf.mpr ⟨hU1U w w.2, LinearMap.mem_ker.mpr (by simpa using hw)⟩
    have h0 := hA _ w.2 _ hwK
    by_contra hne
    have hne' : (w : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hU1U w w.2) hne'
    rw [h0] at this
    simp at this
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (f.comp U1.subtype) hinj1
  let g : M' →ₗ[ℂ] M := U1.subtype.comp h
  have hg : ∀ w ∈ U1, g (f w) = w := by
    intro w hw
    have := congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩)
    simpa [g] using this
  have hkey : ∀ u ∈ U, g (f u) ∈ U1 ∧ u - g (f u) ∈ K := by
    intro u hu
    obtain ⟨k, hk, hw⟩ := hdec u hu
    have hfu : f u = f (u - k) := by rw [map_sub, hKf k hk, sub_zero]
    rw [hfu, hg _ hw, sub_sub_cancel]
    exact ⟨hw, hk⟩
  have hgU1 : ∀ x ∈ U.map f, g x ∈ U1 := by
    rintro x ⟨u, hu, rfl⟩
    exact (hkey u hu).1
  have hfg : ∀ x ∈ U.map f, f (g x) = x := by
    rintro x ⟨u, hu, rfl⟩
    have := hKf _ (hkey u hu).2
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  haveI := hfd
  refine ⟨inferInstance, ?_, (ip.comp g).compl₂ g, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨u, hu, rfl⟩
    exact ⟨F a b u, hst a b hab u hu, hF a b hab u hu⟩
  · intro x hx y hy
    exact hherm _ (hU1U _ (hgU1 x hx)) _ (hU1U _ (hgU1 y hy))
  · intro x hx hne
    apply hpos _ (hU1U _ (hgU1 x hx))
    intro h0
    apply hne
    rw [← hfg x hx]
    change f (g x) = 0
    rw [h0, map_zero]
  · intro a b hab x hx y hy
    have hu0 := hgU1 x hx
    have hv0 := hgU1 y hy
    have e1 : F' a b x = f (F a b (g x)) := by rw [hF a b hab _ (hU1U _ hu0), hfg x hx]
    have e2 : F' b a y = f (F b a (g y)) := by rw [hF b a hab.symm _ (hU1U _ hv0), hfg y hy]
    change ip (g (F' a b x)) (g y) = ip (g x) (g (F' b a y))
    rw [e1, e2]
    have hk1 := (hkey _ (hst a b hab _ (hU1U _ hu0))).2
    have hk2 := (hkey _ (hst b a hab.symm _ (hU1U _ hv0))).2
    have l1 : ip (g (f (F a b (g x)))) (g y) = ip (F a b (g x)) (g y) := by
      have := hA (g y) hv0 _ hk1
      rw [map_sub, LinearMap.sub_apply] at this
      exact (sub_eq_zero.mp this).symm
    have l2 : ip (g x) (g (f (F b a (g y)))) = ip (g x) (F b a (g y)) := by
      have := hA' (g x) hu0 _ hk2
      rw [map_sub] at this
      exact (sub_eq_zero.mp this).symm
    rw [l1, l2]
    exact hadj a b hab _ (hU1U _ hu0) _ (hU1U _ hv0)

end GlobalTheory.HoweR
end

