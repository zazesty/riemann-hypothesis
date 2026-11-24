module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGL
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem entry_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) (i j : Fin n) : (k : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨k0, rfl⟩ := hk
  exact (k0.val i j).2

theorem mulVec_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) {v : Fin n → L} (hv : ∀ i, v i ∈ O) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) L) *ᵥ v) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)

theorem pullLat_mul_of_mem_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  intro E _ _ _ w K B n ψ g k hk
  have hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hk
  ext y
  show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
    (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)
  simp only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro h c i
    have e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) =
        (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y))) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_of_mem_GLint hk (fun j => h c j) i
  · intro h c i
    exact mulVec_mem_of_mem_GLint hk' (fun j => h c j) i

end GlobalTheory.KapOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndex
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLattice

open GlobalTheory.SplitScalar GlobalTheory.CompletedLatticeFinite

theorem relIndex_comap_comap {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (A B : AddSubgroup H)
    (h : ∀ b ∈ B, ∃ x, f x ∈ B ∧ b - f x ∈ A) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_right B A,
    ← AddSubgroup.relIndex_sup_right ((B.comap f).map f) A]
  congr 1
  refine le_antisymm (sup_le_sup_right (AddSubgroup.map_comap_le _ _) _) (sup_le (fun b hb => ?_) le_sup_right)
  obtain ⟨x, hx, hb⟩ := h b hb
  rw [← add_sub_cancel (f x) b]
  exact AddSubgroup.add_mem_sup ⟨x, hx, rfl⟩ hb

theorem fg_of_denom {E : Type} [Field E] [NumberField E] {m n : ℕ} (L : AddSubgroup (Matrix (Fin m) (Fin n) E))
    (d : E) (hd : d ≠ 0) (h : ∀ x ∈ L, ∀ i j, IsIntegral ℤ (d * x i j)) : L.FG := by
  let f : Matrix (Fin m) (Fin n) (𝓞 E) →+ Matrix (Fin m) (Fin n) E :=
    AddMonoidHom.mk' (fun x => Matrix.of fun i j => d⁻¹ * (x i j : E)) fun x y => by
      ext i j
      simp [mul_add]
  have e : L = (L.comap f).map f := by
    refine (AddSubgroup.map_comap_eq_self fun x hx => ⟨Matrix.of fun i j => ⟨d * x i j, h x hx i j⟩, ?_⟩).symm
    ext i j
    show d⁻¹ * (d * x i j) = x i j
    rw [inv_mul_cancel_left₀ hd]
  have h1 : (AddSubgroup.toIntSubmodule (L.comap f)).FG := IsNoetherian.noetherian _
  have h2 := h1.map f.toIntLinearMap
  rw [e]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_denom_latQ (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ d : D.host.E, d ≠ 0 ∧ ∀ x ∈ latQ S T ΛS ΛT, ∀ i j, IsIntegral ℤ (d * x i j) := by
  classical
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  exact ⟨d, hd, fun x hx i j =>
    (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (x i j)).1 (hlat _ hx i j))⟩

theorem exists_rat_add_nsmul (Λ : AddSubgroup (WO S T)) (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (happ : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    {z : WO S T} (hz : z.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ y, ∃ u ∈ Λ, z = finRat S T y + N • u := by
  obtain ⟨γ, hγ, hNγ⟩ := GlobalTheory.RatSelfDual.exists_div hz hN
  obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
  have hγe : γ = finRat S T y₀ + u := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
      have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
      have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
      rw [Matrix.add_apply, RingHom.map_add (f := _), e0, e1, e2, add_zero]
    · have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
      have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at e0
      rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e0]
  exact ⟨N • y₀, u, hu, by rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : XF S T) :
    rhoF S T (g, h) (rhoF S T (g⁻¹, h⁻¹) x) = x ∧ rhoF S T (g⁻¹, h⁻¹) (rhoF S T (g, h) x) = x := by
  constructor
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

theorem mem_map_rhoF (A : Submodule (𝓞 D.host.E) (XF S T)) (g : GA D S) (h : GA D T) (x : XF S T) :
    x ∈ A.map (rhoF S T (g, h)) ↔ rhoF S T (g⁻¹, h⁻¹) x ∈ A :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← e, (actO_inv_actO g h y).2], fun hx => ⟨_, hx, (actO_inv_actO g h x).1⟩⟩

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ XF S T :=
  AddMonoidHom.mk' (fun x => XF.mk (finRat S T x) (finRat_inf S T x)) fun x y => XF.ext ((finRat S T).map_add x y)

theorem rhoF_finX {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (ha : Formalism.L2.Theta.mt S g = a.map (incA D))
    (hb : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T x) = finX S T (b * x * a) := by
  apply XF.ext
  show actO S T g⁻¹ h⁻¹ (finRat S T x) = finRat S T (b * x * a)
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, ha, hb]
  congr 1
  exact ((Matrix.map_mul (f := incA D)).trans (congrArg (· * a.map (incA D)) (Matrix.map_mul (f := incA D)))).symm

theorem latQ_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  intro D ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hdual, happ, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have hden := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S ΛS hS)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice T ΛT hT)
  refine ⟨fun x => ?_, ?_, fun x => ?_, fun g h a b ha hb => ?_⟩
  · refine (GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ _ hψ (fun u hu => latO_fin hu) hdual happ hden x).trans ?_
    exact forall₂_congr fun y _ => (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T x y).symm
  · obtain ⟨d, hd, h⟩ := exists_denom_latQ (S := S) (T := T) hS.1.fg hT.1.fg
    exact fg_of_denom _ d hd h
  · obtain ⟨N, hN, h⟩ := hden x
    exact ⟨N, hN, by rwa [mem_latQ, map_nsmul]⟩
  · obtain ⟨N, hN, hmov⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
      (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g⁻¹ h⁻¹
    rw [GlobalTheory.FinWeil.idx, ← relIndex_comap_comap (finX S T)]
    · congr 1
      refine AddSubgroup.ext fun x => (mem_map_rhoF _ g h (finX S T x)).trans ?_
      rw [rhoF_finX ha hb]
      rfl
    · intro z hz
      obtain ⟨y, u, hu, e⟩ := exists_rat_add_nsmul _ (fun u hu => latO_fin hu) happ z.fin hN
      have e' : z = finX S T y + N • XF.mk u (latO_fin hu) := XF.ext e
      have h1 : N • XF.mk u (latO_fin hu) ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
        rw [mem_map_rhoF, map_nsmul]
        exact hmov u hu
      refine ⟨y, ?_, ?_⟩
      · rw [← sub_eq_iff_eq_add.2 e']
        exact sub_mem hz h1
      · rw [sub_eq_iff_eq_add'.2 e']
        exact nsmul_mem (show XF.mk u (latO_fin hu) ∈ latF S T ΛS ΛT from hu) N

end GlobalTheory.RatLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizer
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbWeights

theorem mem_stabLat_iff_mulLat_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (t : Aˣ) (L : Submodule O A) :
    t ∈ GlobalTheory.UnitLemma.stabLat O L ↔ GlobalTheory.UnitLemma.mulLat O (t : A) L = L := by
  constructor
  · intro ht
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (ht y).1 hy
    · intro y hy
      have h1 : ((t⁻¹ : Aˣ) : A) * y ∈ L := by
        rw [ht]
        rw [← mul_assoc, Units.mul_inv, one_mul]
        exact hy
      refine ⟨((t⁻¹ : Aˣ) : A) * y, h1, ?_⟩
      change (t : A) * (((t⁻¹ : Aˣ) : A) * y) = y
      rw [← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      change (t : A) * z = (t : A) * y at hzy
      have : z = y := by
        have := congrArg (fun w => ((t⁻¹ : Aˣ) : A) * w) hzy
        simpa [← mul_assoc] using this
      rw [← this]
      exact hz

theorem relIndex_stab_eq_relIndex_stabLat : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  intro G _ _ Kg δ O A _ _ _ Tb M τ hK hM hτ hsurj hmul hinj hcpt g
  set T := twCent (MonoidHom.id G) δ with hT
  have hone : τ 1 = 1 := by
    have := hmul 1 T.one_mem 1 T.one_mem
    rw [one_mul] at this
    exact (mul_eq_left.mp this.symm)
  let φ : T →* Aˣ :=
    { toFun := fun h => τ h
      map_one' := hone
      map_mul' := fun a b => hmul a a.2 b b.2 }
  have hφ : ∀ x : T, φ x = τ x := fun _ => rfl
  have hinjφ : Function.Injective φ := fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab)
  have hCT : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  rw [← Subgroup.relIndex_subgroupOf (H := T ⊓ Kg.map (MulAut.conj g).toMonoidHom) hCT,
    ← Subgroup.relIndex_map_map_of_injective _ _ hinjφ]
  congr 1
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, ⟨_, k, hk, hkx⟩, rfl⟩
      refine ⟨?_, (hτ x x.2).1⟩
      rw [hφ, mem_stabLat_iff_mulLat_eq, ← (hτ x x.2).2 g]
      have : (x : G) * g = g * k := by
        rw [← hkx]
        simp [mul_assoc]
      rw [this, hK g k hk]
    · rintro ⟨hs, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      refine ⟨⟨h, hh⟩, ⟨hh, g⁻¹ * (h * g), ?_, ?_⟩, rfl⟩
      · apply hM
        rw [mem_stabLat_iff_mulLat_eq, ← (hτ h hh).2 g] at hs
        exact hs.symm
      · simp [mul_assoc]
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hcpt x x.2).1 hx, (hτ x x.2).1⟩
    · rintro ⟨hi, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      exact ⟨⟨h, hh⟩, (hcpt h hh).2 hi, rfl⟩

end GlobalTheory.OrbWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroup
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory

theorem relIndex_eq_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  intro G H _ _ T S τ A₁ A₂ B₁ B₂ h₁ h₂ e₁ e₂
  have key : ∀ (A : Subgroup G) (B : Subgroup H), (∀ t : T, (t : G) ∈ A ↔ ((τ t : S) : H) ∈ B) →
      (A.subgroupOf T).map τ.toMonoidHom = (B ⊓ S).subgroupOf S := by
    intro A B e
    ext s
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, e]
    simp
  rw [← Subgroup.relIndex_subgroupOf h₂, ← Subgroup.relIndex_subgroupOf (inf_le_right : B₂ ⊓ S ≤ S),
    ← key A₁ B₁ e₁, ← key A₂ B₂ e₂,
    Subgroup.relIndex_map_map_of_injective _ _ τ.injective]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncOpenImmersion
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_pull_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  intro R _ X Y f e _ d s L σ h
  refine ⟨fun i => LB.isLB_pull (h.isLB i) e, fun y => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (e y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (e ⁻¹ᵁ C.U : Y.Opens)) hC
      (e ⁻¹ᵁ C.U).isOpen
  have hle : W ≤ e ⁻¹ᵁ C.U := hWV
  have hap : ∀ a : Γ(X, C.U), (e.appLE C.U W hle).hom a = resG Y hle ((e.app C.U).hom a) :=
    fun _ => rfl
  refine ⟨{ U := W
            affine := hW
            t := fun a => (e.appLE C.U W hle).hom (C.t a)
            etale := _root_.GlobalTheory.LogPair.isEtCoord_openImmersion R X Y f e C.U W hle d C.t C.affine hW C.etale
            c := fun i _ => C.c i
            le := fun i => (hle.trans (e.preimage_mono (C.le i))).trans
              (Cartier.pull_U (L i) e (fun _ => C.c i)).ge
            e := C.e
            inj := C.inj
            u := fun i => Units.map (e.appLE C.U W hle).hom.toMonoidHom (C.u i)
            eq := fun i => ?_ }, hyW⟩
  have h1 := congrArg (e.appLE C.U W hle).hom (C.eq i)
  rw [map_mul, hap, Cartier.app_resG, Cartier.resG_resG] at h1
  refine (Cartier.resG_resG _ _ _).trans (h1.trans ?_)
  congr 1
  cases C.e i with
  | none => exact map_one _
  | some a => rfl

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncSameDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    resG X h2 (resG X h1 z) = resG X (h2.trans h1) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_elim {X : Scheme.{0}} {U W : X.Opens} (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (o : Option (Fin d)) : resG X h (o.elim 1 t) = o.elim 1 (fun a => resG X h (t a)) := by
  cases o <;> simp

theorem relSnc_of_sameDiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ)
    (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec),
    RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  intro R _ X f d s L σ L' σ' hR hL' hS
  refine ⟨hL', fun x => ?_⟩
  obtain ⟨C, hxC⟩ := hR.chart x
  choose U a b ha hb v hxU hv using fun i => hS i x
  let V : X.Opens := C.U ⊓ ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hxV : x ∈ V := ⟨hxC, Set.mem_iInter.2 hxU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWC : W ≤ C.U := fun y hy => (hWV hy).1
  have hWU : ∀ i, W ≤ U i := fun i y hy => Set.mem_iInter.1 (hWV hy).2 i
  have hWca : ∀ i, W ≤ (L i).U (C.c i) ⊓ (L i).U (a i) := fun i => le_inf (hWC.trans (C.le i)) ((hWU i).trans (ha i))
  let G : ∀ i, Γ(X, W)ˣ := fun i => Units.map (resG X (hWca i)).toMonoidHom ((L i).g (C.c i) (a i)) *
    Units.map (resG X (hWU i)).toMonoidHom (v i)
  refine ⟨{
    U := W
    affine := hW
    t := fun j => resG X hWC (C.t j)
    etale := _root_.GlobalTheory.LogPair.isEtCoord_res R X f C.U W hWC d C.t C.affine hW C.etale
    c := b
    le := fun i => (hWU i).trans (hb i)
    e := C.e
    inj := C.inj
    u := fun i => Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹
    eq := fun i => ?_ }, hxW⟩

  have h1 := congrArg (resG X hWC) (C.eq i)
  rw [resG_resG', map_mul, resG_elim] at h1

  have h2 := congrArg (resG X (hWca i)) ((σ i).compat (C.c i) (a i))
  simp only [resG_resG', map_mul] at h2

  have h3 := congrArg (resG X (hWU i)) (hv i)
  simp only [resG_resG', map_mul] at h3
  have hG : (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * (G i : Γ(X, W)) = 1 := Units.inv_mul _
  have hG' : (G i : Γ(X, W)) = resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) *
      resG X (hWU i) (v i : Γ(X, U i)) := by
    simp only [G, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  show _ = ((Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * _
  rw [Units.val_mul, Units.coe_map]
  rw [hG'] at hG
  linear_combination (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h1 - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h2
    - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) * h3
    - resG X (le_trans (hWU i) (hb i)) ((σ' i).f (b i)) * hG

end GlobalTheory.LogPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlacesStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiLocal_kirillov_archimedean_kernel_complexPlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  first | exact @GlobalTheory.JSW.KirArchTransfer.kirillov_arch | exact GlobalTheory.JSW.KirArchTransfer.kirillov_arch | (intros; apply GlobalTheory.JSW.KirArchTransfer.kirillov_arch <;> assumption)
end

