module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramified
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinW

theorem one_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem charW_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι β₀ hβ
  have hloc := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  obtain ⟨φ₀, hφ₀, hιφ₀⟩ := hι.bij.surjOn (GlobalTheory.KSplit.indicator_intM_mem_SB (k := Fv F v) (R := Fin a) (D := Fin (a + a')))
  have h0 : ι φ₀ 0 ≠ 0 := by
    rw [hιφ₀]
    have : (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∈ GlobalTheory.KSplit.intM (Fv F v) (Fin a) (Fin (a + a')) :=
      fun i j => by simp
    simp [Set.indicator_of_mem this]
  have omA_eq : ∀ (h' : GL (Fin (a + a')) (Fv F v)) (Φ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) Y,
      GlobalTheory.SplitFlip.omA 1 β₀ 1 h' Φ Y = ((β₀ (GlobalTheory.SplitFlip.gdet h') : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(a : ℂ) / 2)) * Φ (Y * (GlobalTheory.SplitFlip.invT h').1) := by
    intro h' Φ Y
    simp [GlobalTheory.SplitFlip.omA]
  have gdet_eq : ∀ (h : UA σ G.W.J) (h' : GL (Fin (a + a')) (Fv F v)), (mat h).map (piW t) = h'.1 →
      ((GlobalTheory.SplitFlip.gdet h' : (Fv F v)ˣ) : Fv F v) = ((mat h).map (piW t)).det := by
    intro h h' e
    rw [e]; rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := hloc.2.2 φ₀ hφ₀
    have hUW : {h : UA σ G.W.J | ((1 : UA σ G.V.J), h) ∈ U} ∈ 𝓝 (1 : UA σ G.W.J) := by
      have hc : Continuous (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h)) := continuous_const.prodMk continuous_id
      exact hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hV, hVx⟩ := _root_.GlobalTheory.SkewLeviNear.near_one_det F E σ B a a' G X om om' hTr v hv t _ hUW
    unfold GlobalTheory.SmGL.IsSmoothChar
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hV, _root_.GlobalTheory.units_valuation_eq_one_mem_nhds_one (k := Fv F v)] with x hx hxv
    obtain ⟨h, hh, hhU, hdet⟩ := hVx x hx
    obtain ⟨h', hh', hrel⟩ := hβ h hh
    have hA := hUφ (1, h) hhU (one_mem_UAt' σ G.V _) hh
    have e := congrFun (hrel φ₀ hφ₀ φ₀ hφ₀ hA) 0
    rw [omA_eq] at e
    have hg : GlobalTheory.SplitFlip.gdet h' = x := Units.ext ((gdet_eq h h' hh').trans hdet)
    rw [hg, Matrix.zero_mul, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hxv, mul_one] at e
    have e2 : (β₀ x : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
      exact this
    show β₀ x = 1
    exact Units.ext e2
  · intro x
    have ha : 0 < a + a' := by have := hTr.geo.lt; omega
    let i0 : Fin (a + a') := ⟨0, ha⟩
    let D : (Fv F v)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v) := fun y =>
      Matrix.diagonal (Function.update (1 : Fin (a + a') → Fv F v) i0 (y : Fv F v))
    have hD : ∀ y z : (Fv F v)ˣ, D y * D z = D (y * z) := by
      intro y z
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    have hD1 : D 1 = 1 := by
      simp only [D]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    let h' : GL (Fin (a + a')) (Fv F v) :=
      ⟨D x, D x⁻¹, by rw [hD, mul_inv_cancel, hD1], by rw [hD, inv_mul_cancel, hD1]⟩
    have hg : GlobalTheory.SplitFlip.gdet h' = x := by
      apply Units.ext
      change (D x).det = (x : Fv F v)
      simp only [D, Matrix.det_diagonal]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    obtain ⟨h, hh, hht⟩ := _root_.GlobalTheory.SkewLevi.surj_at_place hP F E σ B a a' G X om om' hTr v hv t h'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 1 (one_mem_UAt' σ G.V _) h hh φ₀ hφ₀
    obtain ⟨h'', hh'', hrel⟩ := hβ h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    have e := hrel φ₀ hφ₀ φ₁ hφ₁ hA
    obtain ⟨ν, hν⟩ := _root_.GlobalTheory.haar_exists_matrix_local_field (k := Fv F v) (a := a) (d := a + a')
    have hu := GlobalTheory.T.triple_local_unitary_action_preserves hP F E σ B a a' G X om om' hTr v h hh φ₀ hφ₀ φ₁ hφ₁ hA
    have hl := _root_.GlobalTheory.LinearModelL2.linIso_lintegral_eq hP F E σ B a a' G X om om' hTr v hv t ι hι φ₀ hφ₀ φ₁ hφ₁ hu ν hν
    rw [e] at hl
    simp_rw [omA_eq, hg] at hl
    set c : ℂ := (β₀ x : ℂ) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) with hcdef
    have hc : ∀ Y : Matrix (Fin a) (Fin (a + a')) (Fv F v), ‖c * ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 =
        ‖c‖ₑ ^ 2 * ‖ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 := by
      intro Y; rw [enorm_mul, mul_pow]
    simp_rw [hc] at hl
    rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), _root_.GlobalTheory.SplitFlip.lintegral_mul_invT_sq (ι φ₀) h' ν hν, hg] at hl
    obtain ⟨hn0, hntop⟩ := _root_.GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top (ι φ₀) (hι.bij.mapsTo hφ₀) (fun hz => h0 (by simp [hz])) ν hν
    rw [← mul_assoc] at hl
    have h1 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = 1 :=
      (ENNReal.mul_left_inj hn0 hntop).mp (hl.trans (one_mul _).symm)
    clear_value c
    have h2 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by
      have : c * c * GlobalTheory.SplitFlip.apow x (a : ℂ) = (β₀ x : ℂ) * (β₀ x : ℂ) := by
        rw [hcdef]
        have e3 : GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (a : ℂ) = 1 := by
          rw [← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]
          have : -(a : ℂ) / 2 + -(a : ℂ) / 2 + a = 0 := by ring
          rw [this, GlobalTheory.SplitFlip.apow_zero]
        linear_combination ((β₀ x : ℂ) * (β₀ x : ℂ)) * e3
      calc ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖c * c * GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ := by
            rw [enorm_mul, enorm_mul]; ring
        _ = ‖(β₀ x : ℂ) * (β₀ x : ℂ)‖ₑ := by rw [this]
        _ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by rw [enorm_mul]; ring
    rw [h2] at h1
    have h3 : ‖(β₀ x : ℂ)‖₊ = 1 := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one] at h1
      exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h1
    exact congrArg NNReal.toReal h3

end GlobalTheory.WeilLinW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogShortThetaSeriesDenominatorBoundLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovIntNum

section Size

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sum_abs_laOf (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H) :
    ∑ k, |((laOf Dw a n τ k : ℤ) : ℝ)| =
      ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) +
        ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin Dw.p, |((laOf Dw a n τ (Fin.castAdd Dw.q i) : ℤ) : ℝ)| = (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_pos hi, Fin.val_castAdd]
    simp only [Int.cast_add, Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  have h2 : ∀ i : Fin Dw.q, |((laOf Dw a n τ (Fin.natAdd Dw.p i) : ℤ) : ℝ)| =
      (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ¬ ((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    have hidx : Dw.q - 1 - (((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) - Dw.p) = (Fin.rev i : ℕ) := by
      simp only [Fin.val_natAdd, Fin.val_rev]; omega
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_neg hi, hidx]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast]
    have h3 : (0 : ℝ) ≤ (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : (∑ i : Fin Dw.q, (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)) = ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ) :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hr]
  push_cast
  ring

theorem DF_eq_sum (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) :
    (DF Dw a : ℝ) = ∑ τ : Psi H, ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) := by
  classical
  let P : (E →+* ℂ) → Prop := fun τ => τ (H.rt : E) = H.rt0
  have h := Fintype.sum_subtype_add_sum_subtype P (fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ))
  beta_reduce at h
  have e1 : (∑ τ : {τ // P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ) := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Datum.mult, if_pos τ.2]
  let e : {τ : E →+* ℂ // ¬ P τ} ≃ {τ // P τ} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun σ => ⟨conjEmb σ.1, GlobalTheory.AllWt.conj_not_mem (H := H) σ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun σ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have e2 : (∑ τ : {τ // ¬ P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    show _ = ∑ i : Fin Dw.q, (a (conjEmb (conjEmb τ.1), i) : ℝ)
    rw [GlobalTheory.AllWt.conjEmb_conjEmb, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_neg τ.2]
  unfold DF
  push_cast
  calc (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = _ := h.symm
    _ = (∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) +
          ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
        convert congrArg₂ (· + ·) e1 e2 using 2 <;> first | rfl | exact Finset.sum_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl | congr 1
    _ = _ := by
        rw [← Finset.sum_add_distrib]

theorem sizeK_eq (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    sizeK Dw a n = (DF Dw a : ℝ) + (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  unfold sizeK
  simp only [sum_abs_laOf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [DF_eq_sum, Finset.sum_add_distrib]
  ring

end Size

end GlobalTheory.CovIntNum

namespace GlobalTheory.CovIntNum

theorem intZ_log_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n →
    0 < intZ D (T.Q.Dw j) Y.d.l₂ n a ∧
    Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n := by
  refine ⟨67, by norm_num, ?_⟩
  intro D T j Y e o Lb a n h
  obtain ⟨-, -, -, -, -, -, hLb, hM, hsz, -, -, -, hn, -, -, -⟩ := h
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := D.host.hyp
  have hM3 : 3 ≤ Y.d.l₂.M := Y.d.l₂.three_le
  have hZ : (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      (Y.d.l₂.M : ℝ) ^ (Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a) *
        ((NumberField.discr D.host.E).natAbs : ℝ) ^ DF (T.Q.Dw j) a := by
    rw [intZ_eq]
    push_cast [-Nat.cast_natAbs]
    ring
  have hD1 : (1 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have hlD : Real.log ((NumberField.discr D.host.E).natAbs : ℝ) ≤ D.R.f * (7 * Lb) := by
    have h1 := log_discr_natAbs_le D.host.E
    have h2 : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
    have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    rw [h2] at h1
    nlinarith
  have hMpos : (0 : ℝ) < Y.d.l₂.M := by exact_mod_cast (by omega : 0 < Y.d.l₂.M)
  have hq0 : (0 : ℝ) < D.host.q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast hdp.pos
  have hZpos : (0 : ℝ) < (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) := by rw [hZ]; positivity
  refine ⟨by exact_mod_cast hZpos, ?_⟩
  have hlogZ : Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      ((Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a : ℕ) : ℝ) *
          Real.log Y.d.l₂.M +
        (DF (T.Q.Dw j) a : ℝ) * Real.log ((NumberField.discr D.host.E).natAbs : ℝ) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [hlogZ]

  have hSe := sizeK_eq (T.Q.Dw j) a n
  have hcard : Fintype.card (Psi T.Q.H) = Module.finrank ℚ D.host.E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.LamF.card_psiSet T.Q.H
  rw [hcard] at hSe
  have hlD0 := Real.log_nonneg hD1
  generalize Real.log ((NumberField.discr D.host.E).natAbs : ℝ) = lD at hlD hlD0 ⊢
  obtain ⟨t, rfl⟩ := hn
  have ht : (t + t) / 2 = t := by omega
  rw [ht] at hSe
  generalize Module.finrank ℚ D.host.E / 2 = m at hSe ⊢
  generalize sizeK (T.Q.Dw j) a (t + t) = S at hSe ⊢
  generalize DF (T.Q.Dw j) a = dF at hSe ⊢
  push_cast at hSe ⊢

  have hf : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hlM0 : 0 ≤ Real.log Y.d.l₂.M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y.d.l₂.M))
  have hdF0 : (0 : ℝ) ≤ dF := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * t := by positivity
  have hS0 : 0 ≤ S := by rw [hSe]; positivity
  have hX : (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF ≤ 2 * S := by rw [hSe]; linarith
  have hdFS : (dF : ℝ) ≤ S := by rw [hSe]; linarith
  have h1 : ((m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF) * Real.log Y.d.l₂.M ≤
      (2 * S) * (30 * Lb) := mul_le_mul hX hM hlM0 (by linarith)
  have h2 : (dF : ℝ) * lD ≤ (D.R.f * S) * (7 * Lb) :=
    (mul_le_mul hdFS hlD hlD0 hS0).trans (le_of_eq (by ring))
  have hLS : 0 ≤ Lb * S := mul_nonneg (by linarith) hS0
  have hA : Lb * S ≤ D.R.f * (Lb * S) := le_mul_of_one_le_left hLS hf1
  have h3 : (2 * S) * (30 * Lb) + (D.R.f * S) * (7 * Lb) ≤ 67 * ((D.R.f : ℝ) * Lb) * S := by linarith
  have hx1 : (1 : ℝ) ≤ D.R.f * D.R.r * Lb :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hLb
  have h5 : (D.R.f : ℝ) * Lb ≤ D.R.f * D.R.r * Lb :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr1) (by linarith)
  have h4 : (D.R.f : ℝ) * Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := h5.trans (le_self_pow₀ hx1 (by norm_num))
  have h6 : 67 * ((D.R.f : ℝ) * Lb) * S ≤ 67 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * S :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  linarith

end GlobalTheory.CovIntNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.DetImMeas

theorem measurableSet_det_im_pos : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  intro κ _ p q ρ₀
  haveI : BorelSpace (UpqT (p ρ₀) (q ρ₀)) := (GlobalTheory.UpqTopology.upq_lcsc (p ρ₀) (q ρ₀)).2.2.2.2.1
  have hc : Continuous fun g : UpqT (p ρ₀) (q ρ₀) => (UpqT.mat g).det.im :=
    Complex.continuous_im.comp ((continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat)
  have hm : Measurable fun b : (∀ ρ, UpqT (p ρ) (q ρ)) => (UpqT.mat (b ρ₀)).det.im :=
    hc.measurable.comp (measurable_pi_apply ρ₀)
  exact measurableSet_lt measurable_const hm

end GlobalTheory.CovTop.VolUp.DetImMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

theorem rp_eq_one (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (k : GA D V) (hk : k ∈ GfC V) : rp k = 1 := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  have h1 : infMat D.sp.cm.sig V.gram (θ ρ) k = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hk)
    show (Units.val (infHom V k)).map (θ ρ) = 1
    rw [h2]
    simp
  rw [hrp, h1, Pi.one_apply, GlobalTheory.Mem.VolExists.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem rp_realElt (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (b : ∀ ρ, Upq V ρ) :
    rp (realElt θ V fun ρ => realMat V A ρ (b ρ)) = b := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D ρ))).2.2 (A ρ) (hA ρ)
  have e : UpqT.mat (b ρ) * A ρ = A ρ * (C * (UpqT.mat (b ρ) * A ρ)) := by
    rw [← Matrix.mul_assoc (A ρ), h1, Matrix.one_mul]
  rw [hrp, GlobalTheory.RealBoxMeasure.infMat_realElt θ hθ V _ (fun τ => GlobalTheory.RealBoxMeasure.realMat_mem V hV A hA τ _) ρ,
    GlobalTheory.RealBoxMeasure.realMat_of V A hA ρ _ _ e, ← e]

theorem exists_fin (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (h : GA D V) :
    ∃ k : GA D V, rp k = 1 ∧ finE V k = finE V h := by
  refine ⟨(realElt θ V fun ρ => realMat V A ρ (rp h ρ))⁻¹ * h, ?_, ?_⟩
  · rw [map_mul, map_inv, rp_realElt V θ A rp hV hθ hA hrp, inv_mul_cancel]
  · rw [map_mul, map_inv, GlobalTheory.RealBoxMeasure.finE_realElt, inv_one, one_mul]

theorem meas_level (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ))
    (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ)) (hc : Continuous rp)
    (hrp : IsRealPart V θ A rp) (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  have hBm : MeasurableSet (rp ⁻¹' B) := hc.measurable hB
  have H := GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ V hV K μ hμ A hA m hm
    ((rp ⁻¹' B).indicator 1) (measurable_one.indicator hBm) (fun g k hk => by
      have : rp (g * k) = rp g := by rw [map_mul, rp_eq_one V θ A rp hV hA hrp k hk.1, mul_one]
      exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, this, Set.mem_preimage]) rfl) hK.measurableSet
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at H
  rw [← lintegral_indicator_one hB, show {h | finE V h ∈ K ∧ rp h ∈ B} = rp ⁻¹' B ∩ {h : GA D V | finE V h ∈ K} from
    Set.ext fun h => and_comm, H]
  refine lintegral_congr fun b => ?_
  exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, rp_realElt V θ A rp hV hθ hA hrp]) rfl

theorem meas_translate_le : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  intro D V θ A m rp K K₀ μ hV hθ hA hm hc hrp _ hi hK hμ g _ B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let S : (K₀ ⧸ K.subgroupOf K₀) → Set (GA D V) := fun q =>
    {h | (∃ hh : finE V (g⁻¹ * h) ∈ K₀, (QuotientGroup.mk ⟨_, hh⟩ : K₀ ⧸ K.subgroupOf K₀) = q) ∧ rp h ∈ B}
  have hS : ∀ q, μ (S q) ≤ Measure.pi m B := by
    intro q
    rcases (S q).eq_empty_or_nonempty with h0 | ⟨h₀, ⟨hh₀, hq₀⟩, -⟩
    · rw [h0, measure_empty]; exact zero_le
    obtain ⟨k, hk1, hk2⟩ := exists_fin V θ A rp hV hθ hA hrp h₀
    rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB, ← measure_preimage_mul μ k⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
    refine measure_mono ?_
    rintro h ⟨⟨hh, hq⟩, hb⟩
    have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hq₀.trans hq.symm))
    show finE V (k⁻¹ * h) ∈ K ∧ rp (k⁻¹ * h) ∈ B
    refine ⟨?_, ?_⟩
    · have h2 : finE V (k⁻¹ * h) = (finE V (g⁻¹ * h₀))⁻¹ * finE V (g⁻¹ * h) := by
        simp only [map_mul, map_inv, hk2]; group
      rw [h2]; exact h1
    · rwa [map_mul, map_inv, hk1, inv_one, one_mul]
  calc μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ μ (⋃ q, S q) :=
        measure_mono fun h hh => Set.mem_iUnion.2 ⟨_, ⟨hh.1, rfl⟩, hh.2⟩
    _ ≤ ∑ q, μ (S q) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _q : K₀ ⧸ K.subgroupOf K₀, Measure.pi m B := Finset.sum_le_sum fun q _ => hS q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end GlobalTheory.CovTop.VolBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheaf
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem mem_basicOpen_of_sub_one_mem_baseIdeal (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0})
    (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z)
    (hz : z ∈ V) (hI : I ≤ (p z).asIdeal) (hr : r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩) :
    z ∈ Z.basicOpen r := by
  have hs : z ∈ (baseIdeal p I).support := (mem_support_baseIdeal p I z).2 hI
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hz] at hs
  have h1 : z ∉ Z.basicOpen (r - 1) := by
    rw [Scheme.mem_zeroLocus_iff] at hs
    exact hs _ hr
  rw [Scheme.mem_basicOpen _ _ _ hz] at h1 ⊢
  have hsum : Z.presheaf.germ V z hz r + (-(Z.presheaf.germ V z hz (r - 1))) = 1 := by
    simp [map_sub]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact h
  · exact absurd (by simpa using h.neg) h1

end GlobalTheory.FormalAlg
end

