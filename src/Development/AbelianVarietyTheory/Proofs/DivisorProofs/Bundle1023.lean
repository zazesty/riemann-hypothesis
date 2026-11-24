module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FactorDepth

section Series
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exp_eq_of_log_hom {d : ℕ} (G G' : LogFGL v d) (Φ : Fin d → MvPowerSeries (Fin d) C)
    (h0 : ∀ e, constantCoeff (Φ e) = 0) (M : Matrix (Fin d) (Fin d) C)
    (hl : ∀ e, subst Φ (G.lg e) = ∑ f, M e f • G'.lg f) {τ : Type} (w w' : Fin d → MvPowerSeries τ C)
    (hw' : ∀ e, constantCoeff (w' e) = 0) (hw : ∀ e, w e = ∑ f, M e f • w' f) (e : Fin d) :
    subst w (expOf G e) = subst (fun f => subst w' (expOf G' f)) (Φ e) := by
  have s1 : HasSubst w' := hasSubst_of_constantCoeff_zero hw'
  have c2 : ∀ f, constantCoeff (subst w' (expOf G' f) : MvPowerSeries τ C) = 0 := fun f =>
    constantCoeff_subst_eq_zero s1 hw' ((isExp_expOf G').1 f)
  have s2 := hasSubst_of_constantCoeff_zero c2
  have s3 : HasSubst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun e => constantCoeff_subst_eq_zero s2 c2 (h0 e)
  have key : (fun j => subst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) (G.lg j)) = w := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) s2, hl, hw, ← coe_substAlgHom s2, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, coe_substAlgHom,
      ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G').1) s1, (isExp_expOf G').2,
      subst_X s1]
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.lg_const) s3 (expOf G e)
  rw [subst_lg_expOf, subst_X s3, key] at this
  exact this.symm

theorem depth_le_of_log_hom {κ : Type} [Finite κ] {d : κ → ℕ} (G G' : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u u' : ∀ b, ι b → Fin (d b) → C) (Φ : ∀ b, Fin (d b) → MvPowerSeries (Fin (d b)) C)
    (h0 : ∀ b e, constantCoeff (Φ b e) = 0) (hI : ∀ b e, MvIsInt v (Φ b e))
    (M : ∀ b, Matrix (Fin (d b)) (Fin (d b)) C)
    (hl : ∀ b e, subst (Φ b) ((G b).lg e) = ∑ f, M b e f • (G' b).lg f)
    (hu : ∀ b a, u b a = (M b).mulVec (u' b a)) (P : MvPolynomial (Σ b, ι b) C) :
    depth G' u' P ≤ depth G u P := by
  classical
  have cX : ∀ b (e : Fin (d b)), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C) = 0 := fun b e => by simp
  let Ψ : (Σ b, Fin (d b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun x => subst (fun e : Fin (d x.1) => (X ⟨x.1, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C)) (Φ x.1 x.2)
  have cΨ : ∀ x, constantCoeff (Ψ x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cX x.1)) (cX x.1) (h0 x.1 x.2)
  have iΨ : ∀ x, MvIsInt v (Ψ x) := fun x =>
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hI x.1 x.2)
      (fun e α => by rw [coeff_X]; split_ifs <;> simp [IsIntV]) (cX x.1)
  have cw : ∀ b (e : Fin (d b)),
      constantCoeff (∑ a, u' b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have cE : ∀ x, constantCoeff (expAlong G' u' x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cw x.1)) (cw x.1) ((isExp_expOf _).1 _)
  have sE := hasSubst_of_constantCoeff_zero cE
  have key : expAlong G u = fun x => subst (expAlong G' u') (Ψ x) := by
    funext x
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cX x.1)) sE]
    simp only [subst_X sE]
    refine exp_eq_of_log_hom (G x.1) (G' x.1) (Φ x.1) (h0 x.1) (M x.1) (hl x.1) _ _ (cw x.1) (fun e => ?_) x.2
    simp only [hu, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le
    ⟨subst Ψ f.1, ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 iΨ cΨ⟩ (le_of_eq ?_)
  rw [key, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero cΨ) sE]

end Series

section Law
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.LawLog

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem logOf_spec (G : FGLaw C d) : GP (GlobalTheory.FormalLog.logOf G) ∧ dLin (GlobalTheory.FormalLog.logOf G) = 1 ∧
    comp1 (GlobalTheory.FormalLog.logOf G) (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 0) + comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 1) := by
  refine ⟨fun i => GlobalTheory.FormalLog.constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (GlobalTheory.FormalLog.logOf G i) = (1 : Matrix (Fin d) (Fin d) C) i j
    have h := congrArg constantCoeff (GlobalTheory.FormalLog.pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (GlobalTheory.FormalLog.cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · have e : addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G.F := add_pt G
    rw [e]
    funext i
    exact GlobalTheory.FormalLog.logOf_add G i

theorem logOf_comp_hom (G G' : FGLaw C d) (φ : Pt C 1 d) (hφ : GP φ)
    (hhom : comp1 φ G'.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1))) :
    comp1 (GlobalTheory.FormalLog.logOf G) φ = fun i => ∑ j : Fin d, dLin φ i j • GlobalTheory.FormalLog.logOf G' j := by
  obtain ⟨a0, a1, a2⟩ := logOf_spec G
  obtain ⟨b0, b1, b2⟩ := logOf_spec G'
  obtain ⟨ε, hi⟩ := ChartInv.exists_isInvPair C d _ b0 (by rw [b1, Matrix.det_one]; exact isUnit_one)
  have p0 : GP (pt C (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) d 1) := gp_pt 1
  have e : addOf G'.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G'.F := add_pt G'
  have e1 := additive_eq_lin _ G'.const _ ε (comp1 (GlobalTheory.FormalLog.logOf G) φ) b1 b2 hi
    (gp_comp1 _ _ a0 hφ) (by
    rw [e, gt_comp1_comp1 _ _ hφ _ G'.const, hhom,
      additive_at _ G.const _ a2 _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
      gt_comp1_comp1 _ _ hφ _ p0, gt_comp1_comp1 _ _ hφ _ p1])
  rw [dLin_comp _ _ hφ, a1, one_mul] at e1
  rw [e1]
  funext i
  rw [germComp_matrixLinearMap_apply _ _ b0]
  simp only [MvPowerSeries.smul_eq_C_mul]


open ReciprocityTheory.PGsh GlobalTheory.FGDepth in
theorem detDepth_le_of_transF {R : Type} [CommRing R] (v : AddValuation C (WithTop ℝ)) (j : R →+* C)
    (hj : ∀ r, IsIntV v (j r)) (F F' : Fin d → PS R 2 d) (hF : ∀ a, constantCoeff (F a) = 0)
    (φ φi : Pt R 1 d) (hi : IsInvPair φ φi)
    (ht : ∀ a, F' a = transF F φ φi a) (L L' : FGLaw C d) (hL : ∀ a, L.F a = MvPowerSeries.map j (F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (F' a))
    (hI : ∀ a, MvIsInt v (subst (twoVars C d) (L.F a))) (hI' : ∀ a, MvIsInt v (subst (twoVars C d) (L'.F a)))
    {i : ℕ} (u u' : Fin i → Fin d → R) (hu : ∀ a, u a = (dLin φ).mulVec (u' a)) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hφ : GP φ := hi.1
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have q := gp_addOf F hF _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1)
  have e0 : F' = comp1 φi (addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) := funext ht
  have hF' : GP F' := e0 ▸ gp_comp1 _ _ hi.2.1 q
  have e1 : comp1 φ F' = addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) := by
    rw [e0, gt_comp_inv hi _ q]
  have e2 := congrArg (GlobalTheory.FBMap.mapPt j) e1
  rw [GlobalTheory.FBMap.mapPt_comp1 j _ hF', GlobalTheory.FBMap.mapPt_addOf j _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
    GlobalTheory.FBMap.mapPt_comp1 j _ p0, GlobalTheory.FBMap.mapPt_comp1 j _ p1, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_pt,
    show GlobalTheory.FBMap.mapPt j F = L.F from (funext hL).symm, show GlobalTheory.FBMap.mapPt j F' = L'.F from (funext hL').symm] at e2
  have hψ : GP (GlobalTheory.FBMap.mapPt j φ) := fun a => by simp [GlobalTheory.FBMap.mapPt, hφ a]
  have e3 := logOf_comp_hom L L' _ hψ e2
  refine depth_le_of_log_hom _ _ _ _ (fun _ a => subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a))
    (fun _ a => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hψ a)) (fun _ a α => ?_)
    (fun _ => dLin (GlobalTheory.FBMap.mapPt j φ)) (fun _ a => ?_) (fun _ a => ?_) _
  · have e : subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a) = MvPowerSeries.map j (subst (oneVar R d) (φ a)) := by
      rw [MvPowerSeries.map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact hj _
  · show subst _ (subst (oneVar C d) (GlobalTheory.FormalLog.logOf L a)) =
      ∑ f, _ • subst (oneVar C d) (GlobalTheory.FormalLog.logOf L' f)
    rw [subst_oneVar _ cc_oneVar _ hψ]
    refine (congrArg (subst (oneVar C d)) (congrFun e3 a)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hs_oneVar, map_sum]
    simp only [map_smul]
  · funext e
    rw [hu, RingHom.map_mulVec]
    rfl

end Law

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp GlobalTheory.CharDepth ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog

theorem detDepth_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB V d (𝓞 E)) (B' : FB V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → V) (uv' : Fin d' → Fin d' → V)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    {i : ℕ} (u : Fin i → Fin d → V) (u' : Fin i → Fin d' → V)
    (w : Fin i → (Sp (DualNumber V) ⟶ t.G.left))
    (hw : ∀ ℓ, IsCombAtG t (𝟙 (Sp V)) (dirs x) (u ℓ) (w ℓ))
    (hw' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp V)) (dirs x') (u' ℓ) (w ℓ ≫ n.φ))
    {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (j : V →+* C) (hj : ∀ r, IsIntV v (j r))
    (L : FGLaw C d) (L' : FGLaw C d') (hL : ∀ a, L.F a = MvPowerSeries.map j (B.G.F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (B'.G.F a))
    (hI : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d) (L.F a)))
    (hI' : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d') (L'.F a))) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hd : d = d' := by
    obtain ⟨x'', -, h2, -⟩ := _root_.GlobalTheory.PushChart.pushChart E H V t t' n d x
    exact _root_.GlobalTheory.ChartCmp.univJ_dim_unique V t'.G d d' x'' x' (h2 hu) hu'
  subst hd
  obtain ⟨φ, φi, hJ, hdir⟩ := _root_.GlobalTheory.ChartCmp.jrel_of_sabMap E H hs V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  obtain ⟨ε, hε⟩ := hJ 0
  exact detDepth_le_of_transF v j hj _ _ B.G.const φ φi hε.inv hε.law L L' hL hL' hI hI' u u'
    (fun a => hdir _ _ _ (hw a) (hw' a)) k

theorem nuFacC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
      (C C' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC C' X f k ≤ nuFacC C X f k := by
  letI := H.starRing
  intro p _ T io y C C' X f k
  letI := io.toAlgebra
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io y.1 C.I C'.I
  obtain ⟨B, b1, b2, b3, b4, b5, b6, -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨B', b1', b2', b3', b4', b5', b6', -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  refine detDepth_le_of_charts (fun _ => rfl) T.V C.I.G C'.I.G n (GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io y.1 C'.I) _ _ B B'
    C.tgT C'.tgT (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_
    (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C') ?_ ?_
    (fun a => C.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩) (fun a => C'.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩)
    (fun a => (C.I.ub f.1 (Fin.castLE (rk_le f) a)).left) (fun a => C.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩) ?_
    (vX_vp X) (jX X) (isIntV_jX X) (lawX C X) (lawX C' X) ?_ ?_ (fgl C X).F_int (fgl C' X).F_int k
  · rw [b1, b2]; exact C.chartT
  · rw [b1', b2']; exact C'.chartT
  · rw [b1, b2, b3, b4, b5, b6]; exact C.frameT
  · rw [b1', b2', b3', b4', b5', b6']; exact C'.frameT
  · intro a
    rw [hn]
    exact C'.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩
  · intro a; rw [b1]; exact lawX_F C X a
  · intro a; rw [b1']; exact lawX_F C' X a

theorem nuFacC_chart_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ),
    nuFacC Ch X f k = nuFacC Ch' X f k :=
  fun _ _ _ _ _ _ _ Xo c p _ T io y Ch Ch' X f k =>
    le_antisymm (nuFacC_le Xo c p T io y Ch' Ch X f k) (nuFacC_le Xo c p T io y Ch Ch' X f k)

end GlobalTheory.FactorDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardMulLeOfQuotEmbed
section
open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_of_quot_embed : ∀ (G : Type) [AddCommGroup G] (Λ Λ' Λ₀ Λ₀' : AddSubgroup G) (B E : ℝ → Set G)
    (T : G →+ G), IsBallFam Λ B → IsBallFam Λ' E → (∀ u ∈ B 1, T u ∈ E 1) → (∀ u ∈ Λ, T u ∈ Λ₀' → u ∈ Λ₀) →
    (B 1).Finite → (B 1).encard * (E 1 ∩ Λ₀').encard ≤ (B 2 ∩ Λ₀).encard * (E 2).encard := by
  intro G _ Λ Λ' Λ₀ Λ₀' B E T hB hE hT hpull _
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  let q : G → G ⧸ Λ₀ := QuotientAddGroup.mk
  let R : Set (G ⧸ Λ₀) := q '' B 1
  let s : G ⧸ Λ₀ → G := Function.invFunOn q (B 1)
  have hs_mem : ∀ c ∈ R, s c ∈ B 1 := fun c hc => Function.invFunOn_mem hc
  have hs_eq : ∀ c ∈ R, q (s c) = c := fun c hc => Function.invFunOn_eq hc

  have h1 : (B 1).encard ≤ R.encard * (B 2 ∩ Λ₀ : Set G).encard := by
    rw [← Set.encard_prod]
    refine le_trans (Set.encard_le_encard (s := B 1)
      (t := (fun p : (G ⧸ Λ₀) × G => s p.1 + p.2) '' (R ×ˢ (B 2 ∩ (Λ₀ : Set G)))) ?_) (Set.encard_image_le _ _)
    intro x hx
    have hqx : q x ∈ R := ⟨x, hx, rfl⟩
    refine ⟨(q x, x - s (q x)), ⟨hqx, ?_, ?_⟩, by simp⟩
    · have := hB.sub_mem 1 1 x (s (q x)) hx (hs_mem _ hqx)
      rwa [h2] at this
    · have he : q (s (q x)) = q x := hs_eq _ hqx
      have := (QuotientAddGroup.eq).mp he
      show x - s (q x) ∈ Λ₀
      rwa [sub_eq_neg_add]

  have h3 : R.encard * (E 1 ∩ Λ₀' : Set G).encard ≤ (E 2).encard := by
    rw [← Set.encard_prod]
    refine Set.encard_le_encard_of_injOn (f := fun p : (G ⧸ Λ₀) × G => T (s p.1) - p.2) ?_ ?_
    · rintro ⟨c, v⟩ ⟨hc, hv, -⟩
      have := hE.sub_mem 1 1 _ _ (hT _ (hs_mem c hc)) hv
      rwa [h2] at this
    · rintro ⟨c, v⟩ ⟨hc, hv, hv'⟩ ⟨c', w⟩ ⟨hc', hw, hw'⟩ heq
      simp only at heq
      have hd : T (s c - s c') ∈ Λ₀' := by
        have : T (s c - s c') = v - w := by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp heq
        rw [this]; exact Λ₀'.sub_mem hv' hw'
      have hΛ : s c - s c' ∈ Λ := Λ.sub_mem (hB.subset 1 (hs_mem c hc)) (hB.subset 1 (hs_mem c' hc'))
      have h0 : s c - s c' ∈ Λ₀ := hpull _ hΛ hd
      have hqq : q (s c) = q (s c') := by
        apply (QuotientAddGroup.eq).mpr
        have := Λ₀.neg_mem h0
        rwa [neg_sub, sub_eq_neg_add] at this
      have hcc : c = c' := by rw [← hs_eq c hc, ← hs_eq c' hc', hqq]
      subst hcc
      have : v = w := by simpa using heq
      rw [this]
  calc (B 1).encard * (E 1 ∩ Λ₀' : Set G).encard
      ≤ (R.encard * (B 2 ∩ Λ₀ : Set G).encard) * (E 1 ∩ Λ₀' : Set G).encard := by gcongr
    _ = (B 2 ∩ Λ₀ : Set G).encard * (R.encard * (E 1 ∩ Λ₀' : Set G).encard) := by ring
    _ ≤ (B 2 ∩ Λ₀ : Set G).encard * (E 2).encard := by gcongr

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallLePowMulSmaller
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem finrank_span_finset_le_of_indep {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (T : Finset G) (r : ℕ)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ (T : Set G)) → n ≤ r) :
    Module.finrank ℤ (Submodule.span ℤ (T : Set G)) ≤ r := by
  classical
  haveI : HasUniqueDiv G := IsAddTorsionFree.hasUniqueDiv
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (Subtype.val : ↥(T : Set G) → G)
  have ha : ∀ i : (T : Set G), ∃ a : ℤ, a ≠ 0 ∧ a • (i : G) ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro i
    by_cases h : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, h, rfl⟩⟩
    · exact hmax i h
  choose a ha0 ha using ha
  set M : ℤ := ∏ i, a i with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hMmem : ∀ x ∈ Submodule.span ℤ (T : Set G), M • x ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have e : M = a ⟨y, hy⟩ * ∏ i ∈ Finset.univ.erase ⟨y, hy⟩, a i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      rw [e, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ha ⟨y, hy⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  let f : Submodule.span ℤ (T : Set G) →ₗ[ℤ] Submodule.span ℤ (Subtype.val '' s) :=
    { toFun := fun x => ⟨M • (x : G), hMmem x x.2⟩
      map_add' := by intro x y; ext; simp [smul_add]
      map_smul' := by
        intro c x; ext
        change M • (c • (x : G)) = c • (M • (x : G))
        exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (smul_right_injective G hM0 e)
  have hsfin : (Subtype.val '' s : Set G).Finite := (Set.toFinite s).image _
  haveI : Module.Finite ℤ (Submodule.span ℤ (Subtype.val '' s)) := Module.Finite.span_of_finite ℤ hsfin
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have hli : LinearIndepOn ℤ id (Subtype.val '' s) := hs.id_image
  haveI := hsfin.fintype
  rw [finrank_span_set_eq_card hli, Set.toFinset_card] at h1
  let eqv := Fintype.equivFin (Subtype.val '' s : Set G)
  have h2 := hr _ (fun j => (eqv.symm j : G)) (hli.comp _ eqv.symm.injective) (by
    intro j
    obtain ⟨i, _, hi⟩ := (eqv.symm j).2
    rw [← hi]; exact i.2)
  exact h1.trans h2

theorem encard_finset_le_pow_mul {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G)
    (B : ℝ → Set G) (hB : IsBallFam Λ B) (R : ℝ) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r)
    (T : Finset G) (hT : (T : Set G) ⊆ B R) :
    (T : Set G).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  classical
  haveI : HasUniqueDiv G := IsAddTorsionFree.hasUniqueDiv
  haveI : NeZero q := ⟨hq.ne'⟩
  set L := Submodule.span ℤ (T : Set G) with hLdef
  have hd : Module.finrank ℤ L ≤ r :=
    finrank_span_finset_le_of_indep T r (fun n e he hmem => hr n e he (fun j => hT (hmem j)))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set d := Module.finrank ℤ L with hddef
  let b := Module.finBasis ℤ L
  let v : G → (Fin d → ℤ) := fun x => if hx : x ∈ L then b.equivFun ⟨x, hx⟩ else 0
  let c : G → (Fin d → ZMod q) := fun x i => ((v x i : ℤ) : ZMod q)
  let z : G → G → G := fun x y => ((b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) : G)
  have hkey : ∀ x ∈ L, ∀ y ∈ L, c x = c y → q • z x y = x - y := by
    intro x hx y hy hc
    have hdvd : ∀ i, (q : ℤ) ∣ v x i - v y i := by
      intro i
      have e := congrFun hc i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.2 e
    have hvx : v x = b.equivFun ⟨x, hx⟩ := dif_pos hx
    have hvy : v y = b.equivFun ⟨y, hy⟩ := dif_pos hy
    have e : q • (b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) = ⟨x, hx⟩ - ⟨y, hy⟩ := by
      apply b.equivFun.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub, ← hvx, ← hvy]
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]
      exact Int.mul_ediv_cancel' (hdvd i)
    have e2 := congrArg Subtype.val e
    simpa [z] using e2
  have hLΛ : ∀ x ∈ L, x ∈ Λ := by
    intro x hx
    have : L ≤ Λ.toIntSubmodule := Submodule.span_le.2 (fun y hy => hB.subset R (hT hy))
    exact this hx
  let ρ : (Fin d → ZMod q) → G := Function.invFunOn c (T : Set G)
  have hρ : ∀ x ∈ (T : Set G), ρ (c x) ∈ (T : Set G) ∧ c (ρ (c x)) = c x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  let φ : G → (Fin d → ZMod q) × G := fun x => (c x, z x (ρ (c x)))
  have hsub : ∀ x ∈ (T : Set G), x ∈ L := fun x hx => Submodule.subset_span hx
  have hmaps : Set.MapsTo φ (T : Set G) (Set.univ ×ˢ B (2 * R / q)) := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h2 : x - ρ (c x) ∈ B (R + R) := hB.sub_mem R R _ _ (hT hx) (hT hyT)
    have hqR : ((q : ℝ)) * (2 * R / q) = R + R := by
      have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp; ring
    have hzΛ : z x (ρ (c x)) ∈ Λ := hLΛ _ (Subtype.property _)
    refine (hB.nsmul_iff q (2 * R / q) _ hq hzΛ).1 ?_
    rw [hqR, h1]; exact h2
  have hinj : Set.InjOn φ (T : Set G) := by
    intro x hx x' hx' h
    have hc : c x = c x' := congrArg Prod.fst h
    have hz : z x (ρ (c x)) = z x' (ρ (c x')) := congrArg Prod.snd h
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h1' := hkey x' (hsub x' hx') (ρ (c x)) (hsub _ hyT) (by rw [hyc, hc])
    rw [← hc] at hz
    rw [hz] at h1
    exact sub_left_injective (h1.symm.trans h1')
  have hle := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_prod, Set.encard_univ] at hle
  refine hle.trans ?_
  gcongr
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact_mod_cast Nat.pow_le_pow_right hq hd

theorem encard_ball_le_pow_mul : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G),
    IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q →
    (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) →
    (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  intro G _ _ Λ B hB R q r hq hr
  by_contra hlt
  push_neg at hlt
  have hC := hlt.ne_top
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hC
  have htfin : t.Finite := Set.encard_ne_top_iff.1 (by rw [htc, ← hm]; exact ENat.coe_ne_top (m + 1))
  have h := encard_finset_le_pow_mul Λ B hB R q r hq hr htfin.toFinset (by simpa using hts)
  rw [Set.Finite.coe_toFinset, htc, ← hm] at h
  norm_cast at h
  omega

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_inC_eventually) | (exact GlobalTheory.FinClsLoc.intC_inC_eventually) | (intros; apply GlobalTheory.FinClsLoc.intC_inC_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpaceStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  first | exact @GlobalTheory.JSW.MirSemi.whitSpace_exists | exact GlobalTheory.JSW.MirSemi.whitSpace_exists | (intros; apply GlobalTheory.JSW.MirSemi.whitSpace_exists <;> assumption)
end

