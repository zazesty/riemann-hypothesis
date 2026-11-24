module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Formalism.LocalToGlobal.GroupLattices.JointServices.VwResChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultAddMultConj
section
set_option autoImplicit false

namespace GlobalTheory.ConjugateMultiplicitySum

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_iff {z w : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) (hw : w ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = w ↔ ¬ z = w := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re hz
    simpa [pow_two] using this
  have him : z.re * z.im = 0 := by
    have := congrArg Complex.im hz
    simp [pow_two] at this
    linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  have hc : starRingEnd ℂ z = -z := by
    apply Complex.ext <;> simp [hre0]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hre
    exact hd.ne' hre
  rw [hc]
  constructor
  · intro h1 h2
    apply hz0
    have : (2 : ℂ) * z = 0 := by linear_combination h2 - h1
    simpa using this
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hw.symm) with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]

theorem mult_add_mult_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (τ : E →+* ℂ) : Datum.mult D τ + Datum.mult D (conjEmb τ) = D.p + D.q := by
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simpa using h
  have key : conjEmb τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 :=
    conj_eq_iff H.d_prime.pos hsq H.sqrt_neg_disc_sq
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (fun h' => key.1 h' h)]
  · rw [if_neg h, if_pos (key.2 h), add_comm]

end GlobalTheory.ConjugateMultiplicitySum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundaryStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nadel_vanishing_canonical_add_boundary : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → letI := algebraΓOfHom q; ∀ (K : CanonLB q D) (B M₀ : LB X) (hB : B.IsLB) (D₀ : CartierDiv X) (m' r : ℕ), 0 < m' → 0 < r → D₀.Eff → IsNef ℂ M₀ → IsBig ℂ M₀ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![B] : ℚ) = interNumRed ℂ C ![toLB D₀] / m' + interNumRed ℂ C ![M₀] / r) → ∃ J : X.IdealSheafData, (∀ y : X, y ∈ J.support ↔ ¬ KltAt q D (qWeil D₀ m') y) ∧ ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) (tens K.bundle B)) i) := by
  first | exact @GlobalTheory.NadelApp.nadel_canonical_add | exact GlobalTheory.NadelApp.nadel_canonical_add | (intros; apply GlobalTheory.NadelApp.nadel_canonical_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullMeasurableSetClassesOverFramesOn
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.ClassesMeas

theorem nullMeasurableSet_classesOver_framesOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ σ, GoodEmb c σ → ∀ Z : Comp Xo c, NullMeasurableSet (classesOver (V σ) (dict σ) (framesOn (U σ) Z)) (muQ1 (V σ)) := by
  intro D H Dw l Xo c r U V dict hC σ hσ Z
  obtain ⟨hU, ⟨Kf, th, hr, hK, _, hd⟩, _, _⟩ := hC.2 σ hσ
  obtain ⟨d1, d2, ⟨x0, _, d3⟩, d4, _, _⟩ := hd
  haveI : BorelSpace (GA D (V σ)) := ⟨rfl⟩
  let S : Set (U σ).Comp := {k | ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z}
  have key : ∀ g, dict σ g ∈ framesOn (U σ) Z ↔ (dict σ g).1 ∈ S := by
    intro g
    constructor
    · intro h
      exact ⟨(dict σ g).2, h⟩
    · rintro ⟨y, hy⟩
      exact _root_.GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c r U σ hU Z _ y _ (d4 g) hy
  have hP : IsOpen {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    refine Filter.mem_of_superset
      (GlobalTheory.LevelOpen.level_mem_nhds D (V σ) l.M Kf (by have := l.three_le; omega) hK g₀) ?_
    rintro g ⟨k, hk, h, hh, rfl⟩
    obtain ⟨γ, _, e1⟩ := d2 k hk g₀
    obtain ⟨γ', _, e2⟩ := d3 (g₀ * k) h hh
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    show (dict σ (g₀ * k * h)).1 ∈ S
    rw [f2, f1]
    exact hg₀
  have hpre : (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ))) =
      {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    show dict σ (Quotient.mk'' g : AutQ (V σ)).out ∈ framesOn (U σ) Z ↔ _
    rw [key]
    have hrel : QuotientGroup.rightRel (GQ (V σ)) (Quotient.mk'' g : AutQ (V σ)).out g :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨γ', _, e⟩ := d1 _ (inv_mem hrel) g
    have f := congrArg Sigma.fst e
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at f
    rw [f]
  refine MeasurableSet.nullMeasurableSet ?_
  show MeasurableSet (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ)))
  rw [hpre]
  exact hP.measurableSet

end GlobalTheory.ClassesMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentAndSum
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      rw [Nat.padicValNat_def]
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlace
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.BigOn.Exp.SerBase

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem natPrime_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hne : q ≠ Formalism.EigenvalueLevelCeiling.plc v) : (q : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  have hdvd : Formalism.EigenvalueLevelCeiling.plc v ∣ q := (ringChar.spec (𝓞 K ⧸ v.asIdeal) q).1 hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.L2.DIV.plc_prime' v) hq).1 hdvd).symm

theorem ownAt_prime_ne (D : D7) (w : D.what₂.places.Pl) :
    (ownAt D (D.plEq w)).Prime ∧ ownAt D (D.plEq w) ≠ Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  unfold ownAt
  split_ifs with h
  · exact ⟨D.host.pde'_prime, fun e => D.host.pde_ne (h.symm.trans e.symm)⟩
  · exact ⟨D.host.pde_prime, fun e => h e.symm⟩

theorem ownUnit : OwnUnit := by
  intro D c w
  obtain ⟨hq, hne⟩ := ownAt_prime_ne D w
  set q := ownAt D (D.plEq w) with hqdef
  have hnot := natPrime_notMem (D.plEq w) hq hne
  have hv : (D.plEq w).valuation D.what₂.LL (q : D.what₂.LL) = 1 := by
    have := ((D.plEq w).valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 hnot
    simpa using this
  have hq0 : (q : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hnn : (0 : WithTop ℤ) ≤ D.what₂.places.val w (q : D.what₂.LL)⁻¹ :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  obtain ⟨y, hy⟩ := (c.embW_w w _).1 hnn
  rw [map_inv₀, map_natCast] at hy
  have hqF : ((q : ℕ) : FractionRing (c.Oe w)) ≠ 0 := by
    have := (map_ne_zero (c.embW w)).2 hq0
    rwa [map_natCast] at this
  have h1 : algebraMap (c.Oe w) (FractionRing (c.Oe w)) (y * (q : c.Oe w)) = 1 := by
    rw [map_mul, hy, map_natCast]
    exact inv_mul_cancel₀ hqF
  have h2 : y * (q : c.Oe w) = 1 := by
    apply IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w))
    rw [h1, map_one]
  exact (Units.mkOfMulEqOne (q : c.Oe w) y (by rw [mul_comm]; exact h2)).isUnit

end GlobalTheory.BigOn.Exp.SerBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def PhiAt (y : Y₀ X Z) (ν : Valuation ((Y₀ X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (φ : ℝ) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V) (ρ φT : ℝ),
    0 < ρ ∧ GlobalTheory.SlopeRec.HasPhi y' φT ∧ φ = ρ * φT ∧
    (letI := io.toAlgebra; X.ptY y'.1 =
      Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ∧
    ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPoint
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
   intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
   have hG := ObjDim.isAbelianScheme Xo.univ
   have hA : IsAbelianScheme A := by
     have := hG.comm
     have hc : IsCommMonObj A := by
       rw [isCommMonObj_iff_isMulCommutative]
       intro T
       refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
       rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
         ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
     exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
       MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
       MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
   have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
     (ObjDim.smoothOfRelativeDimension Xo.univ)
   have := hA.comm
   have := a.hom
   exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
     (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v
end GlobalTheory.PolAdjointRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  first | exact @GlobalTheory.mixExp_interNumRed | exact GlobalTheory.mixExp_interNumRed | (intros; apply GlobalTheory.mixExp_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelNbhd

open GlobalTheory.GfCut

variable {D : D7}

def finIdem (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem finIdem_mul : finIdem D * finIdem D = finIdem D := by
  unfold finIdem
  rw [← map_mul]
  congr 1
  show ((0 : Ainf D.host.F) * 0, (1 : Af D.host.F) * 1) = (0, 1)
  simp

theorem cA_finIdem : cA D (finIdem D) = finIdem D := by
  unfold finIdem
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem fst_finIdem :
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 0 := by
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem snd_finIdem :
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 1 := by
  show sndA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 1
  rw [show sndA D.host.F (pairA D.host.F 0 1) = 1 from rfl]
  rfl

def finPartGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (AE D) :=
  ⟨finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • 1,
    finIdem D • ((matHom V g)⁻¹).1 + (1 - finIdem D) • 1,
    idem_mul _ finIdem_mul _ _ (matHom V g).mul_inv, idem_mul _ finIdem_mul _ _ (matHom V g).inv_mul⟩

theorem finPartGL_mem (V : HSp D) (g : GA D V) : finPartGL V g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have hgU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU := idem_unitary (cA D) _ cA_finIdem finIdem_mul _ _ hgU
  exact hKU

def finPartG (V : HSp D) (g : GA D V) : GA D V :=
  (⟨finPartGL V g, finPartGL_mem V g⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem finPartG_mem_GfC (V : HSp D) (g : GA D V) : finPartG V g ∈ GfC V := by
  show infHom V (finPartG V g) = 1
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = 1
  rw [map_idem, fst_finIdem, zero_smul, zero_add, sub_zero, one_smul]

theorem finHom_finPartG (V : HSp D) (g : GA D V) : finHom V (finPartG V g) = finHom V g := by
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = _
  rw [map_idem, snd_finIdem, one_smul, sub_self, zero_smul, add_zero]
  rfl

theorem inv_finPartG_mul_mem_GinfC (V : HSp D) (g : GA D V) : (finPartG V g)⁻¹ * g ∈ GinfC V := by
  show finHom V ((finPartG V g)⁻¹ * g) = 1
  rw [map_mul, map_inv, finHom_finPartG, inv_mul_cancel]

theorem finCong_finPartG_iff {V : HSp D} {N : ℕ} (g : GA D V) :
    GlobalTheory.Member.FinCong V N (finPartG V g) ↔ GlobalTheory.Member.FinCong V N g := by
  unfold GlobalTheory.Member.FinCong
  rw [finHom_finPartG]

theorem level_mul_inf_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N →
    IsLevelK V N Kf → ∀ g₀ : GA D V,
      {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hU := GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN
  have ht : Filter.Tendsto (fun x : GA D V => g₀⁻¹ * x) (𝓝 g₀) (𝓝 1) := by
    have := (continuous_const_mul g₀⁻¹).tendsto g₀
    rwa [inv_mul_cancel] at this
  refine Filter.mem_of_superset (ht hU) fun x hx => ?_
  have hx' : GlobalTheory.Member.FinCong V N (g₀⁻¹ * x) := hx
  refine ⟨finPartG V (g₀⁻¹ * x), (hK _).2 ⟨finPartG_mem_GfC V _, (finCong_finPartG_iff _).2 hx'⟩,
    (finPartG V (g₀⁻¹ * x))⁻¹ * (g₀⁻¹ * x), inv_finPartG_mul_mem_GinfC V _, ?_⟩
  group

end GlobalTheory.LevelNbhd
end
end

