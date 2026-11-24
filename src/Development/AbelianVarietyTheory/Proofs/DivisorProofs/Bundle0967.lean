module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FrameDom

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexOrder

variable {n : ℕ} {Hm x₀ : Mt n} {q : ℕ}

theorem conjTranspose_map_conj (y : Mt n) : (y.map (starRingEnd ℂ))ᴴ = yᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem map_conj_conj (y : Mt n) : (y.map (starRingEnd ℂ)).map (starRingEnd ℂ) = y := by
  ext i j
  simp

theorem det_map_conj_ne {y : Mt n} (h : y.det ≠ 0) : (y.map (starRingEnd ℂ)).det ≠ 0 := by
  have e : y.map (starRingEnd ℂ) = (yᴴ)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, det_transpose, det_conjTranspose]
  intro h0
  exact h (star_eq_zero.mp h0)

theorem neg_gram_mul (Hm x b : Mt n) : -((x * b)ᴴ * Hm * (x * b)) = bᴴ * (-(xᴴ * Hm * x)) * b := by
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem neg_gram_orth (h : OrthFr Hm q x₀) : -(x₀ᴴ * Hm * x₀) = diagonal (sv q) := by
  rw [h.2, ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq q n, ← Matrix.diagonal_neg, neg_neg]

theorem sv_mul_self (a : Fin n) : sv q a * sv q a = 1 := by
  simp only [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv]
  split_ifs <;> norm_num

theorem det_diag_sv_ne : (diagonal (sv q) : Mt n).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => left_ne_zero_of_mul_eq_one (sv_mul_self a)

theorem det_ne_of_orth (h : OrthFr Hm q x₀) : x₀.det ≠ 0 ∧ Hm.det ≠ 0 := by
  have h1 : (x₀ᴴ * Hm * x₀).det ≠ 0 := by
    have e : x₀ᴴ * Hm * x₀ = -(diagonal (sv q)) := by rw [← neg_gram_orth h, neg_neg]
    rw [e, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) det_diag_sv_ne
  rw [det_mul, det_mul] at h1
  exact ⟨right_ne_zero_of_mul h1, right_ne_zero_of_mul (left_ne_zero_of_mul h1)⟩

theorem neg_gram_isHermitian (h : OrthFr Hm q x₀) (x : Mt n) : (-(xᴴ * Hm * x)).IsHermitian := by
  obtain ⟨hx0, -⟩ := det_ne_of_orth h
  have hD : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [h.2, Matrix.diagonal_conjTranspose]
    congr 1
    ext a
    simp
  have hD' : x₀ᴴ * Hmᴴ * x₀ = x₀ᴴ * Hm * x₀ := by
    rw [← hD]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).mpr hx0.isUnit
  have hus : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [det_conjTranspose]
    have hs : star x₀.det ≠ 0 := fun h0 => hx0 (star_eq_zero.mp h0)
    exact hs.isUnit
  have hH : Hmᴴ = Hm := hus.mul_left_cancel (hu.mul_right_cancel hD')
  exact (Matrix.isHermitian_conjTranspose_mul_mul x (hH : Hm.IsHermitian)).neg

theorem mul_upT_mem {x b : Mt n} (hx : x ∈ frDom Hm q) (hb : UpT b) : x * b ∈ frDom Hm q := by
  obtain ⟨hdet, hmin⟩ := hx
  refine ⟨by rw [det_mul]; exact mul_ne_zero hdet hb.1, fun i => ?_⟩
  have hbT : b.BlockTriangular id := fun a c hca => hb.2 a c hca
  have hN : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    simp [hb.2 a c hca]
  have hdiag : ∀ k, b k k ≠ 0 := by
    have := hb.1
    rw [Matrix.det_of_upperTriangular hbT] at this
    exact fun k => Finset.prod_ne_zero_iff.mp this k (Finset.mem_univ k)
  have e : -((x * b)ᴴ * Hm * (x * b)) =
      (b.map (starRingEnd ℂ))ᵀ * (-(xᴴ * Hm * x)) * (b.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    rw [neg_gram_mul, ← conjTranspose_map_conj (b.map (starRingEnd ℂ)), map_conj_conj]
  rw [e, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj hN i]
  refine ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pos_conj_mul ?_ (hmin i)
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  simpa using hdiag _

theorem unitary_mul_mem (hH : Hm.det ≠ 0) {u x : Mt n} (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    u * x ∈ frDom Hm q := by
  have hu' : uᴴ * Hm * u = Hm := hu
  have hg : (u * x)ᴴ * Hm * (u * x) = xᴴ * Hm * x := by
    have : (u * x)ᴴ * Hm * (u * x) = xᴴ * (uᴴ * Hm * u) * x := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hu']
  have hu0 : u.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hu'
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hH this.symm
  refine ⟨by rw [det_mul]; exact mul_ne_zero hu0 hx.1, fun i => ?_⟩
  rw [hg]
  exact hx.2 i

theorem neg_gram_conj (h : OrthFr Hm q x₀) (y : Mt n) :
    -((x₀ * y.map (starRingEnd ℂ))ᴴ * Hm * (x₀ * y.map (starRingEnd ℂ))) = Gy q y := by
  rw [neg_gram_mul Hm x₀ (y.map (starRingEnd ℂ)), neg_gram_orth h, conjTranspose_map_conj]
  rfl

theorem mem_of_ok (h : OrthFr Hm q x₀) {y : Mt n} (hy : Ok q y) : x₀ * y.map (starRingEnd ℂ) ∈ frDom Hm q := by
  refine ⟨?_, fun i => ?_⟩
  · rw [det_mul]
    exact mul_ne_zero (det_ne_of_orth h).1 (det_map_conj_ne (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.det_ne_of_ok hy))
  · rw [neg_gram_conj h]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos hy i (Nat.le_of_lt_succ i.isLt)

theorem ok_of_gy {y : Mt n} (h : Gy q y = diagonal (sv q)) : Ok q y := by
  show (diagonal (sv q) * Gy q y).PosDef
  rw [h, diagonal_mul_diagonal]
  have e : (fun a : Fin n => sv q a * sv q a) = fun _ => (1 : ℂ) := funext sv_mul_self
  rw [e, diagonal_one]
  exact Matrix.PosDef.one

theorem ok_one : Ok q (1 : Mt n) := by
  refine ok_of_gy ?_
  show (1 : Mt n)ᵀ * diagonal (sv q) * (1 : Mt n).map (starRingEnd ℂ) = diagonal (sv q)
  rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem base_mem (h : OrthFr Hm q x₀) : x₀ ∈ frDom Hm q := by
  have := mem_of_ok h (ok_one (q := q) (n := n))
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem isOpen_frDom (Hm : Mt n) (q : ℕ) : IsOpen (frDom Hm q) := by
  have e : frDom Hm q = {x : Mt n | x.det ≠ 0} ∩
      ⋂ i : Fin (n + 1), {x : Mt n | 0 < psgn q i * (lminor (-(xᴴ * Hm * x)) i).re} := by
    ext x
    simp only [frDom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsOpen.inter (isOpen_ne_fun continuous_id.matrix_det continuous_const) ?_
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  exact ((((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id).neg).matrix_submatrix _ _).matrix_det

theorem isPreconnected_frDom (h : OrthFr Hm q x₀) : IsPreconnected (frDom Hm q) := by
  have hOk : IsPreconnected {y : Mt n | Ok q y} := by
    have e : {y : Mt n | Ok q y} =
        (fun y : Unit → Mt n => y ()) '' {y : Unit → Mt n | ∀ i, Ok q (y i)} := by
      ext y
      constructor
      · intro hy
        exact ⟨fun _ => y, fun _ => hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok (p0 := q) (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hUp : IsPreconnected {b : Mt n | UpT b} := by
    have e : {b : Mt n | UpT b} =
        (fun b : Unit → Mt n => b ()) '' {b : Unit → Mt n |
          ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin n, c < a → b i a c = 0} := by
      ext b
      constructor
      · intro hb
        exact ⟨fun _ => b, fun _ => hb, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hT : IsPreconnected ((fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y}) :=
    hOk.image _ (continuous_const.matrix_mul
      (continuous_id.matrix_map Complex.continuous_conj)).continuousOn
  have hTsub : (fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y} ⊆ frDom Hm q := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_of_ok h hy
  refine isPreconnected_of_forall x₀ fun x hx => ?_
  have hxB : IsPreconnected ((fun b : Mt n => x * b) '' {b : Mt n | UpT b}) :=
    hUp.image _ (continuous_const.matrix_mul continuous_id).continuousOn
  have hxBsub : (fun b : Mt n => x * b) '' {b : Mt n | UpT b} ⊆ frDom Hm q := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_upT_mem hx hb

  obtain ⟨b, hbdet, hbT, hbeq⟩ := GlobalTheory.UnitFrames.exists_upper_conj_eq_signature q (-(xᴴ * Hm * x))
    (neg_gram_isHermitian h x) hx.2
  set c : Mt n := b.map (starRingEnd ℂ) with hc
  have hcU : UpT c := by
    refine ⟨det_map_conj_ne hbdet, fun a d hda => ?_⟩
    simp [hc, hbT hda]
  have hgc : -((x * c)ᴴ * Hm * (x * c)) = diagonal (sv q) := by
    rw [neg_gram_mul, hc, conjTranspose_map_conj, hbeq, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq]
  have hx0 := (det_ne_of_orth h).1
  set y : Mt n := (x₀⁻¹ * (x * c)).map (starRingEnd ℂ) with hy
  have hxy : x₀ * y.map (starRingEnd ℂ) = x * c := by
    rw [hy, map_conj_conj, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv x₀ hx0.isUnit, Matrix.one_mul]
  have hyOk : Ok q y := by
    refine ok_of_gy ?_
    rw [← neg_gram_conj h y, hxy, hgc]
  refine ⟨_ ∪ _, Set.union_subset hTsub hxBsub, Or.inl ⟨1, ok_one, ?_⟩,
    Or.inr ⟨1, ⟨by simp, fun a c hca => by simp [Matrix.one_apply_ne (ne_of_lt hca).symm]⟩, Matrix.mul_one x⟩,
    hT.union (x * c) ⟨y, hyOk, hxy⟩ ⟨c, hcU, rfl⟩ hxB⟩
  show x₀ * (1 : Mt n).map (starRingEnd ℂ) = x₀
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

end GlobalTheory.HolDict.FrameDom


open GlobalTheory.HolDict.FrameDom in
theorem GlobalTheory.HolDict.frDoms_open_preconnected_stable : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → IsOpen (frDoms Hm q) ∧ IsPreconnected (frDoms Hm q) ∧ (∀ u ∈ UG Hm, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → ∀ x ∈ frDoms Hm q, (fun τ => (u τ * Matrix.of (x τ) * b τ : Mt n)) ∈ frDoms Hm q) ∧ (fun τ => (x₀ τ : Mt n)) ∈ frDoms Hm q := by
  intro n ι _ _ Hm q x₀ h
  have e : frDoms Hm q = Set.univ.pi fun τ => frDom (Hm τ) (q τ) := by
    ext x
    exact ⟨fun hx τ _ => hx τ, fun hx τ => hx τ (Set.mem_univ τ)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]
    exact isOpen_set_pi Set.finite_univ fun τ _ => isOpen_frDom (Hm τ) (q τ)
  · rw [e]
    exact isPreconnected_univ_pi fun τ => isPreconnected_frDom (h τ)
  · intro u hu b hb x hx τ
    exact mul_upT_mem (unitary_mul_mem (det_ne_of_orth (h τ)).2 (hu τ) (hx τ)) (hb τ)
  · intro τ
    exact base_mem (h τ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

end GlobalTheory.FockSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixing
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem support_cxF_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  intro p _ G v wt Kf f _ K' f' _ β x t hx hfin a
  by_cases hpos : 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re
  · refine (hfin (LeftCosets.rep _ _ a.1) _ hpos).subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    unfold cxF at hy
    split_ifs at hy with hc
    · exact ⟨hc.2, left_ne_zero_of_mul hy⟩
    · exact absurd rfl hy
  · convert Set.finite_empty
    ext y
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    unfold cxF
    rw [if_neg (fun hc => hpos hc.1)]

end GlobalTheory.CxUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinsFixHalf

theorem pb_eq_of_pins : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → LawsJ T → (∀ i, OMPins T R κ v₀ O i) → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR hT hO
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR
    ((hO ⟨0, lt_of_lt_of_le (by norm_num) D.R.two_le_m⟩).2.tuple ()).half

end GlobalTheory.PinsFixHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeAdjoint

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem realUnif (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.SphericalOps.RealUnif P := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (unramified_host D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap, SetLike.not_le_iff_exists] at h2
  obtain ⟨x, hx, hx2⟩ := h2
  exact ⟨x, algebraMap _ _ x, rfl, hx, hx2⟩


open GlobalTheory.SphericalOps in
theorem ipM_heckeOn_dualLab : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  intro D V S θ M J χ Sb μ 𝓕 hθ hμ h𝓕 hS P d R R' h h' T hT T' hT' hRT hRT'
  obtain ⟨R₁, h₁', hcard, K, x, hK, hR, hR₁⟩ := exists_dual (realUnif D P) h
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI : μ.IsMulRightInvariant := _root_.GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hS' := hS hθ hμ h𝓕
  have h₁ := ipM_spec M μ 𝓕 _ _ (hS' _ hRT _ hT')
  have h₂ := ipM_spec M μ 𝓕 _ _ (hS' _ hT _ hRT')
  obtain ⟨c₃, h₃⟩ := hS' _ hT _ hT
  obtain ⟨c₄, h₄⟩ := hS' _ hT' _ hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  have hex : ∀ τ, ∃ w : M.sm τ, (w : M.H τ) ≠ 0 := fun τ => by
    obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
    exact ⟨⟨w, hw⟩, h0⟩
  choose v hv using hex
  have hv0 : ∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv τ)
  have e : heckeOn M R' T' v = heckeLin V R₁ (T' v) :=
    labelUnique (realUnif D) P (dualLab d) R' R₁ h' h₁' (T' v) (hT'.lev v)
  have key : ∫ g in 𝓕, star (heckeOn M R T v g) * T' v g ∂μ =
      ∫ g in 𝓕, star (T v g) * heckeOn M R' T' v g ∂μ := by
    rw [e]
    exact integral_adjoint h𝓕 K x R R₁ (hT.aut v).cont (hT'.aut v).cont (hT.aut v).left (hT'.aut v).left
      (fun k hk g => by rw [hT.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (fun k hk g => by rw [hT'.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (h₃ v v).1 (h₄ v v).1 hR hR₁ hcard
  exact mul_right_cancel₀ hv0 ((h₁ v v).2.symm.trans (key.trans (h₂ v v).2))

end GlobalTheory.HeckeAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphicStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G), Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  first | (exact @GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (exact GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (intros; apply GlobalTheory.LKCx.Form.mk_eq_iff_rel <;> assumption)
end

