module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogClassNumberAtLe
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnClassLog

theorem log_le_of_count (h f n N g₀ g₁ T : ℕ) (rd L : ℝ) (hf : 1 ≤ f) (hn : 1 ≤ n) (hnN : n ≤ N) (hT : 1 ≤ T) (hrd : 0 < rd)
    (hL : 1 ≤ L) (hrdL : Real.log rd ≤ L) (hfN : (f : ℝ) * N ≤ Real.exp L) (hg₀ : Real.exp L ≤ g₀) (hg₁ : 1 ≤ g₁)
    (hh : (h : ℝ) ≤ (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2)) ^ (3 * (2 * f) * n ^ 2) *
      ((g₀ : ℝ) * g₁ * T) ^ (f * (n * n))) :
    Real.log h ≤ 55 * (f : ℝ) * (N : ℝ) ^ 2 * Real.log ((g₀ : ℝ) * g₁ * T) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hg₁' : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have he : 0 < Real.exp L := Real.exp_pos L
  have hg0 : (0 : ℝ) < g₀ := lt_of_lt_of_le he hg₀
  have hG : Real.exp L ≤ (g₀ : ℝ) * g₁ * T := by
    calc Real.exp L ≤ g₀ := hg₀
      _ = (g₀ : ℝ) * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  set G : ℝ := (g₀ : ℝ) * g₁ * T with hGd
  have hGp : 0 < G := lt_of_lt_of_le he hG
  have hLG : L ≤ Real.log G := (Real.le_log_iff_exp_le hGp).2 hG
  have hlG : 0 ≤ Real.log G := by linarith
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hrd' : rd ≤ Real.exp L := (Real.log_le_iff_le_exp hrd).1 hrdL
  have hfn : (f : ℝ) * n ≤ Real.exp L := le_trans (by gcongr) hfN
  have hn2 : (n : ℝ) ≤ Real.exp L := le_trans (by nlinarith) hfn
  have h12 : (12 : ℝ) ≤ Real.exp L ^ 3 := by
    have h1 : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.2 hL
    have h2 : (2.7 : ℝ) ≤ Real.exp L := by linarith [Real.exp_one_gt_d9]
    calc (12 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  set A : ℝ := 3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2) with hA
  have hAp : 0 < A := by rw [hA]; push_cast; positivity
  have hA9 : A ≤ G ^ 9 := by
    calc A = 12 * ((f : ℝ) * n) ^ 2 * (n : ℝ) ^ 2 * rd ^ 2 := by rw [hA]; push_cast; ring
      _ ≤ Real.exp L ^ 3 * Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp L ^ 2 := by gcongr
      _ = Real.exp L ^ 9 := by ring
      _ ≤ G ^ 9 := by gcongr
  have hfin : (h : ℝ) ≤ G ^ (55 * f * n ^ 2) := by
    calc (h : ℝ) ≤ A ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := hh
      _ ≤ (G ^ 9) ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := by gcongr
      _ = G ^ (55 * f * n ^ 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  calc Real.log h ≤ Real.log (G ^ (55 * f * n ^ 2)) := Real.log_le_log (by exact_mod_cast hpos) hfin
    _ = 55 * (f : ℝ) * (n : ℝ) ^ 2 * Real.log G := by rw [Real.log_pow]; push_cast; ring
    _ ≤ _ := by gcongr

theorem fibre_bound_le {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (u : Pr.Word) (n : ℕ) (hn : 1 ≤ n)
    (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (hSG : SG = Pr.vGs) :
    (∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n * n) ≤
      (Pr.g 0 * Pr.g 1 * Pr.T u) ^ (X.f * (n * n)) := by
  classical
  subst hSG
  have hT : ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n ≤ Pr.T u ^ (X.f * (n * n)) := by
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vT_norm u P hP']), Finset.prod_const, hP.vT_card, ← pow_mul]
    exact Nat.pow_le_pow_right (hP.T_prime u).pos (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_mul_self n))
  have hg : ∀ i, ∏ w ∈ Pr.vG i, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g i ^ (X.f * (n * n)) := by
    intro i
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vG_norm i P hP']), Finset.prod_const, hP.vG_card, ← pow_mul, mul_comm]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hP.g_ne ((hP.vG_norm 0 w h0).symm.trans (hP.vG_norm 1 w h1))
  have hU : ∏ w ∈ Pr.vGs, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g 0 ^ (X.f * (n * n)) * Pr.g 1 ^ (X.f * (n * n)) := by
    rw [← hg 0, ← hg 1, ← Finset.prod_union hd]
    unfold Primes.vGs
    congr
  rw [hU, mul_pow, mul_pow, mul_comm]
  exact Nat.mul_le_mul_left _ hT

end GlobalTheory.ColumnClassLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GlobalTheory.JSW

variable {n : ℕ}

def htGL (g : GL (Fin n) ℂ) : ℝ :=
  1 + ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖

def levSet (n r : ℕ) : Set (GL (Fin n) ℂ) :=
  {g | ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}

def rowCut (ρ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := fun j => if j ≤ ρ then x ρ j else 0

def secMat (ρ j : Fin n) (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i l => if i = ρ then (if l ≤ ρ then v l else 0) else if l = Equiv.swap j ρ i then 1 else 0


open Classical in
def toGL (x : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n) ℂ := if h : IsUnit x then h.unit else 1

theorem val_toGL {x : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit x) : (toGL x : Matrix (Fin n) (Fin n) ℂ) = x := by
  simp [toGL, h]

theorem one_le_htGL (g : GL (Fin n) ℂ) : 1 ≤ htGL g := by
  unfold htGL
  have h1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  linarith

theorem htGL_pos (g : GL (Fin n) ℂ) : 0 < htGL g := lt_of_lt_of_le one_pos (one_le_htGL g)

theorem htGL_inv (g : GL (Fin n) ℂ) : htGL g⁻¹ = htGL g := by
  unfold htGL; rw [inv_inv]; ring

theorem sum_norm_mul_le (a b : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(a * b) i j‖ ≤ ∑ j, ∑ l, ‖a i l‖ * ‖b l j‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ l, ‖a i l‖ * ∑ j, ‖b l j‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, ‖a i l‖ * ∑ l', ∑ j, ‖b l' j‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun l' => ∑ j, ‖b l' j‖) (fun _ _ => by positivity) (Finset.mem_univ l))
          (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem htGL_mul_le (g h : GL (Fin n) ℂ) : htGL (g * h) ≤ htGL g * htGL h := by
  unfold htGL
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 := sum_norm_mul_le (g : Matrix (Fin n) (Fin n) ℂ) h
  have h2 := sum_norm_mul_le ((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (g⁻¹ : GL (Fin n) ℂ)
  have a1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a3 : 0 ≤ ∑ i, ∑ j, ‖(h : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a4 : 0 ≤ ∑ i, ∑ j, ‖((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  nlinarith [mul_nonneg a1 a4, mul_nonneg a2 a3]

theorem norm_entry_le_htGL (g : GL (Fin n) ℂ) (i j : Fin n) : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ htGL g := by
  unfold htGL
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h1 : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ i))
  linarith

theorem continuous_htGL : Continuous (htGL : GL (Fin n) ℂ → ℝ) := by
  have h1 : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) ℂ => ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    Units.continuous_coe_inv
  unfold htGL
  fun_prop

theorem isOpenEmbedding_valGL :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) ℂ => fun i j => (g : Matrix (Fin n) (Fin n) ℂ) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℂ)

theorem measurable_comp_GL {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) ℂ → β} (hF : Continuous F) {γ : X → GL (Fin n) ℂ}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGL.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_dual {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {η : X → Z →L[ℝ] ℝ} (h : ∀ z, Measurable fun x => η x z) : Measurable η := by
  let b := Module.finBasis ℝ Z
  have : η = fun x => ∑ i, η x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext x
    ext z
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr z, map_sum]
    simp only [map_smul]
    simp [mul_comm]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (h _).smul_const _


end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
section
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.AdelicDetSpan

variable {E : Type} [Field E] [NumberField E]

noncomputable def comp (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem comp_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    comp P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem val_det_le_one {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  let N : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨M i j, h i j⟩
  have e : M = v.integer.subtype.mapMatrix N := rfl
  rw [e, ← RingHom.map_det]
  exact N.det.2

theorem exists_clear (Q : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hy : Valued.v (comp Q y) ≤ 1) :
    ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      P.valuation E (b : E) * Valued.v (comp P y) ≤ 1 := by
  classical
  have hloc : ∀ P : HeightOneSpectrum (𝓞 E), ∃ c : 𝓞 E, c ∉ Q.asIdeal ∧
      P.valuation E (c : E) * Valued.v (comp P y) ≤ 1 := by
    intro P
    by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, by simpa using h1⟩
    have hPQ : P ≠ Q := by rintro rfl; exact h1 hy
    have hnle : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      hPQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hnle
    have hlt : P.valuation E (a : E) < 1 := (P.valuation_lt_one_iff_mem (K := E) a).2 haP
    have h0 : Valued.v (comp P y) ≠ 0 := by
      intro h; rw [h] at h1; exact h1 zero_le_one
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ h0)⁻¹
    refine ⟨a ^ m, fun h => haQ (Q.isPrime.mem_of_pow_mem m h), ?_⟩
    have : ((a ^ m : 𝓞 E) : E) = (a : E) ^ m := by simp
    rw [this, map_pow]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc _ ≤ (Valued.v (comp P y))⁻¹ * Valued.v (comp P y) := mul_le_mul' hm.le le_rfl
      _ = 1 := inv_mul_cancel₀ h0
  choose c hcQ hc using hloc
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ Valued.v (comp P y) ≤ 1}.Finite :=
    Filter.eventually_cofinite.1 y.2
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  refine ⟨∏ P ∈ hfin.toFinset, c P, ?_, fun P => ?_⟩
  · rw [Q.isPrime.prod_mem_iff]
    rintro ⟨P, -, h⟩
    exact hcQ P h
  · by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact mul_le_one' (hle _ _) h1
    · have hm : P ∈ hfin.toFinset := by simpa using h1
      rw [← Finset.prod_erase_mul _ _ hm]
      have : (((∏ x ∈ hfin.toFinset.erase P, c x) * c P : 𝓞 E) : E) =
        ((∏ x ∈ hfin.toFinset.erase P, c x : 𝓞 E) : E) * (c P : E) := by push_cast; rfl
      rw [this, map_mul, mul_assoc]
      exact mul_le_one' (hle _ _) (hc P)

theorem exists_approx_matrix (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) (hg : h * g = 1) :
    ∃ X : Matrix (Fin n) (Fin n) E,
      (∀ i j, Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j) ≤ 1) ∧
      Valued.v (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det = 1 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => Pi.map fun _ : Fin n =>
      (algebraMap E (Q.adicCompletion E) : E → _)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) Q
  have hc : Continuous fun X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) => h * X :=
    continuous_const.matrix_mul continuous_id
  have hb : IsOpen {z : Q.adicCompletion E | Valued.v z < 1} := by
    have h := Valued.isOpen_ball (Q.adicCompletion E) 1
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  have hU : IsOpen {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      (∀ i j, Valued.v ((h * X - 1) i j) < 1) ∧ Valued.v ((h * X).det - 1) < 1} := by
    change IsOpen ({X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      ∀ i j, Valued.v ((h * X - 1) i j) < 1} ∩
      (fun X => (h * X).det - 1) ⁻¹' {z | Valued.v z < 1})
    refine IsOpen.inter ?_ (hb.preimage (hc.matrix_det.sub continuous_const))
    have : IsOpen (⋂ i, ⋂ j, {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
        Valued.v ((h * X - 1) i j) < 1}) :=
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hb.preimage ((hc.sub continuous_const).matrix_elem i j)
    simp only [← Set.setOf_forall] at this
    exact this
  obtain ⟨X, h1, h2⟩ := hd.exists_mem_open hU ⟨g, ⟨fun i j => by rw [hg]; simp, by rw [hg]; simp⟩⟩
  refine ⟨X, fun i j => ?_, ?_⟩
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j) < 1 := h1 i j
    have e : (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j =
        (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j +
          (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ h3.le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det - 1) < 1 := h2
    have := Valuation.map_eq_of_sub_lt Valued.v (x := (1 : Q.adicCompletion E)) (by rw [map_one]; exact h3)
    rwa [map_one] at this

theorem comp_mulVec {n : ℕ} (h : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (X : Matrix (Fin n) (Fin n) E) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    comp P (h.mulVec (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) =
      ((comp P).mapMatrix h * (algebraMap E (P.adicCompletion E)).mapMatrix X) i j := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, comp_alg]

theorem mem_span_detSet_iff : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  intro E _ _ n g L hL x
  classical
  have hL' : ∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
      Valued.v (comp Q ((g⁻¹).1.mulVec
        (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i)) ≤ 1 := hL
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  have hhg : ∀ Q : HeightOneSpectrum (𝓞 E),
      (comp Q).mapMatrix (g⁻¹).1 * (comp Q).mapMatrix g.1 = 1 := fun Q => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hdet : ∀ (Q : HeightOneSpectrum (𝓞 E)) (X : Matrix (Fin n) (Fin n) E),
      Q.valuation E X.det = Valued.v (comp Q g.1.det) *
        Valued.v ((comp Q).mapMatrix (g⁻¹).1 *
          (algebraMap E (Q.adicCompletion E)).mapMatrix X).det := fun Q X => by
    rw [← map_mul, RingHom.map_det, ← Matrix.det_mul, ← mul_assoc, ← map_mul, Units.mul_inv,
      map_one, one_mul, ← RingHom.map_det, val_alg]
  show _ ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (comp Q g.1.det)
  constructor
  · intro hx Q
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨v, hv, rfl⟩ := hd
      rw [hdet]
      refine mul_le_of_le_one_right' (val_det_le_one _ _ fun i j => ?_)
      rw [← comp_mulVec]
      exact (hL' _).1 (hv j) i Q
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul a b _ hb =>
      have e : a • b = (a : E) * b := rfl
      rw [e, map_mul]
      exact (mul_le_of_le_one_left' (hle Q a)).trans hb
  · intro hx
    have hloc : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧
        b • x ∈ Submodule.span (𝓞 E) (detSet L) := by
      intro Q
      obtain ⟨X, hX1, hX2⟩ := exists_approx_matrix Q _ _ (hhg Q)
      choose c hcQ hc using fun i j => exists_clear Q ((g⁻¹).1.mulVec
        (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i)
        (by rw [comp_mulVec]; exact hX1 i j)
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, b = ∏ p : Fin n × Fin n, c p.1 p.2 := ⟨_, rfl⟩
      have hbQ : b ∉ Q.asIdeal := by
        rw [hb, Q.isPrime.prod_mem_iff]
        rintro ⟨p, -, h⟩
        exact hcQ _ _ h
      have hb1 : Q.valuation E (b : E) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q (r := b)).2 hbQ
      have hbc : ∀ i j (P : HeightOneSpectrum (𝓞 E)),
          P.valuation E (b : E) ≤ P.valuation E (c i j : E) := by
        intro i j P
        obtain ⟨t, ht⟩ : c i j ∣ b := hb ▸ Finset.dvd_prod_of_mem
          (fun p : Fin n × Fin n => c p.1 p.2) (Finset.mem_univ (i, j))
        have : (b : E) = (c i j : E) * (t : E) := by rw [ht]; push_cast; rfl
        rw [this, map_mul]
        exact mul_le_of_le_one_right' (hle P t)
      have hd : ((b : E) • X).det ∈ detSet L := by
        refine ⟨fun j i => (b : E) * X i j, fun j => (hL' _).2 fun i P => ?_, rfl⟩
        have e : comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) ((b : E) * X k j)) i) =
            algebraMap E _ (b : E) * comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, comp_alg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [e, map_mul, val_alg]
        exact (mul_le_mul' (hbc i j P) le_rfl).trans (hc i j P)
      have hdv : Q.valuation E ((b : E) • X).det = Valued.v (comp Q g.1.det) := by
        rw [Matrix.det_smul, map_mul, map_pow, hb1, one_pow, one_mul, hdet, hX2, mul_one]
      obtain ⟨d, hdd⟩ : ∃ d, d = ((b : E) • X).det := ⟨_, rfl⟩
      rw [← hdd] at hd hdv
      have hg0 : Valued.v (comp Q g.1.det) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((g.isUnit.map Matrix.detMonoidHom).map (comp Q)).ne_zero
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hdv
        exact hg0 hdv.symm
      obtain ⟨s, hsQ, hs⟩ := exists_clear Q (algebraMap E _ (x / d)) (by
        rw [comp_alg, val_alg, map_div₀, hdv]
        exact (div_le_one₀ (zero_lt_iff.2 hg0)).2 (hx Q))
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
        ((s : E) * (x / d)) (fun P => by
          have := hs P
          rwa [comp_alg, val_alg, ← map_mul] at this)
      refine ⟨s, hsQ, ?_⟩
      have e : s • x = a • d := by
        have e1 : s • x = (s : E) * x := rfl
        have e2 : a • d = algebraMap (𝓞 E) E a * d := rfl
        rw [e1, e2, ha]
        field_simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hd)
    let I : Ideal (𝓞 E) := (Submodule.span (𝓞 E) (detSet L)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E x)
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
      have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
      obtain ⟨b, hb, hbx⟩ := hloc ⟨M, hM.isPrime, hM0⟩
      exact hb (hIM hbx)
    have h1 : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (detSet L) := h1
    rwa [one_smul] at h2

end GlobalTheory.AdelicDetSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDerivWeierstrassPHalfPeriodsDiscriminantStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant : ∀ (L : PeriodPair) (a b t : ℂ), a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice → 2 * b ∈ L.lattice → 2 * t ∉ L.lattice → L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) * L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  first | exact @GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ | exact GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ | (intros; apply GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDetStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursionStatement
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  first | exact @GlobalTheory.WhittakerRecursion.recursion | exact GlobalTheory.WhittakerRecursion.recursion | (intros; apply GlobalTheory.WhittakerRecursion.recursion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k rS r t j c' n' c n : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → n' + c' = r + (j - 1) * t → n' + c' ≤ n + c → k ≤ n' → k ≤ n → k ≤ r → LocSmall q (LocE.lamY P q n' c' fun i => i + 1) (LocE.lamY P q n c fun i => i + 1) (LocE.PhiGS q ψ χ k rS r t j c' n' c n) 1 := by
  first | exact @GlobalTheory.SymLevelDatum.locSmall_phiGS | exact GlobalTheory.SymLevelDatum.locSmall_phiGS | (intros; apply GlobalTheory.SymLevelDatum.locSmall_phiGS <;> assumption)
end

