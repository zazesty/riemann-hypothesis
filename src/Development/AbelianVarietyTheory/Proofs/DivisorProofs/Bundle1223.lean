module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureWeylCellOddUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZeta
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section

namespace GlobalTheory.FullRankCoinv

theorem continuous_of_mul_right_inv {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ) (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ho : IsOpen ((g⁻¹ * ·) ⁻¹' (H : Set G)) := hH.preimage (continuous_const.mul continuous_id)
  have hev : ∀ᶠ x in nhds g, f g = f x := by
    filter_upwards [ho.mem_nhds (by simpa using H.one_mem)] with x hx
    have := hf g (g⁻¹ * x) hx
    simpa using this.symm
  exact tendsto_const_nhds.congr' hev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gdet (n : ℕ) : Continuous (gdet : GL (Fin n) k → kˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert (Units.continuous_val (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
  · convert (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g
    show (((gdet g)⁻¹ : kˣ) : k) = _
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _

theorem continuous_char_apow (n : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν) (z : ℂ) :
    Continuous fun g : GL (Fin n) k => (ν (gdet g) : ℂ) * apow (gdet g) z := by
  let H : Subgroup (GL (Fin n) k) := GlobalTheory.SplitWeil.KO k (Fin n) ⊓ ν.ker.comap Matrix.GeneralLinearGroup.det
  have hH : IsOpen (H : Set (GL (Fin n) k)) :=
    isOpen_KO.inter (hν.preimage (continuous_gdet (k := k) n))
  refine continuous_of_mul_right_inv H hH _ fun g h hh => ?_
  have h1 : ν (gdet h) = 1 := hh.2
  have h2 : apow (gdet h) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hh.1) z
  simp only [gdet_mul, map_mul, Units.val_mul, apow_mul, h1, h2, Units.val_one, mul_one]

theorem integrable_fibre (n d : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν)
    [MeasurableSpace k] [BorelSpace k] (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ fullRk k n d)
    (Y : Matrix (Fin n) (Fin d) k) :
    Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  obtain ⟨⟨hlc, hcs⟩, hrk⟩ := hΨ
  by_cases hY : Y.rank = n
  swap
  · have h0 : (fun g : GL (Fin n) k =>
        Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = 0 := by
      funext g
      have : (g.val * Y).rank = Y.rank :=
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
      rw [hrk _ (by rw [this]; exact hY)]; simp
    rw [h0]; exact integrable_zero _ _ _

  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin d) (Fin n) k, Y * R = 1 := by
    have hsurj : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hY
    obtain ⟨f, hf⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have := congrArg LinearMap.toMatrix' hf
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' Y.mulVecLin = Y from LinearMap.toMatrix'_toLin' Y] at this

  have hsupp : tsupport Ψ = Function.support Ψ := by
    refine (IsClosed.closure_eq ?_)
    convert (hlc.isOpen_fiber 0).isClosed_compl using 1
    ext x; simp [Function.support]
  have hrkS : ∀ X ∈ tsupport Ψ, X.rank = n := fun X hX => by
    by_contra h; rw [hsupp] at hX; exact hX (hrk X h)
  set K' : Set (Matrix (Fin n) (Fin d) k) := tsupport Ψ ∩ {X | X * R * Y = X}
  have hK' : IsCompact K' := hcs.inter_right
    (isClosed_eq ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const) continuous_id)
  have hunit : ∀ X ∈ K', IsUnit (X * R) := fun X hX => by
    have h1 : n ≤ (X * R).rank := by
      calc n = X.rank := (hrkS X hX.1).symm
        _ = (X * R * Y).rank := by rw [hX.2]
        _ ≤ (X * R).rank := Matrix.rank_mul_le_left _ _
    have h2 : (X * R).rank = Fintype.card (Fin n) := le_antisymm
      ((Matrix.rank_le_card_width _).trans (by simp)) (by simpa using h1)
    have hli : LinearIndependent k (X * R).row := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact h2.symm.trans (Matrix.rank_eq_finrank_span_row _)
    exact Matrix.linearIndependent_rows_iff_isUnit.1 hli
  classical
  let φ : Matrix (Fin n) (Fin d) k → GL (Fin n) k := fun X =>
    if h : IsUnit (X * R) then h.unit else 1
  have hφ : ∀ X ∈ K', (φ X).val = X * R := fun X hX => by simp [φ, hunit X hX]
  have hφc : ContinuousOn φ K' := by
    rw [(isEmbedding_val_GL (k := k) (n := Fin n)).isInducing.continuousOn_iff]
    exact (continuous_id.matrix_mul continuous_const).continuousOn.congr fun X hX => hφ X hX
  set S : Set (GL (Fin n) k) := {g | g.val * Y ∈ tsupport Ψ}
  have hSsub : S ⊆ φ '' K' := fun g hg => by
    have hX : g.val * Y ∈ K' := ⟨hg, show g.val * Y * R * Y = g.val * Y by rw [Matrix.mul_assoc g.val Y R, hR, Matrix.mul_one]⟩
    refine ⟨_, hX, Units.ext ?_⟩
    rw [hφ _ hX, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hSc : IsClosed S := (isClosed_tsupport Ψ).preimage (Units.continuous_val.matrix_mul continuous_const)
  have hS : IsCompact S := (hK'.image_of_continuousOn hφc).of_isClosed_subset hSc hSsub
  have hcont : Continuous (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) := by
    have h1 : Continuous fun g : GL (Fin n) k => Ψ (g.val * Y) :=
      hlc.continuous.comp (Units.continuous_val.matrix_mul continuous_const)
    refine (h1.mul (continuous_char_apow n ν hν ((Fintype.card (Fin d) : ℂ) / 2))).congr fun g => ?_
    simp only [Pi.mul_apply]; ring
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  refine hcont.integrable_of_hasCompactSupport (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (HasCompactSupport.intro hS fun g hg => ?_)
  rw [image_eq_zero_of_notMem_tsupport hg]; simp

end GlobalTheory.FullRankCoinv

theorem GlobalTheory.FullRankCoinv.integrable_fibre_target : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) :=
  fun _ _ _ _ _ _ _ n d ν hν Ψ hΨ Y => GlobalTheory.FullRankCoinv.integrable_fibre n d ν hν Ψ hΨ Y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDepthPowerLastSimpleReflectionCell
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell.Atone

theorem level_sets {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (V : ℕ → ℝ)
    (hmeas : ∀ j : ℕ, MeasurableSet {x | f x ≤ j})
    (hV : ∀ j, μ {x | f x ≤ j} = ENNReal.ofReal (V j))
    (hV0 : ∀ j, 0 ≤ V j) :
    Measurable f ∧ ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (V j - if j = 0 then 0 else V (j - 1)) := by
  have hset : ∀ i : ℕ, f ⁻¹' {i + 1} = {x | f x ≤ i + 1} \ {x | f x ≤ i} := by
    intro i; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]; omega
  have hset0 : f ⁻¹' {0} = {x | f x ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]; omega
  refine ⟨measurable_to_countable' fun j => ?_, fun j => ?_⟩
  · rcases j with _ | i
    · rw [hset0]; exact hmeas 0
    · rw [hset]; exact (hmeas _).diff (hmeas _)
  · rcases j with _ | i
    · rw [hset0, hV]; simp
    · have hsub : {x | f x ≤ i} ⊆ {x | f x ≤ i + 1} := fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; omega
      rw [hset, measure_diff hsub (hmeas i).nullMeasurableSet (by rw [hV]; exact ENNReal.ofReal_ne_top),
        hV, hV, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ENNReal.ofReal_sub _ (hV0 i)]

theorem sums_over_levels {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (hf : Measurable f)
    (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (w j))
    (c : ℕ → ℂ) (s : ℂ) (hs : HasSum (fun j => c j * (w j : ℂ)) s) (r : ℝ)
    (hr : HasSum (fun j => ‖c j‖ * w j) r) :
    ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r ∧ Integrable (fun x => c (f x)) μ ∧ ∫ x, c (f x) ∂μ = s := by
  have hmap : ∀ j, (μ.map f) {j} = ENNReal.ofReal (w j) := fun j => by
    rw [Measure.map_apply hf (measurableSet_singleton j)]; exact hw j
  have hL : ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r := by
    rw [← lintegral_map (f := fun j => ‖c j‖ₑ) measurable_from_nat hf, lintegral_countable']
    simp_rw [hmap]
    rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (hw0 j)) hr.summable]
    congr 1; funext j
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  have hI : Integrable (fun x => c (f x)) μ := by
    refine ⟨(measurable_from_nat.comp hf).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL]; exact ENNReal.ofReal_lt_top
  refine ⟨hL, hI, ?_⟩
  have hIm : Integrable c (μ.map f) :=
    (integrable_map_measure measurable_from_nat.aestronglyMeasurable hf.aemeasurable).2 hI
  rw [← integral_map hf.aemeasurable measurable_from_nat.aestronglyMeasurable, integral_countable hIm,
    ← hs.tsum_eq]
  congr 1; funext j
  rw [measureReal_def, hmap, ENNReal.toReal_ofReal (hw0 j), Complex.real_smul, mul_comm]

end GlobalTheory.WeylCell.WeylUnipotentShell.Atone


open GlobalTheory.WeylCell.WeylUnipotentShell.Atone in
theorem _root_.GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hy hwy _ _ μ _ hμ z hz
  have q2 : 2 ≤ q := hq.2.2.2.2.2.1
  have hsh := _root_.GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup L ϖ σ q hq n k hk hn y hy hwy
  have hvol := _root_.GlobalTheory.WeylCell.WeylUnipotentShell.measure_shellU L ϖ σ q hq n k hk hn y hy hwy μ hμ
  let f : cellU y → ℕ := fun u => depthU k (u : GU σ n)
  let V : ℕ → ℝ := fun j => (q : ℝ) ^ (j + 2 * (j / 2))
  have hV0 : ∀ j, 0 ≤ V j := fun j => by positivity
  have hlev : ∀ j : ℕ, {u : cellU y | f u ≤ j} = shellU k y j := by
    intro j; ext u; exact (mem_shellU_iff_depth k y j u).symm
  have hmeas : ∀ j : ℕ, MeasurableSet {u : cellU y | f u ≤ j} := fun j => by
    rw [hlev]; exact (hsh.1 j).1.measurableSet
  have hV : ∀ j : ℕ, μ {u : cellU y | f u ≤ j} = ENNReal.ofReal (V j) := fun j => by
    rw [hlev, hvol j, ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast]
  obtain ⟨hf, hlv⟩ := level_sets μ f V hmeas hV hV0
  let w : ℕ → ℝ := fun j => V j - if j = 0 then 0 else V (j - 1)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [w, V]
    split_ifs with h
    · simp only [sub_zero]; positivity
    · rw [sub_nonneg]; exact pow_le_pow_right₀ hq1 (by omega)
  have hwc : ∀ j : ℕ, ((w j : ℝ) : ℂ) = (q : ℂ) ^ (j + 2 * (j / 2)) -
      (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))) := fun j => by
    simp only [w, V]; split_ifs <;> push_cast <;> rfl
  let c : ℕ → ℂ := fun j => (z / (q : ℂ) ^ 2) ^ j
  have hs : HasSum (fun j => c j * (w j : ℂ)) (cSU q z) := by
    simp only [c, hwc]; exact _root_.GlobalTheory.SURankOneSeries.hasSum_series q q2 z hz
  have hz' : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hz
  have hs' := _root_.GlobalTheory.SURankOneSeries.hasSum_series q q2 _ hz'
  have hterm : ∀ j : ℕ, (((‖z‖ : ℝ) : ℂ) / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))) =
      ((‖c j‖ * w j : ℝ) : ℂ) := fun j => by
    rw [← hwc]; simp only [c, norm_pow, norm_div, Complex.norm_natCast]; push_cast; rfl
  simp only [hterm] at hs'
  have hsum : Summable (fun j => ‖c j‖ * w j) := Complex.summable_ofReal.1 hs'.summable
  have hr := hsum.hasSum
  have heq : cSU q ((‖z‖ : ℝ) : ℂ) = ((∑' j, ‖c j‖ * w j : ℝ) : ℂ) :=
    hs'.unique (Complex.hasSum_ofReal.2 hr)
  obtain ⟨h1, h2, h3⟩ := sums_over_levels μ f hf w hw0 hlv c _ hs _ hr
  refine ⟨h2, h3, ?_⟩
  rw [h1, heq, ← ofReal_norm_eq_enorm, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hw0 j))]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | exact GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | (intros; apply GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNefStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_nonneg_of_nef_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → (∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | exact GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | (intros; apply GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInductionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  first | exact @GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | exact GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | (intros; apply GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurableStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitz_pointCount_one_class_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  first | (exact @GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (exact GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (intros; apply GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable  <;> assumption)
end

