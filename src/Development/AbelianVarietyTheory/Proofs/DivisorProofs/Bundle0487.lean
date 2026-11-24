module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatBaseChangeIdeal

theorem toImage_std {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem ker_comap_flat {X Y V : Scheme.{0}} (h : X ⟶ Y) [QuasiCompact h] (g : V ⟶ Y) [Flat g] :
    h.ker.comap g = (pullback.fst g h).ker := by
  have := toImage_std h
  let m : pullback g h ⟶ pullback g h.imageι :=
    pullback.map g h g h.imageι (𝟙 _) h.toImage (𝟙 _) (by simp) (by simp)
  have hm1 : m ≫ pullback.fst g h.imageι = pullback.fst g h := by
    simp only [m, pullback.lift_fst, Category.comp_id]
  have hm2 : m ≫ pullback.snd g h.imageι = pullback.snd g h ≫ h.toImage := by
    simp only [m, pullback.lift_snd]
  have big : IsPullback (pullback.snd g h) (m ≫ pullback.fst g h.imageι)
      (h.toImage ≫ h.imageι) g := by
    rw [hm1, h.toImage_imageι]; exact (IsPullback.of_hasPullback g h).flip
  have hsq : IsPullback (pullback.snd g h) m h.toImage (pullback.snd g h.imageι) :=
    IsPullback.of_bot big hm2.symm (IsPullback.of_hasPullback g h.imageι).flip
  have hd : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback hsq
  rw [← hm1, Scheme.Hom.ker_comp, hd.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  congr 1
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

end GlobalTheory.FlatBaseChangeIdeal

namespace GlobalTheory.FlatBaseChangeIdeal

theorem map_comap_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π →
    ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  intro W W' V V' π g g' π' H hg hπ T
  have big : IsPullback (pullback.snd g' T.subschemeι) (pullback.fst g' T.subschemeι ≫ π')
      (T.subschemeι ≫ π) g :=
    (IsPullback.of_hasPullback g' T.subschemeι).flip.paste_vert H
  rw [Scheme.IdealSheafData.map, ker_comap_flat, Scheme.IdealSheafData.comap,
    Scheme.IdealSheafData.map_ker, ← big.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end GlobalTheory.FlatBaseChangeIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentity
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.SUVol.DensChart

open scoped Pointwise

theorem mem_grpBall_iff_norm {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) {ε : ℝ}
    (hε : 0 < ε) (g : H) :
    g ∈ grpBall H ε ↔ ‖(fun τ i j => ((((g : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) i j) - (fun (_ : ι) i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j)‖ < ε := by
  rw [pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem tanBall_eq_ball {ι : Type} [Fintype ι] {r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tanBall ι r ε = Metric.ball 0 ε := by
  ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem density_at_one : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  intro ι _ r H _ μ W _ _ _ _ _ lam _ Q D h a ρ hD hQ0 hDi hon hh ha0 hat hρ hμ
  set f : W → (ι → Fin r → Fin r → ℂ) := fun w τ i j =>
    ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf
  set one : ι → Fin r → Fin r → ℂ := fun _ i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hone
  have hf0 : f 0 = one := by simp [hf, hone, hQ0]
  have hD' : HasStrictFDerivAt f D 0 := hD
  obtain ⟨K, -, hK⟩ := (D : W →ₗ[ℝ] (ι → Fin r → Fin r → ℂ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hDi)
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hnorm : ∀ w, ‖w‖ ≤ K' * ‖D w‖ := by
    intro w
    have h1 := hK.le_mul_dist w 0
    simp only [dist_zero_right, map_zero] at h1
    calc ‖w‖ ≤ K * ‖D w‖ := h1
      _ ≤ K' * ‖D w‖ := by gcongr; linarith
  have hcw : ∀ c : ℝ, 0 ≤ c → ∀ w, c / K' * ‖w‖ ≤ c * ‖D w‖ := by
    intro c hc w
    calc c / K' * ‖w‖ ≤ c / K' * (K' * ‖D w‖) := by gcongr; exact hnorm w
      _ = c * ‖D w‖ := by field_simp
  have approx : ∀ κ : ℝ, 0 < κ → ∃ δ > 0, ∀ w : W, ‖w‖ < δ → ‖f w - one - D w‖ ≤ κ * ‖w‖ := by
    intro κ hκ
    have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD'.hasFDerivAt).def hκ
    obtain ⟨δ, hδ, hh'⟩ := Metric.eventually_nhds_iff.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hh' (y := w) (by rwa [dist_zero_right])
    simpa [hf0] using this
  set V : ℝ → ℝ≥0∞ := fun ε => lam (D ⁻¹' Metric.ball 0 ε) with hVdef
  set S : ℝ → Set W := fun ε => D ⁻¹' Metric.ball 0 ε ∩ Metric.ball 0 ρ with hSdef
  set F : ℝ → ℝ≥0∞ := fun ε => μ (Q '' S ε) with hFdef
  have hV0 : ∀ ε : ℝ, 0 < ε → V ε ≠ 0 := fun ε hε =>
    (Metric.isOpen_ball.preimage D.continuous).measure_ne_zero lam ⟨0, by simp [hε]⟩
  have hVt : ∀ ε : ℝ, V ε ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := lam) (x := 0) (r := K' * ε)).ne
      (measure_mono fun w hw => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ ≤ K' * ε := by gcongr
  have hVhom : ∀ t ε : ℝ, 0 < t → 0 < ε → V (t * ε) = ENNReal.ofReal (t ^ Module.finrank ℝ W) * V ε := by
    intro t ε ht _
    have hs : D ⁻¹' Metric.ball 0 (t * ε) = t • (D ⁻¹' Metric.ball 0 ε) := by
      ext w
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
      simp only [Set.mem_preimage, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht]
      rw [inv_mul_lt_iff₀ ht]
    simp only [hVdef]
    rw [hs, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]
  have hSmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurableSet_ball.preimage D.measurable).inter measurableSet_ball
  have hSeq : ∀ ε : ℝ, ε < ρ / K' → S ε = D ⁻¹' Metric.ball 0 ε := by
    intro ε hε
    refine Set.inter_eq_left.2 fun w hw => ?_
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ < K' * (ρ / K') := by gcongr; linarith [norm_nonneg (D w)]
      _ = ρ := by field_simp
  have hFint : ∀ ε : ℝ, F ε = ∫⁻ w in S ε, h w ∂lam := fun ε =>
    hμ (S ε) (hSmeas ε) Set.inter_subset_right
  have hF : Tendsto (fun ε => F ε / V ε) (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨a', hb', ha'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (lt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : a' * V ε ≤ F ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc b < a' := hb'
        _ = a' * V ε / V ε := (ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)).symm
        _ ≤ F ε / V ε := ENNReal.div_le_div_right hle _
    · obtain ⟨a', ha', hb'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (gt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : F ε ≤ a' * V ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc F ε / V ε ≤ a' * V ε / V ε := ENNReal.div_le_div_right hle _
        _ = a' := ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)
        _ < b := hb'
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (t⁻¹ * ε) ≤ μ (grpBall H ε) ∧ μ (grpBall H ε) ≤ F (t * ε) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    obtain ⟨δ1, hδ1, H1⟩ := approx ((t - 1) / K') (div_pos (by linarith) hK'0)
    obtain ⟨δ2, hδ2, H2⟩ := approx ((1 - t⁻¹) / K') (div_pos (by linarith) hK'0)
    obtain ⟨ε0, hε0, hon0⟩ := hon (min ρ δ2) (lt_min hρ hδ2)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hε0 (lt_min (div_pos hδ1 hK'0) (div_pos hρ hK'0)))]
      with ε hε
    obtain ⟨hεp, hε1⟩ := hε
    simp only [lt_min_iff] at hε1
    obtain ⟨hεe, hεd, hερ⟩ := hε1
    constructor
    · refine measure_mono ?_
      rintro _ ⟨w, ⟨hw1, -⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff] at hw1
      rw [mem_grpBall_iff_norm H hεp]
      change ‖f w - one‖ < ε
      have hDw : ‖D w‖ < ε := by
        calc ‖D w‖ < t⁻¹ * ε := hw1
          _ < 1 * ε := by gcongr
          _ = ε := one_mul ε
      have hw : ‖w‖ < δ1 := by
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δ1 / K') := by gcongr; linarith
          _ = δ1 := by field_simp
      have e1 := H1 w hw
      have e2 := hcw (t - 1) (by linarith) w
      have e3 : ‖f w - one‖ ≤ ‖D w‖ + ‖f w - one - D w‖ := by
        calc ‖f w - one‖ = ‖D w + (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have e4 : t * ‖D w‖ < ε := by
        calc t * ‖D w‖ < t * (t⁻¹ * ε) := by gcongr
          _ = ε := by field_simp
      nlinarith
    · refine measure_mono fun g hg => ?_
      have hg0 : g ∈ grpBall H ε0 := fun τ i j => (hg τ i j).trans hεe
      obtain ⟨w, hw, rfl⟩ := hon0 g hg0
      rw [lt_min_iff] at hw
      rw [mem_grpBall_iff_norm H hεp] at hg
      change ‖f w - one‖ < ε at hg
      refine ⟨w, ⟨?_, mem_ball_zero_iff.2 hw.1⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have e1 := H2 w hw.2
      have e2 := hcw (1 - t⁻¹) (by linarith) w
      have e3 : ‖D w‖ ≤ ‖f w - one‖ + ‖f w - one - D w‖ := by
        calc ‖D w‖ = ‖(f w - one) - (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e4 : t⁻¹ * ‖D w‖ < ε := by linarith
      calc ‖D w‖ = t * (t⁻¹ * ‖D w‖) := by field_simp
        _ < t * ε := by gcongr
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze (F := F) (V := V)
    (A := fun ε => μ (grpBall H ε)) (n := Module.finrank ℝ W) hat hVhom hF hA
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  simp only [hVdef]
  rw [tanBall_eq_ball hε, Measure.map_apply D.measurable measurableSet_ball]

end GlobalTheory.SUVol.DensChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquation
section
open NumberField MeasureTheory

namespace GlobalTheory

theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticRepresentationHolds
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticRepresentation_holds : GlobalTheory.Published.MetaplecticRepresentation := by
  intro ι _ _
  obtain ⟨G, iG, tG, tgG, pr, om, omS, φ, hcov, hsurj, ⟨ε, hε1, hker, hεf⟩, hcont, hint, hcompat, hφ, hjc,
    hgauss⟩ := _root_.GlobalTheory.metaplectic_euclidean_gaussian ι
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.schwartz_L2_euclidean_identification ι
  have hes : ∀ (ψ : Sch ι) (x : ι → ℝ), e.symm ψ x = ψ (WithLp.toLp 2 x) := by
    intro ψ x
    simpa using (he (e.symm ψ) (WithLp.toLp 2 x)).symm
  have inj : ∀ ψ₁ ψ₂ : Sch ι, ψ₁.toLp 2 = ψ₂.toLp 2 → ψ₁ = ψ₂ := fun ψ₁ ψ₂ h =>
    SchwartzMap.injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume h
  let Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))) :=
    { toFun := fun g => ((u.symm.toContinuousLinearEquiv : L2 ι →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))).comp
          ((om g).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι)).comp
          (u.toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] L2 ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hΩ : ∀ g f, Ω g f = u.symm (om g (u f)) := fun g f => rfl
  let ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ)) :=
    { toFun := fun g => ((e.symm : Sch ι →L[ℂ] 𝓢(ι → ℝ, ℂ)).comp (omS g)).comp (e : 𝓢(ι → ℝ, ℂ) →L[ℂ] Sch ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hω : ∀ g f, ω g f = e.symm (omS g (e f)) := fun g f => rfl
  have heω : ∀ g f, e (ω g f) = omS g (e f) := fun g f => by rw [hω, e.apply_symm_apply]
  have hφ₀ : ∀ x : ι → ℝ, e.symm φ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
    intro x
    rw [hes, hφ]
  refine ⟨G, iG, tG, tgG, pr, Ω, ω, e.symm φ, hsurj, hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ₀, ?_, ?_⟩
  · have hk : (pr.ker : Set G) = {1, ε} := by
      ext g
      simp [MonoidHom.mem_ker, hker]
    rw [← SetLike.coe_sort_coe, hk, Nat.card_coe_set_eq, Set.ncard_pair hε1.symm]
  · intro g f
    rw [hΩ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · intro f
    exact u.symm.continuous.comp (hcont (u f))
  · intro g ψ
    rw [hΩ, LinearIsometryEquiv.symm_apply_eq, hu, hu, heω, hcompat]
  · have : (fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) =
        (fun y : Sch ι => e.symm y) ∘ (fun y : G × Sch ι => omS y.1 y.2) ∘ (fun x : G × 𝓢(ι → ℝ, ℂ) => (x.1, e x.2)) := by
      funext x; rfl
    rw [this]
    exact e.symm.continuous.comp (hjc.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro g w ψ
    apply e.injective
    apply inj
    rw [heω, ← hcompat]
    rw [_root_.GlobalTheory.Proof.schrodinger_models_agree ι w ψ (e ψ) (e (GlobalTheory.Published.Metaplectic.rho w ψ)) (he ψ) (he _)]
    rw [hint, hcompat]
    rw [_root_.GlobalTheory.Proof.schrodinger_models_agree ι (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ) (e (ω g ψ))
      (e (GlobalTheory.Published.Metaplectic.rho (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ))) (he _) (he _)]
    rw [heω]
    congr 2
    simp [GlobalTheory.Published.Metaplectic.act, Sum.elim_comp_inl_inr]
  · intro g hg1 hg ψ
    have hgε : g = ε := ((hker g).1 hg1).resolve_left hg
    subst hgε
    have h1 : omS g (e ψ) = -(e ψ) := by
      apply inj
      have hn := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).map_neg (e ψ)
      simp only [SchwartzMap.toLpCLM_apply] at hn
      rw [← hcompat, hεf, hn]
    rw [hω, h1, map_neg, e.symm_apply_apply]
  · intro g
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨-, hsymm⟩ := _root_.GlobalTheory.SympBlocks.det_ne_zero_and_isSymm ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2
    have hsieg := GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 hdet hsymm
    have hωx : ∀ x : ι → ℝ, ω g (e.symm φ) x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ
        (-((Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) *
          (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))⁻¹)) *ᵥ
          fun i => (x i : ℂ))) := by
      intro x
      rw [hω, e.apply_symm_apply, hes, hcx]
    simp only [hωx, hφ₀]
    exact _root_.GlobalTheory.vacuum_coef_sq ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) hdet hsieg c hc
  · intro g horth
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨hP, hq⟩ := GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 horth hdet
    refine ⟨c, by rw [hP]; exact hc, ?_⟩
    ext x
    rw [hω, e.apply_symm_apply, hes, hcx, SchwartzMap.smul_apply, smul_eq_mul, hφ₀]
    simp only [PiLp.toLp_apply]
    rw [hq x]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlat
section
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem mulP_flat : ∀ (p : ℕ) (R : Type) [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
    RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) with hB₀
  let f : G.A n →ₐ[R] B₀ := AlgHom.codRestrict (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B₀
    (fun a => by
      show G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ[R] 1
      exact G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Test.mulP_injective G n (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨e, he⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨e, Subtype.ext he⟩
  have h1 : RingHom.Flat (algebraMap B₀ (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h2 : RingHom.Flat (f : G.A n →+* B₀) := RingHom.Flat.of_bijective hf
  have h3 := RingHom.Flat.comp h2 h1
  convert h3 using 1
  exact RingHom.ext fun a => rfl
end GlobalTheory.PDivGroup
end

