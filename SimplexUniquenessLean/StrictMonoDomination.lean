import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.CDF

/-!
# Strict-monotone rigidity of stochastic domination

First step of the independent route described in Remark 1 of the paper.
If `μ` is stochastically dominated (`ν (Iic c) ≤ μ (Iic c)` for every `c`)
and one strictly increasing integrable moment agrees under `μ` and `ν`,
then `μ = ν`. No continuity of the distribution functions is assumed. The
layer-cake deficit of the pushed-forward measures vanishes, the identity
case is settled by positive- and negative-part tail representations, and
the general case reduces to it through the measurable embedding given by a
continuous strictly monotone test function.

Specializations to the identity (`measure_eq_of_iic_le_of_mean_eq`) and to
a single exponential moment (`measure_eq_of_iic_le_of_mgf_eq`) follow. The
latter is the single-parameter moment-generating rigidity used in the
paper.
-/

namespace SimplexUniqueness

open MeasureTheory Set Filter
open ProbabilityTheory
open scoped Topology

private theorem measure_eq_of_iic_le_of_mean_eq_aux
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ c : ℝ, ν (Iic c) ≤ μ (Iic c))
    (hμ : Integrable id μ) (hν : Integrable id ν)
    (heq : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    μ = ν := by
  let p : ℝ → ℝ := fun x => max x 0
  let n : ℝ → ℝ := fun x => max (-x) 0
  have hpμ : Integrable p μ := by
    refine (hμ.sup (integrable_const (0 : ℝ))).congr (ae_of_all μ fun x => ?_)
    rfl
  have hpν : Integrable p ν := by
    refine (hν.sup (integrable_const (0 : ℝ))).congr (ae_of_all ν fun x => ?_)
    rfl
  have hnμ : Integrable n μ := by
    refine (hμ.neg.sup (integrable_const (0 : ℝ))).congr (ae_of_all μ fun x => ?_)
    rfl
  have hnν : Integrable n ν := by
    refine (hν.neg.sup (integrable_const (0 : ℝ))).congr (ae_of_all ν fun x => ?_)
    rfl
  have hp_nonneg : 0 ≤ p := fun x => le_max_right x 0
  have hn_nonneg : 0 ≤ n := fun x => le_max_right (-x) 0
  have hpos_set (t : ℝ) (ht : 0 < t) : {x : ℝ | t < p x} = Ioi t := by
    ext x
    simp only [mem_setOf_eq, mem_Ioi]
    by_cases hx : x ≤ 0
    · rw [show p x = 0 by simp [p, max_eq_right hx]]
      constructor <;> intro h <;> linarith
    · rw [show p x = x by simp [p, max_eq_left (le_of_not_ge hx)]]
  have hneg_set (t : ℝ) (ht : 0 < t) : {x : ℝ | t ≤ n x} = Iic (-t) := by
    ext x
    simp only [mem_setOf_eq, mem_Iic]
    by_cases hx : -x ≤ 0
    · rw [show n x = 0 by simp [n, max_eq_right hx]]
      constructor <;> intro h <;> linarith
    · rw [show n x = -x by simp [n, max_eq_left (le_of_not_ge hx)]]
      constructor <;> intro h <;> linarith
  have hdecompμ : ∫ x, x ∂μ = (∫ x, p x ∂μ) - ∫ x, n x ∂μ := by
    rw [← integral_sub hpμ hnμ]
    apply integral_congr_ae
    filter_upwards [] with x
    change x = p x - n x
    by_cases hx : x ≤ 0
    · simp [p, n, max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]
    · simp [p, n, max_eq_left (le_of_not_ge hx), max_eq_right (by linarith : -x ≤ 0)]
  have hdecompν : ∫ x, x ∂ν = (∫ x, p x ∂ν) - ∫ x, n x ∂ν := by
    rw [← integral_sub hpν hnν]
    apply integral_congr_ae
    filter_upwards [] with x
    change x = p x - n x
    by_cases hx : x ≤ 0
    · simp [p, n, max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]
    · simp [p, n, max_eq_left (le_of_not_ge hx), max_eq_right (by linarith : -x ≤ 0)]
  have hlpμ :
      ∫⁻ x, ENNReal.ofReal (p x) ∂μ = ∫⁻ t in Ioi 0, μ (Ioi t) := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all μ hp_nonneg) hpμ.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change μ {a : ℝ | t < p a} = μ (Ioi t)
    rw [hpos_set t ht]
  have hlpν :
      ∫⁻ x, ENNReal.ofReal (p x) ∂ν = ∫⁻ t in Ioi 0, ν (Ioi t) := by
    rw [lintegral_eq_lintegral_meas_lt ν (ae_of_all ν hp_nonneg) hpν.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ν {a : ℝ | t < p a} = ν (Ioi t)
    rw [hpos_set t ht]
  have hlnμ :
      ∫⁻ x, ENNReal.ofReal (n x) ∂μ = ∫⁻ t in Ioi 0, μ (Iic (-t)) := by
    rw [lintegral_eq_lintegral_meas_le μ (ae_of_all μ hn_nonneg) hnμ.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change μ {a : ℝ | t ≤ n a} = μ (Iic (-t))
    rw [hneg_set t ht]
  have hlnν :
      ∫⁻ x, ENNReal.ofReal (n x) ∂ν = ∫⁻ t in Ioi 0, ν (Iic (-t)) := by
    rw [lintegral_eq_lintegral_meas_le ν (ae_of_all ν hn_nonneg) hnν.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ν {a : ℝ | t ≤ n a} = ν (Iic (-t))
    rw [hneg_set t ht]
  have htail (c : ℝ) : μ (Ioi c) ≤ ν (Ioi c) := by
    rw [← compl_Iic, measure_compl measurableSet_Iic (by finiteness),
      measure_compl measurableSet_Iic (by finiteness), measure_univ, measure_univ]
    exact tsub_le_tsub_left (hdom c) 1
  have hLP :
      (∫⁻ t in Ioi 0, μ (Ioi t)) ≤ ∫⁻ t in Ioi 0, ν (Ioi t) :=
    lintegral_mono fun t => htail t
  have hLN :
      (∫⁻ t in Ioi 0, ν (Iic (-t))) ≤ ∫⁻ t in Ioi 0, μ (Iic (-t)) :=
    lintegral_mono fun t => hdom (-t)
  have hLPμ_fin : (∫⁻ t in Ioi 0, μ (Ioi t)) ≠ ⊤ := by
    rw [← hlpμ]
    exact hpμ.lintegral_lt_top.ne
  have hLPν_fin : (∫⁻ t in Ioi 0, ν (Ioi t)) ≠ ⊤ := by
    rw [← hlpν]
    exact hpν.lintegral_lt_top.ne
  have hLNμ_fin : (∫⁻ t in Ioi 0, μ (Iic (-t))) ≠ ⊤ := by
    rw [← hlnμ]
    exact hnμ.lintegral_lt_top.ne
  have hLNν_fin : (∫⁻ t in Ioi 0, ν (Iic (-t))) ≠ ⊤ := by
    rw [← hlnν]
    exact hnν.lintegral_lt_top.ne
  have hp_tailμ :
      ∫ x, p x ∂μ = ENNReal.toReal (∫⁻ t in Ioi 0, μ (Ioi t)) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hp_nonneg) hpμ.aestronglyMeasurable,
      hlpμ]
  have hp_tailν :
      ∫ x, p x ∂ν = ENNReal.toReal (∫⁻ t in Ioi 0, ν (Ioi t)) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all ν hp_nonneg) hpν.aestronglyMeasurable,
      hlpν]
  have hn_tailμ :
      ∫ x, n x ∂μ = ENNReal.toReal (∫⁻ t in Ioi 0, μ (Iic (-t))) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hn_nonneg) hnμ.aestronglyMeasurable,
      hlnμ]
  have hn_tailν :
      ∫ x, n x ∂ν = ENNReal.toReal (∫⁻ t in Ioi 0, ν (Iic (-t))) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all ν hn_nonneg) hnν.aestronglyMeasurable,
      hlnν]
  have hp_le : (∫ x, p x ∂μ) ≤ ∫ x, p x ∂ν := by
    rw [hp_tailμ, hp_tailν]
    exact (ENNReal.toReal_le_toReal hLPμ_fin hLPν_fin).2 hLP
  have hn_le : (∫ x, n x ∂ν) ≤ ∫ x, n x ∂μ := by
    rw [hn_tailν, hn_tailμ]
    exact (ENNReal.toReal_le_toReal hLNν_fin hLNμ_fin).2 hLN
  have hp_eq : (∫ x, p x ∂μ) = ∫ x, p x ∂ν := by
    linarith [hdecompμ, hdecompν, heq]
  have hn_eq : (∫ x, n x ∂ν) = ∫ x, n x ∂μ := by
    linarith [hdecompμ, hdecompν, heq]
  have hLP_eq :
      (∫⁻ t in Ioi 0, μ (Ioi t)) = ∫⁻ t in Ioi 0, ν (Ioi t) := by
    apply (ENNReal.toReal_eq_toReal_iff' hLPμ_fin hLPν_fin).1
    rw [← hp_tailμ, ← hp_tailν, hp_eq]
  have hLN_eq :
      (∫⁻ t in Ioi 0, ν (Iic (-t))) = ∫⁻ t in Ioi 0, μ (Iic (-t)) := by
    apply (ENNReal.toReal_eq_toReal_iff' hLNν_fin hLNμ_fin).1
    rw [← hn_tailν, ← hn_tailμ, hn_eq]
  have hpos_measν : Measurable (fun t : ℝ => ν (Ioi t)) :=
    Antitone.measurable fun _ _ hab => measure_mono (Ioi_subset_Ioi hab)
  have hneg_measμ : Measurable (fun t : ℝ => μ (Iic (-t))) :=
    Antitone.measurable fun _ _ hab => measure_mono (Iic_subset_Iic.2 (neg_le_neg hab))
  have hpos_ae :
      (fun t : ℝ => μ (Ioi t)) =ᵐ[volume.restrict (Ioi 0)] fun t => ν (Ioi t) :=
    ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ htail) hLPμ_fin
      hpos_measν.aemeasurable hLP_eq.ge
  have hneg_ae :
      (fun t : ℝ => ν (Iic (-t))) =ᵐ[volume.restrict (Ioi 0)]
        fun t => μ (Iic (-t)) :=
    ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ fun t => hdom (-t)) hLNν_fin
      hneg_measμ.aemeasurable hLN_eq.ge
  have hpos_imp : ∀ᵐ c ∂volume, 0 < c → μ (Ioi c) = ν (Ioi c) := by
    simpa only [mem_Ioi] using (ae_restrict_iff' measurableSet_Ioi).1 hpos_ae
  have hneg_imp_t : ∀ᵐ t ∂volume, 0 < t → ν (Iic (-t)) = μ (Iic (-t)) := by
    simpa only [mem_Ioi] using (ae_restrict_iff' measurableSet_Ioi).1 hneg_ae
  have hneg_imp : ∀ᵐ c ∂volume, c < 0 → ν (Iic c) = μ (Iic c) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      hneg_imp_t
    simpa only [neg_pos, neg_neg] using h
  have hiic_ae : (fun c : ℝ => μ (Iic c)) =ᵐ[volume] fun c => ν (Iic c) := by
    filter_upwards [hpos_imp, hneg_imp, volume.ae_ne (0 : ℝ)] with c hpos hneg hc
    by_cases hcneg : c < 0
    · exact (hneg hcneg).symm
    · have hcpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hcneg) (Ne.symm hc)
      have htail_eq := hpos hcpos
      calc
        μ (Iic c) = μ ((Ioi c)ᶜ) := by rw [compl_Ioi]
        _ = μ univ - μ (Ioi c) := measure_compl measurableSet_Ioi (by finiteness)
        _ = ν univ - ν (Ioi c) := by rw [measure_univ, measure_univ, htail_eq]
        _ = ν ((Ioi c)ᶜ) := (measure_compl measurableSet_Ioi (by finiteness)).symm
        _ = ν (Iic c) := by rw [compl_Ioi]
  have hcdf_ae : (cdf μ : ℝ → ℝ) =ᵐ[volume] cdf ν := by
    filter_upwards [hiic_ae] with c hc
    rw [cdf_eq_real μ c, cdf_eq_real ν c]
    change (μ (Iic c)).toReal = (ν (Iic c)).toReal
    rw [hc]
  have hcdf : cdf μ = cdf ν := by
    apply StieltjesFunction.ext
    intro c
    have hdense : Dense {x : ℝ | cdf μ x = cdf ν x} := Measure.dense_of_ae hcdf_ae
    obtain ⟨u, -, hu, huc⟩ := hdense.exists_seq_strictAnti_tendsto c
    have hu_within : Tendsto u atTop (𝓝[Ici c] c) :=
      tendsto_nhdsWithin_iff.2
        ⟨huc, Eventually.of_forall fun k => show c ≤ u k from le_of_lt (hu k).1⟩
    have hlimμ : Tendsto (fun k => cdf μ (u k)) atTop (𝓝 (cdf μ c)) :=
      ((cdf μ).right_continuous c).tendsto.comp hu_within
    have hlimν : Tendsto (fun k => cdf ν (u k)) atTop (𝓝 (cdf ν c)) :=
      ((cdf ν).right_continuous c).tendsto.comp hu_within
    have hseq : (fun k => cdf μ (u k)) = fun k => cdf ν (u k) := by
      funext k
      exact (hu k).2
    rw [hseq] at hlimμ
    exact tendsto_nhds_unique hlimμ hlimν
  exact Measure.eq_of_cdf μ ν hcdf

/-- **Stochastic domination + equality of one strictly increasing moment forces
equality of laws.**  `μ` is the law of the dominated variable, `ν` of the
dominating one: `ν (Iic c) ≤ μ (Iic c)` for every `c`. -/
theorem measure_eq_of_iic_le_of_integral_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ c : ℝ, ν (Iic c) ≤ μ (Iic c))
    {f : ℝ → ℝ} (hmono : StrictMono f) (hcont : Continuous f)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (heq : ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  let μ' : Measure ℝ := μ.map f
  let ν' : Measure ℝ := ν.map f
  have hfemb : MeasurableEmbedding f := hcont.measurableEmbedding hmono.injective
  letI : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
  letI : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
  have hdom' : ∀ t : ℝ, ν' (Iic t) ≤ μ' (Iic t) := by
    intro t
    rw [show ν' (Iic t) = ν (f ⁻¹' Iic t) by
      simp only [ν', Measure.map_apply hcont.measurable measurableSet_Iic]]
    rw [show μ' (Iic t) = μ (f ⁻¹' Iic t) by
      simp only [μ', Measure.map_apply hcont.measurable measurableSet_Iic]]
    by_cases ht : ∃ c, f c = t
    · obtain ⟨c, rfl⟩ := ht
      have hpre : f ⁻¹' Iic (f c) = Iic c := by
        ext x
        exact hmono.le_iff_le
      rw [hpre]
      exact hdom c
    · by_cases hx : ∃ x, f x ≤ t
      · obtain ⟨x, hx⟩ := hx
        have hall : ∀ y, f y ≤ t := by
          intro y
          by_contra hy
          have hty : t < f y := lt_of_not_ge hy
          have hxy : x < y := hmono.lt_iff_lt.mp (lt_of_le_of_lt hx hty)
          obtain ⟨z, -, hz⟩ :=
            intermediate_value_Icc hxy.le hcont.continuousOn ⟨hx, hty.le⟩
          exact ht ⟨z, hz⟩
        have hpre : f ⁻¹' Iic t = univ := by
          ext y
          simp [hall y]
        rw [hpre]
        simp only [measure_univ]
        exact le_rfl
      · have hall : ∀ x, t < f x := by
          intro x
          exact lt_of_not_ge fun hx' => hx ⟨x, hx'⟩
        have hpre : f ⁻¹' Iic t = ∅ := by
          ext x
          simp [not_le.mpr (hall x)]
        rw [hpre]
        simp only [measure_empty, le_refl]
  have hμ' : Integrable id μ' := by
    exact hfemb.integrable_map_iff.2 (by simpa [Function.comp_def] using hμ)
  have hν' : Integrable id ν' := by
    exact hfemb.integrable_map_iff.2 (by simpa [Function.comp_def] using hν)
  have heq' : ∫ x, x ∂μ' = ∫ x, x ∂ν' := by
    rw [show (∫ x, x ∂μ') = ∫ x, f x ∂μ by
      simpa [μ', Function.comp_def] using hfemb.integral_map (μ := μ) id]
    rw [show (∫ x, x ∂ν') = ∫ x, f x ∂ν by
      simpa [ν', Function.comp_def] using hfemb.integral_map (μ := ν) id]
    exact heq
  have hmap : μ' = ν' :=
    measure_eq_of_iic_le_of_mean_eq_aux μ' ν' hdom' hμ' hν' heq'
  exact hfemb.map_injective hmap

/-- Specialization to the identity: domination + equal means. -/
theorem measure_eq_of_iic_le_of_mean_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ c : ℝ, ν (Iic c) ≤ μ (Iic c))
    (hμ : Integrable id μ) (hν : Integrable id ν)
    (heq : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    μ = ν :=
  measure_eq_of_iic_le_of_integral_eq μ ν hdom strictMono_id continuous_id hμ hν heq

/-- Specialization to an exponential moment at a single tilt `λ > 0`:
domination + equality of the MGF at one point forces equality of laws.
This is the every-SNR uniqueness lever. -/
theorem measure_eq_of_iic_le_of_mgf_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ c : ℝ, ν (Iic c) ≤ μ (Iic c))
    {l : ℝ} (hl : 0 < l)
    (hμ : Integrable (fun x => Real.exp (l * x)) μ)
    (hν : Integrable (fun x => Real.exp (l * x)) ν)
    (heq : ∫ x, Real.exp (l * x) ∂μ = ∫ x, Real.exp (l * x) ∂ν) :
    μ = ν := by
  refine measure_eq_of_iic_le_of_integral_eq μ ν hdom ?_ ?_ hμ hν heq
  · exact fun a b hab => Real.exp_lt_exp.mpr (by nlinarith)
  · exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

end SimplexUniqueness
