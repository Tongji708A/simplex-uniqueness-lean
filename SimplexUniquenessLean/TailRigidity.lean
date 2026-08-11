/-
Module 2 — Tail rigidity: the equality case of the stochastic-domination
theorem.

Paper reference: Lemma 6.2.  If R is an m×m correlation matrix with
R - J/m ⪰ 0 and the centered Gaussian with covariance R attains
P{max_i X_i ≤ c} = Φ(c)^m for EVERY c, then R = I.

Proof route (each step is a standalone lemma below):
  (a) one-sided union bound with a single pair subtracted:
      P{max > c} ≤ m·q(c) - p_ρ(c)  for the pair (i,j), ρ = R i j;
  (b) second-order Bonferroni for the iid side:
      Φ(c)^m ≤ 1 - m·q(c) + C(m,2)·q(c)²;
  (c) bivariate lower bound on the square [c, c+1/c]²:
      p_ρ(c) ≥ (c⁻²/(2π√(1-ρ²))) · exp(-(c+c⁻¹)²/(1+ρ) - ρ/(2(1-ρ²)c²))
      for 0 < ρ < 1, and p_1(c) = q(c) in the degenerate case;
  (d) q(c) ≤ φ(c)/c  for c > 0, hence p_ρ(c)/q(c)² → ∞ for every 0 < ρ ≤ 1;
  (e) (a)-(d) contradict equality at large c unless all off-diagonals are ≤ 0;
      then 0 ≤ 1ᵀ(R - J/m)1 = 2·Σ_{i<j} R i j forces R = 1.

Statement vocabulary is that of the dependency
`weak-simplex-conjecture-lean` (namespace `WeakSimplex`):
`multivariateGaussian 0 R`, `lowerOrthant c`, `IsWeakSimplexCov`.
-/
import WeakSimplexConjectureLean

namespace SimplexUniqueness

open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators InnerProductSpace

/-- (d) Standard normal upper-tail bound `q(c) ≤ φ(c)/c` for `c > 0`. -/
theorem gaussianReal_tail_le_pdf_div
    {c : ℝ} (hc : 0 < c) :
    ((gaussianReal 0 1) (Ioi c)).toReal ≤ Real.exp (-c ^ 2 / 2) / (c * Real.sqrt (2 * Real.pi)) := by
  have hsymm :
      (gaussianReal 0 1) (Ioi c) = (gaussianReal 0 1) (Iic (-c)) := by
    have hmap := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    have hpre : (fun x : ℝ => -x) ⁻¹' Ioi c = Iio (-c) := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_Iio]
      constructor <;> intro hx <;> linarith
    calc
      (gaussianReal 0 1) (Ioi c) =
          Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) (Ioi c) := by
            rw [hmap]
            norm_num
      _ = (gaussianReal 0 1) ((fun x : ℝ => -x) ⁻¹' Ioi c) := by
            rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
      _ = (gaussianReal 0 1) (Iio (-c)) := by rw [hpre]
      _ = (gaussianReal 0 1) (Iic (-c)) := by
            letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
            exact measure_congr Iio_ae_eq_Iic
  rw [hsymm, ← normalCDF_eq_measure_Iic]
  rw [ENNReal.toReal_ofReal (normalCDF_pos (-c)).le]
  calc
    normalCDF (-c) ≤ normalPDF c / c := mills_upper c hc
    _ = Real.exp (-c ^ 2 / 2) / (c * Real.sqrt (2 * Real.pi)) := by
      rw [normalPDF]
      norm_num [gaussianPDFReal]
      field_simp

/-- The `2 × 2` correlation matrix with off-diagonal entry `ρ`. -/
def pairCorrelation (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, ρ; ρ, 1]

private lemma pairCorrelation_posDef {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (pairCorrelation ρ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pairCorrelation, Matrix.conjTranspose_apply]
  · intro x hx
    have hcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    simp [pairCorrelation, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hsquares : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      rcases hcoord with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_pos_of_ne_zero h1]
    have hone : 0 < 1 - ρ := sub_pos.mpr hρ1
    have hsum : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
    nlinarith

private lemma pairCorrelation_det (ρ : ℝ) :
    (pairCorrelation ρ).det = 1 - ρ ^ 2 := by
  simp [pairCorrelation, Matrix.det_fin_two]
  ring

private lemma pairCorrelation_inv {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 < ρ) :
    (pairCorrelation ρ)⁻¹ =
      (1 - ρ ^ 2)⁻¹ • !![1, -ρ; -ρ, 1] := by
  rw [Matrix.inv_def, pairCorrelation_det]
  have hdet : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  rw [Ring.inverse_eq_inv]
  congr 1
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairCorrelation]

private lemma pairCorrelation_qform_inv_sub_one
    {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 < ρ) (x : Coord 2) :
    qform ((pairCorrelation ρ)⁻¹ - 1) x =
      (ρ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) - 2 * ρ * x 0 * x 1) / (1 - ρ ^ 2) := by
  rw [pairCorrelation_inv hρ1 hρ0, qform_eq_dotProduct]
  have hdet : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.one_fin_two]
  field_simp
  ring

private noncomputable def stdDensity2 (x : Coord 2) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

private lemma measurable_stdDensity2 : Measurable stdDensity2 := by
  unfold stdDensity2
  fun_prop

private lemma stdGaussian_eq_volume_withDensity2 :
    stdGaussian (Coord 2) =
      (volume : Measure (Coord 2)).withDensity stdDensity2 := by
  rw [← map_pi_eq_stdGaussian,
    WeakSimplex.Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity]
  have hmap :=
    WeakSimplex.Vendor.StatLean.AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      (volume : Measure (Fin 2 → ℝ)) (WithLp.toLp 2) (by fun_prop)
      stdDensity2 measurable_stdDensity2
  rw [(PiLp.volume_preserving_toLp (Fin 2)).map_eq] at hmap
  exact hmap.symm.trans (by rfl)

private lemma multivariateGaussian_pair_eq_volume_withDensity
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    multivariateGaussian (0 : Coord 2) (pairCorrelation ρ) =
      (volume : Measure (Coord 2)).withDensity
        (fun x => stdDensity2 x * ENNReal.ofReal
          (gaussianDensityRatio (pairCorrelation ρ) x)) := by
  rw [multivariateGaussian_eq_stdGaussian_withDensity
    (pairCorrelation_posDef hρ0 hρ1), stdGaussian_eq_volume_withDensity2]
  have hrho : Measurable (fun x : Coord 2 => ENNReal.ofReal
      (gaussianDensityRatio (pairCorrelation ρ) x)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianDensityRatio qform matrixMul
    fun_prop
  exact (withDensity_mul (volume : Measure (Coord 2)) measurable_stdDensity2 hrho).symm

private lemma toReal_stdDensity2 (x : Coord 2) :
    (stdDensity2 x).toReal =
      (2 * Real.pi)⁻¹ * Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) := by
  unfold stdDensity2
  rw [ENNReal.toReal_prod]
  simp [Fin.prod_univ_two, toReal_gaussianPDF, gaussianPDFReal]
  rw [show (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-x 0 ^ 2 / 2) *
      ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-x 1 ^ 2 / 2)) =
      ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) ^ 2 *
        (Real.exp (-x 0 ^ 2 / 2) * Real.exp (-x 1 ^ 2 / 2)) by ring]
  rw [← Real.exp_add]
  congr 1
  rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt Real.pi_nonneg,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- A boundary-insensitive representative of `[c, c + 1/c]²`. -/
private def pairSquare (c : ℝ) : Set (Coord 2) :=
  {x | x 0 ∈ Ioc c (c + c⁻¹) ∧ x 1 ∈ Ioc c (c + c⁻¹)}

private lemma measurableSet_pairSquare (c : ℝ) : MeasurableSet (pairSquare c) := by
  unfold pairSquare
  exact (measurableSet_Ioc.preimage
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable).inter
    (measurableSet_Ioc.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).measurable)

private lemma volume_pairSquare {c : ℝ} (_hc : 0 < c) :
    volume (pairSquare c) = ENNReal.ofReal c⁻¹ ^ 2 := by
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).map_eq,
    Measure.map_apply (by fun_prop) (measurableSet_pairSquare c)]
  have hpre : (WithLp.toLp 2) ⁻¹' pairSquare c =
      Set.univ.pi (fun _ : Fin 2 => Ioc c (c + c⁻¹)) := by
    ext x
    simp [pairSquare]
  rw [hpre, Real.volume_pi_Ioc]
  simp

private lemma pairSquare_subset_pairTail {c : ℝ} (_hc : 0 < c) :
    pairSquare c ⊆ {x : Coord 2 | c < x 0 ∧ c < x 1} := by
  intro x hx
  exact ⟨hx.1.1, hx.2.1⟩

private noncomputable def pairDensityLower (ρ c : ℝ) : ℝ :=
  (2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ *
    Real.exp (-(c + c⁻¹) ^ 2 / (1 + ρ) -
      ρ / (2 * (1 - ρ ^ 2) * c ^ 2))

private lemma pairDensityLower_pos {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < pairDensityLower ρ c := by
  unfold pairDensityLower
  have hdet : 0 < 1 - ρ ^ 2 := by nlinarith
  positivity

private lemma pair_integrand_lower_on_square
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {c : ℝ} (hc : 1 ≤ c)
    {x : Coord 2} (hx : x ∈ pairSquare c) :
    ENNReal.ofReal (pairDensityLower ρ c) ≤
      stdDensity2 x * ENNReal.ofReal
        (gaussianDensityRatio (pairCorrelation ρ) x) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hd0 : 0 ≤ c + c⁻¹ := add_nonneg hc0.le hci
  have hx0 : 0 ≤ x 0 := le_trans hc0.le hx.1.1.le
  have hx1 : 0 ≤ x 1 := le_trans hc0.le hx.2.1.le
  have hx0sq : x 0 ^ 2 ≤ (c + c⁻¹) ^ 2 :=
    (sq_le_sq₀ hx0 hd0).2 hx.1.2
  have hx1sq : x 1 ^ 2 ≤ (c + c⁻¹) ^ 2 :=
    (sq_le_sq₀ hx1 hd0).2 hx.2.2
  have hdiffabs : |x 0 - x 1| ≤ c⁻¹ := by
    rw [abs_le]
    constructor <;> linarith [hx.1.1.le, hx.1.2, hx.2.1.le, hx.2.2]
  have hdiff : (x 0 - x 1) ^ 2 ≤ (c⁻¹) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hci] using hdiffabs
  have hdet : 0 < 1 - ρ ^ 2 := by nlinarith
  have hplus : 0 < 1 + ρ := by linarith
  have hqform :
      (x 0 ^ 2 + x 1 ^ 2 - 2 * ρ * x 0 * x 1) /
          (2 * (1 - ρ ^ 2)) ≤
        (c + c⁻¹) ^ 2 / (1 + ρ) +
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2) := by
    have hid :
        (x 0 ^ 2 + x 1 ^ 2 - 2 * ρ * x 0 * x 1) /
            (2 * (1 - ρ ^ 2)) =
          (x 0 ^ 2 + x 1 ^ 2) / (2 * (1 + ρ)) +
            ρ * (x 0 - x 1) ^ 2 / (2 * (1 - ρ ^ 2)) := by
      field_simp
      ring
    rw [hid]
    have hfirst :
        (x 0 ^ 2 + x 1 ^ 2) / (2 * (1 + ρ)) ≤
          (c + c⁻¹) ^ 2 / (1 + ρ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + ρ))).2
      rw [show (c + c⁻¹) ^ 2 / (1 + ρ) * (2 * (1 + ρ)) =
          2 * (c + c⁻¹) ^ 2 by field_simp]
      nlinarith
    have hsecond :
        ρ * (x 0 - x 1) ^ 2 / (2 * (1 - ρ ^ 2)) ≤
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2) := by
      have hcne : c ≠ 0 := hc0.ne'
      rw [show ρ / (2 * (1 - ρ ^ 2) * c ^ 2) =
          ρ * (c⁻¹) ^ 2 / (2 * (1 - ρ ^ 2)) by field_simp]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff hρ0.le) (by positivity)
    linarith
  have hratio_nonneg :
      0 ≤ gaussianDensityRatio (pairCorrelation ρ) x := by
    unfold gaussianDensityRatio
    have hsqrt : 0 < Real.sqrt (pairCorrelation ρ).det := by
      rw [pairCorrelation_det]
      positivity
    positivity
  rw [← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by
      unfold stdDensity2
      exact ENNReal.prod_ne_top fun _ _ => gaussianPDF_ne_top)
      ENNReal.ofReal_ne_top)]
  rw [ENNReal.toReal_ofReal (pairDensityLower_pos hρ0 hρ1).le,
    ENNReal.toReal_mul, toReal_stdDensity2,
    ENNReal.toReal_ofReal hratio_nonneg]
  unfold pairDensityLower gaussianDensityRatio
  rw [pairCorrelation_det, pairCorrelation_qform_inv_sub_one hρ1 hρ0]
  have hsqrt : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.2 hdet
  have hconst : 0 < (2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ := by positivity
  have hexp :
      Real.exp (-(c + c⁻¹) ^ 2 / (1 + ρ) -
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2)) ≤
        Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) *
          Real.exp (-((ρ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) -
            2 * ρ * x 0 * x 1) / (1 - ρ ^ 2)) / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have halgebra :
        -(x 0 ^ 2 + x 1 ^ 2) / 2 -
            ((ρ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) -
              2 * ρ * x 0 * x 1) / (1 - ρ ^ 2)) / 2 =
          -(x 0 ^ 2 + x 1 ^ 2 - 2 * ρ * x 0 * x 1) /
            (2 * (1 - ρ ^ 2)) := by
      field_simp
      ring
    rw [show -(x 0 ^ 2 + x 1 ^ 2) / 2 +
        -((ρ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) -
          2 * ρ * x 0 * x 1) / (1 - ρ ^ 2)) / 2 =
        -(x 0 ^ 2 + x 1 ^ 2) / 2 -
          ((ρ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) -
            2 * ρ * x 0 * x 1) / (1 - ρ ^ 2)) / 2 by ring,
      halgebra]
    calc
      -(c + c⁻¹) ^ 2 / (1 + ρ) -
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2) =
        -((c + c⁻¹) ^ 2 / (1 + ρ) +
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2)) := by ring
      _ ≤ -((x 0 ^ 2 + x 1 ^ 2 - 2 * ρ * x 0 * x 1) /
          (2 * (1 - ρ ^ 2))) := neg_le_neg hqform
      _ = -(x 0 ^ 2 + x 1 ^ 2 - 2 * ρ * x 0 * x 1) /
          (2 * (1 - ρ ^ 2)) := by ring
  have hfactor :
      (2 * Real.pi)⁻¹ * (Real.sqrt (1 - ρ ^ 2))⁻¹ =
        (2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ := by ring
  rw [← hfactor]
  nlinarith [mul_le_mul_of_nonneg_left hexp hconst.le]

/-- (c) Direct lower bound for the upper-pair tail of the centered Gaussian with
`2 × 2` correlation matrix `pairCorrelation ρ`.  The proof integrates the explicit density on
the square `(c, c + 1/c]²`, which differs from `[c, c + 1/c]²` only on a null boundary. -/
theorem bivariate_pair_tail_lower_bound
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {c : ℝ} (hc : 1 ≤ c) :
    (c ^ 2 * 2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ *
          Real.exp (-(c + c⁻¹) ^ 2 / (1 + ρ) -
            ρ / (2 * (1 - ρ ^ 2) * c ^ 2)) ≤
      ((multivariateGaussian (0 : Coord 2) (pairCorrelation ρ))
        {x | c < x 0 ∧ c < x 1}).toReal := by
  let tail : Set (Coord 2) := {x | c < x 0 ∧ c < x 1}
  let target : ℝ :=
    (c ^ 2 * 2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ *
      Real.exp (-(c + c⁻¹) ^ 2 / (1 + ρ) -
        ρ / (2 * (1 - ρ ^ 2) * c ^ 2))
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hdet : 0 < 1 - ρ ^ 2 := by nlinarith
  have htarget : 0 ≤ target := by
    dsimp [target]
    positivity
  have htail_meas : MeasurableSet tail := by
    dsimp [tail]
    exact (measurableSet_Ioi.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable).inter
      (measurableSet_Ioi.preimage
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).measurable)
  have hrho_meas : Measurable (fun x : Coord 2 => ENNReal.ofReal
      (gaussianDensityRatio (pairCorrelation ρ) x)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianDensityRatio qform matrixMul
    fun_prop
  have hintegrand_meas : Measurable (fun x : Coord 2 =>
      stdDensity2 x * ENNReal.ofReal
        (gaussianDensityRatio (pairCorrelation ρ) x)) :=
    measurable_stdDensity2.mul hrho_meas
  have hmass :
      ENNReal.ofReal target =
        ENNReal.ofReal (pairDensityLower ρ c) * volume (pairSquare c) := by
    rw [volume_pairSquare hc0, ← ENNReal.ofReal_pow (inv_nonneg.mpr hc0.le) 2,
      ← ENNReal.ofReal_mul (pairDensityLower_pos hρ0 hρ1).le]
    congr 1
    dsimp [target, pairDensityLower]
    have hsqrt : Real.sqrt (1 - ρ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hdet).ne'
    field_simp [hc0.ne', Real.pi_ne_zero, hsqrt]
  have hlower_square :
      ENNReal.ofReal (pairDensityLower ρ c) * volume (pairSquare c) ≤
        ∫⁻ x in pairSquare c,
          stdDensity2 x * ENNReal.ofReal
            (gaussianDensityRatio (pairCorrelation ρ) x) ∂volume := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono hintegrand_meas fun x hx =>
      pair_integrand_lower_on_square hρ0 hρ1 hc hx
  have hsquare_measure :
      (∫⁻ x in pairSquare c,
          stdDensity2 x * ENNReal.ofReal
            (gaussianDensityRatio (pairCorrelation ρ) x) ∂volume) =
        (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ)) (pairSquare c) := by
    rw [multivariateGaussian_pair_eq_volume_withDensity hρ0 hρ1,
      withDensity_apply _ (measurableSet_pairSquare c)]
  have hENN : ENNReal.ofReal target ≤
      (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ)) tail := by
    rw [hmass]
    calc
      ENNReal.ofReal (pairDensityLower ρ c) * volume (pairSquare c) ≤
          ∫⁻ x in pairSquare c,
            stdDensity2 x * ENNReal.ofReal
              (gaussianDensityRatio (pairCorrelation ρ) x) ∂volume := hlower_square
      _ = (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ))
          (pairSquare c) := hsquare_measure
      _ ≤ (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ)) tail :=
        measure_mono (pairSquare_subset_pairTail hc0)
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (measure_ne_top (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ)) tail)).2 hENN
  rw [ENNReal.toReal_ofReal htarget] at hreal
  exact hreal

/-- (a) A finite union bound sharpened by subtracting one selected pair intersection. -/
private lemma measure_iUnion_add_inter_le_sum
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (μ : Measure α) (A : ι → Set α) (hA : ∀ k, MeasurableSet (A k))
    {i j : ι} (hij : i ≠ j) :
    μ (⋃ k, A k) + μ (A i ∩ A j) ≤ ∑ k, μ (A k) := by
  let rest : Finset ι := (Finset.univ.erase i).erase j
  have hjrest : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hcover : (⋃ k, A k) ⊆ (A i ∪ A j) ∪ ⋃ k ∈ rest, A k := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    by_cases hki : k = i
    · exact Or.inl (Or.inl (hki ▸ hk))
    by_cases hkj : k = j
    · exact Or.inl (Or.inr (hkj ▸ hk))
    · exact Or.inr (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨by
        simp [rest, hki, hkj], hk⟩⟩)
  calc
    μ (⋃ k, A k) + μ (A i ∩ A j) ≤
        (μ (A i ∪ A j) + μ (⋃ k ∈ rest, A k)) + μ (A i ∩ A j) := by
      gcongr
      exact (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ (μ (A i ∪ A j) + ∑ k ∈ rest, μ (A k)) + μ (A i ∩ A j) := by
      gcongr
      exact measure_biUnion_finset_le rest A
    _ = ∑ k, μ (A k) := by
      rw [show (μ (A i ∪ A j) + ∑ k ∈ rest, μ (A k)) + μ (A i ∩ A j) =
          (μ (A i ∪ A j) + μ (A i ∩ A j)) + ∑ k ∈ rest, μ (A k) by ac_rfl,
        measure_union_add_inter (A i) (hA j)]
      rw [show ∑ k, μ (A k) =
          ((∑ k ∈ rest, μ (A k)) + μ (A j)) + μ (A i) by
        rw [Finset.sum_erase_add (Finset.univ.erase i) (fun k => μ (A k)) hjrest,
          Finset.sum_erase_add Finset.univ (fun k => μ (A k)) (Finset.mem_univ i)]]
      ac_rfl

private lemma toReal_measure_iUnion_add_inter_le_sum
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (μ : Measure α) [IsFiniteMeasure μ] (A : ι → Set α)
    (hA : ∀ k, MeasurableSet (A k)) {i j : ι} (hij : i ≠ j) :
    (μ (⋃ k, A k)).toReal + (μ (A i ∩ A j)).toReal ≤
      ∑ k, (μ (A k)).toReal := by
  have h := measure_iUnion_add_inter_le_sum μ A hA hij
  rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ← ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]
  exact ENNReal.toReal_mono
    (ENNReal.sum_ne_top.2 fun k _ => measure_ne_top μ (A k)) h

/-- (b) The second-order Bonferroni polynomial bound for equal marginal tail `q`. -/
private lemma one_sub_pow_le_second_order (m : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ m ≤ 1 - (m : ℝ) * q + (m.choose 2 : ℕ) * q ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      have hmul := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hq1)
      calc
        (1 - q) ^ m * (1 - q) ≤
            (1 - (m : ℝ) * q + (m.choose 2 : ℕ) * q ^ 2) * (1 - q) := hmul
        _ ≤ 1 - ((m + 1 : ℕ) : ℝ) * q + ((m + 1).choose 2 : ℕ) * q ^ 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          push_cast
          nlinarith [sq_nonneg q,
            mul_nonneg (Nat.cast_nonneg (α := ℝ) (m.choose 2))
              (mul_nonneg (sq_nonneg q) hq0)]

private noncomputable def pairProjectionCLM {m : ℕ} (i j : Fin m) :
    Coord m →L[ℝ] Coord 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      EuclideanSpace.proj (𝕜 := ℝ) i,
      EuclideanSpace.proj (𝕜 := ℝ) j])

@[simp] private lemma pairProjectionCLM_apply_zero
    {m : ℕ} (i j : Fin m) (x : Coord m) :
    pairProjectionCLM i j x 0 = x i := by
  rfl

@[simp] private lemma pairProjectionCLM_apply_one
    {m : ℕ} (i j : Fin m) (x : Coord m) :
    pairProjectionCLM i j x 1 = x j := by
  rfl

private lemma map_pairProjectionCLM_multivariateGaussian
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (i j : Fin m) (hpair : (pairCorrelation (R i j)).PosDef) :
    Measure.map (pairProjectionCLM i j)
        (multivariateGaussian (0 : Coord m) R) =
      multivariateGaussian (0 : Coord 2) (pairCorrelation (R i j)) := by
  let μp : Measure (Coord 2) := Measure.map (pairProjectionCLM i j)
    (multivariateGaussian (0 : Coord m) R)
  let νp : Measure (Coord 2) :=
    multivariateGaussian (0 : Coord 2) (pairCorrelation (R i j))
  change μp = νp
  haveI : IsGaussian μp := by dsimp [μp]; infer_instance
  haveI : IsGaussian νp := by dsimp [νp]; infer_instance
  apply IsGaussian.ext
  · dsimp [μp, νp]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian]
    simp
  · dsimp [μp, νp]
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      fun a b => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have ha : (fun u ↦ ⟪(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis a, u⟫_ℝ) ∘
          pairProjectionCLM i j = fun u => u (if a = 0 then i else j) := by
        ext u
        fin_cases a <;> simp [PiLp.inner_apply]
      have hb : (fun u ↦ ⟪(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis b, u⟫_ℝ) ∘
          pairProjectionCLM i j = fun u => u (if b = 0 then i else j) := by
        ext u
        fin_cases b <;> simp [PiLp.inner_apply]
      rw [ha, hb, covariance_eval_multivariateGaussian hR.1,
        covarianceBilin_multivariateGaussian hpair.posSemidef]
      fin_cases a <;> fin_cases b <;> simp [pairCorrelation, hR.2]
      simpa using (hR.1.isHermitian.apply j i).symm
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

private def coordinateTail {m : ℕ} (i : Fin m) (c : ℝ) : Set (Coord m) :=
  {x | c < x i}

private lemma measurableSet_coordinateTail {m : ℕ} (i : Fin m) (c : ℝ) :
    MeasurableSet (coordinateTail i c) := by
  exact measurableSet_Ioi.preimage
    (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

private lemma measure_coordinateTail_eq
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (i : Fin m) (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R) (coordinateTail i c) =
      (gaussianReal 0 1) (Ioi c) := by
  have hmap := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord m)) hR.1 (i := i)).map_eq
  have happ := congrArg (fun ν : Measure ℝ => ν (Ioi c)) hmap
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at happ
  have hset : coordinateTail i c = (fun x : Coord m => x i) ⁻¹' Ioi c := by
    ext x
    rfl
  rw [hset]
  simpa [hR.2] using happ

private lemma measure_pairTail_eq
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (i j : Fin m) {ρ : ℝ} (hρ : R i j = ρ)
    (hpair : (pairCorrelation ρ).PosDef) (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R)
        (coordinateTail i c ∩ coordinateTail j c) =
      (multivariateGaussian (0 : Coord 2) (pairCorrelation ρ))
        {x | c < x 0 ∧ c < x 1} := by
  have hmap := map_pairProjectionCLM_multivariateGaussian hR i j
    (hρ ▸ hpair)
  have happ := congrArg (fun ν : Measure (Coord 2) =>
    ν {x | c < x 0 ∧ c < x 1}) hmap
  have htail : MeasurableSet {x : Coord 2 | c < x 0 ∧ c < x 1} :=
    (measurableSet_Ioi.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable).inter
      (measurableSet_Ioi.preimage
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).measurable)
  rw [Measure.map_apply (by fun_prop) htail] at happ
  have hset : coordinateTail i c ∩ coordinateTail j c =
      pairProjectionCLM i j ⁻¹' {x : Coord 2 | c < x 0 ∧ c < x 1} := by
    ext x
    simp [coordinateTail]
  rw [hset]
  simpa [hρ] using happ

private lemma pairTail_le_choose_mul_sq
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (heq : ∀ c : ℝ,
      (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) =
        (gaussianReal 0 1) (Iic c) ^ m)
    {i j : Fin m} (hij : i ≠ j) (c : ℝ) :
    ((multivariateGaussian (0 : Coord m) R)
        (coordinateTail i c ∩ coordinateTail j c)).toReal ≤
      (m.choose 2 : ℕ) * ((gaussianReal 0 1) (Ioi c)).toReal ^ 2 := by
  let μ : Measure (Coord m) := multivariateGaussian (0 : Coord m) R
  let q : ℝ := ((gaussianReal 0 1) (Ioi c)).toReal
  let f : ℝ := ((gaussianReal 0 1) (Iic c)).toReal
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hqf : q = 1 - f := by
    have hcompl : Ioi c = (Iic c)ᶜ := by ext x; simp
    dsimp [q, f]
    rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hA : ∀ k : Fin m, MeasurableSet (coordinateTail k c) :=
    fun k => measurableSet_coordinateTail k c
  have ha := toReal_measure_iUnion_add_inter_le_sum μ
    (fun k : Fin m => coordinateTail k c) hA hij
  have ha' :
      (μ (⋃ k : Fin m, coordinateTail k c)).toReal +
          (μ (coordinateTail i c ∩ coordinateTail j c)).toReal ≤
        (m : ℝ) * q := by
    simpa [μ, q, measure_coordinateTail_eq hR] using ha
  have hUcomp : (⋃ k : Fin m, coordinateTail k c)ᶜ = lowerOrthant c := by
    ext x
    simp [coordinateTail, lowerOrthant]
  have hU : (⋃ k : Fin m, coordinateTail k c) = (lowerOrthant c)ᶜ := by
    apply compl_injective
    simpa using hUcomp
  have hUreal :
      (μ (⋃ k : Fin m, coordinateTail k c)).toReal = 1 - f ^ m := by
    rw [hU, prob_compl_eq_one_sub (measurableSet_lowerOrthant c),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    dsimp [μ, f]
    rw [heq c, ENNReal.toReal_pow]
  have hb := one_sub_pow_le_second_order m hq0 hq1
  have hf : f = 1 - q := by linarith
  rw [hf] at hUreal
  rw [hUreal] at ha'
  exact_mod_cast (by linarith :
    (μ (coordinateTail i c ∩ coordinateTail j c)).toReal ≤
      (m.choose 2 : ℕ) * q ^ 2)

private lemma analytic_compare
    {C ρ c E : ℝ} (_hC : 0 ≤ C) (hc : 0 < c)
    (hdet : 0 < 1 - ρ ^ 2)
    (hgrowth : C * Real.sqrt (1 - ρ ^ 2) < Real.exp (c ^ 2 - E)) :
    C * (Real.exp (-c ^ 2 / 2) / (c * Real.sqrt (2 * Real.pi))) ^ 2 <
      (c ^ 2 * 2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ * Real.exp (-E) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  let d := c ^ 2 * 2 * Real.pi
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hU :
      (Real.exp (-c ^ 2 / 2) / (c * Real.sqrt (2 * Real.pi))) ^ 2 =
        Real.exp (-c ^ 2) / d := by
    dsimp [d]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    rw [pow_two (Real.exp _), ← Real.exp_add]
    congr 1
    · ring
    · rw [← mul_assoc]
  have hm :
      (C * Real.sqrt (1 - ρ ^ 2)) * (Real.exp (-c ^ 2) / s) <
        Real.exp (c ^ 2 - E) * (Real.exp (-c ^ 2) / s) :=
    mul_lt_mul_of_pos_right hgrowth (by positivity)
  have hleft :
      (C * s) * (Real.exp (-c ^ 2) / s) = C * Real.exp (-c ^ 2) := by
    field_simp
  have hright :
      Real.exp (c ^ 2 - E) * (Real.exp (-c ^ 2) / s) =
        Real.exp (-E) / s := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  dsimp [s] at hleft hright hm
  rw [hleft, hright] at hm
  have hm' :
      (C * Real.exp (-c ^ 2)) * d⁻¹ <
        (Real.exp (-E) / Real.sqrt (1 - ρ ^ 2)) * d⁻¹ :=
    mul_lt_mul_of_pos_right hm (inv_pos.mpr hd)
  rw [hU]
  dsimp [d, s]
  calc
    C * (Real.exp (-c ^ 2) / (c ^ 2 * 2 * Real.pi)) =
        (C * Real.exp (-c ^ 2)) * (c ^ 2 * 2 * Real.pi)⁻¹ := by ring
    _ < (Real.exp (-E) / Real.sqrt (1 - ρ ^ 2)) *
        (c ^ 2 * 2 * Real.pi)⁻¹ := hm'
    _ = (c ^ 2 * 2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ *
        Real.exp (-E) := by field_simp

private lemma exists_growth
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ c : ℝ, 1 ≤ c ∧
      C * Real.sqrt (1 - ρ ^ 2) <
        Real.exp (c ^ 2 - ((c + c⁻¹) ^ 2 / (1 + ρ) +
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2))) := by
  let a : ℝ := ρ / (1 + ρ)
  let D : ℝ := 3 / (1 + ρ) + ρ / (2 * (1 - ρ ^ 2))
  let B : ℝ := C * Real.sqrt (1 - ρ ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hdet : 0 < 1 - ρ ^ 2 := by nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max 1 ((Real.log (B + 1) + D) / a))
  let c : ℝ := n
  have hc1 : 1 < c := lt_of_le_of_lt (le_max_left _ _) hn
  have hc0 : 0 < c := lt_trans zero_lt_one hc1
  have hct : (Real.log (B + 1) + D) / a < c :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hgrow_linear : Real.log (B + 1) + D < a * c := by
    simpa [mul_comm] using (div_lt_iff₀ ha).mp hct
  have hcc : c ≤ c ^ 2 := by nlinarith
  have hgrow_square : Real.log (B + 1) < a * c ^ 2 - D := by
    nlinarith [mul_le_mul_of_nonneg_left hcc ha.le]
  have hci : 0 < c⁻¹ := inv_pos.mpr hc0
  have hci1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).2 hc1.le
  have hci_sq : (c⁻¹) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c⁻¹)]
  have hsquare : (c + c⁻¹) ^ 2 = c ^ 2 + 2 + (c⁻¹) ^ 2 := by
    field_simp
    ring
  have hE :
      (c + c⁻¹) ^ 2 / (1 + ρ) +
          ρ / (2 * (1 - ρ ^ 2) * c ^ 2) ≤
        c ^ 2 / (1 + ρ) + D := by
    have hplus : 0 < 1 + ρ := by linarith
    have hfirst :
        (c + c⁻¹) ^ 2 / (1 + ρ) ≤
          c ^ 2 / (1 + ρ) + 3 / (1 + ρ) := by
      rw [hsquare]
      apply (div_le_iff₀ hplus).2
      rw [show (c ^ 2 / (1 + ρ) + 3 / (1 + ρ)) * (1 + ρ) =
        c ^ 2 + 3 by field_simp]
      linarith
    have hsecond :
        ρ / (2 * (1 - ρ ^ 2) * c ^ 2) ≤
          ρ / (2 * (1 - ρ ^ 2)) := by
      rw [show ρ / (2 * (1 - ρ ^ 2) * c ^ 2) =
        ρ * (c⁻¹) ^ 2 / (2 * (1 - ρ ^ 2)) by field_simp]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right hρ0.le hci_sq) (by positivity)
    dsimp [D]
    linarith
  have hexp1 : B + 1 < Real.exp (a * c ^ 2 - D) := by
    rw [← Real.exp_log (by linarith : 0 < B + 1)]
    exact Real.exp_lt_exp.mpr hgrow_square
  have hexp2 : Real.exp (a * c ^ 2 - D) ≤
      Real.exp (c ^ 2 - ((c + c⁻¹) ^ 2 / (1 + ρ) +
        ρ / (2 * (1 - ρ ^ 2) * c ^ 2))) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    have halgebra : c ^ 2 - c ^ 2 / (1 + ρ) = ρ / (1 + ρ) * c ^ 2 := by
      field_simp
      ring
    rw [← halgebra]
    linarith
  refine ⟨c, hc1.le, ?_⟩
  dsimp [B] at hB ⊢
  dsimp [B] at hexp1
  linarith

private lemma exists_pairTail_gt_mul_sq
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ c : ℝ, 1 ≤ c ∧
      C * ((gaussianReal 0 1) (Ioi c)).toReal ^ 2 <
        ((multivariateGaussian (0 : Coord 2) (pairCorrelation ρ))
          {x | c < x 0 ∧ c < x 1}).toReal := by
  obtain ⟨c, hc, hgrowth⟩ := exists_growth hC hρ0 hρ1
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hdet : 0 < 1 - ρ ^ 2 := by nlinarith
  let E : ℝ := (c + c⁻¹) ^ 2 / (1 + ρ) +
    ρ / (2 * (1 - ρ ^ 2) * c ^ 2)
  have hcompare := analytic_compare hC hc0 hdet (by simpa [E] using hgrowth)
  have hq := gaussianReal_tail_le_pdf_div hc0
  have hq0 : 0 ≤ ((gaussianReal 0 1) (Ioi c)).toReal := ENNReal.toReal_nonneg
  have hpdf0 : 0 ≤ Real.exp (-c ^ 2 / 2) /
      (c * Real.sqrt (2 * Real.pi)) := by positivity
  have hqsq : ((gaussianReal 0 1) (Ioi c)).toReal ^ 2 ≤
      (Real.exp (-c ^ 2 / 2) / (c * Real.sqrt (2 * Real.pi))) ^ 2 :=
    (sq_le_sq₀ hq0 hpdf0).2 hq
  have hscaled := mul_le_mul_of_nonneg_left hqsq hC
  have hlower := bivariate_pair_tail_lower_bound hρ0 hρ1 hc
  refine ⟨c, hc, lt_of_le_of_lt hscaled (lt_of_lt_of_le hcompare ?_)⟩
  convert hlower using 1
  congr 2
  ring

private lemma correlation_entry_le_one
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (i j : Fin m) : R i j ≤ 1 := by
  let e : Fin 2 → Fin m := ![i, j]
  have hdet := (hR.1.submatrix e).det_nonneg
  have hsymm : R j i = R i j := by
    simpa using (hR.1.isHermitian.apply j i).symm
  simp [Matrix.det_fin_two, e, hR.2, hsymm] at hdet
  nlinarith [sq_nonneg (R i j - 1)]

private lemma measure_pairTail_eq_of_corr_one
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : IsCorrelation R)
    (i j : Fin m) (hρ : R i j = 1) (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R)
        (coordinateTail i c ∩ coordinateTail j c) =
      (gaussianReal 0 1) (Ioi c) := by
  let μ : Measure (Coord m) := multivariateGaussian (0 : Coord m) R
  let Xi : Coord m → ℝ := fun x => x i
  let Xj : Coord m → ℝ := fun x => x j
  have hId : HasGaussianLaw (id : Coord m → Coord m) μ :=
    IsGaussian.hasGaussianLaw_id
  have hXi : MemLp Xi 2 μ := by
    simpa only [Xi, Function.comp_id, EuclideanSpace.coe_proj] using
      (hId.map (EuclideanSpace.proj i)).memLp_two
  have hXj : MemLp Xj 2 μ := by
    simpa only [Xj, Function.comp_id, EuclideanSpace.coe_proj] using
      (hId.map (EuclideanSpace.proj j)).memLp_two
  have hvar : Var[fun x => Xi x - Xj x; μ] = 0 := by
    rw [variance_fun_sub hXi hXj,
      ← covariance_self hXi.aemeasurable, ← covariance_self hXj.aemeasurable,
      covariance_eval_multivariateGaussian hR.1,
      covariance_eval_multivariateGaussian hR.1,
      covariance_eval_multivariateGaussian hR.1]
    rw [hR.2, hR.2, hρ]
    norm_num
  have hint_id : ∫ x : Coord m, x ∂μ = 0 := by
    dsimp [μ]
    exact integral_id_multivariateGaussian
  have hint_i : ∫ x, Xi x ∂μ = 0 := by
    calc
      ∫ x, Xi x ∂μ = (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ x, x ∂μ) := by
        simpa [Xi] using
          (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hId.integrable
      _ = 0 := by rw [hint_id]; simp
  have hint_j : ∫ x, Xj x ∂μ = 0 := by
    calc
      ∫ x, Xj x ∂μ = (EuclideanSpace.proj (𝕜 := ℝ) j) (∫ x, x ∂μ) := by
        simpa [Xj] using
          (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hId.integrable
      _ = 0 := by rw [hint_id]; simp
  have hint : ∫ x, (Xi x - Xj x) ∂μ = 0 := by
    rw [integral_sub (hXi.integrable one_le_two) (hXj.integrable one_le_two),
      hint_i, hint_j, sub_self]
  have hint' : ∫ x, (Xi - Xj) x ∂μ = 0 := by
    simpa only [Pi.sub_apply] using hint
  have hae_const := ae_eq_integral_of_variance_eq_zero (hXi.sub hXj) hvar
  have hae : ∀ᵐ x ∂μ, Xi x = Xj x := by
    filter_upwards [hae_const] with x hx
    rw [hint'] at hx
    dsimp only [Pi.sub_apply] at hx
    linarith
  calc
    μ (coordinateTail i c ∩ coordinateTail j c) = μ (coordinateTail i c) := by
      apply measure_congr
      filter_upwards [hae] with x hx
      change x i = x j at hx
      apply propext
      change (c < x i ∧ c < x j) ↔ c < x i
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, hx ▸ h⟩
    _ = (gaussianReal 0 1) (Ioi c) := measure_coordinateTail_eq hR i c

private lemma gaussian_tail_toReal_pos (c : ℝ) :
    0 < ((gaussianReal 0 1) (Ioi c)).toReal := by
  have hcompl : Ioi c = (Iic c)ᶜ := by ext x; simp
  have hF : ((gaussianReal 0 1) (Iic c)).toReal = normalCDF c := by
    rw [← normalCDF_eq_measure_Iic,
      ENNReal.toReal_ofReal (normalCDF_pos c).le]
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, hF]
  linarith [normalCDF_lt_one c]

private lemma exists_gaussian_tail_mul_lt_one (C : ℝ) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < ((gaussianReal 0 1) (Ioi c)).toReal ∧
      C * ((gaussianReal 0 1) (Ioi c)).toReal < 1 := by
  let s := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := by dsimp [s]; positivity
  let c := C / s + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp : Real.exp (-c ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg c]
  have hpdf : Real.exp (-c ^ 2 / 2) /
      (c * Real.sqrt (2 * Real.pi)) ≤ 1 / (c * s) := by
    dsimp [s]
    exact div_le_div_of_nonneg_right hexp (by positivity)
  have hq := gaussianReal_tail_le_pdf_div hc
  refine ⟨c, gaussian_tail_toReal_pos c, ?_⟩
  have hq' : ((gaussianReal 0 1) (Ioi c)).toReal ≤ 1 / (c * s) := hq.trans hpdf
  have hmul := mul_le_mul_of_nonneg_left hq' hC
  have hCs : C < c * s := by
    dsimp [c]
    field_simp
    linarith
  have hCc : C / (c * s) < 1 := (div_lt_one (mul_pos hc hs)).2 hCs
  rw [show C * (1 / (c * s)) = C / (c * s) by ring] at hmul
  exact hmul.trans_lt hCc

/-- (e) **Tail rigidity (main result of this module).**  Equality of the
lower-orthant probabilities with the iid bound at every threshold forces the
identity correlation matrix. -/
theorem eq_one_of_lowerOrthant_eq_iid
    {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (heq : ∀ c : ℝ,
      (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) =
        (gaussianReal 0 1) (Set.Iic c) ^ m) :
    R = 1 := by
  have hcorr : IsCorrelation R := hR.1
  have hoff : ∀ i j : Fin m, i ≠ j → R i j ≤ 0 := by
    intro i j hij
    by_contra hnot
    have hρ0 : 0 < R i j := lt_of_not_ge hnot
    have hρle : R i j ≤ 1 := correlation_entry_le_one hcorr i j
    rcases hρle.lt_or_eq with hρ1 | hρeq
    · let C : ℝ := (m.choose 2 : ℕ)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      obtain ⟨c, _hc, hlarge⟩ := exists_pairTail_gt_mul_sq hC hρ0 hρ1
      have hup := pairTail_le_choose_mul_sq hcorr heq hij c
      have hpair := measure_pairTail_eq hcorr i j rfl
        (pairCorrelation_posDef hρ0 hρ1) c
      rw [hpair] at hup
      have hup' :
          ((multivariateGaussian (0 : Coord 2) (pairCorrelation (R i j)))
              {x | c < x 0 ∧ c < x 1}).toReal ≤
            C * ((gaussianReal 0 1) (Ioi c)).toReal ^ 2 := by
        simpa [C] using hup
      exact (not_lt_of_ge hup') hlarge
    · let C : ℝ := (m.choose 2 : ℕ)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      obtain ⟨c, hqpos, hqsmall⟩ := exists_gaussian_tail_mul_lt_one C hC
      have hup := pairTail_le_choose_mul_sq hcorr heq hij c
      have hpair := measure_pairTail_eq_of_corr_one hcorr i j hρeq c
      rw [hpair] at hup
      have hup' : ((gaussianReal 0 1) (Ioi c)).toReal ≤
          C * ((gaussianReal 0 1) (Ioi c)).toReal ^ 2 := by
        simpa [C] using hup
      have hprod : 0 < ((gaussianReal 0 1) (Ioi c)).toReal *
          (1 - C * ((gaussianReal 0 1) (Ioi c)).toReal) :=
        mul_pos hqpos (sub_pos.mpr hqsmall)
      nlinarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hquad := hR.2.dotProduct_mulVec_nonneg (fun _ : Fin m => (1 : ℝ))
  have hquad' : 0 ≤ (∑ i : Fin m, ∑ j : Fin m, R i j) - m := by
    simpa [dotProduct, Matrix.mulVec, allOnesMatrix, Finset.sum_sub_distrib,
      hm0] using hquad
  have hrow : ∀ i : Fin m, (∑ j : Fin m, R i j) ≤ 1 := by
    intro i
    rw [show ∑ j : Fin m, R i j =
      (∑ j ∈ Finset.univ.erase i, R i j) + R i i by
        rw [Finset.sum_erase_add Finset.univ (fun j => R i j) (Finset.mem_univ i)]]
    rw [hR.1.2 i]
    have hoffsum : (∑ j ∈ Finset.univ.erase i, R i j) ≤ 0 := by
      exact Finset.sum_nonpos fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    linarith
  have htotal : (∑ i : Fin m, ∑ j : Fin m, R i j) ≤ m := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, R i j) ≤ ∑ _i : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = m := by simp
  have htotaleq : (∑ i : Fin m, ∑ j : Fin m, R i j) =
      ∑ _i : Fin m, (1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    linarith
  have hroweq : ∀ i : Fin m, (∑ j : Fin m, R i j) = 1 := by
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (f := fun i : Fin m => ∑ j : Fin m, R i j)
      (g := fun _ => (1 : ℝ)) (fun i _ => hrow i)).mp htotaleq
    exact fun i => hall i (Finset.mem_univ i)
  have hoffzero : ∀ i j : Fin m, i ≠ j → R i j = 0 := by
    intro i j hij
    have hrowoff : (∑ k ∈ Finset.univ.erase i, R i k) = 0 := by
      have hdecomp := Finset.sum_erase_add Finset.univ (fun k => R i k)
        (Finset.mem_univ i)
      rw [hR.1.2 i] at hdecomp
      linarith [hroweq i]
    have hall : ∀ k ∈ Finset.univ.erase i, R i k ≤ 0 := by
      intro k hk
      exact hoff i k (Finset.ne_of_mem_erase hk).symm
    have hallzero := (Finset.sum_eq_sum_iff_of_le hall).mp (by simpa using hrowoff)
    exact hallzero j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hR.1.2 i
  · simp [hoffzero i j hij, hij]

end SimplexUniqueness
