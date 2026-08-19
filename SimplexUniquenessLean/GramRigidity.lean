import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Gram rigidity

The geometric identification step used in the equal-energy part of the
paper's coding theorem. Two `m`-tuples in `ℝⁿ` with the same Gram matrix
and full span differ by a linear isometry of `ℝⁿ`. The isometry is built by
factoring the two coefficient maps through their common kernel and applying
`LinearEquiv.isometryOfInner`.
-/

namespace SimplexUniqueness

open Set

/-- Two spanning families with identical Gram matrices differ by a linear
isometry equivalence. -/
theorem exists_linearIsometryEquiv_of_gram_eq
    {n m : ℕ} (v u : Fin m → EuclideanSpace ℝ (Fin n))
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (u i) (u j))
    (hv : Submodule.span ℝ (range v) = ⊤)
    (hu : Submodule.span ℝ (range u) = ⊤) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, T (v i) = u i := by
  let lv : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Fintype.linearCombination ℝ v
  let lu : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Fintype.linearCombination ℝ u
  have hinner_coeff (a b : Fin m → ℝ) :
      inner ℝ (lv a) (lv b) = inner ℝ (lu a) (lu b) := by
    simp only [lv, lu, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    simp_rw [hgram]
  have hker : LinearMap.ker lv = LinearMap.ker lu := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      rw [← hinner_coeff a a, ha, inner_zero_left]
    · intro ha
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      rw [hinner_coeff a a, ha, inner_zero_left]
  have hsv : Function.Surjective lv :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := ℝ) (v := v)).mp hv
  have hsu : Function.Surjective lu :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := ℝ) (v := u)).mp hu
  let ev := lv.quotKerEquivOfSurjective hsv
  let eu := lu.quotKerEquivOfSurjective hsu
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ev.symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans eu)
  have he_apply (a : Fin m → ℝ) : e (lv a) = lu a := by
    simp [e, ev, eu]
  have he_inner (x y : EuclideanSpace ℝ (Fin n)) :
      inner ℝ (e x) (e y) = inner ℝ x y := by
    obtain ⟨a, rfl⟩ := hsv x
    obtain ⟨b, rfl⟩ := hsv y
    rw [he_apply, he_apply]
    exact (hinner_coeff a b).symm
  refine ⟨e.isometryOfInner he_inner, fun i ↦ ?_⟩
  change e (v i) = u i
  let a : Fin m → ℝ := Pi.single i 1
  have hva : lv a = v i := by simp [lv, a]
  have hua : lu a = u i := by simp [lu, a]
  rw [← hva, he_apply, hua]

end SimplexUniqueness
