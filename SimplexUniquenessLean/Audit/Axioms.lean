import SimplexUniquenessLean.StrictMonoDomination
import SimplexUniquenessLean.TailRigidity
import SimplexUniquenessLean.GramRigidity

/-!
# Axiom audit

This file records the transitive axioms used by the public declarations. The accepted
output for every command is exactly `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms SimplexUniqueness.measure_eq_of_iic_le_of_integral_eq
#print axioms SimplexUniqueness.measure_eq_of_iic_le_of_mean_eq
#print axioms SimplexUniqueness.measure_eq_of_iic_le_of_mgf_eq
#print axioms SimplexUniqueness.gaussianReal_tail_le_pdf_div
#print axioms SimplexUniqueness.bivariate_pair_tail_lower_bound
#print axioms SimplexUniqueness.eq_one_of_lowerOrthant_eq_iid
#print axioms SimplexUniqueness.exists_linearIsometryEquiv_of_gram_eq
