module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFSplit

/-!
# The two forms of the reference generator agree

`rfGeneratorEq_holds` proves `RFGeneratorEqStatement`: `referenceArrayGenerator F a b₀ ω ℓ σ h z`
equals `refGenerator (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) σ h z` for every function `h` and
point `z`; no smoothness, no condition on `ℓ`, `F`, `ω`.

* Short rotations. `referenceArrayGenerator` sums `j` with `i < j ∧ labelDist i j < ℓ` and the
  rate `flowRate`; `refGenerator` sums all `j` with `if i < j then shortRate … i j * …`,
  `shortRate = flowRate · 1{i ≠ j ∧ |i-j| < ℓ}`. On `i < j` the condition `i ≠ j` is automatic,
  so the summands agree term by term.
* Vector fields. For `i ≠ j`, the matrix `rotX i j` acting by `lmul` is minus the vector field
  `rotX i j` (`lmul_rotX`), and the matrix `rotY i j` acting by `lmul` is the vector field
  `rotY i j` (`lmul_rotY`). The square `D²h(Wz, Wz) + Dh(W W z)` is unchanged under `W ↦ -W`
  (`vfSq_rotX`). For `i = j` the two conventions differ (the matrix `rotX i i = 0`, the vector
  field `rotX i i z = e_i z_i`), but `i = j` never occurs in either sum (`i < j`).
* Damping. The two `refDamping` have identical bodies; `Pi.single i (z i) = rowProj i z`,
  `Pi.single i (Pi.single q 1) = unitEntry i q`,
  `Pi.single i (Pi.single q I) = I • unitEntry i q` (`smul_single_single`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.AbstractFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r : ℕ}

/-- For `i ≠ j`, the matrix `X_ij` acting on labels is minus the vector field `rotX i j`. -/
theorem lmul_rotX {i j : Fin N} (hij : i ≠ j) (w : Fin N → Fin r → ℂ) :
    BlockBand.Palm.ReferenceFlow.lmul (BlockBand.Internal.Contracts.TransmissionFlow.rotX i j) w =
      -(rotX i j w) := by
  funext k q
  have hji : j ≠ i := Ne.symm hij
  simp only [BlockBand.Palm.ReferenceFlow.lmul,
    BlockBand.Internal.Contracts.TransmissionFlow.rotX, Matrix.sub_apply, Matrix.single_apply,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, rotX, Pi.neg_apply]
  by_cases hki : k = i
  · subst hki; simp [hji]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, Ne.symm hki]
    · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- For `i ≠ j`, the matrix `Y_ij` acting on labels is the vector field `rotY i j`. -/
theorem lmul_rotY {i j : Fin N} (hij : i ≠ j) (w : Fin N → Fin r → ℂ) :
    BlockBand.Palm.ReferenceFlow.lmul (BlockBand.Internal.Contracts.TransmissionFlow.rotY i j) w =
      rotY i j w := by
  funext k q
  have hji : j ≠ i := Ne.symm hij
  simp only [BlockBand.Palm.ReferenceFlow.lmul,
    BlockBand.Internal.Contracts.TransmissionFlow.rotY, Matrix.smul_apply, Matrix.add_apply,
    Matrix.single_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, rotY]
  by_cases hki : k = i
  · subst hki; simp [hji]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, Ne.symm hki]
    · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]

theorem rotX_neg (i j : Fin N) (w : Fin N → Fin r → ℂ) : rotX i j (-w) = -(rotX i j w) := by
  funext k
  by_cases hki : k = i
  · simp [rotX, hki]
  · by_cases hkj : k = j
    · subst hkj; simp [rotX, hki]
    · simp [rotX, hki, hkj]

/-- `X_ij² h` in matrix form equals `fieldSq (rotX i j) h` (sign invariance). -/
theorem vfSq_rotX {i j : Fin N} (hij : i ≠ j) (h : (Fin N → Fin r → ℂ) → ℝ)
    (z : Fin N → Fin r → ℂ) :
    BlockBand.Palm.ReferenceFlow.vfSq (BlockBand.Internal.Contracts.TransmissionFlow.rotX i j)
        h z = fieldSq (rotX i j) h z := by
  unfold BlockBand.Palm.ReferenceFlow.vfSq BlockBand.Palm.ReferenceFlow.D2 fieldSq
  rw [lmul_rotX hij, lmul_rotX hij, rotX_neg, neg_neg]
  simp only [map_neg, _root_.neg_apply, neg_neg]

/-- `Y_ij² h` in matrix form equals `fieldSq (rotY i j) h`. -/
theorem vfSq_rotY {i j : Fin N} (hij : i ≠ j) (h : (Fin N → Fin r → ℂ) → ℝ)
    (z : Fin N → Fin r → ℂ) :
    BlockBand.Palm.ReferenceFlow.vfSq (BlockBand.Internal.Contracts.TransmissionFlow.rotY i j)
        h z = fieldSq (rotY i j) h z := by
  unfold BlockBand.Palm.ReferenceFlow.vfSq BlockBand.Palm.ReferenceFlow.D2 fieldSq
  rw [lmul_rotY hij, lmul_rotY hij]

theorem rowProj_eq (i : Fin N) (z : Fin N → Fin r → ℂ) :
    BlockBand.Palm.ReferenceFlow.rowProj i z = Pi.single i (z i) := by
  funext k q
  by_cases hki : k = i
  · subst hki; simp [BlockBand.Palm.ReferenceFlow.rowProj]
  · simp [BlockBand.Palm.ReferenceFlow.rowProj, hki]

theorem unitEntry_eq (i : Fin N) (q : Fin r) :
    BlockBand.Palm.ReferenceFlow.unitEntry i q =
      (Pi.single i (Pi.single q 1) : Fin N → Fin r → ℂ) := by
  funext k q'
  by_cases hki : k = i
  · subst hki
    by_cases hq : q' = q
    · subst hq; simp [BlockBand.Palm.ReferenceFlow.unitEntry]
    · simp [BlockBand.Palm.ReferenceFlow.unitEntry, hq]
  · simp [BlockBand.Palm.ReferenceFlow.unitEntry, hki]

theorem smul_single_single (i : Fin N) (q : Fin r) :
    Complex.I • (Pi.single i (Pi.single q 1) : Fin N → Fin r → ℂ) =
      Pi.single i (Pi.single q Complex.I) := by
  funext k q'
  by_cases hki : k = i
  · subst hki
    by_cases hq : q' = q
    · subst hq; simp
    · simp [hq]
  · simp [hki]

/-- `referenceArrayGenerator` is `refGenerator` with the coefficients `shortRate`, `refDamping`,
for every `h` and `z`. -/
theorem rfGeneratorEq_holds :
    ∀ N r, BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.RFGeneratorEqStatement N r := by
  intro N r F a b₀ ω ℓ σ h z
  unfold referenceArrayGenerator BlockBand.Palm.ReferenceFlow.refGenerator
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · rw [vfSq_rotX hij.ne, vfSq_rotY hij.ne]
      by_cases hd : labelDist i j < ℓ
      · simp [BlockBand.Palm.RelativeLocalization.StochasticBridge.shortRate, hij, hd, hij.ne]
      · simp [BlockBand.Palm.RelativeLocalization.StochasticBridge.shortRate, hij, hd]
    · simp [hij]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [refDamping, BlockBand.Palm.RelativeLocalization.StochasticBridge.refDamping,
      rowProj_eq, BlockBand.Palm.ReferenceFlow.D2, unitEntry_eq, smul_single_single]

end BlockBand.Critical.RelativeVectors.AbstractFlow
