module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.TailSupportReduction
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedIntegralAbsolute

/-!
# Ordered APSSS shifted Fourier tail

This module removes the global coefficient-nonvanishing premise from the
shifted two-dimensional estimate of APSSS (Aizenman–Peled–Schenker–Shamis–Sodin).  Only the selected dominant coordinates
must be nonzero; zero tail coordinates are erased by `nonzeroTailSupport`.
The split rank and tail scale are the canonical ones coming from the ordered
coefficient energies.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory
open scoped ENNReal NNReal

/-- The canonical contour displacement is the displacement belonging to
`dominantTailScale`. -/
theorem selectionDelta_eq_dominantTailScale {n : ℕ} (E b : Fin n → ℝ) :
    selectionDelta E b (dominantSplitRank E b) =
      1 / (10 * dominantTailScale E b ^ 2) := by
  unfold selectionDelta
  change 1 / (10 * tailEnergy E b (dominantSplitRank E b)) =
    1 / (10 * dominantTailScale E b ^ 2)
  rw [dominantTailScale_sq]

/-- The algebraically combined dominant decay used by the Hölder coordinate
is the cube of the source's dominant factor. -/
theorem dominantCubedDecay_eq_pow (E b η : ℝ) :
    dominantCubedDecay E b η = dominantDecayFactor E b η ^ 3 := by
  unfold dominantCubedDecay dominantDecayFactor
  rw [mul_pow]
  have hbase : 0 ≤ 1 + 4 * (η * E) ^ 2 := by positivity
  have hpow :
      (1 + (2 * E * η) ^ 2) ^ (-(3 : ℝ) / 4) =
        ((1 + 4 * (η * E) ^ 2) ^ (-(1 / 4 : ℝ))) ^ 3 := by
    have hbeq : 1 + (2 * E * η) ^ 2 = 1 + 4 * (η * E) ^ 2 := by ring
    rw [hbeq]
    calc
      (1 + 4 * (η * E) ^ 2) ^ (-(3 : ℝ) / 4) =
          (1 + 4 * (η * E) ^ 2) ^ ((-(1 / 4 : ℝ)) * 3) := by
            congr 1
            ring
      _ = ((1 + 4 * (η * E) ^ 2) ^ (-(1 / 4 : ℝ))) ^ (3 : ℝ) := by
            rw [Real.rpow_mul hbase]
      _ = ((1 + 4 * (η * E) ^ 2) ^ (-(1 / 4 : ℝ))) ^ 3 := by
            exact Real.rpow_natCast _ 3
  rw [show 1 + (2 * E) ^ 2 * η ^ 2 = 1 + (2 * E * η) ^ 2 by ring]
  rw [hpow]
  conv_rhs => rw [mul_pow]
  apply congrArg₂ (· * ·) rfl
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The tail decay after the first Hölder exponent has been installed.  For
`r = 0` this is the source decay itself.  For `r = 1,2` its polynomial
quarter-power is unchanged, while the negative exponential is weakened by
the factor `(3-r)/3`. -/
def holderWeakenedTailDecayFactor (r : ℕ) (E b ξ η : ℝ) : ℝ :=
  (1 + 4 * (tailAffineFrequency E ξ η) ^ 2) ^ (-(1 / 4 : ℝ)) *
    Real.exp
      ((-2 * b ^ 2 * (tailAffineFrequency E ξ η) ^ 2 /
          (1 + 4 * (tailAffineFrequency E ξ η) ^ 2)) *
        (((3 - r : ℕ) : ℝ) / 3))

/-- Exact polynomial exponent arithmetic in the second and first Hölder
steps.  This is the `A^{-3/(4(3-r)α)}` to `A^{-1/4}` match in APSSS; no
inequality is used here. -/
theorem tailHolder_polynomial_match (r : ℕ) (hr : r ≤ 2)
    (α z : ℝ) (hα : 0 < α) :
    (((1 + 4 * z ^ 2) ^
          (-(3 / (4 * ((3 - r : ℕ) : ℝ) * α)) : ℝ)) ^ α) ^
        (((3 - r : ℕ) : ℝ) / 3) =
      (1 + 4 * z ^ 2) ^ (-(1 / 4 : ℝ)) := by
  have hbase : 0 ≤ 1 + 4 * z ^ 2 := by positivity
  have hc : (0 : ℝ) < ((3 - r : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 3 - r)
  rw [← Real.rpow_mul hbase, ← Real.rpow_mul hbase]
  congr 1
  field_simp

/-- The pointwise comparison used in the contour-to-Hölder bridge.
For `r = 1,2` the exponent `(3-r)/3` lies in `[0,1]`, so replacing
`exp (-q)` by `exp (-q(3-r)/3)` enlarges the factor.  Thus the source decay
is bounded **above** by the Hölder decay; it is not equal to it. -/
theorem tailDecayFactor_le_holderWeakened (r : ℕ) (_hr : r ≤ 2)
    (E b ξ η : ℝ) :
    tailDecayFactor E b ξ η ≤ holderWeakenedTailDecayFactor r E b ξ η := by
  let z := tailAffineFrequency E ξ η
  let q := 2 * b ^ 2 * z ^ 2 / (1 + 4 * z ^ 2)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hc0 : (0 : ℝ) ≤ ((3 - r : ℕ) : ℝ) / 3 := by positivity
  have hc1 : ((3 - r : ℕ) : ℝ) / 3 ≤ 1 := by
    apply (div_le_one (by norm_num : (0 : ℝ) < 3)).2
    exact_mod_cast (Nat.sub_le 3 r)
  have hexp : Real.exp (-q) ≤
      Real.exp (-q * (((3 - r : ℕ) : ℝ) / 3)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hc1 hq
    nlinarith
  unfold tailDecayFactor holderWeakenedTailDecayFactor
  dsimp [z, q] at hexp ⊢
  have hexp' :
      Real.exp (-2 * b ^ 2 * tailAffineFrequency E ξ η ^ 2 /
          (1 + 4 * tailAffineFrequency E ξ η ^ 2)) ≤
        Real.exp (-2 * b ^ 2 * tailAffineFrequency E ξ η ^ 2 /
          (1 + 4 * tailAffineFrequency E ξ η ^ 2) *
            (((3 - r : ℕ) : ℝ) / 3)) := by
    convert hexp using 1 <;> ring
  exact mul_le_mul_of_nonneg_left hexp' (Real.rpow_nonneg (by positivity) _)

/-- The coefficient-dependent part of one tail Hölder coordinate, with the
common shifted kernel omitted. -/
def tailHolderDecayCore (r : ℕ) (α E b ξ η : ℝ) : ℝ :=
  (1 + 4 * (tailAffineFrequency E ξ η) ^ 2) ^
      (-(3 / (4 * ((3 - r : ℕ) : ℝ) * α)) : ℝ) *
    Real.exp
      (-(2 * b ^ 2 / α) * (tailAffineFrequency E ξ η) ^ 2 /
        (1 + 4 * (tailAffineFrequency E ξ η) ^ 2))

/-- After both Hölder powers, the tail core has exactly the source polynomial
quarter-power and the deliberately weakened exponential.  This is the
coordinatewise algebra behind the pointwise comparison; positivity of `α`
is essential because the coordinate contains `1/α`. -/
theorem tailHolderDecayCore_rpow_eq_weakened
    (r : ℕ) (hr : r ≤ 2) (α E b ξ η : ℝ) (hα : 0 < α) :
    ((tailHolderDecayCore r α E b ξ η) ^ α) ^
        (((3 - r : ℕ) : ℝ) / 3) =
      holderWeakenedTailDecayFactor r E b ξ η := by
  let z := tailAffineFrequency E ξ η
  let A := 1 + 4 * z ^ 2
  let q := 2 * b ^ 2 * z ^ 2 / A
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpoly : 0 ≤ A ^
      (-(3 / (4 * ((3 - r : ℕ) : ℝ) * α)) : ℝ) :=
    Real.rpow_nonneg hA.le _
  have hexp0 : 0 ≤ Real.exp (-q / α) := (Real.exp_pos _).le
  have hcore :
      tailHolderDecayCore r α E b ξ η =
        A ^ (-(3 / (4 * ((3 - r : ℕ) : ℝ) * α)) : ℝ) *
          Real.exp (-q / α) := by
    unfold tailHolderDecayCore
    dsimp [z, A, q]
    congr 2
    · ring
  rw [hcore, Real.mul_rpow hpoly hexp0]
  rw [Real.mul_rpow (Real.rpow_nonneg hpoly _)
    (Real.rpow_nonneg hexp0 _)]
  rw [tailHolder_polynomial_match r hr α z hα]
  have hexp :
      ((Real.exp (-q / α)) ^ α) ^ (((3 - r : ℕ) : ℝ) / 3) =
        Real.exp (-q * (((3 - r : ℕ) : ℝ) / 3)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp
  rw [hexp]
  unfold holderWeakenedTailDecayFactor
  dsimp [z, A, q]
  congr 2
  ring

/-- Separation of the common shifted kernel from the coefficient-dependent
tail core.  This is a definitional-algebraic identity, prior to either Hölder
power. -/
theorem tailHolderCoordinate_eq_kernel_mul_core {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ) (j : Fin n)
    (x : ℝ × ℝ) :
    tailHolderCoordinate E b r ν δ j x =
      ENNReal.ofReal
        (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
          tailHolderDecayCore r (tailHolderWeight E b ν j)
            (E j) (b j) x.1 x.2) := by
  unfold tailHolderCoordinate tailHolderDecayCore
  apply congrArg ENNReal.ofReal
  ring

/-- Every coordinate retained in `nonzeroTailSupport` has a strictly positive
normalized Hölder weight. -/
theorem tailHolderWeight_pos_of_mem_nonzeroTailSupport {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν : ℝ) (hν : 0 < ν)
    (j : Fin n) (hj : j ∈ nonzeroTailSupport E r) :
    0 < tailHolderWeight E b ν j := by
  have hE : E j ≠ 0 :=
    coefficient_ne_zero_of_mem_nonzeroTailSupport E r j hj
  unfold tailHolderWeight
  positivity

/-- Coordinatewise powered identity including the common shifted kernel.
The kernel receives exponent `α(3-r)/3`, while the coefficient-dependent
factor becomes exactly `holderWeakenedTailDecayFactor`. -/
theorem tailHolderCoordinate_powered_eq {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hν : 0 < ν) (hδ : 0 < δ) (j : Fin n)
    (hj : j ∈ nonzeroTailSupport E r) (x : ℝ × ℝ) :
    ((tailHolderCoordinate E b r ν δ j x ^
        tailHolderWeight E b ν j) ^
      (((3 - r : ℕ) : ℝ) / 3)) =
      ENNReal.ofReal
        (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
            (tailHolderWeight E b ν j * (((3 - r : ℕ) : ℝ) / 3)) *
          holderWeakenedTailDecayFactor r (E j) (b j) x.1 x.2) := by
  let α := tailHolderWeight E b ν j
  let K := (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)
  let H := tailHolderDecayCore r α (E j) (b j) x.1 x.2
  have hα : 0 < α :=
    tailHolderWeight_pos_of_mem_nonzeroTailSupport E b r ν hν j hj
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hH : 0 < H := by
    dsimp [H, tailHolderDecayCore]
    positivity
  rw [tailHolderCoordinate_eq_kernel_mul_core]
  change ((ENNReal.ofReal (K * H) ^ α) ^
    (((3 - r : ℕ) : ℝ) / 3)) = _
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hK hH)]
  rw [ENNReal.ofReal_rpow_of_pos
    (Real.rpow_pos_of_pos (mul_pos hK hH) α)]
  apply congrArg ENNReal.ofReal
  rw [Real.mul_rpow hK.le hH.le]
  rw [Real.mul_rpow (Real.rpow_nonneg hK.le _)
    (Real.rpow_nonneg hH.le _)]
  rw [← Real.rpow_mul hK.le]
  rw [show ((H ^ α) ^ (((3 - r : ℕ) : ℝ) / 3)) =
      holderWeakenedTailDecayFactor r (E j) (b j) x.1 x.2 by
    exact tailHolderDecayCore_rpow_eq_weakened
      r hr α (E j) (b j) x.1 x.2 hα]

/-- The preceding coordinate identity tensorizes over the nonzero tail
support.  This retains the per-coordinate kernel exponents; the
next normalization step collapses their product using that the active weights
sum to one. -/
theorem supportedTailHolderProduct_powered_eq_product {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hν : 0 < ν) (hδ : 0 < δ) (x : ℝ × ℝ) :
    (supportedTailHolderProduct E b r ν δ x ^
      (((3 - r : ℕ) : ℝ) / 3)) =
      ∏ j ∈ nonzeroTailSupport E r,
        ENNReal.ofReal
          (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
              (tailHolderWeight E b ν j *
                (((3 - r : ℕ) : ℝ) / 3)) *
            holderWeakenedTailDecayFactor r (E j) (b j) x.1 x.2) := by
  have hs : (0 : ℝ) ≤ ((3 - r : ℕ) : ℝ) / 3 := by positivity
  unfold supportedTailHolderProduct
  rw [← ENNReal.prod_rpow_of_nonneg hs]
  apply Finset.prod_congr rfl
  intro j hj
  exact tailHolderCoordinate_powered_eq E b r hr ν δ hν hδ j hj x

/-- The normalized active tail weights collapse all copies of the common
shifted kernel to the single exponent `(3-r)/3`. -/
theorem prod_tail_kernel_rpow_eq {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ)
    (hνpos : 0 < ν) (hν : ν ^ 2 = tailEnergy E b r)
    (hδ : 0 < δ) (x : ℝ × ℝ) :
    (∏ j ∈ nonzeroTailSupport E r,
      ((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
        (tailHolderWeight E b ν j * (((3 - r : ℕ) : ℝ) / 3))) =
      ((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
        (((3 - r : ℕ) : ℝ) / 3) := by
  let K := (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  rw [← Real.rpow_sum_of_pos hK]
  congr 1
  rw [← Finset.sum_mul]
  rw [sum_nonzeroTailSupport_tailHolderWeight_eq_one E b r ν hνpos hν]
  simp

/-- Complete active-tail identity after both Hölder powers: one common kernel
of exponent `(3-r)/3`, times the product of the weakened coefficient
decays. -/
theorem supportedTailHolderProduct_powered_eq {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hνpos : 0 < ν) (hν : ν ^ 2 = tailEnergy E b r)
    (hδ : 0 < δ) (x : ℝ × ℝ) :
    (supportedTailHolderProduct E b r ν δ x ^
      (((3 - r : ℕ) : ℝ) / 3)) =
      ENNReal.ofReal
        (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
          (((3 - r : ℕ) : ℝ) / 3)) *
        ∏ j ∈ nonzeroTailSupport E r,
          ENNReal.ofReal
            (holderWeakenedTailDecayFactor r (E j) (b j) x.1 x.2) := by
  rw [supportedTailHolderProduct_powered_eq_product
    E b r hr ν δ hνpos hδ x]
  simp_rw [ENNReal.ofReal_mul
    (Real.rpow_nonneg (by positivity : 0 ≤
      (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) _)]
  rw [Finset.prod_mul_distrib]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun _ _ => Real.rpow_nonneg (by positivity) _)]
  rw [prod_tail_kernel_rpow_eq E b r ν δ hνpos hν hδ x]

/-- The source tail decay (restricted only by deleting unit zero
coordinates) is bounded by the powered supported Hölder product.  The sole
loss is the exponential weakening proved above. -/
theorem sourceTailDecay_le_supportedHolder {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hνpos : 0 < ν) (hν : ν ^ 2 = tailEnergy E b r)
    (hδ : 0 < δ) (x : ℝ × ℝ) :
    ENNReal.ofReal
        (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^
          (((3 - r : ℕ) : ℝ) / 3)) *
      (∏ j ∈ nonzeroTailSupport E r,
        ENNReal.ofReal (tailDecayFactor (E j) (b j) x.1 x.2)) ≤
      supportedTailHolderProduct E b r ν δ x ^
        (((3 - r : ℕ) : ℝ) / 3) := by
  rw [supportedTailHolderProduct_powered_eq
    E b r hr ν δ hνpos hν hδ x]
  gcongr
  exact tailDecayFactor_le_holderWeakened r hr (E j) (b j) x.1 x.2

/-- A dominant coordinate contributes exactly one third of the common kernel
and one copy of the source dominant decay after the first Hölder power. -/
theorem dominantHolderCoordinate_rpow_eq {n : ℕ}
    (E b : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (j : Fin n) (x : ℝ × ℝ) :
    dominantHolderCoordinate E b δ j x ^ ((1 : ℝ) / 3) =
      ENNReal.ofReal
        (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
          dominantDecayFactor (E j) (b j) x.2) := by
  let K := (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)
  let D := dominantDecayFactor (E j) (b j) x.2
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hD : 0 < D := by
    dsimp [D, dominantDecayFactor]
    positivity
  unfold dominantHolderCoordinate
  rw [dominantCubedDecay_eq_pow]
  change ENNReal.ofReal (K * D ^ 3) ^ ((1 : ℝ) / 3) =
    ENNReal.ofReal (K ^ ((1 : ℝ) / 3) * D)
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hK (pow_pos hD 3))]
  apply congrArg ENNReal.ofReal
  rw [Real.mul_rpow hK.le (pow_nonneg hD.le 3)]
  rw [← Real.rpow_natCast D 3, ← Real.rpow_mul hD.le]
  norm_num

/-- For ranks zero, one, and two, the characteristic envelope splits
into the explicitly selected dominant factors and the nonzero tail
support.  The hypotheses identifying `j₀,j₁` are used only to name the unique
indices of values zero and one; zero tail coefficients are then erased
exactly. -/
theorem selectionDecayProduct_eq_ordered {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    (ξ η : ℝ) :
    (∏ j : Fin n, if (j : ℕ) < r then
        dominantDecayFactor (E j) (b j) η
      else tailDecayFactor (E j) (b j) ξ η) =
      if r = 0 then
        ∏ j ∈ nonzeroTailSupport E r,
          tailDecayFactor (E j) (b j) ξ η
      else if r = 1 then
        dominantDecayFactor (E j₀) (b j₀) η *
          ∏ j ∈ nonzeroTailSupport E r,
            tailDecayFactor (E j) (b j) ξ η
      else
        dominantDecayFactor (E j₀) (b j₀) η *
          dominantDecayFactor (E j₁) (b j₁) η *
          ∏ j ∈ nonzeroTailSupport E r,
            tailDecayFactor (E j) (b j) ξ η := by
  have h0 (j : Fin n) : (j : ℕ) = 0 ↔ j = j₀ := by
    constructor
    · intro hj
      apply Fin.ext
      simpa only [hj₀] using hj
    · intro hj
      simp only [hj, hj₀]
  have h1 (j : Fin n) : (j : ℕ) = 1 ↔ j = j₁ := by
    constructor
    · intro hj
      apply Fin.ext
      simpa only [hj₁] using hj
    · intro hj
      simp only [hj, hj₁]
  have htail (s : ℕ) :
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < s),
          tailDecayFactor (E j) (b j) ξ η) =
        ∏ j ∈ nonzeroTailSupport E s,
          tailDecayFactor (E j) (b j) ξ η := by
    rw [show Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < s) =
        tailIndices n s by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailIndices,
        Nat.not_lt]]
    exact prod_tailDecayFactor_eq_prod_nonzeroTailSupport E b s ξ η
  interval_cases r
  · rw [Finset.prod_ite, htail]
    simp
  · have hdominant :
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < 1) = {j₀} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [← h0]
      omega
    rw [Finset.prod_ite, hdominant, htail]
    simp
  · have hdominant :
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < 2) = {j₀, j₁} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      rw [← h0, ← h1]
      omega
    have h01 : j₀ ≠ j₁ := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [Finset.prod_ite, hdominant, htail]
    simp [h01, mul_assoc]

/-- The source decay envelope with the common shifted kernel already
distributed according to the first Hölder exponents.  This is equal to the
undistributed source envelope by exponent addition; keeping the allocation
visible makes the pointwise comparison transparent. -/
def orderedHolderSourceEnvelope {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (δ : ℝ)
    (j₀ j₁ : Fin n) (x : ℝ × ℝ) : ℝ≥0∞ :=
  let K := (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)
  let T := ∏ j ∈ nonzeroTailSupport E r,
    ENNReal.ofReal (tailDecayFactor (E j) (b j) x.1 x.2)
  if r = 0 then ENNReal.ofReal (K ^ (1 : ℝ)) * T
  else if r = 1 then
    ENNReal.ofReal (K ^ ((1 : ℝ) / 3) *
      dominantDecayFactor (E j₀) (b j₀) x.2) *
    (ENNReal.ofReal (K ^ ((2 : ℝ) / 3)) * T)
  else
    ENNReal.ofReal (K ^ ((1 : ℝ) / 3) *
      dominantDecayFactor (E j₀) (b j₀) x.2) *
    ENNReal.ofReal (K ^ ((1 : ℝ) / 3) *
      dominantDecayFactor (E j₁) (b j₁) x.2) *
    (ENNReal.ofReal (K ^ ((1 : ℝ) / 3)) * T)

/-- The allocated source envelope is exactly the common shifted kernel times
the full selected decay product.  This is only bookkeeping: the nontrivial
inequality remains the exponential weakening in
`tailDecayFactor_le_holderWeakened`. -/
theorem orderedHolderSourceEnvelope_eq_kernel_mul_selectionDecayProduct
    {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (δ : ℝ)
    (hδ : 0 < δ)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    (x : ℝ × ℝ) :
    orderedHolderSourceEnvelope E b r δ j₀ j₁ x =
      ENNReal.ofReal
          ((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
        ENNReal.ofReal
          (∏ j : Fin n, if (j : ℕ) < r then
            dominantDecayFactor (E j) (b j) x.2
          else tailDecayFactor (E j) (b j) x.1 x.2) := by
  let K := (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)
  let T (s : ℕ) := ∏ j ∈ nonzeroTailSupport E s,
    tailDecayFactor (E j) (b j) x.1 x.2
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hKdef :
      (x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4) = K := rfl
  have hTofReal (s : ℕ) :
      ENNReal.ofReal (T s) =
        ∏ j ∈ nonzeroTailSupport E s,
          ENNReal.ofReal (tailDecayFactor (E j) (b j) x.1 x.2) := by
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => by
      unfold tailDecayFactor
      positivity
  rw [selectionDecayProduct_eq_ordered E b r hr j₀ j₁ hj₀ hj₁ x.1 x.2]
  change orderedHolderSourceEnvelope E b r δ j₀ j₁ x =
    ENNReal.ofReal K *
      ENNReal.ofReal
        (if r = 0 then T r
        else if r = 1 then
          dominantDecayFactor (E j₀) (b j₀) x.2 * T r
        else
          dominantDecayFactor (E j₀) (b j₀) x.2 *
            dominantDecayFactor (E j₁) (b j₁) x.2 * T r)
  interval_cases r
  · simp [orderedHolderSourceEnvelope, hKdef, T, hTofReal]
  · have hKsplit :
        K ^ ((1 : ℝ) / 3) * K ^ ((2 : ℝ) / 3) = K := by
      rw [← Real.rpow_add hK]
      norm_num
    have hdom0 :
        0 ≤ dominantDecayFactor (E j₀) (b j₀) x.2 := by
      unfold dominantDecayFactor
      positivity
    simp only [orderedHolderSourceEnvelope, hKdef, one_ne_zero, ite_false,
      ite_true]
    rw [← hTofReal,
      ENNReal.ofReal_mul hdom0,
      ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
    have hKsplit' := congrArg ENNReal.ofReal hKsplit
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)] at hKsplit'
    rw [← hKsplit']
    ac_rfl
  · have hKsplit :
        K ^ ((1 : ℝ) / 3) * K ^ ((1 : ℝ) / 3) *
            K ^ ((1 : ℝ) / 3) = K := by
      rw [← Real.rpow_add hK, ← Real.rpow_add hK]
      norm_num
    have hdom0 :
        0 ≤ dominantDecayFactor (E j₀) (b j₀) x.2 := by
      unfold dominantDecayFactor
      positivity
    have hdom1 :
        0 ≤ dominantDecayFactor (E j₁) (b j₁) x.2 := by
      unfold dominantDecayFactor
      positivity
    simp only [orderedHolderSourceEnvelope, hKdef, OfNat.ofNat_ne_zero,
      ite_false, OfNat.ofNat_ne_one]
    rw [← hTofReal,
      ENNReal.ofReal_mul (mul_nonneg hdom0 hdom1),
      ENNReal.ofReal_mul hdom0,
      ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _),
      ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
    have hKsplit' := congrArg ENNReal.ofReal hKsplit
    rw [ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_nonneg hK.le _)
          (Real.rpow_nonneg hK.le _)),
      ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)] at hKsplit'
    rw [← hKsplit']
    ac_rfl

/-- The reciprocal Fourier denominator is exactly the negative
three-quarter-power kernel used by the Hölder coordinates. -/
theorem shiftedDenominator_inv_eq_kernel (ξ δ : ℝ) (hδ : 0 < δ) :
    (ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)))⁻¹ =
      ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) := by
  have hbase : 0 < ξ ^ 2 + δ ^ 2 := by positivity
  rw [show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring,
    Real.rpow_neg hbase.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hbase _)]

/-- The characteristic-function estimate, divided by the exact
Fourier denominator, is bounded pointwise by `exp 1` times the allocated
source envelope.  This is the bridge from the contour estimate to the
unconditional Hölder analysis. -/
theorem shiftedCharFun_div_le_orderedHolderSourceEnvelope {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (δ : ℝ) (hδ : 0 < δ) (hδeq : δ = selectionDelta E b r)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    (ξ η a : ℝ) :
    ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ /
        ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)) ≤
      ENNReal.ofReal (Real.exp 1) *
        orderedHolderSourceEnvelope E b r δ j₀ j₁ (ξ, η) := by
  let P := ∏ j : Fin n, if (j : ℕ) < r then
    dominantDecayFactor (E j) (b j) η
  else tailDecayFactor (E j) (b j) ξ η
  have hnorm :
      ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ ≤ Real.exp 1 * P := by
    rw [hδeq]
    simpa only [P] using
      norm_weightedSquaresCharFun_selection_le E b r hr hthree ξ η a
  have henorm :
      ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ ≤
        ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal P := by
    calc
      ‖weightedSquaresCharFun E b r
          ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ =
          ENNReal.ofReal
            ‖weightedSquaresCharFun E b r
              ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ :=
        (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (Real.exp 1 * P) :=
        ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal P :=
        ENNReal.ofReal_mul (Real.exp_pos 1).le
  rw [div_eq_mul_inv, shiftedDenominator_inv_eq_kernel ξ δ hδ]
  calc
    ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ *
        ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ≤
      (ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal P) *
        ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp 1) *
        orderedHolderSourceEnvelope E b r δ j₀ j₁ (ξ, η) := by
      rw [orderedHolderSourceEnvelope_eq_kernel_mul_selectionDecayProduct
        E b r hr δ hδ j₀ j₁ hj₀ hj₁ (ξ, η)]
      change (ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal P) *
          ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) =
        ENNReal.ofReal (Real.exp 1) *
          (ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
            ENNReal.ofReal P)
      ac_rfl

/-- Pointwise source-to-Hölder comparison for all three selected
ranks.  Equality holds in the dominant factors and polynomial tail powers;
for ranks one and two only the negative tail exponential is weakened. -/
theorem orderedHolderSourceEnvelope_le_firstHolder {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hνpos : 0 < ν) (hν : ν ^ 2 = tailEnergy E b r)
    (hδ : 0 < δ) (j₀ j₁ : Fin n) (x : ℝ × ℝ) :
    orderedHolderSourceEnvelope E b r δ j₀ j₁ x ≤
      firstHolderIntegrand r
        (dominantHolderCoordinate E b δ j₀)
        (dominantHolderCoordinate E b δ j₁)
        (tailHolderProduct E b r ν δ) x := by
  rw [tailHolderProduct_eq_supportedTailHolderProduct]
  have htail := sourceTailDecay_le_supportedHolder
    E b r hr ν δ hνpos hν hδ x
  interval_cases r
  · simpa [orderedHolderSourceEnvelope, firstHolderIntegrand] using htail
  · have h10 : (1 : ℕ) ≠ 0 := by decide
    simp only [orderedHolderSourceEnvelope, firstHolderIntegrand, h10,
      ite_false, ite_true]
    rw [dominantHolderCoordinate_rpow_eq E b δ hδ j₀ x]
    norm_num at htail ⊢
    simpa only [neg_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_left htail
        (ENNReal.ofReal
          (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
            dominantDecayFactor (E j₀) (b j₀) x.2))
  · have h20 : (2 : ℕ) ≠ 0 := by decide
    have h21 : (2 : ℕ) ≠ 1 := by decide
    simp only [orderedHolderSourceEnvelope, firstHolderIntegrand, h20, h21,
      ite_false]
    rw [dominantHolderCoordinate_rpow_eq E b δ hδ j₀ x,
      dominantHolderCoordinate_rpow_eq E b δ hδ j₁ x]
    norm_num at htail ⊢
    simpa only [neg_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_left (mul_le_mul_left htail
        (ENNReal.ofReal
          (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
            dominantDecayFactor (E j₁) (b j₁) x.2)))
        (ENNReal.ofReal
          (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
            dominantDecayFactor (E j₀) (b j₀) x.2))

/-- Absolute shifted-integral bound for an ordered family with arbitrary zero
coefficients in the tail.  There is no coefficient-bound or integral-bound
hypothesis and no global `∀ j, E j ≠ 0` premise. -/
theorem ordered_shifted_integral_le_absolute {n : ℕ}
    (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1) :
    (∫⁻ x : ℝ × ℝ,
      firstHolderIntegrand (dominantSplitRank E b)
        (dominantHolderCoordinate E b
          (selectionDelta E b (dominantSplitRank E b)) j₀)
        (dominantHolderCoordinate E b
          (selectionDelta E b (dominantSplitRank E b)) j₁)
        (tailHolderProduct E b (dominantSplitRank E b)
          (dominantTailScale E b)
          (selectionDelta E b (dominantSplitRank E b))) x) ≤
      shiftedIntegralAbsoluteConstant := by
  let r := dominantSplitRank E b
  let ν := dominantTailScale E b
  let δ := selectionDelta E b r
  let C := shiftedIntegralAbsoluteConstant
  have hsel : DominantSelection E b r :=
    dominantSelection_dominantSplitRank E b hord
  have hr : r ≤ 2 := dominantSplitRank_le_two E b
  have hνpos : 0 < ν := dominantTailScale_pos E b hthree
  have hν : ν ^ 2 = tailEnergy E b r := dominantTailScale_sq E b
  have hδ : δ = 1 / (10 * ν ^ 2) := by
    simpa only [r, ν, δ] using selectionDelta_eq_dominantTailScale E b
  have hweight : ∀ j ∈ nonzeroTailSupport E r,
      ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1 := by
    intro j hj
    exact dominantSelection_three_sub_mul_tailHolderWeight_le_one E b r ν
      hsel hν j ((mem_nonzeroTailSupport E r j).mp hj).1
  have htail := supportedTailHolderProduct_lintegral_le_absolute
    E b r hr ν δ hνpos hν hδ hweight
  have hdom (j : Fin n) (hj : (j : ℕ) < r) :
      (∫⁻ x : ℝ × ℝ, dominantHolderCoordinate E b δ j x) ≤ C := by
    have hEj : E j ≠ 0 := dominantSplitRank_coefficient_ne_zero E b j (by
      simpa only [r] using hj)
    apply (dominantHolderCoordinate_lintegral_le E b ν δ j hEj hνpos hδ ?_).trans
      dominant_constant_le_absolute
    rw [hν]
    exact dominantSelection_tailEnergy_le hsel j hj
  have hassembly := shifted_integral_le_of_tail_bound r hr
    (dominantHolderCoordinate E b δ j₀)
    (dominantHolderCoordinate E b δ j₁)
    (supportedTailHolderProduct E b r ν δ)
    (dominantHolderCoordinate_aemeasurable E b δ j₀)
    (dominantHolderCoordinate_aemeasurable E b δ j₁)
    (supportedTailHolderProduct_aemeasurable E b r ν δ) C htail
  rw [tailHolderProduct_eq_supportedTailHolderProduct]
  change (∫⁻ x : ℝ × ℝ,
      firstHolderIntegrand r
        (dominantHolderCoordinate E b δ j₀)
        (dominantHolderCoordinate E b δ j₁)
        (supportedTailHolderProduct E b r ν δ) x) ≤ C
  interval_cases r
  · simpa [firstHolderIntegrand, C] using hassembly
  · have h₀ : (∫⁻ x : ℝ × ℝ,
        dominantHolderCoordinate E b δ j₀ x) ≤ C := hdom j₀ (by omega)
    apply hassembly.trans
    norm_num
    calc
      (∫⁻ x : ℝ × ℝ, dominantHolderCoordinate E b δ j₀ x) ^ ((1 : ℝ) / 3) *
          C ^ ((2 : ℝ) / 3) ≤
        C ^ ((1 : ℝ) / 3) * C ^ ((2 : ℝ) / 3) := by gcongr
      _ = C := by
        rw [← ENNReal.rpow_add_of_nonneg ((1 : ℝ) / 3) (2 / 3)
          (by norm_num) (by norm_num)]
        norm_num
  · have h₀ : (∫⁻ x : ℝ × ℝ,
        dominantHolderCoordinate E b δ j₀ x) ≤ C := hdom j₀ (by omega)
    have h₁ : (∫⁻ x : ℝ × ℝ,
        dominantHolderCoordinate E b δ j₁ x) ≤ C := hdom j₁ (by omega)
    apply hassembly.trans
    norm_num
    calc
      (∫⁻ x : ℝ × ℝ, dominantHolderCoordinate E b δ j₀ x) ^ ((1 : ℝ) / 3) *
          (∫⁻ x : ℝ × ℝ, dominantHolderCoordinate E b δ j₁ x) ^ ((1 : ℝ) / 3) *
          C ^ ((1 : ℝ) / 3) ≤
        C ^ ((1 : ℝ) / 3) * C ^ ((1 : ℝ) / 3) *
          C ^ ((1 : ℝ) / 3) := by gcongr
      _ = C := by
        rw [← ENNReal.rpow_add_of_nonneg ((1 : ℝ) / 3) ((1 : ℝ) / 3)
          (by norm_num) (by norm_num),
          ← ENNReal.rpow_add_of_nonneg ((1 : ℝ) / 3 + (1 : ℝ) / 3)
            ((1 : ℝ) / 3) (by norm_num) (by norm_num)]
        norm_num

/-- The canonical shifted characteristic-function majorant has an absolute
two-dimensional integral bound.  The constant is completely explicit and is
uniform in the centering parameter `a`; no nonvanishing assumption is imposed
on nominal tail coordinates. -/
theorem ordered_shifted_fourier_integral_le_absolute {n : ℕ}
    (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    (a : ℝ) :
    (∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
      ‖weightedSquaresCharFun E b (dominantSplitRank E b)
        ((ξ : ℂ) -
          selectionDelta E b (dominantSplitRank E b) * Complex.I)
        (η : ℂ) a‖ₑ /
      ENNReal.ofReal
        ((ξ ^ 2 + selectionDelta E b (dominantSplitRank E b) ^ 2) ^
          ((3 : ℝ) / 4))) ≤
      ENNReal.ofReal (Real.exp 1) * shiftedIntegralAbsoluteConstant := by
  let r := dominantSplitRank E b
  let ν := dominantTailScale E b
  let δ := selectionDelta E b r
  let f := firstHolderIntegrand r
    (dominantHolderCoordinate E b δ j₀)
    (dominantHolderCoordinate E b δ j₁)
    (tailHolderProduct E b r ν δ)
  have hr : r ≤ 2 := dominantSplitRank_le_two E b
  have hνpos : 0 < ν := dominantTailScale_pos E b hthree
  have hν : ν ^ 2 = tailEnergy E b r := dominantTailScale_sq E b
  have hδ : 0 < δ := selectionDelta_pos E b r hr hthree
  have hd₀ := dominantHolderCoordinate_aemeasurable E b δ j₀
  have hd₁ := dominantHolderCoordinate_aemeasurable E b δ j₁
  have ht := tailHolderProduct_aemeasurable E b r ν δ
  have hf : AEMeasurable f (volume : Measure (ℝ × ℝ)) := by
    dsimp [f]
    interval_cases r
    · change AEMeasurable (tailHolderProduct E b 0 ν δ) volume
      exact ht
    · exact (hd₀.pow_const _).mul (ht.pow_const _)
    · exact ((hd₀.pow_const _).mul (hd₁.pow_const _)).mul
        (ht.pow_const _)
  have hpoint (ξ η : ℝ) :
      ‖weightedSquaresCharFun E b r
          ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ /
          ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)) ≤
        ENNReal.ofReal (Real.exp 1) * f (ξ, η) := by
    refine (shiftedCharFun_div_le_orderedHolderSourceEnvelope
      E b r hr hthree δ hδ rfl j₀ j₁ hj₀ hj₁ ξ η a).trans ?_
    simpa only [mul_comm] using mul_le_mul_left
      (orderedHolderSourceEnvelope_le_firstHolder
        E b r hr ν δ hνpos hν hδ j₀ j₁ (ξ, η))
      (ENNReal.ofReal (Real.exp 1))
  have hcf : AEMeasurable
      (fun x : ℝ × ℝ => ENNReal.ofReal (Real.exp 1) * f x)
      (volume : Measure (ℝ × ℝ)) :=
    aemeasurable_const.mul hf
  change (∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
      ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ /
      ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))) ≤ _
  calc
    (∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
        ‖weightedSquaresCharFun E b r
          ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ /
        ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))) ≤
      ∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
        ENNReal.ofReal (Real.exp 1) * f (ξ, η) := by
          apply lintegral_mono
          intro η
          exact lintegral_mono fun ξ => hpoint ξ η
    _ = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (Real.exp 1) * f x := by
      exact (lintegral_prod_symm
        (fun x : ℝ × ℝ => ENNReal.ofReal (Real.exp 1) * f x) hcf).symm
    _ = ENNReal.ofReal (Real.exp 1) * ∫⁻ x : ℝ × ℝ, f x := by
      rw [lintegral_const_mul' _ _ (by simp)]
    _ ≤ ENNReal.ofReal (Real.exp 1) * shiftedIntegralAbsoluteConstant := by
      gcongr
      simpa only [r, ν, δ, f] using
        ordered_shifted_integral_le_absolute E b hord hthree j₀ j₁ hj₀ hj₁

/-- The contour-shift liminf theorem specialized to the canonical ordered
selection.  In particular, its continuation hypotheses are derived from the
three-active-coordinate regime, and it makes no global nonvanishing
assumption on the nominal tail coefficients. -/
theorem ordered_liminf_fourier_le_shifted {n : ℕ}
    (E b : Fin n → ℝ)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Filter.liminf
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ ξ : ℝ,
          weightedSquaresCharFun E b (dominantSplitRank E b) ξ (η : ℂ) a /
            ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) +
              (ξ : ℂ) * Complex.I) ^
              (((3 / 2 + δ' : ℝ)) : ℂ))‖ₑ)
      (nhdsWithin 0 (Set.Ioi 0)) ≤
    ∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
      ‖weightedSquaresCharFun E b (dominantSplitRank E b)
        ((ξ : ℂ) -
          selectionDelta E b (dominantSplitRank E b) * Complex.I)
        (η : ℂ) a‖ₑ /
      ENNReal.ofReal
        ((ξ ^ 2 + selectionDelta E b (dominantSplitRank E b) ^ 2) ^
          ((3 : ℝ) / 4)) := by
  let r := dominantSplitRank E b
  have hr : r ≤ 2 := dominantSplitRank_le_two E b
  exact liminf_fourier_le_shifted E b r hr hthree hε
    (selectionDelta_pos E b r hr hthree)
    (selectionDelta_coefficient_lt E b r hr hthree) a

/-- Full ordered APSSS Fourier-tail estimate through the contour-shift
liminf.  It is uniform in `a`, allows zero nominal tail coefficients, and has
the explicit universal constant from the scalar Hölder analysis.  Turning
this analytic liminf bound into the final probability statement remains the
separate low-rank/Fourier-inversion step. -/
theorem ordered_liminf_fourier_le_absolute {n : ℕ}
    (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Filter.liminf
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ ξ : ℝ,
          weightedSquaresCharFun E b (dominantSplitRank E b) ξ (η : ℂ) a /
            ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) +
              (ξ : ℂ) * Complex.I) ^
              (((3 / 2 + δ' : ℝ)) : ℂ))‖ₑ)
      (nhdsWithin 0 (Set.Ioi 0)) ≤
      ENNReal.ofReal (Real.exp 1) * shiftedIntegralAbsoluteConstant := by
  exact (ordered_liminf_fourier_le_shifted E b hthree hε a).trans
    (ordered_shifted_fourier_integral_le_absolute
      E b hord hthree j₀ j₁ hj₀ hj₁ a)

end PSSSNative.BlockBand.PSSS
