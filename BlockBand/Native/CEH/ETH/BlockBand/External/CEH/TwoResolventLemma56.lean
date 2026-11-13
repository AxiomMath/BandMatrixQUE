module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventStability
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEQuantitative
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Quantitative tensor step for CEH Lemma 5.6

This module separates the finite-dimensional part of the tensor
meta-argument in CEH Lemma 5.6 from its random-matrix input, which is not part of
this module.  Under replication by `I_d`, products, adjoints, imaginary parts,
two-resolvent words, and positive chains are preserved, and their normalized
traces have *zero* error for every positive `d`.

The final section is a quantitative (rather than bare `lim`) transfer API.  It
shows separately how each of the five displayed bounds follows from a
`C/(d+1)` comparison with the concrete replicated resolvent word and its
finite-dimensional Ward estimate.  The comparison hypotheses are quantitative
single-resolvent GUE comparisons, taken as hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-!
## Replication of all matrix operations used in the meta-argument
-/

@[simp] theorem tensorReplicate_one {N d : ℕ} :
    tensorReplicate d (1 : Matrix (Fin N) (Fin N) ℂ) =
      (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [tensorReplicate, Matrix.kronecker, Matrix.one_apply]
  by_cases hij : i = j <;> by_cases hab : a = b <;> simp [hij, hab, Prod.ext_iff]

@[simp] theorem tensorReplicate_add {N d : ℕ}
    (X Y : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (X + Y) = tensorReplicate d X + tensorReplicate d Y := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [tensorReplicate, Matrix.kronecker, add_mul]

@[simp] theorem tensorReplicate_sub {N d : ℕ}
    (X Y : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (X - Y) = tensorReplicate d X - tensorReplicate d Y := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [tensorReplicate, Matrix.kronecker, sub_mul]

@[simp] theorem tensorReplicate_smul {N d : ℕ} (c : ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (c • X) = c • tensorReplicate d X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [tensorReplicate, Matrix.kronecker, mul_assoc]

@[simp] theorem tensorReplicate_adjoint {N d : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d Xᴴ = (tensorReplicate d X)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [tensorReplicate, Matrix.kronecker, Matrix.conjTranspose_apply]
  by_cases hab : a = b
  · simp [hab, mul_comm]
  · have hba : b ≠ a := fun h => hab h.symm
    simp [hab, hba]

/-- Adjoint selection on an arbitrary square index type. -/
def chooseAdjointOn {ι : Type*} (c : AdjointChoice)
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  match c with
  | .plain => X
  | .adjoint => Xᴴ

@[simp] theorem tensorReplicate_chooseAdjoint {N d : ℕ}
    (c : AdjointChoice) (X : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (chooseAdjoint c X) =
      chooseAdjointOn c (tensorReplicate d X) := by
  cases c <;> simp [chooseAdjoint, chooseAdjointOn]

@[simp] theorem tensorReplicate_imaginaryPart {N d : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (CEHNative.BlockBand.matrixImaginaryPart X) =
      CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d X) := by
  simp [CEHNative.BlockBand.matrixImaginaryPart]

/-- Every concrete adjoint constellation commutes with tensor replication. -/
theorem tensorReplicate_twoResolventWord {N d : ℕ}
    (c₁ c₂ : AdjointChoice) (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (twoResolventWord c₁ c₂ G₁ A G₂) =
      chooseAdjointOn c₁ (tensorReplicate d G₁) * tensorReplicate d A *
        chooseAdjointOn c₂ (tensorReplicate d G₂) := by
  simp [twoResolventWord, tensorReplicate_mul]

/-- The normalized trace of every replicated resolvent word is exactly the
original normalized trace; there is no limiting error in the tensor
meta-argument. -/
theorem productNTrace_replicated_twoResolventWord {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (c₁ c₂ : AdjointChoice)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    productNTrace (chooseAdjointOn c₁ (tensorReplicate d G₁) *
      tensorReplicate d A * chooseAdjointOn c₂ (tensorReplicate d G₂)) =
      twoResolventObservable c₁ c₂ G₁ A G₂ := by
  rw [← tensorReplicate_twoResolventWord]
  exact productNTrace_tensorReplicate hN hd _

/-- The two-resolvent approximation on the product index space.  Its
trace functional is `productNTrace`, so this is the `dN` analogue of
(5.12). -/
def productTwoResolventApprox {N d : ℕ} (lambda : ℂ)
    (M₁ A M₂ :
      Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) :
      Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  let word := M₁ * A * M₂
  let pair := M₁ * M₂
  word + (lambda ^ 2 *
    (productNTrace word /
      stabilityDenominator lambda (productNTrace pair))) • pair

/-- Exact finite-`d` version of the CEH tensor meta-argument: not only its trace but the
entire deterministic two-resolvent approximation is replicated. -/
theorem productTwoResolventApprox_tensorReplicate {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    productTwoResolventApprox lambda (tensorReplicate d M₁)
        (tensorReplicate d A) (tensorReplicate d M₂) =
      tensorReplicate d (twoResolventApprox lambda M₁ A M₂) := by
  dsimp [productTwoResolventApprox, twoResolventApprox]
  have hword : tensorReplicate d M₁ * tensorReplicate d A *
      tensorReplicate d M₂ = tensorReplicate d (M₁ * A * M₂) := by
    rw [← tensorReplicate_mul, ← tensorReplicate_mul]
  have hpair : tensorReplicate d M₁ * tensorReplicate d M₂ =
      tensorReplicate d (M₁ * M₂) := by
    rw [tensorReplicate_mul]
  rw [hword, hpair, productNTrace_tensorReplicate hN hd,
    productNTrace_tensorReplicate hN hd]
  simp

/-- Consequently the approximation's normalized trace is independent of the
replication size exactly, not merely in the `d → ∞` limit. -/
theorem productNTrace_productTwoResolventApprox_tensorReplicate {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    productNTrace
        (productTwoResolventApprox lambda (tensorReplicate d M₁)
          (tensorReplicate d A) (tensorReplicate d M₂)) =
      NTrace (twoResolventApprox lambda M₁ A M₂) := by
  rw [productTwoResolventApprox_tensorReplicate hN hd]
  exact productNTrace_tensorReplicate hN hd _

/-- The positive four-factor chain also commutes with replication. -/
theorem tensorReplicate_positiveChain {N d : ℕ}
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d
        (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
          CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ) =
      CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₁) *
        tensorReplicate d A *
        CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₂) *
        (tensorReplicate d A)ᴴ := by
  simp [tensorReplicate_mul]

/-- Exact normalized-trace invariance for the positive chain used in the tensor
meta-argument. -/
theorem productNTrace_replicated_positiveChain {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    productNTrace
        (CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₁) *
          tensorReplicate d A *
          CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₂) *
          (tensorReplicate d A)ᴴ) =
      NTrace (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
        CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ) := by
  rw [← tensorReplicate_positiveChain]
  exact productNTrace_tensorReplicate hN hd _

/-- Quantitative form of deterministic tensor convergence: its error is zero,
and hence is bounded by every nonnegative requested tolerance. -/
theorem replicatedWord_error_le {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (c₁ c₂ : AdjointChoice)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖productNTrace (chooseAdjointOn c₁ (tensorReplicate d G₁) *
        tensorReplicate d A * chooseAdjointOn c₂ (tensorReplicate d G₂)) -
      twoResolventObservable c₁ c₂ G₁ A G₂‖ ≤ ε := by
  rw [productNTrace_replicated_twoResolventWord hN hd]
  simpa using hε

/-- Quantitative zero-error convergence for the replicated positive chain. -/
theorem replicatedPositiveChain_error_le {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖productNTrace
        (CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₁) *
          tensorReplicate d A *
          CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₂) *
          (tensorReplicate d A)ᴴ) -
      NTrace (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
        CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ)‖ ≤ ε := by
  rw [productNTrace_replicated_positiveChain hN hd]
  simpa using hε

/-!
## Weighted Ward–Schwarz comparisons with source normalization
-/

/-- A weighted finite spectral average with the normalization `1/N`. -/
def weightedSpectralAverage {N : ℕ}
    (w : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, w i

/-- Weighted Cauchy–Schwarz in normalized-trace normalization. -/
theorem weightedSpectralSchwarz {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt (weightedSpectralAverage (fun i => w i * u i ^ 2)) *
      Real.sqrt (weightedSpectralAverage (fun i => w i * v i ^ 2)) := by
  let a : Fin N → ℝ := fun i => Real.sqrt (w i) * u i
  let b : Fin N → ℝ := fun i => Real.sqrt (w i) * v i
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hab := spectralSchwarzChain_abs a b
  unfold weightedSpectralAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
  have huv : (∑ i, a i * b i) = ∑ i, w i * u i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, b]
    rw [show Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i) =
      (Real.sqrt (w i) * Real.sqrt (w i)) * u i * v i by ring,
      Real.mul_self_sqrt (hw i)]
  have hu : (∑ i, a i ^ 2) = ∑ i, w i * u i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hv : (∑ i, b i ^ 2) = ∑ i, w i * v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [b]
    rw [mul_pow, Real.sq_sqrt (hw i)]
  rw [huv, hu, hv] at hab
  have hsu :
      Real.sqrt ((N : ℝ)⁻¹ * ∑ i, w i * u i ^ 2) =
        Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (∑ i, w i * u i ^ 2) :=
    Real.sqrt_mul (inv_nonneg.mpr hNreal.le) _
  have hsv :
      Real.sqrt ((N : ℝ)⁻¹ * ∑ i, w i * v i ^ 2) =
        Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (∑ i, w i * v i ^ 2) :=
    Real.sqrt_mul (inv_nonneg.mpr hNreal.le) _
  calc
    (N : ℝ)⁻¹ * |∑ i, w i * u i * v i| ≤
        (N : ℝ)⁻¹ *
          (Real.sqrt (∑ i, w i * u i ^ 2) *
            Real.sqrt (∑ i, w i * v i ^ 2)) :=
      mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hNreal.le)
    _ = Real.sqrt ((N : ℝ)⁻¹ * ∑ i, w i * u i ^ 2) *
        Real.sqrt ((N : ℝ)⁻¹ * ∑ i, w i * v i ^ 2) := by
      rw [hsu, hsv]
      have hi : Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (N : ℝ)⁻¹ =
          (N : ℝ)⁻¹ :=
        Real.mul_self_sqrt (inv_nonneg.mpr hNreal.le)
      calc
        (N : ℝ)⁻¹ * (Real.sqrt (∑ i, w i * u i ^ 2) *
            Real.sqrt (∑ i, w i * v i ^ 2)) =
          (Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (N : ℝ)⁻¹) *
            (Real.sqrt (∑ i, w i * u i ^ 2) *
              Real.sqrt (∑ i, w i * v i ^ 2)) :=
            congrArg (fun z => z * (Real.sqrt (∑ i, w i * u i ^ 2) *
              Real.sqrt (∑ i, w i * v i ^ 2))) hi.symm
        _ = _ := by ring

/-- Common exact Ward scaling calculation. -/
theorem weightedWard_scale {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {R S s₂ : ℝ}
    (hu : weightedSpectralAverage (fun i => w i * u i ^ 2) ≤ R)
    (hv : weightedSpectralAverage (fun i => w i * v i ^ 2) ≤ S * s₂ ^ 2)
    (hS : 0 ≤ S) (hs₂ : 0 ≤ s₂) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt R * Real.sqrt S * s₂ := by
  calc
    _ ≤ Real.sqrt (weightedSpectralAverage (fun i => w i * u i ^ 2)) *
        Real.sqrt (weightedSpectralAverage (fun i => w i * v i ^ 2)) :=
      weightedSpectralSchwarz hN w u v hw
    _ ≤ Real.sqrt R * Real.sqrt (S * s₂ ^ 2) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hS, Real.sqrt_sq_eq_abs, abs_of_nonneg hs₂]
      ring

/-- Exact Ward normalization: if the two weighted square chains are at the
CEH scales `ρ₂/η₁` and `ρ₁ρ₂ s₂²`, their mixed chain is at the first displayed
scale. -/
theorem weightedWard_pp {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {rho₁ rho₂ eta₁ s₂ : ℝ}
    (hu : weightedSpectralAverage (fun i => w i * u i ^ 2) ≤ rho₂ / eta₁)
    (hv : weightedSpectralAverage (fun i => w i * v i ^ 2) ≤
      rho₁ * rho₂ * s₂ ^ 2)
    (hρ : 0 ≤ rho₁ * rho₂) (hs₂ : 0 ≤ s₂) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂ := by
  exact weightedWard_scale hN w u v hw hu hv hρ hs₂

/-- The `--` Ward comparison, with the roles of the two heights exchanged. -/
theorem weightedWard_mm {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {rho₁ rho₂ eta₂ s₂ : ℝ}
    (hu : weightedSpectralAverage (fun i => w i * u i ^ 2) ≤ rho₁ / eta₂)
    (hv : weightedSpectralAverage (fun i => w i * v i ^ 2) ≤
      rho₁ * rho₂ * s₂ ^ 2)
    (hρ : 0 ≤ rho₁ * rho₂) (hs₂ : 0 ≤ s₂) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂ := by
  exact weightedWard_scale hN w u v hw hu hv hρ hs₂

/-- Mixed-sign comparison at the maximum of the two Ward scales. -/
theorem weightedWard_mp {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {rho₁ rho₂ eta₁ eta₂ s₂ : ℝ}
    (hu : weightedSpectralAverage (fun i => w i * u i ^ 2) ≤
      max (rho₁ / eta₂) (rho₂ / eta₁))
    (hv : weightedSpectralAverage (fun i => w i * v i ^ 2) ≤
      rho₁ * rho₂ * s₂ ^ 2)
    (hρ : 0 ≤ rho₁ * rho₂) (hs₂ : 0 ≤ s₂) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂ := by
  exact weightedWard_scale hN w u v hw hu hv hρ hs₂

/-- Hatted one-observable comparison at the minimum of the Ward scales. -/
theorem weightedWard_hat {N : ℕ} (hN : 0 < N)
    (w u v : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {rho₁ rho₂ eta₁ eta₂ s₂ : ℝ}
    (hu : weightedSpectralAverage (fun i => w i * u i ^ 2) ≤
      min (rho₁ / eta₂) (rho₂ / eta₁))
    (hv : weightedSpectralAverage (fun i => w i * v i ^ 2) ≤
      rho₁ * rho₂ * s₂ ^ 2)
    (hρ : 0 ≤ rho₁ * rho₂) (hs₂ : 0 ≤ s₂) :
    |weightedSpectralAverage (fun i => w i * u i * v i)| ≤
      Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂ := by
  exact weightedWard_scale hN w u v hw hu hv hρ hs₂

/-- Positive-chain comparison in the exact `ρ₁ρ₂s₂²` normalization. -/
theorem weightedWard_positive {N : ℕ}
    (w q : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    {rho₁ rho₂ s₂ : ℝ}
    (hq : ∀ i, q i ≤ rho₁ * rho₂ * s₂ ^ 2) :
    weightedSpectralAverage (fun i => w i * q i) ≤
      weightedSpectralAverage w * (rho₁ * rho₂ * s₂ ^ 2) := by
  unfold weightedSpectralAverage
  have hsum : ∑ i, w i * q i ≤ ∑ i, w i * (rho₁ * rho₂ * s₂ ^ 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq i) (hw i)
  rw [← Finset.sum_mul] at hsum
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N)))

/-!
## Quantitative removal of the tensor size
-/

/-- A uniform `C/(d+1)` error can be removed without appealing to an informal
meta-limit. -/
theorem le_of_le_add_inv_succ (x B C : ℝ) (hC : 0 ≤ C)
    (h : ∀ d : ℕ, x ≤ B + C / (d + 1 : ℝ)) : x ≤ B := by
  apply le_of_forall_sub_le
  intro ε hε
  by_cases hC0 : C = 0
  · have hx : x ≤ B := by simpa [hC0] using h 0
    linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    obtain ⟨d, hd⟩ := exists_nat_one_div_lt (div_pos hε hCpos)
    have herr : C / (d + 1 : ℝ) < ε := by
      rw [div_eq_mul_inv]
      have := mul_lt_mul_of_pos_left hd hCpos
      calc
        C * (↑d + 1)⁻¹ < C * (ε / C) := by simpa [one_div] using this
        _ = ε := by field_simp [hC0]
    linarith [h d]

/-- Quantitative comparison plus a finite-dimensional Ward bound. -/
theorem norm_le_of_tensorComparison
    (target : ℂ) (finiteWord : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤ B) : ‖target‖ ≤ B := by
  apply le_of_le_add_inv_succ ‖target‖ B C hC
  intro d
  calc
    ‖target‖ = ‖(target - finiteWord d) + finiteWord d‖ := by ring_nf
    _ ≤ ‖target - finiteWord d‖ + ‖finiteWord d‖ := norm_add_le _ _
    _ ≤ C / (d + 1 : ℝ) + B := add_le_add (hcompare d) (hward d)
    _ = B + C / (d + 1 : ℝ) := by ring

/-!
The next five theorems export the five CEH scales separately.  Their
`hcompare` hypotheses are the quantitative single-resolvent GUE comparisons;
`hward` is the finite-dimensional Ward conclusion, not the target MDE bound.
-/

theorem lemma56_bound_pp
    (target : ℂ) (finiteWord : ℕ → ℂ) (C rho₁ rho₂ eta₁ s₂ : ℝ)
    (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤
      Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂) :
    ‖target‖ ≤ Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_le_of_tensorComparison target finiteWord _ C hC hcompare hward

theorem lemma56_bound_mm
    (target : ℂ) (finiteWord : ℕ → ℂ) (C rho₁ rho₂ eta₂ s₂ : ℝ)
    (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤
      Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂) :
    ‖target‖ ≤ Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_le_of_tensorComparison target finiteWord _ C hC hcompare hward

theorem lemma56_bound_mp
    (target : ℂ) (finiteWord : ℕ → ℂ) (C rho₁ rho₂ eta₁ eta₂ s₂ : ℝ)
    (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤
      Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) :
    ‖target‖ ≤ Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
      Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_le_of_tensorComparison target finiteWord _ C hC hcompare hward

theorem lemma56_bound_hat
    (target : ℂ) (finiteWord : ℕ → ℂ) (C rho₁ rho₂ eta₁ eta₂ s₂ : ℝ)
    (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤
      Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) :
    ‖target‖ ≤ Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
      Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_le_of_tensorComparison target finiteWord _ C hC hcompare hward

theorem lemma56_bound_positive
    (target : ℂ) (finiteWord : ℕ → ℂ) (C rho₁ rho₂ s₂ : ℝ)
    (hC : 0 ≤ C)
    (hcompare : ∀ d, ‖target - finiteWord d‖ ≤ C / (d + 1 : ℝ))
    (hward : ∀ d, ‖finiteWord d‖ ≤ rho₁ * rho₂ * s₂ ^ 2) :
    ‖target‖ ≤ rho₁ * rho₂ * s₂ ^ 2 :=
  norm_le_of_tensorComparison target finiteWord _ C hC hcompare hward

/-- The five bounds of CEH Lemma 5.6 together. -/
theorem lemma56_five_bounds
    (tpp tmm tmp that tpos : ℂ)
    (fpp fmm fmp fhat fpos : ℕ → ℂ)
    (C rho₁ rho₂ eta₁ eta₂ s₂ : ℝ) (hC : 0 ≤ C)
    (hpp : ∀ d, ‖tpp - fpp d‖ ≤ C / (d + 1 : ℝ))
    (hmm : ∀ d, ‖tmm - fmm d‖ ≤ C / (d + 1 : ℝ))
    (hmp : ∀ d, ‖tmp - fmp d‖ ≤ C / (d + 1 : ℝ))
    (hhat : ∀ d, ‖that - fhat d‖ ≤ C / (d + 1 : ℝ))
    (hpos : ∀ d, ‖tpos - fpos d‖ ≤ C / (d + 1 : ℝ))
    (wpp : ∀ d, ‖fpp d‖ ≤ Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂)
    (wmm : ∀ d, ‖fmm d‖ ≤ Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂)
    (wmp : ∀ d, ‖fmp d‖ ≤ Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) * Real.sqrt (rho₁ * rho₂) * s₂)
    (what : ∀ d, ‖fhat d‖ ≤ Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) * Real.sqrt (rho₁ * rho₂) * s₂)
    (wpos : ∀ d, ‖fpos d‖ ≤ rho₁ * rho₂ * s₂ ^ 2) :
    (‖tpp‖ ≤ Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖tmm‖ ≤ Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖tmp‖ ≤ Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖that‖ ≤ Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖tpos‖ ≤ rho₁ * rho₂ * s₂ ^ 2) := by
  exact ⟨lemma56_bound_pp tpp fpp C rho₁ rho₂ eta₁ s₂ hC hpp wpp,
    lemma56_bound_mm tmm fmm C rho₁ rho₂ eta₂ s₂ hC hmm wmm,
    lemma56_bound_mp tmp fmp C rho₁ rho₂ eta₁ eta₂ s₂ hC hmp wmp,
    lemma56_bound_hat that fhat C rho₁ rho₂ eta₁ eta₂ s₂ hC hhat what,
    lemma56_bound_positive tpos fpos C rho₁ rho₂ s₂ hC hpos wpos⟩

end CEHNative.BlockBand.External.CEH
