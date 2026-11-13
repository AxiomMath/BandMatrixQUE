module

public import BlockBand.SourceProcess.LengthCont.OneLayer.FarUpdate
public import BlockBand.SourceProcess.ComplexSourceLaw.SourceBound

/-!
# The source data in unit-frame coordinates and its exact one-layer increment

At length `n`, with all probes born (`β_j = ⌊Wτ_j⌋₊ < n`), the probe column `j` is
`√m_j · unitTag W n β_j g_j`, the frame column is `√m_j · fᵢ` with `fⱼ = RawTag.frame …`, and
with `μ_{ik} = √m_i √m_k`:
* `𝒦_{ik} = μ_{ik} · rawForm` (`sourceK_eq`);
* `M_{ik} = (𝒦_{ik} - conj 𝒦_{ki}) / (z̄ - z)` (`sourceM_eq`, Hermitian blocks);
* `B_{ik} = M_{ik} - μ_{ik} Fd_{ik}` (`sourceB_eq`), `Fd_{ik} = Σ_y conj(d_i y) d_k y`;
* `J_{ik} = μ_{ik} (Fd_{ik} - Fe_{ik})` (`sourceJ_eq`, `𝕊` unitary), `Fe` the same with `e`.
Then the exact increment `complexSourceData (n+1) - complexSourceData n` is written with the
length-`n` frames and the fresh `Δ` (`ae_incr_eq`, a.s. on `probedPathLaw`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.RawTag BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ComplexOrder ComplexConjugate

variable {W : ℕ}

/-- Birth index `⌊Wτ_j⌋₊` of probe `j`. -/
def birth {np : ℕ} (W : ℕ) (τ : Fin np → ℝ) (j : Fin np) : ℕ := ⌊(W : ℝ) * τ j⌋₊

/-- The mass factor `μ_{ik} = √m_i √m_k`. -/
def massF {np : ℕ} (m : Fin np → ℝ) (i k : Fin np) : ℂ :=
  ((Real.sqrt (m i) * Real.sqrt (m k) : ℝ) : ℂ)

/-- The far Gram `Fd_{ik} = Σ_y conj(d_i y) d_k y`. -/
def gramOf (u v : Fin W → ℂ) : ℂ := ∑ y, star (u y) * v y

theorem probeColumns_col {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ)
    (j : Fin np) (hm : 0 ≤ m j) (hβ : birth W τ j < n) :
    (fun x => probeColumns W n τ m g x j) =
      ((Real.sqrt (m j) : ℝ) : ℂ) • unitTag W n (birth W τ j) (g j) := by
  funext x
  simp only [probeColumns, unitTag, Pi.smul_apply, smul_eq_mul]
  rw [show ⌊(W : ℝ) * τ j⌋₊ = birth W τ j from rfl]
  by_cases h : x.1.val = n - 1 - birth W τ j
  · simp only [hβ, h, and_self, ↓reduceIte]
    rw [div_eq_mul_one_div, Real.sqrt_mul hm, Complex.ofReal_mul]
    ring
  · simp [h]

theorem probeFrame_col {np : ℕ} (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (j : Fin np) (hm : 0 ≤ m j) (hβ : birth W τ j < n) (c : Fin 2 × Fin W) :
    probeFrame b E W n τ m x c j =
      ((Real.sqrt (m j) : ℝ) : ℂ) * frame b E W n (birth W τ j) x.1 (x.2 j) c := by
  have h := congrFun (probeColumns_col n τ m x.2 j hm hβ)
  simp only [probeFrame, Matrix.mul_apply, frame, mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [h y, Pi.smul_apply, smul_eq_mul]
  ring

/-- Entries of `Aᴴ M A` as bilinear forms of columns. -/
theorem sandwich_apply {ι κ : Type*} [Fintype ι] (A : Matrix ι κ ℂ) (M : Matrix ι ι ℂ)
    (i k : κ) : (Aᴴ * M * A) i k = star (fun x => A x i) ⬝ᵥ (M *ᵥ fun x => A x k) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem sourceK_eq {np : ℕ} (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (hm : ∀ j, 0 ≤ m j) (i k : Fin np) (hi : birth W τ i < n) (hk : birth W τ k < n) :
    complexSourceData b E W n τ m x 0 i k =
      massF m i k * rawForm b E W n (birth W τ i) (birth W τ k) x.1 (x.2 i) (x.2 k) := by
  simp only [complexSourceData, Matrix.cons_val_zero, complexSourceK]
  rw [sandwich_apply, probeColumns_col n τ m x.2 i (hm i) hi,
    probeColumns_col n τ m x.2 k (hm k) hk, rawForm, massF, star_smul, mulVec_smul,
    smul_dotProduct, dotProduct_smul, Complex.ofReal_mul]
  simp only [RCLike.star_def, Complex.conj_ofReal, smul_eq_mul]
  ring

/-- `M = (𝒦 - 𝒦ᴴ)/(z̄ - z)` entrywise. -/
theorem sourceM_eq {np : ℕ} (b E : ℝ) (hη : 0 < etaZ b E) (n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) (i k : Fin np) :
    complexSourceData b E W n τ m x 1 i k =
      (complexSourceData b E W n τ m x 0 i k - star (complexSourceData b E W n τ m x 0 k i)) /
        (conj (boundaryZ b E) - boundaryZ b E) := by
  have h := congrFun (congrFun (kc_sub_conjTranspose b E n τ m x hA) i) k
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    smul_eq_mul] at h
  have hne : conj (boundaryZ b E) - boundaryZ b E ≠ 0 := by
    rw [conj_boundaryZ_sub]
    have : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simp [this]
  simp only [complexSourceData, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eq_div_iff hne, h]
  ring

/-- `(VᴴPV)_{ik} = (VᴴV)_{ik} - Σ_y conj V_{(1,y) i} V_{(1,y) k}`. -/
theorem near_sandwich_apply {κ : Type*} (V : Matrix (Fin 2 × Fin W) κ ℂ) (i k : κ) :
    (Vᴴ * nearProjection W * V) i k =
      (Vᴴ * V) i k - ∑ y, star (V (1, y) i) * V (1, y) k := by
  simp only [Matrix.mul_apply, nearProjection, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp

theorem far_sum_frame {np : ℕ} (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (hm : ∀ j, 0 ≤ m j) (i k : Fin np) (hi : birth W τ i < n) (hk : birth W τ k < n) :
    ∑ y, star (probeFrame b E W n τ m x (1, y) i) * probeFrame b E W n τ m x (1, y) k =
      massF m i k * gramOf (farL b E W n (birth W τ i) x.1 (x.2 i))
        (farL b E W n (birth W τ k) x.1 (x.2 k)) := by
  simp only [probeFrame_col b E n τ m x _ (hm _) hi, probeFrame_col b E n τ m x _ (hm _) hk,
    gramOf, farL, massF, Finset.mul_sum, star_mul', Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [RCLike.star_def, Complex.conj_ofReal]
  ring

theorem sourceB_eq {np : ℕ} (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (hm : ∀ j, 0 ≤ m j) (i k : Fin np) (hi : birth W τ i < n) (hk : birth W τ k < n) :
    complexSourceData b E W n τ m x 2 i k = complexSourceData b E W n τ m x 1 i k -
      massF m i k * gramOf (farL b E W n (birth W τ i) x.1 (x.2 i))
        (farL b E W n (birth W τ k) x.1 (x.2 k)) := by
  change ((probeFrame b E W n τ m x)ᴴ * nearProjection W * probeFrame b E W n τ m x) i k =
    ((probeFrame b E W n τ m x)ᴴ * probeFrame b E W n τ m x) i k - _
  rw [near_sandwich_apply, far_sum_frame b E n τ m x hm i k hi hk]

theorem sourceJ_eq {np : ℕ} (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (hA : ∀ k, (x.1.1 k).IsHermitian) (hm : ∀ j, 0 ≤ m j) (i k : Fin np)
    (hi : birth W τ i < n) (hk : birth W τ k < n) :
    complexSourceData b E W n τ m x 3 i k =
      massF m i k * (gramOf (farL b E W n (birth W τ i) x.1 (x.2 i))
        (farL b E W n (birth W τ k) x.1 (x.2 k)) -
        gramOf (farR b E W n (birth W τ i) x.1 (x.2 i))
          (farR b E W n (birth W τ k) x.1 (x.2 k))) := by
  have hU := conjTranspose_mul_scattering b E n x.1 hA
  have e2 : (scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x)ᴴ *
      (scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x) =
      (probeFrame b E W n τ m x)ᴴ * probeFrame b E W n τ m x := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (scatteringMatrix b E W n x.1)ᴴ,
      hU, Matrix.one_mul]
  have e3 : ∀ (j : Fin np), birth W τ j < n → ∀ y,
      (scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x) (1, y) j =
      ((Real.sqrt (m j) : ℝ) : ℂ) * farR b E W n (birth W τ j) x.1 (x.2 j) y := by
    intro j hj y
    simp only [Matrix.mul_apply, farR, mulVec, dotProduct, Finset.mul_sum,
      probeFrame_col b E n τ m x j (hm j) hj]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have e5 : ∑ y, star ((scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x) (1, y) i) *
      (scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x) (1, y) k =
      massF m i k * gramOf (farR b E W n (birth W τ i) x.1 (x.2 i))
        (farR b E W n (birth W τ k) x.1 (x.2 k)) := by
    simp only [e3 i hi, e3 k hk, gramOf, massF, Finset.mul_sum, star_mul', Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [RCLike.star_def, Complex.conj_ofReal]
    ring
  have e1 : ((probeFrame b E W n τ m x)ᴴ * pathCurrent b E W n x.1 * probeFrame b E W n τ m x) i k
      = ((scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x)ᴴ * nearProjection W *
          (scatteringMatrix b E W n x.1 * probeFrame b E W n τ m x)) i k -
        ((probeFrame b E W n τ m x)ᴴ * nearProjection W * probeFrame b E W n τ m x) i k := by
    rw [← Matrix.sub_apply]
    simp only [pathCurrent, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  change ((probeFrame b E W n τ m x)ᴴ * pathCurrent b E W n x.1 * probeFrame b E W n τ m x) i k
    = _
  rw [e1, near_sandwich_apply, near_sandwich_apply, e2, e5, far_sum_frame b E n τ m x hm i k hi hk]
  ring

end BlockBand.SourceProcess.LengthCont.OneLayer
