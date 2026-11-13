module

public import BlockBand.Critical.MatrixClosing.Algebra
public import BlockBand.Critical.Herglotz.Atomic
public import BlockBand.Critical.WeightedDensity.Spectral
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Critical.Collar.Kernel.Universal

/-!
# Matrix closing: the physical collar function `F_W` as a finite atomic Herglotz function

* `ofAtoms`, `eval_ofAtoms`: `C₀ + Σ_ℓ (x_ℓ - z)⁻¹R_ℓ` as an `AtomicHerglotz`.
* `simpleSpectrum_inv_eq_sum`, `simpleSpectrum_eigenvalue_sub_ne`: spectral resolvent off the spectrum.
* `collarFunction b e X J ω : AtomicHerglotz r`: constant (Hermitian part of) `η⁻¹J*(KD⁻¹K* - H_o)J`,
  poles `Wρ(e)λ_ℓ(Q)`, residues `(Wρ(e)/η)(J*KD⁻¹B)u_ℓu_ℓ*(J*KD⁻¹B)* = Wρ(e)V*u_ℓu_ℓ*V`, with the
  measurable ordered spectral selection (`freshEigenvalue`, `freshProjector`) of `Q` on `Fin W`.
* `collarFunction_eval_eq` (deterministic) and **`ae_collarFunction_eval_eq`**: under the
  collar law, for Hermitian `X`, every frame `J` and every real `x`,
  `F_W(x) = -iJ*{2(I - U_{x/(Wρ(e))}𝔯)⁻¹ - I}J` almost surely.
* **`measurable_collarFunction_eval`**: `(ω, z) ↦ F_W(ω)(z)` is jointly measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Critical.Herglotz
open scoped ComplexOrder

/-!
## Finite atomic Herglotz functions from finitely many atoms
-/

section Atoms

variable {r n : ℕ}

/-- `C₀ + Σ_ℓ (x_ℓ - z)⁻¹ R_ℓ` as a finite atomic Herglotz function (coincident atoms merged). -/
def ofAtoms (C0 : Matrix (Fin r) (Fin r) ℂ) (hC0 : C0.IsHermitian) (pts : Fin n → ℝ)
    (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (hres : ∀ ℓ, (res ℓ).PosSemidef) :
    AtomicHerglotz r where
  const := C0
  const_isHermitian := hC0
  residue := ∑ ℓ, Finsupp.single (pts ℓ) (res ℓ)
  residue_posSemidef x := by
    rw [Finsupp.finsetSum_apply]
    refine Matrix.posSemidef_sum _ fun ℓ _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact hres ℓ
    · exact PosSemidef.zero

theorem eval_ofAtoms (C0 : Matrix (Fin r) (Fin r) ℂ) (hC0 : C0.IsHermitian) (pts : Fin n → ℝ)
    (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (hres : ∀ ℓ, (res ℓ).PosSemidef) (z : ℂ) :
    (ofAtoms C0 hC0 pts res hres).eval z = C0 + ∑ ℓ, ((pts ℓ : ℂ) - z)⁻¹ • res ℓ := by
  simp only [AtomicHerglotz.eval, ofAtoms]
  congr 1
  rw [← Finsupp.sum_finsetSum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  exact Finsupp.sum_single_index (smul_zero _)

end Atoms

/-!
## Spectral resolvent off the spectrum
-/

open BlockBand.Critical.WeightedDensity BlockBand.Coarea.FreshPalm in
/-- `(K - w)⁻¹ = Σ_ℓ (λ_ℓ - w)⁻¹ u_ℓu_ℓ*` for simple spectrum and `w` off the spectrum. -/
theorem simpleSpectrum_inv_eq_sum {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) {w : ℂ} (hne : ∀ ℓ, ((freshEigenvalue K ℓ : ℝ) : ℂ) - w ≠ 0) :
    (K - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      ∑ ℓ, (((freshEigenvalue K ℓ : ℝ) : ℂ) - w)⁻¹ • freshProjector K ℓ := by
  apply inv_eq_right_inv
  rw [Finset.mul_sum]
  calc ∑ ℓ, (K - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *
        ((((freshEigenvalue K ℓ : ℝ) : ℂ) - w)⁻¹ • freshProjector K ℓ)
      = ∑ ℓ, freshProjector K ℓ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_smul, sub_mul, hK.mul_freshProjector, smul_mul, one_mul, ← sub_smul,
          smul_smul, inv_mul_cancel₀ (hne ℓ), one_smul]
    _ = 1 := hK.sum_freshProjector

open BlockBand.Critical.WeightedDensity BlockBand.Coarea.FreshPalm in
/-- Off an invertible shift, no eigenvalue equals the shift. -/
theorem simpleSpectrum_eigenvalue_sub_ne {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) {w : ℂ} (hw : IsUnit (K - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det)
    (ℓ : Fin N) : ((freshEigenvalue K ℓ : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have hu : freshEigenvector K ℓ ≠ 0 := by
    intro h0
    have := hK.orthonormal ℓ ℓ
    rw [h0] at this
    simp at this
  have hker : (K - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ freshEigenvector K ℓ = 0 := by
    rw [sub_mulVec, hK.mulVec_freshEigenvector, smul_mulVec, one_mulVec, ← sub_smul, h,
      zero_smul]
  exact hw.ne_zero (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hu, hker⟩)

/-!
## The physical collar function
-/

section Collar

variable {W : ℕ}

/-- The port index `Fin 1 × Fin W ≃ Fin W`. -/
def portEquiv (W : ℕ) : PortSite W .common ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)

/-- `Q` on `Fin W` (for the measurable ordered spectral selection). -/
def portSchurFin (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : CollarSample W) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.reindex (portEquiv W) (portEquiv W) (portSchur e X ω)

/-- The unfolding scale `Wρ(e)` of the physical collar function. -/
def poleScale (W : ℕ) (e : ℝ) : ℝ := (W : ℝ) * Parameters.semicircleDensity e

/-- The residue weight `Wρ(e)/η` (cut at `0` so that residues are positive for every
parameter; it is `Wρ(e)/η` in the bulk). -/
def residueWeight (W : ℕ) (b e : ℝ) : ℝ := max (poleScale W e / (boundaryZ b e).im) 0

/-- `J*KD⁻¹B` with the port index on `Fin W`. -/
def frameFin {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) : Matrix (Fin r) (Fin W) ℂ :=
  (collarFrame b e X J ω).submatrix id (portEquiv W).symm

/-- The residue `Wρ(e) V*u_ℓu_ℓ*V = (Wρ(e)/η)(J*KD⁻¹B)u_ℓu_ℓ*(J*KD⁻¹B)*` at the pole
`Wρ(e)λ_ℓ(Q)`. -/
def collarResidue {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (ℓ : Fin W) :
    Matrix (Fin r) (Fin r) ℂ :=
  ((residueWeight W b e : ℝ) : ℂ) • (frameFin b e X J ω *
    BlockBand.Coarea.FreshPalm.freshProjector (portSchurFin e X ω) ℓ * (frameFin b e X J ω)ᴴ)

theorem collarResidue_posSemidef {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (ℓ : Fin W) :
    (collarResidue b e X J ω ℓ).PosSemidef :=
  ((posSemidef_vecMulVec_self_star _).mul_mul_conjTranspose_same _).smul
    (by exact_mod_cast le_max_right _ _)

/-- **The physical collar function** `F_W`,
as a finite atomic Herglotz function: constant (the Hermitian part of)
`η⁻¹J*(KD⁻¹K* - H_o)J`, poles `Wρ(e)λ_ℓ(Q)`, residues `Wρ(e)V*u_ℓu_ℓ*V` (measurable ordered
spectral selection of `Q`). -/
def collarFunction {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) : AtomicHerglotz r :=
  ofAtoms (Collar.Kernel.rePart (collarConst b e X J ω)) (Collar.Kernel.rePart_isHermitian _)
    (fun ℓ => poleScale W e * freshEigenvalue (portSchurFin e X ω) ℓ)
    (collarResidue b e X J ω) (collarResidue_posSemidef b e X J ω)

theorem rePart_eq_self {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    Collar.Kernel.rePart M = M := by
  rw [Collar.Kernel.rePart, hM.eq, ← two_smul ℂ M, smul_smul, inv_mul_cancel₀ two_ne_zero,
    one_smul]

theorem collarConst_isHermitian {r : ℕ} (b e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) : (collarConst b e X J ω).IsHermitian := by
  have hD : (topBlock e X ω).IsHermitian := by
    refine ((Collar.Kernel.blockDiag_isHermitian' hA).sub ?_).sub hX
    simp [IsHermitian, conjTranspose_smul]
  have hH : (matchedLeadK b e X * (topBlock e X ω)⁻¹ * (matchedLeadK b e X)ᴴ -
      (((boundaryZ b e).re : ℂ) • 1 - X)).IsHermitian := by
    refine (isHermitian_mul_mul_conjTranspose _ hD.inv).sub (IsHermitian.sub ?_ hX)
    simp [IsHermitian, conjTranspose_smul]
  have h2 := isHermitian_conjTranspose_mul_mul J hH
  unfold collarConst
  simp only [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [h2.eq]

/-- Reindexing the frame sandwich. -/
theorem frameFin_sandwich {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W)
    (M : Matrix (PortSite W .common) (PortSite W .common) ℂ) :
    frameFin b e X J ω * Matrix.reindex (portEquiv W) (portEquiv W) M * (frameFin b e X J ω)ᴴ =
      collarFrame b e X J ω * M * (collarFrame b e X J ω)ᴴ := by
  simp only [frameFin, reindex_apply, conjTranspose_submatrix]
  rw [submatrix_mul_equiv, submatrix_mul_equiv]
  simp

open BlockBand.Critical.WeightedDensity in
/-- **`F_W(x)` is the middle-shifted closing matrix** (the physical collar function at a real
point `x` equals the physical collar value). Deterministic; one collar sample with
Hermitian blocks, Hermitian `X`, `η > 0`, `Wρ(e) > 0`, invertible `D`, `G - (e+s)`, `Q - s`
(`s = x/(Wρ(e))`), and `Q` with simple spectrum. -/
theorem collarFunction_eval_eq {r : ℕ} (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    (hc : 0 < poleScale W e) {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian)
    (hG : ω.2.IsHermitian) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hD : IsUnit (topBlock e X ω).det) (x : ℝ)
    (hGs : IsUnit (ω.2 - ((e + microShift W e x : ℝ) : ℂ) • 1).det)
    (hQ : IsUnit (portSchur e X ω - (microShift W e x : ℂ) • 1).det)
    (hS : SimpleSpectrum (portSchurFin e X ω)) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) :
    (collarFunction b e X J ω).eval x = closingMatrix b e (microShift W e x) X J ω := by
  set s := microShift W e x with hsdef
  set c := poleScale W e
  set η := (boundaryZ b e).im
  rw [closingMatrix_eq b e s hη hA hG hX hD hGs hQ J, collarFunction, eval_ofAtoms,
    rePart_eq_self (collarConst_isHermitian b e hX hA J)]
  congr 1
  have hQf : IsUnit (portSchurFin e X ω - (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).det := by
    have : portSchurFin e X ω - (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
        Matrix.reindex (portEquiv W) (portEquiv W) (portSchur e X ω - (s : ℂ) • 1) := by
      simp [portSchurFin, reindex_apply, submatrix_sub, submatrix_smul]
    rw [this, det_reindex_self]; exact hQ
  have hne := simpleSpectrum_eigenvalue_sub_ne hS hQf
  have hinv : (portSchur e X ω - (s : ℂ) • 1)⁻¹ = (Matrix.reindex (portEquiv W) (portEquiv W)).symm
      (portSchurFin e X ω - (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by
    have : portSchurFin e X ω - (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
        Matrix.reindex (portEquiv W) (portEquiv W) (portSchur e X ω - (s : ℂ) • 1) := by
      simp [portSchurFin, reindex_apply, submatrix_sub, submatrix_smul]
    rw [this, inv_reindex]
    simp
  rw [← frameFin_sandwich, hinv, Equiv.apply_symm_apply, simpleSpectrum_inv_eq_sum hS hne, Matrix.mul_sum,
    Matrix.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [collarResidue, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
  congr 1
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hw : residueWeight W b e = c / η := max_eq_left (div_nonneg hc.le hη.le)
  have hl := hne ℓ
  have hs : (s : ℂ) = (x : ℂ) / c := by
    simp only [hsdef, microShift, c, poleScale]; push_cast; ring
  rw [hw]
  rw [hs] at hl ⊢
  set l : ℂ := (freshEigenvalue (portSchurFin e X ω) ℓ : ℂ)
  have hl' : (c : ℂ) * l - x ≠ 0 := by
    intro h; apply hl
    field_simp
    linear_combination h
  push_cast
  field_simp
  change ((c : ℂ) * l - x) / ((c : ℂ) * l - x) = (η : ℂ) / η
  rw [div_self hl', div_self hη']

/-!
### Measurability
-/

open BlockBand.Critical.Collar.Kernel in
theorem measurable_topBlock (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : CollarSample W => topBlock e X ω :=
  measurable_matrix_sub' (measurable_matrix_sub' measurable_blockDiag_collar measurable_const)
    measurable_const

open BlockBand.Critical.Collar.Kernel in
theorem measurable_portSchur (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : CollarSample W => portSchur e X ω :=
  measurable_matrix_sub' (measurable_matrix_sub' measurable_snd measurable_const)
    (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_conjTranspose' measurable_bondMatrix_collar)
      (measurable_matrix_inv' (measurable_topBlock e X))) measurable_bondMatrix_collar)

theorem measurable_portSchurFin (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : CollarSample W => portSchurFin e X ω := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [portSchurFin, reindex_apply, submatrix_apply]
  exact Matrix.measurable_apply.comp (measurable_portSchur e X)

open BlockBand.Critical.Collar.Kernel in
theorem measurable_collarFrame {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) :
    Measurable fun ω : CollarSample W => collarFrame b e X J ω :=
  measurable_matrix_mul' (measurable_matrix_mul' measurable_const
    (measurable_matrix_inv' (measurable_topBlock e X))) measurable_bondMatrix_collar

open BlockBand.Critical.Collar.Kernel in
theorem measurable_collarConst {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) :
    Measurable fun ω : CollarSample W => Collar.Kernel.rePart (collarConst b e X J ω) := by
  have h : Measurable fun ω : CollarSample W => collarConst b e X J ω :=
    measurable_matrix_smul' _ (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
      (measurable_matrix_sub' (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
        (measurable_matrix_inv' (measurable_topBlock e X))) measurable_const) measurable_const))
      measurable_const)
  exact measurable_matrix_smul' _ (measurable_matrix_add' h (measurable_matrix_conjTranspose' h))

open BlockBand.Critical.Collar.Kernel BlockBand.Coarea.FreshPalm in
theorem measurable_collarResidue {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ℓ : Fin W) :
    Measurable fun ω : CollarSample W => collarResidue b e X J ω ℓ := by
  have hF : Measurable fun ω : CollarSample W => frameFin b e X J ω := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [frameFin, submatrix_apply]
    exact Matrix.measurable_apply.comp (measurable_collarFrame b e X J)
  exact measurable_matrix_smul' _ (measurable_matrix_mul' (measurable_matrix_mul' hF
    ((measurable_freshProjector ℓ).comp (measurable_portSchurFin e X)))
    (measurable_matrix_conjTranspose' hF))

open BlockBand.Coarea.FreshPalm in
/-- **Joint measurability** of `(ω, z) ↦ F_W(ω)(z)` (field `measurable_eval` of
`HerglotzTailHypotheses`). -/
theorem measurable_collarFunction_eval {r : ℕ} (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (i j : Fin r) :
    Measurable fun p : CollarSample W × ℂ => (collarFunction b e X J p.1).eval p.2 i j := by
  have heq : (fun p : CollarSample W × ℂ => (collarFunction b e X J p.1).eval p.2 i j) =
      fun p => Collar.Kernel.rePart (collarConst b e X J p.1) i j +
        ∑ ℓ, (((poleScale W e * freshEigenvalue (portSchurFin e X p.1) ℓ : ℝ) : ℂ) - p.2)⁻¹ *
          collarResidue b e X J p.1 ℓ i j := by
    funext p
    rw [collarFunction, eval_ofAtoms]
    simp [Matrix.sum_apply]
  rw [heq]
  refine Measurable.add (Matrix.measurable_apply.comp
    ((measurable_collarConst b e X J).comp measurable_fst)) ?_
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  refine Measurable.mul (Measurable.inv (Measurable.sub ?_ measurable_snd)) ?_
  · exact Complex.measurable_ofReal.comp (measurable_const.mul
      (((measurable_freshEigenvalue ℓ).comp (measurable_portSchurFin e X)).comp measurable_fst))
  · exact Matrix.measurable_apply.comp ((measurable_collarResidue b e X J ℓ).comp measurable_fst)

/-!
### Almost-sure identification
-/

/-- `D = A - e - X` is invertible `collarLaw`-a.s. -/
theorem ae_isUnit_det_topBlock {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∀ᵐ ω ∂collarLaw W b, IsUnit (topBlock e X ω).det := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : t ≠ 0 :=
    (Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))).ne'
  have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
      IsUnit (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X).det := by
    rw [ae_iff]
    have := BlockBand.Layers.srec_pi_gue_det_null W 2 ht (-((e : ℂ) • 1) - X)
    refine measure_mono_null (fun A hA => ?_) this
    simp only [Set.mem_ofPred_eq, isUnit_iff_ne_zero, not_not] at hA ⊢
    rw [← hA]; congr 1; abel
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := Measure.pi fun _ : Fin 2 =>
    gueMeasure (Fin W) t) (ν := Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))).ae h1
  exact (Measure.quasiMeasurePreserving_fst (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) t)).ae h2

open BlockBand.Critical.WeightedDensity in
/-- For fixed end blocks and bonds with Hermitian `A_j` and invertible `D`, the middle Schur
complement `Q - s` is invertible and `Q` has simple spectrum, `G`-a.s. -/
theorem ae_port_good {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e s : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hX : X.IsHermitian)
    (ω₁ : LayerSample W .common) (hA : ∀ j, (ω₁.1 j).IsHermitian) :
    ∀ᵐ G ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)),
      IsUnit (portSchur e X (ω₁, G) - (s : ℂ) • 1).det ∧
        SimpleSpectrum (portSchurFin e X (ω₁, G)) := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have htpos : 0 < t := Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))
  set B := bondMatrix .common ω₁.2
  set D := blockDiag ω₁.1 - (e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hD : D.IsHermitian := by
    refine ((Collar.Kernel.blockDiag_isHermitian' hA).sub ?_).sub hX
    simp [IsHermitian, conjTranspose_smul]
  set N0 : Matrix (PortSite W .common) (PortSite W .common) ℂ := -((e : ℂ) • 1) - Bᴴ * D⁻¹ * B
  have hN0 : N0.IsHermitian := by
    refine IsHermitian.sub ?_ (isHermitian_conjTranspose_mul_mul B hD.inv)
    simp [IsHermitian, conjTranspose_smul]
  have hps : ∀ G, portSchur e X (ω₁, G) = G + N0 := by
    intro G; simp only [portSchur, topBlock, N0, D, B]; abel
  have hdet : ∀ᵐ G ∂gueMeasure (PortSite W .common) t,
      IsUnit (portSchur e X (ω₁, G) - (s : ℂ) • 1).det := by
    rw [ae_iff]
    have := Collar.Kernel.gueMeasure_port_det_null htpos.ne' (N0 - (s : ℂ) • 1)
    refine measure_mono_null (fun G hG => ?_) this
    simp only [Set.mem_ofPred_eq, isUnit_iff_ne_zero, not_not, hps] at hG ⊢
    rw [← hG]; congr 1; abel
  have hR : Measurable (Matrix.reindex (portEquiv W) (portEquiv W) :
      Matrix (PortSite W .common) (PortSite W .common) ℂ → Matrix (Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hsimple : ∀ᵐ G ∂gueMeasure (PortSite W .common) t,
      SimpleSpectrum (portSchurFin e X (ω₁, G)) := by
    have hF : (Matrix.reindex (portEquiv W) (portEquiv W) N0).IsHermitian := by
      simpa [reindex_apply] using hN0.submatrix (portEquiv W).symm
    have h0 := ae_simpleSpectrum_add_gue hF htpos
    rw [← BlockBand.Coarea.GUELaw.gueMeasure_map_reindex (portEquiv W) t] at h0
    have h1 := ae_of_ae_map hR.aemeasurable h0
    filter_upwards [h1] with G hG
    have : portSchurFin e X (ω₁, G) = Matrix.reindex (portEquiv W) (portEquiv W) N0 +
        Matrix.reindex (portEquiv W) (portEquiv W) G := by
      rw [portSchurFin, hps, add_comm]; simp [reindex_apply, submatrix_add]
    rw [this]; exact hG
  filter_upwards [hdet, hsimple] with G h1 h2
  exact ⟨h1, h2⟩

open BlockBand.Critical.WeightedDensity in
/-- **`F_W(x) = -iJ*{2(I - U_x𝔯)⁻¹ - I}J` almost surely** under the collar law, for every
real `x` (middle shift `x/(Wρ(e))`), every Hermitian `X` and every frame `J`
(the physical collar value and its middle-shifted versions). -/
theorem ae_collarFunction_eval_eq {r : ℕ} {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    (hη : 0 < (boundaryZ b e).im) (hc : 0 < poleScale W e)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (x : ℝ) :
    ∀ᵐ ω ∂collarLaw W b,
      (collarFunction b e X J ω).eval x = closingMatrix b e (microShift W e x) X J ω := by
  set s := microShift W e x
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have hH := Collar.Density.ae_collarMatrix_isHermitian b e hX (W := W)
  have hD := ae_isUnit_det_topBlock hb hW e X
  have hG := Collar.Kernel.ae_isUnit_det_middleBlock (W := W) hb e s
  have hmeasS : MeasurableSet {K : Matrix (Fin W) (Fin W) ℂ | SimpleSpectrum K} :=
    measurableSet_simpleSpectrum
  have hP : ∀ᵐ ω ∂collarLaw W b, (∀ j, (ω.1.1 j).IsHermitian) →
      IsUnit (portSchur e X ω - (s : ℂ) • 1).det ∧ SimpleSpectrum (portSchurFin e X ω) := by
    have hmeas : MeasurableSet {ω : CollarSample W | (∀ j, (ω.1.1 j).IsHermitian) →
        IsUnit (portSchur e X ω - (s : ℂ) • 1).det ∧ SimpleSpectrum (portSchurFin e X ω)} := by
      have hA : MeasurableSet {ω : CollarSample W | ∀ j, (ω.1.1 j).IsHermitian} := by
        simp only [Set.ofPred_forall]
        refine MeasurableSet.iInter fun j => ?_
        exact (BlockBand.Model.Construction.measurableSet_isHermitian).preimage
          ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
      have hU : MeasurableSet {ω : CollarSample W |
          IsUnit (portSchur e X ω - (s : ℂ) • 1).det} := by
        simp only [isUnit_iff_ne_zero]
        exact (measurableSet_eq_fun ((Continuous.matrix_det continuous_id).measurable.comp
          (Collar.Kernel.measurable_matrix_sub' (measurable_portSchur e X) measurable_const))
          measurable_const).compl
      have hS : MeasurableSet {ω : CollarSample W | SimpleSpectrum (portSchurFin e X ω)} :=
        hmeasS.preimage (measurable_portSchurFin e X)
      have he : {ω : CollarSample W | (∀ j, (ω.1.1 j).IsHermitian) →
          IsUnit (portSchur e X ω - (s : ℂ) • 1).det ∧ SimpleSpectrum (portSchurFin e X ω)} =
          {ω : CollarSample W | ∀ j, (ω.1.1 j).IsHermitian}ᶜ ∪
            ({ω : CollarSample W | IsUnit (portSchur e X ω - (s : ℂ) • 1).det} ∩
              {ω : CollarSample W | SimpleSpectrum (portSchurFin e X ω)}) := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
        tauto
      rw [he]
      exact hA.compl.union (hU.inter hS)
    rw [collarLaw, Measure.ae_prod_iff_ae_ae hmeas]
    exact Filter.Eventually.of_forall fun ω₁ => by
      by_cases hA : ∀ j, (ω₁.1 j).IsHermitian
      · filter_upwards [ae_port_good hb hW e s X hX ω₁ hA] with G hG
        exact fun _ => hG
      · exact Filter.Eventually.of_forall fun G h => absurd h hA
  filter_upwards [hH, hD, hG, hP] with ω hH hD hG hP
  obtain ⟨hQ, hS⟩ := hP hH.2.1
  exact collarFunction_eval_eq b e hη hc hH.2.1 hH.2.2 hX hD x hG hQ hS J

end Collar

end BlockBand.Critical.MatrixClosing
