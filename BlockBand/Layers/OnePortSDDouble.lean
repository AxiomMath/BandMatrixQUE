module

public import BlockBand.Layers.OnePortSDCov
public import BlockBand.Layers.OnePortMoments

/-!
# The doubled passive one-port family: first- and second-order Schwinger–Dyson at once

Support for `oppPassiveMeanEquations_holds`: the mean equations and the bottom-source trace
equations of the passive one-port layer, with the passive bounds lemma.

## Setting

The fresh one-block one-port layer in real Gaussian coordinates `x ~ gaussianProduct (tflVar …)`
(`tfl_layerLaw_eq_map`): `N(x) = 𝒢(x)⁻¹ = tflConst + Λ(x)` (`Λ(x) = tflLin x` Hermitian), at
`z = z_∂(E)`, `η = Im z > 0`, for a **passive** `X` (`-Im X ⪰ 0`, no bound on `X`), `P = P_port`.

## The doubling device

`𝒩(x) = [[N, -ηP], [0, -N*]]` is affine in `x` with linear part `diag(Λ, -Λ)`, and
`𝒩⁻¹ = [[𝒢, -η𝒢P𝒢*], [0, -𝒢*]]` (`osd_inv_dbl`). Its imaginary part is `⪰ 0`: the diagonal
blocks contribute `Im N ⪰ diag(Y, η)` each (passivity), and the off-diagonal `-ηP` is dominated
by the two port contributions (`osd_dbl_coercive`). Hence `CoreReg` holds (`osd_coreReg`) and the
generic first-order identity `core_limit_identity` applies to `𝒩`. Its `(1,1)` block is the
first-order Schwinger–Dyson identity of `𝒢` and its `(1,2)` block is the **second-order**
identity for `F = 𝒢P𝒢*` (the one obtained from `NF = P𝒢*` by Gaussian integration by parts):
`C₀ EF - E[S(𝒢)F] - E[S(F)𝒢*] = P E𝒢*`. Likewise, every trace–matrix covariance of words in
`𝒢, 𝒢*, F, 𝒢*𝒦*, F𝒦*` is a **one-letter** covariance of `𝒩⁻¹`, bounded by the generic
`osd_cov_limit` with the weight `𝒲 = diag(0, 𝒦*)` handled through `𝒦𝒢 = J + (𝒦 - JN)𝒢`, the
word `K𝒢` only (never `𝒢₁₁K*`).

Helper prefix `osd`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (gaussianProduct ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Quadratic forms of block matrices
-/

section Forms

variable {n m : Type} [Fintype n] [Fintype m]

theorem osd_dot_fromBlocks (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) (v : n ⊕ m → ℂ) :
    star v ⬝ᵥ (fromBlocks A B C D *ᵥ v) =
      star (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl)) + star (v ∘ Sum.inl) ⬝ᵥ (B *ᵥ (v ∘ Sum.inr)) +
        (star (v ∘ Sum.inr) ⬝ᵥ (C *ᵥ (v ∘ Sum.inl)) +
          star (v ∘ Sum.inr) ⬝ᵥ (D *ᵥ (v ∘ Sum.inr))) := by
  rw [fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Pi.star_apply, Function.comp_apply]

theorem osd_cplSq_sum (v : n ⊕ m → ℂ) : cplSq v = cplSq (v ∘ Sum.inl) + cplSq (v ∘ Sum.inr) := by
  unfold cplSq
  rw [Fintype.sum_sum_type]
  rfl

theorem osd_form_fromBlocks (A : Matrix n n ℂ) (B : Matrix n m ℂ) (D : Matrix m m ℂ)
    (v : n ⊕ m → ℂ) :
    cplForm (fromBlocks A B 0 D) v = cplForm A (v ∘ Sum.inl) +
      (star (v ∘ Sum.inl) ⬝ᵥ (B *ᵥ (v ∘ Sum.inr))).im + cplForm D (v ∘ Sum.inr) := by
  unfold cplForm
  rw [osd_dot_fromBlocks]
  simp only [zero_mulVec, dotProduct_zero, zero_add, Complex.add_im]

theorem osd_form_neg_conjTranspose (A : Matrix n n ℂ) (u : n → ℂ) :
    cplForm (-Aᴴ) u = cplForm A u := by
  unfold cplForm
  have h := cpl_star_dot_mulVec_star A u
  rw [neg_mulVec, dotProduct_neg, Complex.neg_im, ← h, Complex.star_def, Complex.conj_im, neg_neg]

theorem osd_form_I_smul (M : Matrix n n ℂ) (u : n → ℂ) :
    cplForm (Complex.I • M) u = (star u ⬝ᵥ (M *ᵥ u)).re := by
  unfold cplForm
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem osd_dot_diagonal [DecidableEq n] (q : n → ℝ) (u : n → ℂ) :
    (star u ⬝ᵥ (diagonal (fun x => (q x : ℂ)) *ᵥ u)).re = ∑ x, q x * ‖u x‖ ^ 2 := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mulVec_diagonal, mul_left_comm, Complex.re_ofReal_mul, show star (u x) * u x = conj (u x) * u x from rfl,
    mul_comm (conj (u x)), Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Forms

/-!
## 2. Coercivity of the passive one-port layer and of its doubling
-/

section Coercive

variable {W : ℕ}

/-- **Coercivity of the passive layer matrix**: for a sample with Hermitian GUE block, a passive
`X`, `Im z ≥ 0` and `κ ≥ 0`, `Im ⟨u, (N + iκ) u⟩ ≥ κ‖u‖² + Im z · ‖u_port‖²`. -/
theorem osd_layer_form (E : ℝ) (z : ℂ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    {ω : LayerSample W .oneBlockOnePort} (hA : (blockDiag ω.1).IsHermitian) (κ : ℝ)
    (u : LayerSite W .oneBlockOnePort → ℂ) :
    κ * cplSq u + z.im * ∑ p : PortSite W .oneBlockOnePort, ‖u (Sum.inr p)‖ ^ 2 ≤
      cplForm (tflReg κ (layerMatrix .oneBlockOnePort E z (onePortLift X) ω)) u := by
  set Y := onePortDissipation X with hYdef
  have hY : Y.PosSemidef := hX
  have hXh := opmHerm_isHermitian X
  have hlift : onePortLift X = onePortLift (opmHerm X) - Complex.I • onePortLift Y := by
    conv_lhs => rw [opm_decomp X]
    rw [opm_lift_sub, opm_lift_smul]
  have hsplit : tflReg κ (layerMatrix .oneBlockOnePort E z (onePortLift X) ω) =
      tflHerm .oneBlockOnePort E z (onePortLift (opmHerm X)) ω +
        Complex.I • diagonal (fun x => ((Sum.elim (fun _ => κ) (fun _ => κ + z.im) x : ℝ) : ℂ)) +
        Complex.I • fromBlocks (onePortLift Y) 0 0 0 := by
    rw [hlift, opm_layerMatrix_pencil, ← tflReg_layerMatrix_eq]
    unfold tflReg
    abel
  rw [hsplit, cpl_form_add, cpl_form_add,
    cpl_form_herm (tflHerm_isHermitian _ E z (opm_lift_isHermitian hXh) ω hA), zero_add,
    osd_form_I_smul, osd_form_I_smul, osd_dot_diagonal, osd_dot_fromBlocks]
  simp only [zero_mulVec, dotProduct_zero, add_zero]
  have hq := (opm_lift_posSemidef hY).dotProduct_mulVec_nonneg (u ∘ Sum.inl)
  rw [Complex.le_def, Complex.zero_re] at hq
  have e : ∑ x : LayerSite W .oneBlockOnePort,
      (Sum.elim (fun _ => κ) (fun _ => κ + z.im) x : ℝ) * ‖u x‖ ^ 2 =
        κ * cplSq u + z.im * ∑ p : PortSite W .oneBlockOnePort, ‖u (Sum.inr p)‖ ^ 2 := by
    unfold cplSq
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, add_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring
  rw [e]
  linarith [hq.1]

/-- The doubling `[[A, -ηP], [0, -A*]]`. -/
def osdDbl (η : ℝ) (A : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks A (-((η : ℂ) • onePortPortProj)) 0 (-Aᴴ)

/-- The port cross term: `|⟨v₁, P v₂⟩| ≤ (‖v₁,port‖² + ‖v₂,port‖²)/2`. -/
theorem osd_cross_le (v₁ v₂ : LayerSite W .oneBlockOnePort → ℂ) :
    ‖star v₁ ⬝ᵥ ((onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ) *ᵥ v₂)‖ ≤
      (∑ p : PortSite W .oneBlockOnePort, ‖v₁ (Sum.inr p)‖ ^ 2 +
        ∑ p : PortSite W .oneBlockOnePort, ‖v₂ (Sum.inr p)‖ ^ 2) / 2 := by
  have e : star v₁ ⬝ᵥ ((onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ) *ᵥ v₂) =
        ∑ p : PortSite W .oneBlockOnePort, star (v₁ (Sum.inr p)) * v₂ (Sum.inr p) := by
    unfold onePortPortProj
    rw [← Sum.elim_comp_inl_inr v₂, fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖v₁ (Sum.inr p)‖ - ‖v₂ (Sum.inr p)‖)]

/-- **Coercivity of the doubling**: if `Im⟨u, A u⟩ ≥ κ‖u‖² + η‖u_port‖²` with `η ≥ 0`, then
`Im⟨v, [[A, -ηP], [0, -A*]] v⟩ ≥ κ‖v‖²`. -/
theorem osd_dbl_coercive {A : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    {κ η : ℝ} (hη : 0 ≤ η)
    (hA : ∀ u, κ * cplSq u + η * ∑ p : PortSite W .oneBlockOnePort, ‖u (Sum.inr p)‖ ^ 2 ≤
      cplForm A u) :
    cplCoercive κ (osdDbl η A) := by
  intro v
  unfold osdDbl
  rw [osd_form_fromBlocks, osd_form_neg_conjTranspose, osd_cplSq_sum]
  have h1 := hA (v ∘ Sum.inl)
  have h2 := hA (v ∘ Sum.inr)
  have hc := osd_cross_le (v ∘ Sum.inl) (v ∘ Sum.inr)
  have him : -(η * ((∑ p : PortSite W .oneBlockOnePort, ‖(v ∘ Sum.inl) (Sum.inr p)‖ ^ 2 +
      ∑ p : PortSite W .oneBlockOnePort, ‖(v ∘ Sum.inr) (Sum.inr p)‖ ^ 2) / 2)) ≤
      (star (v ∘ Sum.inl) ⬝ᵥ (-((η : ℂ) • onePortPortProj) *ᵥ (v ∘ Sum.inr))).im := by
    rw [neg_mulVec, smul_mulVec, dotProduct_neg, dotProduct_smul, smul_eq_mul, Complex.neg_im,
      neg_le_neg_iff]
    refine (Complex.im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hc hη
  have hp1 : 0 ≤ ∑ p : PortSite W .oneBlockOnePort, ‖(v ∘ Sum.inl) (Sum.inr p)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hp2 : 0 ≤ ∑ p : PortSite W .oneBlockOnePort, ‖(v ∘ Sum.inr) (Sum.inr p)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  nlinarith

end Coercive

/-!
## 3. The doubled family
-/

section Family

variable {W : ℕ}

/-- The layer matrix of the one-port layer in real coordinates, `N(x) = 𝒢(x)⁻¹`. -/
def osdN (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerMatrix .oneBlockOnePort E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x)

/-- The constant part of the doubled family, `[[C₀, -ηP], [0, -C₀*]]`. -/
def osdC0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  osdDbl (boundaryZ b E).im (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X))

/-- `M ↦ diag(M, -M)` (real-linear). -/
def osdDiag (W : ℕ) : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ →ₗ[ℝ]
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ where
  toFun M := fromBlocks M 0 0 (-M)
  map_add' M N := by rw [fromBlocks_add]; congr 1 <;> abel
  map_smul' r M := by rw [RingHom.id_apply, fromBlocks_smul]; simp

/-- The linear part of the doubled family, `x ↦ diag(Λ(x), -Λ(x))`. -/
def osdL (W : ℕ) (b : ℝ) : (TflCoord W .oneBlockOnePort → ℝ) →L[ℝ]
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  (LinearMap.toContinuousLinearMap (osdDiag W)).comp (meqLc W b .oneBlockOnePort)

theorem osdL_apply (b : ℝ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    osdL W b x = fromBlocks (tflLin W b .oneBlockOnePort x) 0 0
      (-tflLin W b .oneBlockOnePort x) := rfl

theorem osd_N_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    osdN b E X x = tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) +
      tflLin W b .oneBlockOnePort x :=
  tfl_layerMatrix_embed W b _ E _ _ x

/-- `𝒩(x) = C₀ᴰ + Lᴰ x = [[N, -ηP], [0, -N*]]`. -/
theorem osd_C0_add_L (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    osdC0 b E X + osdL W b x = osdDbl (boundaryZ b E).im (osdN b E X x) := by
  rw [osdC0, osdDbl, osdDbl, osdL_apply, fromBlocks_add, osd_N_eq, conjTranspose_add,
    tcv_lin_herm]
  congr 1 <;> abel

/-- The regularized doubled family is the doubling of the regularized layer matrix. -/
theorem osd_psi_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (κ : ℝ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    corePsi (osdC0 b E X) (osdL W b) κ x =
      osdDbl (boundaryZ b E).im (tflReg κ (osdN b E X x)) := by
  have h1 : corePsi (osdC0 b E X) (osdL W b) κ x =
      (osdC0 b E X + osdL W b x) + ((κ : ℂ) * Complex.I) •
        (1 : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
          (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ) := by
    unfold corePsi; abel
  rw [h1, osd_C0_add_L, osdDbl, osdDbl, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add, tflReg,
    conjTranspose_add, conjTranspose_smul, conjTranspose_one]
  congr 1 <;> first
    | (simp; done)
    | (rw [neg_add, ← neg_smul]; congr 2; apply Complex.ext <;> simp)

/-- **`CoreReg` for the doubled passive family** (`Im z ≥ 0`, passive `X`). -/
theorem osd_coreReg {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hz : 0 ≤ (boundaryZ b E).im) : CoreReg (osdC0 b E X) (osdL W b) := by
  intro κ hκ x
  rw [osd_psi_eq]
  have hc : cplCoercive κ (osdDbl (boundaryZ b E).im (tflReg κ (osdN b E X x))) :=
    osd_dbl_coercive hz fun u => osd_layer_form E (boundaryZ b E) hX
      (tflEmbed_blockDiag_isHermitian W b _ x) κ u
  obtain ⟨hu, hn⟩ := cpl_coercive_inv hκ hc
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hu, ?_⟩
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact hn

/-- The regularized passive layer matrix is invertible with `‖(N + iκ)⁻¹‖ ≤ κ⁻¹`. -/
theorem osd_reg_layer {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hz : 0 ≤ (boundaryZ b E).im) {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    IsUnit (tflReg κ (osdN b E X x)).det ∧ ‖(tflReg κ (osdN b E X x))⁻¹‖ ≤ κ⁻¹ := by
  refine cpl_coercive_inv hκ fun u => ?_
  have h := osd_layer_form E (boundaryZ b E) hX (tflEmbed_blockDiag_isHermitian W b _ x) κ u
  have h0 : 0 ≤ (boundaryZ b E).im * ∑ p : PortSite W .oneBlockOnePort, ‖u (Sum.inr p)‖ ^ 2 :=
    mul_nonneg hz (Finset.sum_nonneg fun _ _ => by positivity)
  exact le_trans (by linarith) h

/-- **The inverse of the doubling**: `[[A, -ηP], [0, -A*]]⁻¹ = [[A⁻¹, -ηA⁻¹PA⁻*], [0, -A⁻*]]`. -/
theorem osd_inv_dbl (η : ℝ) {A : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (hA : IsUnit A.det) :
    (osdDbl η A)⁻¹ = fromBlocks A⁻¹ (-((η : ℂ) • (A⁻¹ * onePortPortProj * A⁻¹ᴴ))) 0 (-A⁻¹ᴴ) := by
  apply Matrix.inv_eq_right_inv
  have h1 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
  have h2 : Aᴴ * A⁻¹ᴴ = 1 := by
    rw [← conjTranspose_mul, nonsing_inv_mul A hA, conjTranspose_one]
  rw [osdDbl, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp [h1]
  · simp [← Matrix.mul_assoc, h1]
  · simp
  · simp [h2]

end Family

/-!
## 4. Norms and block algebra
-/

section BlockAlgebra

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem osd_fromBlocks_decomp (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) :
    fromBlocks A B C D =
      (wlIncl (Sum.inl : n → n ⊕ m))ᴴ * A * wlIncl (Sum.inl : n → n ⊕ m) +
        (wlIncl (Sum.inl : n → n ⊕ m))ᴴ * B * wlIncl (Sum.inr : m → n ⊕ m) +
        (wlIncl (Sum.inr : m → n ⊕ m))ᴴ * C * wlIncl (Sum.inl : n → n ⊕ m) +
        (wlIncl (Sum.inr : m → n ⊕ m))ᴴ * D * wlIncl (Sum.inr : m → n ⊕ m) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [wlIncl, Matrix.mul_apply, conjTranspose_apply, ite_mul, mul_ite]

/-- `‖[[A, B], [C, D]]‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖`. -/
theorem osd_norm_fromBlocks_le (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) : ‖fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have key : ∀ {k l : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]
      {f : k → n ⊕ m} {g : l → n ⊕ m}, Function.Injective f → Function.Injective g →
      ∀ M : Matrix k l ℂ, ‖(wlIncl f)ᴴ * M * wlIncl g‖ ≤ ‖M‖ := by
    intro k l _ _ _ _ f g hf hg M
    calc ‖(wlIncl f)ᴴ * M * wlIncl g‖ ≤ ‖(wlIncl f)ᴴ‖ * ‖M‖ * ‖wlIncl g‖ :=
          (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * ‖M‖ * 1 := by
          rw [l2_opNorm_conjTranspose]
          exact mul_le_mul (mul_le_mul_of_nonneg_right (wl_norm_incl_le hf) (norm_nonneg _))
            (wl_norm_incl_le hg) (norm_nonneg _) (by positivity)
      _ = ‖M‖ := by ring
  rw [osd_fromBlocks_decomp]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · exact key Sum.inl_injective Sum.inl_injective A
  · exact key Sum.inl_injective Sum.inr_injective B
  · exact key Sum.inr_injective Sum.inl_injective C
  · exact key Sum.inr_injective Sum.inr_injective D

theorem osd_norm_toBlocks22_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₂₂‖ ≤ ‖M‖ :=
  wl_norm_submatrix_le M Sum.inr_injective Sum.inr_injective

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem osd_sum_smul_fromBlocks {α R : Type*} [Fintype α] [SMul R ℂ] (r : α → R)
    (a : α → Matrix n n ℂ) (b : α → Matrix n m ℂ) (c : α → Matrix m n ℂ)
    (d : α → Matrix m m ℂ) :
    ∑ i, r i • fromBlocks (a i) (b i) (c i) (d i) =
      fromBlocks (∑ i, r i • a i) (∑ i, r i • b i) (∑ i, r i • c i) (∑ i, r i • d i) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.sum_apply]

end BlockAlgebra

/-!
## 5. The Gaussian contraction of the doubled family
-/

section Contraction

variable {W : ℕ}

/-- `𝒮ᴰ([[A, B], [C, D]]) = [[S A, -S B], [-S C, S D]]`, `S = meqS` the layer contraction. -/
theorem osd_coreS_fromBlocks (b : ℝ)
    (A B C D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    coreS (tflVar W b .oneBlockOnePort) (osdL W b) (fromBlocks A B C D) =
      fromBlocks (meqS W b .oneBlockOnePort A) (-meqS W b .oneBlockOnePort B)
        (-meqS W b .oneBlockOnePort C) (meqS W b .oneBlockOnePort D) := by
  have hterm : ∀ i : TflCoord W .oneBlockOnePort,
      osdL W b (Pi.single i 1) * fromBlocks A B C D * osdL W b (Pi.single i 1) =
        fromBlocks (tflLin W b _ (Pi.single i 1) * A * tflLin W b _ (Pi.single i 1))
          (-(tflLin W b _ (Pi.single i 1) * B * tflLin W b _ (Pi.single i 1)))
          (-(tflLin W b _ (Pi.single i 1) * C * tflLin W b _ (Pi.single i 1)))
          (tflLin W b _ (Pi.single i 1) * D * tflLin W b _ (Pi.single i 1)) := by
    intro i
    rw [osdL_apply, fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> simp [Matrix.mul_assoc]
  unfold coreS meqS
  simp only [hterm, osd_sum_smul_fromBlocks, smul_neg, Finset.sum_neg_distrib]

/-- **Contraction bound for the doubled family**: `‖Σᵢ vᵢ Tr(KΛᵢᴰ)Λᵢᴰ‖ ≤ (40/W)‖K‖`. -/
theorem osd_contract_le (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (K : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ) :
    ‖∑ i, (((tflVar W b .oneBlockOnePort i : ℝ) : ℂ) * (K * osdL W b (Pi.single i 1)).trace) •
        osdL W b (Pi.single i 1)‖ ≤ 40 / W * ‖K‖ := by
  set D := K.toBlocks₁₁ - K.toBlocks₂₂ with hD
  have htr : ∀ i : TflCoord W .oneBlockOnePort, (K * osdL W b (Pi.single i 1)).trace =
      (D * tflLin W b _ (Pi.single i 1)).trace := by
    intro i
    conv_lhs => rw [← fromBlocks_toBlocks K]
    rw [osdL_apply, fromBlocks_multiply, wl_trace_fromBlocks, hD, Matrix.sub_mul, trace_sub]
    simp [trace_neg, sub_eq_add_neg]
  have hsum : ∑ i, (((tflVar W b .oneBlockOnePort i : ℝ) : ℂ) * (K * osdL W b (Pi.single i 1)).trace) •
        osdL W b (Pi.single i 1) =
      fromBlocks (tcvContract W b _ D) 0 0 (-tcvContract W b _ D) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [htr i, osdL_apply], osd_sum_smul_fromBlocks]
    simp only [smul_zero, Finset.sum_const_zero, smul_neg, Finset.sum_neg_distrib, tcvContract]
  rw [hsum]
  have h1 := tcv_contract_le W b _ hW hb0 hb1 D
  have hD' : ‖D‖ ≤ 2 * ‖K‖ := by
    calc ‖D‖ ≤ ‖K.toBlocks₁₁‖ + ‖K.toBlocks₂₂‖ := norm_sub_le _ _
      _ ≤ ‖K‖ + ‖K‖ := add_le_add (wl_norm_toBlocks11_le K) (osd_norm_toBlocks22_le K)
      _ = 2 * ‖K‖ := by ring
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc ‖fromBlocks (tcvContract W b _ D) 0 0 (-tcvContract W b _ D)‖
      ≤ ‖tcvContract W b _ D‖ + ‖(0 : Matrix (LayerSite W .oneBlockOnePort)
          (LayerSite W .oneBlockOnePort) ℂ)‖ + ‖(0 : Matrix (LayerSite W .oneBlockOnePort)
          (LayerSite W .oneBlockOnePort) ℂ)‖ + ‖-tcvContract W b _ D‖ :=
        osd_norm_fromBlocks_le _ _ _ _
    _ = 2 * ‖tcvContract W b _ D‖ := by rw [norm_neg, norm_zero]; ring
    _ ≤ 2 * (10 / W * (2 * ‖K‖)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left hD' (by positivity))
    _ = 40 / W * ‖K‖ := by ring

end Contraction

/-!
## 6. The doubled resolvent and its majorant
-/

section Majorant

variable {W : ℕ}

/-- `𝒢(x) = N(x)⁻¹` (`= layerResolvent … (tflEmbed x)`). -/
def osdG (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  (osdN b E X x)⁻¹

/-- The bottom source `F = 𝒢 P_port 𝒢*`. -/
def osdF (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  osdG b E X x * onePortPortProj * (osdG b E X x)ᴴ

/-- The doubled resolvent in block form, `[[𝒢, -ηF], [0, -𝒢*]]`. -/
def osdB (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks (osdG b E X x) (-(((boundaryZ b E).im : ℂ) • osdF b E X x)) 0 (-(osdG b E X x)ᴴ)

/-- The doubled weight `𝒲_K = diag(0, 𝒦*)`, `𝒦 = diag(z - X, 0)`. -/
def osdWK (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks 0 0 0 (wlKh (m := PortSite W .oneBlockOnePort)
    (boundaryZ b E • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
      onePortLift X))ᴴ

theorem osd_inv_eq_B {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {x : TflCoord W .oneBlockOnePort → ℝ}
    (hx : IsUnit (osdN b E X x).det) : (osdC0 b E X + osdL W b x)⁻¹ = osdB b E X x := by
  rw [osd_C0_add_L, osd_inv_dbl _ hx]
  rfl

theorem osd_det_dbl {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {x : TflCoord W .oneBlockOnePort → ℝ}
    (hx : IsUnit (osdN b E X x).det) : IsUnit (osdC0 b E X + osdL W b x).det := by
  rw [osd_C0_add_L, osdDbl, det_fromBlocks_zero₂₁, det_neg, det_conjTranspose]
  exact hx.mul (((isUnit_neg_one (α := ℂ)).pow _).mul hx.star)

theorem osd_coreG_eq {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hz : 0 ≤ (boundaryZ b E).im) {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    coreG (osdC0 b E X) (osdL W b) κ x =
      fromBlocks (tflReg κ (osdN b E X x))⁻¹
        (-(((boundaryZ b E).im : ℂ) • ((tflReg κ (osdN b E X x))⁻¹ * onePortPortProj *
          (tflReg κ (osdN b E X x))⁻¹ᴴ))) 0 (-(tflReg κ (osdN b E X x))⁻¹ᴴ) := by
  rw [coreG, osd_psi_eq, ← Matrix.nonsing_inv_eq_ringInverse,
    osd_inv_dbl _ (osd_reg_layer hX hz hκ x).1]

/-- Norm bounds for a doubling `[[G, -ηGPG*], [0, -G*]]` from `‖G‖, ‖𝒦G‖ ≤ 2F`, `‖P‖ ≤ 1`. -/
theorem osd_dbl_norm_le {n : Type} [Fintype n] [DecidableEq n] (G P Kh : Matrix n n ℂ)
    {η F : ℝ} (hη : 0 ≤ η) (hF1 : 1 ≤ F) (hP : ‖P‖ ≤ 1) (hG : ‖G‖ ≤ 2 * F)
    (hK : ‖Kh * G‖ ≤ 2 * F) :
    ‖fromBlocks G (-((η : ℂ) • (G * P * Gᴴ))) 0 (-Gᴴ)‖ ≤ (4 + 4 * η) * F ^ 2 ∧
      ‖fromBlocks G (-((η : ℂ) • (G * P * Gᴴ))) 0 (-Gᴴ) * fromBlocks 0 0 0 Khᴴ‖ ≤
        (4 + 4 * η) * F ^ 2 := by
  have hηn : ‖(η : ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_of_nonneg hη]
  have hGh : ‖Gᴴ‖ = ‖G‖ := l2_opNorm_conjTranspose _
  have hKGh : ‖Gᴴ * Khᴴ‖ ≤ 2 * F := by
    rw [← conjTranspose_mul, l2_opNorm_conjTranspose]; exact hK
  have hF0 : 0 ≤ F := by linarith
  have hFF : F ≤ F ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hF0 hF1
  have h3 : ∀ M : Matrix n n ℂ, ‖M‖ ≤ 2 * F → ‖G * P * M‖ ≤ (2 * F) * (2 * F) := by
    intro M hM
    calc ‖G * P * M‖ ≤ ‖G‖ * ‖P‖ * ‖M‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (2 * F) * 1 * (2 * F) :=
          mul_le_mul (mul_le_mul hG hP (norm_nonneg _) (by linarith)) hM (norm_nonneg _)
            (by linarith)
      _ = (2 * F) * (2 * F) := by ring
  have hB : ‖-((η : ℂ) • (G * P * Gᴴ))‖ ≤ η * ((2 * F) * (2 * F)) := by
    rw [norm_neg, norm_smul, hηn]
    exact mul_le_mul_of_nonneg_left (h3 _ (hGh.le.trans hG)) hη
  constructor
  · refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
    rw [norm_zero, norm_neg (Gᴴ), hGh]
    calc ‖G‖ + ‖-((η : ℂ) • (G * P * Gᴴ))‖ + 0 + ‖G‖
        ≤ 2 * F + η * ((2 * F) * (2 * F)) + 0 + 2 * F :=
          add_le_add (add_le_add (add_le_add hG hB) le_rfl) hG
      _ = 4 * F + 4 * (η * F ^ 2) := by ring
      _ ≤ 4 * F ^ 2 + 4 * (η * F ^ 2) := by linarith only [hFF]
      _ = (4 + 4 * η) * F ^ 2 := by ring
  · have e : fromBlocks G (-((η : ℂ) • (G * P * Gᴴ))) 0 (-Gᴴ) * fromBlocks 0 0 0 Khᴴ =
        fromBlocks 0 (-((η : ℂ) • (G * P * (Gᴴ * Khᴴ)))) 0 (-(Gᴴ * Khᴴ)) := by
      rw [fromBlocks_multiply]
      simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [e]
    refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
    rw [norm_zero, norm_neg, norm_neg, norm_smul, hηn]
    have h4 := mul_le_mul_of_nonneg_left (h3 _ hKGh) hη
    calc 0 + η * ‖G * P * (Gᴴ * Khᴴ)‖ + 0 + ‖Gᴴ * Khᴴ‖
        ≤ 0 + η * ((2 * F) * (2 * F)) + 0 + 2 * F :=
          add_le_add (add_le_add (add_le_add le_rfl h4) le_rfl) hKGh
      _ = 2 * F + 4 * (η * F ^ 2) := by ring
      _ ≤ 4 * F ^ 2 + 4 * (η * F ^ 2) := by linarith only [hFF, hF1]
      _ = (4 + 4 * η) * F ^ 2 := by ring

/-- **Pointwise weight bounds** (deterministic): for `κ ∈ [0,1]`, `|E| ≤ 2`, `|z| ≤ 3` and a
right inverse `G'` of `N + iκ` with `‖G'‖ ≤ 2‖𝒢‖`: `‖G'‖ ≤ 2F` and `‖𝒦G'‖ ≤ 2F`,
`F = 1 + 6(1 + ‖Λ‖)‖𝒢‖` (`wlF`). Only the word `𝒦G'` is used
(`𝒦G' = J + (𝒦 - J(N + iκ))G'`, valid for every `X`). -/
theorem osd_pointwise_le {E : ℝ} {z : ℂ} (hE : |E| ≤ 2) (hz : ‖z‖ ≤ 3)
    (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) {G' : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (hG' : tflReg κ (layerMatrix .oneBlockOnePort E z (onePortLift X) ω) * G' = 1)
    (hG'n : ‖G'‖ ≤ 2 * ‖layerResolvent .oneBlockOnePort E z (onePortLift X) ω‖) :
    ‖G'‖ ≤ 2 * wlF E z (onePortLift X) ω ∧
      ‖wlKh (m := PortSite W .oneBlockOnePort)
          (z • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
            onePortLift X) * G'‖ ≤ 2 * wlF E z (onePortLift X) ω := by
  set g := ‖layerResolvent .oneBlockOnePort E z (onePortLift X) ω‖ with hg
  set lam := ‖wlLam ω‖ with hlam
  have hFe : wlF E z (onePortLift X) ω = 1 + 6 * ((1 + lam) * g) := rfl
  have hg0 : 0 ≤ g := norm_nonneg _
  have hl0 : 0 ≤ lam := norm_nonneg _
  refine ⟨hG'n.trans (by rw [hFe]; nlinarith), ?_⟩
  rw [wl_Kh_mul_eq hG']
  refine wl_norm_weighted_le.trans ?_
  have hb := wl_norm_Kh_sub_left_le E z (onePortLift X) ω hκ0
  have hG0 := norm_nonneg G'
  calc 1 + ‖wlKh (m := PortSite W .oneBlockOnePort)
          (z • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
            onePortLift X) - wlJ (PhysSite W .oneBlockOnePort) (PortSite W .oneBlockOnePort) *
        tflReg κ (layerMatrix .oneBlockOnePort E z (onePortLift X) ω)‖ * ‖G'‖
      ≤ 1 + (‖z‖ + |E| + κ + lam) * (2 * g) :=
        add_le_add le_rfl (mul_le_mul hb hG'n hG0 (by positivity))
    _ ≤ 2 * wlF E z (onePortLift X) ω := by
        rw [hFe]
        have : ‖z‖ + |E| + κ ≤ 6 := by linarith
        nlinarith

end Majorant

/-!
## 7. The covariance package and the doubled identity
-/

section Package

variable {W : ℕ}

/-- The majorant `H = (4 + 4η) F²` in coordinates (`F = wlF`). -/
def osdH (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) : ℝ :=
  (4 + 4 * (boundaryZ b E).im) *
    wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x) ^ 2

theorem osd_measurable_H (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Measurable (osdH b E X) :=
  measurable_const.mul (((wl_measurable_wlF E _ _).comp (tfl_measurable_embed W b _)).pow_const 2)

theorem osd_one_le_wlF (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    1 ≤ wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x) := by
  unfold wlF
  have h1 := norm_nonneg (wlLam (tflEmbed W b .oneBlockOnePort x))
  have h2 := norm_nonneg (layerResolvent .oneBlockOnePort E (boundaryZ b E) (onePortLift X)
    (tflEmbed W b .oneBlockOnePort x))
  nlinarith

theorem osd_wlF_ge_norm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    ‖osdG b E X x‖ ≤ wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x) := by
  have h1 := norm_nonneg (wlLam (tflEmbed W b .oneBlockOnePort x))
  have h2 := norm_nonneg (osdG b E X x)
  change ‖osdG b E X x‖ ≤ 1 + 6 * ((1 + ‖wlLam (tflEmbed W b .oneBlockOnePort x)‖) *
    ‖osdG b E X x‖)
  nlinarith

/-- `‖G_κ‖, ‖G_κ 𝒲_K‖ ≤ H` for the regularized doubled resolvent, `κ ∈ (0,1]`. -/
theorem osd_H_bound {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hE : |E| ≤ 2) (hz : ‖boundaryZ b E‖ ≤ 3) (hη : 0 ≤ (boundaryZ b E).im) {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) {x : TflCoord W .oneBlockOnePort → ℝ} (hx : IsUnit (osdN b E X x).det) :
    ‖coreG (osdC0 b E X) (osdL W b) κ x‖ ≤ osdH b E X x ∧
      ‖coreG (osdC0 b E X) (osdL W b) κ x * osdWK b E X‖ ≤ osdH b E X x := by
  rw [osd_coreG_eq hX hη hκ]
  obtain ⟨hu, hn⟩ := osd_reg_layer hX hη hκ x
  have hG' : tflReg κ (osdN b E X x) * (tflReg κ (osdN b E X x))⁻¹ = 1 := mul_nonsing_inv _ hu
  have hc : ((κ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') Complex.I_ne_zero
  have hnc : ‖(κ : ℂ) * Complex.I‖ = κ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  have hG'n : ‖(tflReg κ (osdN b E X x))⁻¹‖ ≤ 2 * ‖(osdN b E X x)⁻¹‖ :=
    tfl_inv_add_le_two hc hx hu (by rw [hnc]; exact hn)
  obtain ⟨hG, hK⟩ := osd_pointwise_le hE hz X (tflEmbed W b .oneBlockOnePort x) hκ.le hκ1 hG' hG'n
  exact osd_dbl_norm_le _ _ _ hη (osd_one_le_wlF b E X x)
    (wl_norm_Q_le (n := PhysSite W .oneBlockOnePort) (m := PortSite W .oneBlockOnePort)) hG hK

/-- `‖𝒩⁻¹‖ = ‖[[𝒢, -ηF], [0, -𝒢*]]‖ ≤ H` wherever `N` is invertible. -/
theorem osd_H_bound0 {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hE : |E| ≤ 2)
    (hz : ‖boundaryZ b E‖ ≤ 3) (hη : 0 ≤ (boundaryZ b E).im) {x : TflCoord W .oneBlockOnePort → ℝ}
    (hx : IsUnit (osdN b E X x).det) : ‖osdB b E X x‖ ≤ osdH b E X x := by
  have hG' : tflReg 0 (osdN b E X x) * osdG b E X x = 1 := by
    rw [wl_tflReg_zero]; exact mul_nonsing_inv _ hx
  have hG'n : ‖osdG b E X x‖ ≤ 2 * ‖(osdN b E X x)⁻¹‖ := by
    have := norm_nonneg ((osdN b E X x)⁻¹)
    change ‖(osdN b E X x)⁻¹‖ ≤ 2 * ‖(osdN b E X x)⁻¹‖
    linarith
  obtain ⟨hG, hK⟩ := osd_pointwise_le hE hz X (tflEmbed W b .oneBlockOnePort x) le_rfl
    zero_le_one hG' hG'n
  exact (osd_dbl_norm_le _ _ _ hη (osd_one_le_wlF b E X x)
    (wl_norm_Q_le (n := PhysSite W .oneBlockOnePort) (m := PortSite W .oneBlockOnePort)) hG hK).1

/-- **The covariance package.** For `W ≥ 1`, `b ∈ (0,1/2)`, passive `X`, `|E| ≤ 2`, `|z| ≤ 3`,
`η = Im z ≥ 0`, a.s. invertibility and `H⁴ ∈ L¹`: for deterministic `𝒫, 𝒬` and a weight `𝒲` with
`‖𝒲‖ ≤ 1` or `𝒲 = 𝒲_K`, the trace `f = W⁻¹ Tr(𝒫 𝒩⁻¹)`, the entries of `U = 𝒬 𝒩⁻¹ 𝒲` and of `fU`
are integrable and `‖Cov(f, U)‖ ≤ (40/W²) ‖𝒫‖ ‖𝒬‖ E H⁴` (entrywise expectations). -/
theorem osd_cov_pkg {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hW : 0 < W) (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hX : IsPassiveInput X) (hE : |E| ≤ 2) (hz : ‖boundaryZ b E‖ ≤ 3)
    (hη : 0 ≤ (boundaryZ b E).im)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b .oneBlockOnePort), IsUnit (osdN b E X x).det)
    (hH4 : Integrable (fun x => osdH b E X x ^ 4) (gaussianProduct (tflVar W b .oneBlockOnePort)))
    (P Q Wt : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ)
    (hWt : ‖Wt‖ ≤ 1 ∨ Wt = osdWK b E X) :
    Integrable (fun x => (W : ℂ)⁻¹ * (P * osdB b E X x).trace)
        (gaussianProduct (tflVar W b .oneBlockOnePort)) ∧
      (∀ i j, Integrable (fun x => (Q * osdB b E X x * Wt) i j)
        (gaussianProduct (tflVar W b .oneBlockOnePort))) ∧
      (∀ i j, Integrable (fun x => (W : ℂ)⁻¹ * (P * osdB b E X x).trace *
        (Q * osdB b E X x * Wt) i j) (gaussianProduct (tflVar W b .oneBlockOnePort))) ∧
      ‖meqCov (gaussianProduct (tflVar W b .oneBlockOnePort))
          (fun x => (W : ℂ)⁻¹ * (P * osdB b E X x).trace) (fun x => Q * osdB b E X x * Wt)‖ ≤
        40 / (W : ℝ) ^ 2 * ‖P‖ * ‖Q‖ *
          ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort) := by
  set μ := gaussianProduct (tflVar W b .oneBlockOnePort) with hμ
  have hreg := osd_coreReg (W := W) hX hη
  have hinvD : ∀ᵐ x ∂μ, IsUnit (osdC0 b E X + osdL W b x).det :=
    hinv.mono fun x hx => osd_det_dbl hx
  have hH : ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ᵐ x ∂μ,
      ‖coreG (osdC0 b E X) (osdL W b) κ x‖ ≤ osdH b E X x ∧
        ‖coreG (osdC0 b E X) (osdL W b) κ x * Wt‖ ≤ osdH b E X x := by
    intro κ hκ hκ1
    filter_upwards [hinv] with x hx
    obtain ⟨h1, h2⟩ := osd_H_bound hX hE hz hη hκ hκ1 hx
    refine ⟨h1, ?_⟩
    rcases hWt with h | rfl
    · refine (norm_mul_le _ _).trans ?_
      have := norm_nonneg (coreG (osdC0 b E X) (osdL W b) κ x)
      nlinarith
    · exact h2
  have hγ : (0 : ℝ) ≤ 40 / W := by positivity
  obtain ⟨hf, hU, hfU, hcov⟩ := osd_cov_limit (tflVar W b .oneBlockOnePort) hreg hγ
    (fun K => osd_contract_le hW hb0 hb1 K) ((W : ℝ)⁻¹) P Q Wt hinvD
    (osd_measurable_H b E X).aestronglyMeasurable hH hH4
  have hae : ∀ᵐ x ∂μ, (osdC0 b E X + osdL W b x)⁻¹ = osdB b E X x :=
    hinv.mono fun x hx => osd_inv_eq_B hx
  have hcast : (((W : ℝ)⁻¹ : ℝ) : ℂ) = (W : ℂ)⁻¹ := by push_cast; rfl
  have hf' : Integrable (fun x => (W : ℂ)⁻¹ * (P * osdB b E X x).trace) μ :=
    hf.congr (hae.mono fun x hx => by beta_reduce; rw [hx, hcast])
  have hU' : Integrable (fun x => Q * osdB b E X x * Wt) μ :=
    hU.congr (hae.mono fun x hx => by beta_reduce; rw [hx])
  have hfU' : Integrable (fun x => ((W : ℂ)⁻¹ * (P * osdB b E X x).trace) •
      (Q * osdB b E X x * Wt)) μ :=
    hfU.congr (hae.mono fun x hx => by beta_reduce; rw [hx, hcast])
  refine ⟨hf', fun i j => ?_, fun i j => ?_, ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j :
      Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ →ₗ[ℂ] ℂ)).integrable_comp hU'
  · have := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j :
      Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ →ₗ[ℂ] ℂ)).integrable_comp hfU'
    simpa using this
  · rw [meq_cov_eq hfU' hU']
    have e : (∫ x, ((W : ℂ)⁻¹ * (P * osdB b E X x).trace) • (Q * osdB b E X x * Wt) ∂μ) -
        (∫ x, (W : ℂ)⁻¹ * (P * osdB b E X x).trace ∂μ) • ∫ x, Q * osdB b E X x * Wt ∂μ =
        osdCov μ (fun x => (((W : ℝ)⁻¹ : ℝ) : ℂ) * (P * (osdC0 b E X + osdL W b x)⁻¹).trace)
          (fun x => Q * (osdC0 b E X + osdL W b x)⁻¹ * Wt) := by
      have i1 : ∫ x, ((W : ℂ)⁻¹ * (P * osdB b E X x).trace) • (Q * osdB b E X x * Wt) ∂μ =
          ∫ x, ((((W : ℝ)⁻¹ : ℝ) : ℂ) * (P * (osdC0 b E X + osdL W b x)⁻¹).trace) •
            (Q * (osdC0 b E X + osdL W b x)⁻¹ * Wt) ∂μ :=
        integral_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx, hcast])
      have i2 : ∫ x, (W : ℂ)⁻¹ * (P * osdB b E X x).trace ∂μ =
          ∫ x, (((W : ℝ)⁻¹ : ℝ) : ℂ) * (P * (osdC0 b E X + osdL W b x)⁻¹).trace ∂μ :=
        integral_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx, hcast])
      have i3 : ∫ x, Q * osdB b E X x * Wt ∂μ = ∫ x, Q * (osdC0 b E X + osdL W b x)⁻¹ * Wt ∂μ :=
        integral_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx])
      unfold osdCov
      rw [i1, i2, i3]
    rw [e]
    refine hcov.trans (le_of_eq ?_)
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    rw [abs_of_pos (inv_pos.mpr hW')]
    field_simp
    rfl

/-- **The doubled Schwinger–Dyson identity** (both the first- and the second-order identity of
the passive layer): `C₀ᴰ E[𝒩⁻¹] - E[𝒮ᴰ(𝒩⁻¹)𝒩⁻¹] = 1`, entrywise expectations, `𝒩⁻¹ = osdB`. -/
theorem osd_identity {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hE : |E| ≤ 2) (hz : ‖boundaryZ b E‖ ≤ 3) (hη : 0 ≤ (boundaryZ b E).im)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b .oneBlockOnePort), IsUnit (osdN b E X x).det)
    (hH4 : Integrable (fun x => osdH b E X x ^ 4) (gaussianProduct (tflVar W b .oneBlockOnePort))) :
    osdC0 b E X * matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort)) (osdB b E X) -
      matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort))
        (fun x => coreS (tflVar W b .oneBlockOnePort) (osdL W b) (osdB b E X x) * osdB b E X x) =
      1 := by
  set μ := gaussianProduct (tflVar W b .oneBlockOnePort) with hμ
  set v := tflVar W b .oneBlockOnePort with hv
  have hreg := osd_coreReg (W := W) hX hη
  have hinvD : ∀ᵐ x ∂μ, IsUnit (osdC0 b E X + osdL W b x).det :=
    hinv.mono fun x hx => osd_det_dbl hx
  have hae : ∀ᵐ x ∂μ, (osdC0 b E X + osdL W b x)⁻¹ = osdB b E X x :=
    hinv.mono fun x hx => osd_inv_eq_B hx
  have hGm : Measurable (fun x => (osdC0 b E X + osdL W b x)⁻¹) :=
    measurable_matrix_inv.comp (continuous_const.add (osdL W b).continuous).measurable
  have hbd : ∀ᵐ x ∂μ, ‖(osdC0 b E X + osdL W b x)⁻¹‖ ≤ osdH b E X x := by
    filter_upwards [hinv] with x hx
    rw [osd_inv_eq_B hx]
    exact osd_H_bound0 hE hz hη hx
  have hH0 : ∀ x, 0 ≤ osdH b E X x := fun x => by unfold osdH; positivity
  have hH2 : Integrable (fun x => osdH b E X x ^ 2) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hH4)
      ((osd_measurable_H b E X).pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact (osd_le_one_add_pow4 _).2
  have hH1 : Integrable (fun x => osdH b E X x) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hH4)
      (osd_measurable_H b E X).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (hH0 x)]
    exact (osd_le_one_add_pow4 _).1
  have hG2 : Integrable (fun x => ‖(osdC0 b E X + osdL W b x)⁻¹‖ ^ 2) μ := by
    refine Integrable.mono' hH2 (hGm.norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbd] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hI1 : Integrable (fun x => (osdC0 b E X + osdL W b x)⁻¹) μ :=
    Integrable.mono' hH1 hGm.aestronglyMeasurable hbd
  have hI2 : Integrable (fun x => coreS v (osdL W b) ((osdC0 b E X + osdL W b x)⁻¹) *
      (osdC0 b E X + osdL W b x)⁻¹) μ := by
    refine Integrable.mono' (hH2.const_mul (coreCS v (osdL W b)))
      ((core_continuous_S_mul v (osdL W b)).measurable.comp hGm).aestronglyMeasurable ?_
    filter_upwards [hbd] with x hx
    have hCS := coreCS_nonneg v (osdL W b)
    calc ‖coreS v (osdL W b) ((osdC0 b E X + osdL W b x)⁻¹) * (osdC0 b E X + osdL W b x)⁻¹‖
        ≤ ‖coreS v (osdL W b) ((osdC0 b E X + osdL W b x)⁻¹)‖ *
            ‖(osdC0 b E X + osdL W b x)⁻¹‖ := norm_mul_le _ _
      _ ≤ coreCS v (osdL W b) * ‖(osdC0 b E X + osdL W b x)⁻¹‖ *
            ‖(osdC0 b E X + osdL W b x)⁻¹‖ := by
          gcongr; exact core_norm_S_le v (osdL W b) _
      _ ≤ coreCS v (osdL W b) * osdH b E X x ^ 2 := by
          rw [mul_assoc, ← sq]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hCS
  have h := core_limit_identity v hreg hinvD hG2
  rw [← meq_matrixExpect_eq hI1, ← meq_matrixExpect_eq hI2] at h
  have e1 : matrixExpect μ (fun x => (osdC0 b E X + osdL W b x)⁻¹) = matrixExpect μ (osdB b E X) := by
    ext i j
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have e2 : matrixExpect μ (fun x => coreS v (osdL W b) ((osdC0 b E X + osdL W b x)⁻¹) *
      (osdC0 b E X + osdL W b x)⁻¹) =
      matrixExpect μ (fun x => coreS v (osdL W b) (osdB b E X x) * osdB b E X x) := by
    ext i j
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  rw [e1, e2] at h
  exact h

/-!
## 8. Moments and a.s. invertibility in coordinates
-/

/-- **Setup.** For `b ∈ (0,1/2)`, `κ > 0` there are `C_H ≥ 0`, `W₀` such that for `W ≥ W₀`, every
passive `X` and `E ∈ bulkInterval κ`: `N(x)` is a.s. invertible and `E H⁴ ≤ C_H` (with
`H⁴ ∈ L¹`), from `opm_passive_inverse_moments` (order 16, passive inputs) and the Gaussian moments
of `Λ` (`wl_lam_eLpNorm_le_layer`). -/
theorem osd_setup (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (CH : ℝ) (W₀ : ℕ), 0 ≤ CH ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      (∀ᵐ x ∂gaussianProduct (tflVar W b .oneBlockOnePort), IsUnit (osdN b E X x).det) ∧
      Integrable (fun x => osdH b E X x ^ 4) (gaussianProduct (tflVar W b .oneBlockOnePort)) ∧
      ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort) ≤ CH := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨CA, W₁, hCA, h1⟩ := opm_passive_inverse_moments hcount b hb0 hb1 κ hκ 16 (by norm_num)
  set CF : ℝ := 1 + 6 * (wlLamConst * CA) with hCF
  have hCF0 : 0 ≤ CF := by have := wlLamConst_pos; positivity
  refine ⟨16 ^ 4 * CF ^ 8, max W₁ 16, by positivity, ?_⟩
  intro W hW hWW X hX E hE
  obtain ⟨hzη, hzM, hE2⟩ := hbulk E hE
  have hη : 0 ≤ (boundaryZ b E).im := hη₀.le.trans hzη
  have hη3 : (boundaryZ b E).im ≤ 3 := (Complex.im_le_norm _).trans hzM
  obtain ⟨hinvL, hG16, -⟩ := h1 W hW (le_of_max_le_left hWW) X hX E hE
  have hW16 : (16 : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hWW
  have := bond_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
  have hL := wl_lam_eLpNorm_le_layer (σ := .oneBlockOnePort) hb0 hb1 (q := 2 * 8) (by norm_num)
    (by linarith)
  have hG16' : eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal (2 * 8))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal CA := by
    rw [show (2 : ℝ) * 8 = 16 by norm_num]; exact hG16
  have hF := wl_eLpNorm_F_le (μ := layerLaw W b .oneBlockOnePort)
    (Lam := fun ω => ‖wlLam ω‖) (Gn := fun ω => ‖onePortResolvent b E X ω‖)
    (continuous_norm.measurable.comp wl_measurable_wlLam).aestronglyMeasurable
    (measurable_norm_layerResolvent _ E _ _).aestronglyMeasurable (q := 8) (by norm_num)
    wlLamConst_pos.le hCA.le hL hG16'
  have hFm := wl_measurable_wlF (σ := .oneBlockOnePort) E (boundaryZ b E) (onePortLift X)
  have hF' : eLpNorm (fun ω => ‖wlF E (boundaryZ b E) (onePortLift X) ω‖)
      (ENNReal.ofReal ((8 : ℕ) : ℝ)) (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal CF := by
    rw [eLpNorm_norm _ hFm.aestronglyMeasurable]
    exact_mod_cast hF
  obtain ⟨hFi, hFI⟩ := tcv_moment (m := 8) (by norm_num) hCF0 hF'
  have hΦ := tfl_measurable_embed W b .oneBlockOnePort
  have hpow : ∀ x, osdH b E X x ^ 4 = (4 + 4 * (boundaryZ b E).im) ^ 4 *
      ‖wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x)‖ ^ 8 := by
    intro x
    rw [Real.norm_of_nonneg (wlF_nonneg _ _ _ _), osdH]
    ring
  have hgm : AEStronglyMeasurable (fun ω => ‖wlF E (boundaryZ b E) (onePortLift X) ω‖ ^ 8)
      (layerLaw W b .oneBlockOnePort) := (hFm.norm.pow_const 8).aestronglyMeasurable
  have hFi' : Integrable (fun x =>
      ‖wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x)‖ ^ 8)
      (gaussianProduct (tflVar W b .oneBlockOnePort)) := by
    rw [tfl_layerLaw_eq_map] at hFi hgm
    exact (integrable_map_measure hgm hΦ.aemeasurable).mp hFi
  have hFI' : ∫ x, ‖wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x)‖ ^ 8
      ∂gaussianProduct (tflVar W b .oneBlockOnePort) ≤ CF ^ 8 := by
    have e := integral_map (μ := gaussianProduct (tflVar W b .oneBlockOnePort)) hΦ.aemeasurable
      (by rw [← tfl_layerLaw_eq_map]; exact hgm)
    rw [← tfl_layerLaw_eq_map] at e
    rw [← e]
    exact hFI
  refine ⟨?_, ?_, ?_⟩
  · rw [tfl_layerLaw_eq_map] at hinvL
    exact ae_of_ae_map hΦ.aemeasurable hinvL
  · simp only [hpow]
    exact hFi'.const_mul _
  · simp only [hpow]
    rw [integral_const_mul]
    have h4 : (4 + 4 * (boundaryZ b E).im) ^ 4 ≤ 16 ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hI0 : 0 ≤ ∫ x, ‖wlF E (boundaryZ b E) (onePortLift X)
        (tflEmbed W b .oneBlockOnePort x)‖ ^ 8 ∂gaussianProduct (tflVar W b .oneBlockOnePort) :=
      integral_nonneg fun _ => by positivity
    calc (4 + 4 * (boundaryZ b E).im) ^ 4 * ∫ x, ‖wlF E (boundaryZ b E) (onePortLift X)
          (tflEmbed W b .oneBlockOnePort x)‖ ^ 8 ∂gaussianProduct (tflVar W b .oneBlockOnePort)
        ≤ 16 ^ 4 * CF ^ 8 := mul_le_mul h4 hFI' hI0 (by positivity)

end Package

end BlockBand.Layers
