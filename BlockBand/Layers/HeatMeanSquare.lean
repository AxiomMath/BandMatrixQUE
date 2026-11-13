module

public import BlockBand.Layers.HeatCoreMeanSquare
public import BlockBand.Layers.FreshCountMeanSquare
public import BlockBand.Layers.MatchedTraces
public import BlockBand.RankLocation.RankLocation

/-!
# The mean-square trace input `ChtMeanSquare` and the rank-location theorem

The input `ChtMeanSquare` of `CompensatedHeat`: along the interpolation `ℋ_t` the linearized
coefficients are `t(c + tb²a²)Q` and `tQ(cI + tb²a²𝟙𝟙ᵀ)`, whose row sums are at most
`(c + b²)/(1-b) + Cd < 1` and `(c + 2b²)/(1-b) + Cd < 1`, and the same stable-branch comparison as
in the layer-contraction lemma gives trace errors `O_{L²}(d + W⁻¹)` uniformly in `t`. Then the
compensated contracts and the rank-location theorem are assembled from `ConditionalBlockGUECount`
and `GaussianLpGradient` alone.

Law: `layerLaw W b σ`, `σ ∈ {.separate, .common}` (port coefficient `β = b` resp. `2b`),
deterministic Hermitian two-port `X` (the old Schur matrix), `E ∈ bulkInterval κ`,
`d = d(X) = matchedDistance b E X ≤ d_*`, `t ∈ (0, 1)`. Norms: `ℓ²` operator norm, modulus.

* §1 the layer data: weights `hmsWsep`, `hmsWcom` (`S(G) = D(g(G))`, `C₁ = D(a)`).
* §2 the reference inverse `Π = diag((z_∂ - X)⁻¹, a)` (`hmsR0`; `Π C₀ = 1`,
  `‖Π‖ ≤ ((1-b)α₀)⁻¹`), the linearized coefficients `Q_kl = W⁻¹Tr R_kl R_lk` on the tops and
  `a²` on the ports (`hms_Q_phys`, `hms_Q_port`), and the deterministic stability
  `hms_sep_stable`, `hms_com_stable` under `Σ_l |Q_kl| ≤ q`, `q(c + 2b²) ≤ 1 - m/2`,
  `m = b(1-2b)/(1-b)` (from `strictContraction_rowSum`: `q = (1-b)⁻¹ + C d`).
* §3 **`chtMeanSquare_holds (hcount) (hgrad) : ChtMeanSquare`** (through `hms_meanSquare_gen`).
* §4 **assembly**: `compensatedIncrement_holds`, `compensatedPhase_holds`,
  `ringCompensatedPhase_holds`, and **`rankLocation_holds (hcount) (hgrad) : RankLocationContract`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. The layer weights
-/

section LayerData

variable {W : ℕ}

/-- The separate-port weights: `c` on the block itself, `b` between a block and its port. -/
def hmsWsep (b : ℝ) : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → ℂ
  | .inl a, .inl a' => if a = a' then ((1 - 2 * b : ℝ) : ℂ) else 0
  | .inl a, .inr j => if a = j then (b : ℂ) else 0
  | .inr j, .inl a => if a = j then (b : ℂ) else 0
  | .inr _, .inr _ => 0

/-- The common-port weights. -/
def hmsWcom (b : ℝ) : Fin 2 ⊕ Fin 1 → Fin 2 ⊕ Fin 1 → ℂ
  | .inl a, .inl a' => if a = a' then ((1 - 2 * b : ℝ) : ℂ) else 0
  | .inl _, .inr _ => (b : ℂ)
  | .inr _, .inl _ => (b : ℂ)
  | .inr _, .inr _ => 0

theorem hms_wsep_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β γ : Fin 2 ⊕ Fin 2) :
    ‖hmsWsep b β γ‖ ≤ 1 := by
  have hc : ‖((1 - 2 * b : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hb : ‖(b : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]; linarith
  rcases β with a | j <;> rcases γ with a' | j' <;> simp only [hmsWsep] <;>
    (try split_ifs) <;> simp_all

theorem hms_wcom_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β γ : Fin 2 ⊕ Fin 1) :
    ‖hmsWcom b β γ‖ ≤ 1 := by
  have hc : ‖((1 - 2 * b : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hb : ‖(b : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]; linarith
  rcases β with a | j <;> rcases γ with a' | j' <;> simp only [hmsWcom] <;>
    (try split_ifs) <;> simp_all

theorem hms_sep_S (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    coreS (tflVar W b .separate) (meqLc W b .separate) G = hmsD (hmsWsep b) (coreTr G) := by
  change meqS W b .separate G = _
  rw [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0]
  ext p q
  rcases p with ⟨a, α⟩ | ⟨j, α⟩ <;> rcases q with ⟨c, γ⟩ | ⟨k, γ⟩ <;>
    (try fin_cases a) <;> (try fin_cases j) <;>
    simp [meqShift, hmsD, hmsS, diagonal_apply, coreBlk, coreTr, hmsWsep, Fintype.sum_sum_type,
      Fin.sum_univ_two, meqInc, LayerShape.incident]

theorem hms_com_S (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) :
    coreS (tflVar W b .common) (meqLc W b .common) G = hmsD (hmsWcom b) (coreTr G) := by
  change meqS W b .common G = _
  rw [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0]
  ext p q
  rcases p with ⟨a, α⟩ | ⟨j, α⟩ <;> rcases q with ⟨c, γ⟩ | ⟨k, γ⟩ <;>
    (try fin_cases a) <;> (try fin_cases j) <;>
    simp [meqShift, hmsD, hmsS, diagonal_apply, coreBlk, coreTr, hmsWcom, Fintype.sum_sum_type,
      Fin.sum_univ_two, meqInc, LayerShape.incident]
  all_goals (try split_ifs) <;> ring

theorem hms_sep_C1 (b E : ℝ) :
    (chtC1 (W := W) .separate b E b) = hmsD (hmsWsep b) (fun _ => matchedA E) := by
  ext x y
  rcases x with ⟨i, α⟩ | ⟨i, α⟩ <;> rcases y with ⟨j, γ⟩ | ⟨j, γ⟩ <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    simp [chtC1, hmsD, hmsS, hmsWsep, coreBlk, diagonal_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    (try split_ifs) <;> (try simp_all) <;> ring

theorem hms_com_C1 (b E : ℝ) :
    (chtC1 (W := W) .common b E (2 * b)) = hmsD (hmsWcom b) (fun _ => matchedA E) := by
  ext x y
  rcases x with ⟨i, α⟩ | ⟨i, α⟩ <;> rcases y with ⟨j, γ⟩ | ⟨j, γ⟩ <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    simp [chtC1, hmsD, hmsS, hmsWcom, coreBlk, diagonal_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    (try split_ifs) <;> (try simp_all) <;> ring

end LayerData

/-!
## 2. The reference inverse and the layer stability
-/

section LayerR0

variable {W : ℕ} {σ : LayerShape}

/-- The reference inverse `Π = diag((z_∂ - X)⁻¹, a)`. -/
def hmsR0 (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks ((boundaryZ b E • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)⁻¹) 0 0
    (matchedA E • 1)

theorem hms_R0_entry_ll (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (p q : PhysSite W σ) :
    hmsR0 b E X (Sum.inl p) (Sum.inl q) = (boundaryZ b E • 1 - X)⁻¹ p q := rfl

theorem hms_Q_phys (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (γ : Fin σ.blocks ⊕ Fin σ.ports) (k : Fin σ.blocks) :
    coreTr (hmsR0 b E X * coreProj γ * hmsR0 b E X) (Sum.inl k) =
      match γ with
      | .inl l => (W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W,
          (boundaryZ b E • 1 - X)⁻¹ (k, x) (l, y) * (boundaryZ b E • 1 - X)⁻¹ (l, y) (k, x)
      | .inr _ => 0 := by
  rcases γ with l | j
  · simp only [coreTr, Sum.elim_inl, physBlockTrace, Matrix.mul_apply, hms_proj_apply,
      Fintype.sum_sum_type, hmsR0, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      Matrix.zero_apply, mul_zero, zero_mul, add_zero, coreBlk, Sum.map_inl,
      Sum.map_inr, Sum.inl.injEq, reduceCtorEq, ite_false, Finset.sum_const_zero]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_mul,
      zero_mul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq']
  · simp only [coreTr, Sum.elim_inl, physBlockTrace, Matrix.mul_apply, hms_proj_apply,
      Fintype.sum_sum_type, hmsR0, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      Matrix.zero_apply, mul_zero, zero_mul, add_zero, coreBlk, Sum.map_inl,
      Sum.map_inr, reduceCtorEq, ite_false, Finset.sum_const_zero]
    simp

theorem hms_Q_port (hW : 0 < W) (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (γ : Fin σ.blocks ⊕ Fin σ.ports) (j : Fin σ.ports) :
    coreTr (hmsR0 b E X * coreProj γ * hmsR0 b E X) (Sum.inr j) =
      match γ with
      | .inl _ => 0
      | .inr j' => if j' = j then matchedA E ^ 2 else 0 := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rcases γ with l | j'
  · simp only [coreTr, Sum.elim_inr, portBlockTrace, Matrix.mul_apply, hms_proj_apply,
      Fintype.sum_sum_type, hmsR0, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, mul_zero, zero_mul, zero_add, coreBlk, Sum.map_inl,
      Sum.map_inr, reduceCtorEq, ite_false, Finset.sum_const_zero]
    simp
  · simp only [coreTr, Sum.elim_inr, portBlockTrace, Matrix.mul_apply, hms_proj_apply,
      Fintype.sum_sum_type, hmsR0, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, mul_zero, zero_mul, coreBlk, Sum.map_inl,
      Sum.map_inr, Sum.inr.injEq, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : j' = j
    · subst h
      simp [Finset.sum_ite_eq', hW', sq]
    · simp [h, Ne.symm h]

theorem hms_R0_tr_port (hW : 0 < W) (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (j : Fin σ.ports) : coreTr (hmsR0 b E X) (Sum.inr j) = matchedA E := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  simp [coreTr, portBlockTrace, hmsR0, hW']

theorem hms_R0_tr_phys (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (k : Fin σ.blocks) : coreTr (hmsR0 b E X) (Sum.inl k) =
      (W : ℂ)⁻¹ * ∑ x : Fin W, (boundaryZ b E • 1 - X)⁻¹ (k, x) (k, x) := rfl

/-- `Π C₀ = 1` and `‖Π‖ ≤ ((1-b)α₀)⁻¹` on the bulk. -/
theorem hms_R0_facts {b E α₀ : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hα₀ : 0 < α₀) (hE2 : |E| < 2)
    (ha1 : ‖matchedA E‖ = 1) (haim : (matchedA E).im ≤ -α₀)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) :
    hmsR0 b E X * chtC0 σ b E X = 1 ∧ ‖hmsR0 b E X‖ ≤ ((1 - b) * α₀)⁻¹ := by
  obtain ⟨hinv, -, hα, -⟩ := hms_a_facts hE2 ha1 haim
  have ha0 : matchedA E ≠ 0 := fun h => by rw [h, norm_zero] at ha1; exact zero_ne_one ha1
  have hzim : (boundaryZ b E).im = (1 - b) * (-(matchedA E).im) := by
    rw [boundaryZ, Complex.add_im, hinv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hδ : 0 < (1 - b) * α₀ := mul_pos (by linarith) hα₀
  have hzδ : (1 - b) * α₀ ≤ (boundaryZ b E).im := by
    rw [hzim]; exact mul_le_mul_of_nonneg_left hα (by linarith)
  have hH : (-X).IsHermitian := hX.neg
  have hcz : cplCoercive (boundaryZ b E).im
      (boundaryZ b E • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X) := by
    have := cht_coercive_herm_scalar hH (boundaryZ b E)
    rwa [neg_add_eq_sub] at this
  have hzu := (cpl_coercive_inv (lt_of_lt_of_le hδ hzδ) hcz).1
  have h1 : hmsR0 b E X * chtC0 σ b E X = 1 := by
    rw [hmsR0, cht_C0_eq hE2.le, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [nonsing_inv_mul _ hzu, smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ ha0, one_smul,
      fromBlocks_one]
  refine ⟨h1, ?_⟩
  have hco : cplCoercive ((1 - b) * α₀) (chtC0 σ b E X) := by
    rw [cht_C0_eq hE2.le]
    refine cht_coercive_fromBlocks hδ (cpl_coercive_mono hzδ hcz) ?_
    refine cpl_coercive_mono ?_ cpl_coercive_scalar
    rw [hinv]
    have : (1 - b) * α₀ ≤ 1 * α₀ := mul_le_mul_of_nonneg_right (by linarith) hα₀.le
    linarith
  rw [← Matrix.inv_eq_left_inv h1]
  exact (cpl_coercive_inv hδ hco).2

/-- The linearized layer equations in block form. -/
theorem hms_layer_eq (hW : 0 < W) (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ) (t : ℝ)
    (εb r : Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (h : ∀ β, εb β = (coreTr (hmsR0 b E X) β - matchedA E) +
      (t : ℂ) * ∑ γ, coreTr (hmsR0 b E X * coreProj γ * hmsR0 b E X) β * hmsS wt εb γ + r β) :
    (∀ k, εb (Sum.inl k) = (coreTr (hmsR0 b E X) (Sum.inl k) - matchedA E) +
      (t : ℂ) * ∑ l, ((W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W,
          (boundaryZ b E • 1 - X)⁻¹ (k, x) (l, y) * (boundaryZ b E • 1 - X)⁻¹ (l, y) (k, x)) *
        hmsS wt εb (Sum.inl l) + r (Sum.inl k)) ∧
    (∀ j, εb (Sum.inr j) = (t : ℂ) * (matchedA E ^ 2 * hmsS wt εb (Sum.inr j)) + r (Sum.inr j)) := by
  constructor
  · intro k
    rw [h (Sum.inl k), Fintype.sum_sum_type]
    simp only [hms_Q_phys, zero_mul, Finset.sum_const_zero, add_zero]
  · intro j
    rw [h (Sum.inr j), Fintype.sum_sum_type, hms_R0_tr_port hW, sub_self, zero_add]
    simp only [hms_Q_port hW, zero_mul, Finset.sum_const_zero, zero_add, ite_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The layer stability margin `m = b(1 - 2b)/(1 - b)`. -/
def hmsM (b : ℝ) : ℝ := b * (1 - 2 * b) / (1 - b)

/-- The layer stability constant. -/
def hmsCstL (b : ℝ) : ℝ := 2 * (3 * b + 1) * (1 + 2 * b) / hmsM b + 1

theorem hmsM_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) : 0 < hmsM b := by
  have : 0 < 1 - 2 * b := by linarith
  have : 0 < 1 - b := by linarith
  rw [hmsM]; positivity

theorem hms_sep_coef_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) :
    (1 - 2 * b + 2 * b ^ 2) / (1 - b) = 1 - hmsM b := by
  have : 1 - b ≠ 0 := by linarith
  rw [hmsM]; field_simp; ring

/-- The top step of the layer stability: from `x_k ≤ d + q((c + 2b²)M + bR) + R` for both tops,
`M ≤ (2/m)(3b + 1)(d + R)`. -/
theorem hms_top_close {b q d R x0 x1 : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hq3 : q ≤ 3) (hqc : q * (1 - 2 * b + 2 * b ^ 2) ≤ 1 - hmsM b / 2) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hx0 : 0 ≤ x0) (h0 : x0 ≤ d + q * ((1 - 2 * b + 2 * b ^ 2) * max x0 x1 + b * R) + R)
    (h1 : x1 ≤ d + q * ((1 - 2 * b + 2 * b ^ 2) * max x0 x1 + b * R) + R) :
    max x0 x1 ≤ 2 * (3 * b + 1) / hmsM b * (d + R) := by
  have hm := hmsM_pos hb0 hb1
  set M := max x0 x1
  have hM : M ≤ d + q * ((1 - 2 * b + 2 * b ^ 2) * M + b * R) + R := max_le h0 h1
  have hqb : q * b * R ≤ 3 * b * R := by
    have := mul_le_mul_of_nonneg_right hq3 (mul_nonneg hb0.le hR); nlinarith
  have hM0 : 0 ≤ M := hx0.trans (le_max_left _ _)
  have hqM := mul_le_mul_of_nonneg_right hqc hM0
  have h2 : hmsM b / 2 * M ≤ d + (3 * b + 1) * R := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  have h3 : d + (3 * b + 1) * R ≤ (3 * b + 1) * (d + R) := by nlinarith
  nlinarith

/-- **Stability of the separate-port layer** (in the paper: row sums `(c + b²)/(1-b) + Cd < 1`):
on `Σ_l |Q_kl| ≤ q` with `q(c + 2b²) ≤ 1 - m/2`, `q ≤ 3`. -/
theorem hms_sep_stable (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (ha1 : ‖matchedA E‖ = 1) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {q : ℝ}
    (hq3 : q ≤ 3) (hqc : q * (1 - 2 * b + 2 * b ^ 2) ≤ 1 - hmsM b / 2)
    (hrow : ∀ k : Fin 2, ∑ l : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ ≤ q)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HmsStable (hmsR0 (σ := .separate) b E X) (hmsWsep b) (matchedA E) t (matchedDistance b E X)
      (hmsCstL b) := by
  intro εb r h β
  obtain ⟨htop, hport⟩ := hms_layer_eq hW (σ := .separate) b E X (hmsWsep b) t εb r h
  set d := matchedDistance b E X
  have hd : 0 ≤ d := (norm_nonneg _).trans (cmp_le_matchedDistance b E X 0)
  set R := ∑ γ, ‖r γ‖ with hRdef
  have hr : ∀ γ, ‖r γ‖ ≤ R := fun γ =>
    Finset.single_le_sum (f := fun γ => ‖r γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb' : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hc' : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set x0 := ‖εb (Sum.inl 0)‖
  set x1 := ‖εb (Sum.inl 1)‖
  set M := max x0 x1 with hMdef
  have hxM : ∀ l : Fin 2, ‖εb (Sum.inl l)‖ ≤ M := fun l => by
    fin_cases l
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hsP : ∀ j : Fin 2, hmsS (hmsWsep b) εb (Sum.inr j) = (b : ℂ) * εb (Sum.inl j) := by
    intro j; fin_cases j <;> simp [hmsS, hmsWsep, Fintype.sum_sum_type]
  have hsT : ∀ l : Fin 2, hmsS (hmsWsep b) εb (Sum.inl l) =
      ((1 - 2 * b : ℝ) : ℂ) * εb (Sum.inl l) + (b : ℂ) * εb (Sum.inr l) := by
    intro l; fin_cases l <;> simp [hmsS, hmsWsep, Fintype.sum_sum_type]
  have hy : ∀ j : Fin 2, ‖εb (Sum.inr j)‖ ≤ b * M + R := fun j => by
    rw [hport j]
    refine (hms_norm_ta2 ha1 ht0 ht1).trans (add_le_add ?_ (hr _))
    rw [hsP, norm_mul, hb']
    exact mul_le_mul_of_nonneg_left (hxM j) hb0.le
  have hs : ∀ l : Fin 2, ‖hmsS (hmsWsep b) εb (Sum.inl l)‖ ≤
      (1 - 2 * b + 2 * b ^ 2) * M + b * R := fun l => by
    rw [hsT]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hc', hb']
    have h1 := hxM l
    have h2 := hy l
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hxM 0)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - 2 * b),
      mul_le_mul_of_nonneg_left h2 hb0.le, sq_nonneg b, mul_nonneg (sq_nonneg b) hM0]
  have hS0 : 0 ≤ (1 - 2 * b + 2 * b ^ 2) * M + b * R := by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hxM 0)
    have : 0 ≤ 1 - 2 * b + 2 * b ^ 2 := by nlinarith
    positivity
  have hx : ∀ k : Fin 2, ‖εb (Sum.inl k)‖ ≤
      d + q * ((1 - 2 * b + 2 * b ^ 2) * M + b * R) + R := fun k => by
    rw [htop k]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      (hr _))
    · rw [hms_R0_tr_phys]; exact cmp_le_matchedDistance b E X k
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ((norm_sum_le _ _).trans ?_)
      calc ∑ l, ‖((W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W,
            (boundaryZ b E • 1 - X)⁻¹ (k, x) (l, y) * (boundaryZ b E • 1 - X)⁻¹ (l, y) (k, x)) *
            hmsS (hmsWsep b) εb (Sum.inl l)‖
          ≤ ∑ l, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ *
              ((1 - 2 * b + 2 * b ^ 2) * M + b * R) :=
            Finset.sum_le_sum fun l _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hs l) (norm_nonneg _)
        _ ≤ q * ((1 - 2 * b + 2 * b ^ 2) * M + b * R) := by
            rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hrow k) hS0
  have hMb := hms_top_close hb0 hb1 hq3 hqc hd hR0 (norm_nonneg _) (hx 0) (hx 1)
  rw [← hMdef] at hMb
  have hm := hmsM_pos hb0 hb1
  set Q := 2 * (3 * b + 1) / hmsM b with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hdR : 0 ≤ d + R := by positivity
  rw [hmsCstL]
  have e : 2 * (3 * b + 1) * (1 + 2 * b) / hmsM b = Q * (1 + 2 * b) := by rw [hQ]; ring
  rw [e]
  rcases β with k | j
  · have := (hxM k).trans hMb
    nlinarith [mul_nonneg hQ0 hdR, mul_nonneg (mul_nonneg hQ0 hdR) hb0.le]
  · have h1 := hy j
    have h2 : b * M ≤ b * (Q * (d + R)) := mul_le_mul_of_nonneg_left hMb hb0.le
    nlinarith [mul_nonneg hQ0 hdR, mul_nonneg (mul_nonneg hQ0 hdR) hb0.le]

/-- **Stability of the common-port layer** (in the paper: row sums `(c + 2b²)/(1-b) + Cd < 1`):
on `Σ_l |Q_kl| ≤ q` with `q(c + 2b²) ≤ 1 - m/2`, `q ≤ 3`. -/
theorem hms_com_stable (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (ha1 : ‖matchedA E‖ = 1) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {q : ℝ}
    (hq3 : q ≤ 3) (hqc : q * (1 - 2 * b + 2 * b ^ 2) ≤ 1 - hmsM b / 2)
    (hrow : ∀ k : Fin 2, ∑ l : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ ≤ q)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HmsStable (hmsR0 (σ := .common) b E X) (hmsWcom b) (matchedA E) t (matchedDistance b E X)
      (hmsCstL b) := by
  intro εb r h β
  obtain ⟨htop, hport⟩ := hms_layer_eq hW (σ := .common) b E X (hmsWcom b) t εb r h
  set d := matchedDistance b E X
  have hd : 0 ≤ d := (norm_nonneg _).trans (cmp_le_matchedDistance b E X 0)
  set R := ∑ γ, ‖r γ‖ with hRdef
  have hr : ∀ γ, ‖r γ‖ ≤ R := fun γ =>
    Finset.single_le_sum (f := fun γ => ‖r γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb' : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hc' : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set x0 := ‖εb (Sum.inl 0)‖
  set x1 := ‖εb (Sum.inl 1)‖
  set M := max x0 x1 with hMdef
  have hxM : ∀ l : Fin 2, ‖εb (Sum.inl l)‖ ≤ M := fun l => by
    fin_cases l
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hsP : ∀ j : Fin 1, hmsS (hmsWcom b) εb (Sum.inr j) =
      (b : ℂ) * (εb (Sum.inl 0) + εb (Sum.inl 1)) := by
    intro j; simp [hmsS, hmsWcom, Fintype.sum_sum_type, Fin.sum_univ_two]; ring
  have hsT : ∀ l : Fin 2, hmsS (hmsWcom b) εb (Sum.inl l) =
      ((1 - 2 * b : ℝ) : ℂ) * εb (Sum.inl l) + (b : ℂ) * εb (Sum.inr 0) := by
    intro l; fin_cases l <;> simp [hmsS, hmsWcom, Fintype.sum_sum_type]
  have hy : ∀ j : Fin 1, ‖εb (Sum.inr j)‖ ≤ 2 * b * M + R := fun j => by
    rw [hport j]
    refine (hms_norm_ta2 ha1 ht0 ht1).trans (add_le_add ?_ (hr _))
    rw [hsP, norm_mul, hb']
    have := norm_add_le (εb (Sum.inl 0)) (εb (Sum.inl 1))
    have h0 := hxM 0
    have h1 := hxM 1
    nlinarith [mul_le_mul_of_nonneg_left this hb0.le]
  have hs : ∀ l : Fin 2, ‖hmsS (hmsWcom b) εb (Sum.inl l)‖ ≤
      (1 - 2 * b + 2 * b ^ 2) * M + b * R := fun l => by
    rw [hsT]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hc', hb']
    have h1 := hxM l
    have h2 := hy 0
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hxM 0)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - 2 * b),
      mul_le_mul_of_nonneg_left h2 hb0.le, sq_nonneg b, mul_nonneg (sq_nonneg b) hM0]
  have hS0 : 0 ≤ (1 - 2 * b + 2 * b ^ 2) * M + b * R := by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hxM 0)
    have : 0 ≤ 1 - 2 * b + 2 * b ^ 2 := by nlinarith
    positivity
  have hx : ∀ k : Fin 2, ‖εb (Sum.inl k)‖ ≤
      d + q * ((1 - 2 * b + 2 * b ^ 2) * M + b * R) + R := fun k => by
    rw [htop k]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      (hr _))
    · rw [hms_R0_tr_phys]; exact cmp_le_matchedDistance b E X k
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ((norm_sum_le _ _).trans ?_)
      calc ∑ l, ‖((W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W,
            (boundaryZ b E • 1 - X)⁻¹ (k, x) (l, y) * (boundaryZ b E • 1 - X)⁻¹ (l, y) (k, x)) *
            hmsS (hmsWcom b) εb (Sum.inl l)‖
          ≤ ∑ l, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ *
              ((1 - 2 * b + 2 * b ^ 2) * M + b * R) :=
            Finset.sum_le_sum fun l _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hs l) (norm_nonneg _)
        _ ≤ q * ((1 - 2 * b + 2 * b ^ 2) * M + b * R) := by
            rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hrow k) hS0
  have hMb := hms_top_close hb0 hb1 hq3 hqc hd hR0 (norm_nonneg _) (hx 0) (hx 1)
  rw [← hMdef] at hMb
  have hm := hmsM_pos hb0 hb1
  set Q := 2 * (3 * b + 1) / hmsM b with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hdR : 0 ≤ d + R := by positivity
  rw [hmsCstL]
  have e : 2 * (3 * b + 1) * (1 + 2 * b) / hmsM b = Q * (1 + 2 * b) := by rw [hQ]; ring
  rw [e]
  rcases β with k | j
  · have := (hxM k).trans hMb
    nlinarith [mul_nonneg hQ0 hdR, mul_nonneg (mul_nonneg hQ0 hdR) hb0.le]
  · have h1 := hy j
    have h2 : 2 * b * M ≤ 2 * b * (Q * (d + R)) := mul_le_mul_of_nonneg_left hMb (by positivity)
    nlinarith [mul_nonneg hQ0 hdR, mul_nonneg (mul_nonneg hQ0 hdR) hb0.le]

end LayerR0

/-!
## 3. `ChtMeanSquare`
-/

section LayerMain

theorem hmsM_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) : hmsM b ≤ b := by
  have h1 : 0 < 1 - b := by linarith
  rw [hmsM, div_le_iff₀ h1]; nlinarith

/-- The row-sum parameters: on `C' d ≤ m/2`, `q = (1-b)⁻¹ + C' d` satisfies `0 ≤ q ≤ 3` and
`q(c + 2b²) ≤ 1 - m/2`. -/
theorem hms_q_facts {b C' d : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hC' : 0 ≤ C') (hd : 0 ≤ d)
    (hCd : C' * d ≤ hmsM b / 2) :
    0 ≤ (1 - b)⁻¹ + C' * d ∧ (1 - b)⁻¹ + C' * d ≤ 3 ∧
      ((1 - b)⁻¹ + C' * d) * (1 - 2 * b + 2 * b ^ 2) ≤ 1 - hmsM b / 2 := by
  have h1 : 0 < 1 - b := by linarith
  have hinv : (1 - b)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h1 two_pos]; linarith
  have hm := hmsM_le hb0 hb1
  have hCd0 : 0 ≤ C' * d := mul_nonneg hC' hd
  refine ⟨by positivity, by linarith, ?_⟩
  have e := hms_sep_coef_le hb0 hb1
  have hc : 0 ≤ 1 - 2 * b + 2 * b ^ 2 := by nlinarith
  have hc1 : 1 - 2 * b + 2 * b ^ 2 ≤ 1 := by nlinarith
  have e2 : (1 - b)⁻¹ * (1 - 2 * b + 2 * b ^ 2) = 1 - hmsM b := by
    rw [← e]; field_simp
  have h3 : C' * d * (1 - 2 * b + 2 * b ^ 2) ≤ C' * d := mul_le_of_le_one_right hCd0 hc1
  nlinarith

/-- **The separate-port clause of `ChtMeanSquare`**. -/
theorem hms_meanSquare_separate (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr .separate E (chtHeat .separate b E X b t ω)⁻¹ ∂layerLaw W b .separate ≤
        C * (matchedDistance b E X ^ 2 + ((W : ℝ) ^ 2)⁻¹) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  intro b hb0 hb1 κ hκ
  obtain ⟨CA, W₁, hCA, hmom⟩ := hms_layer_moments hcount hb0 hb1 hκ
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨Crs, hCrs⟩ := strictContraction_rowSum b hb0 hb1 κ hκ
  set C' := max Crs 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hm := hmsM_pos hb0 hb1
  set d₁ := hmsM b / (2 * (C' + 1)) with hd₁
  have hd₁0 : 0 < d₁ := by positivity
  set nB : ℝ := (Fintype.card (Fin LayerShape.separate.blocks ⊕
    Fin LayerShape.separate.ports) : ℝ)
  set ρ := ((1 - b) * α₀)⁻¹ with hρ
  set K1 := hmsK1 nB (hmsCstL b) (hmsKr nB ρ CA) with hK1def
  have hK1 : 1 ≤ K1 := hmsK1_ge_one (Nat.cast_nonneg _)
  set Kf := 4 * Real.sqrt 2 * Cg * 4 * CA ^ 2 with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  refine ⟨min d₁ (1 / (4 * K1)), 2 * K1 * max 1 (Kf ^ 2), max W₁ (⌈4 * K1 * Kf⌉₊ + 1),
    lt_min hd₁0 (by positivity), fun W hW hW₀ X hX E hE hdX t ht => ?_⟩
  obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set d := matchedDistance b E X with hddef
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (cmp_le_matchedDistance b E X 0)
  have hWK : 4 * K1 * Kf < W := by
    have h1 := Nat.le_ceil (4 * K1 * Kf)
    have h2 : ((⌈4 * K1 * Kf⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
    push_cast at h2; linarith
  have hV : hmsV Cg 4 CA W = Kf / W := by rw [hmsV, hKf]
  have hV0 : 0 ≤ Kf / W := div_nonneg hKf0 hW'.le
  have hVs : Kf / W * (4 * K1) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hW']; linarith
  have hV1 : hmsV Cg 4 CA W ≤ 1 := by
    rw [hV]
    have : Kf / W * 1 ≤ Kf / W * (4 * K1) := mul_le_mul_of_nonneg_left (by linarith) hV0
    linarith
  have hdK : d * (4 * K1) ≤ 1 := by
    have := hdX.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsmall : 4 * K1 * (K1 * (d ^ 2 + hmsV Cg 4 CA W ^ 2)) < 1 := by
    rw [hV]
    have h1 : (d * (4 * K1)) ^ 2 ≤ 1 := by
      have := mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 4 * K1); nlinarith
    have h2 : (Kf / W * (4 * K1)) ^ 2 < 1 := by
      have := mul_nonneg hV0 (by linarith : (0 : ℝ) ≤ 4 * K1); nlinarith
    nlinarith
  obtain ⟨hR0, hR0b⟩ := hms_R0_facts (W := W) (σ := .separate) hb0.le (by linarith) hα₀ hE2
    ha1 haim hX
  have hCd : C' * d ≤ hmsM b / 2 := by
    have h1 : d ≤ d₁ := hdX.trans (min_le_left _ _)
    calc C' * d ≤ C' * d₁ := mul_le_mul_of_nonneg_left h1 hC'0
      _ ≤ hmsM b / 2 := by
        rw [hd₁, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith
  obtain ⟨-, hq3, hqc⟩ := hms_q_facts hb0 hb1 hC'0 hd0 hCd
  have hrow : ∀ k : Fin 2, ∑ l : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ ≤
      (1 - b)⁻¹ + C' * d := fun k =>
    (hCrs W hW X hX E hE k).trans (by gcongr; exact le_max_left _ _)
  have hCst0 : 0 ≤ hmsCstL b := by rw [hmsCstL]; positivity
  have hstab : ∀ t ∈ Set.Ico (0 : ℝ) 1, HmsStable (hmsR0 (σ := .separate) b E X) (hmsWsep b)
      (matchedA E) t d (hmsCstL b) := fun t ht =>
    hms_sep_stable hW hb0 hb1 ha1 hq3 hqc hrow ht.1 ht.2.le
  have h0 : ∑ δ, ‖coreTr (hmsR0 (σ := .separate) b E X) δ - matchedA E‖ ^ 2 ≤ 2 * d ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp only [hms_R0_tr_port hW, sub_self, norm_zero]
    have hk : ∀ k : Fin 2, ‖coreTr (hmsR0 (σ := .separate) b E X) (Sum.inl k) - matchedA E‖ ^ 2
        ≤ d ^ 2 := fun k =>
      pow_le_pow_left₀ (norm_nonneg _) (by rw [hms_R0_tr_phys]; exact cmp_le_matchedDistance b E X k) 2
    simp only [Fin.sum_univ_two, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    linarith [hk 0, hk 1]
  have key := hms_meanSquare_gen (tflVar W b .separate) (σ := .separate) hW
    (cht_lin_isHermitian .separate b) (hms_wsep_le hb0.le hb1.le) (hms_sep_S hW hb0.le hb1.le)
    (hms_sep_C1 b E) hR0 hR0b
    (hms_coer_unif (cht_layer_coercive hb1 hb0.le (by linarith) hE2 hX)) hCg.le hgr
    (by norm_num : (0 : ℝ) ≤ 4) (hms_layer_weighted_le hW hb0 hb1) hCA.le
    (fun t ht => hmom W hW ((le_max_left _ _).trans hW₀) .separate b hb0.le (by linarith) X hX
      E hE t ht) hd0 hCst0 hstab h0 hV1 hsmall t ⟨ht.1.le, ht.2⟩
  -- transfer to the layer law
  have hlaw := tfl_layerLaw_eq_map W b .separate
  have hΦ := tfl_measurable_embed W b .separate
  have hm' : Measurable (fun ω : LayerSample W .separate =>
      chtErr .separate E (chtHeat .separate b E X b t ω)⁻¹) :=
    (cht_continuous_err E).measurable.comp
      (measurable_matrix_inv.comp (cht_measurable_heat .separate b E X b t))
  rw [hlaw, integral_map hΦ.aemeasurable hm'.aestronglyMeasurable]
  have e : ∫ x, chtErr .separate E (chtHeat .separate b E X b t (tflEmbed W b _ x))⁻¹
      ∂gaussianProduct (tflVar W b .separate) =
      hmsErr (tflVar W b .separate) (chtC0 .separate b E X) (chtC1 .separate b E b)
        (meqLc W b .separate) (matchedA E) t := by
    rw [hmsErr]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [hms_chtErr_eq, cht_heat_embed]
  rw [e]
  refine key.trans ?_
  rw [hV, ← hK1def]
  have hmx : 1 ≤ max 1 (Kf ^ 2) := le_max_left _ _
  have hmx2 : Kf ^ 2 ≤ max 1 (Kf ^ 2) := le_max_right _ _
  have e2 : (Kf / W) ^ 2 = Kf ^ 2 * ((W : ℝ) ^ 2)⁻¹ := by field_simp
  rw [e2]
  have hWi : 0 ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K1 := by linarith
  calc 2 * (K1 * (d ^ 2 + Kf ^ 2 * ((W : ℝ) ^ 2)⁻¹))
      ≤ 2 * (K1 * (max 1 (Kf ^ 2) * d ^ 2 + max 1 (Kf ^ 2) * ((W : ℝ) ^ 2)⁻¹)) := by
        gcongr
        · exact le_mul_of_one_le_left hd2 hmx
    _ = 2 * K1 * max 1 (Kf ^ 2) * (d ^ 2 + ((W : ℝ) ^ 2)⁻¹) := by ring

/-- **The common-port clause of `ChtMeanSquare`**. -/
theorem hms_meanSquare_common (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr .common E (chtHeat .common b E X (2 * b) t ω)⁻¹ ∂layerLaw W b .common ≤
        C * (matchedDistance b E X ^ 2 + ((W : ℝ) ^ 2)⁻¹) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  intro b hb0 hb1 κ hκ
  obtain ⟨CA, W₁, hCA, hmom⟩ := hms_layer_moments hcount hb0 hb1 hκ
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨Crs, hCrs⟩ := strictContraction_rowSum b hb0 hb1 κ hκ
  set C' := max Crs 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hm := hmsM_pos hb0 hb1
  set d₁ := hmsM b / (2 * (C' + 1)) with hd₁
  have hd₁0 : 0 < d₁ := by positivity
  set nB : ℝ := (Fintype.card (Fin LayerShape.common.blocks ⊕
    Fin LayerShape.common.ports) : ℝ)
  set ρ := ((1 - b) * α₀)⁻¹ with hρ
  set K1 := hmsK1 nB (hmsCstL b) (hmsKr nB ρ CA) with hK1def
  have hK1 : 1 ≤ K1 := hmsK1_ge_one (Nat.cast_nonneg _)
  set Kf := 4 * Real.sqrt 2 * Cg * 4 * CA ^ 2 with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  refine ⟨min d₁ (1 / (4 * K1)), 2 * K1 * max 1 (Kf ^ 2), max W₁ (⌈4 * K1 * Kf⌉₊ + 1),
    lt_min hd₁0 (by positivity), fun W hW hW₀ X hX E hE hdX t ht => ?_⟩
  obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set d := matchedDistance b E X with hddef
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (cmp_le_matchedDistance b E X 0)
  have hWK : 4 * K1 * Kf < W := by
    have h1 := Nat.le_ceil (4 * K1 * Kf)
    have h2 : ((⌈4 * K1 * Kf⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
    push_cast at h2; linarith
  have hV : hmsV Cg 4 CA W = Kf / W := by rw [hmsV, hKf]
  have hV0 : 0 ≤ Kf / W := div_nonneg hKf0 hW'.le
  have hVs : Kf / W * (4 * K1) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hW']; linarith
  have hV1 : hmsV Cg 4 CA W ≤ 1 := by
    rw [hV]
    have : Kf / W * 1 ≤ Kf / W * (4 * K1) := mul_le_mul_of_nonneg_left (by linarith) hV0
    linarith
  have hdK : d * (4 * K1) ≤ 1 := by
    have := hdX.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsmall : 4 * K1 * (K1 * (d ^ 2 + hmsV Cg 4 CA W ^ 2)) < 1 := by
    rw [hV]
    have h1 : (d * (4 * K1)) ^ 2 ≤ 1 := by
      have := mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 4 * K1); nlinarith
    have h2 : (Kf / W * (4 * K1)) ^ 2 < 1 := by
      have := mul_nonneg hV0 (by linarith : (0 : ℝ) ≤ 4 * K1); nlinarith
    nlinarith
  obtain ⟨hR0, hR0b⟩ := hms_R0_facts (W := W) (σ := .common) hb0.le (by linarith) hα₀ hE2
    ha1 haim hX
  have hCd : C' * d ≤ hmsM b / 2 := by
    have h1 : d ≤ d₁ := hdX.trans (min_le_left _ _)
    calc C' * d ≤ C' * d₁ := mul_le_mul_of_nonneg_left h1 hC'0
      _ ≤ hmsM b / 2 := by
        rw [hd₁, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith
  obtain ⟨-, hq3, hqc⟩ := hms_q_facts hb0 hb1 hC'0 hd0 hCd
  have hrow : ∀ k : Fin 2, ∑ l : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k l‖ ≤
      (1 - b)⁻¹ + C' * d := fun k =>
    (hCrs W hW X hX E hE k).trans (by gcongr; exact le_max_left _ _)
  have hCst0 : 0 ≤ hmsCstL b := by rw [hmsCstL]; positivity
  have hstab : ∀ t ∈ Set.Ico (0 : ℝ) 1, HmsStable (hmsR0 (σ := .common) b E X) (hmsWcom b)
      (matchedA E) t d (hmsCstL b) := fun t ht =>
    hms_com_stable hW hb0 hb1 ha1 hq3 hqc hrow ht.1 ht.2.le
  have h0 : ∑ δ, ‖coreTr (hmsR0 (σ := .common) b E X) δ - matchedA E‖ ^ 2 ≤ 2 * d ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp only [hms_R0_tr_port hW, sub_self, norm_zero]
    have hk : ∀ k : Fin 2, ‖coreTr (hmsR0 (σ := .common) b E X) (Sum.inl k) - matchedA E‖ ^ 2
        ≤ d ^ 2 := fun k =>
      pow_le_pow_left₀ (norm_nonneg _) (by rw [hms_R0_tr_phys]; exact cmp_le_matchedDistance b E X k) 2
    simp only [Fin.sum_univ_two, Fin.sum_univ_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero]
    linarith [hk 0, hk 1]
  have key := hms_meanSquare_gen (tflVar W b .common) (σ := .common) hW
    (cht_lin_isHermitian .common b) (hms_wcom_le hb0.le hb1.le) (hms_com_S hW hb0.le hb1.le)
    (hms_com_C1 b E) hR0 hR0b
    (hms_coer_unif (cht_layer_coercive hb1 (by linarith) le_rfl hE2 hX)) hCg.le hgr
    (by norm_num : (0 : ℝ) ≤ 4) (hms_layer_weighted_le hW hb0 hb1) hCA.le
    (fun t ht => hmom W hW ((le_max_left _ _).trans hW₀) .common (2 * b) (by linarith) le_rfl X hX
      E hE t ht) hd0 hCst0 hstab h0 hV1 hsmall t ⟨ht.1.le, ht.2⟩
  -- transfer to the layer law
  have hlaw := tfl_layerLaw_eq_map W b .common
  have hΦ := tfl_measurable_embed W b .common
  have hm' : Measurable (fun ω : LayerSample W .common =>
      chtErr .common E (chtHeat .common b E X (2 * b) t ω)⁻¹) :=
    (cht_continuous_err E).measurable.comp
      (measurable_matrix_inv.comp (cht_measurable_heat .common b E X (2 * b) t))
  rw [hlaw, integral_map hΦ.aemeasurable hm'.aestronglyMeasurable]
  have e : ∫ x, chtErr .common E (chtHeat .common b E X (2 * b) t (tflEmbed W b _ x))⁻¹
      ∂gaussianProduct (tflVar W b .common) =
      hmsErr (tflVar W b .common) (chtC0 .common b E X) (chtC1 .common b E (2 * b))
        (meqLc W b .common) (matchedA E) t := by
    rw [hmsErr]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [hms_chtErr_eq, cht_heat_embed]
  rw [e]
  refine key.trans ?_
  rw [hV, ← hK1def]
  have hmx : 1 ≤ max 1 (Kf ^ 2) := le_max_left _ _
  have hmx2 : Kf ^ 2 ≤ max 1 (Kf ^ 2) := le_max_right _ _
  have e2 : (Kf / W) ^ 2 = Kf ^ 2 * ((W : ℝ) ^ 2)⁻¹ := by field_simp
  rw [e2]
  have hWi : 0 ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K1 := by linarith
  calc 2 * (K1 * (d ^ 2 + Kf ^ 2 * ((W : ℝ) ^ 2)⁻¹))
      ≤ 2 * (K1 * (max 1 (Kf ^ 2) * d ^ 2 + max 1 (Kf ^ 2) * ((W : ℝ) ^ 2)⁻¹)) := by
        gcongr
        · exact le_mul_of_one_le_left hd2 hmx
    _ = 2 * K1 * max 1 (Kf ^ 2) * (d ^ 2 + ((W : ℝ) ^ 2)⁻¹) := by ring

/-- **`ChtMeanSquare`** (compensated-phase lemma: "trace errors `O_{L²}(d + W⁻¹)` uniformly in
`t`"). Law: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, bonds `Gin(b/W)`), `σ = .separate` with port
coefficient `β = b`, `σ = .common` with `β = 2b`; the heat matrix `ℋ_t = chtHeat σ b E X β t`.
Domain: deterministic Hermitian two-port `X` with `d(X) = matchedDistance b E X ≤ d_*`,
`E ∈ bulkInterval κ`, `t ∈ (0, 1)`, `W ≥ W₀`. Norms: complex modulus of the normalized block
traces `g_k, u_j` of `ℋ_t⁻¹` (`chtErr`). Quantifier order: `b, κ` first, then `d_*, C, W₀`, then
`W, X, E, t`; `E[Σ_k |g_k - a|² + Σ_j |u_j - a|²] ≤ C (d(X)² + W⁻²)`. Uniformity: in `W ≥ W₀`,
`X`, `E` and `t`; the constants depend on `b, κ` and the constants of the two inputs only. No
limits are taken. Inputs: `ConditionalBlockGUECount` (inverse moments `hms_layer_moments`),
`GaussianLpGradient` (fluctuations, `hms_path_fl`) and `strictContraction_rowSum`. -/
theorem chtMeanSquare_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : ChtMeanSquare :=
  ⟨hms_meanSquare_separate hcount hgrad, hms_meanSquare_common hcount hgrad⟩

end LayerMain

/-!
## 4. Assembly
-/

section Assembly

/-- **`CompensatedIncrementContract`** (conditional phase increments, a display in the proof of
the compensated-phase lemma), from `ConditionalBlockGUECount` and `GaussianLpGradient`.

* Law: the fresh layer `layerLaw W b .separate` (resp. `.common`), conditional on a deterministic
  Hermitian two-port deformation `X` (the old path).
* Domain: `b ∈ (0, 1/2)`, `W ≥ 1`, every Hermitian `X`, deterministic `E ∈ bulkInterval κ`.
* Statement: separate ports
  `|E[N_-(A-E-X) + Θ_{z_∂}(X₊)] - Θ_{z_∂}(X) - 2W F_sc(E)| ≤ C(W d(X)² + W⁻¹)`; common port (`Ξ`)
  `|E[N_-(A-E-X) + Θ_{z₀}(X₊)] - Θ_{z_∂}(X) - W(ℓ + h)| ≤ C(W d(X)² + W⁻¹)` (absolute values of
  real expectations; no `L^p` norm).
* Quantifier order and uniformity: `b, κ` first, then `C`; uniformly in `W`, `X` and `E`. -/
theorem compensatedIncrement_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : CompensatedIncrementContract :=
  compensatedIncrement_holds_of_meanSquare hcount hgrad (chtMeanSquare_holds hcount hgrad)

/-- **The compensated-phase lemma** (`CompensatedPhaseContract`), from `ConditionalBlockGUECount`
and `GaussianLpGradient`.

* Law: the path law `pathLaw W r b` of `Ψ_r = N_r(E) + Θ_{z_∂}(X_r)` (`compensatedPhase`).
* Domain: `b ∈ (0, 1/2)`, `W ≥ 1`, `1 ≤ r ≤ TW` (both parities), deterministic
  `E ∈ bulkInterval κ`.
* Norms and statements: `fluctuation`: `‖Ψ_r - EΨ_r‖_{L^p} ≤ C_p √(r+1)` for each fixed `p ≥ 1`;
  `mean`: `|EΨ_r - r W F_sc(E) - W(2ℓ + bh)| ≤ C(r+1)/W`.
* Quantifier order and uniformity: `b, κ, T` (and `p`) first, then the constant; uniformly in
  `W`, `r` and `E`. -/
theorem compensatedPhase_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : CompensatedPhaseContract :=
  compensatedPhase_holds_of_meanSquare hcount hgrad (chtMeanSquare_holds hcount hgrad)
    (chtCoreMeanSquare_holds hcount hgrad)

/-- **The ring compensated phase** (`RingCompensatedPhaseContract`, a display in the proof of the
rank-location theorem), from `ConditionalBlockGUECount` and `GaussianLpGradient`.

* Law: the exact physical ring `model.law` (`p.GaussianRingModel`), with block `k` deleted:
  `Ξ_{n-1} = N_{H_R}(E) + Θ_{z₀}(Σ)` (`ringCompensatedPhase`).
* Domain: `4 ≤ n ≤ TW`, `p.b = b ∈ (0, 1/2)`, every block `k` (in the paper: block zero), deterministic
  `E ∈ bulkInterval κ`.
* Norms and statements: `fluctuation`: `‖Ξ_{n-1} - EΞ_{n-1}‖_{L^q} ≤ C_q √n` for each fixed
  `q ≥ 1`; `mean`: `|EΞ_{n-1} - (n-1) W F_sc(E) - W(ℓ + bh)| ≤ C n/W`.
* Quantifier order and uniformity: `b, κ, T` (and `q`) first, then the constant; uniformly in the
  parameters, the model, `k` and `E`. -/
theorem ringCompensatedPhase_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : RingCompensatedPhaseContract :=
  ringCompensatedPhase_holds_of_meanSquare hcount hgrad (chtMeanSquare_holds hcount hgrad)
    (chtCoreMeanSquare_holds hcount hgrad)

/-- **The rank-location theorem** (`RankLocationContract`, all three fields), from
`ConditionalBlockGUECount` and `GaussianLpGradient`, through `freshCount_holds`,
`ringCompensatedPhase_holds` and `matchedTraces_holds`, assembled by
`BlockBand.RankLocation.rankLocation_of_contracts`.

* Law: the exact physical ring (raw `H`, row variance one, `p.GaussianRingModel`), under every
  `MassLaw` (the physical law, each normalized block-mass law and each pair-mass law
  the pair law: "these eigenvalue-only statements also hold under each normalized block-mass or
  pair-mass law"), with constants the same under every law.
* Domain: `N = nW`, `4 ≤ n ≤ TW` (`Parameters`, `(p.n : ℝ) ≤ T * p.W`), `p.b = b ∈ (0, 1/2)`;
  deterministic `E ∈ bulkInterval κ` (a compact bulk interval `I`); ϑ-bulk ranks
  `ϑ ≤ α/N ≤ 1 - ϑ`, `ϑ ∈ (0, 1/2)` (one-based `IsBulkRank`), increasing eigenvalues
  `physicalOrderedEigenvalue`, classical locations `e_α = classicalLocation p α`.
* Norms: `L^q` (`eLpNorm`, `ENNReal.ofReal q`, `q ≥ 1`) under the mass law.
* Statements and quantifier order: `count_moment` (the physical count): `b, κ, T, q` first, then
  `C_q`; `‖N_H(E) - N F_sc(E)‖_q ≤ C_q √W`. `count_mean` (the physical count mean): `b, κ, T`
  first, then `C`; `|E N_H(E) - N F_sc(E)| ≤ C(n/W + W^{2/5} log 2W)`. `location`
  (the rank-location bound): `b, T, ϑ, q` first, then `C`;
  `‖λ_α - e_α‖_q ≤ C/(n √W)` for every ϑ-bulk rank.
* Uniformity: in the parameters `p` (all `W`, `4 ≤ n ≤ TW`), the Gaussian ring model, the mass
  law, `E ∈ I` and the bulk rank; constants depend on `b, κ, T, q` (resp. `b, T, ϑ, q`) and the
  constants of the two inputs only.
* Order of limits: none; all bounds are non-asymptotic at fixed `W` (with constants chosen
  before `p`). -/
theorem rankLocation_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : RankLocationContract :=
  BlockBand.RankLocation.rankLocation_of_contracts (freshCount_holds hcount hgrad)
    (ringCompensatedPhase_holds hcount hgrad) (matchedTraces_holds hcount hgrad)

end Assembly

end BlockBand.Layers
