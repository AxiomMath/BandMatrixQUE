module

public import BlockBand.Endpoints.Response.ClockEntranceCoreResolvent

/-!
# The propagation step, part 2: the growth step `A_{j+1} = L* A_j L` along one sample

Part of the clock fractional-entrance lemma: during homogeneous propagation `A₊ = L*AL`.
Deterministic block algebra across the `pathAt` reindexing: position `i + 1` of the path of
length `j + 1` is position `i` of the path of length `j`; the new block `A_j = ω.1 j` sits at
position `0`, coupled to the old position `0` by the old near bond `B_j` and to the near port by
the fresh bond `B_{j+1} = ω.2 (j+1)`.

* `cec_fresh ω j` — the fresh one-port layer `(A_j, B_{j+1})` as a `LayerSample W .oneBlockOnePort`.
* `cec_full_mul_candidate` — for any column block `V` on the fresh layer sites, the candidate
  `Ψ(V)` (new block: `V`'s block rows; old positions: `𝒰_j^{near} K w`; far port: `ℝ_{10} K w`)
  satisfies `𝓜_{j+1} Ψ(V) = embed(N V)`, `N` the fresh layer matrix, `K = z - X_j`.
* `cec_step_column` — `N` is invertible when `𝓜_{j+1}` is (kernel argument), and the candidate
  built from the fresh layer resolvent is the near-port column of `G_{j+1}`.
* `cec_nearClock_succ` — **the propagation identity**: on the good events at lengths `j`,
  `j + 1`, if the tag weight of the new block vanishes, `q((j+1)/W) = 0`, then
  `nearClock (j+1) = L* (nearClock j) L` with `L = freshL b E (pathX j) (cec_fresh ω j)`.
* `cec_passiveResolvent_succ` — the new near resolvent `(z - X_{j+1})⁻¹` is the port block of the
  fresh layer resolvent, so `δ₀` at length `j + 1` is a function of `(X_j, fresh layer)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Entries of the length-`(j+1)` path in terms of length `j`
-/

theorem cec_pm_zero_zero (ω : GrowthPath W) (j : ℕ) (x y : Fin W) :
    pathMatrix (pathAt W (j + 1) ω) ((0 : Fin (j + 1)), x) (0, y) = ω.1 j x y := by
  simp [pathMatrix, pathAt]

theorem cec_pm_zero_succ (ω : GrowthPath W) (j : ℕ) (i : Fin j) (x y : Fin W) :
    pathMatrix (pathAt W (j + 1) ω) ((0 : Fin (j + 1)), x) (i.succ, y) =
      star (pfiCoup W j ω.2 (i, y) (0, x)) := by
  by_cases hi : i.val = 0
  · simp [pathMatrix, pathAt, pfiCoup, pathPortCoupling, hi, Fin.ext_iff]
  · simp [pathMatrix, pfiCoup, pathPortCoupling, hi, Fin.ext_iff]

theorem cec_pm_succ_zero (ω : GrowthPath W) (j : ℕ) (i : Fin j) (x y : Fin W) :
    pathMatrix (pathAt W (j + 1) ω) (i.succ, x) ((0 : Fin (j + 1)), y) =
      pfiCoup W j ω.2 (i, x) (0, y) := by
  by_cases hi : i.val = 0
  · simp [pathMatrix, pathAt, pfiCoup, pathPortCoupling, hi, Fin.ext_iff]
  · simp [pathMatrix, pfiCoup, pathPortCoupling, hi, Fin.ext_iff]

theorem cec_pm_succ_succ (ω : GrowthPath W) (j : ℕ) (i k : Fin j) (x y : Fin W) :
    pathMatrix (pathAt W (j + 1) ω) (i.succ, x) (k.succ, y) =
      pathMatrix (pathAt W j ω) (i, x) (k, y) := by
  have e1 : ∀ a : ℕ, j + 1 - 1 - (a + 1) = j - 1 - a := by intro a; omega
  simp only [pathMatrix, pathAt, Fin.succ_inj, Fin.val_succ, e1]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cec_pc_zero (B : ℕ → Matrix (Fin W) (Fin W) ℂ) {j : ℕ} (hj : 1 ≤ j) (p : Fin 2)
    (x y : Fin W) :
    pfiCoup W (j + 1) B ((0 : Fin (j + 1)), x) (p, y) = if p = 0 then B (j + 1) x y else 0 := by
  fin_cases p
  · simp [pfiCoup, pathPortCoupling, pathAt]
  · simp [pfiCoup, pathPortCoupling, pathAt]
    omega

theorem cec_pc_succ (B : ℕ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (i : Fin j) (p : Fin 2)
    (x y : Fin W) :
    pfiCoup W (j + 1) B (i.succ, x) (p, y) = if p = 0 then 0 else pfiCoup W j B (i, x) (p, y) := by
  fin_cases p
  · simp [pfiCoup, pathPortCoupling]
  · simp [pfiCoup, pathPortCoupling, pathAt]

theorem cec_pc_near (B : ℕ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (i : Fin j) (x y : Fin W) :
    pfiCoup W j B (i, x) (0, y) = if i.val = 0 then B j x y else 0 := by
  simp [pfiCoup, pathPortCoupling, pathAt]

/-!
## The candidate column
-/

/-- The fresh one-port layer `(A_j, B_{j+1})` of the growth step `j → j + 1`. -/
def cec_fresh (ω : GrowthPath W) (j : ℕ) : LayerSample W .oneBlockOnePort :=
  (fun _ => ω.1 j, fun _ _ => ω.2 (j + 1))

/-- Near column `U_{·,(0,·)}` of a port-indexed matrix. -/
def cec_nearCol {S : Type*} (U : Matrix S (Fin 2 × Fin W) ℂ) : Matrix S (Fin W) ℂ :=
  Matrix.of fun s y => U s (0, y)

/-- Far column `U_{·,(1,·)}` of a port-indexed matrix. -/
def cec_farCol {S : Type*} (U : Matrix S (Fin 2 × Fin W) ℂ) : Matrix S (Fin W) ℂ :=
  Matrix.of fun s y => U s (1, y)

/-- Block rows `V_{(block,·)}` of a fresh-layer column block. -/
def cec_blockRows {κ : Type*} (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) :
    Matrix (Fin W) κ ℂ :=
  Matrix.of fun x c => V (Sum.inl (0, x)) c

/-- Port rows `V_{(port,·)}` of a fresh-layer column block. -/
def cec_portRows {κ : Type*} (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) :
    Matrix (Fin W) κ ℂ :=
  Matrix.of fun x c => V (Sum.inr (0, x)) c

/-- The candidate column block at length `j + 1`: the new block carries `w = V_{block}`, the old
positions carry `nU K w`, the near port `V_{port}` and the far port `Rf K w`. -/
def cec_candidate {j : ℕ} {κ : Type*} (nU : Matrix (Fin j × Fin W) (Fin W) ℂ)
    (Rf K : Matrix (Fin W) (Fin W) ℂ) (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) :
    Matrix (FullSite W (j + 1)) κ ℂ := fun s c =>
  match s with
  | Sum.inl (i, x) => Fin.cases (motive := fun _ => ℂ) (cec_blockRows V x c)
      (fun i' => (nU * K * cec_blockRows V) (i', x) c) i
  | Sum.inr (p, x) => if p = 0 then cec_portRows V x c else (Rf * K * cec_blockRows V) x c

/-- Embedding of the fresh-layer rows into the length-`(j+1)` sites (new block, near port). -/
def cec_embed {j : ℕ} {κ : Type*} (Y : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) :
    Matrix (FullSite W (j + 1)) κ ℂ := fun s c =>
  match s with
  | Sum.inl (i, x) => Fin.cases (motive := fun _ => ℂ) (Y (Sum.inl (0, x)) c) (fun _ => 0) i
  | Sum.inr (p, x) => if p = 0 then Y (Sum.inr (0, x)) c else 0

theorem cec_full_inl (b E : ℝ) (ω : GrowthPath W) {j : ℕ} {κ : Type*}
    (Ψ : Matrix (FullSite W (j + 1)) κ ℂ) (i : Fin (j + 1)) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * Ψ) (Sum.inl (i, x)) c =
      (∑ t : Fin (j + 1) × Fin W, pfiInt E W (j + 1) ω (i, x) t * Ψ (Sum.inl t) c) +
        ∑ t : Fin 2 × Fin W, pfiCoup W (j + 1) ω.2 (i, x) t * Ψ (Sum.inr t) c := by
  rw [fullPathMatrix_eq, mul_apply, Fintype.sum_sum_type]
  rfl

theorem cec_full_inr (b E : ℝ) (ω : GrowthPath W) {j : ℕ} {κ : Type*}
    (Ψ : Matrix (FullSite W (j + 1)) κ ℂ) (p : Fin 2) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * Ψ) (Sum.inr (p, x)) c =
      (∑ t : Fin (j + 1) × Fin W, star (pfiCoup W (j + 1) ω.2 t (p, x)) * Ψ (Sum.inl t) c) +
        boundaryZ b E * Ψ (Sum.inr (p, x)) c := by
  rw [fullPathMatrix_eq, mul_apply, Fintype.sum_sum_type]
  simp [fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq]

theorem cec_row_new (b E : ℝ) (ω : GrowthPath W) {j : ℕ} (hj : 1 ≤ j) {κ : Type*}
    (nU : Matrix (Fin j × Fin W) (Fin W) ℂ) (Rf K : Matrix (Fin W) (Fin W) ℂ)
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * cec_candidate nU Rf K V) (Sum.inl (0, x)) c =
      (((ω.1 j - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * cec_blockRows V +
        (cec_nearCol (pfiCoup W j ω.2))ᴴ * (nU * K * cec_blockRows V) +
          ω.2 (j + 1) * cec_portRows V : Matrix (Fin W) κ ℂ) x c) := by
  rw [cec_full_inl]
  have h0 : ∀ i : Fin j, ((0 : Fin (j + 1)) = i.succ) = False :=
    fun i => eq_false (Fin.succ_ne_zero i).symm
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, pfiInt,
    Matrix.sub_apply, Matrix.smul_apply, cec_pm_zero_zero, cec_pm_zero_succ, cec_pc_zero _ hj,
    cec_candidate, Fin.cases_zero, Fin.cases_succ, Matrix.add_apply, mul_apply,
    conjTranspose_apply, cec_nearCol, of_apply]
  simp [one_apply, h0, Prod.ext_iff, sub_mul, Finset.sum_sub_distrib]

theorem cec_row_old (b E : ℝ) (ω : GrowthPath W) {j : ℕ} {κ : Type*}
    (nU : Matrix (Fin j × Fin W) (Fin W) ℂ) (Rf K : Matrix (Fin W) (Fin W) ℂ)
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (i : Fin j) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * cec_candidate nU Rf K V) (Sum.inl (i.succ, x)) c =
      ((cec_nearCol (pfiCoup W j ω.2) * cec_blockRows V + pfiInt E W j ω * (nU * K * cec_blockRows V) +
        cec_farCol (pfiCoup W j ω.2) * (Rf * K * cec_blockRows V) :
          Matrix (Fin j × Fin W) κ ℂ) (i, x) c) := by
  rw [cec_full_inl]
  have h0 : ∀ i : Fin j, (i.succ = (0 : Fin (j + 1))) = False :=
    fun i => eq_false (Fin.succ_ne_zero i)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, pfiInt,
    Matrix.sub_apply, Matrix.smul_apply, cec_pm_succ_zero, cec_pm_succ_succ, cec_pc_succ,
    cec_candidate, Fin.cases_zero, Fin.cases_succ, Matrix.add_apply, mul_apply,
    cec_nearCol, cec_farCol, of_apply]
  simp [one_apply, h0, Prod.ext_iff, sub_mul, Finset.sum_sub_distrib]

theorem cec_row_near (b E : ℝ) (ω : GrowthPath W) {j : ℕ} (hj : 1 ≤ j) {κ : Type*}
    (nU : Matrix (Fin j × Fin W) (Fin W) ℂ) (Rf K : Matrix (Fin W) (Fin W) ℂ)
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * cec_candidate nU Rf K V) (Sum.inr (0, x)) c =
      (((ω.2 (j + 1))ᴴ * cec_blockRows V + boundaryZ b E • cec_portRows V :
          Matrix (Fin W) κ ℂ) x c) := by
  rw [cec_full_inr]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, cec_pc_zero _ hj, cec_pc_succ,
    cec_candidate, Fin.cases_zero, Fin.cases_succ, Matrix.add_apply, mul_apply,
    Matrix.smul_apply, conjTranspose_apply]
  simp

theorem cec_row_far (b E : ℝ) (ω : GrowthPath W) {j : ℕ} (hj : 1 ≤ j) {κ : Type*}
    (nU : Matrix (Fin j × Fin W) (Fin W) ℂ) (Rf K : Matrix (Fin W) (Fin W) ℂ)
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (x : Fin W) (c : κ) :
    (fullPathMatrix b E W (j + 1) ω * cec_candidate nU Rf K V) (Sum.inr (1, x)) c =
      (((cec_farCol (pfiCoup W j ω.2))ᴴ * (nU * K * cec_blockRows V) +
        boundaryZ b E • (Rf * K * cec_blockRows V) : Matrix (Fin W) κ ℂ) x c) := by
  rw [cec_full_inr]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, cec_pc_zero _ hj, cec_pc_succ,
    cec_candidate, Fin.cases_zero, Fin.cases_succ, Matrix.add_apply, mul_apply,
    Matrix.smul_apply, conjTranspose_apply, cec_farCol, of_apply]
  simp

/-- The fresh one-port layer matrix `N = [[A - E - X, B],[B*, z]]` (so `freshLayer = N⁻¹`). -/
def cec_layerMat (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ν : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerMatrix .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ν

theorem cec_freshLayer_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) : freshLayer b E X ν = (cec_layerMat b E X ν)⁻¹ := rfl

theorem cec_layer_row_block (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) {κ : Type*}
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (x : Fin W) (c : κ) :
    (cec_layerMat b E X ν * V) (Sum.inl (0, x)) c =
      (((ν.1 0 - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * cec_blockRows V +
        ν.2 0 0 * cec_portRows V : Matrix (Fin W) κ ℂ) x c) := by
  simp only [cec_layerMat, layerMatrix, mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident,
    cec_blockRows, cec_portRows, of_apply]
  simp [one_apply, sub_mul, Finset.sum_sub_distrib]

theorem cec_layer_row_port (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) {κ : Type*}
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) (x : Fin W) (c : κ) :
    (cec_layerMat b E X ν * V) (Sum.inr (0, x)) c =
      (((ν.2 0 0)ᴴ * cec_blockRows V + boundaryZ b E • cec_portRows V :
        Matrix (Fin W) κ ℂ) x c) := by
  simp only [cec_layerMat, layerMatrix, mul_apply, Fintype.sum_sum_type, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.add_apply,
    Matrix.smul_apply, bondMatrix, LayerShape.incident, conjTranspose_apply,
    cec_blockRows, cec_portRows, of_apply]
  simp [one_apply]

/-- **The candidate equation.** If the length-`j` boundary columns `nU = 𝒰_j^{near}`,
`Rn = ℝ_{00}`, `Rf = ℝ_{10}` solve the length-`j` equations and `Rn K = I` with `K = z - X_j`,
then for every fresh-layer column block `V`: `𝓜_{j+1} Ψ(V) = embed(N V)`. -/
theorem cec_full_mul_candidate (b E : ℝ) (ω : GrowthPath W) {j : ℕ} (hj : 1 ≤ j) {κ : Type*}
    {nU : Matrix (Fin j × Fin W) (Fin W) ℂ} {Rn Rf K : Matrix (Fin W) (Fin W) ℂ}
    (h1 : pfiInt E W j ω * nU + cec_nearCol (pfiCoup W j ω.2) * Rn +
      cec_farCol (pfiCoup W j ω.2) * Rf = 0)
    (h2 : (cec_nearCol (pfiCoup W j ω.2))ᴴ * nU + boundaryZ b E • Rn = 1)
    (h3 : (cec_farCol (pfiCoup W j ω.2))ᴴ * nU + boundaryZ b E • Rf = 0)
    (hRK : Rn * K = 1) (hK : K = boundaryZ b E • 1 - pathX b E W j ω)
    (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) :
    fullPathMatrix b E W (j + 1) ω * cec_candidate nU Rf K V =
      cec_embed (cec_layerMat b E (pathX b E W j ω) (cec_fresh ω j) * V) := by
  set Cn := cec_nearCol (pfiCoup W j ω.2)
  set Cf := cec_farCol (pfiCoup W j ω.2)
  set w := cec_blockRows V
  set X := pathX b E W j ω
  have I1 : Cnᴴ * (nU * K * w) = -(X * w) := by
    have e : Cnᴴ * nU = 1 - boundaryZ b E • Rn := eq_sub_of_add_eq h2
    calc Cnᴴ * (nU * K * w) = (Cnᴴ * nU) * K * w := by simp only [Matrix.mul_assoc]
      _ = K * w - boundaryZ b E • ((Rn * K) * w) := by
        rw [e, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
      _ = -(X * w) := by
        rw [hRK, Matrix.one_mul, hK, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]; abel
  have I2 : Cn * w + pfiInt E W j ω * (nU * K * w) + Cf * (Rf * K * w) = 0 := by
    have e : pfiInt E W j ω * nU + Cf * Rf = -(Cn * Rn) := by
      rw [eq_neg_iff_add_eq_zero, ← h1]; abel
    calc Cn * w + pfiInt E W j ω * (nU * K * w) + Cf * (Rf * K * w) =
        Cn * w + (pfiInt E W j ω * nU + Cf * Rf) * K * w := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]; abel
      _ = 0 := by
        rw [e, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc Cn, hRK, Matrix.mul_one]; abel
  have I3 : Cfᴴ * (nU * K * w) + boundaryZ b E • (Rf * K * w) = 0 := by
    calc _ = (Cfᴴ * nU + boundaryZ b E • Rf) * K * w := by
          simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = 0 := by rw [h3, Matrix.zero_mul, Matrix.zero_mul]
  ext s c
  rcases s with ⟨i, x⟩ | ⟨p, x⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · rw [cec_row_new b E ω hj, I1]
      simp only [cec_embed, Fin.cases_zero]
      rw [cec_layer_row_block]
      have e : (ω.1 j - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * w + -(X * w) +
          ω.2 (j + 1) * cec_portRows V =
          ((cec_fresh ω j).1 0 - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * w +
            (cec_fresh ω j).2 0 0 * cec_portRows V := by
        simp only [cec_fresh, Matrix.sub_mul]; abel
      exact congrFun (congrFun e x) c
    · rw [cec_row_old, I2]
      simp [cec_embed]
  · fin_cases p
    · simp only [Fin.zero_eta]
      rw [cec_row_near b E ω hj]
      simp only [cec_embed]
      rw [cec_layer_row_port]
      rfl
    · simp only [Fin.mk_one]
      rw [cec_row_far b E ω hj, I3]
      simp [cec_embed]

/-!
## Specialization to the path
-/

/-- The near-column equations of length `j` (from `𝓜_j G_j = I`). -/
theorem cec_near_eqs {b E : ℝ} {j : ℕ} {ω : GrowthPath W}
    (hM : IsUnit (fullPathMatrix b E W j ω).det) :
    pfiInt E W j ω * cec_nearCol (boundaryToInterior b E W j ω) +
        cec_nearCol (pfiCoup W j ω.2) * portBlock (boundaryResolvent b E W j ω) 0 0 +
        cec_farCol (pfiCoup W j ω.2) * portBlock (boundaryResolvent b E W j ω) 1 0 = 0 ∧
      (cec_nearCol (pfiCoup W j ω.2))ᴴ * cec_nearCol (boundaryToInterior b E W j ω) +
        boundaryZ b E • portBlock (boundaryResolvent b E W j ω) 0 0 = 1 ∧
      (cec_farCol (pfiCoup W j ω.2))ᴴ * cec_nearCol (boundaryToInterior b E W j ω) +
        boundaryZ b E • portBlock (boundaryResolvent b E W j ω) 1 0 = 0 := by
  obtain ⟨e1, e2⟩ := cec_column_eqs hM
  refine ⟨?_, ?_, ?_⟩
  · ext s y
    have := congrFun (congrFun e1 s) (0, y)
    simpa [mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, cec_nearCol, cec_farCol,
      portBlock, add_assoc] using this
  · ext x y
    have := congrFun (congrFun e2 (0, x)) (0, y)
    simpa [mul_apply, Fintype.sum_prod_type, cec_nearCol, portBlock, one_apply] using this
  · ext x y
    have := congrFun (congrFun e2 (1, x)) (0, y)
    simpa [mul_apply, Fintype.sum_prod_type, cec_farCol, cec_nearCol, portBlock, one_apply] using this

/-- `Rn K = I` on the good event of length `j`. -/
theorem cec_Rn_mul_K {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ}
    {ω : GrowthPath W} (hg : cec_good E W j ω) :
    portBlock (boundaryResolvent b E W j ω) 0 0 *
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathX b E W j ω) = 1 := by
  obtain ⟨h1, h2⟩ := cec_nearResolvent hb hE1 hE2 hg
  rw [h1]
  exact nonsing_inv_mul _ h2

/-- The fresh-layer port column `𝒢_{·,port}`. -/
def cec_portCol (V : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ :=
  Matrix.of fun s y => V s (Sum.inr (0, y))

theorem cec_embed_portCol_one {j : ℕ} :
    cec_embed (j := j) (cec_portCol (1 : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)) =
      Matrix.of fun s y => (1 : Matrix (FullSite W (j + 1)) (FullSite W (j + 1)) ℂ) s
        (Sum.inr (0, y)) := by
  ext s y
  rcases s with ⟨i, x⟩ | ⟨p, x⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> simp [cec_embed, cec_portCol, one_apply]
  · fin_cases p <;> simp [cec_embed, cec_portCol, one_apply]

/-- **The growth step along one sample.** On the good event of length `j`, for invertible full
matrices at lengths `j` and `j + 1`: the fresh layer matrix is invertible, and the candidate
built from the fresh layer resolvent's port column is the near-port column of `G_{j+1}`. -/
theorem cec_step_column {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ}
    (hj : 1 ≤ j) {ω : GrowthPath W} (hg : cec_good E W j ω)
    (hM : IsUnit (fullPathMatrix b E W j ω).det)
    (hM' : IsUnit (fullPathMatrix b E W (j + 1) ω).det) :
    IsUnit (cec_layerMat b E (pathX b E W j ω) (cec_fresh ω j)).det ∧
      ∀ s y, cec_candidate (cec_nearCol (boundaryToInterior b E W j ω))
          (portBlock (boundaryResolvent b E W j ω) 1 0)
          (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathX b E W j ω)
          (cec_portCol (freshLayer b E (pathX b E W j ω) (cec_fresh ω j))) s y =
        fullInverse b E W (j + 1) ω s (Sum.inr (0, y)) := by
  obtain ⟨h1, h2, h3⟩ := cec_near_eqs hM
  have hRK := cec_Rn_mul_K hb hE1 hE2 hg
  have key := fun {κ : Type} (V : Matrix (LayerSite W .oneBlockOnePort) κ ℂ) =>
    cec_full_mul_candidate b E ω hj h1 h2 h3 hRK rfl V
  have hGM : fullInverse b E W (j + 1) ω * fullPathMatrix b E W (j + 1) ω = 1 :=
    nonsing_inv_mul _ hM'
  set N := cec_layerMat b E (pathX b E W j ω) (cec_fresh ω j)
  have hN : IsUnit N.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have e := key (Matrix.of fun s (_ : Unit) => v s)
    have hNV : N * (Matrix.of fun s (_ : Unit) => v s) = 0 := by
      ext s u; have := congrFun hv s; simpa [mulVec, dotProduct, mul_apply] using this
    rw [hNV] at e
    have hz : cec_embed (j := j) (0 : Matrix (LayerSite W .oneBlockOnePort) Unit ℂ) = 0 := by
      ext s u
      rcases s with ⟨i, x⟩ | ⟨p, x⟩
      · refine Fin.cases ?_ (fun i => ?_) i <;> simp [cec_embed]
      · simp [cec_embed]
    rw [hz] at e
    have e' := congrArg (fun A => fullInverse b E W (j + 1) ω * A) e
    simp only [← Matrix.mul_assoc, hGM, Matrix.one_mul, Matrix.mul_zero] at e'
    apply hv0
    funext t
    rcases t with ⟨a, x⟩ | ⟨a, x⟩ <;> obtain rfl : a = 0 := Subsingleton.elim _ _
    · have := congrFun (congrFun e' (Sum.inl (0, x))) ()
      simpa [cec_candidate, cec_blockRows] using this
    · have := congrFun (congrFun e' (Sum.inr (0, x))) ()
      simpa [cec_candidate, cec_portRows] using this
  refine ⟨hN, ?_⟩
  have e := key (cec_portCol (freshLayer b E (pathX b E W j ω) (cec_fresh ω j)))
  have hNG : N * cec_portCol (freshLayer b E (pathX b E W j ω) (cec_fresh ω j)) =
      cec_portCol (1 : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) := by
    rw [cec_freshLayer_eq]
    ext s y
    have := congrFun (congrFun (mul_nonsing_inv N hN) s) (Sum.inr (0, y))
    simpa [cec_portCol, mul_apply] using this
  rw [hNG, cec_embed_portCol_one] at e
  have e' := congrArg (fun A => fullInverse b E W (j + 1) ω * A) e
  simp only [← Matrix.mul_assoc, hGM, Matrix.one_mul] at e'
  intro s y
  rw [e']
  simp [mul_apply, one_apply]

/-!
## The clock and the new near resolvent
-/

/-- The port block `𝒢_{port,port}` of the fresh layer resolvent. -/
def cec_freshPortBlock (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => freshLayer b E X ν (Sum.inr (0, x)) (Sum.inr (0, y))

theorem cec_sandwich_diag {S κ : Type*} [Fintype S] [DecidableEq S]
    (A B : Matrix S κ ℂ) (d : S → ℂ) (x y : κ) :
    (Aᴴ * diagonal d * B) x y = ∑ s, star (A s x) * d s * B s y := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply]

theorem cec_portBlock_tagResponse (b E : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    portBlock (tagResponse b E W n k ω) 0 0 =
      (cec_nearCol (boundaryToInterior b E W n ω))ᴴ * tagProjection W n k *
        cec_nearCol (boundaryToInterior b E W n ω) := by
  ext x y
  simp [portBlock, tagResponse, mul_apply, cec_nearCol]

theorem cec_nearClock_eq (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    nearClock b E W n q ω = ∑ k ∈ Finset.range n,
      ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) •
        ((cec_nearCol (boundaryToInterior b E W n ω))ᴴ * tagProjection W n k *
          cec_nearCol (boundaryToInterior b E W n ω)) := by
  simp only [← cec_portBlock_tagResponse, nearClock, intervalSource]
  ext x y
  simp [portBlock, Matrix.sum_apply]

/-- One tag term across the growth step. -/
theorem cec_tag_succ {j k : ℕ} (hk : k < j) (nU : Matrix (Fin j × Fin W) (Fin W) ℂ)
    (nU' : Matrix (Fin (j + 1) × Fin W) (Fin W) ℂ) (L : Matrix (Fin W) (Fin W) ℂ)
    (h : ∀ i x y, nU' (i.succ, x) y = (nU * L) (i, x) y) :
    nU'ᴴ * tagProjection W (j + 1) k * nU' = Lᴴ * (nUᴴ * tagProjection W j k * nU) * L := by
  have e : Lᴴ * (nUᴴ * tagProjection W j k * nU) * L =
      (nU * L)ᴴ * tagProjection W j k * (nU * L) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e]
  ext x y
  simp only [tagProjection, cec_sandwich_diag, Fintype.sum_prod_type, Fin.sum_univ_succ, h]
  have h0 : ∀ x' : Fin W, (if k < j + 1 ∧ ((0 : Fin (j + 1)), x').1.val = j + 1 - 1 - k
      then (1 : ℂ) else 0) = 0 := by
    intro x'
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    simp only [Fin.val_zero, not_and]
    omega
  have hs : ∀ (i : Fin j) (x' : Fin W), (if k < j + 1 ∧ (i.succ, x').1.val = j + 1 - 1 - k
      then (1 : ℂ) else 0) = if k < j ∧ (i, x').1.val = j - 1 - k then 1 else 0 := by
    intro i x'
    simp only [Fin.val_succ]
    congr 1
    apply propext; omega
  simp only [h0, hs, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]

/-- **Propagation identity `A_{j+1} = L* A_j L`.** Deterministic, on the good event of length `j`
with invertible full matrices at lengths `j` and `j + 1`, for a source whose tag weight on the new
block vanishes. `L` is `freshL b E X_j` of the fresh one-port layer `(A_j, B_{j+1})`. -/
theorem cec_nearClock_succ {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ}
    (hj : 1 ≤ j) {ω : GrowthPath W} (hg : cec_good E W j ω)
    (hM : IsUnit (fullPathMatrix b E W j ω).det)
    (hM' : IsUnit (fullPathMatrix b E W (j + 1) ω).det) {q : ℝ → ℝ}
    (hq : q (((j + 1 : ℕ) : ℝ) / W) = 0) :
    nearClock b E W (j + 1) q ω =
      (freshL b E (pathX b E W j ω) (cec_fresh ω j))ᴴ * nearClock b E W j q ω *
        freshL b E (pathX b E W j ω) (cec_fresh ω j) := by
  obtain ⟨-, hcol⟩ := cec_step_column hb hE1 hE2 hj hg hM hM'
  set L := freshL b E (pathX b E W j ω) (cec_fresh ω j)
  have hrel : ∀ (i : Fin j) (x y : Fin W),
      cec_nearCol (boundaryToInterior b E W (j + 1) ω) (i.succ, x) y =
        (cec_nearCol (boundaryToInterior b E W j ω) * L) (i, x) y := by
    intro i x y
    have := hcol (Sum.inl (i.succ, x)) y
    simp only [cec_candidate, Fin.cases_succ] at this
    simp only [cec_nearCol, of_apply, boundaryToInterior, toBlocks₁₂]
    rw [← this, Matrix.mul_assoc]
    rfl
  rw [cec_nearClock_eq, cec_nearClock_eq, Finset.sum_range_succ, hq, zero_div,
    Complex.ofReal_zero, zero_smul, add_zero, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [cec_tag_succ (Finset.mem_range.1 hk) _ _ L hrel, Matrix.mul_smul, Matrix.smul_mul]

/-- **The new near resolvent** `(z - X_{j+1})⁻¹` is the port block of the fresh layer resolvent
(on the good events of lengths `j` and `j + 1`); hence `δ₀` at length `j + 1` is a function of
`(X_j, fresh layer)`. -/
theorem cec_passiveResolvent_succ {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ}
    (hj : 1 ≤ j) {ω : GrowthPath W} (hg : cec_good E W j ω) (hg' : cec_good E W (j + 1) ω)
    (hM : IsUnit (fullPathMatrix b E W j ω).det)
    (hM' : IsUnit (fullPathMatrix b E W (j + 1) ω).det) :
    passiveResolvent b E (pathX b E W (j + 1) ω) =
      cec_freshPortBlock b E (pathX b E W j ω) (cec_fresh ω j) := by
  obtain ⟨-, hcol⟩ := cec_step_column hb hE1 hE2 hj hg hM hM'
  rw [← (cec_nearResolvent hb hE1 hE2 hg').1]
  ext x y
  have := hcol (Sum.inr (0, x)) y
  simp only [cec_candidate] at this
  simp only [portBlock, of_apply, boundaryResolvent, toBlocks₂₂, cec_freshPortBlock]
  rw [← this]
  rfl

end BlockBand.Endpoints
