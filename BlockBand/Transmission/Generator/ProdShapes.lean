module

public import BlockBand.Transmission.Generator.ProdPoint

/-!
# The four tested shapes of the product martingale problem

Expanding `M_k M_l - ∫B` with `M_k = Y_k - ∫A_k`, `Y_k = P_k(t) - P_k(s)`, the tested terms are
continuous functions of power sums at finitely many times:
* `hYY` at `ptYY`: `Y_k Y_l`;
* `hYA D l` at `ptYA k l s t u`: `Y_k·A_l(P(u))`;
* `hAA D l k` at `ptAA l k v u`: `A_l(P(v))·A_k(P(u))`;
* `hBr D k l` at `ptVec (k+l+1) u`: `B_{kl}(P(u))`.
Each has `|h(x)| ≤ c(1 + Σ|x_i|)⁴` (the hypothesis of `poly_point`), and is identified with the
path quantity at width `W` (`*_fin`) and on the limit (`*_lim`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

theorem abs_le_sum_abs {q : ℕ} (x : Fin q → ℝ) (i : Fin q) : |x i| ≤ ∑ j, |x j| :=
  Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem abs_extendVec_le (n : ℕ) (y : Fin n → ℝ) (j : ℕ) : |extendVec n y j| ≤ ∑ i, |y i| := by
  unfold extendVec
  split_ifs with h
  · exact abs_le_sum_abs y _
  · rw [abs_zero]; positivity

theorem sum_castAdd_le {a c : ℕ} (x : Fin (a + c) → ℝ) :
    ∑ i, |x (Fin.castAdd c i)| ≤ ∑ i, |x i| := by
  rw [Fin.sum_univ_add]
  have : 0 ≤ ∑ i : Fin c, |x (Fin.natAdd a i)| := by positivity
  linarith

theorem sum_natAdd_le {a c : ℕ} (x : Fin (a + c) → ℝ) :
    ∑ i, |x (Fin.natAdd a i)| ≤ ∑ i, |x i| := by
  rw [Fin.sum_univ_add]
  have : 0 ≤ ∑ i : Fin a, |x (Fin.castAdd c i)| := by positivity
  linarith

theorem pow_le_one_add_pow4 {Z : ℝ} (hZ : 0 ≤ Z) {j : ℕ} (hj : j ≤ 4) : Z ^ j ≤ (1 + Z) ^ 4 :=
  (pow_le_pow_left₀ hZ (by linarith) j).trans (pow_le_pow_right₀ (by linarith) hj)

theorem extendVec_finVec (b : ℝ) (e : ℕ → ℝ) (W n : ℕ) (u : ℝ) (ω : GrowthPath W) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ n) :
    extendVec n (finVec b e W (ptVec n u) ω) j = pathPowers b (e W) W ⌊(W : ℝ) * u⌋₊ ω j := by
  simp only [extendVec, h1, h2, and_self, ↓reduceDIte, finVec, ptVec, pathPowers]
  congr; omega

theorem extendVec_limVec {Ω : Type*} (Pk : ℕ → ℝ → Ω → ℝ) (n : ℕ) (u : ℝ) (ω : Ω) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ n) : extendVec n (limVec Pk (ptVec n u) ω) j = Pk j u ω := by
  simp only [extendVec, h1, h2, and_self, ↓reduceDIte, limVec, ptVec]
  congr; omega

/-!
### `Y_k Y_l`
-/

def hYY (x : Fin 4 → ℝ) : ℝ := (x 1 - x 0) * (x 3 - x 2)

def ptYY (k l : ℕ) (s t : ℝ) : Fin 4 → ℕ × ℝ := ![(k, s), (k, t), (l, s), (l, t)]

theorem continuous_hYY : Continuous hYY := by unfold hYY; fun_prop

theorem hYY_le (x : Fin 4 → ℝ) : |hYY x| ≤ 4 * (1 + ∑ i, |x i|) ^ 4 := by
  have hZ : 0 ≤ ∑ i, |x i| := by positivity
  have h1 : |x 1 - x 0| ≤ 2 * ∑ i, |x i| :=
    (abs_sub _ _).trans (by linarith [abs_le_sum_abs x 1, abs_le_sum_abs x 0])
  have h2 : |x 3 - x 2| ≤ 2 * ∑ i, |x i| :=
    (abs_sub _ _).trans (by linarith [abs_le_sum_abs x 3, abs_le_sum_abs x 2])
  unfold hYY
  rw [abs_mul]
  calc |x 1 - x 0| * |x 3 - x 2| ≤ (2 * ∑ i, |x i|) * (2 * ∑ i, |x i|) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * (∑ i, |x i|) ^ 2 := by ring
    _ ≤ 4 * (1 + ∑ i, |x i|) ^ 4 := by gcongr; exact pow_le_one_add_pow4 hZ (by norm_num)

theorem hYY_fin (b : ℝ) (e : ℕ → ℝ) (W k l : ℕ) (s t : ℝ) (ω : GrowthPath W) :
    hYY (finVec b e W (ptYY k l s t) ω) =
      (pathPower b (e W) W k ⌊(W : ℝ) * t⌋₊ ω - pathPower b (e W) W k ⌊(W : ℝ) * s⌋₊ ω) *
        (pathPower b (e W) W l ⌊(W : ℝ) * t⌋₊ ω - pathPower b (e W) W l ⌊(W : ℝ) * s⌋₊ ω) := by
  simp [hYY, ptYY, finVec]

theorem hYY_lim {Ω : Type*} (Pk : ℕ → ℝ → Ω → ℝ) (k l : ℕ) (s t : ℝ) (ω : Ω) :
    hYY (limVec Pk (ptYY k l s t) ω) = (Pk k t ω - Pk k s ω) * (Pk l t ω - Pk l s ω) := by
  simp [hYY, ptYY, limVec]

/-!
### `Y_k·A_l(P(u))`
-/

def hYA (D : ℝ) (l : ℕ) (x : Fin (2 + l) → ℝ) : ℝ :=
  (x (Fin.castAdd l 1) - x (Fin.castAdd l 0)) *
    transmissionDrift D l (extendVec l fun i => x (Fin.natAdd 2 i))

def ptYA (k l : ℕ) (s t u : ℝ) : Fin (2 + l) → ℕ × ℝ := Fin.append ![(k, s), (k, t)] (ptVec l u)

theorem continuous_hYA (D : ℝ) (l : ℕ) : Continuous (hYA D l) := by
  have h : Continuous fun x : Fin (2 + l) → ℝ => extendVec l fun i => x (Fin.natAdd 2 i) :=
    (continuous_extendVec l).comp (continuous_pi fun i => continuous_apply _)
  exact (by fun_prop : Continuous fun x : Fin (2 + l) → ℝ =>
    x (Fin.castAdd l 1) - x (Fin.castAdd l 0)).mul (continuous_transmissionDrift D l
      (v := fun x : Fin (2 + l) → ℝ => extendVec l fun i => x (Fin.natAdd 2 i))
      fun j => (continuous_apply j).comp h)

theorem hYA_le {D : ℝ} (hD : 0 ≤ D) (l : ℕ) (x : Fin (2 + l) → ℝ) :
    |hYA D l x| ≤ 2 * D * l ^ 2 * (1 + ∑ i, |x i|) ^ 4 := by
  set Z := ∑ i, |x i|
  have hZ : 0 ≤ Z := by positivity
  have a1 := abs_le_sum_abs x (Fin.castAdd l 1)
  have a0 := abs_le_sum_abs x (Fin.castAdd l 0)
  have h1 : |x (Fin.castAdd l 1) - x (Fin.castAdd l 0)| ≤ 2 * Z :=
    (abs_sub _ _).trans (by linarith)
  have h2 : |transmissionDrift D l (extendVec l fun i => x (Fin.natAdd 2 i))| ≤ D * l ^ 2 * Z ^ 2 :=
    abs_transmissionDrift_le hD l fun j _ _ =>
      (abs_extendVec_le l _ j).trans (sum_natAdd_le x)
  unfold hYA
  rw [abs_mul]
  calc _ ≤ (2 * Z) * (D * l ^ 2 * Z ^ 2) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 * D * l ^ 2 * Z ^ 3 := by ring
    _ ≤ 2 * D * l ^ 2 * (1 + Z) ^ 4 := by gcongr; exact pow_le_one_add_pow4 hZ (by norm_num)

theorem hYA_fin (D b : ℝ) (e : ℕ → ℝ) (W k l : ℕ) (s t u : ℝ) (ω : GrowthPath W) :
    hYA D l (finVec b e W (ptYA k l s t u) ω) =
      (pathPower b (e W) W k ⌊(W : ℝ) * t⌋₊ ω - pathPower b (e W) W k ⌊(W : ℝ) * s⌋₊ ω) *
        transmissionDrift D l (pathPowers b (e W) W ⌊(W : ℝ) * u⌋₊ ω) := by
  obtain ⟨h1, h2⟩ := finVec_append b e W ![(k, s), (k, t)] (ptVec l u) ω
  simp only [hYA, ptYA]
  rw [h2, drift_extend_fin]
  simp [finVec, Fin.append_left]

theorem hYA_lim {Ω : Type*} (D : ℝ) (Pk : ℕ → ℝ → Ω → ℝ) (k l : ℕ) (s t u : ℝ) (ω : Ω) :
    hYA D l (limVec Pk (ptYA k l s t u) ω) =
      (Pk k t ω - Pk k s ω) * transmissionDrift D l (fun i => Pk i u ω) := by
  obtain ⟨h1, h2⟩ := limVec_append Pk ![(k, s), (k, t)] (ptVec l u) ω
  simp only [hYA, ptYA]
  rw [h2, (drift_extend_lim D l Pk u ω).1]
  simp [limVec, Fin.append_left]

/-!
### `A_l(P(v))·A_k(P(u))`
-/

def hAA (D : ℝ) (l k : ℕ) (x : Fin (l + k) → ℝ) : ℝ :=
  transmissionDrift D l (extendVec l fun i => x (Fin.castAdd k i)) *
    transmissionDrift D k (extendVec k fun i => x (Fin.natAdd l i))

def ptAA (l k : ℕ) (v u : ℝ) : Fin (l + k) → ℕ × ℝ := Fin.append (ptVec l v) (ptVec k u)

theorem continuous_hAA (D : ℝ) (l k : ℕ) : Continuous (hAA D l k) := by
  unfold hAA
  exact ((continuous_transmissionDrift D l (v := fun x : ℕ → ℝ => x) fun j =>
      continuous_apply j).comp ((continuous_extendVec l).comp
        (continuous_pi fun i => continuous_apply _))).mul
    ((continuous_transmissionDrift D k (v := fun x : ℕ → ℝ => x) fun j =>
      continuous_apply j).comp ((continuous_extendVec k).comp
        (continuous_pi fun i => continuous_apply _)))

theorem hAA_le {D : ℝ} (hD : 0 ≤ D) (l k : ℕ) (x : Fin (l + k) → ℝ) :
    |hAA D l k x| ≤ D * l ^ 2 * (D * k ^ 2) * (1 + ∑ i, |x i|) ^ 4 := by
  set Z := ∑ i, |x i|
  have hZ : 0 ≤ Z := by positivity
  have h1 : |transmissionDrift D l (extendVec l fun i => x (Fin.castAdd k i))| ≤ D * l ^ 2 * Z ^ 2 :=
    abs_transmissionDrift_le hD l fun j _ _ => (abs_extendVec_le l _ j).trans (sum_castAdd_le x)
  have h2 : |transmissionDrift D k (extendVec k fun i => x (Fin.natAdd l i))| ≤ D * k ^ 2 * Z ^ 2 :=
    abs_transmissionDrift_le hD k fun j _ _ => (abs_extendVec_le k _ j).trans (sum_natAdd_le x)
  unfold hAA
  rw [abs_mul]
  calc _ ≤ (D * l ^ 2 * Z ^ 2) * (D * k ^ 2 * Z ^ 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = D * l ^ 2 * (D * k ^ 2) * Z ^ 4 := by ring
    _ ≤ D * l ^ 2 * (D * k ^ 2) * (1 + Z) ^ 4 := by
        gcongr; linarith

theorem hAA_fin (D b : ℝ) (e : ℕ → ℝ) (W l k : ℕ) (v u : ℝ) (ω : GrowthPath W) :
    hAA D l k (finVec b e W (ptAA l k v u) ω) =
      transmissionDrift D l (pathPowers b (e W) W ⌊(W : ℝ) * v⌋₊ ω) *
        transmissionDrift D k (pathPowers b (e W) W ⌊(W : ℝ) * u⌋₊ ω) := by
  obtain ⟨h1, h2⟩ := finVec_append b e W (ptVec l v) (ptVec k u) ω
  simp only [hAA, ptAA]
  rw [h1, h2, drift_extend_fin, drift_extend_fin]

theorem hAA_lim {Ω : Type*} (D : ℝ) (Pk : ℕ → ℝ → Ω → ℝ) (l k : ℕ) (v u : ℝ) (ω : Ω) :
    hAA D l k (limVec Pk (ptAA l k v u) ω) =
      transmissionDrift D l (fun i => Pk i v ω) * transmissionDrift D k (fun i => Pk i u ω) := by
  obtain ⟨h1, h2⟩ := limVec_append Pk (ptVec l v) (ptVec k u) ω
  simp only [hAA, ptAA]
  rw [h1, h2, (drift_extend_lim D l Pk v ω).1, (drift_extend_lim D k Pk u ω).1]

/-!
### `B_{kl}(P(u))`
-/

def hBr (D : ℝ) (k l : ℕ) (x : Fin (k + l + 1) → ℝ) : ℝ :=
  transmissionBracket D k l (extendVec (k + l + 1) x)

theorem continuous_hBr (D : ℝ) (k l : ℕ) : Continuous (hBr D k l) :=
  (continuous_transmissionBracket D k l (v := fun x : ℕ → ℝ => x) fun j =>
    continuous_apply j).comp (continuous_extendVec _)

theorem hBr_le {D : ℝ} (hD : 0 ≤ D) (k l : ℕ) (x : Fin (k + l + 1) → ℝ) :
    |hBr D k l x| ≤ 2 * D * k * l * (1 + ∑ i, |x i|) ^ 4 := by
  set Z := ∑ i, |x i|
  have hZ : 0 ≤ Z := by positivity
  refine (abs_transmissionBracket_le hD k l (abs_extendVec_le _ x _)
    (abs_extendVec_le _ x _)).trans ?_
  have : Z ≤ (1 + Z) ^ 4 := by simpa using pow_le_one_add_pow4 hZ (j := 1) (by norm_num)
  have h0 : 0 ≤ 2 * D * k * l := by positivity
  exact mul_le_mul_of_nonneg_left this h0

theorem hBr_fin (D b : ℝ) (e : ℕ → ℝ) (W : ℕ) {k : ℕ} (hk : 1 ≤ k) (l : ℕ) (u : ℝ)
    (ω : GrowthPath W) :
    hBr D k l (finVec b e W (ptVec (k + l + 1) u) ω) =
      transmissionBracket D k l (pathPowers b (e W) W ⌊(W : ℝ) * u⌋₊ ω) := by
  simp only [hBr, transmissionBracket]
  rw [extendVec_finVec b e W _ u ω (by omega) (by omega),
    extendVec_finVec b e W _ u ω (by omega) le_rfl]

theorem hBr_lim {Ω : Type*} (D : ℝ) (Pk : ℕ → ℝ → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k) (l : ℕ) (u : ℝ)
    (ω : Ω) : hBr D k l (limVec Pk (ptVec (k + l + 1) u) ω) =
      transmissionBracket D k l (fun i => Pk i u ω) := by
  simp only [hBr, transmissionBracket]
  rw [extendVec_limVec Pk _ u ω (by omega) (by omega), extendVec_limVec Pk _ u ω (by omega) le_rfl]

theorem bracket_cutVec {Ω : Type*} (D : ℝ) (Pk : ℕ → ℝ → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k) (l : ℕ)
    (u : ℝ) (ω : Ω) :
    transmissionBracket D k l (cutVec Pk u ω) = transmissionBracket D k l (fun i => Pk i u ω) := by
  simp only [transmissionBracket, cutVec, show 1 ≤ k + l by omega, show 1 ≤ k + l + 1 by omega,
    ↓reduceIte]

/-- Times of the shapes: all in `[s, t]`, powers `≥ 1`. -/
theorem ptYY_mem {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {s t : ℝ} (hst : s ≤ t) :
    ∀ i, 1 ≤ (ptYY k l s t i).1 ∧ s ≤ (ptYY k l s t i).2 ∧ (ptYY k l s t i).2 ≤ t := by
  intro i; fin_cases i <;> simp [ptYY, hk, hl, hst]

theorem ptYA_mem {k l : ℕ} (hk : 1 ≤ k) {s t u : ℝ} (hst : s ≤ t) (hu : u ∈ Set.Icc s t) :
    ∀ i, 1 ≤ (ptYA k l s t u i).1 ∧ s ≤ (ptYA k l s t u i).2 ∧ (ptYA k l s t u i).2 ≤ t := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> simp [ptYA, hk, hst]
  · simp [ptYA, ptVec, hu.1, hu.2]

theorem ptAA_mem {l k : ℕ} {s t v u : ℝ} (hv : v ∈ Set.Icc s t) (hu : u ∈ Set.Icc s t) :
    ∀ i, 1 ≤ (ptAA l k v u i).1 ∧ s ≤ (ptAA l k v u i).2 ∧ (ptAA l k v u i).2 ≤ t := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simp [ptAA, ptVec, hv.1, hv.2]
  · simp [ptAA, ptVec, hu.1, hu.2]

theorem ptVec_mem {n : ℕ} {s t u : ℝ} (hu : u ∈ Set.Icc s t) :
    ∀ i, 1 ≤ (ptVec n u i).1 ∧ s ≤ (ptVec n u i).2 ∧ (ptVec n u i).2 ≤ t :=
  fun i => ⟨by simp [ptVec], hu.1, hu.2⟩

end BlockBand.Transmission.Generator
