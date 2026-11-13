module

public import BlockBand.Endpoints.Poisson.SingleCollarStage
public import BlockBand.Endpoints.Response.EdgeClockMoments
public import BlockBand.Endpoints.Poisson.PhaseFractionalCollar

/-!
# Assembly of the single-collar log-error bound: one-configuration moment bookkeeping

* `sca2_transfer`: the law clause of `ScsWardData.paths` transfers
  `E (Tr Qc^q)^r` to the `growthPathLaw` integral of the interval source, and `Qc` is Hermitian
  almost surely.
* `sca2_sigma_moment`: at one stage configuration with Ward data `D`, and source profiles `qs`
  equal to `1` on the source windows, if the four interval-source moments
  `E (Tr Q(qs i)^{q})^{r}`, `(q, r) ∈ {p, p/2} × {1, 2}`, are at most `B`, then
  `E(σ̄ + σ̄²) ≤ sca2K2 p ηm κm · m² · B`, for `η ≤ ηm` and `0 ≤ κ ≤ κm` (Ward majorant
  `σ̄ = scsSigmaBound p η κ Q`, `Tr Q^q ≤ Σ_i Tr (Qc i)^q`, `(Σ_{i<m} x_i)² ≤ m Σ x_i²`).
* `sca2_boundaryZ_im_le_one`: `Im z_b(e) ≤ 1` on `(-2, 2)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw
  GrowthPath)
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open scoped ENNReal ComplexOrder

/-!
## 1. The Hermitian part
-/

section Herm

/-- The Hermitian part `(A + Aᴴ)/2`. -/
def sca2_herm {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem sca2_herm_isHermitian {ι : Type*} (A : Matrix ι ι ℂ) : (sca2_herm A).IsHermitian := by
  unfold sca2_herm IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem sca2_herm_of_isHermitian {ι : Type*} {A : Matrix ι ι ℂ} (h : A.IsHermitian) :
    sca2_herm A = A := by
  unfold sca2_herm
  rw [h.eq, ← two_smul ℂ A, smul_smul]
  norm_num

theorem sca2_continuous_herm {ι : Type*} : Continuous (sca2_herm (ι := ι)) := by
  unfold sca2_herm
  exact ((continuous_id (X := Matrix ι ι ℂ)).add
    (continuous_id (X := Matrix ι ι ℂ)).matrix_conjTranspose).const_smul (1 / 2 : ℂ)

theorem sca2_measurable_fracTrace_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ}
    (hq : 0 < q) : Measurable (fun A : Matrix ι ι ℂ => fracTrace q (sca2_herm A)) :=
  rh_measurable_fracTrace sca2_continuous_herm.measurable sca2_herm_isHermitian hq

end Herm

theorem sca2_measurable_intervalSource (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => intervalSource b E W j q ω) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [intervalSource, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul
    ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      (ns_measurable_tagResponse b E W j k)))

/-!
## 2. Transfer of interval-source moments
-/

/-- **Law transfer.** If `μ.map Qc = growthPathLaw.map (intervalSource …)` for a measurable `Qc` and a nonnegative
profile, then `Qc` is Hermitian almost surely and `E_μ (Tr (Qc)_h^q)^r ≤ E (Tr Q(qs)^q)^r` under `growthPathLaw`
(`(·)_h` the Hermitian part). -/
theorem sca2_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {b e : ℝ} {W n : ℕ}
    {qs : ℝ → ℝ} (hqs : ∀ x, 0 ≤ qs x)
    {Qc : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hQm : Measurable Qc)
    (hlaw : μ.map Qc = (growthPathLaw W b).map (intervalSource b e W n qs)) {q : ℝ} (hq : 0 < q)
    (r : ℝ) :
    (∀ᵐ ω ∂μ, (Qc ω).IsHermitian) ∧
      ∫⁻ ω, ENNReal.ofReal (fracTrace q (sca2_herm (Qc ω))) ^ r ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (fracTrace q (intervalSource b e W n qs ω)) ^ r ∂growthPathLaw W b := by
  have hH : ∀ ω, (intervalSource b e W n qs ω).IsHermitian := fun ω =>
    (intervalSource_posSemidef b e W n qs hqs ω).isHermitian
  have hs : MeasurableSet {A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ | ¬ A.IsHermitian} := by
    have : IsClosed {A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ | Aᴴ = A} :=
      isClosed_eq continuous_id.matrix_conjTranspose continuous_id
    exact this.measurableSet.compl
  refine ⟨?_, ?_⟩
  · rw [ae_iff]
    change μ (Qc ⁻¹' {A | ¬ A.IsHermitian}) = 0
    rw [← Measure.map_apply hQm hs, hlaw,
      Measure.map_apply (sca2_measurable_intervalSource b e W n qs) hs]
    have : intervalSource b e W n qs ⁻¹' {A | ¬ A.IsHermitian} = ∅ := by
      ext ω; simp [hH ω]
    rw [this, measure_empty]
  · have hg : Measurable fun A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
        ENNReal.ofReal (fracTrace q (sca2_herm A)) ^ r :=
      (ENNReal.measurable_ofReal.comp (sca2_measurable_fracTrace_herm hq)).pow_const r
    rw [← lintegral_map hg hQm, hlaw, lintegral_map hg (sca2_measurable_intervalSource b e W n qs)]
    refine le_of_eq (lintegral_congr fun ω => ?_)
    rw [sca2_herm_of_isHermitian (hH ω)]

/-!
## 3. The Ward majorant in terms of component traces
-/

/-- The constant `K₁ = 2^{p/2}·2·((2ηm κm)^p + (4ηm κm)^{p/2})` bounding the coefficients of the
Ward majorant. -/
def sca2K1 (p ηm κm : ℝ) : ℝ :=
  2 ^ (p / 2) * (2 * ((2 * ηm * κm) ^ p + (4 * ηm * κm) ^ (p / 2)))

/-- The constant `K₂ = 4 (K₁ + 2K₁²)` of `sca2_sigma_moment`. -/
def sca2K2 (p ηm κm : ℝ) : ℝ := 4 * (sca2K1 p ηm κm + 2 * sca2K1 p ηm κm ^ 2)

theorem sca2K1_nonneg {p ηm κm : ℝ} (hη : 0 ≤ ηm) (hκ : 0 ≤ κm) : 0 ≤ sca2K1 p ηm κm := by
  unfold sca2K1; positivity

theorem sca2K2_nonneg {p ηm κm : ℝ} (hη : 0 ≤ ηm) (hκ : 0 ≤ κm) : 0 ≤ sca2K2 p ηm κm := by
  have := sca2K1_nonneg (p := p) hη hκ
  unfold sca2K2; positivity

theorem sca2_sigmaBound_nonneg {p η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Q : Matrix ι ι ℂ) : 0 ≤ scsSigmaBound p η κ Q := by
  unfold scsSigmaBound
  have := fracTrace_nonneg p Q
  have := fracTrace_nonneg (p / 2) Q
  positivity

theorem sca2_sigmaBound_le {p η κ ηm κm : ℝ} (hp : 0 < p) (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hηm : η ≤ ηm) (hκm : κ ≤ κm) {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ) :
    scsSigmaBound p η κ Q ≤ sca2K1 p ηm κm * (fracTrace p Q + fracTrace (p / 2) Q) := by
  unfold scsSigmaBound sca2K1
  have h1 : (2 * η * κ) ^ p ≤ (2 * ηm * κm) ^ p :=
    Real.rpow_le_rpow (by positivity) (by gcongr; linarith) hp.le
  have h2 : (4 * η * κ) ^ (p / 2) ≤ (4 * ηm * κm) ^ (p / 2) :=
    Real.rpow_le_rpow (by positivity) (by gcongr; linarith) (by positivity)
  have t1 := fracTrace_nonneg p Q
  have t2 := fracTrace_nonneg (p / 2) Q
  have a1 : 0 ≤ (2 * η * κ) ^ p := by positivity
  have a2 : 0 ≤ (4 * η * κ) ^ (p / 2) := by positivity
  have h3 : (2 * η * κ) ^ p * fracTrace p Q + (4 * η * κ) ^ (p / 2) * fracTrace (p / 2) Q ≤
      ((2 * ηm * κm) ^ p + (4 * ηm * κm) ^ (p / 2)) * (fracTrace p Q + fracTrace (p / 2) Q) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 t1, mul_le_mul_of_nonneg_right h2 t2]
  have h4 : (0 : ℝ) ≤ 2 ^ (p / 2) := by positivity
  calc 2 ^ (p / 2) * (2 * ((2 * η * κ) ^ p * fracTrace p Q +
        (4 * η * κ) ^ (p / 2) * fracTrace (p / 2) Q))
      ≤ 2 ^ (p / 2) * (2 * (((2 * ηm * κm) ^ p + (4 * ηm * κm) ^ (p / 2)) *
        (fracTrace p Q + fracTrace (p / 2) Q))) := by gcongr
    _ = _ := by ring

/-- Real arithmetic: `0 ≤ s ≤ K (x + y)`, `x ≤ Σ a`, `y ≤ Σ c` (`a, c, K ≥ 0`, `m ≥ 1`) give
`s + s² ≤ (K + 2K²) m Σ_i (a_i + a_i² + c_i + c_i²)`. -/
theorem sca2_sq_arith {m : ℕ} (hm : 1 ≤ m) {K s x y : ℝ} {a c : Fin m → ℝ} (hK : 0 ≤ K)
    (hs0 : 0 ≤ s) (hs : s ≤ K * (x + y)) (hx : x ≤ ∑ i, a i)
    (hy : y ≤ ∑ i, c i) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) :
    s + s ^ 2 ≤ (K + 2 * K ^ 2) * m * ∑ i, (a i + a i ^ 2 + c i + c i ^ 2) := by
  set T := ∑ i, (a i + c i) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => add_nonneg (ha i) (hc i)
  have hxy : x + y ≤ T := by rw [hT, Finset.sum_add_distrib]; linarith
  have hsT : s ≤ K * T := hs.trans (mul_le_mul_of_nonneg_left hxy hK)
  have hT2 : T ^ 2 ≤ m * ∑ i, (a i + c i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => a i + c i)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hsq : ∀ i, (a i + c i) ^ 2 ≤ 2 * (a i ^ 2 + c i ^ 2) := fun i => by
    nlinarith [sq_nonneg (a i - c i)]
  have hT2' : T ^ 2 ≤ m * (2 * ∑ i, (a i ^ 2 + c i ^ 2)) := by
    calc T ^ 2 ≤ m * ∑ i, (a i + c i) ^ 2 := hT2
      _ ≤ m * ∑ i, 2 * (a i ^ 2 + c i ^ 2) := by gcongr with i; exact hsq i
      _ = m * (2 * ∑ i, (a i ^ 2 + c i ^ 2)) := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set U := ∑ i, (a i + a i ^ 2 + c i + c i ^ 2) with hU
  have hTU : T ≤ U := Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (a i), sq_nonneg (c i)]
  have hSU : ∑ i, (a i ^ 2 + c i ^ 2) ≤ U :=
    Finset.sum_le_sum fun i _ => by nlinarith [ha i, hc i]
  have hU0 : 0 ≤ U := hT0.trans hTU
  have hs2 : s ^ 2 ≤ K ^ 2 * T ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs0 hsT 2
  have e1 : s ≤ K * m * U := by
    refine hsT.trans ?_
    calc K * T ≤ K * U := mul_le_mul_of_nonneg_left hTU hK
      _ ≤ K * m * U := by nlinarith [mul_nonneg hK hU0]
  have e2 : s ^ 2 ≤ 2 * K ^ 2 * m * U := by
    refine hs2.trans ?_
    calc K ^ 2 * T ^ 2 ≤ K ^ 2 * (m * (2 * ∑ i, (a i ^ 2 + c i ^ 2))) :=
          mul_le_mul_of_nonneg_left hT2' (sq_nonneg K)
      _ ≤ K ^ 2 * (m * (2 * U)) := by gcongr
      _ = 2 * K ^ 2 * m * U := by ring
  nlinarith

/-!
## 4. The `σ̄`-moment at one configuration
-/

/-- **The Ward-majorant moment at one stage configuration** (the dilation fractional moments). Ward data `D` with
`η = Im z_b(e) ∈ [0, ηm]`, `0 ≤ κ ≤ κm`, `0 < p < 1`, `m ≥ 1`. For source profiles `qs i ∈ [0, 1]` equal to `1` on
the source windows of `D.paths`, if every interval-source moment `E (Tr Q(qs i)^q)^r`,
`(q, r) ∈ {p, p/2} × {1, 2}`, is at most `B` under `growthPathLaw`, then `E(σ̄ + σ̄²) ≤ K₂ m² B` with
`K₂ = sca2K2 p ηm κm`. -/
theorem sca2_sigma_moment (P : Parameters) {m : ℕ} (hm : 1 ≤ m) (L : Fin m → ℕ) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (buf : ℕ) (κ : ℝ)
    (D : ScsWardData P L 0 π S k e buf κ) {p ηm κm B : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη0 : 0 ≤ (boundaryZ P.b e).im) (hη : (boundaryZ P.b e).im ≤ ηm) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ κm) (qs : Fin m → ℝ → ℝ) (hqs : ∀ i x, 0 ≤ qs i x ∧ qs i x ≤ 1)
    (hwin : ∀ i, ∀ x ∈ Icc (((buf : ℝ) - 2) / P.W) (((D.len i : ℝ) - buf + 2) / P.W),
      qs i x = 1)
    (hB : ∀ i, ∀ q ∈ ({p, p / 2} : Set ℝ), ∀ r ∈ ({1, 2} : Set ℝ),
      ∫⁻ ω, ENNReal.ofReal (fracTrace q (intervalSource P.b e P.W (D.len i) (qs i) ω)) ^ r
        ∂growthPathLaw P.W P.b ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (scsSigmaBound p (boundaryZ P.b e).im κ (D.Q (oldCoords L 0 k ω)) +
        scsSigmaBound p (boundaryZ P.b e).im κ (D.Q (oldCoords L 0 k ω)) ^ 2)
      ∂(ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal (sca2K2 p ηm κm * (m : ℝ) ^ 2 * B) := by
  set μ := ringCoordLaw P.n P.W P.b
  have hηm : 0 ≤ ηm := hη0.trans hη
  have hκm : 0 ≤ κm := hκ0.trans hκ
  obtain ⟨Qc, hQm, hlaw, hdom⟩ := D.paths qs hqs hwin
  have hp2 : 0 < p / 2 := by positivity
  have hp2' : p / 2 < 1 := by linarith
  set t : ℝ → Fin m → RingCoords P.n P.W → ℝ := fun q i ω => fracTrace q (sca2_herm (Qc i ω))
  have htm : ∀ q, 0 < q → ∀ i, Measurable (t q i) := fun q hq i =>
    (sca2_measurable_fracTrace_herm hq).comp (hQm i)
  have ht0 : ∀ q i ω, 0 ≤ t q i ω := fun q i ω => fracTrace_nonneg _ _
  have htr := fun i (q : ℝ) (hq : 0 < q) (r : ℝ) =>
    sca2_transfer (fun x => (hqs i x).1) (hQm i) (hlaw i) hq r
  have hHerm : ∀ᵐ ω ∂μ, ∀ i, (Qc i ω).IsHermitian :=
    ae_all_iff.2 fun i => (htr i p hp0 1).1
  set K₁ := sca2K1 p ηm κm
  have hK₁ : 0 ≤ K₁ := sca2K1_nonneg hηm hκm
  set Y : RingCoords P.n P.W → ℝ := fun ω =>
    ∑ i, (t p i ω + t p i ω ^ 2 + t (p / 2) i ω + t (p / 2) i ω ^ 2)
  have hpt : ∀ᵐ ω ∂μ,
      scsSigmaBound p (boundaryZ P.b e).im κ (D.Q (oldCoords L 0 k ω)) +
        scsSigmaBound p (boundaryZ P.b e).im κ (D.Q (oldCoords L 0 k ω)) ^ 2 ≤
      (K₁ + 2 * K₁ ^ 2) * m * Y ω := by
    filter_upwards [hdom, hHerm] with ω hω hH
    have hti : ∀ q i, fracTrace q (Qc i ω) = t q i ω := fun q i => by
      simp only [t, sca2_herm_of_isHermitian (hH i)]
    have hx := hω p hp0 hp1
    have hy := hω (p / 2) hp2 hp2'
    simp only [hti] at hx hy
    exact sca2_sq_arith hm hK₁ (sca2_sigmaBound_nonneg hη0 hκ0 _)
      (sca2_sigmaBound_le hp0 hη0 hκ0 hη hκ _) hx hy (fun i => ht0 _ i ω) (fun i => ht0 _ i ω)
  -- the four moments of each component
  have hmom : ∀ q ∈ ({p, p / 2} : Set ℝ), ∀ r ∈ ({1, 2} : Set ℝ), ∀ i,
      ∫⁻ ω, ENNReal.ofReal (t q i ω) ^ r ∂μ ≤ ENNReal.ofReal B := by
    intro q hq r hr i
    have hq0 : 0 < q := by rcases hq with rfl | rfl <;> assumption
    exact (htr i q hq0 r).2.trans (hB i q hq r hr)
  have hsq : ∀ q i ω, ENNReal.ofReal (t q i ω ^ 2) = ENNReal.ofReal (t q i ω) ^ (2 : ℝ) :=
    fun q i ω => by
      rw [ENNReal.ofReal_rpow_of_nonneg (ht0 q i ω) (by norm_num)]
      norm_cast
  have hone : ∀ q i ω, ENNReal.ofReal (t q i ω) = ENNReal.ofReal (t q i ω) ^ (1 : ℝ) :=
    fun q i ω => (ENNReal.rpow_one _).symm
  have hcomp : ∀ i, ∫⁻ ω, ENNReal.ofReal (t p i ω + t p i ω ^ 2 + t (p / 2) i ω +
      t (p / 2) i ω ^ 2) ∂μ ≤ 4 * ENNReal.ofReal B := by
    intro i
    have m1 := htm p hp0 i
    have m2 := htm (p / 2) hp2 i
    have e : ∀ ω, ENNReal.ofReal (t p i ω + t p i ω ^ 2 + t (p / 2) i ω + t (p / 2) i ω ^ 2) =
        ENNReal.ofReal (t p i ω) + ENNReal.ofReal (t p i ω ^ 2) + ENNReal.ofReal (t (p / 2) i ω) +
          ENNReal.ofReal (t (p / 2) i ω ^ 2) := fun ω => by
      have := ht0 p i ω; have := ht0 (p / 2) i ω
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    simp_rw [e]
    have mm : ∀ q, 0 < q → Measurable fun ω => ENNReal.ofReal (t q i ω) := fun q hq =>
      ENNReal.measurable_ofReal.comp (htm q hq i)
    have mm2 : ∀ q, 0 < q → Measurable fun ω => ENNReal.ofReal (t q i ω ^ 2) := fun q hq =>
      ENNReal.measurable_ofReal.comp ((htm q hq i).pow_const 2)
    rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (t p i ω) + ENNReal.ofReal (t p i ω ^ 2) +
        ENNReal.ofReal (t (p / 2) i ω)) (((mm p hp0).add (mm2 p hp0)).add (mm _ hp2)),
      lintegral_add_left (f := fun ω => ENNReal.ofReal (t p i ω) + ENNReal.ofReal (t p i ω ^ 2))
        ((mm p hp0).add (mm2 p hp0)),
      lintegral_add_left (f := fun ω => ENNReal.ofReal (t p i ω)) (mm p hp0)]
    simp_rw [hsq]
    have a1 := hmom p (by simp) 1 (by simp) i
    have a2 := hmom p (by simp) 2 (by simp) i
    have a3 := hmom (p / 2) (by simp) 1 (by simp) i
    have a4 := hmom (p / 2) (by simp) 2 (by simp) i
    simp only [← hone] at a1 a3
    calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B := by
          gcongr
      _ = 4 * ENNReal.ofReal B := by ring
  have hK2 : 0 ≤ K₁ + 2 * K₁ ^ 2 := by positivity
  have hY0 : ∀ ω, ∀ i ∈ Finset.univ,
      0 ≤ t p i ω + t p i ω ^ 2 + t (p / 2) i ω + t (p / 2) i ω ^ 2 := fun ω i _ => by
    have := ht0 p i ω; have := ht0 (p / 2) i ω; positivity
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal ((K₁ + 2 * K₁ ^ 2) * m * Y ω) ∂μ :=
        lintegral_mono_ae (hpt.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal ((K₁ + 2 * K₁ ^ 2) * m) * ∑ i, ∫⁻ ω, ENNReal.ofReal (t p i ω +
          t p i ω ^ 2 + t (p / 2) i ω + t (p / 2) i ω ^ 2) ∂μ := by
        simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (K₁ + 2 * K₁ ^ 2) * (m : ℝ)), Y]
        rw [lintegral_const_mul]
        · congr 1
          simp_rw [ENNReal.ofReal_sum_of_nonneg (hY0 _)]
          refine lintegral_finsetSum _ fun i _ => ENNReal.measurable_ofReal.comp ?_
          exact (((htm p hp0 i).add ((htm p hp0 i).pow_const 2)).add
            (htm _ hp2 i)).add ((htm _ hp2 i).pow_const 2)
        · refine ENNReal.measurable_ofReal.comp ?_
          exact Finset.measurable_sum _ fun i _ => (((htm p hp0 i).add
            ((htm p hp0 i).pow_const 2)).add (htm _ hp2 i)).add ((htm _ hp2 i).pow_const 2)
    _ ≤ ENNReal.ofReal ((K₁ + 2 * K₁ ^ 2) * m) * ∑ _i : Fin m, 4 * ENNReal.ofReal B := by
        gcongr with i
        exact hcomp i
    _ = ENNReal.ofReal (sca2K2 p ηm κm * (m : ℝ) ^ 2 * B) := by
        rcases le_or_gt B 0 with hB0 | hB0
        · have h0 : 0 ≤ sca2K2 p ηm κm * (m : ℝ) ^ 2 := by
            have := sca2K2_nonneg (p := p) hηm hκm; positivity
          rw [ENNReal.ofReal_of_nonpos hB0,
            ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 hB0)]
          simp
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [sca2K2, K₁]
        ring

/-!
## 5. The height `η`
-/

theorem sca2_boundaryZ_im_le_one {b e : ℝ} (hb : 0 < b) (he1 : -2 < e) (he2 : e < 2) :
    (boundaryZ b e).im ≤ 1 := by
  rw [PhaseFractional.boundaryZ_im_eq b (by nlinarith)]
  have h1 : Real.sqrt (4 - e ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 := Real.sqrt_nonneg (4 - e ^ 2)
  nlinarith

end BlockBand.Endpoints
