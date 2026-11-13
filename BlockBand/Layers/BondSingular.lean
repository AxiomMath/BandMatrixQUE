module

public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.Nets
public import BlockBand.Layers.SpectralSplit

/-!
# The bond singular floor `d = s_min(B*|_S) ∧ 1`: tail and inverse moments

## Setting and law

Conditional on `D`, let `d = s_min(B*|_{Ran P}) ∧ 1` and `K = ‖B‖`. On `K ≤ t^{-1/2}`, a net of
mesh `t^{3/2}/2` on the unit sphere of `Ran P` gives `P(d < t | D) ≤ (C_b' t)^W`, uniformly in
the subspace; integrating the lower tail gives `‖d⁻¹‖_{L^q(·|D)} ≤ C_b` for `q ≤ ε₂ W`.

`S` is a fixed deterministic complex subspace of the physical coordinates
`EuclideanSpace ℂ (PhysSite W σ)` with `finrank ℂ S ≤ W / 8` (natural division; this is
conditioning on `D`, with `S = Ran P`, e.g. `S = lowSubspace hD τ`). The law is
`layerLaw W b σ` (bonds `Gin(b/W)`, `E|B_ij|² = b/W`); only the bond coordinate `ω.2` enters.
Norms are Euclidean on vectors and the `L²` operator norm on matrices.

## Main declarations

* `singFloor S B = sInf ({1} ∪ {‖(bondMatrix σ B)ᴴ u‖ : u ∈ S, ‖u‖ = 1})`, i.e.
  `min 1 (inf_{u ∈ S, ‖u‖ = 1} ‖B* u‖)`, equal to `1` for `S = ⊥` (deterministic).
  `singFloor_nonneg`, `singFloor_le_one`, `singFloor_mul_norm_le`, and `singFloor_hPB`
  (the hypothesis `hPB` of `BlockBand.Layers.layerResolvent_bound` with `d = singFloor S B`),
  `singFloor_hPB_lowProjection` (for `P = lowProjection hD τ`, `S = lowSubspace hD τ`).
* `singFloor_tail`: for `0 < t ≤ 1`,
  `layerLaw W b σ {singFloor S ω.2 < t} ≤ (singTailConst b * t)^W`,
  `singTailConst b = 27 e / b + 4 b 12^8` (uniform in `S`, `W ≥ 1`, `σ`; `t₀ = 1`).
* `singFloor_pos_ae`: `0 < singFloor S ω.2` almost surely.
* `singFloor_inv_moment`: for `1 ≤ q ≤ W/2` (`ε₂ = 1/2`),
  `∫⁻ (singFloor S ω.2)⁻¹^q ≤ (singMomentConst b)^q`, `singMomentConst b = 4^(⌈singTailConst b⌉₊+2)`.
  No measurability of `singFloor` is used (measurable hulls `toMeasurable`).
* Helpers: `singRestrict` (`B*|_S` as a continuous linear map, `‖B*|_S‖ ≤ ‖B‖`),
  `singFloor_tail_split` (union bound for general `K, ε`), `sing_net_term_le`,
  `sing_norm_term_le`, `sing_exists_net`, and the dyadic integration lemmas
  `sing_inv_rpow_le_dyadic`, `sing_dyadic_term_le`, `sing_dyadic_final_le` (renamed copies
  of the `AbsorberCount` lemmas, which are not imported here) with `sing_lintegral_inv_rpow_le_of_tail`
  (the `AbsorberCount` version without the measurability hypothesis).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix MeasureTheory Module Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator ENNReal

/-!
## Deterministic part
-/

section Deterministic

variable {W : ℕ} {σ : LayerShape}

/-- The value set `{1} ∪ {‖(bondMatrix σ B)ᴴ u‖ : u ∈ S, ‖u‖ = 1}`. -/
def singValues (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ)))
    (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) : Set ℝ :=
  insert 1 ((fun u => ‖toEuclideanLin (bondMatrix σ B)ᴴ u‖) '' {u | u ∈ S ∧ ‖u‖ = 1})

/-- **The bond singular floor** `d = s_min(B*|_S) ∧ 1` (the Gaussian absorption lemma):
`singFloor S B = min 1 (inf_{u ∈ S, ‖u‖ = 1} ‖(bondMatrix σ B)ᴴ u‖)`, written as `sInf` of
`singValues S B` (the `1` makes the set nonempty, so `singFloor ⊥ B = 1`). Deterministic. -/
def singFloor (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ)))
    (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  sInf (singValues S B)

variable (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ)))
  (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ)

theorem singValues_nonempty : (singValues S B).Nonempty := Set.insert_nonempty _ _

theorem singValues_nonneg : ∀ x ∈ singValues S B, 0 ≤ x := by
  rintro x (rfl | ⟨u, _, rfl⟩)
  · exact zero_le_one
  · exact norm_nonneg _

theorem singValues_bddBelow : BddBelow (singValues S B) := ⟨0, singValues_nonneg S B⟩

/-- `0 ≤ singFloor S B`. -/
theorem singFloor_nonneg : 0 ≤ singFloor S B :=
  le_csInf (singValues_nonempty S B) (singValues_nonneg S B)

/-- `singFloor S B ≤ 1`. -/
theorem singFloor_le_one : singFloor S B ≤ 1 :=
  csInf_le (singValues_bddBelow S B) (Set.mem_insert _ _)

/-- Normalization at `S = ⊥`: the floor of the zero subspace is `1`. -/
theorem singFloor_bot : singFloor (⊥ : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) B = 1 := by
  have h : singValues (⊥ : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) B = {1} := by
    ext x
    simp only [singValues, Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq,
      Submodule.mem_bot, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨u, ⟨rfl, hu⟩, _⟩)
      · exact h
      · simp at hu
    · exact Or.inl
  rw [singFloor, h, csInf_singleton]

/-- `singFloor S B ≤ ‖B* u‖` for every unit `u ∈ S`. -/
theorem singFloor_le_norm {u : EuclideanSpace ℂ (PhysSite W σ)} (hu : u ∈ S) (h1 : ‖u‖ = 1) :
    singFloor S B ≤ ‖toEuclideanLin (bondMatrix σ B)ᴴ u‖ :=
  csInf_le (singValues_bddBelow S B) (Set.mem_insert_of_mem _ ⟨u, ⟨hu, h1⟩, rfl⟩)

/-- **Lower bound on `S`**: `singFloor S B * ‖w‖ ≤ ‖B* w‖` for every `w ∈ S`. -/
theorem singFloor_mul_norm_le {w : EuclideanSpace ℂ (PhysSite W σ)} (hw : w ∈ S) :
    singFloor S B * ‖w‖ ≤ ‖toEuclideanLin (bondMatrix σ B)ᴴ w‖ := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hcx : ‖((‖w‖⁻¹ : ℝ) : ℂ)‖ = ‖w‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have hu : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ S := S.smul_mem _ hw
  have h1 : ‖((‖w‖⁻¹ : ℝ) : ℂ) • w‖ = 1 := by rw [norm_smul, hcx, inv_mul_cancel₀ hn.ne']
  have h := singFloor_le_norm S B hu h1
  rw [map_smul, norm_smul, hcx] at h
  calc singFloor S B * ‖w‖ ≤ (‖w‖⁻¹ * ‖toEuclideanLin (bondMatrix σ B)ᴴ w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right h hn.le
    _ = ‖toEuclideanLin (bondMatrix σ B)ᴴ w‖ := by field_simp

/-- **The hypothesis `hPB` of `layerResolvent_bound`** with `d = singFloor S B`:
for every matrix `P` whose range lies in `S`,
`d ‖P v‖ ≤ ‖(bondMatrix σ B)ᴴ (P v)‖` for all `v`. Deterministic. -/
theorem singFloor_hPB (P : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (hP : ∀ v : EuclideanSpace ℂ (PhysSite W σ), toEuclideanLin P v ∈ S)
    (v : EuclideanSpace ℂ (PhysSite W σ)) :
    singFloor S B * ‖toEuclideanLin P v‖ ≤
      ‖toEuclideanLin (bondMatrix σ B)ᴴ (toEuclideanLin P v)‖ :=
  singFloor_mul_norm_le S B (hP v)

/-- `singFloor_hPB` for the low spectral projection `P = lowProjection hD τ` and
`S = lowSubspace hD τ`. -/
theorem singFloor_hPB_lowProjection {D : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hD : D.IsHermitian) (τ : ℝ) (v : EuclideanSpace ℂ (PhysSite W σ)) :
    singFloor (lowSubspace hD τ) B * ‖toEuclideanLin (lowProjection hD τ) v‖ ≤
      ‖toEuclideanLin (bondMatrix σ B)ᴴ (toEuclideanLin (lowProjection hD τ) v)‖ :=
  singFloor_hPB (lowSubspace hD τ) B _ (lowProjection_mem hD τ) v

/-- For `t ≤ 1`, `singFloor S B < t` forces a unit `u ∈ S` with `‖B* u‖ < t`. -/
theorem exists_of_singFloor_lt {t : ℝ} (ht : t ≤ 1) (h : singFloor S B < t) :
    ∃ u ∈ S, ‖u‖ = 1 ∧ ‖toEuclideanLin (bondMatrix σ B)ᴴ u‖ < t := by
  obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt (singValues_nonempty S B) h
  rcases ha with rfl | ⟨u, ⟨hu, h1⟩, rfl⟩
  · exact absurd ht (not_le.mpr hat)
  · exact ⟨u, hu, h1, hat⟩

/-- `B*` restricted to `S`, as a continuous `ℂ`-linear map `S → ℂ^{ports}`. -/
def singRestrict : S →L[ℂ] EuclideanSpace ℂ (PortSite W σ) :=
  (LinearMap.toContinuousLinearMap (toEuclideanLin (bondMatrix σ B)ᴴ)).comp S.subtypeL

theorem singRestrict_apply (x : S) :
    singRestrict S B x = toEuclideanLin (bondMatrix σ B)ᴴ (x : EuclideanSpace ℂ (PhysSite W σ)) :=
  rfl

/-- `‖B*|_S‖ ≤ ‖B‖` (`L²` operator norm). -/
theorem norm_singRestrict_le : ‖singRestrict S B‖ ≤ ‖bondMatrix σ B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [singRestrict_apply, ← l2_opNorm_conjTranspose (bondMatrix σ B)]
  exact (LinearMap.toContinuousLinearMap (toEuclideanLin (bondMatrix σ B)ᴴ)).le_opNorm
    (x : EuclideanSpace ℂ (PhysSite W σ))

end Deterministic

/-!
## Elementary estimates for the tail
-/

section Elementary

/-- Net term (`ε = t^{3/2}/2`, `K = t^{-1/2}`, `8k ≤ W`, `0 < t ≤ 1`):
`(3/ε)^{2k} (c (t + ε K)²)^W ≤ (6 (9/4) c t)^W`. -/
theorem sing_net_term_le {t c : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hc : 0 ≤ c) {k W : ℕ}
    (hk : 8 * k ≤ W) :
    (3 / (t * Real.sqrt t / 2)) ^ (2 * k) *
        (c * (t + t * Real.sqrt t / 2 * (Real.sqrt t)⁻¹) ^ 2) ^ W ≤
      (6 * (9 / 4) * c * t) ^ W := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have e1 : t + t * Real.sqrt t / 2 * (Real.sqrt t)⁻¹ = 3 / 2 * t := by
    field_simp; ring
  have e2 : (3 / (t * Real.sqrt t / 2)) ^ (2 * k) = 6 ^ (2 * k) / t ^ (3 * k) := by
    rw [eq_div_iff (by positivity)]
    have e3 : t ^ (3 * k) = (t * Real.sqrt t) ^ (2 * k) := by
      rw [pow_mul, pow_mul]
      congr 1
      calc t ^ 3 = t ^ 2 * (Real.sqrt t * Real.sqrt t) := by rw [hss]; ring
        _ = (t * Real.sqrt t) ^ 2 := by ring
    rw [e3, ← mul_pow]
    congr 1
    field_simp
    ring
  rw [e1, e2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h1 : (6 : ℝ) ^ (2 * k) ≤ 6 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : t ^ W ≤ t ^ (3 * k) := pow_le_pow_of_le_one ht0.le ht1 (by omega)
  have e4 : (c * (3 / 2 * t) ^ 2) ^ W = (9 / 4 * c) ^ W * t ^ W * t ^ W := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  have e5 : (6 * (9 / 4) * c * t) ^ W = 6 ^ W * (9 / 4 * c) ^ W * t ^ W := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  rw [e4, e5]
  have h0 : 0 ≤ (9 / 4 * c) ^ W * t ^ W := by positivity
  calc (6 : ℝ) ^ (2 * k) * ((9 / 4 * c) ^ W * t ^ W * t ^ W)
      = ((9 / 4 * c) ^ W * t ^ W) * (6 ^ (2 * k) * t ^ W) := by ring
    _ ≤ ((9 / 4 * c) ^ W * t ^ W) * (6 ^ W * t ^ (3 * k)) := by gcongr
    _ = 6 ^ W * (9 / 4 * c) ^ W * t ^ W * t ^ (3 * k) := by ring

/-- Norm term (`K = t^{-1/2}`): with nets of cardinalities `n₁, n₂ ≤ 12^{4W}`,
`n₁ n₂ exp(-K² W/(4b)) ≤ (4 b 12^8 t)^W` for `t, b > 0` (from `e^{-y} ≤ 1/y`). -/
theorem sing_norm_term_le {t b : ℝ} (ht0 : 0 < t) (hb : 0 < b) (W : ℕ) {n1 n2 : ℝ}
    (hn1 : n1 ≤ (12 : ℝ) ^ (4 * W)) (hn2 : n2 ≤ (12 : ℝ) ^ (4 * W))
    (hn20 : 0 ≤ n2) :
    n1 * n2 * Real.exp (-((Real.sqrt t)⁻¹ ^ 2 * W) / (4 * b)) ≤ (4 * b * 12 ^ 8 * t) ^ W := by
  have hs : (Real.sqrt t)⁻¹ ^ 2 = t⁻¹ := by rw [inv_pow, Real.sq_sqrt ht0.le]
  have he : Real.exp (-((Real.sqrt t)⁻¹ ^ 2 * W) / (4 * b)) =
      Real.exp (-(1 / (4 * b * t))) ^ W := by
    rw [hs, ← Real.exp_nat_mul]; congr 1; field_simp
  have hy : 0 < 1 / (4 * b * t) := by positivity
  have hexp : Real.exp (-(1 / (4 * b * t))) ≤ 4 * b * t := by
    rw [Real.exp_neg]
    have : 1 / (4 * b * t) ≤ Real.exp (1 / (4 * b * t)) := by
      linarith [Real.add_one_le_exp (1 / (4 * b * t))]
    calc (Real.exp (1 / (4 * b * t)))⁻¹ ≤ (1 / (4 * b * t))⁻¹ := inv_anti₀ hy this
      _ = 4 * b * t := by rw [one_div, inv_inv]
  rw [he]
  have h12 : (4 * b * 12 ^ 8 * t) ^ W = 12 ^ (4 * W) * 12 ^ (4 * W) * (4 * b * t) ^ W := by
    rw [show (4 * b * 12 ^ 8 * t) = 12 ^ 8 * (4 * b * t) by ring, mul_pow, ← pow_add, ← pow_mul]
    ring_nf
  rw [h12]
  have hw : Real.exp (-(1 / (4 * b * t))) ^ W ≤ (4 * b * t) ^ W :=
    pow_le_pow_left₀ (by positivity) hexp W
  have hnn : n1 * n2 ≤ 12 ^ (4 * W) * 12 ^ (4 * W) := mul_le_mul hn1 hn2 hn20 (by positivity)
  exact mul_le_mul hnn hw (by positivity) (by positivity)

/-- Every shape has at most two blocks. -/
theorem sing_blocks_le (σ : LayerShape) : σ.blocks ≤ 2 := by cases σ <;> decide

/-- Every shape has at most two ports. -/
theorem sing_ports_le (σ : LayerShape) : σ.ports ≤ 2 := by cases σ <;> decide

theorem sing_card_physSite_le (σ : LayerShape) (W : ℕ) : Fintype.card (PhysSite W σ) ≤ 2 * W := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  exact Nat.mul_le_mul_right W (sing_blocks_le σ)

theorem sing_card_portSite_le (σ : LayerShape) (W : ℕ) : Fintype.card (PortSite W σ) ≤ 2 * W := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  exact Nat.mul_le_mul_right W (sing_ports_le σ)

/-- A `1/4`-net of the unit sphere of `ℂ^ι` with at most `12^{4W}` points when `|ι| ≤ 2W`. -/
theorem sing_exists_net (ι : Type*) [Fintype ι] {W : ℕ} (hcard : Fintype.card ι ≤ 2 * W) :
    ∃ N : Finset (EuclideanSpace ℂ ι), (∀ u ∈ N, ‖u‖ = 1) ∧ (N.card : ℝ) ≤ 12 ^ (4 * W) ∧
      ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ n ∈ N, ‖x - n‖ ≤ 1 / 4 := by
  obtain ⟨N, h1, h2, h3⟩ := exists_sphere_net_euclidean (ι := ι) (ε := 1 / 4) (by norm_num)
    (by norm_num)
  refine ⟨N, h1, h2.trans ?_, h3⟩
  rw [show (3 : ℝ) / (1 / 4) = 12 by norm_num]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

end Elementary

/-!
## The tail `P(d < t) ≤ (C_b t)^W`
-/

section Tail

/-- The tail constant `C_b = 27 e / b + 4 b 12^8` of `singFloor_tail` (depends only on `b`). -/
def singTailConst (b : ℝ) : ℝ := 27 * Real.exp 1 / b + 4 * b * 12 ^ 8

theorem singTailConst_pos {b : ℝ} (hb : 0 < b) : 0 < singTailConst b := by
  unfold singTailConst; positivity

/-- Union-bound step, any `K`, mesh `0 < ε ≤ 1`, `t ≤ 1`, `t + ε K > 0`:
`P(singFloor S B < t) ≤ P(‖B‖ ≥ K) + (3/ε)^{2k} ((2e/b)(t + εK)²)^W`, `k = finrank ℂ S`. -/
theorem singFloor_tail_split (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) {t ε K : ℝ} (ht1 : t ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < t + ε * K) :
    layerLaw W b σ {ω | singFloor S ω.2 < t} ≤
      layerLaw W b σ {ω | K ≤ ‖bondMatrix σ ω.2‖} +
        ENNReal.ofReal ((3 / ε) ^ (2 * finrank ℂ S)) *
          ENNReal.ofReal ((2 * Real.exp 1 / b * (t + ε * K) ^ 2) ^ W) := by
  have hsub : {ω : LayerSample W σ | singFloor S ω.2 < t} ⊆
      {ω | ∃ x : S, ‖x‖ = 1 ∧ ‖singRestrict S ω.2 x‖ < t} := by
    intro ω hω
    obtain ⟨u, hu, h1, hlt⟩ := exists_of_singFloor_lt S ω.2 ht1 hω
    exact ⟨⟨u, hu⟩, h1, hlt⟩
  have hp : ∀ u : S, ‖u‖ = 1 → layerLaw W b σ {ω | ‖singRestrict S ω.2 u‖ < t + ε * K} ≤
      ENNReal.ofReal ((2 * Real.exp 1 / b * (t + ε * K) ^ 2) ^ W) := by
    intro u hu
    have hv : ‖(WithLp.toLp 2 (WithLp.ofLp (u : EuclideanSpace ℂ (PhysSite W σ))) :
        EuclideanSpace ℂ (PhysSite W σ))‖ = 1 := by
      rw [WithLp.toLp_ofLp]; exact hu
    exact layerLaw_bond_smallBall_norm σ hW hb _ hv hτ
  have hnet := measure_exists_unit_lt_le_complex (layerLaw W b σ) hε hε1
    (fun ω => singRestrict S ω.2) hp
  have hK : {ω : LayerSample W σ | K < ‖singRestrict S ω.2‖} ⊆
      {ω | K ≤ ‖bondMatrix σ ω.2‖} := fun ω hω =>
    (le_of_lt hω).trans (norm_singRestrict_le S ω.2)
  exact (measure_mono hsub).trans (hnet.trans (add_le_add_left (measure_mono hK) _))

/-- **Lower tail of the bond singular floor** (the Gaussian absorption lemma).
Under `layerLaw W b σ` (bonds `Gin(b/W)`), for every shape `σ`, `W ≥ 1`, `b > 0`, every
deterministic complex subspace `S` of the physical coordinates with `finrank ℂ S ≤ W / 8`, and
`0 < t ≤ 1`:
`P(singFloor S B < t) ≤ (C_b t)^W`, `C_b = singTailConst b = 27 e / b + 4 b 12^8`.
Uniform in `S`, `W` and `σ`. Proof: `K = t^{-1/2}`, net of mesh
`ε = t^{3/2}/2` on the unit sphere of `S` (`≤ (3/ε)^{2k}` points,
`measure_exists_unit_lt_le_complex`), fixed-vector small ball `layerLaw_bond_smallBall_norm` at
radius `t + ε K = 3t/2` (net term `≤ (27 e t / b)^W` using `8k ≤ W`), and the norm event
`{‖B‖ ≥ K}` by `layerLaw_bondMatrix_opNorm_tail_of_net` with `1/4`-nets
(`≤ 12^{8W} e^{-W/(4bt)} ≤ (4 b 12^8 t)^W`). No measurability of `singFloor` is used. -/
theorem singFloor_tail (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) (hS : finrank ℂ S ≤ W / 8)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    layerLaw W b σ {ω | singFloor S ω.2 < t} ≤ ENNReal.ofReal ((singTailConst b * t) ^ W) := by
  have hk : 8 * finrank ℂ S ≤ W := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mp hS
    omega
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hε : 0 < t * Real.sqrt t / 2 := by positivity
  have hε1 : t * Real.sqrt t / 2 ≤ 1 := by
    have : t * Real.sqrt t ≤ 1 * 1 := mul_le_mul ht1 hs1 hs.le zero_le_one
    linarith
  have hK : 0 < (Real.sqrt t)⁻¹ := by positivity
  have hsplit := singFloor_tail_split σ hW hb S ht1 hε hε1 (K := (Real.sqrt t)⁻¹)
    (by positivity)
  obtain ⟨Nu, hNu1, hNuc, hNu⟩ := sing_exists_net (PhysSite W σ) (sing_card_physSite_le σ W)
  obtain ⟨Nw, hNw1, hNwc, hNw⟩ := sing_exists_net (PortSite W σ) (sing_card_portSite_le σ W)
  have hnorm : layerLaw W b σ {ω | (Real.sqrt t)⁻¹ ≤ ‖bondMatrix σ ω.2‖} ≤
      ENNReal.ofReal ((4 * b * 12 ^ 8 * t) ^ W) :=
    (layerLaw_bondMatrix_opNorm_tail_of_net σ hW hb Nu Nw hNu1 hNw1 hNu hNw hK).trans
      (ENNReal.ofReal_le_ofReal (sing_norm_term_le ht0 hb W hNuc hNwc (by positivity)))
  have hprod : ENNReal.ofReal ((3 / (t * Real.sqrt t / 2)) ^ (2 * finrank ℂ S)) *
        ENNReal.ofReal ((2 * Real.exp 1 / b *
          (t + t * Real.sqrt t / 2 * (Real.sqrt t)⁻¹) ^ 2) ^ W) ≤
      ENNReal.ofReal ((6 * (9 / 4) * (2 * Real.exp 1 / b) * t) ^ W) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sing_net_term_le ht0 ht1 (by positivity) hk)
  refine (hsplit.trans (add_le_add hnorm hprod)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal
    ((pow_add_pow_le (by positivity) (by positivity) hW.ne').trans (le_of_eq ?_))
  congr 1
  unfold singTailConst
  ring

/-- **`d > 0` almost surely** (`d = singFloor S B`, hypothesis `hd` of `layerResolvent_bound`):
under `layerLaw W b σ`, `W ≥ 1`, `b > 0`, `finrank ℂ S ≤ W / 8`, `0 < singFloor S ω.2` a.s.
(from `singFloor_tail` as `t → 0`; outer measure, no measurability used). -/
theorem singFloor_pos_ae (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) (hS : finrank ℂ S ≤ W / 8) :
    ∀ᵐ ω ∂layerLaw W b σ, 0 < singFloor S ω.2 := by
  rw [ae_iff]
  simp only [not_lt]
  refine le_antisymm ?_ bot_le
  have hT : Tendsto (fun t : ℝ => ENNReal.ofReal ((singTailConst b * t) ^ W)) (𝓝[>] 0)
      (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => ENNReal.ofReal ((singTailConst b * t) ^ W)) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.mul continuous_id).pow W)
    have h0 := hc.tendsto 0
    have e : ENNReal.ofReal ((singTailConst b * 0) ^ W) = 0 := by
      rw [mul_zero, zero_pow hW.ne', ENNReal.ofReal_zero]
    rw [e] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hT ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hsub : {ω : LayerSample W σ | singFloor S ω.2 ≤ 0} ⊆ {ω | singFloor S ω.2 < t} :=
    fun ω hω => lt_of_le_of_lt hω ht.1
  exact (measure_mono hsub).trans (singFloor_tail σ hW hb S hS ht.1 ht.2)

end Tail

/-!
## Inverse moments `‖d⁻¹‖_{L^q} ≤ C_b`, `q ≤ W/2`
-/

section Moments

/-- Pointwise dyadic majorant: `δ^{-q} ≤ 2^q + Σ_m 2^{(m+2)q} 1{δ < 2^{-m}}` (and `0⁻¹ = 0`). -/
theorem sing_inv_rpow_le_dyadic {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 < q) :
    ENNReal.ofReal (δ⁻¹ ^ q) ≤ ENNReal.ofReal ((2 : ℝ) ^ q) +
      ∑' m : ℕ, (if δ < ((2 : ℝ) ^ m)⁻¹ then ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q) else 0) := by
  rcases hδ.eq_or_lt with h0 | hpos
  · rw [← h0, _root_.inv_zero, Real.zero_rpow hq.ne', ENNReal.ofReal_zero]; exact bot_le
  have hi0 : 0 < δ⁻¹ := inv_pos.mpr hpos
  by_cases h2 : δ⁻¹ < 2
  · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow hi0.le h2.le hq.le
  · have h2' : (2 : ℝ) ≤ δ⁻¹ := not_lt.mp h2
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ δ⁻¹)
      (by norm_num : (1 : ℝ) < 2)
    rcases m with _ | m
    · simp at hm2; linarith
    · refine le_add_left (le_trans ?_ (ENNReal.le_tsum m))
      have hlt : δ < ((2 : ℝ) ^ m)⁻¹ := by
        have : (2 : ℝ) ^ m < δ⁻¹ := lt_of_lt_of_le
          (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self m)) hm1
        calc δ = (δ⁻¹)⁻¹ := (inv_inv δ).symm
          _ < ((2 : ℝ) ^ m)⁻¹ := inv_strictAnti₀ (by positivity) this
      simp only [hlt, ↓reduceIte]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hi0.le hm2.le hq.le)

/-- Termwise bound, `β = ⌈b⌉₊`, `1 ≤ q ≤ n - 1`:
`2^{(m+2)q} min(1, (b 2^{-m})^n) ≤ 2^{(β+2)q} 2^β 2^{-m}`. -/
theorem sing_dyadic_term_le {b q : ℝ} (hb : 0 ≤ b) {n : ℕ} (hq1 : 1 ≤ q) (hqn : q + 1 ≤ n) (m : ℕ) :
    ((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n) ≤
      ((2 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q * 2 ^ ⌈b⌉₊ * (2⁻¹ : ℝ) ^ m := by
  set β := ⌈b⌉₊ with hβ
  have hq0 : 0 ≤ q := by linarith
  by_cases hm : m ≤ β
  · have h1 : ((2 : ℝ) ^ (m + 2)) ^ q ≤ ((2 : ℝ) ^ (β + 2)) ^ q :=
      Real.rpow_le_rpow (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega)) hq0
    have h2 : (1 : ℝ) ≤ 2 ^ β * (2⁻¹ : ℝ) ^ m := by
      rw [inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hm
    calc ((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)
        ≤ ((2 : ℝ) ^ (β + 2)) ^ q * 1 :=
          mul_le_mul h1 (min_le_left _ _) (by positivity) (by positivity)
      _ ≤ ((2 : ℝ) ^ (β + 2)) ^ q * (2 ^ β * (2⁻¹ : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · have hm' : β < m := not_le.mp hm
    obtain ⟨d, rfl⟩ : ∃ d, m = β + d := ⟨m - β, by omega⟩
    have hd : 1 ≤ d := by omega
    set Y : ℝ := 2 ^ d with hY
    have hY1 : 1 ≤ Y := one_le_pow₀ (by norm_num)
    have hYpos : 0 < Y := by positivity
    have hbβ : b ≤ 2 ^ β := (Nat.le_ceil b).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
    have hbase : b * ((2 : ℝ) ^ (β + d))⁻¹ ≤ Y⁻¹ := by
      rw [pow_add, mul_inv, ← mul_assoc]
      calc b * ((2 : ℝ) ^ β)⁻¹ * Y⁻¹ ≤ 1 * Y⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact hbβ
        _ = Y⁻¹ := one_mul _
    have hpow : (b * ((2 : ℝ) ^ (β + d))⁻¹) ^ n ≤ Y⁻¹ ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      have : (1 : ℝ) ≤ n := by linarith
      have : 1 ≤ n := by exact_mod_cast this
      omega⟩
    have hqn' : q ≤ (n' : ℝ) := by push_cast at hqn; linarith
    have hYq : Y ^ q ≤ Y ^ n' := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hY1 hqn'
    have hsplit : ((2 : ℝ) ^ (β + d + 2)) ^ q = ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q := by
      rw [show β + d + 2 = (β + 2) + d by ring, pow_add, Real.mul_rpow (by positivity)
        (by positivity)]
    have hkey : Y ^ q * Y⁻¹ ^ (n' + 1) ≤ Y⁻¹ := by
      calc Y ^ q * Y⁻¹ ^ (n' + 1) ≤ Y ^ n' * Y⁻¹ ^ (n' + 1) :=
            mul_le_mul_of_nonneg_right hYq (by positivity)
        _ = Y⁻¹ := by
            rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hYpos.ne', one_pow, one_mul]
    have hrhs : ((2 : ℝ) ^ (β + 2)) ^ q * 2 ^ β * (2⁻¹ : ℝ) ^ (β + d) =
        ((2 : ℝ) ^ (β + 2)) ^ q * Y⁻¹ := by
      have e : (2 : ℝ) ^ β * (2⁻¹ : ℝ) ^ (β + d) = Y⁻¹ := by
        rw [hY, inv_pow, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      rw [mul_assoc _ ((2 : ℝ) ^ β), e]
    rw [hrhs, hsplit]
    calc ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q * min 1 ((b * ((2 : ℝ) ^ (β + d))⁻¹) ^ (n' + 1))
        ≤ ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q * Y⁻¹ ^ (n' + 1) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hpow) (by positivity)
      _ = ((2 : ℝ) ^ (β + 2)) ^ q * (Y ^ q * Y⁻¹ ^ (n' + 1)) := by ring
      _ ≤ ((2 : ℝ) ^ (β + 2)) ^ q * Y⁻¹ := mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Final constant: `2^q + 2 · 2^{(β+2)q} 2^β ≤ (4^{β+2})^q` for `q ≥ 1`. -/
theorem sing_dyadic_final_le {b q : ℝ} (hq1 : 1 ≤ q) :
    (2 : ℝ) ^ q + ((2 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q * 2 ^ ⌈b⌉₊ * 2 ≤ ((4 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q := by
  set β := ⌈b⌉₊
  have hq0 : 0 ≤ q := by linarith
  set Z := ((2 : ℝ) ^ (β + 2)) ^ q with hZ
  have h4 : ((4 : ℝ) ^ (β + 2)) ^ q = Z * Z := by
    rw [hZ, ← Real.mul_rpow (by positivity) (by positivity), ← mul_pow]; norm_num
  have hP1 : (1 : ℝ) ≤ 2 ^ β := one_le_pow₀ (by norm_num)
  have hP : (2 : ℝ) ^ (β + 2) = 4 * 2 ^ β := by rw [pow_add]; ring
  have hZ1 : (2 : ℝ) ^ (β + 2) ≤ Z := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ) ^ (β + 2))
      (one_le_pow₀ (by norm_num)) hq1
    rwa [Real.rpow_one] at this
  have h2q : (2 : ℝ) ^ q ≤ Z :=
    Real.rpow_le_rpow (by norm_num) (by rw [hP]; nlinarith) hq0
  rw [h4]
  nlinarith

/-- **Inverse moments from an outer-measure tail** (no measurability). If `0 ≤ δ` and
`μ(δ < 2^{-m}) ≤ (c 2^{-m})^n` for all `m` (outer measure; `δ` need not be measurable), then for
`1 ≤ q ≤ n - 1`: `∫⁻ δ^{-q} dμ ≤ (4^{⌈c⌉₊+2})^q`. Any probability space. The dyadic majorant is
integrated against the measurable hulls `toMeasurable μ {δ < 2^{-m}}`, which have the same
measure. -/
theorem sing_lintegral_inv_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδ0 : ∀ ω, 0 ≤ δ ω)
    {c q : ℝ} (hc : 0 ≤ c) {n : ℕ} (hq1 : 1 ≤ q) (hqn : q + 1 ≤ n)
    (htail : ∀ m : ℕ, μ {ω | δ ω < ((2 : ℝ) ^ m)⁻¹} ≤
      ENNReal.ofReal ((c * ((2 : ℝ) ^ m)⁻¹) ^ n)) :
    ∫⁻ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ∂μ ≤ ENNReal.ofReal (((4 : ℝ) ^ (⌈c⌉₊ + 2)) ^ q) := by
  set β := ⌈c⌉₊
  set K : ℝ := ((2 : ℝ) ^ (β + 2)) ^ q * 2 ^ β with hK
  have hK0 : 0 ≤ K := by positivity
  have hq0 : 0 < q := by linarith
  let S : ℕ → Set Ω := fun m => {ω | δ ω < ((2 : ℝ) ^ m)⁻¹}
  let H : ℕ → Set Ω := fun m => toMeasurable μ (S m)
  have hH : ∀ m, MeasurableSet (H m) := fun m => measurableSet_toMeasurable μ (S m)
  have hHμ : ∀ m, μ (H m) = μ (S m) := fun m => measure_toMeasurable (S m)
  let w : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q)
  have hpt : ∀ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, (H m).indicator (fun _ => w m) ω := by
    intro ω
    refine (sing_inv_rpow_le_dyadic (hδ0 ω) hq0).trans ?_
    gcongr with m
    by_cases h : δ ω < ((2 : ℝ) ^ m)⁻¹
    · rw [ite_eq_left h, Set.indicator_of_mem (subset_toMeasurable μ (S m) h)]
    · rw [ite_eq_right h]; exact bot_le
  have hterm : ∀ m, w m * μ (H m) ≤ ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) := by
    intro m
    have hμ : μ (H m) ≤ ENNReal.ofReal (min 1 ((c * ((2 : ℝ) ^ m)⁻¹) ^ n)) := by
      rw [ENNReal.ofReal_min, ENNReal.ofReal_one, hHμ]
      exact le_min prob_le_one (htail m)
    calc w m * μ (H m) ≤ w m * ENNReal.ofReal (min 1 ((c * ((2 : ℝ) ^ m)⁻¹) ^ n)) :=
          by gcongr
      _ = ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((c * ((2 : ℝ) ^ m)⁻¹) ^ n)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) :=
          ENNReal.ofReal_le_ofReal (sing_dyadic_term_le hc hq1 hqn m)
  have hgeom : ∑' m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) = ENNReal.ofReal K * 2 := by
    have e : ∀ m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) = ENNReal.ofReal K * 2⁻¹ ^ m := by
      intro m
      rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    simp only [e, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
  calc ∫⁻ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, (H m).indicator (fun _ => w m) ω) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, w m * μ (H m) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun m => (measurable_const.indicator (hH m)).aemeasurable)]
        congr 1
        exact tsum_congr fun m => lintegral_indicator_const (hH m) (w m)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) :=
        by gcongr with m; exact hterm m
    _ = ENNReal.ofReal ((2 : ℝ) ^ q + K * 2) := by
        rw [hgeom, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hK0, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (((4 : ℝ) ^ (⌈c⌉₊ + 2)) ^ q) :=
        ENNReal.ofReal_le_ofReal (sing_dyadic_final_le hq1)

/-- `layerLaw W b σ` is a probability measure. -/
theorem sing_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    IsProbabilityMeasure (layerLaw W b σ) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold layerLaw
  infer_instance

/-- The moment constant `C_b = 4^{⌈singTailConst b⌉₊ + 2}` of `singFloor_inv_moment`
(depends only on `b`). -/
def singMomentConst (b : ℝ) : ℝ := (4 : ℝ) ^ (⌈singTailConst b⌉₊ + 2)

theorem singMomentConst_pos (b : ℝ) : 0 < singMomentConst b := by
  unfold singMomentConst; positivity

/-- **Inverse moments of the bond singular floor** (the Gaussian absorption lemma, "`‖d⁻¹‖_{L^q(·|D)} ≤ C_b`, `q ≤ ε₂ W`"). Under `layerLaw W b σ`, for every shape
`σ`, `W ≥ 1`, `b > 0`, every deterministic complex subspace `S` of the physical coordinates with
`finrank ℂ S ≤ W / 8`, and real `1 ≤ q ≤ W/2` (`ε₂ = 1/2`):
`∫⁻ (singFloor S B)^{-q} ≤ C_b^q`, `C_b = singMomentConst b = 4^{⌈27e/b + 4b 12^8⌉₊ + 2}`.
Uniform in `S`, `W`, `σ`. (Lean's `0⁻¹ = 0` is harmless: `singFloor > 0` a.s.,
`singFloor_pos_ae`.) No measurability of `singFloor` is used. -/
theorem singFloor_inv_moment (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (S : Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ))) (hS : finrank ℂ S ≤ W / 8)
    {q : ℝ} (hq1 : 1 ≤ q) (hqW : q ≤ (W : ℝ) / 2) :
    ∫⁻ ω, ENNReal.ofReal ((singFloor S ω.2)⁻¹ ^ q) ∂layerLaw W b σ ≤
      ENNReal.ofReal (singMomentConst b ^ q) := by
  have := sing_isProbabilityMeasure_layerLaw W b σ
  have hqn : q + 1 ≤ (W : ℝ) := by linarith
  refine sing_lintegral_inv_rpow_le_of_tail (layerLaw W b σ) (fun ω => singFloor S ω.2)
    (fun ω => singFloor_nonneg S ω.2) (singTailConst_pos hb).le hq1 hqn fun m => ?_
  have h := singFloor_tail σ hW hb S hS (t := ((2 : ℝ) ^ m)⁻¹) (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  exact h

end Moments

end BlockBand.Layers
